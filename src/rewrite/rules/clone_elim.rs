//! Rule 4: `redundant-clone-elim` v1 — remove a `.clone()` call at the PROVEN
//! last use of a bare local binding, so the original value is moved instead of
//! copied.
//!
//! The proof is the CPG's `DATA_DEP` overlay (ADR-0003). `DATA_DEP` is
//! conservative **may-reach** def-use: every read that any execution could
//! perform is recorded (macro arguments, closure bodies, and nested groups are
//! all scanned; string/comment contents are not tokens and cannot alias).
//! Therefore the direction this rule needs is SOUND: when the graph shows **no
//! statement reachable after the clone reads the binding's definition**, no
//! execution reads it — an over-approximation that concludes "no reader" is
//! trustworthy precisely because it can only err by inventing readers
//! (refusing a valid site), never by missing one (permitting an invalid one).
//!
//! HONESTLY SCOPED (v1). Recognized shapes — the clone expression must be
//! exactly `X.clone()` with `X` a bare local:
//!
//! - `let [mut] Y [: TYPE] = X.clone();` where the RHS is exactly `X.clone()`;
//! - `PATH(… , X.clone() , …);` — a plain path call (no `.`, no `!`, no
//!   keywords in the callee) whose argument is exactly `X.clone()`.
//!
//! Semantic requirements, each checked against the real CPG and each a
//! machine-readable rejection when it fails:
//!
//! - the statement is not inside any loop body (`clone_in_loop`: a loop
//!   executes the clone repeatedly; the move is only legal once);
//! - `X` occurs exactly once in the statement (`receiver_reused_in_statement`:
//!   argument evaluation order could observe the moved value);
//! - `X` has exactly ONE reaching definition at the clone, of kind `let`
//!   (`receiver_def_not_single_let`: parameters and pattern bindings may be
//!   references or by-`ref` bindings — a claim this rule does not make);
//! - that definition is a bare single-ident `let [mut] X …` binding
//!   (`receiver_def_not_bare_let`: `ref` patterns and destructurings are out);
//! - no statement CFG-reachable after the clone reads that definition
//!   (`cloned_value_read_later` — the last-use proof). Reads on paths that can
//!   only execute BEFORE the clone are permitted: a move at last use cannot
//!   invalidate a read that already happened.
//!
//! Everything else — field/deref/chain receivers (`self.x.clone()`,
//! `(*p).clone()`, `x.clone().len()`), macro arguments, `return x.clone()`,
//! turbofish, clone-with-arguments — is refused (`clone_receiver_not_bare_local`
//! / `clone_not_in_recognized_position`) or is not a candidate. Conservative
//! by charter: when unsure, REFUSE.
//!
//! Emission is the minimal safe edit: delete the `.clone()` bytes (the span
//! from the `.` to the closing `)`), leaving `X` in place. No other byte moves.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::core::span::ByteSpan;
use crate::ir::cpg::{elems, flat_tokens, top_index, ElsePart, Stmt, StmtKind, E};
use crate::ir::ontology::edge;
use crate::lang::rust::lexer::{is_keyword, kind as tk};
use crate::rewrite::proposal::{ProposedEdit, Rejection};
use crate::rewrite::rules::{
    edge_prop, line_of, text_of, walk_stmts, FileCpg, FnUnit, Rule, RuleOptions, RuleOutcome,
};

pub struct RedundantCloneElim;

impl Rule for RedundantCloneElim {
    fn id(&self) -> &'static str {
        "redundant-clone-elim"
    }

    fn version(&self) -> &'static str {
        "1"
    }

    fn summary(&self) -> &'static str {
        "Remove `.clone()` at the proven last use of a bare local: the CPG's may-reach \
         DATA_DEP records no read of the binding on any path after the call, so the \
         original value is moved instead of copied."
    }

    fn shapes(&self) -> &'static [&'static str] {
        &[
            "let y = x.clone();      => let y = x;      (x: bare local, single `let` def, no read on any path after)",
            "let mut y = x.clone();  => let mut y = x;  (same proof; binder mutability is untouched)",
            "f(x.clone());           => f(x);           (plain path call, argument exactly `x.clone()`, same proof)",
            "g(a, x.clone(), b);     => g(a, x, b);     (each qualifying argument is its own site)",
        ]
    }

    fn propose(&self, file: &FileCpg<'_>, _opts: &RuleOptions) -> Result<RuleOutcome, String> {
        let mut out = RuleOutcome::default();
        for f in &file.fns {
            let reach = FnReach::new(file, f);
            scan_block(file, f, &reach, &f.stmts, false, &mut out);
        }
        out.edits.sort_by_key(|e| (e.span.start, e.span.end));
        out.rejections.sort_by_key(|r| (r.span.start, r.span.end));
        Ok(out)
    }
}

// ---------------------------------------------------------------------------
// CFG reachability: which statements can execute AFTER a given one?
// ---------------------------------------------------------------------------

/// Forward `FLOWS_TO` adjacency for one function's statement nodes. The CFG is
/// syntactic (every branch edge present), so the successor closure
/// OVER-approximates "can execute after" — the safe direction for refusal.
pub(crate) struct FnReach {
    succ: BTreeMap<String, Vec<String>>,
}

impl FnReach {
    pub(crate) fn new(file: &FileCpg<'_>, f: &FnUnit<'_>) -> FnReach {
        let stem = f.fn_id.strip_prefix("fn::").unwrap_or(&f.fn_id);
        let prefix = format!("stmt::{stem}::");
        let belongs = |id: &str| id == f.fn_id || id.starts_with(&prefix);
        let mut succ: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for e in file.graph.edges() {
            if e.kind == edge::FLOWS_TO && belongs(&e.from) && belongs(&e.to) {
                succ.entry(e.from.clone()).or_default().push(e.to.clone());
            }
        }
        FnReach { succ }
    }

    /// Every node reachable from `start` via one or more `FLOWS_TO` edges
    /// (`start` itself only if it sits on a cycle).
    pub(crate) fn after(&self, start: &str) -> BTreeSet<String> {
        let mut seen: BTreeSet<String> = BTreeSet::new();
        let mut queue: VecDeque<&str> = VecDeque::new();
        if let Some(next) = self.succ.get(start) {
            for n in next {
                if seen.insert(n.clone()) {
                    queue.push_back(n);
                }
            }
        }
        while let Some(id) = queue.pop_front() {
            if let Some(next) = self.succ.get(id) {
                for n in next {
                    if seen.insert(n.clone()) {
                        queue.push_back(n.as_str());
                    }
                }
            }
        }
        seen
    }
}

// ---------------------------------------------------------------------------
// Recognizer
// ---------------------------------------------------------------------------

/// One `.clone()` occurrence inside a statement: the deletable span (from the
/// `.` to the `)`), the receiver name when it is a bare local, and whether the
/// receiver was disqualified syntactically.
struct Occurrence {
    span: ByteSpan,
    /// `Ok(name)` for a bare-local receiver; `Err(detail)` otherwise.
    receiver: Result<String, String>,
}

fn scan_block(
    file: &FileCpg<'_>,
    f: &FnUnit<'_>,
    reach: &FnReach,
    stmts: &[Stmt<'_>],
    in_loop: bool,
    out: &mut RuleOutcome,
) {
    for s in stmts {
        scan_stmt(file, f, reach, s, in_loop, out);
    }
}

fn scan_stmt(
    file: &FileCpg<'_>,
    f: &FnUnit<'_>,
    reach: &FnReach,
    s: &Stmt<'_>,
    in_loop: bool,
    out: &mut RuleOutcome,
) {
    examine(file, f, reach, s, in_loop, out);
    let body_in_loop =
        in_loop || matches!(s.kind, StmtKind::For | StmtKind::While | StmtKind::Loop);
    if let Some(b) = &s.body {
        scan_block(file, f, reach, b, body_in_loop, out);
    }
    match &s.else_part {
        Some(ElsePart::Block(_, b)) => scan_block(file, f, reach, b, in_loop, out),
        Some(ElsePart::If(nested)) => scan_stmt(file, f, reach, nested, in_loop, out),
        None => {}
    }
    for arm in &s.arms {
        if let Some(b) = &arm.block {
            scan_block(file, f, reach, b, in_loop, out);
        }
    }
}

/// Examine one statement: enumerate `.clone()` occurrences (header + arm
/// expressions), match the statement against the recognized shapes, and push
/// one edit or one rejection per occurrence.
fn examine(
    file: &FileCpg<'_>,
    f: &FnUnit<'_>,
    reach: &FnReach,
    s: &Stmt<'_>,
    in_loop: bool,
    out: &mut RuleOutcome,
) {
    let src = file.src;
    let mut occs = occurrences(&s.header, src);
    for arm in &s.arms {
        occs.extend(occurrences(&arm.pattern, src));
        occs.extend(occurrences(&arm.expr, src));
    }
    if occs.is_empty() {
        return;
    }
    // The spans this statement's shape recognizes: name → deletable span.
    let recognized = recognized_sites(s, src);

    for occ in occs {
        let mut reject = |reason: &str, detail: String| {
            out.rejections.push(Rejection {
                span: occ.span,
                reason: reason.to_string(),
                detail,
            });
        };
        let x = match &occ.receiver {
            Ok(name) => name.clone(),
            Err(detail) => {
                reject("clone_receiver_not_bare_local", detail.clone());
                continue;
            }
        };
        if !recognized.iter().any(|(_, sp)| *sp == occ.span) {
            reject(
                "clone_not_in_recognized_position",
                format!(
                    "`{}.clone()` is not the whole RHS of a `let` or a whole argument of a \
                     plain path call — the only positions this rule recognizes",
                    x
                ),
            );
            continue;
        }
        if in_loop {
            reject(
                "clone_in_loop",
                format!(
                    "the clone of `{x}` sits inside a loop body and may execute repeatedly; \
                     the original can be moved at most once"
                ),
            );
            continue;
        }
        match check_site(file, f, reach, s, &x, occ.span) {
            Ok(edit) => out.edits.push(edit),
            Err((reason, detail)) => reject(reason, detail),
        }
    }
}

/// Every `x.clone()`-shaped token run in `els` (any depth): `.` `clone` `(`
/// `)` with the receiver token immediately before the `.`.
fn occurrences(els: &[E<'_>], src: &str) -> Vec<Occurrence> {
    let toks = flat_tokens(els);
    let mut out = Vec::new();
    for (k, dot) in toks.iter().enumerate() {
        if dot.span.text(src) != "."
            || toks.get(k + 1).map(|t| t.span.text(src)) != Some("clone")
            || toks.get(k + 2).map(|t| t.span.text(src)) != Some("(")
            || toks.get(k + 3).map(|t| t.span.text(src)) != Some(")")
        {
            continue;
        }
        let span = ByteSpan::new(dot.span.start as usize, toks[k + 3].span.end as usize);
        let receiver = match k.checked_sub(1).map(|i| toks[i]) {
            Some(r) if r.kind == tk::IDENT || r.kind == tk::RAW_IDENT => {
                let name = r.span.text(src);
                if is_keyword(name) {
                    Err(format!(
                        "the clone receiver `{name}` is a keyword, not a local binding"
                    ))
                } else {
                    match k.checked_sub(2).map(|i| toks[i].span.text(src)) {
                        Some(".") | Some("::") => Err(format!(
                            "the clone receiver `{name}` is a field/path projection, not a \
                             bare local — ownership of the containing place is a claim this \
                             rule does not make"
                        )),
                        _ => Ok(name.to_string()),
                    }
                }
            }
            _ => Err(
                "the clone receiver is not a bare identifier (chained call, deref, index, \
                 or literal)"
                    .to_string(),
            ),
        };
        out.push(Occurrence { span, receiver });
    }
    out
}

/// The clone sites this statement's SHAPE recognizes: `(receiver, span)` per
/// site. Element-level (depth-0) match — nested occurrences never qualify.
/// Also consumed by the certifier (ADR-0007) to re-derive sites from the
/// before tree.
pub(crate) fn recognized_sites(s: &Stmt<'_>, src: &str) -> Vec<(String, ByteSpan)> {
    match s.kind {
        StmtKind::Let => let_site(s, src).into_iter().collect(),
        StmtKind::Expr => call_sites(s, src),
        _ => Vec::new(),
    }
}

/// Shape A: `let [mut] Y [: TYPE] = X.clone();` — binder a bare ident, RHS
/// exactly the four elements `X . clone ()`.
fn let_site(s: &Stmt<'_>, src: &str) -> Option<(String, ByteSpan)> {
    let h = trim_semi(&s.header, src);
    if h.first()?.text(src)? != "let" {
        return None;
    }
    let mut idx = 1;
    if h.get(idx)?.text(src)? == "mut" {
        idx += 1;
    }
    match h.get(idx) {
        Some(E::T(t)) if t.kind == tk::IDENT || t.kind == tk::RAW_IDENT => {}
        _ => return None, // pattern binder — not the recognized shape
    }
    match h.get(idx + 1)?.text(src)? {
        ":" | "=" => {}
        _ => return None,
    }
    let eq = top_index(h, "=", src)?;
    clone_expr(&h[eq + 1..], src)
}

/// Shape B: `PATH(ARGS);` with a plain path callee; each depth-0 argument
/// that is exactly `X.clone()` is a site.
fn call_sites(s: &Stmt<'_>, src: &str) -> Vec<(String, ByteSpan)> {
    let h = trim_semi(&s.header, src);
    let Some((E::G(group), callee)) = h.split_last() else {
        return Vec::new();
    };
    if callee.is_empty()
        || src.as_bytes().get(group.span.start as usize) != Some(&b'(')
        || !callee.iter().enumerate().all(|(i, e)| match e {
            E::G(_) => false,
            E::T(t) => {
                let text = t.span.text(src);
                if i % 2 == 0 {
                    (t.kind == tk::IDENT || t.kind == tk::RAW_IDENT) && !is_keyword(text)
                } else {
                    text == "::"
                }
            }
        })
    {
        return Vec::new();
    }
    let inner = paren_inner(group, src);
    let mut out = Vec::new();
    for arg in split_args(&inner, src) {
        if let Some(site) = clone_expr(arg, src) {
            out.push(site);
        }
    }
    out
}

/// Is this element run exactly `X . clone ()` (empty parens)? Returns the
/// receiver name and the deletable `.clone()` span.
fn clone_expr(els: &[E<'_>], src: &str) -> Option<(String, ByteSpan)> {
    let els = trim_semi(els, src);
    let [E::T(x), E::T(dot), E::T(m), E::G(g)] = els else {
        return None;
    };
    if (x.kind != tk::IDENT && x.kind != tk::RAW_IDENT)
        || is_keyword(x.span.text(src))
        || dot.span.text(src) != "."
        || m.span.text(src) != "clone"
        || !paren_inner(g, src).is_empty()
        || src.as_bytes().get(g.span.start as usize) != Some(&b'(')
    {
        return None;
    }
    Some((
        x.span.text(src).to_string(),
        ByteSpan::new(dot.span.start as usize, g.span.end as usize),
    ))
}

/// The semantic checks: single occurrence, single `let` definition, bare-ident
/// binder, and the last-use proof. Returns the edit or a rejection reason.
fn check_site(
    file: &FileCpg<'_>,
    f: &FnUnit<'_>,
    reach: &FnReach,
    s: &Stmt<'_>,
    x: &str,
    span: ByteSpan,
) -> Result<ProposedEdit, (&'static str, String)> {
    let src = file.src;
    let sid = s.id.clone().unwrap_or_default();

    // `X` occurs exactly once in the whole statement: a second occurrence
    // (another argument, the binder, an index) could observe the moved value
    // during this statement's own evaluation.
    let uses = count_ident(s, x, src);
    if uses != 1 {
        return Err((
            "receiver_reused_in_statement",
            format!("`{x}` occurs {uses} times in this statement; the move must be its only use"),
        ));
    }

    // Exactly one reaching definition, of kind `let`.
    let defs: BTreeSet<(String, String)> = file
        .graph
        .edges()
        .filter(|e| e.kind == edge::DATA_DEP && e.from == sid && edge_prop(e, "var") == Some(x))
        .map(|e| (e.to.clone(), edge_prop(e, "def").unwrap_or("-").to_string()))
        .collect();
    if defs.len() != 1 || defs.iter().next().is_none_or(|(_, k)| k != "let") {
        let listed: Vec<String> = defs.iter().map(|(d, k)| format!("{d} (def={k})")).collect();
        return Err((
            "receiver_def_not_single_let",
            format!(
                "`{x}` must have exactly one reaching definition of kind `let`; the CPG \
                 records: [{}] — parameters, pattern bindings, and merged redefinitions \
                 may not be owned bare locals",
                listed.join(", ")
            ),
        ));
    }
    let def_id = defs.iter().next().expect("checked len above").0.clone();

    // The definition must be a bare single-ident `let [mut] x …` statement.
    let Some(def_stmt) = find_stmt_by_id(&f.stmts, &def_id) else {
        return Err((
            "receiver_def_not_bare_let",
            format!("definition {def_id} of `{x}` is not a statement of this function"),
        ));
    };
    if !bare_let_binds(def_stmt, x, src) {
        return Err((
            "receiver_def_not_bare_let",
            format!(
                "definition {def_id} of `{x}` is not a bare `let [mut] {x} …` binding \
                 (destructuring or `ref` patterns may bind by reference)"
            ),
        ));
    }

    // THE LAST-USE PROOF: no statement CFG-reachable after this one reads the
    // definition. DATA_DEP is may-reach (over-approximates readers), so an
    // empty reachable-reader set is sound evidence of last use.
    let after = reach.after(&sid);
    let late_readers: Vec<String> = file
        .graph
        .edges()
        .filter(|e| {
            e.kind == edge::DATA_DEP
                && e.to == def_id
                && edge_prop(e, "var") == Some(x)
                && e.from != sid
                && after.contains(&e.from)
        })
        .map(|e| e.from.clone())
        .collect();
    if !late_readers.is_empty() {
        return Err((
            "cloned_value_read_later",
            format!(
                "`{x}` is read after the clone on some path: DATA_DEP var={x} -> {def_id} \
                 from {{{}}} — the clone is not the last use",
                late_readers.join(", ")
            ),
        ));
    }

    let line = line_of(src, span.start as usize);
    Ok(ProposedEdit {
        span,
        before: text_of(src, span).to_string(),
        after: String::new(),
        why_safe: format!(
            "`{x}` has a single `let` definition and the CPG's conservative may-reach \
             DATA_DEP records no read of it on any path after this statement, so this \
             `.clone()` is the last use — the original value is moved instead of copied; \
             may-reach over-approximates readers, so the no-reader conclusion is sound"
        ),
        cpg_facts: vec![
            format!(
                "{}: statement {sid} (stmt_kind={}, line {line}) holds the last use of `{x}`",
                f.fn_id,
                s.kind.label()
            ),
            format!("DATA_DEP var={x} def=let: {sid} -> {def_id} — the single reaching definition"),
            format!(
                "definition {def_id} is a bare `let` binding of `{x}` (line {})",
                line_of(src, def_stmt.span.start as usize)
            ),
            format!(
                "no DATA_DEP edge var={x} targets {def_id} from any statement reachable \
                 after {sid} via FLOWS_TO — the last-use proof (may-reach DATA_DEP \
                 over-approximates reads, so absence of readers is trustworthy)"
            ),
            format!("{sid} is not inside any loop body — the clone executes at most once per call"),
        ],
    })
}

// ---------------------------------------------------------------------------
// Small helpers
// ---------------------------------------------------------------------------

/// Drop a trailing `;` element.
fn trim_semi<'e, 'a>(els: &'e [E<'a>], src: &str) -> &'e [E<'a>] {
    match els.last() {
        Some(e) if e.text(src) == Some(";") => &els[..els.len() - 1],
        _ => els,
    }
}

/// A paren group's depth-0 elements without the `(` `)` delimiters.
fn paren_inner<'a>(group: &'a crate::core::cst::Node, src: &str) -> Vec<E<'a>> {
    let mut v = elems(group);
    if v.first().and_then(|e| e.text(src)) == Some("(") {
        v.remove(0);
    }
    if v.last().and_then(|e| e.text(src)) == Some(")") {
        v.pop();
    }
    v
}

/// Split depth-0 elements on `,`.
fn split_args<'e, 'a>(els: &'e [E<'a>], src: &str) -> Vec<&'e [E<'a>]> {
    let mut out = Vec::new();
    let mut start = 0;
    for (i, e) in els.iter().enumerate() {
        if e.text(src) == Some(",") {
            out.push(&els[start..i]);
            start = i + 1;
        }
    }
    out.push(&els[start..]);
    out
}

/// How many IDENT/RAW_IDENT tokens named `name` appear anywhere under `s`
/// (header, bodies, arms — any depth).
pub(crate) fn count_ident(s: &Stmt<'_>, name: &str, src: &str) -> usize {
    let mut n = 0;
    crate::rewrite::rules::walk_stmt(s, &mut |st| {
        n += flat_tokens(&st.header)
            .iter()
            .filter(|t| {
                (t.kind == tk::IDENT || t.kind == tk::RAW_IDENT) && t.span.text(src) == name
            })
            .count();
        for arm in &st.arms {
            for els in [&arm.pattern, &arm.expr] {
                n += flat_tokens(els)
                    .iter()
                    .filter(|t| {
                        (t.kind == tk::IDENT || t.kind == tk::RAW_IDENT) && t.span.text(src) == name
                    })
                    .count();
            }
        }
    });
    n
}

/// Find a statement (any depth) by its assigned CPG node id.
pub(crate) fn find_stmt_by_id<'s, 'a>(stmts: &'s [Stmt<'a>], id: &str) -> Option<&'s Stmt<'a>> {
    let mut found: Option<&'s Stmt<'a>> = None;
    walk_stmts(stmts, &mut |s| {
        if found.is_none() && s.id.as_deref() == Some(id) {
            found = Some(s);
        }
    });
    found
}

/// Is `s` a bare single-ident `let [mut] {name} [: TYPE] = …` statement?
pub(crate) fn bare_let_binds(s: &Stmt<'_>, name: &str, src: &str) -> bool {
    if s.kind != StmtKind::Let {
        return false;
    }
    let h = &s.header;
    if h.first().and_then(|e| e.text(src)) != Some("let") {
        return false;
    }
    let idx = if h.get(1).and_then(|e| e.text(src)) == Some("mut") {
        2
    } else {
        1
    };
    matches!(h.get(idx), Some(E::T(t))
        if (t.kind == tk::IDENT || t.kind == tk::RAW_IDENT) && t.span.text(src) == name)
        && matches!(
            h.get(idx + 1).and_then(|e| e.text(src)),
            Some(":") | Some("=")
        )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::rust::parser::parse;
    use crate::rewrite::edit::{apply_edits, SpanEdit};
    use crate::rewrite::rules::analyze_file;

    fn run(src: &str) -> (String, RuleOutcome) {
        let tree = parse("t.rs", src);
        assert!(tree.is_lossless());
        let file = analyze_file(&tree);
        let out = RedundantCloneElim
            .propose(&file, &RuleOptions::default())
            .unwrap();
        let edits: Vec<SpanEdit> = out
            .edits
            .iter()
            .map(|e| SpanEdit {
                span: e.span,
                replacement: e.after.clone(),
            })
            .collect();
        (apply_edits(src, &edits).unwrap(), out)
    }

    fn only_rejection(out: &RuleOutcome) -> &Rejection {
        assert!(out.edits.is_empty(), "expected no edits: {:?}", out.edits);
        assert_eq!(out.rejections.len(), 1, "{:?}", out.rejections);
        &out.rejections[0]
    }

    // --- accepted shapes ------------------------------------------------------

    #[test]
    fn let_clone_at_last_use_is_removed() {
        let src = "fn f() {\n    let x = make();\n    let y = x.clone();\n    use_it(y);\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1, "{:?}", o.rejections);
        assert_eq!(
            out,
            "fn f() {\n    let x = make();\n    let y = x;\n    use_it(y);\n}\n"
        );
        assert_eq!(o.edits[0].before, ".clone()");
        assert_eq!(o.edits[0].after, "");
    }

    #[test]
    fn call_argument_clone_at_last_use_is_removed() {
        let src = "fn f() {\n    let x = make();\n    take(x.clone());\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1, "{:?}", o.rejections);
        assert_eq!(out, "fn f() {\n    let x = make();\n    take(x);\n}\n");
    }

    #[test]
    fn multi_argument_call_keeps_other_args() {
        let src = "fn f(a: i32) {\n    let x = make();\n    take(a, x.clone(), 3);\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1, "{:?}", o.rejections);
        assert_eq!(
            out,
            "fn f(a: i32) {\n    let x = make();\n    take(a, x, 3);\n}\n"
        );
    }

    #[test]
    fn path_callee_is_recognized() {
        let src = "fn f() {\n    let x = make();\n    sink::push(x.clone());\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1, "{:?}", o.rejections);
        assert!(out.contains("sink::push(x);"), "{out}");
    }

    #[test]
    fn mut_binder_and_type_ascription_are_kept() {
        let src =
            "fn f() {\n    let x = make();\n    let mut y: Thing = x.clone();\n    y.go();\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1, "{:?}", o.rejections);
        assert!(out.contains("let mut y: Thing = x;"), "{out}");
    }

    #[test]
    fn read_before_the_clone_is_allowed() {
        // A read that can only execute BEFORE the clone does not block the
        // move: the last-use proof is about paths AFTER this statement.
        let src = "fn f() {\n    let x = make();\n    log(&x);\n    let y = x.clone();\n    use_it(y);\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1, "{:?}", o.rejections);
        assert!(out.contains("let y = x;"), "{out}");
    }

    #[test]
    fn conditional_clone_is_recognized() {
        // Moving inside one branch is fine: no path after the move reads `x`.
        let src = "fn f(c: bool) {\n    let x = make();\n    if c {\n        sink(x.clone());\n    }\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1, "{:?}", o.rejections);
        assert!(out.contains("sink(x);"), "{out}");
    }

    #[test]
    fn second_clone_is_last_use_first_is_not() {
        let src = "fn f() {\n    let x = make();\n    let a = x.clone();\n    let b = x.clone();\n    use_it(a, b);\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1, "{:?}", o.edits);
        assert_eq!(o.rejections.len(), 1, "{:?}", o.rejections);
        assert_eq!(o.rejections[0].reason, "cloned_value_read_later");
        assert!(out.contains("let a = x.clone();"), "{out}");
        assert!(out.contains("let b = x;"), "{out}");
    }

    #[test]
    fn shadowed_inner_binding_is_its_own_last_use() {
        // The inner `x` is a different definition; reading the OUTER `x`
        // afterwards does not block the inner move.
        let src = "fn f(c: bool) {\n    let x = outer();\n    if c {\n        let x = inner();\n        sink(x.clone());\n    }\n    use_it(&x);\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1, "{:?}", o.rejections);
        assert!(out.contains("sink(x);"), "{out}");
        assert!(out.contains("use_it(&x);"), "{out}");
    }

    #[test]
    fn why_safe_cites_the_last_use_proof() {
        let src = "fn f() {\n    let x = make();\n    let y = x.clone();\n    use_it(y);\n}\n";
        let (_, o) = run(src);
        let e = &o.edits[0];
        assert!(e.why_safe.contains("may-reach"), "{}", e.why_safe);
        assert!(e.why_safe.contains("last use"), "{}", e.why_safe);
        let facts = e.cpg_facts.join("\n");
        assert!(facts.contains("fn::f#1"), "{facts}");
        assert!(facts.contains("DATA_DEP var=x def=let"), "{facts}");
        assert!(facts.contains("last-use proof"), "{facts}");
        assert!(facts.contains("not inside any loop body"), "{facts}");
    }

    // --- rejected shapes (machine-readable reasons) ---------------------------

    #[test]
    fn value_read_after_the_clone_is_rejected() {
        let src = "fn f() {\n    let x = make();\n    let y = x.clone();\n    use_it(&x);\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        let r = only_rejection(&o);
        assert_eq!(r.reason, "cloned_value_read_later");
        assert!(r.detail.contains("var=x"), "{}", r.detail);
    }

    #[test]
    fn clone_inside_for_loop_is_rejected() {
        let src = "fn f(xs: Vec<i32>) {\n    let x = make();\n    for _i in xs {\n        sink(x.clone());\n    }\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert_eq!(only_rejection(&o).reason, "clone_in_loop");
    }

    #[test]
    fn clone_inside_while_loop_is_rejected() {
        let src = "fn f(c: bool) {\n    let x = make();\n    while c {\n        sink(x.clone());\n    }\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert_eq!(only_rejection(&o).reason, "clone_in_loop");
    }

    #[test]
    fn field_clone_is_rejected() {
        let src = "fn f() {\n    let a = make();\n    let y = a.b.clone();\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert_eq!(only_rejection(&o).reason, "clone_receiver_not_bare_local");
    }

    #[test]
    fn self_field_clone_is_rejected() {
        let src = "fn f(&self) {\n    sink(self.x.clone());\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert_eq!(only_rejection(&o).reason, "clone_receiver_not_bare_local");
    }

    #[test]
    fn deref_clone_is_rejected() {
        let src = "fn f(p: &Thing) {\n    let y = (*p).clone();\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert_eq!(only_rejection(&o).reason, "clone_receiver_not_bare_local");
    }

    #[test]
    fn chained_clone_is_rejected() {
        let src = "fn f() {\n    let x = make();\n    let y = x.clone().len();\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert_eq!(
            only_rejection(&o).reason,
            "clone_not_in_recognized_position"
        );
    }

    #[test]
    fn macro_argument_clone_is_rejected() {
        // A macro may expand its argument zero or many times — never licensed.
        let src = "fn f() {\n    let x = make();\n    println!(\"{}\", x.clone());\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert_eq!(
            only_rejection(&o).reason,
            "clone_not_in_recognized_position"
        );
    }

    #[test]
    fn method_call_argument_clone_is_rejected() {
        // `obj.method(x.clone())` — the callee is not a plain path (v1 scope).
        let src =
            "fn f() {\n    let x = make();\n    let obj = build();\n    obj.push(x.clone());\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert_eq!(
            only_rejection(&o).reason,
            "clone_not_in_recognized_position"
        );
    }

    #[test]
    fn return_position_clone_is_rejected() {
        let src = "fn f() -> Thing {\n    let x = make();\n    return x.clone();\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert_eq!(
            only_rejection(&o).reason,
            "clone_not_in_recognized_position"
        );
    }

    #[test]
    fn closure_body_clone_is_rejected() {
        // Inside a closure the clone may run repeatedly; the RHS shape gate
        // refuses anything that is not exactly `x.clone()`.
        let src =
            "fn f() {\n    let x = make();\n    let g = move || sink(x.clone());\n    g();\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert_eq!(
            only_rejection(&o).reason,
            "clone_not_in_recognized_position"
        );
    }

    #[test]
    fn parameter_receiver_is_rejected() {
        // A parameter may be a reference; its binding mode is a claim this
        // rule does not make.
        let src = "fn f(x: String) {\n    let y = x.clone();\n    use_it(y);\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert_eq!(only_rejection(&o).reason, "receiver_def_not_single_let");
    }

    #[test]
    fn merged_redefinition_is_rejected() {
        let src = "fn f(c: bool) {\n    let mut x = a();\n    if c {\n        x = b();\n    }\n    let y = x.clone();\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert_eq!(only_rejection(&o).reason, "receiver_def_not_single_let");
    }

    #[test]
    fn destructured_definition_is_rejected() {
        let src = "fn f() {\n    let (x, z) = pair();\n    let y = x.clone();\n    use_it(z);\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert_eq!(only_rejection(&o).reason, "receiver_def_not_bare_let");
    }

    #[test]
    fn receiver_reused_in_the_same_statement_is_rejected() {
        let src = "fn f() {\n    let x = make();\n    take(x.clone(), &x);\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert_eq!(only_rejection(&o).reason, "receiver_reused_in_statement");
    }

    #[test]
    fn rebinding_the_same_name_is_rejected() {
        // `let x = x.clone();` — the binder is a second occurrence of `x`.
        let src = "fn f() {\n    let x = make();\n    let x = x.clone();\n    use_it(x);\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert_eq!(only_rejection(&o).reason, "receiver_reused_in_statement");
    }

    #[test]
    fn clone_with_arguments_is_not_a_candidate() {
        let src = "fn f() {\n    let x = make();\n    let y = x.clone(depth);\n    use_it(y);\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert!(o.edits.is_empty());
        assert!(o.rejections.is_empty(), "{:?}", o.rejections);
    }

    #[test]
    fn ordinary_code_is_silent() {
        let src = "fn f(xs: Vec<i32>) {\n    for x in xs {\n        use_it(x);\n    }\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert!(o.edits.is_empty());
        assert!(o.rejections.is_empty());
    }

    #[test]
    fn proposal_is_deterministic() {
        let src = "fn f() {\n    let x = make();\n    let y = x.clone();\n    use_it(y);\n}\n";
        let (a, oa) = run(src);
        let (b, ob) = run(src);
        assert_eq!(a, b);
        assert_eq!(oa.edits, ob.edits);
        assert_eq!(oa.rejections, ob.rejections);
    }
}
