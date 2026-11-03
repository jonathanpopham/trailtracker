//! Rule 2: `loop-to-iterator` v1 (ADR-0006) — rewrite an adjacent
//! accumulator/loop statement pair into the equivalent iterator chain:
//!
//! ```text
//! S1: let mut ACC[: TYPE] = INIT;
//! S2: for X in ITER { BODY }
//! ```
//!
//! HONESTLY SCOPED: the recognizer accepts exactly the grammar below and
//! rejects every near-miss with a machine-readable reason. The body must be
//! ONE of: `ACC.method(ARGS);`, `ACC op= EXPR;`, or `if COND { <either> }`
//! (no `else`). `X` must be a single bare identifier, the loop unlabeled,
//! `ACC` unread outside receiver position, and no `?`/`break`/`continue`/
//! `return` anywhere inside — checked textually AND against the CPG's
//! `FLOWS_TO` role edges.
//!
//! Emission — exactness over elegance (ADR-0006):
//! - `push` into `Vec::new()`/`vec![]`, no `if`  → `.map(|X| ARG).collect…`
//! - `push` under `if COND`                      → `.filter_map(|X| if COND
//!   { Some(ARG) } else { None }).collect…` (the closure takes `X` by value,
//!   exactly like the loop body did — this is why not `.filter().map()`).
//! - everything else → `.fold(INIT, |mut ACC, X| { BODY ACC })`, reusing the
//!   body text verbatim (same operators, same calls, no type claims).
//!
//! `for x in xs` desugars to `IntoIterator::into_iter(xs)`, so `.into_iter()`
//! is the exact desugaring, not a style choice. The original `mut` on `ACC`
//! is preserved (the binding may be mutated after the loop); a possibly-unused
//! `mut` warning is accepted rather than risking a compile break.

use crate::core::cst::Node;
use crate::core::span::ByteSpan;
use crate::ir::cpg::{has_try_operator, reborrow, span_of, top_index, Stmt, StmtKind, E};
use crate::lang::rust::lexer::kind as tk;
use crate::rewrite::proposal::{ProposedEdit, Rejection};
use crate::rewrite::rules::{
    data_deps_from, edge_prop, flows_from, line_of, subtree_ids, text_of, FileCpg, FnUnit, Rule,
    RuleOptions, RuleOutcome,
};

pub struct LoopToIterator;

impl Rule for LoopToIterator {
    fn id(&self) -> &'static str {
        "loop-to-iterator"
    }

    fn version(&self) -> &'static str {
        "1"
    }

    fn summary(&self) -> &'static str {
        "Rewrite `let mut ACC = INIT;` + `for X in ITER { <single accumulation> }` into \
         the equivalent iterator chain (map/filter_map/fold)."
    }

    fn shapes(&self) -> &'static [&'static str] {
        &[
            "let mut A = Vec::new(); for x in I { A.push(E); }        => let mut A = I.into_iter().map(|x| E).collect::<Vec<_>>();",
            "let mut A = Vec::new(); for x in I { if C { A.push(E); } } => let mut A = I.into_iter().filter_map(|x| if C { Some(E) } else { None }).collect::<Vec<_>>();",
            "let mut A = INIT; for x in I { A op= E; }                 => let mut A = I.into_iter().fold(INIT, |mut A, x| { A op= E; A });",
            "let mut A = INIT; for x in I { A.m(E); }                  => let mut A = I.into_iter().fold(INIT, |mut A, x| { A.m(E); A });",
            "let mut A = INIT; for x in I { if C { <accumulation> } }  => fold with the `if` kept verbatim",
        ]
    }

    fn propose(&self, file: &FileCpg<'_>, _opts: &RuleOptions) -> Result<RuleOutcome, String> {
        let mut out = RuleOutcome::default();
        for f in &file.fns {
            scan_block(file, f, &f.stmts, &mut out);
        }
        out.edits.sort_by_key(|e| (e.span.start, e.span.end));
        out.rejections.sort_by_key(|r| (r.span.start, r.span.end));
        Ok(out)
    }
}

// ---------------------------------------------------------------------------
// Recognizer
// ---------------------------------------------------------------------------

/// The single accumulation statement's shape, decomposed.
struct Accum<'s, 'a> {
    /// The accumulator name (the receiver).
    acc: String,
    /// `Some(cond_els)` when wrapped in `if COND { … }` (shape c).
    cond: Option<&'s [E<'a>]>,
    /// The flat accumulation statement (`ACC.m(…);` or `ACC op= …;`).
    stmt: &'s Stmt<'a>,
    /// `Some((method, args_group))` for shape (a); `None` for shape (b).
    method: Option<(String, &'a Node)>,
    /// The value elements read in non-receiver position: `ARGS`' tokens for
    /// (a), `EXPR`'s elements for (b). Used for the `acc_read_in_body` check.
    value_els: Vec<E<'a>>,
}

fn scan_block(file: &FileCpg<'_>, f: &FnUnit<'_>, stmts: &[Stmt<'_>], out: &mut RuleOutcome) {
    for (i, s) in stmts.iter().enumerate() {
        if s.kind == StmtKind::For {
            let prev = if i > 0 { Some(&stmts[i - 1]) } else { None };
            examine(file, f, prev, s, out);
        }
        // Descend into every nested block.
        if let Some(b) = &s.body {
            scan_block(file, f, b, out);
        }
        match &s.else_part {
            Some(crate::ir::cpg::ElsePart::Block(_, b)) => scan_block(file, f, b, out),
            Some(crate::ir::cpg::ElsePart::If(nested)) => {
                scan_block(file, f, std::slice::from_ref(nested), out)
            }
            None => {}
        }
        for arm in &s.arms {
            if let Some(b) = &arm.block {
                scan_block(file, f, b, out);
            }
        }
    }
}

/// Examine one `for` statement (with the statement preceding it at the same
/// block level, if any). Pushes at most one edit or one rejection.
fn examine(
    file: &FileCpg<'_>,
    f: &FnUnit<'_>,
    prev: Option<&Stmt<'_>>,
    s2: &Stmt<'_>,
    out: &mut RuleOutcome,
) {
    let src = file.src;

    // A site is a CANDIDATE when either side of the pair signals accumulation:
    // the body is a single accumulation statement, or the preceding statement
    // is a single-binding `let mut`. Everything else is silence, not a
    // rejection — an ordinary loop is not a near-miss.
    let accum = match_accum(src, s2);
    let prev_let = prev.filter(|p| is_single_let_mut_any(src, p));
    if accum.is_none() && prev_let.is_none() {
        return;
    }
    let span = match prev {
        Some(p) => ByteSpan::new(p.span.start as usize, s2.span.end as usize),
        None => s2.span,
    };
    let mut reject = |reason: &str, detail: String| {
        out.rejections.push(Rejection {
            span,
            reason: reason.to_string(),
            detail,
        });
    };

    let Some(accum) = accum else {
        // A shape that earns a more specific reason (e.g. `if_has_else`)
        // gets it; everything else falls into the generic bucket.
        if let Some((reason, detail)) = accum_shape_veto(src, s2) {
            reject(reason, detail);
        } else {
            reject(
                "body_not_single_accumulation",
                "the loop body is not exactly one `ACC.method(ARGS);`, `ACC op= EXPR;`, or \
                 `if COND { <either> }` statement"
                    .to_string(),
            );
        }
        return;
    };
    let acc = accum.acc.clone();

    // The loop itself: unlabeled, `X` a single bare identifier.
    if s2.label.is_some() {
        reject(
            "loop_labeled",
            format!(
                "the loop carries label `{}`; labeled loops may be break targets",
                s2.label.as_deref().unwrap_or("?")
            ),
        );
        return;
    }
    let Some(in_idx) = top_index(&s2.header, "in", src) else {
        reject(
            "loop_pattern_not_bare_ident",
            "could not find the `in` keyword in the loop header".to_string(),
        );
        return;
    };
    let x = match (in_idx, &s2.header[..in_idx]) {
        (1, [E::T(t)]) if t.kind == tk::IDENT || t.kind == tk::RAW_IDENT => {
            t.span.text(src).to_string()
        }
        _ => {
            reject(
                "loop_pattern_not_bare_ident",
                format!(
                    "the loop pattern `{}` is not a single bare identifier",
                    text_of(src, span_of(&s2.header[..in_idx]))
                ),
            );
            return;
        }
    };
    if x == acc {
        reject(
            "loop_var_shadows_acc",
            format!("the loop variable `{x}` shadows the accumulator"),
        );
        return;
    }

    // The iterable: no `?` (at any depth — a try before the loop and a try
    // inside a closure are different claims; refuse both), no `ACC`.
    let iter_els = &s2.header[in_idx + 1..];
    if iter_els.is_empty() {
        reject("loop_pattern_not_bare_ident", "empty iterable".to_string());
        return;
    }
    if tokens_contain(iter_els, "?", src) {
        reject(
            "iterable_has_try",
            "the iterable expression contains `?`".to_string(),
        );
        return;
    }
    if idents_contain(iter_els, &acc, src) {
        reject(
            "acc_in_iterable",
            format!("the iterable reads the accumulator `{acc}`"),
        );
        return;
    }

    // The accumulator definition: the IMMEDIATELY preceding statement must be
    // `let mut ACC [: TYPE] = INIT;` binding exactly ACC.
    let Some(s1) = prev else {
        reject(
            "acc_def_not_adjacent",
            format!("no statement precedes the loop; `{acc}` is defined elsewhere"),
        );
        return;
    };
    let Some(parts) = parse_let_mut(src, s1, &acc) else {
        if s1.kind == StmtKind::Let
            && let_binds_only(src, s1, &acc)
            && s1.header.get(1).and_then(|e| e.text(src)) != Some("mut")
        {
            reject(
                "acc_not_mut",
                format!("`{acc}` is bound without `mut` immediately before the loop"),
            );
        } else {
            reject(
                "acc_def_not_adjacent",
                format!(
                    "the statement immediately before the loop is not \
                     `let mut {acc} [: TYPE] = INIT;`"
                ),
            );
        }
        return;
    };

    // Nothing but whitespace may sit between the two statements: a comment in
    // the gap would be silently deleted by the pair replacement.
    let gap = &src[s1.span.end as usize..s2.span.start as usize];
    if !gap.chars().all(char::is_whitespace) {
        reject(
            "gap_not_whitespace",
            format!(
                "non-whitespace between the two statements would be deleted: {:?}",
                gap.trim()
            ),
        );
        return;
    }

    // `?` anywhere in the body (any depth): a try that exited the FUNCTION
    // would exit the CLOSURE after the rewrite — a semantic change.
    if stmt_tokens_contain(s2, "?", src) {
        reject(
            "body_has_try",
            "the loop body contains `?`; inside a closure it would exit the closure, \
             not the function"
                .to_string(),
        );
        return;
    }

    // `ACC` read outside receiver position (in ARGS / EXPR / COND).
    if idents_contain(&accum.value_els, &acc, src)
        || accum.cond.is_some_and(|c| idents_contain(c, &acc, src))
    {
        reject(
            "acc_read_in_body",
            format!("the accumulator `{acc}` is read outside receiver position in the body"),
        );
        return;
    }
    if let Some(cond) = accum.cond {
        if has_try_operator(cond, src) || tokens_contain(cond, "?", src) {
            reject(
                "condition_has_try",
                "the `if` condition contains `?`".to_string(),
            );
            return;
        }
    }

    // --- CPG checks (belt-and-braces over the textual grammar) --------------
    let body_ids = s2.body.as_ref().map(|b| subtree_ids(b)).unwrap_or_default();
    let mut edge_ids = body_ids.clone();
    if let Some(id) = &s2.id {
        edge_ids.push(id.clone());
    }
    let bad_exit: Vec<String> = flows_from(&file.graph, &edge_ids)
        .iter()
        .filter_map(|e| {
            let role = edge_prop(e, "role").unwrap_or("-");
            matches!(role, "break" | "continue" | "return" | "try-exit")
                .then(|| format!("FLOWS_TO role={role}: {} -> {}", e.from, e.to))
        })
        .collect();
    if !bad_exit.is_empty() {
        reject(
            "body_has_early_exit",
            format!("the CPG records early-exit flow: {}", bad_exit.join("; ")),
        );
        return;
    }
    let s1_id = s1.id.clone().unwrap_or_default();
    let acc_dep_edges: Vec<String> = data_deps_from(&file.graph, &body_ids)
        .iter()
        .filter(|e| edge_prop(e, "var") == Some(acc.as_str()))
        .map(|e| {
            format!(
                "DATA_DEP var={acc} def={}: {} -> {}",
                edge_prop(e, "def").unwrap_or("-"),
                e.from,
                e.to
            )
        })
        .collect();
    let foreign_def = data_deps_from(&file.graph, &body_ids).iter().any(|e| {
        edge_prop(e, "var") == Some(acc.as_str()) && e.to != s1_id && !body_ids.contains(&e.to)
    });
    if foreign_def {
        reject(
            "acc_defs_not_single",
            format!("a definition of `{acc}` other than the adjacent `let` may reach the loop"),
        );
        return;
    }

    // --- Emit ----------------------------------------------------------------
    let iter_text = iterable_text(src, iter_els);
    let after = emit(src, &parts, &accum, &x, &iter_text);

    let mut facts = vec![
        format!(
            "{}: statements {s1_id} (let, line {}) and {} (for, line {}) are adjacent at \
             one block level",
            f.fn_id,
            line_of(src, s1.span.start as usize),
            s2.id.clone().unwrap_or_default(),
            line_of(src, s2.span.start as usize),
        ),
        format!(
            "accumulator `{acc}`: single reaching def at the loop = {s1_id} (`let mut`, \
             adjacent — no statement can intervene)"
        ),
        format!("loop pattern `{x}` is a single bare identifier; the loop is unlabeled"),
    ];
    facts.extend(acc_dep_edges);
    facts.push(format!(
        "no FLOWS_TO edge with role break/continue/return/try-exit leaves {{{}}}",
        edge_ids.join(", ")
    ));

    out.edits.push(ProposedEdit {
        span,
        before: text_of(src, span).to_string(),
        after,
        why_safe: format!(
            "the loop body is a single accumulation into `{acc}` (defined immediately \
             before, mutated only here, never read in the body), the body has no \
             break/continue/return/try-exit edges in the CPG, and `for` desugars to \
             `IntoIterator::into_iter`, so the iterator chain computes the identical value"
        ),
        cpg_facts: facts,
    });
}

/// Match the loop body against the accumulation grammar: exactly one statement
/// of shape (a) `ACC.method(ARGS);`, (b) `ACC op= EXPR;`, or (c) `if COND
/// { (a)|(b) }` with no `else`.
fn match_accum<'s, 'a>(src: &'a str, s2: &'s Stmt<'a>) -> Option<Accum<'s, 'a>> {
    let body = s2.body.as_ref()?;
    let [only] = body.as_slice() else {
        return None;
    };
    match only.kind {
        StmtKind::Expr => match_flat(src, only, None),
        StmtKind::If => {
            if only.else_part.is_some() {
                return None; // vetoed with `if_has_else` by accum_shape_veto
            }
            let inner_body = only.body.as_ref()?;
            let [inner] = inner_body.as_slice() else {
                return None;
            };
            if inner.kind != StmtKind::Expr {
                return None;
            }
            match_flat(src, inner, Some(only.header.as_slice()))
        }
        _ => None,
    }
}

/// Shape veto that deserves its own reason: `if … { <accumulation> } else …`.
/// (Without this, an else-carrying wrapper would fall into the generic
/// `body_not_single_accumulation` bucket — less actionable.)
fn accum_shape_veto(src: &str, s2: &Stmt<'_>) -> Option<(&'static str, String)> {
    let body = s2.body.as_ref()?;
    let [only] = body.as_slice() else {
        return None;
    };
    if only.kind == StmtKind::If && only.else_part.is_some() {
        let inner_ok = only
            .body
            .as_ref()
            .and_then(|b| match b.as_slice() {
                [inner] if inner.kind == StmtKind::Expr => match_flat(src, inner, None),
                _ => None,
            })
            .is_some();
        if inner_ok {
            return Some((
                "if_has_else",
                "the `if` wrapper has an `else`; only `if COND { <accumulation> }` \
                 (no else) is recognized"
                    .to_string(),
            ));
        }
    }
    None
}

/// Match one FLAT statement against `ACC.method(ARGS);` or `ACC op= EXPR;`.
fn match_flat<'s, 'a>(
    src: &'a str,
    stmt: &'s Stmt<'a>,
    cond: Option<&'s [E<'a>]>,
) -> Option<Accum<'s, 'a>> {
    let els = trim_semi(&stmt.header, src);
    let first = match els.first() {
        Some(E::T(t)) if t.kind == tk::IDENT || t.kind == tk::RAW_IDENT => t.span.text(src),
        _ => return None,
    };
    // (a) ACC . method ( ARGS )  — exactly four elements.
    if let [_, E::T(dot), E::T(m), E::G(g)] = els {
        if dot.span.text(src) == "."
            && (m.kind == tk::IDENT || m.kind == tk::RAW_IDENT)
            && g.kind_is_paren(src)
        {
            return Some(Accum {
                acc: first.to_string(),
                cond,
                stmt,
                method: Some((m.span.text(src).to_string(), g)),
                value_els: crate::ir::cpg::elems(g),
            });
        }
    }
    // (b) ACC op= EXPR
    const COMPOUND: &[&str] = &["+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>="];
    if els.len() >= 3 {
        if let E::T(op) = &els[1] {
            if COMPOUND.contains(&op.span.text(src)) {
                return Some(Accum {
                    acc: first.to_string(),
                    cond,
                    stmt,
                    method: None,
                    value_els: els[2..].iter().map(reborrow).collect(),
                });
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// The `let mut` side
// ---------------------------------------------------------------------------

/// The decomposed `let mut ACC [: TYPE] = INIT;` statement.
struct LetParts {
    acc: String,
    /// The `TYPE` text when an ascription is present.
    ty: Option<String>,
    /// The `INIT` expression text, verbatim.
    init: String,
}

/// Parse `s1` as `let mut ACC [: TYPE] = INIT;` binding exactly `acc`.
fn parse_let_mut(src: &str, s1: &Stmt<'_>, acc: &str) -> Option<LetParts> {
    if s1.kind != StmtKind::Let {
        return None;
    }
    let h = &s1.header;
    if h.first()?.text(src)? != "let" || h.get(1)?.text(src)? != "mut" {
        return None;
    }
    let name = match h.get(2) {
        Some(E::T(t)) if t.kind == tk::IDENT || t.kind == tk::RAW_IDENT => t.span.text(src),
        _ => return None,
    };
    if name != acc {
        return None;
    }
    let eq = top_index(h, "=", src)?;
    let ty = match h.get(3).and_then(|e| e.text(src)) {
        Some(":") if eq > 4 => Some(text_of(src, span_of(&h[4..eq])).to_string()),
        Some(":") => return None, // `let mut x: = …` — malformed
        Some("=") if eq == 3 => None,
        _ => return None, // extra tokens between the name and `:`/`=`
    };
    let init_els = trim_semi(&h[eq + 1..], src);
    if init_els.is_empty() {
        return None;
    }
    Some(LetParts {
        acc: acc.to_string(),
        ty,
        init: text_of(src, span_of(init_els)).to_string(),
    })
}

/// Does a `let` statement bind exactly `{name}` (any mutability)?
fn let_binds_only(src: &str, s1: &Stmt<'_>, name: &str) -> bool {
    let h = &s1.header;
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

/// Is `p` a single-binding `let mut NAME … = …;` statement (the candidacy
/// signal from the definition side)?
fn is_single_let_mut_any(src: &str, p: &Stmt<'_>) -> bool {
    p.kind == StmtKind::Let
        && p.header.get(1).and_then(|e| e.text(src)) == Some("mut")
        && matches!(p.header.get(2), Some(E::T(t)) if t.kind == tk::IDENT || t.kind == tk::RAW_IDENT)
        && matches!(
            p.header.get(3).and_then(|e| e.text(src)),
            Some(":") | Some("=")
        )
}

// ---------------------------------------------------------------------------
// Emitter
// ---------------------------------------------------------------------------

/// Build the replacement statement text.
fn emit(src: &str, parts: &LetParts, accum: &Accum<'_, '_>, x: &str, iter: &str) -> String {
    let acc = &parts.acc;
    let ty_part = parts
        .ty
        .as_ref()
        .map(|t| format!(": {t}"))
        .unwrap_or_default();
    // The push special case: map / filter_map + collect.
    let is_vec_init = matches!(parts.init.as_str(), "Vec::new()" | "vec![]");
    if let Some((method, group)) = &accum.method {
        if method == "push" && is_vec_init && single_argument(group, src) {
            let arg = group_inner_text(group, src);
            let collect = if parts.ty.is_some() {
                ".collect()"
            } else {
                ".collect::<Vec<_>>()"
            };
            return match accum.cond {
                None => format!(
                    "let mut {acc}{ty_part} = {iter}.into_iter().map(|{x}| {arg}){collect};"
                ),
                Some(cond) => {
                    let cond_text = text_of(src, span_of(cond));
                    format!(
                        "let mut {acc}{ty_part} = {iter}.into_iter()\
                         .filter_map(|{x}| if {cond_text} {{ Some({arg}) }} else {{ None }})\
                         {collect};"
                    )
                }
            };
        }
    }
    // Everything else: the fold form, body text verbatim. For shape (c) the
    // verbatim body is the whole `if COND { … }` wrapper statement.
    let body_text = match accum.cond {
        None => text_of(src, accum.stmt.span).to_string(),
        Some(cond) => {
            let inner = text_of(src, accum.stmt.span);
            let cond_text = text_of(src, span_of(cond));
            format!("if {cond_text} {{ {inner} }}")
        }
    };
    format!(
        "let mut {acc}{ty_part} = {iter}.into_iter().fold({init}, |mut {acc}, {x}| \
         {{ {body_text} {acc} }});",
        init = parts.init
    )
}

/// The iterable text, parenthesized when its depth-0 elements include
/// anything that binds looser than a method call (`0..n`, `&xs`, casts, …).
/// `(EXPR).into_iter()` is always correct; bare is used only for the safe set
/// (identifiers, literals, `.`/`::` chains, and balanced groups).
fn iterable_text(src: &str, els: &[E<'_>]) -> String {
    let safe = els.iter().all(|e| match e {
        E::G(_) => true,
        E::T(t) => {
            matches!(
                t.kind,
                tk::IDENT
                    | tk::RAW_IDENT
                    | tk::INT
                    | tk::FLOAT
                    | tk::CHAR
                    | tk::BYTE
                    | tk::STRING
                    | tk::BYTE_STRING
                    | tk::C_STRING
            ) || matches!(t.span.text(src), "." | "::")
        }
    });
    let text = text_of(src, span_of(els));
    if safe {
        text.to_string()
    } else {
        format!("({text})")
    }
}

// ---------------------------------------------------------------------------
// Token scans
// ---------------------------------------------------------------------------

/// Drop a trailing `;` element.
fn trim_semi<'e, 'a>(els: &'e [E<'a>], src: &str) -> &'e [E<'a>] {
    match els.last() {
        Some(e) if e.text(src) == Some(";") => &els[..els.len() - 1],
        _ => els,
    }
}

/// Any token (at any depth) with exactly this text?
fn tokens_contain(els: &[E<'_>], what: &str, src: &str) -> bool {
    crate::ir::cpg::flat_tokens(els)
        .iter()
        .any(|t| t.span.text(src) == what)
}

/// Any token at any depth under a whole statement subtree with this text?
fn stmt_tokens_contain(s: &Stmt<'_>, what: &str, src: &str) -> bool {
    text_of(src, s.span).contains(what) && {
        // `contains` is a fast pre-filter; confirm on real tokens so `?`
        // inside a string/comment does not trigger.
        let mut hit = false;
        crate::rewrite::rules::walk_stmt(s, &mut |st| {
            if tokens_contain(&st.header, what, src) {
                hit = true;
            }
            for arm in &st.arms {
                if tokens_contain(&arm.pattern, what, src) || tokens_contain(&arm.expr, what, src) {
                    hit = true;
                }
            }
        });
        hit
    }
}

/// Any IDENT/RAW_IDENT token (at any depth) named `name`?
fn idents_contain(els: &[E<'_>], name: &str, src: &str) -> bool {
    crate::ir::cpg::flat_tokens(els)
        .iter()
        .any(|t| (t.kind == tk::IDENT || t.kind == tk::RAW_IDENT) && t.span.text(src) == name)
}

/// Exactly one argument: the paren group's depth-0 elements contain no `,`
/// and at least one non-delimiter element.
fn single_argument(group: &Node, src: &str) -> bool {
    let inner = paren_inner(group, src);
    !inner.is_empty() && !inner.iter().any(|e| e.text(src) == Some(","))
}

/// A paren group's elements without the `(` `)` delimiters.
fn paren_inner<'a>(group: &'a Node, src: &str) -> Vec<E<'a>> {
    let mut v = crate::ir::cpg::elems(group);
    if v.first().and_then(|e| e.text(src)) == Some("(") {
        v.remove(0);
    }
    if v.last().and_then(|e| e.text(src)) == Some(")") {
        v.pop();
    }
    v
}

/// The verbatim text between a paren group's delimiters, trimmed.
fn group_inner_text<'a>(group: &Node, src: &'a str) -> &'a str {
    src[group.span.start as usize + 1..group.span.end as usize - 1].trim()
}

// A tiny CST convenience: is this group parenthesized?
trait ParenCheck {
    fn kind_is_paren(&self, src: &str) -> bool;
}
impl ParenCheck for Node {
    fn kind_is_paren(&self, src: &str) -> bool {
        src.as_bytes().get(self.span.start as usize) == Some(&b'(')
    }
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
        let out = LoopToIterator
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

    // --- accepted shapes ----------------------------------------------------

    #[test]
    fn push_into_vec_new_becomes_map_collect() {
        let src = "fn f(xs: Vec<i32>) {\n    let mut out = Vec::new();\n    for x in xs {\n        out.push(x * 2);\n    }\n    use_it(out);\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1);
        assert_eq!(
            out,
            "fn f(xs: Vec<i32>) {\n    let mut out = xs.into_iter().map(|x| x * 2).collect::<Vec<_>>();\n    use_it(out);\n}\n"
        );
    }

    #[test]
    fn push_with_type_ascription_uses_plain_collect() {
        let src = "fn f(xs: Vec<i32>) {\n    let mut out: Vec<i32> = Vec::new();\n    for x in xs {\n        out.push(x + 1);\n    }\n}\n";
        let (out, _) = run(src);
        assert_eq!(
            out,
            "fn f(xs: Vec<i32>) {\n    let mut out: Vec<i32> = xs.into_iter().map(|x| x + 1).collect();\n}\n"
        );
    }

    #[test]
    fn conditional_push_becomes_filter_map() {
        let src = "fn f(xs: Vec<i32>) {\n    let mut out = Vec::new();\n    for x in xs {\n        if x > 0 {\n            out.push(x * 2);\n        }\n    }\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1);
        assert_eq!(
            out,
            "fn f(xs: Vec<i32>) {\n    let mut out = xs.into_iter().filter_map(|x| if x > 0 { Some(x * 2) } else { None }).collect::<Vec<_>>();\n}\n"
        );
    }

    #[test]
    fn compound_assign_becomes_fold() {
        let src = "fn f(xs: Vec<i32>) {\n    let mut sum = 0;\n    for x in xs {\n        sum += x;\n    }\n    use_it(sum);\n}\n";
        let (out, _) = run(src);
        assert_eq!(
            out,
            "fn f(xs: Vec<i32>) {\n    let mut sum = xs.into_iter().fold(0, |mut sum, x| { sum += x; sum });\n    use_it(sum);\n}\n"
        );
    }

    #[test]
    fn method_accumulation_becomes_fold() {
        let src = "fn f(xs: Vec<i32>) {\n    let mut set = HashSet::new();\n    for x in xs {\n        set.insert(x);\n    }\n}\n";
        let (out, _) = run(src);
        assert_eq!(
            out,
            "fn f(xs: Vec<i32>) {\n    let mut set = xs.into_iter().fold(HashSet::new(), |mut set, x| { set.insert(x); set });\n}\n"
        );
    }

    #[test]
    fn conditional_compound_becomes_fold_with_if() {
        let src = "fn f(xs: Vec<i32>) {\n    let mut sum = 0;\n    for x in xs {\n        if x > 0 { sum += x; }\n    }\n}\n";
        let (out, _) = run(src);
        assert_eq!(
            out,
            "fn f(xs: Vec<i32>) {\n    let mut sum = xs.into_iter().fold(0, |mut sum, x| { if x > 0 { sum += x; } sum });\n}\n"
        );
    }

    #[test]
    fn range_iterable_is_parenthesized() {
        let src = "fn f(n: i32) {\n    let mut sum = 0;\n    for x in 0..n {\n        sum += x;\n    }\n}\n";
        let (out, _) = run(src);
        assert_eq!(
            out,
            "fn f(n: i32) {\n    let mut sum = (0..n).into_iter().fold(0, |mut sum, x| { sum += x; sum });\n}\n"
        );
    }

    #[test]
    fn method_chain_iterable_stays_bare() {
        let src = "fn f(xs: Vec<i32>) {\n    let mut out = Vec::new();\n    for x in xs.iter() {\n        out.push(x);\n    }\n}\n";
        let (out, _) = run(src);
        assert!(out.contains("xs.iter().into_iter().map(|x| x)"), "{out}");
    }

    #[test]
    fn why_safe_cites_cpg_facts() {
        let src = "fn f(xs: Vec<i32>) {\n    let mut sum = 0;\n    for x in xs {\n        sum += x;\n    }\n}\n";
        let (_, o) = run(src);
        let e = &o.edits[0];
        assert!(
            e.why_safe.contains("IntoIterator::into_iter"),
            "{}",
            e.why_safe
        );
        let facts = e.cpg_facts.join("\n");
        assert!(facts.contains("fn::f#1"), "{facts}");
        assert!(facts.contains("adjacent"), "{facts}");
        assert!(
            facts.contains("no FLOWS_TO edge with role break/continue/return/try-exit"),
            "{facts}"
        );
        assert!(facts.contains("DATA_DEP var=sum"), "{facts}");
    }

    #[test]
    fn candidate_inside_nested_block_is_found() {
        let src = "fn f(c: bool, xs: Vec<i32>) {\n    if c {\n        let mut out = Vec::new();\n        for x in xs {\n            out.push(x);\n        }\n    }\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1);
        assert!(out.contains(".map(|x| x).collect::<Vec<_>>()"), "{out}");
    }

    // --- rejected shapes (machine-readable reasons) --------------------------

    #[test]
    fn multi_statement_body_is_rejected() {
        let src = "fn f(xs: Vec<i32>) {\n    let mut out = Vec::new();\n    for x in xs {\n        log(x);\n        out.push(x);\n    }\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert_eq!(only_rejection(&o).reason, "body_not_single_accumulation");
    }

    #[test]
    fn if_with_else_is_rejected() {
        let src = "fn f(xs: Vec<i32>) {\n    let mut out = Vec::new();\n    for x in xs {\n        if x > 0 { out.push(x); } else { skip(); }\n    }\n}\n";
        let (_, o) = run(src);
        assert_eq!(only_rejection(&o).reason, "if_has_else");
    }

    #[test]
    fn acc_read_in_body_is_rejected() {
        let src = "fn f(xs: Vec<i32>) {\n    let mut out = Vec::new();\n    for x in xs {\n        out.push(out.len());\n    }\n}\n";
        let (_, o) = run(src);
        assert_eq!(only_rejection(&o).reason, "acc_read_in_body");
    }

    #[test]
    fn acc_in_iterable_is_rejected() {
        let src = "fn f() {\n    let mut out = Vec::new();\n    for x in out.clone() {\n        out.push(x);\n    }\n}\n";
        let (_, o) = run(src);
        assert_eq!(only_rejection(&o).reason, "acc_in_iterable");
    }

    #[test]
    fn labeled_loop_is_rejected() {
        let src = "fn f(xs: Vec<i32>) {\n    let mut out = Vec::new();\n    'outer: for x in xs {\n        out.push(x);\n    }\n}\n";
        let (_, o) = run(src);
        assert_eq!(only_rejection(&o).reason, "loop_labeled");
    }

    #[test]
    fn tuple_pattern_is_rejected() {
        let src = "fn f(xs: Vec<(i32, i32)>) {\n    let mut out = Vec::new();\n    for (a, b) in xs {\n        out.push(a);\n    }\n}\n";
        let (_, o) = run(src);
        assert_eq!(only_rejection(&o).reason, "loop_pattern_not_bare_ident");
    }

    #[test]
    fn loop_var_shadowing_acc_is_rejected() {
        let src = "fn f(xs: Vec<i32>) {\n    let mut v = Vec::new();\n    for v in xs {\n        v.push(1);\n    }\n}\n";
        let (_, o) = run(src);
        assert_eq!(only_rejection(&o).reason, "loop_var_shadows_acc");
    }

    #[test]
    fn immutable_binding_is_rejected() {
        let src = "fn f(xs: Vec<i32>) {\n    let out = Vec::new();\n    for x in xs {\n        out.push(x);\n    }\n}\n";
        let (_, o) = run(src);
        assert_eq!(only_rejection(&o).reason, "acc_not_mut");
    }

    #[test]
    fn non_adjacent_definition_is_rejected() {
        let src = "fn f(xs: Vec<i32>) {\n    let mut out = Vec::new();\n    other();\n    for x in xs {\n        out.push(x);\n    }\n}\n";
        let (_, o) = run(src);
        assert_eq!(only_rejection(&o).reason, "acc_def_not_adjacent");
    }

    #[test]
    fn comment_in_gap_is_rejected() {
        let src = "fn f(xs: Vec<i32>) {\n    let mut out = Vec::new();\n    // do not lose me\n    for x in xs {\n        out.push(x);\n    }\n}\n";
        let (_, o) = run(src);
        assert_eq!(only_rejection(&o).reason, "gap_not_whitespace");
    }

    #[test]
    fn try_in_body_is_rejected() {
        let src = "fn f(xs: Vec<String>) -> Result<(), E> {\n    let mut out = Vec::new();\n    for x in xs {\n        out.push(x.parse()?);\n    }\n    Ok(())\n}\n";
        let (_, o) = run(src);
        assert_eq!(only_rejection(&o).reason, "body_has_try");
    }

    #[test]
    fn try_in_iterable_is_rejected() {
        let src = "fn f() -> Result<(), E> {\n    let mut out = Vec::new();\n    for x in get()? {\n        out.push(x);\n    }\n    Ok(())\n}\n";
        let (_, o) = run(src);
        assert_eq!(only_rejection(&o).reason, "iterable_has_try");
    }

    #[test]
    fn break_in_body_is_rejected_not_rewritten() {
        // Textually this is two statements, so the grammar refuses before the
        // CPG check does — the point is that NO break-carrying loop is
        // rewritten, under either detector.
        let src = "fn f(xs: Vec<i32>) {\n    let mut out = Vec::new();\n    for x in xs {\n        if x > 9 { break; }\n        out.push(x);\n    }\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert_eq!(only_rejection(&o).reason, "body_not_single_accumulation");
    }

    #[test]
    fn ordinary_loop_is_silent_not_a_near_miss() {
        let src = "fn f(xs: Vec<i32>) {\n    for x in xs {\n        do_it(x);\n    }\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert!(o.edits.is_empty());
        assert!(o.rejections.is_empty());
    }

    #[test]
    fn proposal_is_deterministic() {
        let src = "fn f(xs: Vec<i32>) {\n    let mut sum = 0;\n    for x in xs {\n        sum += x;\n    }\n}\n";
        let (a, oa) = run(src);
        let (b, ob) = run(src);
        assert_eq!(a, b);
        assert_eq!(oa.edits, ob.edits);
    }
}
