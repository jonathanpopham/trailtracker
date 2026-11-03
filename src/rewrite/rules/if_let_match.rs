//! Rule 5: `if-let-to-match` v1 (ADR-0006) — desugar a statement-position
//! `if let PAT = PLACE { A } else { B }` into the `match` it is sugar for:
//! `match PLACE { PAT => { A } _ => { B } }`.
//!
//! `if let … else` is defined by the language as exactly this match; the
//! rewrite reuses every sub-expression verbatim (pattern, scrutinee, both
//! brace groups), so token streams, evaluation order, and binding semantics
//! are identical by construction.
//!
//! The one honest caveat is temporary drop order: since Rust 2024, an
//! `if let` drops scrutinee temporaries before the `else` block runs, while
//! a `match` holds them for the whole statement. This rule therefore
//! recognizes only scrutinees that are **place expressions** — a bare path
//! of identifiers, `self`, field accesses (`a.b`, `t.0`), and `::` segments,
//! with no groups (no calls, no indexing, no parens). A place creates no
//! temporary, so the two forms are drop-order identical in every edition.
//! Anything else is a near-miss rejection, never a guess.
//!
//! Nesting: only OUTERMOST candidates are emitted per pass (inner spans
//! would shift under the outer edit); re-running propose reaches newly
//! exposed sites. Else-position sites (`… else if let …`) are rejected:
//! `else match { … }` is not grammatical Rust.

use crate::ir::cpg::{span_of, ElsePart, Stmt, StmtKind, E};
use crate::lang::rust::lexer::kind as tk;
use crate::rewrite::proposal::{ProposedEdit, Rejection};
use crate::rewrite::rules::{
    flows_from, line_indent, line_of, text_of, FileCpg, FnUnit, Rule, RuleOptions, RuleOutcome,
};

pub struct IfLetToMatch;

impl Rule for IfLetToMatch {
    fn id(&self) -> &'static str {
        "if-let-to-match"
    }

    fn version(&self) -> &'static str {
        "1"
    }

    fn summary(&self) -> &'static str {
        "Desugar statement-position `if let PAT = PLACE { A } else { B }` into the \
         `match` it is sugar for, reusing pattern, scrutinee, and both blocks verbatim."
    }

    fn shapes(&self) -> &'static [&'static str] {
        &[
            "if let PAT = PLACE { A } else { B }  => match PLACE { PAT => { A } _ => { B } }",
            "PLACE: identifiers/`self` joined by `.`/`::` (tuple fields allowed) — no calls,\
             \n       no indexing, no parens (place expressions carry no temporaries)",
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

/// What the recognizer concluded about one `if` statement.
enum Verdict {
    /// Not an `if let … else { … }` at all (or a shape too common to nag
    /// about, like a bare `if let` without `else`): stay silent.
    NotCandidate,
    /// Looks like the shape but breaks a constraint: machine-readable no.
    Reject(&'static str, String),
    /// Recognized: the index of the top-level `=` splitting PAT from PLACE.
    Recognized { eq: usize },
}

/// Classify one statement against the recognized grammar. `else_position`
/// is true when `s` is the `if` of an `else if` continuation.
fn classify(file: &FileCpg<'_>, s: &Stmt<'_>, else_position: bool) -> Verdict {
    if s.kind != StmtKind::If || s.header.first().and_then(|e| e.text(file.src)) != Some("let") {
        return Verdict::NotCandidate;
    }
    let src = file.src;
    let lets = s
        .header
        .iter()
        .filter(|e| e.text(src) == Some("let"))
        .count();
    if lets > 1 {
        return Verdict::Reject(
            "let_chain_condition",
            "the condition chains more than one `let`; a let-chain has no single-match \
             desugar this rule recognizes"
                .to_string(),
        );
    }
    match &s.else_part {
        Some(ElsePart::Block(_, _)) => {}
        Some(ElsePart::If(_)) => {
            return Verdict::Reject(
                "else_if_chain",
                "the `else if` continuation has no arm-shaped desugar; only \
                 `if let … else { … }` is recognized"
                    .to_string(),
            );
        }
        // Bare `if let` (no else) is ubiquitous, legitimate Rust — silent.
        None => return Verdict::NotCandidate,
    }
    if else_position {
        return Verdict::Reject(
            "else_position",
            "`else match { … }` is not grammatical Rust; an else-position site cannot \
             be desugared in place"
                .to_string(),
        );
    }
    let Some(eq) = s
        .header
        .iter()
        .position(|e| e.text(src) == Some("="))
        .filter(|&i| i > 1 && i + 1 < s.header.len())
    else {
        return Verdict::NotCandidate;
    };
    let scrutinee = &s.header[eq + 1..];
    if !scrutinee.iter().all(|e| is_place_token(e, src)) {
        return Verdict::Reject(
            "scrutinee_not_a_simple_place",
            format!(
                "the scrutinee `{}` is not a bare place expression (identifiers, `self`, \
                 `.`/`::` segments, tuple fields); a non-place scrutinee may create \
                 temporaries whose drop order differs between `if let` and `match` \
                 (Rust 2024 temporary scopes)",
                text_of(src, span_of(scrutinee))
            ),
        );
    }
    Verdict::Recognized { eq }
}

/// One token of a place expression: an identifier, `self`, a `.` or `::`
/// separator, or an integer tuple-field index. Groups (calls, indexing,
/// parens) and every other token disqualify.
fn is_place_token(e: &E<'_>, src: &str) -> bool {
    match e {
        E::G(_) => false,
        E::T(t) => {
            t.kind == tk::IDENT
                || t.kind == tk::RAW_IDENT
                || t.kind == tk::INT
                || matches!(t.span.text(src), "." | "::" | "self")
        }
    }
}

fn scan_block(file: &FileCpg<'_>, f: &FnUnit<'_>, stmts: &[Stmt<'_>], out: &mut RuleOutcome) {
    for s in stmts {
        scan_stmt(file, f, s, false, out);
    }
}

fn scan_stmt(
    file: &FileCpg<'_>,
    f: &FnUnit<'_>,
    s: &Stmt<'_>,
    else_position: bool,
    out: &mut RuleOutcome,
) {
    match classify(file, s, else_position) {
        Verdict::Recognized { eq } => {
            if let Some(edit) = desugar(file, f, s, eq) {
                out.edits.push(edit);
                return; // outermost only: inner spans shift under this edit
            }
        }
        Verdict::Reject(reason, detail) => {
            out.rejections.push(Rejection {
                span: span_of(&s.header),
                reason: reason.to_string(),
                detail,
            });
        }
        Verdict::NotCandidate => {}
    }
    // Descend.
    if let Some(b) = &s.body {
        scan_block(file, f, b, out);
    }
    match &s.else_part {
        Some(ElsePart::Block(_, b)) => scan_block(file, f, b, out),
        Some(ElsePart::If(nested)) => scan_stmt(file, f, nested, true, out),
        None => {}
    }
    for arm in &s.arms {
        if let Some(b) = &arm.block {
            scan_block(file, f, b, out);
        }
    }
}

/// Build the desugaring edit for a recognized site.
fn desugar(file: &FileCpg<'_>, f: &FnUnit<'_>, s: &Stmt<'_>, eq: usize) -> Option<ProposedEdit> {
    let src = file.src;
    let pat = text_of(src, span_of(&s.header[1..eq]));
    let scrut = text_of(src, span_of(&s.header[eq + 1..]));
    let then_group = s.body_group?;
    let Some(ElsePart::Block(else_group, _)) = &s.else_part else {
        return None; // defensive: classify() already required the block
    };
    let indent = line_indent(src, s.span.start as usize);
    let after = format!(
        "match {scrut} {{\n{indent}    {pat} => {then}\n{indent}    _ => {els}\n{indent}}}",
        then = text_of(src, then_group.span),
        els = text_of(src, else_group.span),
    );

    let sid = s.id.clone().unwrap_or_default();
    let scrut_span = span_of(&s.header[eq + 1..]);
    let branch_edges: Vec<String> = flows_from(&file.graph, std::slice::from_ref(&sid))
        .iter()
        .map(|e| {
            let branch = super::edge_prop(e, "branch").unwrap_or("-");
            format!(
                "FLOWS_TO role=branch branch={branch}: {} -> {}",
                e.from, e.to
            )
        })
        .collect();

    let mut facts = vec![
        format!("{}: statement {sid} (stmt_kind=if, `let` header)", f.fn_id),
        format!(
            "scrutinee `{scrut}` at bytes {}..{} (line {}) is a place expression — \
             identifiers/`self`/`.`/`::`/tuple-field tokens only, no groups — so it \
             creates no temporaries and drop order is identical in both forms",
            scrut_span.start,
            scrut_span.end,
            line_of(src, scrut_span.start as usize)
        ),
        format!(
            "pattern `{pat}` and both brace groups are reused verbatim: the `then` \
             block becomes the `{pat} =>` arm, the `else` block becomes the `_ =>` arm"
        ),
    ];
    facts.extend(branch_edges);

    Some(ProposedEdit {
        span: s.span,
        before: text_of(src, s.span).to_string(),
        after,
        why_safe: format!(
            "`if let {pat} = {scrut} {{ … }} else {{ … }}` is the language-defined sugar \
             for `match {scrut} {{ {pat} => {{ … }} _ => {{ … }} }}`; every sub-expression \
             is reused verbatim and the scrutinee is a place expression (no temporaries), \
             so control flow, bindings, evaluation order, and drop order are identical"
        ),
        cpg_facts: facts,
    })
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
        let out = IfLetToMatch
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

    #[test]
    fn basic_if_let_else_desugars_to_match() {
        let src = "fn f(o: Option<i32>) {\n    if let Some(x) = o { use_it(x); } else { fallback(); }\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1);
        assert_eq!(
            out,
            "fn f(o: Option<i32>) {\n    match o {\n        Some(x) => { use_it(x); }\n        _ => { fallback(); }\n    }\n}\n"
        );
        // The rewritten file still parses losslessly.
        assert!(parse("t.rs", &out).is_lossless());
    }

    #[test]
    fn tail_expression_position_keeps_the_value() {
        let src = "fn f(o: Option<i32>) -> i32 {\n    if let Some(x) = o { x } else { 0 }\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1);
        assert_eq!(
            out,
            "fn f(o: Option<i32>) -> i32 {\n    match o {\n        Some(x) => { x }\n        _ => { 0 }\n    }\n}\n"
        );
    }

    #[test]
    fn field_and_path_scrutinees_are_places() {
        let src = "fn f(s: S) {\n    if let Some(x) = s.field { a(x); } else { b(); }\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1);
        assert!(out.contains("match s.field {"), "{out}");
        let src2 =
            "fn g(t: (Option<u8>, u8)) {\n    if let Some(x) = t.0 { a(x); } else { b(); }\n}\n";
        let (out2, o2) = run(src2);
        assert_eq!(o2.edits.len(), 1);
        assert!(out2.contains("match t.0 {"), "{out2}");
    }

    #[test]
    fn multi_line_blocks_are_reused_verbatim() {
        let src = "fn f(o: Option<i32>) {\n    if let Some(x) = o {\n        a(x);\n        b(x);\n    } else {\n        c();\n    }\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1);
        assert!(
            out.contains("Some(x) => {\n        a(x);\n        b(x);\n    }"),
            "then block must be byte-verbatim: {out}"
        );
        assert!(parse("t.rs", &out).is_lossless());
    }

    #[test]
    fn bare_if_let_is_silent() {
        let src = "fn f(o: Option<i32>) {\n    if let Some(x) = o { use_it(x); }\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert!(o.edits.is_empty());
        assert!(o.rejections.is_empty(), "bare if-let is not a near-miss");
    }

    #[test]
    fn call_scrutinee_is_rejected() {
        let src = "fn f() {\n    if let Some(x) = get() { a(x); } else { b(); }\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert!(o.edits.is_empty());
        assert_eq!(o.rejections.len(), 1);
        assert_eq!(o.rejections[0].reason, "scrutinee_not_a_simple_place");
    }

    #[test]
    fn method_chain_scrutinee_is_rejected() {
        let src =
            "fn f(m: M) {\n    if let Ok(g) = m.lock().map(|x| x) { a(g); } else { b(); }\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert_eq!(o.rejections.len(), 1);
        assert_eq!(o.rejections[0].reason, "scrutinee_not_a_simple_place");
    }

    #[test]
    fn else_if_chain_is_rejected() {
        let src = "fn f(o: Option<i32>) {\n    if let Some(x) = o { a(x); } else if cond() { b(); } else { c(); }\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert!(o.edits.is_empty());
        assert_eq!(o.rejections[0].reason, "else_if_chain");
    }

    #[test]
    fn else_position_is_rejected() {
        let src = "fn f(c: bool, o: Option<i32>) {\n    if c { a(); } else if let Some(x) = o { b(x); } else { d(); }\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert!(o.edits.is_empty());
        assert_eq!(o.rejections[0].reason, "else_position");
    }

    #[test]
    fn let_chain_is_rejected() {
        let src = "fn f(a: Option<i32>, b: Option<i32>) {\n    if let Some(x) = a && let Some(y) = b { c(x, y); } else { d(); }\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert!(o.edits.is_empty());
        assert_eq!(o.rejections[0].reason, "let_chain_condition");
    }

    #[test]
    fn plain_if_is_not_a_candidate() {
        let src = "fn f(c: bool) {\n    if c { a(); } else { b(); }\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert!(o.edits.is_empty());
        assert!(o.rejections.is_empty());
    }

    #[test]
    fn nested_candidates_emit_outermost_only() {
        let src = "fn f(o: Option<Option<i32>>, i: Option<i32>) {\n    if let Some(x) = o {\n        if let Some(y) = i { a(y); } else { b(); }\n    } else {\n        c();\n    }\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1, "outer edit only");
        assert!(out.contains("match o {"), "{out}");
        assert!(out.contains("if let Some(y) = i"), "inner untouched: {out}");
        // Second pass catches the inner one.
        let (out2, o2) = run(&out);
        assert_eq!(o2.edits.len(), 1);
        assert!(out2.contains("match i {"), "{out2}");
        assert!(parse("t.rs", &out2).is_lossless());
    }

    #[test]
    fn why_safe_cites_branch_edges_and_place_fact() {
        let src = "fn f(o: Option<i32>) {\n    if let Some(x) = o { a(x); } else { b(); }\n    done();\n}\n";
        let (_, o) = run(src);
        let facts = o.edits[0].cpg_facts.join("\n");
        assert!(facts.contains("place expression"), "{facts}");
        assert!(facts.contains("branch=then"), "{facts}");
        assert!(facts.contains("branch=else"), "{facts}");
        assert!(facts.contains("fn::f#1"), "{facts}");
    }
}
