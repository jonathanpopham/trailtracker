//! Rule 1: `dead-branch-elim` v1 (ADR-0006) — eliminate `if` statements whose
//! condition is **exactly the literal token `true` or `false`**. No constant
//! propagation, no `!true`, no `1 == 1`: a literal token is a grammar fact;
//! everything else is a claim this rule does not make.
//!
//! Safety argument: the CPG's branch edge set. An `if` statement carries
//! `FLOWS_TO branch=then/else` edges; under a literal condition exactly one
//! branch is reachable, so the other branch's statements are dead. The
//! replacement splices the live branch's statements (or, for a dead-`false`
//! head, the else continuation) into the statement's position — a
//! whitespace-only reindentation of bytes that already exist in the file.
//!
//! Nesting: only OUTERMOST candidates are emitted per pass (inner spans would
//! shift under the outer edit); re-running propose reaches newly exposed
//! sites. Else-position candidates (`else if true …`) keep their braces so
//! the surrounding `else` stays grammatical.

use crate::ir::cpg::{ElsePart, Stmt, StmtKind};
use crate::rewrite::proposal::{ProposedEdit, Rejection};
use crate::rewrite::rules::{
    flows_from, line_indent, line_of, splice_block_inner, subtree_ids, text_of, FileCpg, FnUnit,
    Rule, RuleOptions, RuleOutcome,
};

pub struct DeadBranchElim;

impl Rule for DeadBranchElim {
    fn id(&self) -> &'static str {
        "dead-branch-elim"
    }

    fn version(&self) -> &'static str {
        "1"
    }

    fn summary(&self) -> &'static str {
        "Eliminate statement-position `if`/`else` chains whose head condition is the \
         literal token `true` or `false`, splicing the live branch in place."
    }

    fn shapes(&self) -> &'static [&'static str] {
        &[
            "if true { A } [else …]            => A",
            "if false { A } else { B }         => B",
            "if false { A } else if C { … }    => if C { … }",
            "if false { A }                    => (removed)",
            "… else if true { A } [else …]     => else { A }   (braces kept)",
            "… else if false { A } else { B }  => else { B }",
        ]
    }

    fn propose(&self, file: &FileCpg<'_>, _opts: &RuleOptions) -> Result<RuleOutcome, String> {
        let mut out = RuleOutcome::default();
        for f in &file.fns {
            scan_block(file, f, &f.stmts, &mut out);
        }
        // Deterministic order: by span.
        out.edits.sort_by_key(|e| (e.span.start, e.span.end));
        out.rejections.sort_by_key(|r| (r.span.start, r.span.end));
        Ok(out)
    }
}

/// The literal condition of an `if` statement, when it is exactly one token.
fn literal_condition(file: &FileCpg<'_>, s: &Stmt<'_>) -> Option<bool> {
    if s.kind != StmtKind::If || s.header.len() != 1 {
        return None;
    }
    match s.header[0].text(file.src) {
        Some("true") => Some(true),
        Some("false") => Some(false),
        _ => None,
    }
}

/// A near-miss: a condition built only from literals/operators (constant in
/// principle) that is not the single literal token. Real conditions (anything
/// naming a variable, call, or group) are not candidates and stay silent.
fn constant_but_not_literal(file: &FileCpg<'_>, s: &Stmt<'_>) -> bool {
    if s.kind != StmtKind::If || s.header.is_empty() || s.header.len() == 1 {
        return false;
    }
    use crate::ir::cpg::E;
    s.header.iter().all(|e| match e {
        E::G(_) => false,
        E::T(t) => {
            let text = t.span.text(file.src);
            matches!(text, "true" | "false" | "!" | "&&" | "||" | "==" | "!=")
        }
    })
}

fn scan_block(file: &FileCpg<'_>, f: &FnUnit<'_>, stmts: &[Stmt<'_>], out: &mut RuleOutcome) {
    for s in stmts {
        scan_stmt(file, f, s, false, out);
    }
}

/// Scan one statement. `else_position` is true when `s` is the `if` of an
/// `else if` continuation (its replacement must stay brace-wrapped).
fn scan_stmt(
    file: &FileCpg<'_>,
    f: &FnUnit<'_>,
    s: &Stmt<'_>,
    else_position: bool,
    out: &mut RuleOutcome,
) {
    if let Some(lit) = literal_condition(file, s) {
        if let Some(edit) = eliminate(file, f, s, lit, else_position) {
            out.edits.push(edit);
            return; // outermost only: do not descend into a replaced span
        }
    }
    if constant_but_not_literal(file, s) {
        let cond_span = crate::ir::cpg::span_of(&s.header);
        out.rejections.push(Rejection {
            span: cond_span,
            reason: "condition_constant_but_not_literal".to_string(),
            detail: format!(
                "condition `{}` is built from literals but is not the single token \
                 `true`/`false`; this rule does no constant propagation",
                text_of(file.src, cond_span)
            ),
        });
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

/// Build the elimination edit for a literal-condition `if`.
fn eliminate(
    file: &FileCpg<'_>,
    f: &FnUnit<'_>,
    s: &Stmt<'_>,
    lit: bool,
    else_position: bool,
) -> Option<ProposedEdit> {
    let src = file.src;
    let mut span = s.span;
    let indent = line_indent(src, s.span.start as usize);

    // The replacement text and the ids of the statements that die.
    let (after, dead_ids): (String, Vec<String>) = if lit {
        // `true`: the then-branch lives; the else-part (if any) dies.
        let live = match (else_position, s.body_group) {
            (false, Some(g)) => splice_block_inner(src, g, indent),
            (true, Some(g)) => text_of(src, g.span).to_string(),
            (_, None) => return None, // defensive: no then group parsed
        };
        let dead = match &s.else_part {
            Some(ElsePart::Block(_, b)) => subtree_ids(b),
            Some(ElsePart::If(nested)) => subtree_ids(std::slice::from_ref(nested)),
            None => Vec::new(),
        };
        (live, dead)
    } else {
        // `false`: the then-branch dies; the else continuation lives.
        let dead = s.body.as_ref().map(|b| subtree_ids(b)).unwrap_or_default();
        let live = match &s.else_part {
            Some(ElsePart::Block(g, _)) => {
                if else_position {
                    text_of(src, g.span).to_string()
                } else {
                    splice_block_inner(src, g, indent)
                }
            }
            // The trailing chain is already a valid statement (and valid
            // after `else`): keep it verbatim.
            Some(ElsePart::If(nested)) => text_of(src, nested.span).to_string(),
            None => {
                // Nothing lives. In else position the dangling `else` keyword
                // must go too; extend the span left over it.
                if else_position {
                    let before = &src[..s.span.start as usize];
                    let trimmed = before.trim_end();
                    if trimmed.ends_with("else") {
                        span = crate::core::span::ByteSpan::new(
                            trimmed.len() - "else".len(),
                            s.span.end as usize,
                        );
                    }
                }
                String::new()
            }
        };
        (live, dead)
    };

    let sid = s.id.clone().unwrap_or_default();
    let cond_span = crate::ir::cpg::span_of(&s.header);
    let (live_branch, dead_branch) = if lit {
        ("then", "else")
    } else {
        ("else", "then")
    };

    // Cite the real branch edges the CPG emitted for this statement.
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
        format!(
            "condition is the literal token `{}` at bytes {}..{} (line {}) — a grammar \
             fact, not a computed value",
            if lit { "true" } else { "false" },
            cond_span.start,
            cond_span.end,
            line_of(src, cond_span.start as usize)
        ),
        format!("{}: statement {sid} (stmt_kind=if)", f.fn_id),
    ];
    facts.extend(branch_edges);
    if dead_ids.is_empty() {
        facts.push(format!(
            "the {dead_branch} branch is empty/absent — nothing else is removed"
        ));
    } else {
        facts.push(format!(
            "unreachable {dead_branch} branch statements eliminated: {}",
            dead_ids.join(", ")
        ));
    }

    Some(ProposedEdit {
        span,
        before: text_of(src, span).to_string(),
        after,
        why_safe: format!(
            "the `if` condition is the literal `{}`, so the CPG's `branch={dead_branch}` \
             edge can never be taken; only the {live_branch}-branch statements (already \
             present in the file) remain, spliced into statement position",
            if lit { "true" } else { "false" }
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
        let out = DeadBranchElim
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
    fn if_true_splices_then_branch() {
        let src = "fn f() {\n    if true {\n        a();\n        b();\n    }\n    done();\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1);
        assert_eq!(out, "fn f() {\n    a();\n    b();\n    done();\n}\n");
    }

    #[test]
    fn if_true_with_else_drops_else() {
        let src = "fn f() {\n    if true { a(); } else { b(); }\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1);
        assert_eq!(out, "fn f() {\n    a();\n}\n");
        // The dead else statements are cited.
        assert!(o.edits[0]
            .cpg_facts
            .iter()
            .any(|f| f.contains("eliminated")));
    }

    #[test]
    fn if_false_keeps_else_branch() {
        let src = "fn f() {\n    if false { a(); } else { b(); }\n}\n";
        let (out, _) = run(src);
        assert_eq!(out, "fn f() {\n    b();\n}\n");
    }

    #[test]
    fn if_false_without_else_removes_statement() {
        let src = "fn f() {\n    if false { a(); }\n    done();\n}\n";
        let (out, _) = run(src);
        assert_eq!(out, "fn f() {\n    \n    done();\n}\n");
    }

    #[test]
    fn if_false_with_else_if_keeps_the_chain() {
        let src = "fn f(c: bool) {\n    if false { a(); } else if c { b(); } else { d(); }\n}\n";
        let (out, _) = run(src);
        assert_eq!(out, "fn f(c: bool) {\n    if c { b(); } else { d(); }\n}\n");
    }

    #[test]
    fn else_if_true_keeps_braces() {
        let src = "fn f(c: bool) {\n    if c { a(); } else if true { b(); } else { d(); }\n}\n";
        let (out, _) = run(src);
        assert_eq!(out, "fn f(c: bool) {\n    if c { a(); } else { b(); }\n}\n");
    }

    #[test]
    fn else_if_false_without_continuation_drops_dangling_else() {
        let src = "fn f(c: bool) {\n    if c { a(); } else if false { b(); }\n}\n";
        let (out, _) = run(src);
        assert_eq!(out, "fn f(c: bool) {\n    if c { a(); } \n}\n");
    }

    #[test]
    fn nested_candidates_emit_outermost_only() {
        let src = "fn f() {\n    if true {\n        if false { a(); } else { b(); }\n    }\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1, "outer edit only");
        assert_eq!(out, "fn f() {\n    if false { a(); } else { b(); }\n}\n");
        // Second pass catches the inner one.
        let (out2, _) = run(&out);
        assert_eq!(out2, "fn f() {\n    b();\n}\n");
    }

    #[test]
    fn candidates_inside_loops_and_matches_are_found() {
        let src =
            "fn f(xs: Vec<i32>) {\n    for x in xs {\n        if true { use_it(x); }\n    }\n}\n";
        let (out, _) = run(src);
        assert_eq!(
            out,
            "fn f(xs: Vec<i32>) {\n    for x in xs {\n        use_it(x);\n    }\n}\n"
        );
    }

    #[test]
    fn non_literal_conditions_are_not_candidates() {
        let src = "fn f(c: bool) { if c { a(); } }\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert!(o.edits.is_empty());
        assert!(
            o.rejections.is_empty(),
            "real conditions are not near-misses"
        );
    }

    #[test]
    fn constant_expressions_are_rejected_not_folded() {
        let src = "fn f() { if !true { a(); } }\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert!(o.edits.is_empty());
        assert_eq!(o.rejections.len(), 1);
        assert_eq!(o.rejections[0].reason, "condition_constant_but_not_literal");
    }

    #[test]
    fn expression_position_if_is_not_a_candidate() {
        let src = "fn f() { let x = if true { 1 } else { 2 }; }\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert!(o.edits.is_empty());
    }

    #[test]
    fn unit_type_tail_if_splices() {
        let src = "fn f() -> i32 {\n    if true { 1 } else { 2 }\n}\n";
        let (out, _) = run(src);
        assert_eq!(out, "fn f() -> i32 {\n    1\n}\n");
    }

    #[test]
    fn if_let_is_never_a_candidate() {
        let src = "fn f(o: Option<bool>) { if let Some(true) = o { a(); } }\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert!(o.edits.is_empty());
    }

    #[test]
    fn why_safe_cites_branch_edges() {
        let src = "fn f() {\n    if true { a(); } else { b(); }\n    done();\n}\n";
        let (_, o) = run(src);
        let facts = o.edits[0].cpg_facts.join("\n");
        assert!(facts.contains("literal token `true`"), "{facts}");
        assert!(facts.contains("branch=then"), "{facts}");
        assert!(facts.contains("branch=else"), "{facts}");
        assert!(facts.contains("fn::f#1"), "{facts}");
    }
}
