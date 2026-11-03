//! Rewrite rules (ADR-0006): conservative recognizers over the SAME statement
//! segmentation the CPG uses, emitting span edits whose safety arguments cite
//! real CPG facts (statement ids, `FLOWS_TO` roles, `DATA_DEP` def sites).
//!
//! A rule is `(id, version, recognizer, emitter)`. Recognizers partition
//! candidate sites into recognized (→ edits) and near-miss (→ rejections with
//! machine-readable snake_case reasons). Anything outside a rule's documented
//! grammar is rejected, never guessed at.

pub(crate) mod clone_elim;
mod dead_branch;
mod extract_fn;
mod if_let_match;
mod loop_chain;
pub(crate) mod slice_param;

use crate::core::cst::{Node, ParseTree};
use crate::core::span::{ByteSpan, LineIndex};
use crate::graph::{Graph, GraphEdge};
use crate::ir::cpg::{emit_function_cpg_stmts, ElsePart, Stmt};
use crate::ir::ontology::edge;
use crate::lang::rust::parser::node as cst;
use crate::rewrite::proposal::{ProposedEdit, Rejection};

pub use clone_elim::RedundantCloneElim;
pub use dead_branch::DeadBranchElim;
pub use extract_fn::ExtractFunction;
pub use if_let_match::IfLetToMatch;
pub use loop_chain::LoopToIterator;
pub use slice_param::SliceParam;

/// Options a rule may require (per-rule flags surfaced by the CLI).
#[derive(Clone, Debug, Default)]
pub struct RuleOptions {
    /// `--lines A-B` (1-based, inclusive) — required by `extract-function`.
    pub lines: Option<(usize, usize)>,
    /// `--name NAME` — the extracted unit's name (default `extracted`).
    pub name: Option<String>,
}

/// What a recognizer produced for one file.
#[derive(Debug, Default)]
pub struct RuleOutcome {
    pub edits: Vec<ProposedEdit>,
    pub rejections: Vec<Rejection>,
}

/// One rewrite rule. `Err(String)` from [`Rule::propose`] is a usage-level
/// problem (bad/missing options); recognizer refusals are `RuleOutcome`
/// rejections, not errors.
pub trait Rule {
    fn id(&self) -> &'static str;
    fn version(&self) -> &'static str;
    /// One-line summary for `rewrite rules`.
    fn summary(&self) -> &'static str;
    /// The exact recognized shapes, one per line (the honest grammar).
    fn shapes(&self) -> &'static [&'static str];
    /// Whether `--lines A-B` is required.
    fn requires_lines(&self) -> bool {
        false
    }
    fn propose(&self, file: &FileCpg<'_>, opts: &RuleOptions) -> Result<RuleOutcome, String>;
}

/// Every registered rule, in stable order.
pub fn all_rules() -> Vec<Box<dyn Rule>> {
    vec![
        Box::new(DeadBranchElim),
        Box::new(LoopToIterator),
        Box::new(ExtractFunction),
        Box::new(RedundantCloneElim),
        Box::new(IfLetToMatch),
        Box::new(SliceParam),
    ]
}

/// Look a rule up by id.
pub fn rule_by_id(id: &str) -> Option<Box<dyn Rule>> {
    all_rules().into_iter().find(|r| r.id() == id)
}

// ---------------------------------------------------------------------------
// Per-file analysis context
// ---------------------------------------------------------------------------

/// One function with its CPG-segmented statement tree (ids assigned by the
/// same emission the `cpg` command performs).
pub struct FnUnit<'a> {
    /// Proposal-scoped id (`fn::{name}#{line}`), the root of statement ids.
    pub fn_id: String,
    pub name: String,
    pub block: &'a Node,
    /// The function's signature node (`fn name(params) -> ret`), when parsed.
    /// Rules editing the signature (slice-param) recognize sites here.
    pub(crate) sig: Option<&'a Node>,
    pub(crate) stmts: Vec<Stmt<'a>>,
}

/// The analysis context every rule consumes: source, the real CPG graph for
/// each function in the file, and the segmented statement trees.
pub struct FileCpg<'a> {
    pub src: &'a str,
    pub graph: Graph,
    pub fns: Vec<FnUnit<'a>>,
}

/// Build the rule context from a parsed file: find every function with a
/// body, run the real CPG emission (ADR-0003) into one graph, and keep the
/// segmented trees so spans and ids line up by construction.
pub fn analyze_file(tree: &ParseTree) -> FileCpg<'_> {
    let src = tree.source.as_str();
    let li = LineIndex::new(src);
    let mut graph = Graph::new();
    let mut fns = Vec::new();
    for node in tree.root.walk() {
        if node.kind != cst::FUNCTION {
            continue;
        }
        let Some(block) = node.child(cst::BLOCK) else {
            continue; // declaration without a body
        };
        let name = node
            .child(cst::NAME)
            .and_then(|n| n.tokens().next())
            .map(|t| t.span.text(src).to_string())
            .unwrap_or_else(|| "<anon>".to_string());
        let line = li.line_col(node.span.start).line;
        let fn_id = format!("fn::{name}#{line}");
        let signature = node.child(cst::SIGNATURE);
        let stmts = emit_function_cpg_stmts(&mut graph, &fn_id, block, signature, src);
        fns.push(FnUnit {
            fn_id,
            name,
            block,
            sig: signature,
            stmts,
        });
    }
    FileCpg { src, graph, fns }
}

// ---------------------------------------------------------------------------
// Shared helpers for recognizers
// ---------------------------------------------------------------------------

/// Visit every statement in a tree (pre-order), including nested blocks,
/// else-chains, and match-arm blocks.
pub(crate) fn walk_stmts<'s, 'a>(stmts: &'s [Stmt<'a>], f: &mut impl FnMut(&'s Stmt<'a>)) {
    for s in stmts {
        walk_stmt(s, f);
    }
}

pub(crate) fn walk_stmt<'s, 'a>(s: &'s Stmt<'a>, f: &mut impl FnMut(&'s Stmt<'a>)) {
    f(s);
    if let Some(b) = &s.body {
        walk_stmts(b, f);
    }
    match &s.else_part {
        Some(ElsePart::Block(_, b)) => walk_stmts(b, f),
        Some(ElsePart::If(nested)) => walk_stmt(nested, f),
        None => {}
    }
    for arm in &s.arms {
        if let Some(b) = &arm.block {
            walk_stmts(b, f);
        }
    }
}

/// Every CPG node id assigned within a statement subtree (statements + arms).
pub(crate) fn subtree_ids(stmts: &[Stmt<'_>]) -> Vec<String> {
    let mut ids = Vec::new();
    walk_stmts(stmts, &mut |s| {
        if let Some(id) = &s.id {
            ids.push(id.clone());
        }
        for arm in &s.arms {
            if let Some(id) = &arm.id {
                ids.push(id.clone());
            }
        }
    });
    ids
}

/// `FLOWS_TO` edges leaving any of `ids`.
pub(crate) fn flows_from<'g>(graph: &'g Graph, ids: &[String]) -> Vec<&'g GraphEdge> {
    graph
        .edges()
        .filter(|e| e.kind == edge::FLOWS_TO && ids.contains(&e.from))
        .collect()
}

/// `DATA_DEP` edges leaving any of `ids`.
pub(crate) fn data_deps_from<'g>(graph: &'g Graph, ids: &[String]) -> Vec<&'g GraphEdge> {
    graph
        .edges()
        .filter(|e| e.kind == edge::DATA_DEP && ids.contains(&e.from))
        .collect()
}

/// An edge's string property.
pub(crate) fn edge_prop<'g>(e: &'g GraphEdge, key: &str) -> Option<&'g str> {
    match e.props.get(key) {
        Some(crate::core::json::Json::Str(s)) => Some(s.as_str()),
        _ => None,
    }
}

/// The whitespace indentation of the line containing `offset`.
pub(crate) fn line_indent(src: &str, offset: usize) -> &str {
    let line_start = src[..offset].rfind('\n').map(|i| i + 1).unwrap_or(0);
    let rest = &src[line_start..];
    let indent_len = rest
        .find(|c: char| c != ' ' && c != '\t')
        .unwrap_or(rest.len());
    &rest[..indent_len]
}

/// 1-based line number of a byte offset (for human-facing facts).
pub(crate) fn line_of(src: &str, offset: usize) -> usize {
    src[..offset.min(src.len())]
        .bytes()
        .filter(|b| *b == b'\n')
        .count()
        + 1
}

/// The source text of a span.
pub(crate) fn text_of(src: &str, span: ByteSpan) -> &str {
    span.text(src)
}

/// Splice a brace group's inner statements into statement position: the text
/// between `{` and `}`, with the first/last whitespace-only line fragments
/// dropped and the block's excess indentation (relative to `target_indent`)
/// removed from every line. Whitespace-only transformation — token streams
/// are untouched.
pub(crate) fn splice_block_inner(src: &str, group: &Node, target_indent: &str) -> String {
    let inner = &src[group.span.start as usize + 1..group.span.end as usize - 1];
    if !inner.contains('\n') {
        return inner.trim().to_string();
    }
    let mut lines: Vec<&str> = Vec::new();
    let mut start = 0;
    for (i, b) in inner.bytes().enumerate() {
        if b == b'\n' {
            lines.push(&inner[start..=i]);
            start = i + 1;
        }
    }
    if start < inner.len() {
        lines.push(&inner[start..]);
    }
    // Drop the fragment after `{` when blank, and the indent before `}`.
    if lines.first().is_some_and(|l| l.trim().is_empty()) {
        lines.remove(0);
    }
    if lines.last().is_some_and(|l| l.trim().is_empty()) {
        lines.pop();
    }
    let min_indent = lines
        .iter()
        .filter(|l| !l.trim().is_empty())
        .map(|l| l.len() - l.trim_start_matches([' ', '\t']).len())
        .min()
        .unwrap_or(0);
    let excess = min_indent.saturating_sub(target_indent.len());
    let mut out = String::new();
    for (i, line) in lines.iter().enumerate() {
        let strip = if i == 0 { min_indent } else { excess };
        let ws_len = line.len() - line.trim_start_matches([' ', '\t']).len();
        out.push_str(&line[strip.min(ws_len)..]);
    }
    while out.ends_with(['\n', ' ', '\t']) {
        out.pop();
    }
    out
}
