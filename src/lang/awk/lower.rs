//! Lower the AWK CST into the canonical graph.
//!
//! This mirrors the Bash lowering — same conservative principles, same shared
//! ontology — adapted to AWK's tiny surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to a
//!    concrete project function only when the callee name yields exactly one
//!    definition; several definitions become an ambiguous edge carrying the full
//!    `candidates` set; a call to a known AWK built-in resolves to an explicit
//!    `UnresolvedSymbol` tagged `builtin`; an unknown name resolves to an
//!    `UnresolvedSymbol` tagged `external`. There is no LLM in the airgap to guess.
//! 2. **Everything comes from real tokens.** Function names and call sites are
//!    read off the lossless tree, never invented. A user-function call is detected
//!    only as `name(` with **no** space between the name and the paren — exactly
//!    AWK's own rule (`f (x)` is concatenation/grouping, `f(x)` is a call).
//!
//! Honest mappings (see the IR Atlas):
//!   - a `function name(args) { … }` definition → `Function`;
//!   - a `name(…)` user-function call → `CALLS` (to a project function, else a
//!     `builtin`/`external` `UnresolvedSymbol`).
//!
//! `BEGIN` / `END` / pattern–action rules are kept losslessly in the CST but are
//! *not* definitions, so they emit no node of their own; their bodies are scanned
//! for calls, attributed to the enclosing file (AWK rules are file-scope).
//!
//! AWK has no class/struct/interface constructs, no module/import system (standard
//! `awk`), and only implicit, dynamically-scoped globals, so this front end emits
//! **no** `Type`, `HAS_METHOD`, `EXTENDS`, `IMPORTS`, or `Constant` — forcing any
//! of those onto AWK would be dishonest (Atlas design principle 2). See the module
//! `mod.rs` for the explicit punt list.

use std::collections::BTreeMap;

use crate::core::cst::Node;
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::awk::lexer::{is_builtin, is_keyword, kind as tk};
use crate::lang::awk::parser::node as cst;
use crate::lang::frontend::SourceFile;

/// Lower a whole project's worth of AWK files into a graph. `manifest_deps` is
/// unused (AWK has no manifest concept).
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        fn_by_name: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id.clone(),
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("awk"))],
    );

    // Pass A: file nodes + every function definition (so a call to a function
    // defined later in the project still resolves).
    for f in files {
        let li = LineIndex::new(f.source);
        let fid = file_id(&f.rel_path);
        lo.g.upsert_node(
            fid.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("awk")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(pkg_id.clone(), edge::CONTAINS, fid.clone(), vec![]);
        for item in f.root.children_of(cst::FUNCTION) {
            lo.declare_function(item, &fid, &f.rel_path, f.source, &li);
        }
    }

    // Pass B: call sites resolved against the now-complete function table.
    for f in files {
        let li = LineIndex::new(f.source);
        let fid = file_id(&f.rel_path);
        for item in f.root.child_nodes() {
            match item.kind {
                cst::FUNCTION => {
                    let name = name_text(item, f.source).unwrap_or("");
                    let line = li.line_col(name_span_start(item)).line;
                    let caller = fn_id(&f.rel_path, name, line);
                    // Scan only the body (the BLOCK child), never the header — so a
                    // function is not seen as calling itself via its own signature.
                    if let Some(body) = item.child(cst::BLOCK) {
                        lo.scan_calls(body, &caller, f.source);
                    }
                }
                cst::RULE => {
                    // Rule patterns and actions are file-scope (BEGIN/END/main).
                    lo.scan_calls(item, &fid, f.source);
                }
                _ => {}
            }
        }
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    /// Simple function name → all function node ids (AWK functions are global).
    fn_by_name: BTreeMap<String, Vec<String>>,
}

impl Lowerer {
    fn pkg_id(&self) -> String {
        format!("pkg::{}", self.package)
    }

    fn declare_function(
        &mut self,
        item: &Node,
        file_id: &str,
        rel_path: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let name = match name_text(item, src) {
            Some(n) => n.to_string(),
            None => return,
        };
        let line = li.line_col(name_span_start(item)).line;
        let id = fn_id(rel_path, &name, line);
        let has_body = item.child(cst::BLOCK).is_some();
        let arity = param_count(item, src);
        self.g.upsert_node(
            id.clone(),
            ont::FUNCTION,
            name.clone(),
            vec![
                ("qualified_name", Json::str(name.clone())),
                ("language", Json::str("awk")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
                ("arity", Json::U64(arity as u64)),
                ("has_body", Json::Bool(has_body)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.fn_by_name.entry(name).or_default().push(id);
    }

    /// Scan every leaf token in `node` for `name(` user-function call syntax and
    /// emit a `CALLS` edge from `caller` for each one.
    fn scan_calls(&mut self, node: &Node, caller: &str, src: &str) {
        let toks = collect_tokens(node, src);
        for w in toks.windows(2) {
            let (a, b) = (&w[0], &w[1]);
            if a.kind == tk::IDENT && !is_keyword(a.text) && b.text == "(" && a.end == b.start {
                self.emit_call(caller, a.text);
            }
        }
    }

    /// Resolve a callee name to a project function or an explicit
    /// builtin/external `UnresolvedSymbol`, then emit the `CALLS` edge.
    fn emit_call(&mut self, caller: &str, name: &str) {
        let candidates = self.fn_by_name.get(name).cloned().unwrap_or_default();
        let mut props = vec![("callee", Json::str(name.to_string()))];
        match candidates.len() {
            1 => {
                props.push(("resolved", Json::Bool(true)));
                props.push(("resolution", Json::str("project")));
                props.push(("candidate_count", Json::U64(1)));
                self.g
                    .add_edge(caller, edge::CALLS, candidates[0].clone(), props);
            }
            0 => {
                let target = unresolved_id(name);
                let resolution = if is_builtin(name) {
                    "builtin"
                } else {
                    "external"
                };
                self.ensure_unresolved(&target, name, resolution);
                props.push(("resolved", Json::Bool(false)));
                props.push(("resolution", Json::str(resolution)));
                props.push(("candidate_count", Json::U64(0)));
                self.g.add_edge(caller, edge::CALLS, target, props);
            }
            n => {
                let target = unresolved_id(name);
                self.ensure_unresolved(&target, name, "ambiguous");
                props.push(("resolved", Json::Bool(false)));
                props.push(("resolution", Json::str("ambiguous")));
                props.push(("ambiguous", Json::Bool(true)));
                props.push(("candidate_count", Json::U64(n as u64)));
                props.push((
                    "candidates",
                    Json::Array(candidates.into_iter().map(Json::Str).collect()),
                ));
                self.g.add_edge(caller, edge::CALLS, target, props);
            }
        }
    }

    fn ensure_unresolved(&mut self, id: &str, name: &str, role: &str) {
        if !self.g.has_node(id) {
            self.g.upsert_node(
                id.to_string(),
                ont::UNRESOLVED,
                name.to_string(),
                vec![
                    ("unresolved", Json::Bool(true)),
                    ("role", Json::str(role.to_string())),
                ],
            );
        }
    }
}

// --- pure helpers -----------------------------------------------------------

/// A flat leaf token (text + kind + byte span) for the call scanner.
#[derive(Clone, Copy)]
struct TokInfo<'a> {
    text: &'a str,
    kind: &'static str,
    start: u32,
    end: u32,
}

/// All non-trivia leaf tokens of a subtree, in source order (recurses into nested
/// blocks). Trivia is dropped here on purpose: adjacency (`name` immediately
/// followed by `(`) is then verified via the real byte spans (`a.end == b.start`).
fn collect_tokens<'a>(node: &'a Node, src: &'a str) -> Vec<TokInfo<'a>> {
    let mut out = Vec::new();
    collect_into(node, src, &mut out);
    out
}

fn collect_into<'a>(node: &'a Node, src: &'a str, out: &mut Vec<TokInfo<'a>>) {
    use crate::core::cst::Child;
    for child in &node.children {
        match child {
            Child::Node(n) => collect_into(n, src, out),
            Child::Token(t) if !t.trivia => out.push(TokInfo {
                text: t.span.text(src),
                kind: t.kind,
                start: t.span.start,
                end: t.span.end,
            }),
            Child::Token(_) => {}
        }
    }
}

fn name_text<'a>(item: &'a Node, src: &'a str) -> Option<&'a str> {
    let nm = item.child(cst::NAME)?;
    nm.tokens().next().map(|t| t.span.text(src))
}

fn name_span_start(item: &Node) -> u32 {
    item.child(cst::NAME)
        .map(|n| n.span.start)
        .unwrap_or(item.span.start)
}

/// Number of declared parameters: count of `ident` tokens inside the `Params`
/// node. Returns 0 when there is no parameter list.
fn param_count(item: &Node, src: &str) -> usize {
    match item.child(cst::PARAMS) {
        Some(p) => collect_tokens(p, src)
            .iter()
            .filter(|t| t.kind == tk::IDENT)
            .count(),
        None => 0,
    }
}

fn fn_id(rel_path: &str, name: &str, line: u32) -> String {
    format!("fn::{rel_path}:{name}#{line}")
}

fn file_id(rel: &str) -> String {
    format!("file::{rel}")
}

fn unresolved_id(name: &str) -> String {
    format!("unresolved::{name}")
}

fn file_name(rel: &str) -> String {
    rel.rsplit('/').next().unwrap_or(rel).to_string()
}

fn extension(rel: &str) -> String {
    match rel.rsplit_once('.') {
        Some((_, ext)) => ext.to_string(),
        None => String::new(),
    }
}

fn line_count(src: &str) -> usize {
    if src.is_empty() {
        0
    } else {
        src.matches('\n').count() + 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::awk::parser::parse;
    use std::collections::BTreeSet;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("prog.awk", src);
        let file = SourceFile {
            rel_path: "prog.awk".to_string(),
            module_path: vec![],
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    fn call_edges(g: &Graph) -> Vec<&crate::graph::GraphEdge> {
        g.edges().filter(|e| e.kind == edge::CALLS).collect()
    }

    #[test]
    fn emits_function_and_file_nodes() {
        let g = graph_for("function add(a, b) { return a + b }\nfunc mul(a) { return a }\n");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "add + mul");
        assert_eq!(g.count_nodes_of(ont::FILE), 1);
        assert_eq!(g.count_nodes_of(ont::PACKAGE), 1);
        // AWK has no class-like constructs.
        assert_eq!(g.count_nodes_of(ont::TYPE), 0);
    }

    #[test]
    fn function_node_has_awk_language_tag_and_arity() {
        let g = graph_for("function add(a, b) { return a + b }\n");
        let f = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION)
            .expect("a function");
        assert_eq!(f.props.get("language"), Some(&Json::str("awk")));
        assert_eq!(f.props.get("arity"), Some(&Json::U64(2)));
    }

    #[test]
    fn resolves_call_to_project_function() {
        let g = graph_for("function greet() { print \"hi\" }\nfunction run() { greet() }\n");
        let calls = call_edges(&g);
        let to_greet = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("greet")))
            .expect("a call to greet");
        assert!(to_greet.to.starts_with("fn::prog.awk:greet"));
        assert_eq!(to_greet.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(
            to_greet.props.get("resolution"),
            Some(&Json::str("project"))
        );
    }

    #[test]
    fn builtin_call_is_marked_builtin() {
        let g = graph_for("{ n = length($0) }\n");
        let calls = call_edges(&g);
        let len = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("length")))
            .expect("a call to length");
        assert_eq!(len.props.get("resolution"), Some(&Json::str("builtin")));
        let node = g.nodes().find(|n| n.id == "unresolved::length").unwrap();
        assert_eq!(node.props.get("role"), Some(&Json::str("builtin")));
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for("{ notdefined() }\n");
        let calls = call_edges(&g);
        let ext = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("notdefined")))
            .expect("a call to notdefined");
        assert_eq!(ext.props.get("resolution"), Some(&Json::str("external")));
        assert!(g.has_node("unresolved::notdefined"));
    }

    #[test]
    fn space_before_paren_is_not_a_call() {
        // `f (x)` is grouping/concatenation in AWK, not a function call.
        let g = graph_for("function f(x) { return x }\n{ y = f (3) }\n");
        let calls = call_edges(&g);
        assert!(
            !calls
                .iter()
                .any(|e| e.props.get("callee") == Some(&Json::str("f"))),
            "spaced `f (3)` must not be detected as a call"
        );
    }

    #[test]
    fn rule_calls_attributed_to_file() {
        let g = graph_for("function helper() { print }\nBEGIN { helper() }\n");
        let calls = call_edges(&g);
        let c = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("helper")))
            .expect("a call to helper");
        assert_eq!(c.from, "file::prog.awk", "BEGIN body is file-scope");
    }

    #[test]
    fn function_signature_is_not_a_self_call() {
        let g = graph_for("function only(a, b) { print a }\n");
        let calls = call_edges(&g);
        assert!(
            calls.is_empty(),
            "the header `only(a, b)` must not count as a call to `only`"
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src = "function a() { b() }\nfunction b() { print }\nBEGIN { a(); length($0) }\n";
        let x = graph_for(src).to_jsonl();
        let y = graph_for(src).to_jsonl();
        assert_eq!(x, y, "graph output must be byte-identical across runs");

        let callees: BTreeSet<String> = call_edges(&graph_for(src))
            .iter()
            .filter_map(|e| e.props.get("callee"))
            .filter_map(|j| match j {
                Json::Str(s) => Some(s.clone()),
                _ => None,
            })
            .collect();
        assert!(callees.contains("a"));
        assert!(callees.contains("b"));
        assert!(callees.contains("length"));
    }
}
