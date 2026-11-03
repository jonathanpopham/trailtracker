//! Lower the Nix CST into the canonical graph.
//!
//! Nix maps **coarsely** to the shared ontology, and this lowering is honest
//! about that rather than fabricating structure the source does not state. Nix
//! is a functional configuration language: there are no named classes, no static
//! types, and no declaration-site inheritance. Its one pervasive construct is the
//! attribute binding `name = expr;`. The mapping is therefore:
//!
//!   - An attribute / `let` binding `name = expr;` whose value is **not** a
//!     function → [`Constant`] (an attrset binding is the closest honest node;
//!     `binding: "attr"`).
//!   - A binding whose value is a lambda (`foo = x: …`, `foo = { a }: …`,
//!     `foo = a@{ b }: …`) → [`Function`]. Function-ness is read from a top-level
//!     `:` in the value or a `Lambda` header node — never guessed.
//!   - `import ./file.nix` / `import "path"` → [`IMPORTS`] to an
//!     [`UnresolvedSymbol`] (we do not resolve relative paths to project files in
//!     the airgapped runtime). `import <nixpkgs>` and any `<…>` search path →
//!     [`IMPORTS`] plus an [`ExternalDependency`] + `DEPENDS_ON`.
//!   - Function application `f x` → [`CALLS`], but **only** when the head `f` is a
//!     known binding in the same file (resolved if unique, ambiguous with a
//!     `candidates` set if several). An application whose head is not a known
//!     binding is skipped — there is no scope inference, so guessing would
//!     fabricate edges.
//!
//! What this lowering deliberately **punts** (documented, not hidden):
//!   - `inherit …;` bindings are parsed losslessly but not lowered to nodes
//!     (they alias names from elsewhere; no honest definition site exists here).
//!   - Dynamic attribute names (`${expr} = …`) are not named.
//!   - `with`/`let` scope is not modelled, so call resolution is intentionally
//!     file-local and conservative.
//!   - Calls in a file's bare top-level expression (outside any binding) are not
//!     attributed; only calls inside binding values are emitted.
//!   - No `USES_TYPE`/`EXTENDS`/`IMPLEMENTS` edges: Nix has no type annotations or
//!     declaration-site inheritance to read them from.
//!
//! Everything comes from real tokens on the lossless tree; nothing is invented.

use std::collections::BTreeMap;

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::nix::lexer::{is_keyword, kind as tk};
use crate::lang::nix::parser::node as cst;

/// Lower a whole project's worth of Nix files into a graph. `manifest_deps` is
/// unused (Nix has no manifest the pipeline reads); dependencies are discovered
/// from `import`/search-path expressions instead. Call resolution is per-file:
/// Nix files do not implicitly share scope, so resolving a call against another
/// file's bindings would fabricate a relationship.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    let mut g = Graph::new();
    let pkg_id = format!("pkg::{package}");
    g.upsert_node(
        pkg_id.clone(),
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("nix"))],
    );

    for f in files {
        let li = LineIndex::new(f.source);
        let file_id = format!("file::{}", f.rel_path);
        g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("nix")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        g.add_edge(pkg_id.clone(), edge::CONTAINS, file_id.clone(), vec![]);

        // Pass 1: create definition nodes (Constant/Function) and a file-local
        // name → ids index, plus the list of (binding id, value node) to scan.
        let mut names: BTreeMap<String, Vec<String>> = BTreeMap::new();
        let mut defs: Vec<(String, &Node)> = Vec::new();
        collect_defs(
            &mut g,
            f.root,
            &[],
            &file_id,
            &f.rel_path,
            f.source,
            &li,
            &mut names,
            &mut defs,
        );

        // Pass 2: imports / search paths (file-level), scanned over the whole tree.
        let mut spaths: Vec<String> = Vec::new();
        let mut paths: Vec<String> = Vec::new();
        scan_imports(f.root, f.source, &mut spaths, &mut paths);
        for s in spaths {
            let root = s.split('/').next().unwrap_or(&s).to_string();
            let dep_id = format!("ext::{root}");
            g.upsert_node(
                dep_id.clone(),
                ont::EXTERNAL_DEPENDENCY,
                root,
                vec![
                    ("external", Json::Bool(true)),
                    ("source", Json::str("search_path")),
                ],
            );
            g.add_edge(
                file_id.clone(),
                edge::IMPORTS,
                dep_id.clone(),
                vec![("path", Json::str(s)), ("external", Json::Bool(true))],
            );
            g.add_edge(pkg_id.clone(), edge::DEPENDS_ON, dep_id, vec![]);
        }
        for p in paths {
            let target = format!("unresolved::import::{p}");
            g.upsert_node(
                target.clone(),
                ont::UNRESOLVED,
                p.clone(),
                vec![
                    ("unresolved", Json::Bool(true)),
                    ("role", Json::str("import")),
                ],
            );
            g.add_edge(
                file_id.clone(),
                edge::IMPORTS,
                target,
                vec![("path", Json::str(p)), ("external", Json::Bool(false))],
            );
        }

        // Pass 3: calls, resolved against this file's bindings only.
        for (id, val) in &defs {
            let mut calls: Vec<String> = Vec::new();
            scan_calls(val, f.source, &mut calls);
            for callee in calls {
                if let Some(ids) = names.get(&callee) {
                    emit_call(&mut g, id, &callee, ids);
                }
            }
        }
    }

    g
}

/// Recursively create definition nodes for every `Binding`, tracking the
/// attribute-path scope prefix so nested-set bindings get qualified names.
#[allow(clippy::too_many_arguments)]
fn collect_defs<'a>(
    g: &mut Graph,
    container: &'a Node,
    scope: &[String],
    file_id: &str,
    rel: &str,
    src: &'a str,
    li: &LineIndex,
    names: &mut BTreeMap<String, Vec<String>>,
    defs: &mut Vec<(String, &'a Node)>,
) {
    for child in container.child_nodes() {
        match child.kind {
            cst::BINDING => {
                let segs = binding_name_segs(child, src);
                let value = child.child(cst::VALUE);
                if segs.is_empty() {
                    // Unnamed/dynamic binding: still descend into its value so a
                    // nested attribute set's bindings are not lost.
                    if let Some(v) = value {
                        collect_defs(g, v, scope, file_id, rel, src, li, names, defs);
                    }
                    continue;
                }
                let full: Vec<String> = scope.iter().cloned().chain(segs).collect();
                let leaf = full.last().unwrap().clone();
                let qual = full.join(".");
                let line = li.line_col(binding_span_start(child)).line;
                let is_fn = value.map(|v| value_is_function(v, src)).unwrap_or(false);

                let id = if is_fn {
                    let id = format!("fn::{rel}::{qual}#{line}");
                    g.upsert_node(
                        id.clone(),
                        ont::FUNCTION,
                        leaf.clone(),
                        vec![
                            ("qualified_name", Json::str(qual)),
                            ("language", Json::str("nix")),
                            ("line", Json::U64(line as u64)),
                            ("span_start", Json::U64(child.span.start as u64)),
                            ("span_end", Json::U64(child.span.end as u64)),
                            ("has_body", Json::Bool(true)),
                        ],
                    );
                    id
                } else {
                    let id = format!("const::{rel}::{qual}");
                    g.upsert_node(
                        id.clone(),
                        ont::CONSTANT,
                        leaf.clone(),
                        vec![
                            ("binding", Json::str("attr")),
                            ("qualified_name", Json::str(qual)),
                            ("language", Json::str("nix")),
                            ("line", Json::U64(line as u64)),
                        ],
                    );
                    id
                };
                g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
                names.entry(leaf).or_default().push(id.clone());
                if let Some(v) = value {
                    defs.push((id, v));
                    collect_defs(g, v, &full, file_id, rel, src, li, names, defs);
                }
            }
            cst::INHERIT => {} // punted: see module docs
            cst::ATTR_SET
            | cst::LET
            | cst::LAMBDA
            | cst::FORMALS
            | cst::PAREN
            | cst::LIST
            | cst::VALUE
            | cst::SOURCE_FILE => {
                collect_defs(g, child, scope, file_id, rel, src, li, names, defs);
            }
            _ => {}
        }
    }
}

/// A binding's value is a function iff its `Value` region contains a top-level
/// `:` token (`x: body`) or a `Lambda` header node (`{ a }: body`). A `:` inside
/// a nested group (e.g. `map (x: x) xs`) does not count — that value is a list.
fn value_is_function(value: &Node, src: &str) -> bool {
    for c in &value.children {
        match c {
            Child::Token(t) if !t.trivia && t.kind == tk::PUNCT && t.span.text(src) == ":" => {
                return true
            }
            Child::Node(n) if n.kind == cst::LAMBDA => return true,
            _ => {}
        }
    }
    false
}

// --- scanning over the lossless token tree ----------------------------------

enum El<'a> {
    Tok { text: &'a str, kind: &'static str },
    Grp(&'a Node),
}

fn significant_children<'a>(node: &'a Node, src: &'a str) -> Vec<El<'a>> {
    let mut v = Vec::new();
    for c in &node.children {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => v.push(El::Tok {
                text: t.span.text(src),
                kind: t.kind,
            }),
            Child::Node(n) => v.push(El::Grp(n)),
        }
    }
    v
}

fn el_tok_text<'a>(e: &El<'a>) -> Option<&'a str> {
    match e {
        El::Tok { text, .. } => Some(text),
        El::Grp(_) => None,
    }
}

/// Whether `e` can begin a function-application argument: a grouped expression,
/// or an atom literal/identifier (but not a keyword, which would start a new
/// construct rather than continue an application).
fn is_arg_start(e: &El) -> bool {
    match e {
        El::Grp(n) => matches!(n.kind, cst::PAREN | cst::LIST | cst::ATTR_SET),
        El::Tok { text, kind } => {
            matches!(
                *kind,
                tk::IDENT
                    | tk::INT
                    | tk::FLOAT
                    | tk::STRING
                    | tk::INDENTED_STRING
                    | tk::PATH
                    | tk::SEARCH_PATH
            ) && !(*kind == tk::IDENT && is_keyword(text))
        }
    }
}

/// Collect application head names that are candidate calls: a bare identifier in
/// function position (not a keyword, not `import`, not an attribute-selection
/// tail after `.`) immediately followed by an argument. Recurses into `Paren` and
/// `List` groups (same scope); does **not** descend into attribute sets, lambdas
/// or `let` forms (those introduce their own scopes / separate bindings).
fn scan_calls(node: &Node, src: &str, out: &mut Vec<String>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        if let El::Tok { text, kind } = &els[i] {
            if *kind == tk::IDENT && !is_keyword(text) && *text != "import" {
                let prev = if i > 0 {
                    el_tok_text(&els[i - 1])
                } else {
                    None
                };
                if prev != Some(".") && i + 1 < n && is_arg_start(&els[i + 1]) {
                    out.push(text.to_string());
                }
            }
        }
        i += 1;
    }
    for e in &els {
        if let El::Grp(g) = e {
            if matches!(g.kind, cst::PAREN | cst::LIST) {
                scan_calls(g, src, out);
            }
        }
    }
}

/// Collect imports over the whole tree: every `<…>` search path (into `spaths`),
/// and every `import` applied to a path/string (into `paths`). Search paths used
/// as the argument of `import` are captured by the `spaths` sweep already.
fn scan_imports(node: &Node, src: &str, spaths: &mut Vec<String>, paths: &mut Vec<String>) {
    let els = significant_children(node, src);
    let n = els.len();
    for i in 0..n {
        match &els[i] {
            El::Tok { text, kind } if *kind == tk::SEARCH_PATH => {
                spaths.push(strip_angle(text));
            }
            El::Tok { text, kind } if *kind == tk::IDENT && *text == "import" => {
                let prev = if i > 0 {
                    el_tok_text(&els[i - 1])
                } else {
                    None
                };
                if prev == Some(".") {
                    continue; // a field named `import`, not the builtin
                }
                if i + 1 < n {
                    match &els[i + 1] {
                        El::Tok { text, kind } if *kind == tk::PATH => paths.push(text.to_string()),
                        El::Tok { text, kind } if *kind == tk::STRING => {
                            paths.push(strip_quotes(text))
                        }
                        _ => {} // `import <x>` handled by the spath sweep; others skipped
                    }
                }
            }
            _ => {}
        }
    }
    for e in &els {
        if let El::Grp(g) = e {
            scan_imports(g, src, spaths, paths);
        }
    }
}

fn emit_call(g: &mut Graph, caller_id: &str, callee: &str, ids: &[String]) {
    let mut props = vec![
        ("callee", Json::str(callee.to_string())),
        ("resolution", Json::str("binding")),
    ];
    if ids.len() == 1 {
        props.push(("resolved", Json::Bool(true)));
        props.push(("candidate_count", Json::U64(1)));
        g.add_edge(caller_id, edge::CALLS, ids[0].clone(), props);
    } else {
        let target = format!("unresolved::{callee}");
        g.upsert_node(
            target.clone(),
            ont::UNRESOLVED,
            callee.to_string(),
            vec![
                ("unresolved", Json::Bool(true)),
                ("role", Json::str("call")),
            ],
        );
        props.push(("resolved", Json::Bool(false)));
        props.push(("ambiguous", Json::Bool(true)));
        props.push(("candidate_count", Json::U64(ids.len() as u64)));
        props.push((
            "candidates",
            Json::Array(ids.iter().cloned().map(Json::Str).collect()),
        ));
        g.add_edge(caller_id, edge::CALLS, target, props);
    }
}

// --- pure helpers -----------------------------------------------------------

/// Name segments of a binding's attribute path: identifiers and (stripped)
/// string keys, in order. Dots and dynamic `${…}` parts are dropped.
fn binding_name_segs(binding: &Node, src: &str) -> Vec<String> {
    let ap = match binding.child(cst::ATTR_PATH) {
        Some(a) => a,
        None => return Vec::new(),
    };
    let mut v = Vec::new();
    for t in ap.tokens() {
        match t.kind {
            tk::IDENT => v.push(t.span.text(src).to_string()),
            tk::STRING => v.push(strip_quotes(t.span.text(src))),
            _ => {}
        }
    }
    v
}

fn binding_span_start(binding: &Node) -> u32 {
    binding
        .child(cst::ATTR_PATH)
        .map(|n| n.span.start)
        .unwrap_or(binding.span.start)
}

fn strip_quotes(text: &str) -> String {
    let t = text.trim();
    if t.len() >= 2 && t.starts_with('"') && t.ends_with('"') {
        t[1..t.len() - 1].to_string()
    } else {
        t.to_string()
    }
}

fn strip_angle(text: &str) -> String {
    text.trim_start_matches('<')
        .trim_end_matches('>')
        .to_string()
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
    use crate::lang::nix::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("default.nix", src);
        let file = SourceFile {
            rel_path: "default.nix".to_string(),
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
    fn attr_binding_is_constant_lambda_is_function() {
        let g = graph_for("{ version = \"1.0\"; greet = name: \"hi ${name}\"; }");
        let consts: Vec<&str> = g
            .nodes()
            .filter(|n| n.kind == ont::CONSTANT)
            .map(|n| n.name.as_str())
            .collect();
        assert!(consts.contains(&"version"), "version is a Constant");
        let fns: Vec<&str> = g
            .nodes()
            .filter(|n| n.kind == ont::FUNCTION)
            .map(|n| n.name.as_str())
            .collect();
        assert!(fns.contains(&"greet"), "greet is a Function (lambda value)");
    }

    #[test]
    fn formals_lambda_value_is_function() {
        let g = graph_for("{ build = { pkgs, ... }: pkgs.hello; }");
        assert!(
            g.nodes()
                .any(|n| n.kind == ont::FUNCTION && n.name == "build"),
            "a formals lambda value makes build a Function"
        );
    }

    #[test]
    fn list_value_with_inner_lambda_is_constant() {
        // The `:` is inside a Paren, so the value is a list, not a function.
        let g = graph_for("{ xs = map (x: x + 1) [ 1 2 3 ]; }");
        assert!(
            g.nodes().any(|n| n.kind == ont::CONSTANT && n.name == "xs"),
            "xs is a Constant despite the nested lambda"
        );
    }

    #[test]
    fn search_path_import_is_external_dependency() {
        let g = graph_for("{ pkgs = import <nixpkgs> { }; }");
        assert!(g.has_node("ext::nixpkgs"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::nixpkgs"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::IMPORTS && e.to == "ext::nixpkgs"));
    }

    #[test]
    fn relative_import_is_unresolved() {
        let g = graph_for("{ mod = import ./sub/thing.nix; }");
        assert!(g.has_node("unresolved::import::./sub/thing.nix"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn call_to_known_binding_resolves() {
        let g = graph_for("{ helper = x: x + 1; run = y: helper y; }");
        let calls = call_edges(&g);
        let c = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("helper")))
            .expect("a call to helper");
        assert_eq!(c.props.get("resolved"), Some(&Json::Bool(true)));
        assert!(c.to.starts_with("fn::default.nix::helper"));
    }

    #[test]
    fn call_to_unknown_binding_is_skipped() {
        let g = graph_for("{ run = x: mystery x; }");
        // `mystery` is not a known binding, so no CALLS edge is fabricated.
        assert!(call_edges(&g).is_empty());
        assert!(!g.has_node("unresolved::mystery"));
    }

    #[test]
    fn nested_set_bindings_are_qualified() {
        let g = graph_for("{ outer = rec { a = 1; b = a; }; }");
        // outer is a Constant; a and b are nested Constants qualified under outer.
        assert!(g.has_node("const::default.nix::outer.a"));
        assert!(g.has_node("const::default.nix::outer.b"));
    }

    #[test]
    fn output_is_deterministic() {
        let src = "{ a = 1; f = x: g x; g = y: y; }";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
