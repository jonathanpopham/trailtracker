//! Lower the Elm CST into the canonical graph.
//!
//! Honest mapping into the shared ontology:
//! - `module X exposing (..)` (including `port module` / `effect module`) → a
//!   [`Module`](crate::ir::ontology::node::MODULE) node; the package CONTAINS the
//!   module, the module CONTAINS its file, and the module DECLARES every
//!   top-level definition. When a file has no module header, the module name
//!   falls back to the file's scope path / stem.
//! - top-level bindings → [`Function`](crate::ir::ontology::node::FUNCTION) when
//!   they take arguments, else [`Constant`](crate::ir::ontology::node::CONSTANT)
//!   (a nullary binding). Both are honest readings of a lambda-calculus binding.
//! - `type X = …` → [`Type`](crate::ir::ontology::node::TYPE) with
//!   `type_kind = "custom"`; `type alias X = …` → `Type` with
//!   `type_kind = "alias"`.
//! - `import A.B as C exposing (…)` → an
//!   [`IMPORTS`](crate::ir::ontology::edge::IMPORTS) edge to the imported module.
//!   Elm imports always name another module or a package module; that target is
//!   internal when the module is in this batch, otherwise an explicit
//!   [`ExternalDependency`](crate::ir::ontology::node::EXTERNAL_DEPENDENCY) plus a
//!   package-level [`DEPENDS_ON`](crate::ir::ontology::edge::DEPENDS_ON).
//! - applications we can identify → [`CALLS`](crate::ir::ontology::edge::CALLS):
//!   an identifier in a binding's right-hand side that names a known top-level
//!   *function* resolves to it (unique ⇒ resolved, several ⇒ ambiguous with the
//!   full `candidates` set). References to anything not a project function are
//!   not fabricated into edges — there is no LLM in the airgapped runtime to
//!   guess.
//!
//! Deliberate punts (see the module-level report): type signatures (`name : T`)
//! and `port` declarations emit no node — a signature has no value home, and an
//! Elm port has no source-level body, so inventing a definition would be
//! dishonest (the same call the Haskell front end makes for `foreign`). Custom-
//! type *constructors* are not lifted to their own nodes; nested `let` bindings
//! are not lifted (only top-level bindings become functions); and `USES_TYPE` is
//! not emitted (Elm type-reference extraction is left for a later pass rather
//! than guessed).

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::elm::lexer::kind as tk;
use crate::lang::elm::parser::node as cst;
use crate::lang::frontend::SourceFile;

/// Lower a whole package's worth of Elm files plus manifest dependencies.
pub fn lower(package: &str, files: &[SourceFile<'_>], manifest_deps: &[String]) -> Graph {
    let mut g = Graph::new();
    let pkg_id = format!("pkg::{package}");
    g.upsert_node(
        pkg_id.clone(),
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("elm"))],
    );
    for dep in manifest_deps {
        let dep_id = ext_id(dep);
        g.upsert_node(
            dep_id.clone(),
            ont::EXTERNAL_DEPENDENCY,
            dep.clone(),
            vec![
                ("external", Json::Bool(true)),
                ("source", Json::str("manifest")),
            ],
        );
        g.add_edge(pkg_id.clone(), edge::DEPENDS_ON, dep_id, vec![]);
    }

    // Module name per file, and the set of module names defined in this batch
    // (used to tell internal imports from external ones).
    let mut file_modules: Vec<String> = Vec::with_capacity(files.len());
    let mut local_modules: BTreeSet<String> = BTreeSet::new();
    for f in files {
        let name = file_module_name(f);
        local_modules.insert(name.clone());
        file_modules.push(name);
    }

    // Pass B: definition nodes, structural edges, the global function table, and
    // a list of pending callers (every binding, since a nullary binding body can
    // still call functions).
    let mut fn_by_name: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut pend: Vec<Pending> = Vec::new();

    for (idx, f) in files.iter().enumerate() {
        let li = LineIndex::new(f.source);
        let module_name = file_modules[idx].clone();
        let mod_id = format!("module::{module_name}");
        g.upsert_node(
            mod_id.clone(),
            ont::MODULE,
            module_name.clone(),
            vec![("language", Json::str("elm"))],
        );
        g.add_edge(pkg_id.clone(), edge::CONTAINS, mod_id.clone(), vec![]);

        let file_id = format!("file::{}", f.rel_path);
        g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("elm")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        g.add_edge(mod_id.clone(), edge::CONTAINS, file_id.clone(), vec![]);

        for item in f.root.child_nodes() {
            match item.kind {
                cst::IMPORT => {
                    if let Some(m) = import_module(item, f.source) {
                        if local_modules.contains(&m) {
                            g.add_edge(
                                file_id.clone(),
                                edge::IMPORTS,
                                format!("module::{m}"),
                                vec![("path", Json::str(m)), ("external", Json::Bool(false))],
                            );
                        } else {
                            let dep_id = ext_id(&m);
                            g.upsert_node(
                                dep_id.clone(),
                                ont::EXTERNAL_DEPENDENCY,
                                m.clone(),
                                vec![
                                    ("external", Json::Bool(true)),
                                    ("source", Json::str("import")),
                                ],
                            );
                            g.add_edge(
                                file_id.clone(),
                                edge::IMPORTS,
                                dep_id.clone(),
                                vec![("path", Json::str(m)), ("external", Json::Bool(true))],
                            );
                            g.add_edge(pkg_id.clone(), edge::DEPENDS_ON, dep_id, vec![]);
                        }
                    }
                }
                cst::TYPE_CUSTOM | cst::TYPE_ALIAS => {
                    let is_alias = item.kind == cst::TYPE_ALIAS;
                    let kind_tag = if is_alias { "alias" } else { "custom" };
                    if let Some((name, start)) = type_name(item, f.source, is_alias) {
                        let line = li.line_col(start).line;
                        let qual = format!("{module_name}::{name}");
                        let id = format!("type::{qual}");
                        g.upsert_node(
                            id.clone(),
                            ont::TYPE,
                            name,
                            vec![
                                ("type_kind", Json::str(kind_tag)),
                                ("qualified_name", Json::str(qual)),
                                ("language", Json::str("elm")),
                                ("line", Json::U64(line as u64)),
                                ("span_start", Json::U64(item.span.start as u64)),
                                ("span_end", Json::U64(item.span.end as u64)),
                            ],
                        );
                        g.add_edge(mod_id.clone(), edge::DECLARES, id, vec![]);
                    }
                }
                cst::BINDING => {
                    if let Some((name, start, is_fn)) = binding_info(item, f.source) {
                        let line = li.line_col(start).line;
                        let qual = format!("{module_name}::{name}");
                        let id = if is_fn {
                            let id = format!("fn::{qual}#{line}");
                            g.upsert_node(
                                id.clone(),
                                ont::FUNCTION,
                                name.clone(),
                                vec![
                                    ("qualified_name", Json::str(qual)),
                                    ("language", Json::str("elm")),
                                    ("line", Json::U64(line as u64)),
                                    ("span_start", Json::U64(item.span.start as u64)),
                                    ("span_end", Json::U64(item.span.end as u64)),
                                ],
                            );
                            fn_by_name.entry(name.clone()).or_default().push(id.clone());
                            id
                        } else {
                            let id = format!("const::{qual}");
                            g.upsert_node(
                                id.clone(),
                                ont::CONSTANT,
                                name.clone(),
                                vec![
                                    ("binding", Json::str("value")),
                                    ("language", Json::str("elm")),
                                    ("line", Json::U64(line as u64)),
                                ],
                            );
                            id
                        };
                        g.add_edge(mod_id.clone(), edge::DECLARES, id.clone(), vec![]);
                        pend.push(Pending {
                            id,
                            node: item,
                            src: f.source,
                            own: name,
                        });
                    }
                }
                // Module headers, signatures, ports, error items: no node.
                _ => {}
            }
        }
    }

    // Pass C: resolve identifiable applications against the global function table.
    for p in &pend {
        let refs = collect_rhs_idents(p.node, p.src);
        for name in &refs {
            if *name == p.own {
                continue;
            }
            if let Some(ids) = fn_by_name.get(name) {
                emit_call(&mut g, &p.id, name, ids);
            }
        }
    }

    g
}

struct Pending<'a> {
    id: String,
    node: &'a Node,
    src: &'a str,
    own: String,
}

fn emit_call(g: &mut Graph, caller: &str, name: &str, ids: &[String]) {
    if ids.len() == 1 {
        g.add_edge(
            caller.to_string(),
            edge::CALLS,
            ids[0].clone(),
            vec![
                ("callee", Json::str(name.to_string())),
                ("resolved", Json::Bool(true)),
                ("resolution", Json::str("global")),
                ("candidate_count", Json::U64(1)),
            ],
        );
    } else {
        let target = unresolved_id(name);
        g.upsert_node(
            target.clone(),
            ont::UNRESOLVED,
            name.to_string(),
            vec![
                ("unresolved", Json::Bool(true)),
                ("role", Json::str("call")),
            ],
        );
        g.add_edge(
            caller.to_string(),
            edge::CALLS,
            target,
            vec![
                ("callee", Json::str(name.to_string())),
                ("resolved", Json::Bool(false)),
                ("ambiguous", Json::Bool(true)),
                ("resolution", Json::str("ambiguous")),
                ("candidate_count", Json::U64(ids.len() as u64)),
                (
                    "candidates",
                    Json::Array(ids.iter().cloned().map(Json::Str).collect()),
                ),
            ],
        );
    }
}

// --- name / fact extraction over the lossless tree --------------------------

/// A top-level significant leaf of an item: a token or a delimiter group.
enum Leaf<'a> {
    Tok {
        kind: &'static str,
        text: &'a str,
        start: u32,
    },
    Grp(&'a Node),
}

/// Top-level significant leaves of an item (skips trivia and newlines; does not
/// descend into groups).
fn sig_leaves<'a>(node: &'a Node, src: &'a str) -> Vec<Leaf<'a>> {
    let mut v = Vec::new();
    for c in &node.children {
        match c {
            Child::Token(t) if t.trivia || t.kind == tk::NEWLINE => {}
            Child::Token(t) => v.push(Leaf::Tok {
                kind: t.kind,
                text: t.span.text(src),
                start: t.span.start,
            }),
            Child::Node(n) => v.push(Leaf::Grp(n)),
        }
    }
    v
}

/// Module name from a `module X.Y.Z exposing …` header (also `port module …` /
/// `effect module …`): the dotted `conid` path after the `module` keyword.
fn module_decl_name(node: &Node, src: &str) -> Option<String> {
    let leaves = sig_leaves(node, src);
    let mut i = 0;
    while i < leaves.len() {
        if let Leaf::Tok { text, .. } = &leaves[i] {
            if *text == "module" {
                break;
            }
        }
        i += 1;
    }
    i += 1;
    dotted_conid(&leaves, i)
}

/// Imported module name from an `import X.Y [as Z] [exposing (…)]` header: the
/// dotted `conid` path after the `import` keyword (Elm imports have no
/// `qualified` keyword — every import is qualified by default).
fn import_module(node: &Node, src: &str) -> Option<String> {
    let leaves = sig_leaves(node, src);
    let mut i = 0;
    while i < leaves.len() {
        if let Leaf::Tok { text, .. } = &leaves[i] {
            if *text == "import" {
                break;
            }
        }
        i += 1;
    }
    i += 1;
    dotted_conid(&leaves, i)
}

/// Read a dotted constructor path (`A.B.C`) starting at leaf index `from`.
fn dotted_conid(leaves: &[Leaf<'_>], from: usize) -> Option<String> {
    let mut i = from;
    let mut name = String::new();
    while i < leaves.len() {
        match &leaves[i] {
            Leaf::Tok { kind, text, .. } if *kind == tk::CONID => name.push_str(text),
            Leaf::Tok { kind, text, .. } if *kind == tk::OPERATOR && *text == "." => name.push('.'),
            _ => break,
        }
        i += 1;
    }
    if name.is_empty() {
        None
    } else {
        Some(name)
    }
}

/// Declared type name from a `type X …` or `type alias X …` header: the first
/// `conid` after the leading keyword(s). `is_alias` skips the extra `alias` word.
fn type_name(node: &Node, src: &str, is_alias: bool) -> Option<(String, u32)> {
    let leaves = sig_leaves(node, src);
    let start_idx = if is_alias { 2 } else { 1 };
    for l in leaves.iter().skip(start_idx.min(leaves.len())) {
        if let Leaf::Tok { kind, text, start } = l {
            if *kind == tk::CONID {
                return Some((text.to_string(), *start));
            }
        }
    }
    None
}

/// Binding name, its byte offset, and whether it takes arguments (a function) as
/// opposed to a nullary value binding. Handles `name args = …`, an operator in
/// parens `(<|) a b = …`, and a bare value binding `name = …`.
fn binding_info(node: &Node, src: &str) -> Option<(String, u32, bool)> {
    let leaves = sig_leaves(node, src);
    let (name, start) = match leaves.first()? {
        Leaf::Tok { kind, text, start } if *kind == tk::VARID || *kind == tk::CONID => {
            (text.to_string(), *start)
        }
        Leaf::Grp(g) => first_operator(g, src)?,
        _ => return None,
    };
    let eq_pos = leaves.iter().position(
        |l| matches!(l, Leaf::Tok { kind, text, .. } if *kind == tk::OPERATOR && *text == "="),
    );
    // Arguments are the leaves strictly between the head (index 0) and `=`.
    let is_fn = match eq_pos {
        Some(p) => p > 1,
        None => true,
    };
    Some((name, start, is_fn))
}

/// First operator token inside a group (the operator name in `(<|)`).
fn first_operator(g: &Node, src: &str) -> Option<(String, u32)> {
    for c in &g.children {
        if let Child::Token(t) = c {
            if !t.trivia && t.kind == tk::OPERATOR {
                return Some((t.span.text(src).to_string(), t.span.start));
            }
        }
    }
    None
}

/// Identifiers (`varid`/`conid`) on a binding's right-hand side: everything after
/// the first top-level `=` token, descending into groups. Deduplicated.
fn collect_rhs_idents(node: &Node, src: &str) -> BTreeSet<String> {
    let mut set = BTreeSet::new();
    let mut found_eq = false;
    for c in &node.children {
        if !found_eq {
            if let Child::Token(t) = c {
                if !t.trivia && t.kind == tk::OPERATOR && t.span.text(src) == "=" {
                    found_eq = true;
                }
            }
            continue;
        }
        collect_idents(c, src, &mut set);
    }
    set
}

fn collect_idents(c: &Child, src: &str, set: &mut BTreeSet<String>) {
    match c {
        Child::Token(t) if !t.trivia && (t.kind == tk::VARID || t.kind == tk::CONID) => {
            set.insert(t.span.text(src).to_string());
        }
        Child::Token(_) => {}
        Child::Node(n) => {
            for ch in &n.children {
                collect_idents(ch, src, set);
            }
        }
    }
}

// --- pure helpers -----------------------------------------------------------

/// The module name for a file: the `module X exposing …` header if present, else
/// the scope path joined with `.`, else the file stem.
fn file_module_name(f: &SourceFile<'_>) -> String {
    for item in f.root.child_nodes() {
        if item.kind == cst::MODULE {
            if let Some(n) = module_decl_name(item, f.source) {
                return n;
            }
        }
    }
    if !f.module_path.is_empty() {
        return f.module_path.join(".");
    }
    stem(&f.rel_path)
}

fn ext_id(name: &str) -> String {
    format!("ext::{name}")
}

fn unresolved_id(name: &str) -> String {
    format!("unresolved::{name}")
}

fn file_name(rel: &str) -> String {
    rel.rsplit('/').next().unwrap_or(rel).to_string()
}

fn stem(rel: &str) -> String {
    let base = file_name(rel);
    match base.rsplit_once('.') {
        Some((head, _)) => head.to_string(),
        None => base,
    }
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
    use crate::lang::elm::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("Example.elm", src);
        let file = SourceFile {
            rel_path: "Example.elm".to_string(),
            module_path: vec![],
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    #[test]
    fn end_to_end_lossless_round_trip() {
        // A representative snippet: comments, a module header with an export list,
        // qualified and selective imports, a type alias, a custom type, type
        // signatures, a constant, a function, a port, and an application — must
        // reconstruct byte-for-byte.
        let src = "\
module Data.Example exposing (Foo(..), greet, main)

{-| A doc comment. -}
import Html exposing (text)
import Json.Decode as Decode

type alias Name =
    String

type Foo a
    = Bar a
    | Baz

answer : Int
answer =
    42

greet : Foo -> String
greet foo =
    \"hi\"

add : Int -> Int -> Int
add x y =
    x + y

port save : String -> Cmd msg

main =
    text (greet Baz)
";
        let tree = parse("Example.elm", src);
        assert!(tree.is_lossless(), "Elm front end must round-trip source");
    }

    #[test]
    fn emits_module_types_and_functions() {
        let g = graph_for(
            "module Data.Example exposing (..)\n\
             type Foo = Bar | Baz\n\
             type alias Name = String\n\
             add : Int -> Int -> Int\n\
             add x y = x + y\n\
             answer = 42\n",
        );
        assert!(g.has_node("module::Data.Example"));
        assert!(g.nodes().any(|n| n.kind == ont::TYPE && n.name == "Foo"));
        assert!(g.nodes().any(|n| n.kind == ont::TYPE && n.name == "Name"));
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::FUNCTION && n.name == "add"));
        // `answer = 42` is a nullary binding → Constant, not Function.
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::CONSTANT && n.name == "answer"));
    }

    #[test]
    fn type_alias_vs_custom_kind() {
        let g = graph_for("module M exposing (..)\ntype alias Name = String\ntype Color = Red\n");
        let alias = g
            .nodes()
            .find(|n| n.kind == ont::TYPE && n.name == "Name")
            .expect("alias type node");
        assert_eq!(alias.props.get("type_kind"), Some(&Json::str("alias")));
        let custom = g
            .nodes()
            .find(|n| n.kind == ont::TYPE && n.name == "Color")
            .expect("custom type node");
        assert_eq!(custom.props.get("type_kind"), Some(&Json::str("custom")));
    }

    #[test]
    fn resolves_identifiable_call() {
        let g = graph_for(
            "module M exposing (..)\n\
             add x y = x + y\n\
             run z = add z z\n",
        );
        let call = g
            .edges()
            .find(|e| e.kind == edge::CALLS)
            .expect("run should call add");
        assert!(call.to.starts_with("fn::M::add"));
        assert_eq!(call.props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn external_import_creates_dependency() {
        let g = graph_for("module M exposing (..)\nimport Json.Decode as Decode\n");
        assert!(g.has_node("ext::Json.Decode"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::Json.Decode"));
    }

    #[test]
    fn port_and_signature_emit_no_node() {
        let g = graph_for("module M exposing (..)\nport save : String -> Cmd msg\nfoo : Int\n");
        // Neither the port nor the bare signature fabricates a definition node.
        assert!(!g.nodes().any(|n| n.name == "save"));
        assert!(!g.nodes().any(|n| n.name == "foo"));
    }
}
