//! Lower the Haskell CST into the canonical graph.
//!
//! Honest mapping into the shared ontology:
//! - `module X where` → a [`Module`](crate::ir::ontology::node::MODULE) node; the
//!   package CONTAINS the module, the module CONTAINS its file, and the module
//!   DECLARES every top-level definition. When a file has no module header, the
//!   module name falls back to the file's scope path / stem.
//! - top-level bindings → [`Function`](crate::ir::ontology::node::FUNCTION) when
//!   they take arguments, else [`Constant`](crate::ir::ontology::node::CONSTANT)
//!   (a nullary CAF). Both are honest readings of a lambda-calculus binding.
//! - `data` / `newtype` / `type` / `class` / `instance` →
//!   [`Type`](crate::ir::ontology::node::TYPE) with a `type_kind` of
//!   `data` / `newtype` / `alias` / `typeclass` / `instance`.
//! - `import` → an [`IMPORTS`](crate::ir::ontology::edge::IMPORTS) edge to the
//!   imported module (internal when that module is in the batch, otherwise an
//!   explicit [`ExternalDependency`](crate::ir::ontology::node::EXTERNAL_DEPENDENCY)
//!   plus a package-level [`DEPENDS_ON`](crate::ir::ontology::edge::DEPENDS_ON)).
//! - applications we can identify → [`CALLS`](crate::ir::ontology::edge::CALLS):
//!   an identifier in a binding's right-hand side that names a known top-level
//!   *function* resolves to it (unique ⇒ resolved, several ⇒ ambiguous with the
//!   full `candidates` set). References to anything not a project function are
//!   not fabricated into edges — there is no LLM in the airgapped runtime to
//!   guess.
//!
//! Deliberate punts (see the module-level report): type signatures, fixity, and
//! `foreign` declarations emit no node; nested `where` / instance-method bindings
//! are not lifted to definitions (only top-level bindings become functions);
//! superclass / deriving relationships are not turned into `EXTENDS`; and
//! `USES_TYPE` is not emitted (Haskell type-reference extraction is left for a
//! later pass rather than guessed).

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::haskell::lexer::kind as tk;
use crate::lang::haskell::parser::node as cst;

/// Lower a whole package's worth of Haskell files plus manifest dependencies.
pub fn lower(package: &str, files: &[SourceFile<'_>], manifest_deps: &[String]) -> Graph {
    let mut g = Graph::new();
    let pkg_id = format!("pkg::{package}");
    g.upsert_node(
        pkg_id.clone(),
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("cabal"))],
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
    // a list of pending callers (every binding, since a nullary CAF body can
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
            vec![("language", Json::str("haskell"))],
        );
        g.add_edge(pkg_id.clone(), edge::CONTAINS, mod_id.clone(), vec![]);

        let file_id = format!("file::{}", f.rel_path);
        g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("haskell")),
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
                cst::DATA | cst::NEWTYPE | cst::TYPE_ALIAS | cst::CLASS | cst::INSTANCE => {
                    let kind_tag = type_kind(item.kind);
                    let after_ctx = matches!(item.kind, cst::CLASS | cst::INSTANCE);
                    if let Some((name, start)) = type_name(item, f.source, after_ctx) {
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
                                ("language", Json::str("haskell")),
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
                                    ("language", Json::str("haskell")),
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
                                    ("language", Json::str("haskell")),
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
                // Signatures, fixity, foreign, module, error items: no node.
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

fn type_kind(item_kind: &str) -> &'static str {
    match item_kind {
        cst::DATA => "data",
        cst::NEWTYPE => "newtype",
        cst::TYPE_ALIAS => "alias",
        cst::CLASS => "typeclass",
        cst::INSTANCE => "instance",
        _ => "type",
    }
}

/// Module name from a `module X.Y.Z where` header: the dotted `conid` path.
fn module_decl_name(node: &Node, src: &str) -> Option<String> {
    let leaves = sig_leaves(node, src);
    let mut i = 0;
    // Find the `module` keyword.
    while i < leaves.len() {
        if let Leaf::Tok { text, .. } = &leaves[i] {
            if *text == "module" {
                break;
            }
        }
        i += 1;
    }
    i += 1;
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

/// Imported module name from an `import [qualified] X.Y [as Z] …` header.
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
    // Optional `qualified`.
    if let Some(Leaf::Tok { text, .. }) = leaves.get(i) {
        if *text == "qualified" {
            i += 1;
        }
    }
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

/// Declared type name from a `data`/`newtype`/`type`/`class`/`instance` header.
/// When `after_context`, the name is the first `conid` after a `=>` (the class /
/// instance head), else the first `conid` after the leading keyword.
fn type_name(node: &Node, src: &str, after_context: bool) -> Option<(String, u32)> {
    let leaves = sig_leaves(node, src);
    let mut start_idx = 1; // skip the leading keyword
    if after_context {
        if let Some(p) = leaves.iter().position(
            |l| matches!(l, Leaf::Tok { kind, text, .. } if *kind == tk::OPERATOR && *text == "=>"),
        ) {
            start_idx = p + 1;
        }
    }
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
/// opposed to a nullary value binding. Handles `name args = …`, operator-in-
/// parens `(<>) a b = …`, and bare value bindings `name = …`.
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

/// First operator token inside a group (the operator name in `(<>)`).
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

/// The module name for a file: the `module X where` header if present, else the
/// scope path joined with `.`, else the file stem.
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
    use crate::lang::haskell::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("Example.hs", src);
        let file = SourceFile {
            rel_path: "Example.hs".to_string(),
            module_path: vec![],
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    #[test]
    fn end_to_end_lossless_round_trip() {
        // A representative snippet: comments, a pragma, a module header with an
        // export list, qualified and selective imports, a type alias, a newtype,
        // an ADT with deriving, a class, an instance, type signatures, a value
        // binding, a function, and a `do` block — must reconstruct byte-for-byte.
        let src = "\
-- | Example module.
{-# LANGUAGE OverloadedStrings #-}
module Data.Example
  ( Foo(..)
  , greet
  ) where

import Data.Maybe (fromMaybe)
import qualified Data.Map as Map

type Name = String

newtype Age = Age Int

data Foo a
  = Bar a
  | Baz
  deriving (Show, Eq)

class Greet a where
  greet :: a -> String

instance Greet Foo where
  greet Baz = \"baz\"
  greet (Bar _) = \"bar\"

answer :: Int
answer = 42

add :: Int -> Int -> Int
add x y = x + y

main :: IO ()
main = do
  let n = add answer 1
  putStrLn (greet Baz)
";
        let tree = parse("Example.hs", src);
        assert!(
            tree.is_lossless(),
            "Haskell front end must round-trip source"
        );
    }

    #[test]
    fn emits_module_types_and_functions() {
        let g = graph_for(
            "module Data.Example where\n\
             data Foo = Bar | Baz\n\
             add :: Int -> Int -> Int\n\
             add x y = x + y\n\
             answer = 42\n",
        );
        assert!(g.has_node("module::Data.Example"));
        assert!(g.nodes().any(|n| n.kind == ont::TYPE && n.name == "Foo"));
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::FUNCTION && n.name == "add"));
        // `answer = 42` is a nullary binding → Constant, not Function.
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::CONSTANT && n.name == "answer"));
    }

    #[test]
    fn resolves_identifiable_call() {
        let g = graph_for(
            "module M where\n\
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
        let g = graph_for("module M where\nimport qualified Data.Map as Map\n");
        assert!(g.has_node("ext::Data.Map"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::Data.Map"));
    }
}
