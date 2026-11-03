//! Lower the OCaml CST into the canonical graph.
//!
//! Honest mapping into the shared ontology:
//! - Each file `foo.ml` / `foo.mli` is its own OCaml module `Foo` (the compiler's
//!   filename-to-module rule) → a [`Module`](crate::ir::ontology::node::MODULE)
//!   node; the package CONTAINS the module, the module CONTAINS its file, and the
//!   module DECLARES every top-level definition.
//! - top-level `let` bindings → [`Function`](crate::ir::ontology::node::FUNCTION)
//!   when they take argument syntax before `=`, else
//!   [`Constant`](crate::ir::ontology::node::CONSTANT) (a value binding). Both are
//!   honest readings of an ML binding.
//! - `type x = …` → [`Type`](crate::ir::ontology::node::TYPE) with a `type_kind`
//!   of `record` / `variant` / `alias` / `abstract`.
//! - `module X = struct … end` and `module type X = sig … end` →
//!   [`Module`](crate::ir::ontology::node::MODULE) nodes (a `module_kind` of
//!   `structure` / `signature`), CONTAINED by the file's module.
//! - `class X = …` → [`Type`](crate::ir::ontology::node::TYPE) (`type_kind`
//!   `class`); each `method m …` inside it →
//!   [`Function`](crate::ir::ontology::node::FUNCTION) with a
//!   [`HAS_METHOD`](crate::ir::ontology::edge::HAS_METHOD) edge from the class.
//! - `open X` / `include X` → an [`IMPORTS`](crate::ir::ontology::edge::IMPORTS)
//!   edge to module `X` (internal when `X` is a module in the batch, otherwise an
//!   explicit [`ExternalDependency`](crate::ir::ontology::node::EXTERNAL_DEPENDENCY)
//!   plus a package-level [`DEPENDS_ON`](crate::ir::ontology::edge::DEPENDS_ON)).
//! - applications we can identify → [`CALLS`](crate::ir::ontology::edge::CALLS):
//!   a value identifier on a binding's right-hand side that names a known
//!   top-level *function* resolves to it (unique ⇒ resolved, several ⇒ ambiguous
//!   with the full `candidates` set). Qualified accesses `M.f` are skipped (the
//!   `f` after a `.` is not resolved against local names), and references to
//!   anything not a project function are never fabricated into edges — there is no
//!   LLM in the airgapped runtime to guess.
//!
//! Deliberate punts (see the module-level report): `val` signatures (in `.mli`),
//! `exception`, and `external` declarations emit no node; nested `let … in`,
//! `let … and …` continuations that are indented, and definitions inside a
//! sub-module's `struct` body are not lifted to definitions (only top-level items
//! of each file become definitions); top-level expression statements emit no
//! node; `USES_TYPE` and inheritance (`inherit`) edges are not emitted (OCaml
//! type-reference extraction is left for a later pass rather than guessed).

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::ocaml::lexer::{is_keyword, kind as tk};
use crate::lang::ocaml::parser::node as cst;

/// Lower a whole package's worth of OCaml files plus manifest dependencies.
pub fn lower(package: &str, files: &[SourceFile<'_>], manifest_deps: &[String]) -> Graph {
    let mut g = Graph::new();
    let pkg_id = format!("pkg::{package}");
    g.upsert_node(
        pkg_id.clone(),
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("opam"))],
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

    // Module name per file (capitalized file stem), and the set of module names in
    // this batch (used to tell internal imports from external ones).
    let mut file_modules: Vec<String> = Vec::with_capacity(files.len());
    let mut local_modules: BTreeSet<String> = BTreeSet::new();
    for f in files {
        let name = file_module_name(f);
        local_modules.insert(name.clone());
        file_modules.push(name);
    }

    // Pass B: definition nodes, structural edges, the global function table, and a
    // list of pending callers (every binding, since a value binding's body can
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
            vec![
                ("language", Json::str("ocaml")),
                ("module_kind", Json::str("structure")),
            ],
        );
        g.add_edge(pkg_id.clone(), edge::CONTAINS, mod_id.clone(), vec![]);

        let file_id = format!("file::{}", f.rel_path);
        g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("ocaml")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        g.add_edge(mod_id.clone(), edge::CONTAINS, file_id.clone(), vec![]);

        for item in f.root.child_nodes() {
            match item.kind {
                cst::OPEN | cst::INCLUDE => {
                    if let Some(m) = opened_module(item, f.source) {
                        let head = top_module_segment(&m);
                        if local_modules.contains(&head) {
                            g.add_edge(
                                file_id.clone(),
                                edge::IMPORTS,
                                format!("module::{head}"),
                                vec![("path", Json::str(m)), ("external", Json::Bool(false))],
                            );
                        } else {
                            let dep_id = ext_id(&head);
                            g.upsert_node(
                                dep_id.clone(),
                                ont::EXTERNAL_DEPENDENCY,
                                head.clone(),
                                vec![
                                    ("external", Json::Bool(true)),
                                    ("source", Json::str("open")),
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
                cst::TYPE_DECL => {
                    if let Some((name, start)) = type_name(item, f.source) {
                        let line = li.line_col(start).line;
                        let qual = format!("{module_name}.{name}");
                        let id = format!("type::{qual}");
                        g.upsert_node(
                            id.clone(),
                            ont::TYPE,
                            name,
                            vec![
                                ("type_kind", Json::str(type_kind(item, f.source))),
                                ("qualified_name", Json::str(qual)),
                                ("language", Json::str("ocaml")),
                                ("line", Json::U64(line as u64)),
                                ("span_start", Json::U64(item.span.start as u64)),
                                ("span_end", Json::U64(item.span.end as u64)),
                            ],
                        );
                        g.add_edge(mod_id.clone(), edge::DECLARES, id, vec![]);
                    }
                }
                cst::MODULE | cst::MODULE_TYPE => {
                    if let Some((name, start)) = module_name_of(item, f.source) {
                        let line = li.line_col(start).line;
                        let qual = format!("{module_name}.{name}");
                        let id = format!("module::{qual}");
                        let mk = if item.kind == cst::MODULE_TYPE {
                            "signature"
                        } else {
                            "structure"
                        };
                        g.upsert_node(
                            id.clone(),
                            ont::MODULE,
                            name,
                            vec![
                                ("language", Json::str("ocaml")),
                                ("module_kind", Json::str(mk)),
                                ("qualified_name", Json::str(qual)),
                                ("line", Json::U64(line as u64)),
                            ],
                        );
                        g.add_edge(mod_id.clone(), edge::CONTAINS, id, vec![]);
                    }
                }
                cst::CLASS => {
                    if let Some((name, start)) = class_name(item, f.source) {
                        let line = li.line_col(start).line;
                        let qual = format!("{module_name}.{name}");
                        let class_id = format!("type::{qual}");
                        g.upsert_node(
                            class_id.clone(),
                            ont::TYPE,
                            name,
                            vec![
                                ("type_kind", Json::str("class")),
                                ("qualified_name", Json::str(qual.clone())),
                                ("language", Json::str("ocaml")),
                                ("line", Json::U64(line as u64)),
                                ("span_start", Json::U64(item.span.start as u64)),
                                ("span_end", Json::U64(item.span.end as u64)),
                            ],
                        );
                        g.add_edge(mod_id.clone(), edge::DECLARES, class_id.clone(), vec![]);
                        for (m_name, m_start) in class_methods(item, f.source) {
                            let m_line = li.line_col(m_start).line;
                            let m_qual = format!("{qual}#{m_name}");
                            let m_id = format!("fn::{m_qual}#{m_line}");
                            g.upsert_node(
                                m_id.clone(),
                                ont::FUNCTION,
                                m_name,
                                vec![
                                    ("qualified_name", Json::str(m_qual)),
                                    ("language", Json::str("ocaml")),
                                    ("method", Json::Bool(true)),
                                    ("line", Json::U64(m_line as u64)),
                                ],
                            );
                            g.add_edge(class_id.clone(), edge::HAS_METHOD, m_id, vec![]);
                        }
                    }
                }
                cst::BINDING => {
                    if let Some((name, start, is_fn)) = binding_info(item, f.source) {
                        let line = li.line_col(start).line;
                        let qual = format!("{module_name}.{name}");
                        let id = if is_fn {
                            let id = format!("fn::{qual}#{line}");
                            g.upsert_node(
                                id.clone(),
                                ont::FUNCTION,
                                name.clone(),
                                vec![
                                    ("qualified_name", Json::str(qual)),
                                    ("language", Json::str("ocaml")),
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
                                    ("language", Json::str("ocaml")),
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
                // val / exception / external / expr / error items: no node.
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

/// A top-level significant leaf of an item: a token or a delimiter/block group.
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

/// Module path of an `open X.Y` / `include X.Y` item: the dotted `conid` path.
fn opened_module(node: &Node, src: &str) -> Option<String> {
    let leaves = sig_leaves(node, src);
    // leaves[0] is `open` / `include`.
    let mut name = String::new();
    for l in leaves.iter().skip(1) {
        match l {
            Leaf::Tok { kind, text, .. } if *kind == tk::CONID => name.push_str(text),
            Leaf::Tok { kind, text, .. } if *kind == tk::OPERATOR && *text == "." => name.push('.'),
            _ => break,
        }
    }
    if name.is_empty() {
        None
    } else {
        Some(name)
    }
}

/// The first (outermost) segment of a dotted module path: `Core.Std` → `Core`.
fn top_module_segment(path: &str) -> String {
    path.split('.').next().unwrap_or(path).to_string()
}

/// Declared module name from a `module [rec] X …` / `module type X …` header: the
/// first `conid` after the leading keyword(s).
fn module_name_of(node: &Node, src: &str) -> Option<(String, u32)> {
    let leaves = sig_leaves(node, src);
    for l in leaves.iter().skip(1) {
        match l {
            Leaf::Tok { text, .. } if *text == "type" || *text == "rec" => continue,
            Leaf::Tok { kind, text, start } if *kind == tk::CONID => {
                return Some((text.to_string(), *start))
            }
            Leaf::Tok { .. } => continue,
            Leaf::Grp(_) => continue,
        }
    }
    None
}

/// Declared class name from a `class [virtual] [type] X …` header: the first
/// lowercase `varid` (skipping the `virtual`/`type`/type-parameter noise).
fn class_name(node: &Node, src: &str) -> Option<(String, u32)> {
    let leaves = sig_leaves(node, src);
    let mut expect_typevar = false;
    for l in leaves.iter().skip(1) {
        match l {
            Leaf::Tok { kind, text, .. } if *kind == tk::PUNCT && *text == "'" => {
                expect_typevar = true;
            }
            Leaf::Tok { text, .. } if is_keyword(text) => continue,
            Leaf::Tok { kind, .. } if *kind == tk::VARID && expect_typevar => {
                expect_typevar = false;
            }
            Leaf::Tok { kind, text, start } if *kind == tk::VARID => {
                return Some((text.to_string(), *start))
            }
            _ => continue,
        }
    }
    None
}

/// Method names (and offsets) inside a class item: every `method [private]
/// [virtual] name …`, found by walking the whole subtree.
fn class_methods(node: &Node, src: &str) -> Vec<(String, u32)> {
    let mut toks: Vec<(&'static str, &str, u32)> = Vec::new();
    flatten_tokens(node, src, &mut toks);
    let mut out = Vec::new();
    let mut i = 0;
    while i < toks.len() {
        if toks[i].1 == "method" {
            // Skip `private` / `virtual` modifiers, then take the next varid.
            let mut j = i + 1;
            while j < toks.len() && matches!(toks[j].1, "private" | "virtual") {
                j += 1;
            }
            if j < toks.len() && toks[j].0 == tk::VARID && !is_keyword(toks[j].1) {
                out.push((toks[j].1.to_string(), toks[j].2));
            }
            i = j + 1;
        } else {
            i += 1;
        }
    }
    out
}

/// Declared type name from a `type [nonrec] params x …` header: the first
/// lowercase `varid` that is not a type variable.
fn type_name(node: &Node, src: &str) -> Option<(String, u32)> {
    let leaves = sig_leaves(node, src);
    let mut expect_typevar = false;
    for l in leaves.iter().skip(1) {
        match l {
            Leaf::Tok { kind, text, .. } if *kind == tk::PUNCT && *text == "'" => {
                expect_typevar = true;
            }
            Leaf::Tok { text, .. } if *text == "nonrec" => continue,
            Leaf::Tok { kind, .. } if *kind == tk::VARID && expect_typevar => {
                expect_typevar = false;
            }
            Leaf::Tok { kind, text, start } if *kind == tk::VARID && !is_keyword(text) => {
                return Some((text.to_string(), *start))
            }
            Leaf::Grp(_) => continue, // ('a, 'b) parameter group / variance
            Leaf::Tok { kind, .. } if *kind == tk::OPERATOR => continue, // +/- variance
            _ => continue,
        }
    }
    None
}

/// `record` / `variant` / `alias` / `abstract`, inferred from the right-hand side.
fn type_kind(node: &Node, src: &str) -> &'static str {
    let leaves = sig_leaves(node, src);
    let eq = leaves.iter().position(
        |l| matches!(l, Leaf::Tok { kind, text, .. } if *kind == tk::OPERATOR && *text == "="),
    );
    let eq = match eq {
        Some(p) => p,
        None => return "abstract",
    };
    // A `{ … }` group ⇒ record; a `|` at top level ⇒ variant; otherwise a leading
    // constructor (single-constructor variant) ⇒ variant, else an alias.
    let mut first_is_conid = false;
    let mut seen_first = false;
    for l in &leaves[eq + 1..] {
        match l {
            Leaf::Grp(n) if n.kind == cst::BRACE => return "record",
            Leaf::Tok { kind, text, .. } if *kind == tk::OPERATOR && text.contains('|') => {
                return "variant"
            }
            Leaf::Tok { kind, .. } if !seen_first => {
                first_is_conid = *kind == tk::CONID;
                seen_first = true;
            }
            Leaf::Grp(_) if !seen_first => seen_first = true,
            _ => {}
        }
    }
    if first_is_conid {
        "variant"
    } else {
        "alias"
    }
}

/// Binding name, its byte offset, and whether it takes argument syntax (a
/// function) as opposed to a value binding. Handles `let name args = …`,
/// operator-in-parens `let (>>=) a b = …`, and value bindings `let name = …` /
/// `let name : ty = …`. Returns `None` for pattern bindings (`let (a, b) = …`,
/// `let () = …`) — those are punted.
fn binding_info(node: &Node, src: &str) -> Option<(String, u32, bool)> {
    let leaves = sig_leaves(node, src);
    // Skip the leading `let` / `and`, and an optional `rec`.
    let mut i = 1;
    if let Some(Leaf::Tok { text, .. }) = leaves.get(i) {
        if *text == "rec" {
            i += 1;
        }
    }
    let (name, start) = match leaves.get(i)? {
        Leaf::Tok { kind, text, start } if *kind == tk::VARID && !is_keyword(text) => {
            (text.to_string(), *start)
        }
        Leaf::Grp(g) => {
            // `(op)` operator binding; a parenthesized pattern has no lone operator.
            first_operator(g, src)?
        }
        _ => return None,
    };
    // Parameters are the leaves between the name and the first top-level `:`
    // (type annotation) or `=` (definition), whichever comes first.
    // It is a function iff the first leaf after the name is neither `=` nor `:`
    // (i.e. there is a parameter before the type annotation / definition).
    let is_fn = match leaves.get(i + 1) {
        Some(Leaf::Tok { kind, text, .. })
            if *kind == tk::OPERATOR && (*text == "=" || *text == ":") =>
        {
            false
        }
        Some(_) => true,
        None => false,
    };
    Some((name, start, is_fn))
}

/// First operator token inside a group (the operator name in `(>>=)`).
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

/// Value identifiers (`varid`, non-keyword) on a binding's right-hand side:
/// everything after the first top-level `=` token, descending into groups.
/// Qualified accesses (`M.f` — a `varid` directly after a `.`) are skipped so a
/// foreign `f` is not resolved against a local `f`. Deduplicated.
fn collect_rhs_idents(node: &Node, src: &str) -> BTreeSet<String> {
    // Flatten the whole item's tokens in source order, find the first top-level
    // `=`, then scan the remainder tracking the previous token to drop qualified
    // names.
    let mut toks: Vec<(&'static str, &str, u32)> = Vec::new();
    flatten_tokens(node, src, &mut toks);
    let mut set = BTreeSet::new();
    let mut found_eq = false;
    let mut prev: Option<&str> = None;
    for &(kind, text, _) in &toks {
        if !found_eq {
            if kind == tk::OPERATOR && text == "=" {
                found_eq = true;
            }
            continue;
        }
        if kind == tk::VARID && !is_keyword(text) && prev != Some(".") {
            set.insert(text.to_string());
        }
        prev = Some(text);
    }
    set
}

/// Append every non-trivia token in the subtree to `out`, in source order.
fn flatten_tokens<'a>(node: &'a Node, src: &'a str, out: &mut Vec<(&'static str, &'a str, u32)>) {
    for c in &node.children {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => out.push((t.kind, t.span.text(src), t.span.start)),
            Child::Node(n) => flatten_tokens(n, src, out),
        }
    }
}

// --- pure helpers -----------------------------------------------------------

/// The OCaml module name for a file: the capitalized file stem (the compiler's
/// `foo.ml` → module `Foo` rule).
fn file_module_name(f: &SourceFile<'_>) -> String {
    capitalize(&stem(&f.rel_path))
}

fn capitalize(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
        None => String::new(),
    }
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
    use crate::lang::ocaml::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("example.ml", src);
        let file = SourceFile {
            rel_path: "example.ml".to_string(),
            module_path: vec![],
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    #[test]
    fn end_to_end_lossless_round_trip() {
        let src = "\
(* | Example module. *)
open Printf

type 'a tree =
  | Leaf
  | Node of 'a tree * 'a * 'a tree

type point = { x : int; y : int }

module M = struct
  let secret = 42
  let bump n = n + secret
end

class counter = object
  val mutable n = 0
  method incr = n <- n + 1
end

let answer = 42

let add x y = x + y

let main () =
  let m = add answer 1 in
  printf \"%d\\n\" m
;;
";
        let tree = parse("example.ml", src);
        assert!(tree.is_lossless(), "OCaml front end must round-trip source");
    }

    #[test]
    fn emits_module_types_and_functions() {
        let g = graph_for(
            "type foo = Bar | Baz\n\
             let add x y = x + y\n\
             let answer = 42\n",
        );
        assert!(g.has_node("module::Example"));
        assert!(g.nodes().any(|n| n.kind == ont::TYPE && n.name == "foo"));
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::FUNCTION && n.name == "add"));
        // `let answer = 42` is a value binding → Constant, not Function.
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::CONSTANT && n.name == "answer"));
    }

    #[test]
    fn type_kinds_are_classified() {
        let g = graph_for(
            "type r = { a : int; b : int }\n\
             type v = A | B of int\n\
             type alias = int list\n",
        );
        let kind_of = |name: &str| {
            g.nodes()
                .find(|n| n.kind == ont::TYPE && n.name == name)
                .and_then(|n| n.props.get("type_kind"))
                .cloned()
        };
        assert_eq!(kind_of("r"), Some(Json::str("record")));
        assert_eq!(kind_of("v"), Some(Json::str("variant")));
        assert_eq!(kind_of("alias"), Some(Json::str("alias")));
    }

    #[test]
    fn class_emits_type_and_methods() {
        let g = graph_for(
            "class point = object\n\
               method get_x = 0\n\
               method move dx = dx\n\
             end\n",
        );
        assert!(g.nodes().any(|n| n.kind == ont::TYPE
            && n.name == "point"
            && n.props.get("type_kind") == Some(&Json::str("class"))));
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::FUNCTION && n.name == "get_x"));
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::FUNCTION && n.name == "move"));
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD));
    }

    #[test]
    fn submodule_is_contained() {
        let g = graph_for("module M = struct let x = 1 end\n");
        assert!(g.has_node("module::Example.M"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::CONTAINS && e.to == "module::Example.M"));
    }

    #[test]
    fn module_type_is_a_signature_module() {
        let g = graph_for("module type S = sig val run : unit -> unit end\n");
        let m = g
            .nodes()
            .find(|n| n.kind == ont::MODULE && n.name == "S")
            .expect("module type S should be a Module node");
        assert_eq!(m.props.get("module_kind"), Some(&Json::str("signature")));
    }

    #[test]
    fn resolves_identifiable_call() {
        let g = graph_for(
            "let add x y = x + y\n\
             let run z = add z z\n",
        );
        let call = g
            .edges()
            .find(|e| e.kind == edge::CALLS)
            .expect("run should call add");
        assert!(call.to.starts_with("fn::Example.add"));
        assert_eq!(call.props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn operator_binding_is_a_function() {
        let g = graph_for("let ( >>= ) m f = f m\n");
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::FUNCTION && n.name == ">>="));
    }

    #[test]
    fn external_open_creates_dependency() {
        let g = graph_for("open Printf\nlet () = printf \"hi\"\n");
        assert!(g.has_node("ext::Printf"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::Printf"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::IMPORTS && e.to == "ext::Printf"));
    }

    #[test]
    fn qualified_access_is_not_a_local_call() {
        // `List.length` must not resolve to a local `length`.
        let g = graph_for(
            "let length x = x\n\
             let run l = List.length l\n",
        );
        assert!(
            !g.edges().any(|e| e.kind == edge::CALLS),
            "qualified M.f should not resolve to a local f"
        );
    }
}
