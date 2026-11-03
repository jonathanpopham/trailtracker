//! Lower the F# CST into the canonical graph.
//!
//! Honest mapping into the shared ontology:
//! - `namespace X` / `module X` → a [`Module`](crate::ir::ontology::node::MODULE)
//!   node; the package CONTAINS the module, the module CONTAINS its file, and the
//!   module DECLARES every top-level definition. When a file has neither header,
//!   the module name falls back to the file's scope path / stem.
//! - top-level `let` bindings → [`Function`](crate::ir::ontology::node::FUNCTION)
//!   when they take parameters, else [`Constant`](crate::ir::ontology::node::CONSTANT)
//!   (a nullary value binding). Both are honest readings of a binding.
//! - `type X = …` (records, discriminated unions, classes, interfaces, structs,
//!   abbreviations) → [`Type`](crate::ir::ontology::node::TYPE) with a
//!   `type_kind` of `record` / `union` / `class` / `interface` / `struct` /
//!   `type`.
//! - `member` / `static member` / `abstract` / `override` inside a type →
//!   [`Function`](crate::ir::ontology::node::FUNCTION) with a
//!   [`HAS_METHOD`](crate::ir::ontology::edge::HAS_METHOD) edge from the enclosing
//!   type (and a `DECLARES` from the module).
//! - `inherit Base` → [`EXTENDS`](crate::ir::ontology::edge::EXTENDS);
//!   `interface I with …` → [`IMPLEMENTS`](crate::ir::ontology::edge::IMPLEMENTS).
//!   The syntax tells us which, so neither is guessed: the target is the unique
//!   project type when one exists, else an explicit
//!   [`UnresolvedSymbol`](crate::ir::ontology::node::UNRESOLVED) (a framework base
//!   we cannot see in an airgap).
//! - `open X` → an [`IMPORTS`](crate::ir::ontology::edge::IMPORTS) edge to the
//!   opened module (internal when that module is in the batch, otherwise an
//!   explicit [`ExternalDependency`](crate::ir::ontology::node::EXTERNAL_DEPENDENCY)
//!   plus a package-level [`DEPENDS_ON`](crate::ir::ontology::edge::DEPENDS_ON)).
//! - applications we can identify → [`CALLS`](crate::ir::ontology::edge::CALLS):
//!   an identifier in a binding's or member's right-hand side that names a known
//!   project function/method resolves to it (unique ⇒ resolved, several ⇒
//!   ambiguous with the full `candidates` set). References to anything not a
//!   project definition are not fabricated — there is no LLM in the airgapped
//!   runtime to guess.
//!
//! Deliberate punts (see the module-level report): the interior of an indented
//! `module X =` block is captured losslessly but its nested definitions are not
//! lifted (only column-0 top-level items and `type` members become nodes);
//! record fields, DU cases, and constructors emit no node; `USES_TYPE` is not
//! emitted (F# type-reference extraction is left for a later pass rather than
//! guessed); `do`-bindings and module-level expressions are not scanned for
//! calls.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::fsharp::lexer::{is_keyword, kind as tk};
use crate::lang::fsharp::parser::node as cst;

/// Lower a whole package's worth of F# files plus manifest dependencies.
pub fn lower(package: &str, files: &[SourceFile<'_>], manifest_deps: &[String]) -> Graph {
    let mut g = Graph::new();
    let pkg_id = format!("pkg::{package}");
    g.upsert_node(
        pkg_id.clone(),
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("nuget"))],
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

    // Primary module name per file, and the set of namespace/module names defined
    // anywhere in this batch (used to tell internal opens from external ones).
    let mut file_modules: Vec<String> = Vec::with_capacity(files.len());
    let mut local_modules: BTreeSet<String> = BTreeSet::new();
    for f in files {
        let name = file_module_name(f);
        local_modules.insert(name.clone());
        file_modules.push(name);
        // Also record every namespace/module header so opens onto secondary
        // scopes resolve as internal.
        for item in f.root.child_nodes() {
            if matches!(item.kind, cst::NAMESPACE | cst::MODULE) {
                if let Some(n) = dotted_decl_name(item, f.source) {
                    local_modules.insert(n);
                }
            }
        }
    }

    // Tables built in pass 1 and consulted in pass 2.
    let mut fn_by_name: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut method_by_name: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut type_by_name: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut links: Vec<PendingLink> = Vec::new();
    let mut calls: Vec<PendingCall> = Vec::new();

    // Pass 1: definition nodes + structural edges + global tables.
    for (idx, f) in files.iter().enumerate() {
        let li = LineIndex::new(f.source);
        let module_name = file_modules[idx].clone();
        let mod_id = format!("module::{module_name}");
        g.upsert_node(
            mod_id.clone(),
            ont::MODULE,
            module_name.clone(),
            vec![("language", Json::str("fsharp"))],
        );
        g.add_edge(pkg_id.clone(), edge::CONTAINS, mod_id.clone(), vec![]);

        let file_id = format!("file::{}", f.rel_path);
        g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("fsharp")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        g.add_edge(mod_id.clone(), edge::CONTAINS, file_id.clone(), vec![]);

        for item in f.root.child_nodes() {
            match item.kind {
                cst::NAMESPACE | cst::MODULE => {
                    // The primary scope is already created above. A secondary
                    // namespace/module header still earns its own Module node so
                    // imports onto it resolve internally.
                    if let Some(n) = dotted_decl_name(item, f.source) {
                        if n != module_name {
                            let id = format!("module::{n}");
                            g.upsert_node(
                                id.clone(),
                                ont::MODULE,
                                n,
                                vec![("language", Json::str("fsharp"))],
                            );
                            g.add_edge(pkg_id.clone(), edge::CONTAINS, id, vec![]);
                        }
                    }
                }
                cst::OPEN => {
                    if let Some(m) = dotted_decl_name(item, f.source) {
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
                    let leaves = sig_leaves(item, f.source);
                    if let Some((type_name, start)) = type_decl_name(&leaves) {
                        let line = li.line_col(start).line;
                        let qual = format!("{module_name}::{type_name}");
                        let type_id = format!("type::{qual}");
                        let kind_tag = type_kind(&leaves);
                        g.upsert_node(
                            type_id.clone(),
                            ont::TYPE,
                            type_name.clone(),
                            vec![
                                ("type_kind", Json::str(kind_tag)),
                                ("qualified_name", Json::str(qual.clone())),
                                ("language", Json::str("fsharp")),
                                ("line", Json::U64(line as u64)),
                                ("span_start", Json::U64(item.span.start as u64)),
                                ("span_end", Json::U64(item.span.end as u64)),
                            ],
                        );
                        g.add_edge(mod_id.clone(), edge::DECLARES, type_id.clone(), vec![]);
                        type_by_name
                            .entry(type_name)
                            .or_default()
                            .push(type_id.clone());

                        // Members, inherit, interface — all top-level leaves of
                        // the (indented) type body.
                        scan_type_body(
                            &leaves,
                            f.source,
                            &li,
                            &qual,
                            &type_id,
                            &mod_id,
                            &mut g,
                            &mut method_by_name,
                            &mut calls,
                            &mut links,
                        );
                    }
                }
                cst::BINDING => {
                    let leaves = sig_leaves(item, f.source);
                    if let Some((name, start, is_fn)) = binding_info(&leaves, f.source) {
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
                                    ("language", Json::str("fsharp")),
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
                                    ("language", Json::str("fsharp")),
                                    ("line", Json::U64(line as u64)),
                                ],
                            );
                            id
                        };
                        g.add_edge(mod_id.clone(), edge::DECLARES, id.clone(), vec![]);
                        calls.push(PendingCall {
                            id,
                            idents: collect_rhs_idents(item, f.source),
                            own: name,
                        });
                    }
                }
                // Open's secondary, members at column 0, do-bindings, errors: no node.
                _ => {}
            }
        }
    }

    // Pass 2a: resolve inheritance / interface implementation links.
    for l in &links {
        let target = match unique(&type_by_name, &l.base_name) {
            Some(id) => id,
            None => {
                let id = unresolved_id(&l.base_name);
                if !g.has_node(&id) {
                    g.upsert_node(
                        id.clone(),
                        ont::UNRESOLVED,
                        l.base_name.clone(),
                        vec![
                            ("unresolved", Json::Bool(true)),
                            ("role", Json::str("base_type")),
                        ],
                    );
                }
                id
            }
        };
        g.add_edge(
            l.type_id.clone(),
            l.edge_kind,
            target,
            vec![("base_name", Json::str(l.base_name.clone()))],
        );
    }

    // Pass 2b: resolve identifiable applications against the global tables.
    for c in &calls {
        for name in &c.idents {
            if *name == c.own {
                continue;
            }
            let mut ids = fn_by_name.get(name).cloned().unwrap_or_default();
            if let Some(m) = method_by_name.get(name) {
                ids.extend(m.iter().cloned());
            }
            if !ids.is_empty() {
                emit_call(&mut g, &c.id, name, &ids);
            }
        }
    }

    g
}

struct PendingLink {
    type_id: String,
    base_name: String,
    edge_kind: &'static str,
}

struct PendingCall {
    id: String,
    idents: BTreeSet<String>,
    own: String,
}

#[allow(clippy::too_many_arguments)]
fn scan_type_body(
    leaves: &[Leaf<'_>],
    src: &str,
    li: &LineIndex,
    type_qual: &str,
    type_id: &str,
    mod_id: &str,
    g: &mut Graph,
    method_by_name: &mut BTreeMap<String, Vec<String>>,
    calls: &mut Vec<PendingCall>,
    links: &mut Vec<PendingLink>,
) {
    // Indices of the leaves that begin a member head, so each member's body runs
    // to the next head (or the end of the type).
    let mut head_idxs: Vec<usize> = Vec::new();
    for k in 0..leaves.len() {
        if is_member_head(leaves, k) {
            head_idxs.push(k);
        }
    }

    for (h, &k) in head_idxs.iter().enumerate() {
        if let Some((name, start)) = member_name(leaves, k) {
            let line = li.line_col(start).line;
            let qual = format!("{type_qual}.{name}");
            let id = format!("method::{type_qual}::{name}#{line}");
            g.upsert_node(
                id.clone(),
                ont::FUNCTION,
                name.clone(),
                vec![
                    ("qualified_name", Json::str(qual)),
                    ("language", Json::str("fsharp")),
                    ("kind", Json::str("method")),
                    ("line", Json::U64(line as u64)),
                ],
            );
            g.add_edge(type_id.to_string(), edge::HAS_METHOD, id.clone(), vec![]);
            g.add_edge(mod_id.to_string(), edge::DECLARES, id.clone(), vec![]);
            method_by_name
                .entry(name.clone())
                .or_default()
                .push(id.clone());

            // Member body: from this head to the next member head (or end).
            let end = head_idxs.get(h + 1).copied().unwrap_or(leaves.len());
            calls.push(PendingCall {
                id,
                idents: collect_leaf_rhs_idents(&leaves[k..end], src),
                own: name,
            });
        }
    }

    // `inherit Base(...)` and `interface IFoo with ...`.
    for k in 0..leaves.len() {
        if let Leaf::Tok { kind, text, .. } = &leaves[k] {
            if *kind != tk::IDENT {
                continue;
            }
            if *text == "inherit" {
                if let Some((base, _)) = dotted_from(leaves, k + 1) {
                    links.push(PendingLink {
                        type_id: type_id.to_string(),
                        base_name: base,
                        edge_kind: edge::EXTENDS,
                    });
                }
            } else if *text == "interface" {
                // Distinguish an interface *implementation* (`interface I with`)
                // from defining the type itself as an interface (`type T =
                // interface … end`, where `interface` follows the body `=`).
                if prev_sig_is_eq(leaves, k) {
                    continue;
                }
                if let Some((base, _)) = dotted_from(leaves, k + 1) {
                    links.push(PendingLink {
                        type_id: type_id.to_string(),
                        base_name: base,
                        edge_kind: edge::IMPLEMENTS,
                    });
                }
            }
        }
    }
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

/// `type_kind` from the body that follows the first `=`.
fn type_kind(leaves: &[Leaf<'_>]) -> &'static str {
    let eq = leaves.iter().position(
        |l| matches!(l, Leaf::Tok { kind, text, .. } if *kind == tk::OPERATOR && *text == "="),
    );
    let body = match eq {
        Some(p) => &leaves[(p + 1).min(leaves.len())..],
        None => leaves,
    };
    // The first significant leaf after `=` often names the flavor outright.
    if let Some(Leaf::Tok { kind, text, .. }) = body.first() {
        if *kind == tk::IDENT {
            match *text {
                "class" => return "class",
                "struct" => return "struct",
                "interface" => return "interface",
                "delegate" => return "delegate",
                _ => {}
            }
        }
    }
    // Otherwise infer from shape: a record has a brace group; a DU has a
    // top-level `|`.
    if body
        .iter()
        .any(|l| matches!(l, Leaf::Grp(n) if n.kind == cst::BRACE))
    {
        return "record";
    }
    if body
        .iter()
        .any(|l| matches!(l, Leaf::Tok { kind, text, .. } if *kind == tk::OPERATOR && *text == "|"))
    {
        return "union";
    }
    "type"
}

/// Declared type name: the first non-keyword identifier after the leading `type`
/// keyword (skipping access modifiers).
fn type_decl_name(leaves: &[Leaf<'_>]) -> Option<(String, u32)> {
    let kw = leaves.iter().position(
        |l| matches!(l, Leaf::Tok { kind, text, .. } if *kind == tk::IDENT && *text == "type"),
    )?;
    for l in leaves.iter().skip(kw + 1) {
        if let Leaf::Tok { kind, text, start } = l {
            if *kind == tk::IDENT && !is_keyword(text) {
                return Some((text.to_string(), *start));
            }
        }
    }
    None
}

/// Binding name, its byte offset, and whether it takes parameters (a function)
/// as opposed to a nullary value binding. Handles `let [rec] name args = …`,
/// operator-in-parens `let (<+>) a b = …`, and `let name = …`.
fn binding_info(leaves: &[Leaf<'_>], src: &str) -> Option<(String, u32, bool)> {
    let kw = leaves.iter().position(|l| {
        matches!(l, Leaf::Tok { kind, text, .. }
            if *kind == tk::IDENT && matches!(*text, "let" | "use" | "extern"))
    })?;
    // Skip binding modifiers to reach the name.
    let mut i = kw + 1;
    while let Some(Leaf::Tok { kind, text, .. }) = leaves.get(i) {
        if *kind == tk::IDENT
            && matches!(
                *text,
                "rec" | "mutable" | "inline" | "private" | "internal" | "public"
            )
        {
            i += 1;
        } else {
            break;
        }
    }
    let (name, start, name_idx) = match leaves.get(i)? {
        Leaf::Tok { kind, text, start } if *kind == tk::IDENT && !is_keyword(text) => {
            (text.to_string(), *start, i)
        }
        Leaf::Grp(g) => {
            let (n, s) = first_operator(g, src)?;
            (n, s, i)
        }
        _ => return None,
    };
    let eq = leaves
        .iter()
        .skip(name_idx + 1)
        .position(
            |l| matches!(l, Leaf::Tok { kind, text, .. } if *kind == tk::OPERATOR && *text == "="),
        )
        .map(|p| p + name_idx + 1);
    // A leading `:` right after the name is a value type-annotation (no params).
    if let Some(Leaf::Tok { kind, text, .. }) = leaves.get(name_idx + 1) {
        if *kind == tk::OPERATOR && *text == ":" {
            return Some((name, start, false));
        }
    }
    let is_fn = match eq {
        Some(p) => p > name_idx + 1,
        None => leaves.len() > name_idx + 1,
    };
    Some((name, start, is_fn))
}

/// First operator token inside a group (the operator name in `(<+>)`).
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

/// Method-introducing keywords. A head starts at one of these whose previous
/// significant leaf is not itself one (so `abstract member` and `static member`
/// each count once).
fn is_method_kw(text: &str) -> bool {
    matches!(text, "member" | "abstract" | "override" | "default")
}

fn is_member_head(leaves: &[Leaf<'_>], k: usize) -> bool {
    match &leaves[k] {
        Leaf::Tok { kind, text, .. } if *kind == tk::IDENT && is_method_kw(text) => {
            if k == 0 {
                return true;
            }
            !matches!(
                &leaves[k - 1],
                Leaf::Tok { kind, text, .. } if *kind == tk::IDENT && is_method_kw(text)
            )
        }
        _ => false,
    }
}

/// The method name for a head at `k`: skip member modifiers and an optional
/// self-identifier (`this.`), then take the identifier.
fn member_name(leaves: &[Leaf<'_>], k: usize) -> Option<(String, u32)> {
    let mut i = k;
    // Skip the run of member/modifier keywords (`abstract member`, `static
    // member`, `member val`, …).
    while let Some(Leaf::Tok { kind, text, .. }) = leaves.get(i) {
        if *kind == tk::IDENT
            && (is_method_kw(text)
                || matches!(
                    *text,
                    "static" | "val" | "inline" | "mutable" | "private" | "internal" | "public"
                ))
        {
            i += 1;
        } else {
            break;
        }
    }
    let (first, first_start) = match leaves.get(i)? {
        Leaf::Tok { kind, text, start } if *kind == tk::IDENT => (text.to_string(), *start),
        _ => return None,
    };
    // `this.Name` — a self identifier followed by a dot, then the real name.
    if let Some(Leaf::Tok { kind, text, .. }) = leaves.get(i + 1) {
        if *kind == tk::OPERATOR && *text == "." {
            if let Some(Leaf::Tok { kind, text, start }) = leaves.get(i + 2) {
                if *kind == tk::IDENT {
                    return Some((text.to_string(), *start));
                }
            }
        }
    }
    Some((first, first_start))
}

/// A dotted identifier path starting at leaf `i` (`A.B.C`).
fn dotted_from(leaves: &[Leaf<'_>], i: usize) -> Option<(String, u32)> {
    let mut name = String::new();
    let mut start = None;
    let mut j = i;
    while let Some(l) = leaves.get(j) {
        match l {
            Leaf::Tok {
                kind,
                text,
                start: s,
            } if *kind == tk::IDENT && !is_keyword(text) => {
                if start.is_none() {
                    start = Some(*s);
                }
                name.push_str(text);
            }
            Leaf::Tok { kind, text, .. } if *kind == tk::OPERATOR && *text == "." => name.push('.'),
            _ => break,
        }
        j += 1;
    }
    match (name.is_empty(), start) {
        (false, Some(s)) => Some((name, s)),
        _ => None,
    }
}

/// Whether the previous significant leaf before `k` is a `=` operator.
fn prev_sig_is_eq(leaves: &[Leaf<'_>], k: usize) -> bool {
    if k == 0 {
        return false;
    }
    matches!(&leaves[k - 1], Leaf::Tok { kind, text, .. } if *kind == tk::OPERATOR && *text == "=")
}

/// Dotted name from a `namespace X.Y` / `module X.Y` / `open X.Y` header.
fn dotted_decl_name(node: &Node, src: &str) -> Option<String> {
    let leaves = sig_leaves(node, src);
    // Find the leading keyword, then read the dotted path after it (skipping
    // `rec` for `module rec`, and the `=` is never reached as the path stops at
    // the first non-ident/non-dot).
    let kw = leaves.iter().position(|l| {
        matches!(l, Leaf::Tok { kind, text, .. }
            if *kind == tk::IDENT && matches!(*text, "namespace" | "module" | "open"))
    })?;
    let mut i = kw + 1;
    while let Some(Leaf::Tok { kind, text, .. }) = leaves.get(i) {
        if *kind == tk::IDENT && matches!(*text, "rec" | "global" | "type" | "internal" | "private")
        {
            i += 1;
        } else {
            break;
        }
    }
    dotted_from(&leaves, i).map(|(n, _)| n)
}

/// Identifiers on a binding's right-hand side: everything after the first
/// top-level `=` token, descending into groups. Deduplicated.
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

/// Same as [`collect_rhs_idents`] but over a slice of already-extracted leaves
/// (used for a member's body region).
fn collect_leaf_rhs_idents(leaves: &[Leaf<'_>], src: &str) -> BTreeSet<String> {
    let mut set = BTreeSet::new();
    let mut found_eq = false;
    for l in leaves {
        if !found_eq {
            if let Leaf::Tok { kind, text, .. } = l {
                if *kind == tk::OPERATOR && *text == "=" {
                    found_eq = true;
                }
            }
            continue;
        }
        match l {
            Leaf::Tok { kind, text, .. } if *kind == tk::IDENT && !is_keyword(text) => {
                set.insert(text.to_string());
            }
            Leaf::Grp(n) => {
                for ch in &n.children {
                    collect_idents(ch, src, &mut set);
                }
            }
            _ => {}
        }
    }
    set
}

fn collect_idents(c: &Child, src: &str, set: &mut BTreeSet<String>) {
    match c {
        Child::Token(t) if !t.trivia && t.kind == tk::IDENT => {
            let text = t.span.text(src);
            if !is_keyword(text) {
                set.insert(text.to_string());
            }
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

/// The module name for a file: the first `namespace`/`module` header if present,
/// else the scope path joined with `.`, else the file stem.
fn file_module_name(f: &SourceFile<'_>) -> String {
    for item in f.root.child_nodes() {
        if matches!(item.kind, cst::NAMESPACE | cst::MODULE) {
            if let Some(n) = dotted_decl_name(item, f.source) {
                return n;
            }
        }
    }
    if !f.module_path.is_empty() {
        return f.module_path.join(".");
    }
    stem(&f.rel_path)
}

fn unique(table: &BTreeMap<String, Vec<String>>, name: &str) -> Option<String> {
    match table.get(name) {
        Some(ids) if ids.len() == 1 => Some(ids[0].clone()),
        _ => None,
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
    use crate::lang::fsharp::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("Example.fs", src);
        let file = SourceFile {
            rel_path: "Example.fs".to_string(),
            module_path: vec![],
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    #[test]
    fn emits_module_types_and_functions() {
        let g = graph_for(
            "namespace Demo.Lib\n\
             type Foo = Bar | Baz\n\
             let add x y = x + y\n\
             let answer = 42\n",
        );
        assert!(g.has_node("module::Demo.Lib"));
        assert!(g.nodes().any(|n| n.kind == ont::TYPE && n.name == "Foo"));
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::FUNCTION && n.name == "add"));
        // `let answer = 42` is a nullary binding → Constant, not Function.
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::CONSTANT && n.name == "answer"));
    }

    #[test]
    fn emits_members_with_has_method() {
        let g = graph_for(
            "namespace N\n\
             type Counter() =\n\
            \x20   member this.Incr x = x + 1\n\
            \x20   static member Zero () = 0\n",
        );
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::FUNCTION && n.name == "Incr"));
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::FUNCTION && n.name == "Zero"));
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD));
    }

    #[test]
    fn inherit_is_extends_interface_is_implements() {
        let g = graph_for(
            "namespace N\n\
             type Base() = class end\n\
             type Derived() =\n\
            \x20   inherit Base()\n\
            \x20   interface IThing with\n\
            \x20       member this.Do () = ()\n",
        );
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an EXTENDS edge");
        assert!(ext.to.contains("Base"));
        let imp = g
            .edges()
            .find(|e| e.kind == edge::IMPLEMENTS)
            .expect("an IMPLEMENTS edge");
        assert!(imp.to == "unresolved::IThing");
    }

    #[test]
    fn resolves_identifiable_call() {
        let g = graph_for(
            "module M\n\
             let add x y = x + y\n\
             let run z = add z z\n",
        );
        let call = g
            .edges()
            .find(|e| e.kind == edge::CALLS)
            .expect("run should call add");
        assert!(call.to.starts_with("fn::M::add"));
        assert_eq!(call.props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn external_open_creates_dependency() {
        let g = graph_for("namespace N\nopen System.Collections.Generic\n");
        assert!(g.has_node("ext::System.Collections.Generic"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::System.Collections.Generic"));
    }

    #[test]
    fn record_and_union_type_kinds() {
        let g = graph_for(
            "module M\n\
             type Point = { X: int; Y: int }\n\
             type Shape = Circle | Square\n",
        );
        let point = g.nodes().find(|n| n.name == "Point").expect("Point type");
        assert_eq!(point.props.get("type_kind"), Some(&Json::str("record")));
        let shape = g.nodes().find(|n| n.name == "Shape").expect("Shape type");
        assert_eq!(shape.props.get("type_kind"), Some(&Json::str("union")));
    }
}
