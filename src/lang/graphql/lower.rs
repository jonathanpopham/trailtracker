//! Lower the GraphQL (SDL) CST into the canonical graph.
//!
//! GraphQL is a declarative type system, so this lowering is deliberately
//! conservative and contains **no fabricated `CALLS`** — there is no execution in
//! a schema to detect. The honest mapping:
//!
//! - `type` / `interface` / `input` / `enum` / `union` / `scalar` → [`Type`]
//!   nodes distinguished by a `type_kind` property, each `DECLARES`-d by its file.
//! - `type X implements Y` → [`IMPLEMENTS`] (X conforms to interface Y), with an
//!   explicit [`UnresolvedSymbol`] target when Y is not defined in the batch.
//! - A field of a root operation type (`Query`/`Mutation`/`Subscription`) that
//!   has an argument list is the closest thing SDL has to a function, so it is
//!   emitted as a [`Function`] with a `HAS_METHOD` edge from the root type;
//!   fieldless-of-args and non-root fields stay as plain properties (no node).
//! - Type references inside fields / union members → [`USES_TYPE`] to the
//!   referenced definition (only when it resolves to a defined type — ambiguity
//!   is never invented).
//! - `extend <def>` is unwrapped and lowered like its base, tagged
//!   `is_extension`. Directives `@x` are kept in the CST but, lacking an ontology
//!   kind, are not emitted as graph nodes (see the front-end docs / report).
//!
//! [`Type`]: crate::ir::ontology::node::TYPE
//! [`IMPLEMENTS`]: crate::ir::ontology::edge::IMPLEMENTS
//! [`UnresolvedSymbol`]: crate::ir::ontology::node::UNRESOLVED
//! [`Function`]: crate::ir::ontology::node::FUNCTION
//! [`USES_TYPE`]: crate::ir::ontology::edge::USES_TYPE

use std::collections::BTreeMap;

use crate::core::cst::{Child, Node, Token};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::graphql::lexer::kind as tk;
use crate::lang::graphql::parser::node as cst;

/// The conventional root operation type names. A field with arguments on one of
/// these becomes a `Function`.
const ROOT_TYPES: &[&str] = &["Query", "Mutation", "Subscription"];

/// Lower a whole schema's worth of files into a graph.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    let mut lo = Lowerer {
        g: Graph::new(),
        type_by_name: BTreeMap::new(),
    };

    let pkg_id = format!("pkg::{package}");
    lo.g.upsert_node(
        pkg_id.clone(),
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("graphql"))],
    );

    // Pass 1: index every defined type name so type references resolve in pass 2.
    for f in files {
        for def in f.root.child_nodes() {
            lo.collect_type_names(def, f.source);
        }
    }

    // Pass 2: emit file, type, function nodes and their edges.
    for f in files {
        let li = LineIndex::new(f.source);
        let file_id = format!("file::{}", f.rel_path);
        lo.g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("graphql")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(pkg_id.clone(), edge::CONTAINS, file_id.clone(), vec![]);
        for def in f.root.child_nodes() {
            lo.emit_def(def, false, &file_id, f.source, &li);
        }
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    /// Defined type name → its node id. First definition wins (a redefinition is
    /// folded into the same node by `upsert_node`).
    type_by_name: BTreeMap<String, String>,
}

impl Lowerer {
    fn collect_type_names(&mut self, def: &Node, src: &str) {
        match def.kind {
            cst::OBJECT | cst::INTERFACE | cst::INPUT | cst::ENUM | cst::UNION | cst::SCALAR => {
                if let Some(name) = name_text(def, src) {
                    self.type_by_name
                        .entry(name.to_string())
                        .or_insert_with(|| type_id(name));
                }
            }
            cst::EXTENSION => {
                for inner in def.child_nodes() {
                    self.collect_type_names(inner, src);
                }
            }
            _ => {}
        }
    }

    fn emit_def(&mut self, def: &Node, is_extend: bool, file_id: &str, src: &str, li: &LineIndex) {
        match def.kind {
            cst::OBJECT => self.emit_type(def, "object", is_extend, file_id, src, li),
            cst::INTERFACE => self.emit_type(def, "interface", is_extend, file_id, src, li),
            cst::INPUT => self.emit_type(def, "input", is_extend, file_id, src, li),
            cst::ENUM => self.emit_type(def, "enum", is_extend, file_id, src, li),
            cst::UNION => self.emit_type(def, "union", is_extend, file_id, src, li),
            cst::SCALAR => self.emit_type(def, "scalar", is_extend, file_id, src, li),
            cst::EXTENSION => {
                for inner in def.child_nodes() {
                    self.emit_def(inner, true, file_id, src, li);
                }
            }
            // `schema` is anonymous (no Type node) and `directive` has no
            // ontology kind; both stay first-class in the CST but emit nothing.
            _ => {}
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_type(
        &mut self,
        def: &Node,
        type_kind: &'static str,
        is_extend: bool,
        file_id: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let name = match name_text(def, src) {
            Some(n) => n.to_string(),
            None => return,
        };
        let id = type_id(&name);
        let line = li.line_col(name_span_start(def)).line;
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str(type_kind)),
                ("qualified_name", Json::str(name.clone())),
                ("language", Json::str("graphql")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(def.span.start as u64)),
                ("span_end", Json::U64(def.span.end as u64)),
                ("is_extension", Json::Bool(is_extend)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);

        // `implements` → IMPLEMENTS (object & interface only).
        if matches!(def.kind, cst::OBJECT | cst::INTERFACE) {
            if let Some(header) = def.child(cst::HEADER) {
                for iface in implements_names(header, src) {
                    let target = self
                        .type_by_name
                        .get(&iface)
                        .cloned()
                        .unwrap_or_else(|| unresolved_id(&iface));
                    if !self.g.has_node(&target) {
                        self.g.upsert_node(
                            target.clone(),
                            ont::UNRESOLVED,
                            iface.clone(),
                            vec![
                                ("unresolved", Json::Bool(true)),
                                ("role", Json::str("interface")),
                            ],
                        );
                    }
                    self.g.add_edge(
                        id.clone(),
                        edge::IMPLEMENTS,
                        target,
                        vec![("interface_name", Json::str(iface))],
                    );
                }
            }
        }

        // Union members (`= A | B`) live in the header → USES_TYPE.
        if def.kind == cst::UNION {
            if let Some(header) = def.child(cst::HEADER) {
                self.emit_type_uses(&id, header, src);
            }
        }

        // Field-body type references → USES_TYPE (skip enums: their members are
        // values, not type references).
        if let Some(fields) = def.child(cst::FIELDS) {
            if def.kind != cst::ENUM {
                self.emit_type_uses(&id, fields, src);
            }
            // Root operation fields with arguments → Function + HAS_METHOD.
            if def.kind == cst::OBJECT && ROOT_TYPES.contains(&name.as_str()) {
                self.emit_root_functions(&id, &name, fields, file_id, src, li);
            }
        }
    }

    /// Add `USES_TYPE` edges for every name in `region` that resolves to a
    /// defined type (dedup; never to the using node itself). Mirrors the Rust
    /// front end's identifier-walk approach.
    fn emit_type_uses(&mut self, from_id: &str, region: &Node, src: &str) {
        let mut seen: Vec<String> = Vec::new();
        for n in region.walk() {
            for t in n.tokens() {
                if t.kind != tk::NAME {
                    continue;
                }
                let name = t.span.text(src);
                if let Some(type_id) = self.type_by_name.get(name).cloned() {
                    if type_id != from_id && !seen.contains(&type_id) {
                        seen.push(type_id.clone());
                        self.g.add_edge(
                            from_id,
                            edge::USES_TYPE,
                            type_id,
                            vec![("type_name", Json::str(name.to_string()))],
                        );
                    }
                }
            }
        }
    }

    fn emit_root_functions(
        &mut self,
        type_id: &str,
        type_name: &str,
        fields: &Node,
        file_id: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let els = significant_children(fields);
        let n = els.len();
        let mut i = 0;
        while i < n {
            // A field with arguments: NAME, then a `(...)` group, then `:`.
            if let El::Tok(t) = &els[i] {
                if t.kind == tk::NAME {
                    let prev = if i > 0 {
                        el_text(&els[i - 1], src)
                    } else {
                        None
                    };
                    let is_directive_name = prev == Some("@");
                    let has_paren =
                        matches!(els.get(i + 1), Some(El::Grp(p)) if p.kind == cst::PAREN);
                    let then_colon =
                        matches!(els.get(i + 2), Some(e) if el_text(e, src) == Some(":"));
                    if !is_directive_name && has_paren && then_colon {
                        let fname = t.span.text(src);
                        let line = li.line_col(t.span.start).line;
                        let fid = format!("fn::{type_name}::{fname}#{line}");
                        self.g.upsert_node(
                            fid.clone(),
                            ont::FUNCTION,
                            fname.to_string(),
                            vec![
                                ("qualified_name", Json::str(format!("{type_name}.{fname}"))),
                                ("language", Json::str("graphql")),
                                ("line", Json::U64(line as u64)),
                                ("parent_type", Json::str(type_name.to_string())),
                                ("is_field", Json::Bool(true)),
                                ("has_arguments", Json::Bool(true)),
                            ],
                        );
                        self.g
                            .add_edge(file_id, edge::DECLARES, fid.clone(), vec![]);
                        self.g
                            .add_edge(type_id, edge::HAS_METHOD, fid.clone(), vec![]);
                        // Argument type references → USES_TYPE from the function.
                        if let Some(El::Grp(p)) = els.get(i + 1) {
                            self.emit_type_uses(&fid, p, src);
                        }
                        i += 2;
                        continue;
                    }
                }
            }
            i += 1;
        }
    }
}

// --- significant-children view (tokens + groups, trivia dropped) ------------

enum El<'a> {
    Tok(&'a Token),
    Grp(&'a Node),
}

fn significant_children(node: &Node) -> Vec<El<'_>> {
    let mut v = Vec::new();
    for c in &node.children {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => v.push(El::Tok(t)),
            Child::Node(n) => v.push(El::Grp(n)),
        }
    }
    v
}

fn el_text<'a>(e: &El<'a>, src: &'a str) -> Option<&'a str> {
    match e {
        El::Tok(t) => Some(t.span.text(src)),
        El::Grp(_) => None,
    }
}

/// The interface names in an object/interface `implements A & B` clause. Stops at
/// the first directive (`@`); `&` separators are punctuation and ignored.
fn implements_names(header: &Node, src: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut started = false;
    for t in header.tokens() {
        let text = t.span.text(src);
        if t.kind == tk::PUNCT && text == "@" {
            break;
        }
        if t.kind == tk::NAME {
            if text == "implements" {
                started = true;
            } else if started {
                out.push(text.to_string());
            }
        }
    }
    out
}

// --- pure helpers -----------------------------------------------------------

fn type_id(name: &str) -> String {
    format!("type::{name}")
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

fn name_text<'a>(def: &'a Node, src: &'a str) -> Option<&'a str> {
    let nm = def.child(cst::NAME)?;
    nm.tokens().next().map(|t| t.span.text(src))
}

fn name_span_start(def: &Node) -> u32 {
    def.child(cst::NAME)
        .map(|n| n.span.start)
        .unwrap_or(def.span.start)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::graphql::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("schema.graphql", src);
        let file = SourceFile {
            rel_path: "schema.graphql".to_string(),
            module_path: vec![],
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    #[test]
    fn lowering_round_trips_source() {
        // The lossless guarantee is a parse-level property; assert it holds for
        // the same input the lowering consumes.
        let src = "type Query { me(id: ID!): User } type User { id: ID! }";
        let tree = parse("schema.graphql", src);
        assert!(tree.is_lossless(), "must reconstruct source byte-for-byte");
    }

    #[test]
    fn types_become_type_nodes_with_kinds() {
        let g = graph_for(
            "scalar DateTime\nenum Role { A B }\ninput In { x: Int }\nunion U = A | B\n\
             interface Node { id: ID }\ntype A implements Node { id: ID }",
        );
        assert!(g.has_node("type::DateTime"));
        assert!(g.has_node("type::Role"));
        assert!(g.has_node("type::In"));
        assert!(g.has_node("type::U"));
        assert!(g.has_node("type::Node"));
        assert!(g.has_node("type::A"));
        let kind_of = |id: &str| {
            g.nodes()
                .find(|n| n.id == id)
                .and_then(|n| n.props.get("type_kind").cloned())
        };
        assert_eq!(kind_of("type::DateTime"), Some(Json::str("scalar")));
        assert_eq!(kind_of("type::U"), Some(Json::str("union")));
    }

    #[test]
    fn implements_emits_implements_edge() {
        let g = graph_for("interface Node { id: ID }\ntype A implements Node { id: ID }");
        let imp = g
            .edges()
            .find(|e| e.kind == edge::IMPLEMENTS && e.from == "type::A");
        assert!(imp.is_some(), "type A should IMPLEMENTS interface Node");
        assert_eq!(imp.unwrap().to, "type::Node");
    }

    #[test]
    fn unresolved_interface_is_explicit() {
        let g = graph_for("type A implements Missing { id: ID }");
        assert!(g.has_node("unresolved::Missing"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::IMPLEMENTS && e.to == "unresolved::Missing"));
    }

    #[test]
    fn root_field_with_args_is_a_function() {
        let g =
            graph_for("type Query { user(id: ID!): User\n version: String }\ntype User { id: ID }");
        // Only the field with an argument list becomes a Function.
        assert_eq!(g.count_nodes_of(ont::FUNCTION), 1);
        let f = g.nodes().find(|n| n.kind == ont::FUNCTION).unwrap();
        assert_eq!(f.name, "user");
        assert!(g
            .edges()
            .any(|e| e.kind == edge::HAS_METHOD && e.from == "type::Query" && e.to == f.id));
        // The argument type ID is not a defined type; the return type User is.
        assert!(g
            .edges()
            .any(|e| e.kind == edge::USES_TYPE && e.from == "type::Query" && e.to == "type::User"));
    }

    #[test]
    fn non_root_fields_are_not_functions() {
        let g = graph_for("type Widget { resize(w: Int): Widget }");
        assert_eq!(g.count_nodes_of(ont::FUNCTION), 0);
    }

    #[test]
    fn no_calls_are_fabricated() {
        let g = graph_for("type Query { a(x: Int): B }\ntype B { id: ID }");
        assert_eq!(g.count_edges_of(edge::CALLS), 0);
    }

    #[test]
    fn extend_is_lowered_and_tagged() {
        let g = graph_for(
            "type Query { a: Int }\nextend type Query { b(x: Int): C }\ntype C { id: ID }",
        );
        // The extension's argument field still becomes a function.
        assert!(g.nodes().any(|n| n.kind == ont::FUNCTION && n.name == "b"));
    }
}
