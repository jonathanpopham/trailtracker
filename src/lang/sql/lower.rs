//! Lower the SQL CST into the canonical graph.
//!
//! This mirrors the Rust / Verilog lowerings — the same conservative principles
//! and the same shared ontology — adapted to SQL DDL. The honest mapping:
//!
//!   - `CREATE TABLE name (...)` → [`Type`] (`type_kind: table`). Column names are
//!     recorded as a `columns` property (the ontology has no first-class Column
//!     node, so columns are honest metadata rather than fabricated nodes).
//!   - `CREATE [MATERIALIZED] VIEW name` → [`Type`] (`type_kind: view` /
//!     `materialized_view`).
//!   - `CREATE [OR REPLACE] FUNCTION|PROCEDURE name(...)` → [`Function`]
//!     (`subroutine: function` / `procedure`).
//!   - `CREATE SCHEMA name` → [`Module`] (a pure namespace scope).
//!   - `FOREIGN KEY (...) REFERENCES other` (and inline `col … REFERENCES other`)
//!     → a [`USES_TYPE`] edge from this table's `Type` to the referenced table's
//!     `Type` (a type-to-type reference; resolved only when the name is unique,
//!     else an explicit [`UnresolvedSymbol`] / ambiguous edge — never fabricated).
//!   - bare `name(...)` calls inside a (tokenisable) function body → [`CALLS`],
//!     resolved against project functions, else an [`UnresolvedSymbol`].
//!
//! What has no honest home and is punted (kept lossless in the CST, no graph
//! node): `CREATE INDEX`, `CREATE TRIGGER`, and every non-DDL statement
//! (`SELECT`/`INSERT`/…). Function bodies written as dollar-quoted or
//! single-quoted strings are single opaque tokens, so calls *inside* such bodies
//! are not extracted — we never parse inside string literals. Everything emitted
//! comes from real tokens on the lossless tree; nothing is guessed.

use std::collections::BTreeMap;

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::sql::lexer::{is_keyword, kind as tk};
use crate::lang::sql::parser::node as cst;

/// Lower a whole project's worth of SQL files into a graph. `manifest_deps` is
/// unused (SQL has no manifest the pipeline reads).
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        table_by_name: BTreeMap::new(),
        fn_by_name: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("sql"))],
    );

    // Pass B: create definition nodes + structural edges, build symbol tables.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_tables: Vec<PendingTable> = Vec::new();
    for f in files {
        let li = LineIndex::new(f.source);
        let module_join = mod_join(&f.module_path);
        let leaf = lo.ensure_modules(&f.module_path);
        let file_id = format!("file::{}", f.rel_path);
        lo.g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("sql")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(leaf, edge::CONTAINS, file_id.clone(), vec![]);

        for stmt in f.root.child_nodes() {
            match stmt.kind {
                cst::CREATE_TABLE => lo.handle_table(
                    stmt,
                    &file_id,
                    &module_join,
                    f.source,
                    &li,
                    &mut pend_tables,
                ),
                cst::CREATE_VIEW => lo.handle_view(stmt, &file_id, &module_join, f.source, &li),
                cst::CREATE_FUNCTION => {
                    lo.handle_function(stmt, &file_id, &module_join, f.source, &li, &mut pend_fns)
                }
                cst::CREATE_SCHEMA => lo.handle_schema(stmt, &file_id, &module_join, f.source, &li),
                _ => {} // INDEX / TRIGGER / other statements: lossless, no node.
            }
        }
    }

    // Pass C: resolve foreign keys and function calls against the full tables.
    for pt in &pend_tables {
        for target in scan_fks(pt.cols, pt.source) {
            lo.emit_fk(&pt.id, &target);
        }
    }
    for pf in &pend_fns {
        let mut calls = Vec::new();
        scan_calls(pf.body, pf.source, &mut calls);
        for call in &calls {
            lo.emit_call(&pf.id, call);
        }
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    /// Simple (unquoted) name → table/view type node ids (FK resolution targets).
    table_by_name: BTreeMap<String, Vec<String>>,
    /// Simple (unquoted) name → function node ids (call resolution targets).
    fn_by_name: BTreeMap<String, Vec<String>>,
}

struct PendingTable<'a> {
    id: String,
    source: &'a str,
    cols: &'a Node,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    body: &'a Node,
}

impl Lowerer {
    fn pkg_id(&self) -> String {
        format!("pkg::{}", self.package)
    }

    /// Ensure the `Package → mod::a → mod::a.b …` chain exists and return the leaf
    /// module id (or the package id for a root file with no module segments).
    fn ensure_modules(&mut self, path: &[String]) -> String {
        let pkg = self.pkg_id();
        if path.is_empty() {
            return pkg;
        }
        let mut parent = pkg;
        let mut acc: Vec<String> = Vec::new();
        for seg in path {
            acc.push(seg.clone());
            let id = format!("mod::{}", acc.join("."));
            self.g.upsert_node(
                id.clone(),
                ont::MODULE,
                seg.clone(),
                vec![("language", Json::str("sql"))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    fn handle_table<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        module_join: &str,
        src: &'a str,
        li: &LineIndex,
        pend: &mut Vec<PendingTable<'a>>,
    ) {
        let name = simple_name(item, src).unwrap_or_else(|| "<anonymous>".to_string());
        let line = li.line_col(name_start(item)).line;
        let qual = qual_name(module_join, &name);
        let id = format!("type::{qual}");
        let cols = item.child(cst::COLUMN_LIST);
        let col_names: Vec<Json> = cols
            .map(|g| column_names(g, src))
            .unwrap_or_default()
            .into_iter()
            .map(Json::Str)
            .collect();
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str("table")),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("sql")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
                ("columns", Json::Array(col_names)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.table_by_name.entry(name).or_default().push(id.clone());
        if let Some(g) = cols {
            pend.push(PendingTable {
                id,
                source: src,
                cols: g,
            });
        }
    }

    fn handle_view(
        &mut self,
        item: &Node,
        file_id: &str,
        module_join: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let name = simple_name(item, src).unwrap_or_else(|| "<anonymous>".to_string());
        let line = li.line_col(name_start(item)).line;
        let materialized = item
            .tokens()
            .any(|t| t.span.text(src).eq_ignore_ascii_case("materialized"));
        let type_kind = if materialized {
            "materialized_view"
        } else {
            "view"
        };
        let qual = qual_name(module_join, &name);
        let id = format!("type::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str(type_kind)),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("sql")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        // Register so a foreign key may resolve to a view as well as a table.
        self.table_by_name.entry(name).or_default().push(id);
    }

    fn handle_function<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        module_join: &str,
        src: &'a str,
        li: &LineIndex,
        pend: &mut Vec<PendingFn<'a>>,
    ) {
        let name = simple_name(item, src).unwrap_or_else(|| "<anonymous>".to_string());
        let line = li.line_col(name_start(item)).line;
        let is_proc = item
            .tokens()
            .any(|t| t.span.text(src).eq_ignore_ascii_case("procedure"));
        let qual = qual_name(module_join, &name);
        let id = format!("fn::{qual}#{line}");
        self.g.upsert_node(
            id.clone(),
            ont::FUNCTION,
            name.clone(),
            vec![
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("sql")),
                (
                    "subroutine",
                    Json::str(if is_proc { "procedure" } else { "function" }),
                ),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
                ("has_body", Json::Bool(item.child(cst::BODY).is_some())),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.fn_by_name.entry(name).or_default().push(id.clone());
        if let Some(body) = item.child(cst::BODY) {
            pend.push(PendingFn {
                id,
                source: src,
                body,
            });
        }
    }

    fn handle_schema(
        &mut self,
        item: &Node,
        file_id: &str,
        module_join: &str,
        src: &str,
        _li: &LineIndex,
    ) {
        let name = match simple_name(item, src) {
            Some(n) => n,
            None => return,
        };
        let qual = qual_name(module_join, &name);
        let id = format!("mod::schema::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::MODULE,
            name,
            vec![
                ("module_kind", Json::str("schema")),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("sql")),
            ],
        );
        self.g.add_edge(file_id, edge::CONTAINS, id, vec![]);
    }

    // --- foreign-key / call resolution --------------------------------------

    fn emit_fk(&mut self, from_id: &str, table_name: &str) {
        let cands = self
            .table_by_name
            .get(table_name)
            .cloned()
            .unwrap_or_default();
        let mut props = vec![
            ("foreign_key", Json::Bool(true)),
            ("references", Json::str(table_name.to_string())),
        ];
        match cands.len() {
            1 => {
                props.push(("resolved", Json::Bool(true)));
                props.push(("candidate_count", Json::U64(1)));
                self.g
                    .add_edge(from_id, edge::USES_TYPE, cands[0].clone(), props);
            }
            0 => {
                let target = format!("unresolved::{table_name}");
                self.ensure_unresolved(&target, table_name, "table");
                props.push(("resolved", Json::Bool(false)));
                props.push(("candidate_count", Json::U64(0)));
                self.g.add_edge(from_id, edge::USES_TYPE, target, props);
            }
            n => {
                let target = format!("unresolved::{table_name}");
                self.ensure_unresolved(&target, table_name, "table");
                props.push(("resolved", Json::Bool(false)));
                props.push(("ambiguous", Json::Bool(true)));
                props.push(("candidate_count", Json::U64(n as u64)));
                props.push((
                    "candidates",
                    Json::Array(cands.into_iter().map(Json::Str).collect()),
                ));
                self.g.add_edge(from_id, edge::USES_TYPE, target, props);
            }
        }
    }

    fn emit_call(&mut self, caller_id: &str, call: &str) {
        let cands = self.fn_by_name.get(call).cloned().unwrap_or_default();
        let mut props = vec![
            ("callee", Json::str(call.to_string())),
            ("method", Json::Bool(false)),
        ];
        match cands.len() {
            1 => {
                props.push(("resolution", Json::str("global")));
                props.push(("resolved", Json::Bool(true)));
                props.push(("candidate_count", Json::U64(1)));
                self.g
                    .add_edge(caller_id, edge::CALLS, cands[0].clone(), props);
            }
            0 => {
                let target = format!("unresolved::{call}");
                self.ensure_unresolved(&target, call, "call");
                props.push(("resolution", Json::str("external")));
                props.push(("resolved", Json::Bool(false)));
                props.push(("candidate_count", Json::U64(0)));
                self.g.add_edge(caller_id, edge::CALLS, target, props);
            }
            n => {
                let target = format!("unresolved::{call}");
                self.ensure_unresolved(&target, call, "call");
                props.push(("resolution", Json::str("ambiguous")));
                props.push(("resolved", Json::Bool(false)));
                props.push(("ambiguous", Json::Bool(true)));
                props.push(("candidate_count", Json::U64(n as u64)));
                props.push((
                    "candidates",
                    Json::Array(cands.into_iter().map(Json::Str).collect()),
                ));
                self.g.add_edge(caller_id, edge::CALLS, target, props);
            }
        }
    }

    fn ensure_unresolved(&mut self, id: &str, name: &str, role: &'static str) {
        if !self.g.has_node(id) {
            self.g.upsert_node(
                id.to_string(),
                ont::UNRESOLVED,
                name.to_string(),
                vec![("unresolved", Json::Bool(true)), ("role", Json::str(role))],
            );
        }
    }
}

// --- pure helpers -----------------------------------------------------------

fn mod_join(path: &[String]) -> String {
    path.join(".")
}

fn qual_name(module_join: &str, name: &str) -> String {
    if module_join.is_empty() {
        name.to_string()
    } else {
        format!("{module_join}.{name}")
    }
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

/// The simple (last-segment, unquoted) name of a definition's `Name` child.
fn simple_name(item: &Node, src: &str) -> Option<String> {
    let nm = item.child(cst::NAME)?;
    let mut last = None;
    for t in nm.tokens() {
        if t.kind == tk::IDENT || t.kind == tk::QUOTED_IDENT {
            last = Some(unquote(t.span.text(src)));
        }
    }
    last
}

/// Byte offset used for a definition's line number: the `Name` child when present,
/// else the item's own start.
fn name_start(item: &Node) -> u32 {
    item.child(cst::NAME)
        .map(|n| n.span.start)
        .unwrap_or(item.span.start)
}

/// Strip the surrounding quotes of a quoted identifier (`"x"`, `` `x` ``, `[x]`),
/// undoing the doubled-delimiter escape; plain identifiers are returned as-is.
/// Note: unquoted names are kept in their written case (no case folding), so
/// identifier matching across statements is case-sensitive (a documented punt).
fn unquote(text: &str) -> String {
    let bytes = text.as_bytes();
    if text.len() >= 2 {
        let open = bytes[0];
        let close = bytes[text.len() - 1];
        let inner = &text[1..text.len() - 1];
        match (open, close) {
            (b'"', b'"') => return inner.replace("\"\"", "\""),
            (b'`', b'`') => return inner.replace("``", "`"),
            (b'[', b']') => return inner.replace("]]", "]"),
            _ => {}
        }
    }
    text.to_string()
}

/// Keywords that lead a *table-level constraint* clause rather than a column
/// definition, so they are skipped during column-name extraction.
fn is_constraint_lead(text: &str) -> bool {
    [
        "constraint",
        "primary",
        "foreign",
        "unique",
        "check",
        "key",
        "exclude",
        "like",
        "index",
        "period",
    ]
    .iter()
    .any(|k| k.eq_ignore_ascii_case(text))
}

/// Split a balanced group's direct children on top-level commas, dropping the
/// group's own delimiter tokens. Nested groups stay opaque within an item.
fn split_top_level<'a>(group: &'a Node, src: &str) -> Vec<Vec<&'a Child>> {
    let mut items: Vec<Vec<&Child>> = vec![Vec::new()];
    for c in &group.children {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) if matches!(t.span.text(src), "(" | ")" | "[" | "]" | "{" | "}") => {}
            Child::Token(t) if t.span.text(src) == "," => items.push(Vec::new()),
            other => items.last_mut().unwrap().push(other),
        }
    }
    items
}

/// Column names from a `(...)` column list: the leading identifier of each
/// top-level item that is not a table-level constraint clause.
fn column_names(group: &Node, src: &str) -> Vec<String> {
    let mut out = Vec::new();
    for item in split_top_level(group, src) {
        let first = item.iter().find_map(|c| match c {
            Child::Token(t) if !t.trivia => Some(t),
            _ => None,
        });
        if let Some(t) = first {
            let text = t.span.text(src);
            if (t.kind == tk::IDENT || t.kind == tk::QUOTED_IDENT) && !is_constraint_lead(text) {
                out.push(unquote(text));
            }
        }
    }
    out
}

/// Non-trivia tokens of a subtree in source order.
fn flat_sig_tokens<'a>(node: &'a Node, src: &'a str, out: &mut Vec<(&'static str, &'a str)>) {
    for c in &node.children {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => out.push((t.kind, t.span.text(src))),
            Child::Node(n) => flat_sig_tokens(n, src, out),
        }
    }
}

/// Referenced table names of every `REFERENCES other[.tbl]` in a column list
/// (covers both inline `col … REFERENCES t` and table-level
/// `FOREIGN KEY (...) REFERENCES t (...)`). The target is the last segment of the
/// (possibly schema-qualified) name following the `REFERENCES` keyword.
fn scan_fks(group: &Node, src: &str) -> Vec<String> {
    let mut toks: Vec<(&'static str, &str)> = Vec::new();
    flat_sig_tokens(group, src, &mut toks);
    let mut out = Vec::new();
    let mut i = 0;
    while i < toks.len() {
        if toks[i].1.eq_ignore_ascii_case("references")
            && i + 1 < toks.len()
            && (toks[i + 1].0 == tk::IDENT || toks[i + 1].0 == tk::QUOTED_IDENT)
        {
            let mut name = unquote(toks[i + 1].1);
            let mut j = i + 1;
            while j + 2 < toks.len()
                && toks[j + 1].1 == "."
                && (toks[j + 2].0 == tk::IDENT || toks[j + 2].0 == tk::QUOTED_IDENT)
            {
                name = unquote(toks[j + 2].1);
                j += 2;
            }
            out.push(name);
            i = j + 1;
            continue;
        }
        i += 1;
    }
    out
}

// --- call detection over the lossless token tree ----------------------------

enum El<'a> {
    Tok { text: &'a str, ident: bool },
    Grp(&'a Node),
}

fn significant_children<'a>(node: &'a Node, src: &'a str) -> Vec<El<'a>> {
    let mut v = Vec::new();
    for c in &node.children {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => v.push(El::Tok {
                text: t.span.text(src),
                ident: t.kind == tk::IDENT || t.kind == tk::QUOTED_IDENT,
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

fn el_is_ident(e: &El) -> bool {
    matches!(e, El::Tok { ident: true, .. })
}

fn el_is_paren(e: &El) -> bool {
    matches!(e, El::Grp(n) if n.kind == cst::PAREN)
}

/// Detect bare `name(...)` call sites over the real token tree (a name, not
/// after `.`/`::`, not a keyword, immediately followed by a parenthesised group).
/// Recurses into nested groups. Names inside string-literal bodies are invisible
/// to this scan (they are single opaque tokens) — a documented limitation.
fn scan_calls(node: &Node, src: &str, out: &mut Vec<String>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        if el_is_ident(&els[i]) {
            let name = el_tok_text(&els[i]).unwrap_or("");
            let prev = if i > 0 {
                el_tok_text(&els[i - 1])
            } else {
                None
            };
            let after_dot = matches!(prev, Some(".") | Some("::"));
            if !after_dot && !is_keyword(name) && i + 1 < n && el_is_paren(&els[i + 1]) {
                out.push(name.to_string());
                i += 2;
                continue;
            }
        }
        i += 1;
    }
    for e in &els {
        if let El::Grp(g) = e {
            scan_calls(g, src, out);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::sql::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("schema.sql", src);
        let file = SourceFile {
            rel_path: "schema.sql".to_string(),
            module_path: vec!["schema".to_string()],
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    fn edges_of<'a>(g: &'a Graph, kind: &str) -> Vec<&'a crate::graph::GraphEdge> {
        g.edges().filter(|e| e.kind == kind).collect()
    }

    #[test]
    fn table_becomes_type_with_columns() {
        let g = graph_for("CREATE TABLE users (id int PRIMARY KEY, email text);");
        let ty = g
            .nodes()
            .find(|n| n.kind == ont::TYPE && n.name == "users")
            .expect("a Type node for the table");
        assert_eq!(ty.props.get("type_kind"), Some(&Json::str("table")));
        let cols = match ty.props.get("columns") {
            Some(Json::Array(a)) => a.clone(),
            other => panic!("columns should be an array, got {other:?}"),
        };
        assert!(cols.contains(&Json::str("id")));
        assert!(cols.contains(&Json::str("email")));
        // `PRIMARY KEY` is part of the `id` column def, not a separate column.
        assert_eq!(cols.len(), 2, "got columns {cols:?}");
        assert!(g.edges().any(|e| e.kind == edge::DECLARES && e.to == ty.id));
    }

    #[test]
    fn view_and_materialized_view_become_types() {
        let g = graph_for("CREATE VIEW v AS SELECT 1; CREATE MATERIALIZED VIEW mv AS SELECT 2;");
        let v = g
            .nodes()
            .find(|n| n.kind == ont::TYPE && n.name == "v")
            .expect("view type");
        assert_eq!(v.props.get("type_kind"), Some(&Json::str("view")));
        let mv = g
            .nodes()
            .find(|n| n.kind == ont::TYPE && n.name == "mv")
            .expect("materialized view type");
        assert_eq!(
            mv.props.get("type_kind"),
            Some(&Json::str("materialized_view"))
        );
    }

    #[test]
    fn function_and_procedure_become_functions() {
        let g = graph_for(
            "CREATE FUNCTION add(a int, b int) RETURNS int AS $$ SELECT a + b $$ LANGUAGE sql; \
             CREATE PROCEDURE do_it() AS $$ BEGIN END $$ LANGUAGE plpgsql;",
        );
        let add = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "add")
            .expect("the function");
        assert_eq!(add.props.get("subroutine"), Some(&Json::str("function")));
        let proc = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "do_it")
            .expect("the procedure");
        assert_eq!(proc.props.get("subroutine"), Some(&Json::str("procedure")));
    }

    #[test]
    fn schema_becomes_module() {
        let g = graph_for("CREATE SCHEMA app;");
        let m = g
            .nodes()
            .find(|n| n.kind == ont::MODULE && n.name == "app")
            .expect("schema module");
        assert_eq!(m.props.get("module_kind"), Some(&Json::str("schema")));
        assert!(g.edges().any(|e| e.kind == edge::CONTAINS && e.to == m.id));
    }

    #[test]
    fn foreign_key_resolves_to_referenced_table() {
        let g = graph_for(
            "CREATE TABLE orgs (id int PRIMARY KEY); \
             CREATE TABLE users (id int, org_id int REFERENCES orgs (id));",
        );
        let fk = edges_of(&g, edge::USES_TYPE)
            .into_iter()
            .find(|e| e.props.get("foreign_key") == Some(&Json::Bool(true)))
            .expect("a foreign-key USES_TYPE edge");
        assert_eq!(fk.props.get("resolved"), Some(&Json::Bool(true)));
        assert!(fk.to.starts_with("type::"));
        assert!(fk.to.ends_with("orgs"));
    }

    #[test]
    fn table_level_foreign_key_resolves() {
        let g = graph_for(
            "CREATE TABLE orgs (id int PRIMARY KEY); \
             CREATE TABLE users (id int, org_id int, FOREIGN KEY (org_id) REFERENCES orgs (id));",
        );
        let fk = edges_of(&g, edge::USES_TYPE)
            .into_iter()
            .find(|e| e.props.get("foreign_key") == Some(&Json::Bool(true)))
            .expect("a table-level foreign key");
        assert_eq!(fk.props.get("resolved"), Some(&Json::Bool(true)));
        assert!(fk.to.ends_with("orgs"));
    }

    #[test]
    fn unknown_foreign_key_is_unresolved() {
        let g = graph_for("CREATE TABLE t (id int, x int REFERENCES ghost (id));");
        let fk = edges_of(&g, edge::USES_TYPE)
            .into_iter()
            .find(|e| e.props.get("foreign_key") == Some(&Json::Bool(true)))
            .expect("a foreign key");
        assert_eq!(fk.props.get("resolved"), Some(&Json::Bool(false)));
        assert!(g.has_node("unresolved::ghost"));
    }

    #[test]
    fn function_call_in_inline_body_resolves() {
        // Bodies must be tokenisable (no string/dollar-quote) for call scanning.
        let g = graph_for(
            "CREATE FUNCTION g() RETURNS int AS BEGIN RETURN 1 END; \
             CREATE FUNCTION f() RETURNS int AS BEGIN RETURN g() END;",
        );
        let call = edges_of(&g, edge::CALLS)
            .into_iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("g")))
            .expect("a call to g");
        assert_eq!(call.props.get("resolved"), Some(&Json::Bool(true)));
        assert!(call.to.starts_with("fn::"));
    }

    #[test]
    fn output_is_deterministic() {
        let src = "CREATE TABLE a (id int); CREATE TABLE b (id int, a_id int REFERENCES a (id));";
        let first = graph_for(src).to_jsonl();
        let second = graph_for(src).to_jsonl();
        assert_eq!(
            first, second,
            "graph output must be byte-identical across runs"
        );
    }
}
