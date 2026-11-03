//! Lower the APL CST into the canonical graph.
//!
//! APL is terse and largely anonymous, so this lowering is deliberately
//! conservative — it emits only what the lossless tree honestly says, and punts
//! loudly on the rest (see the front-end module doc for the full punt list):
//!
//!   - `∇ … ∇` tradfns → a [`Function`] node (`fn_kind` `tradfn`), the name read
//!     from the header by the standard APL rule (`Z←larg fname rarg`).
//!   - `name←{…}` (a dfn bound to a name) → a [`Function`] node (`fn_kind`
//!     `dfn`).
//!   - a top-level `name←value` whose RHS is *not* a dfn → a [`Constant`]. The
//!     same shape inside a function is a local and is not emitted.
//!   - `:Namespace Name` → a [`Module`] node (the one honest scope construct APL
//!     scripts carry); noted, not deeply scoped.
//!   - references to a defined function's name inside a function body → [`CALLS`],
//!     resolved against the project's function table (unique → resolved; several
//!     → ambiguous with the full `candidates` set, never a guess). APL applies
//!     functions by juxtaposition with no call syntax, so only names that match a
//!     *defined project function* become edges; bare primitives, arguments, and
//!     unknown names are not fabricated into calls.
//!
//! What APL has **no** honest home for from a single script's tokens: argument
//! types, inheritance, and `IMPORTS`/`DEPENDS_ON` (`)COPY` / `⎕CY` workspace
//! pulls are noted as a punt, not modelled). No `USES_TYPE`, `EXTENDS`, or
//! `IMPLEMENTS` edges are emitted. Everything comes from real tokens; nothing is
//! guessed.

use std::collections::BTreeMap;

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::apl::lexer::{is_control_word, kind as tk};
use crate::lang::apl::parser::node as cst;
use crate::lang::frontend::SourceFile;

/// Lower a whole project's worth of APL files into a graph. `manifest_deps` is
/// unused: APL has no manifest the pipeline reads.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        fn_by_name: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("apl"))],
    );

    // Pass A: create File + definition nodes, build the function table, and
    // collect function bodies for call resolution.
    let mut pend: Vec<PendingFn> = Vec::new();
    for f in files {
        let li = LineIndex::new(f.source);
        let file_id = format!("file::{}", f.rel_path);
        lo.g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("apl")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(lo.pkg_id(), edge::CONTAINS, file_id.clone(), vec![]);

        for item in f.root.child_nodes() {
            match item.kind {
                cst::DEL_FN => lo.handle_del_fn(item, &file_id, f.source, &li, &mut pend),
                cst::STMT => lo.handle_stmt(item, &file_id, f.source, &li, false, &mut pend),
                _ => {}
            }
        }
    }

    // Pass B: resolve calls inside function bodies against the complete table.
    for pf in &pend {
        if let Some(body) = pf.body {
            let mut names = Vec::new();
            collect_name_refs(body, pf.source, &mut names);
            let mut emitted: BTreeMap<String, ()> = BTreeMap::new();
            for name in names {
                if emitted.contains_key(&name) {
                    continue;
                }
                emitted.insert(name.clone(), ());
                if let Some(cands) = lo.fn_by_name.get(&name).cloned() {
                    lo.emit_call(&pf.id, &name, &cands);
                }
            }
        }
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    /// Simple name → all function node ids.
    fn_by_name: BTreeMap<String, Vec<String>>,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    /// The body to scan for calls: a tradfn `Body` or a dfn `Brace`.
    body: Option<&'a Node>,
}

impl Lowerer {
    fn pkg_id(&self) -> String {
        format!("pkg::{}", self.package)
    }

    fn handle_del_fn<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        src: &'a str,
        li: &LineIndex,
        pend: &mut Vec<PendingFn<'a>>,
    ) {
        let name = item
            .child(cst::HEADER)
            .and_then(|h| tradfn_name(h, src))
            .unwrap_or_else(|| "<anonymous>".to_string());
        let body = item.child(cst::BODY);
        self.emit_function(&name, "tradfn", item, file_id, src, li, body, pend);
    }

    fn handle_stmt<'a>(
        &mut self,
        stmt: &'a Node,
        file_id: &str,
        src: &'a str,
        li: &LineIndex,
        in_function: bool,
        pend: &mut Vec<PendingFn<'a>>,
    ) {
        // `:Namespace Name` — the one honest scope construct; noted as a Module.
        if let Some(ns) = namespace_name(stmt, src) {
            self.emit_namespace(file_id, &ns);
            return;
        }

        let assign = analyze_assign(stmt, src);
        match assign {
            Some(Assign {
                target,
                rhs_brace: Some(brace),
            }) => {
                // `name←{…}` — a dfn bound to a name.
                self.emit_function(&target, "dfn", brace, file_id, src, li, Some(brace), pend);
            }
            Some(Assign {
                target,
                rhs_brace: None,
            }) if !in_function => {
                // A plain top-level value binding.
                self.emit_constant(&target, stmt, file_id, li);
            }
            _ => {}
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_function<'a>(
        &mut self,
        name: &str,
        fn_kind: &'static str,
        def_node: &'a Node,
        file_id: &str,
        src: &'a str,
        li: &LineIndex,
        body: Option<&'a Node>,
        pend: &mut Vec<PendingFn<'a>>,
    ) {
        let line = li.line_col(def_node.span.start).line;
        let id = format!("fn::{name}#{line}");
        self.g.upsert_node(
            id.clone(),
            ont::FUNCTION,
            name.to_string(),
            vec![
                ("qualified_name", Json::str(name.to_string())),
                ("language", Json::str("apl")),
                ("fn_kind", Json::str(fn_kind)),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(def_node.span.start as u64)),
                ("span_end", Json::U64(def_node.span.end as u64)),
                ("has_body", Json::Bool(body.is_some())),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        if name != "<anonymous>" {
            self.fn_by_name
                .entry(name.to_string())
                .or_default()
                .push(id.clone());
        }
        pend.push(PendingFn {
            id,
            source: src,
            body,
        });
    }

    fn emit_constant(&mut self, name: &str, stmt: &Node, file_id: &str, li: &LineIndex) {
        let line = li.line_col(stmt.span.start).line;
        let id = format!("const::{name}");
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            name.to_string(),
            vec![
                ("binding", Json::str("var")),
                ("language", Json::str("apl")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
    }

    fn emit_namespace(&mut self, file_id: &str, name: &str) {
        let id = format!("mod::{name}");
        self.g.upsert_node(
            id.clone(),
            ont::MODULE,
            name.to_string(),
            vec![
                ("language", Json::str("apl")),
                ("module_kind", Json::str("namespace")),
            ],
        );
        self.g.add_edge(file_id, edge::CONTAINS, id, vec![]);
    }

    /// Emit a `CALLS` edge from `caller_id` to a resolved function name. A unique
    /// candidate resolves; several stay ambiguous with the full candidate set.
    fn emit_call(&mut self, caller_id: &str, name: &str, cands: &[String]) {
        let mut props = vec![
            ("callee", Json::str(name.to_string())),
            ("method", Json::Bool(false)),
        ];
        if cands.len() == 1 {
            props.push(("resolution", Json::str("project")));
            props.push(("resolved", Json::Bool(true)));
            props.push(("candidate_count", Json::U64(1)));
            self.g
                .add_edge(caller_id, edge::CALLS, cands[0].clone(), props);
        } else {
            let target = format!("unresolved::{name}");
            self.g.upsert_node(
                target.clone(),
                ont::UNRESOLVED,
                name.to_string(),
                vec![
                    ("unresolved", Json::Bool(true)),
                    ("role", Json::str("call")),
                ],
            );
            props.push(("resolution", Json::str("ambiguous")));
            props.push(("resolved", Json::Bool(false)));
            props.push(("ambiguous", Json::Bool(true)));
            props.push(("candidate_count", Json::U64(cands.len() as u64)));
            props.push((
                "candidates",
                Json::Array(cands.iter().cloned().map(Json::Str).collect()),
            ));
            self.g.add_edge(caller_id, edge::CALLS, target, props);
        }
    }
}

// --- pure helpers -----------------------------------------------------------

/// The significant (non-trivia) direct children of a node.
fn sig_children(node: &Node) -> Vec<&Child> {
    node.children
        .iter()
        .filter(|c| match c {
            Child::Token(t) => !t.trivia,
            Child::Node(_) => true,
        })
        .collect()
}

fn tok_text<'a>(c: &Child, src: &'a str) -> Option<(&'static str, &'a str)> {
    match c {
        Child::Token(t) => Some((t.kind, t.span.text(src))),
        Child::Node(_) => None,
    }
}

/// The result of analyzing a statement's top-level assignment.
struct Assign<'a> {
    /// The single plain-name assignment target. A complex target (indexed,
    /// vector, multi-token) clears the whole analysis so nothing is mis-named.
    target: String,
    /// The dfn brace when the RHS is exactly `{…}`, else `None`.
    rhs_brace: Option<&'a Node>,
}

/// Analyze `target ← rhs`. Returns `None` unless the LHS is exactly one name.
fn analyze_assign<'a>(stmt: &'a Node, src: &'a str) -> Option<Assign<'a>> {
    let sig = sig_children(stmt);
    // Find the first top-level assignment arrow.
    let arrow = sig
        .iter()
        .position(|c| matches!(tok_text(c, src), Some((tk::ASSIGN, _))))?;
    let before = &sig[..arrow];
    let after = &sig[arrow + 1..];

    // LHS must be exactly one name token.
    if before.len() != 1 {
        return None;
    }
    let target = match tok_text(before[0], src) {
        Some((tk::NAME, name)) => name.to_string(),
        _ => return None,
    };

    // RHS is a dfn only when its first significant element is a brace group.
    let rhs_brace = after.first().and_then(|c| match c {
        Child::Node(n) if n.kind == cst::BRACE => Some(n),
        _ => None,
    });

    Some(Assign { target, rhs_brace })
}

/// `:Namespace Name` → `Name`. Recognized by the leading `:` punct + `Namespace`
/// control word + a following name.
fn namespace_name(stmt: &Node, src: &str) -> Option<String> {
    let sig = sig_children(stmt);
    let (k0, t0) = tok_text(sig.first()?, src)?;
    if !(k0 == tk::PUNCT && t0 == ":") {
        return None;
    }
    let (k1, t1) = tok_text(sig.get(1)?, src)?;
    if !(k1 == tk::NAME && t1 == "Namespace") {
        return None;
    }
    let (k2, t2) = tok_text(sig.get(2)?, src)?;
    if k2 == tk::NAME {
        Some(t2.to_string())
    } else {
        None
    }
}

/// Extract a tradfn name from its header by the standard APL rule. After
/// stripping the localization list (everything from the first `;`) and the
/// result-assignment (`Z←` … up to and including the first `←`), the remaining
/// names are `[larg] fname [rarg]`: 1 name → niladic (it is the name), 2 →
/// monadic (`fname rarg`, first is the name), 3 → dyadic (`larg fname rarg`, the
/// middle is the name).
fn tradfn_name(header: &Node, src: &str) -> Option<String> {
    // Direct significant tokens only (ignore any group content in the header).
    let mut toks: Vec<(&'static str, &str)> = Vec::new();
    for c in &header.children {
        if let Some((k, t)) = tok_text(c, src) {
            toks.push((k, t));
        }
    }
    // Cut the localization list at the first `;`.
    if let Some(semi) = toks.iter().position(|(k, t)| *k == tk::PUNCT && *t == ";") {
        toks.truncate(semi);
    }
    // Drop the result-assignment prefix up to and including the first `←`.
    if let Some(arrow) = toks.iter().position(|(k, _)| *k == tk::ASSIGN) {
        toks.drain(..=arrow);
    }
    let names: Vec<&str> = toks
        .iter()
        .filter(|(k, _)| *k == tk::NAME)
        .map(|(_, t)| *t)
        .collect();
    match names.len() {
        0 => None,
        1 | 2 => Some(names[0].to_string()),
        _ => Some(names[1].to_string()),
    }
}

/// Collect every name reference inside a body subtree that could denote a call:
/// any `name` token that is not an immediate `:`-prefixed control word. Order is
/// pre-order/source order; de-duplication happens at the call site.
fn collect_name_refs(node: &Node, src: &str, out: &mut Vec<String>) {
    let mut prev_colon = false;
    for c in &node.children {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => {
                let text = t.span.text(src);
                if t.kind == tk::NAME {
                    if !(prev_colon && is_control_word(text)) {
                        out.push(text.to_string());
                    }
                    prev_colon = false;
                } else {
                    prev_colon = t.kind == tk::PUNCT && text == ":";
                }
            }
            Child::Node(n) => {
                prev_colon = false;
                collect_name_refs(n, src, out);
            }
        }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::apl::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("ws.apl", src);
        let file = SourceFile {
            rel_path: "ws.apl".to_string(),
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
    fn dfn_assignment_is_a_function() {
        let g = graph_for("avg←{(+/⍵)÷≢⍵}");
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::FUNCTION && n.name == "avg"));
    }

    #[test]
    fn tradfn_name_is_read_from_header() {
        // Dyadic header `Z←L plus R` — the middle name is the function.
        let g = graph_for("∇ Z←L plus R\n Z←L+R\n∇");
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::FUNCTION && n.name == "plus"));
    }

    #[test]
    fn top_level_value_is_a_constant() {
        let g = graph_for("⎕IO←0\nVERSION←'1.2.3'");
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::CONSTANT && n.name == "VERSION"));
    }

    #[test]
    fn call_to_known_function_resolves() {
        // `double` defined as a dfn, then referenced inside `quad`'s body.
        let g = graph_for("double←{2×⍵}\nquad←{double double ⍵}");
        let calls = call_edges(&g);
        assert!(
            calls
                .iter()
                .any(|e| e.props.get("callee") == Some(&Json::str("double"))
                    && e.props.get("resolved") == Some(&Json::Bool(true))),
            "double should resolve as a project call"
        );
    }

    #[test]
    fn namespace_becomes_a_module() {
        let g = graph_for(":Namespace Utils\nx←1\n:EndNamespace");
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::MODULE && n.name == "Utils"));
    }
}
