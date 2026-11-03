//! Lower the Cypher CST into the canonical graph.
//!
//! Cypher is a graph **query** language, not a definition language: a query file
//! declares no functions, types, or modules of its own. So this lowering is
//! deliberately sparse and honest — fabricating definitions to look productive
//! would be a lie. What a Cypher file *does* contain are references, and those
//! map cleanly onto the shared ontology:
//!
//!   - Node labels `(:Label)` / `(n:Label)` and relationship types `[:REL]` /
//!     `[r:REL]` → a [`Type`] node named for the label (the closest honest
//!     analogue of a "type" in a graph DB), with a [`USES_TYPE`] edge from the
//!     file. Labels live in `(...)` groups, relationship types in `[...]`; a `:`
//!     inside a `{...}` property map is a key, never a label — the delimiter kind
//!     disambiguates, so property keys are never mistaken for labels.
//!   - `CALL proc.name(...)` and function calls (`count(*)`, `toInteger(x)`,
//!     `apoc.coll.sum(x)`) → a [`CALLS`] edge from the file to an
//!     [`ExternalDependency`] named for the (dotted) callee. Everything a query
//!     calls is external to the query, so these are external deps, not
//!     resolved-in-file definitions.
//!   - `MATCH` / `CREATE` / `MERGE` / etc. are statements: kept losslessly in the
//!     CST, but they define nothing, so they emit no nodes.
//!
//! What this lowering deliberately **punts** (documented, not hidden):
//!   - Bare label predicates outside a pattern (`WHERE n:Person`) are not lowered
//!     — only labels inside `(...)` and relationship types inside `[...]` are read,
//!     which keeps property-map keys and `CASE` colons from being misread.
//!   - `LOAD CSV FROM '…'` data sources are kept lossless but not modelled as
//!     dependencies.
//!   - Parameters (`$x`), variables, and aliases are not given nodes (no honest
//!     definition site exists in a query).
//!
//! Everything comes from real tokens on the lossless tree; nothing is invented.

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::cypher::lexer::{is_keyword, kind as tk};
use crate::lang::cypher::parser::node as cst;
use crate::lang::frontend::SourceFile;

/// Lower a whole project's worth of Cypher files into a graph. `manifest_deps` is
/// unused (Cypher has no manifest the pipeline reads). Each file is independent:
/// queries do not share scope, so resolving anything across files would fabricate
/// a relationship.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    let mut g = Graph::new();
    let pkg_id = format!("pkg::{package}");
    g.upsert_node(
        pkg_id.clone(),
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("cypher"))],
    );

    for f in files {
        let file_id = format!("file::{}", f.rel_path);
        g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("cypher")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        g.add_edge(pkg_id.clone(), edge::CONTAINS, file_id.clone(), vec![]);

        // Collect references over the whole lossless tree, in deterministic
        // (document) order.
        let mut labels: Vec<String> = Vec::new();
        let mut rels: Vec<String> = Vec::new();
        let mut calls: Vec<String> = Vec::new();
        scan(f.root, f.source, &mut labels, &mut rels, &mut calls);

        dedup(&mut labels);
        dedup(&mut rels);
        dedup(&mut calls);

        for label in labels {
            let type_id = format!("type::cypher::label::{label}");
            g.upsert_node(
                type_id.clone(),
                ont::TYPE,
                label.clone(),
                vec![
                    ("type_kind", Json::str("label")),
                    ("language", Json::str("cypher")),
                ],
            );
            g.add_edge(
                file_id.clone(),
                edge::USES_TYPE,
                type_id,
                vec![
                    ("type_name", Json::str(label)),
                    ("category", Json::str("node_label")),
                ],
            );
        }

        for rel in rels {
            let type_id = format!("type::cypher::rel::{rel}");
            g.upsert_node(
                type_id.clone(),
                ont::TYPE,
                rel.clone(),
                vec![
                    ("type_kind", Json::str("relationship_type")),
                    ("language", Json::str("cypher")),
                ],
            );
            g.add_edge(
                file_id.clone(),
                edge::USES_TYPE,
                type_id,
                vec![
                    ("type_name", Json::str(rel)),
                    ("category", Json::str("relationship_type")),
                ],
            );
        }

        for callee in calls {
            let dep_id = format!("ext::{callee}");
            g.upsert_node(
                dep_id.clone(),
                ont::EXTERNAL_DEPENDENCY,
                callee.clone(),
                vec![
                    ("external", Json::Bool(true)),
                    ("source", Json::str("call")),
                ],
            );
            // The file invokes the procedure/function; there is no in-file
            // definition to resolve against, so the call is always external.
            g.add_edge(
                file_id.clone(),
                edge::CALLS,
                dep_id,
                vec![
                    ("callee", Json::str(callee)),
                    ("resolved", Json::Bool(false)),
                    ("resolution", Json::str("external")),
                ],
            );
        }
    }

    g
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

fn el_text<'a>(e: &El<'a>) -> Option<&'a str> {
    match e {
        El::Tok { text, .. } => Some(text),
        El::Grp(_) => None,
    }
}

/// A name-bearing token: a plain identifier or a backtick-quoted name (with the
/// backticks stripped). Returns `None` for anything else.
fn name_of(e: &El) -> Option<String> {
    match e {
        El::Tok { text, kind } if *kind == tk::IDENT => Some((*text).to_string()),
        El::Tok { text, kind } if *kind == tk::BACKTICK_IDENT => Some(strip_backticks(text)),
        _ => None,
    }
}

/// Recursively scan the tree, reading:
///   - node labels from `:name` (and chained `:a:b`) inside `Paren` groups,
///   - relationship types from `:name` / `|name` inside `Bracket` groups,
///   - call heads `ident(.ident)* (...)` at any level.
fn scan<'a>(
    node: &'a Node,
    src: &'a str,
    labels: &mut Vec<String>,
    rels: &mut Vec<String>,
    calls: &mut Vec<String>,
) {
    let els = significant_children(node, src);
    let n = els.len();

    // Labels / relationship types live directly inside their delimiter group.
    if node.kind == cst::PAREN {
        for i in 0..n {
            if el_text(&els[i]) == Some(":") {
                if let Some(name) = els.get(i + 1).and_then(name_of) {
                    labels.push(name);
                }
            }
        }
    } else if node.kind == cst::BRACKET {
        for i in 0..n {
            let t = el_text(&els[i]);
            // A `:`/`|` introduces a relationship type only when followed by a
            // name (variable-length `[*1..3]` has no name after `*`).
            if t == Some(":") || t == Some("|") {
                if let Some(name) = els.get(i + 1).and_then(name_of) {
                    rels.push(name);
                }
            }
        }
    }

    // Call sites: `head(.head)* (...)` at this level, head not a keyword.
    let mut i = 0;
    while i < n {
        if let El::Tok { text, kind } = &els[i] {
            let is_name = *kind == tk::IDENT || *kind == tk::BACKTICK_IDENT;
            let prev = if i > 0 { el_text(&els[i - 1]) } else { None };
            let head_ok = is_name && prev != Some(".") && !(*kind == tk::IDENT && is_keyword(text));
            if head_ok {
                let mut segs = vec![name_of(&els[i]).unwrap_or_default()];
                let mut j = i;
                while j + 2 < n
                    && el_text(&els[j + 1]) == Some(".")
                    && els.get(j + 2).and_then(name_of).is_some()
                {
                    segs.push(name_of(&els[j + 2]).unwrap_or_default());
                    j += 2;
                }
                if let Some(El::Grp(g)) = els.get(j + 1) {
                    if g.kind == cst::PAREN {
                        calls.push(segs.join("."));
                    }
                }
                i = j + 1;
                continue;
            }
        }
        i += 1;
    }

    // Recurse into every group child.
    for e in &els {
        if let El::Grp(g) = e {
            scan(g, src, labels, rels, calls);
        }
    }
}

// --- pure helpers -----------------------------------------------------------

fn dedup(v: &mut Vec<String>) {
    let mut seen = std::collections::BTreeSet::new();
    v.retain(|x| !x.is_empty() && seen.insert(x.clone()));
}

fn strip_backticks(text: &str) -> String {
    let t = text.trim();
    if t.len() >= 2 && t.starts_with('`') && t.ends_with('`') {
        t[1..t.len() - 1].replace("``", "`")
    } else {
        t.to_string()
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
    use crate::lang::cypher::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("q.cypher", src);
        let file = SourceFile {
            rel_path: "q.cypher".to_string(),
            module_path: vec![],
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    #[test]
    fn node_labels_become_types() {
        let g = graph_for("MATCH (n:Person) RETURN n");
        assert!(g.has_node("type::cypher::label::Person"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::USES_TYPE && e.to == "type::cypher::label::Person"));
    }

    #[test]
    fn relationship_types_become_types() {
        let g = graph_for("MATCH (a)-[:KNOWS]->(b) RETURN a, b");
        assert!(g.has_node("type::cypher::rel::KNOWS"));
        let uses: Vec<_> = g
            .edges()
            .filter(|e| e.kind == edge::USES_TYPE && e.to == "type::cypher::rel::KNOWS")
            .collect();
        assert_eq!(uses.len(), 1);
    }

    #[test]
    fn relationship_type_alternation_is_captured() {
        let g = graph_for("MATCH (a)-[r:LIKES|FOLLOWS]->(b) RETURN r");
        assert!(g.has_node("type::cypher::rel::LIKES"));
        assert!(g.has_node("type::cypher::rel::FOLLOWS"));
    }

    #[test]
    fn property_map_keys_are_not_labels() {
        // `name` and `age` are property keys in a brace, never node labels.
        let g = graph_for("MATCH (n:Person {name: 'x', age: 30}) RETURN n");
        assert!(g.has_node("type::cypher::label::Person"));
        assert!(!g.has_node("type::cypher::label::name"));
        assert!(!g.has_node("type::cypher::label::age"));
    }

    #[test]
    fn function_calls_are_external_deps() {
        let g = graph_for("MATCH (n) RETURN count(n), toInteger(n.x)");
        assert!(g.has_node("ext::count"));
        assert!(g.has_node("ext::toInteger"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::CALLS && e.to == "ext::count"));
    }

    #[test]
    fn dotted_procedure_call_is_one_callee() {
        let g = graph_for("CALL apoc.coll.sum([1,2,3]) YIELD value RETURN value");
        assert!(g.has_node("ext::apoc.coll.sum"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::CALLS && e.to == "ext::apoc.coll.sum"));
    }

    #[test]
    fn property_access_is_not_a_call() {
        // `n.name` has no `(...)`, so it must not be read as a call.
        let g = graph_for("MATCH (n:Person) RETURN n.name");
        assert!(!g.edges().any(|e| e.kind == edge::CALLS));
    }

    #[test]
    fn defines_nothing_emits_only_file_and_refs() {
        // An honest result for a query that defines nothing: a File (+Package)
        // plus its references. No Function/Module/Constant nodes are fabricated.
        let g = graph_for("MATCH (n:Person)-[:KNOWS]->(m:Person) RETURN n, m");
        assert_eq!(g.count_nodes_of(ont::FUNCTION), 0);
        assert_eq!(g.count_nodes_of(ont::MODULE), 0);
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 0);
        assert!(g.count_nodes_of(ont::FILE) >= 1);
    }

    #[test]
    fn backtick_label_is_unquoted() {
        let g = graph_for("MATCH (n:`Weird Label`) RETURN n");
        assert!(g.has_node("type::cypher::label::Weird Label"));
    }

    #[test]
    fn output_is_deterministic() {
        let src = "MATCH (n:Person)-[:KNOWS]->(m) WHERE n.age > count(m) RETURN n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
