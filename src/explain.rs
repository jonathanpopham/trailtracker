//! `trailtracker explain` — the atomic understanding primitive.
//!
//! One card answers the most-asked question in real work: *what is this
//! thing?* Given a target (an exact node id, a file path, or a symbol name)
//! the card joins every view the crate already computes:
//!
//! - **identity** — name, kind, `path:line`, qualified name.
//! - **classification** — domain ([`assign_domains`]), layer
//!   ([`assign_layers`]), archetype ([`classify_with`] over the built-in
//!   [`RULES`]).
//! - **connectivity** — fan-in/fan-out over DEPENDS-family edges, with the
//!   top dependents and dependencies by name.
//! - **blast radius** — the transitive reverse-reachability set, reusing
//!   [`crate::query::blast_radius_set`] (the same machinery behind
//!   `query blast-radius`).
//! - **neighbors** — the top hybrid-search hits for the target's name
//!   (excluding the target itself), each with its `why` evidence.
//!
//! Pure composition: this module *joins* existing deterministic passes, it
//! builds nothing new. Same graph, same target, byte-identical card.
//!
//! # Target resolution
//!
//! 1. Exact node **id** match (`fn::crate::parser::parse#7`).
//! 2. Exact File **path** match (`src/parser.rs`).
//! 3. Exact **name** match over all nodes. One hit resolves; several hits are
//!    an [`ExplainError::Ambiguous`] carrying the candidate list (the CLI
//!    renders it did-you-mean style and exits 2); zero hits are an
//!    [`ExplainError::NotFound`] carrying hybrid-search suggestions (exit 3).
//!
//! [`assign_domains`]: crate::extract::domains::assign_domains
//! [`assign_layers`]: crate::extract::layers::assign_layers
//! [`classify_with`]: crate::extract::archetypes::classify_with
//! [`RULES`]: crate::extract::archetypes::RULES

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use crate::core::json::Json;
use crate::extract::archetypes::{classify_with, SymbolFacts, RULES};
use crate::extract::domains::assign_domains;
use crate::extract::layers::assign_layers;
use crate::graph::{Graph, GraphNode};
use crate::ir::ontology::{node as ont, parent_relation, relation};
use crate::query::blast_radius_set;
use crate::search::{HybridIndex, SearchResult};

/// How many dependents/dependencies, blast-radius examples, and neighbors the
/// card shows. Counts are always exact; only the listings are capped.
const TOP_N: usize = 5;

/// Classification fallback when a node has no owning file in the respective
/// assignment (external deps, packages, ineligible files).
const UNASSIGNED: &str = "unassigned";

/// One resolution candidate, carried by [`ExplainError::Ambiguous`] and
/// rendered did-you-mean style by the CLI.
#[derive(Clone, Debug)]
pub struct Candidate {
    /// Exact node id — what the user should pass to disambiguate.
    pub id: String,
    /// Node kind (`Function`, `Type`, …).
    pub kind: &'static str,
    /// `path:line`, `path`, or `""` when the node has no source location.
    pub location: String,
}

/// Why a target failed to resolve to exactly one node.
#[derive(Debug)]
pub enum ExplainError {
    /// Several nodes share the target name. The CLI exits 2 with the
    /// candidate list (sorted by id — deterministic).
    Ambiguous {
        target: String,
        candidates: Vec<Candidate>,
    },
    /// Nothing matched by id, path, or name. The CLI exits 3 with the top
    /// hybrid-search suggestions (may be empty when the query is featureless).
    NotFound {
        target: String,
        suggestions: Vec<SearchResult>,
    },
}

/// Explain `target` against `graph` (analyzed from `dir`, named in the
/// output). Returns the rendered card — human text, or one
/// `trailtracker.explain/v1` JSON object when `json` is set.
pub fn explain(graph: &Graph, target: &str, dir: &str, json: bool) -> Result<String, ExplainError> {
    let node = resolve(graph, target)?;
    let card = build_card(graph, node, target, dir);
    if json {
        Ok(card_json(&card).to_line())
    } else {
        Ok(card_text(&card))
    }
}

// ---------------------------------------------------------------------------
// Resolution
// ---------------------------------------------------------------------------

/// Resolve `target` to exactly one node: exact id, then exact File path,
/// then exact name (see the module docs for the ambiguity/not-found contract).
/// `pub(crate)` so `nav` reuses the exact same resolution semantics.
pub(crate) fn resolve<'g>(graph: &'g Graph, target: &str) -> Result<&'g GraphNode, ExplainError> {
    // 1. Exact node id.
    if let Some(n) = graph.nodes().find(|n| n.id == target) {
        return Ok(n);
    }
    // 2. Exact File path (File `path` props are unique; nodes iterate in id
    //    order, so a hypothetical duplicate still resolves deterministically).
    if let Some(n) = graph
        .nodes()
        .find(|n| n.kind == ont::FILE && prop_str(n, "path") == target)
    {
        return Ok(n);
    }
    // 3. Exact name, over every node (id order = deterministic candidates).
    let matches: Vec<&GraphNode> = graph.nodes().filter(|n| n.name == target).collect();
    match matches.len() {
        1 => Ok(matches[0]),
        0 => Err(ExplainError::NotFound {
            target: target.to_string(),
            suggestions: HybridIndex::build(graph).search(target, TOP_N),
        }),
        _ => {
            let file_of = file_of_map(graph);
            let candidates = matches
                .iter()
                .map(|n| Candidate {
                    id: n.id.clone(),
                    kind: n.kind,
                    location: location_of(graph, n, &file_of),
                })
                .collect();
            Err(ExplainError::Ambiguous {
                target: target.to_string(),
                candidates,
            })
        }
    }
}

// ---------------------------------------------------------------------------
// Card assembly
// ---------------------------------------------------------------------------

/// One connected node reference: enough to render "name (Kind) — id".
struct NodeRef {
    id: String,
    name: String,
    kind: String,
}

/// Everything the card states, computed once and rendered twice (text/JSON).
struct Card {
    target: String,
    dir: String,
    // identity
    id: String,
    name: String,
    kind: &'static str,
    path: String,
    line: u64,
    qualified: String,
    // classification
    domain: String,
    layer: String,
    archetype: &'static str,
    // connectivity (fan counts are exact; listings capped at TOP_N)
    fan_in: usize,
    fan_out: usize,
    dependents: Vec<NodeRef>,
    dependencies: Vec<NodeRef>,
    // blast radius
    blast_count: usize,
    blast_examples: Vec<(String, String)>, // (id, kind)
    // neighbors
    neighbors: Vec<SearchResult>,
}

fn build_card(graph: &Graph, node: &GraphNode, target: &str, dir: &str) -> Card {
    let file_of = file_of_map(graph);
    let by_id: BTreeMap<&str, &GraphNode> = graph.nodes().map(|n| (n.id.as_str(), n)).collect();

    // Identity.
    let path = effective_path(graph, node, &file_of);
    let line = prop_u64(node, "line");
    let qualified = {
        let q = prop_str(node, "qualified_name");
        if q.is_empty() {
            node.name.clone()
        } else {
            q.to_string()
        }
    };

    // Classification: the owning File keys both assignments. A File node
    // owns itself; a symbol resolves through containment.
    let file_id: Option<&str> = if node.kind == ont::FILE {
        Some(node.id.as_str())
    } else {
        file_of.get(node.id.as_str()).copied()
    };
    let domains = assign_domains(graph);
    let layers = assign_layers(graph);
    let domain = file_id
        .and_then(|f| domains.file_domain.get(f))
        .cloned()
        .unwrap_or_else(|| UNASSIGNED.to_string());
    let layer = file_id
        .and_then(|f| layers.file_unit.get(f))
        .and_then(|unit| layers.unit_layer.get(unit))
        .cloned()
        .unwrap_or_else(|| UNASSIGNED.to_string());
    let declared_path = if path.is_empty() {
        None
    } else {
        Some(path.as_str())
    };
    let archetype = classify_with(RULES, &SymbolFacts::of(node, declared_path));

    // Connectivity: distinct DEPENDS-family neighbors, both directions.
    let mut dependent_ids: BTreeSet<&str> = BTreeSet::new();
    let mut dependency_ids: BTreeSet<&str> = BTreeSet::new();
    for e in graph.edges() {
        if parent_relation(e.kind) != Some(relation::DEPENDS) {
            continue;
        }
        if e.to == node.id && e.from != node.id {
            dependent_ids.insert(e.from.as_str());
        }
        if e.from == node.id && e.to != node.id {
            dependency_ids.insert(e.to.as_str());
        }
    }
    let to_refs = |ids: &BTreeSet<&str>| -> Vec<NodeRef> {
        // "top by name": sort by (name, id) for a stable, readable listing.
        let mut refs: Vec<NodeRef> = ids
            .iter()
            .map(|id| NodeRef {
                id: (*id).to_string(),
                name: by_id
                    .get(id)
                    .map_or_else(|| (*id).to_string(), |n| n.name.clone()),
                kind: by_id.get(id).map_or("?", |n| n.kind).to_string(),
            })
            .collect();
        refs.sort_by(|a, b| a.name.cmp(&b.name).then_with(|| a.id.cmp(&b.id)));
        refs.truncate(TOP_N);
        refs
    };

    // Blast radius: the exact machinery behind `query blast-radius`.
    let affected = blast_radius_set(graph, std::slice::from_ref(&node.id));
    let blast_examples: Vec<(String, String)> = affected
        .iter()
        .take(TOP_N)
        .map(|id| {
            (
                id.clone(),
                by_id.get(id.as_str()).map_or("?", |n| n.kind).to_string(),
            )
        })
        .collect();

    // Neighbors: hybrid search for the target's name, excluding itself.
    let neighbors: Vec<SearchResult> = HybridIndex::build(graph)
        .search(&node.name, TOP_N + 1)
        .into_iter()
        .filter(|r| r.id != node.id)
        .take(TOP_N)
        .collect();

    Card {
        target: target.to_string(),
        dir: dir.to_string(),
        id: node.id.clone(),
        name: node.name.clone(),
        kind: node.kind,
        path,
        line,
        qualified,
        domain,
        layer,
        archetype,
        fan_in: dependent_ids.len(),
        fan_out: dependency_ids.len(),
        dependents: to_refs(&dependent_ids),
        dependencies: to_refs(&dependency_ids),
        blast_count: affected.len(),
        blast_examples,
        neighbors,
    }
}

// ---------------------------------------------------------------------------
// Ownership / location helpers (consume the same containment convention the
// extractors use: CONTAINMENT-family edges, preferring a File parent)
// ---------------------------------------------------------------------------

/// symbol id → owning File id, via CONTAINMENT-family edges. A child reached
/// both by `File DECLARES fn` and `Type HAS_METHOD fn` resolves to its File
/// (first-seen wins among equals; edges iterate in stable signature order).
/// `pub(crate)` so `nav` shares the exact same ownership convention.
pub(crate) fn file_of_map(graph: &Graph) -> BTreeMap<&str, &str> {
    let kind_of: BTreeMap<&str, &'static str> =
        graph.nodes().map(|n| (n.id.as_str(), n.kind)).collect();
    let mut parent: BTreeMap<&str, &str> = BTreeMap::new();
    for e in graph.edges() {
        if parent_relation(e.kind) != Some(relation::CONTAINMENT) {
            continue;
        }
        let from_is_file = kind_of.get(e.from.as_str()).copied() == Some(ont::FILE);
        match parent.get(e.to.as_str()) {
            None => {
                parent.insert(e.to.as_str(), e.from.as_str());
            }
            Some(existing) => {
                let existing_is_file = kind_of.get(existing).copied() == Some(ont::FILE);
                if from_is_file && !existing_is_file {
                    parent.insert(e.to.as_str(), e.from.as_str());
                }
            }
        }
    }
    let mut file_of: BTreeMap<&str, &str> = BTreeMap::new();
    for n in graph.nodes() {
        if n.kind == ont::FILE {
            continue;
        }
        // Bounded walk to the owning File: containment chains are shallow;
        // the bound only guards against a malformed cyclic containment.
        let mut id = n.id.as_str();
        for _ in 0..64 {
            if kind_of.get(id).copied() == Some(ont::FILE) {
                file_of.insert(n.id.as_str(), id);
                break;
            }
            match parent.get(id) {
                Some(p) => id = p,
                None => break,
            }
        }
    }
    file_of
}

/// The node's effective source path: its own `path` prop when present, else
/// the `path` of its owning File, else `""`.
fn effective_path(graph: &Graph, node: &GraphNode, file_of: &BTreeMap<&str, &str>) -> String {
    let own = prop_str(node, "path");
    if !own.is_empty() {
        return own.to_string();
    }
    file_of
        .get(node.id.as_str())
        .and_then(|fid| graph.nodes().find(|n| n.id == *fid))
        .map(|f| prop_str(f, "path").to_string())
        .unwrap_or_default()
}

/// `path:line`, `path`, or `""` — the human location of a node.
fn location_of(graph: &Graph, node: &GraphNode, file_of: &BTreeMap<&str, &str>) -> String {
    let path = effective_path(graph, node, file_of);
    let line = prop_u64(node, "line");
    if path.is_empty() {
        String::new()
    } else if line == 0 {
        path
    } else {
        format!("{path}:{line}")
    }
}

fn prop_str<'a>(node: &'a GraphNode, key: &str) -> &'a str {
    match node.props.get(key) {
        Some(Json::Str(s)) => s.as_str(),
        _ => "",
    }
}

fn prop_u64(node: &GraphNode, key: &str) -> u64 {
    match node.props.get(key) {
        Some(Json::U64(n)) => *n,
        Some(Json::I64(n)) if *n >= 0 => *n as u64,
        _ => 0,
    }
}

// ---------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------

/// The human card. Writing into a String is infallible; the discarded
/// Results are fmt noise.
fn card_text(c: &Card) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "explain: {} ({}) — {}", c.name, c.kind, c.id);
    let _ = writeln!(out, "  identity");
    let location = if c.path.is_empty() {
        "(no source location)".to_string()
    } else if c.line == 0 {
        c.path.clone()
    } else {
        format!("{}:{}", c.path, c.line)
    };
    let _ = writeln!(out, "    path        {location}");
    let _ = writeln!(out, "    qualified   {}", c.qualified);
    let _ = writeln!(out, "  classification");
    let _ = writeln!(out, "    domain      {}", c.domain);
    let _ = writeln!(out, "    layer       {}", c.layer);
    let _ = writeln!(out, "    archetype   {}", c.archetype);
    let _ = writeln!(out, "  connectivity");
    let _ = writeln!(out, "    fan-in {} · fan-out {}", c.fan_in, c.fan_out);
    let list = |out: &mut String, label: &str, total: usize, refs: &[NodeRef]| {
        let _ = writeln!(out, "    {label} ({total})");
        for r in refs {
            let _ = writeln!(out, "      {} ({}) — {}", r.name, r.kind, r.id);
        }
        if total > refs.len() {
            let _ = writeln!(out, "      … +{} more", total - refs.len());
        }
    };
    list(&mut out, "dependents", c.fan_in, &c.dependents);
    list(&mut out, "dependencies", c.fan_out, &c.dependencies);
    let _ = writeln!(out, "  blast radius");
    let _ = writeln!(
        out,
        "    {} node(s) could be affected if this changes",
        c.blast_count
    );
    for (id, kind) in &c.blast_examples {
        let _ = writeln!(out, "      [{kind}] {id}");
    }
    if c.blast_count > c.blast_examples.len() {
        let _ = writeln!(
            out,
            "      … +{} more (see `trailtracker query blast-radius {} {}`)",
            c.blast_count - c.blast_examples.len(),
            c.id,
            c.dir
        );
    }
    let _ = writeln!(out, "  neighbors (hybrid search: \"{}\")", c.name);
    if c.neighbors.is_empty() {
        let _ = writeln!(out, "      (none)");
    }
    for (i, n) in c.neighbors.iter().enumerate() {
        let _ = write!(out, "    {:>3}. {} ({})", i + 1, n.name, n.kind);
        if !n.path.is_empty() {
            let _ = write!(out, "  {}", n.path);
        }
        let _ = writeln!(out);
        if !n.why.is_empty() {
            let _ = writeln!(out, "         {}", n.why.join(" · "));
        }
    }
    out
}

/// Schema `trailtracker.explain/v1` — see `capabilities`.
fn card_json(c: &Card) -> Json {
    let node_ref = |r: &NodeRef| {
        Json::obj([
            ("id", Json::str(r.id.clone())),
            ("name", Json::str(r.name.clone())),
            ("kind", Json::str(r.kind.clone())),
        ])
    };
    let neighbors: Vec<Json> = c
        .neighbors
        .iter()
        .enumerate()
        .map(|(i, r)| {
            Json::obj([
                ("rank", (i + 1).into()),
                ("id", Json::str(r.id.as_str())),
                ("name", Json::str(r.name.as_str())),
                ("kind", Json::str(r.kind)),
                ("path", Json::str(r.path.as_str())),
                ("score", Json::F64(r.score)),
                (
                    "why",
                    Json::Array(r.why.iter().map(|w| Json::str(w.as_str())).collect()),
                ),
            ])
        })
        .collect();
    Json::obj([
        ("schema", Json::str("trailtracker.explain/v1")),
        ("command", Json::str("explain")),
        ("dir", Json::str(c.dir.as_str())),
        ("target", Json::str(c.target.as_str())),
        (
            "identity",
            Json::obj([
                ("id", Json::str(c.id.as_str())),
                ("name", Json::str(c.name.as_str())),
                ("kind", Json::str(c.kind)),
                ("path", Json::str(c.path.as_str())),
                ("line", Json::U64(c.line)),
                ("qualified_name", Json::str(c.qualified.as_str())),
            ]),
        ),
        (
            "classification",
            Json::obj([
                ("domain", Json::str(c.domain.as_str())),
                ("layer", Json::str(c.layer.as_str())),
                ("archetype", Json::str(c.archetype)),
            ]),
        ),
        (
            "connectivity",
            Json::obj([
                ("fan_in", c.fan_in.into()),
                ("fan_out", c.fan_out.into()),
                (
                    "dependents",
                    Json::Array(c.dependents.iter().map(node_ref).collect()),
                ),
                (
                    "dependencies",
                    Json::Array(c.dependencies.iter().map(node_ref).collect()),
                ),
            ]),
        ),
        (
            "blast_radius",
            Json::obj([
                ("count", c.blast_count.into()),
                (
                    "examples",
                    Json::Array(
                        c.blast_examples
                            .iter()
                            .map(|(id, kind)| {
                                Json::obj([
                                    ("id", Json::str(id.clone())),
                                    ("kind", Json::str(kind.clone())),
                                ])
                            })
                            .collect(),
                    ),
                ),
            ]),
        ),
        ("neighbors", Json::Array(neighbors)),
    ])
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    fn calc() -> Graph {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("eval/corpus/calc");
        crate::pipeline::analyze_dir(&root)
            .expect("calc corpus analyzes")
            .graph
    }

    #[test]
    fn explain_resolves_a_unique_name_and_renders_every_section() {
        let g = calc();
        let card = explain(&g, "parse", "eval/corpus/calc", false).expect("parse resolves");
        assert!(
            card.starts_with("explain: parse (Function) — fn::crate::parser::parse#7"),
            "header wrong:\n{card}"
        );
        for section in [
            "  identity",
            "src/parser.rs:7",
            "crate::parser::parse",
            "  classification",
            "    domain      op",
            "    layer       Shared",
            "  connectivity",
            "  blast radius",
            "  neighbors (hybrid search: \"parse\")",
        ] {
            assert!(card.contains(section), "missing `{section}`:\n{card}");
        }
        // The neighbor list never contains the target itself.
        assert!(
            !card
                .split("neighbors")
                .nth(1)
                .unwrap()
                .contains("fn::crate::parser::parse#7"),
            "target must not be its own neighbor:\n{card}"
        );
        // Deterministic.
        assert_eq!(
            card,
            explain(&g, "parse", "eval/corpus/calc", false).unwrap()
        );
    }

    #[test]
    fn explain_by_id_path_and_name_agree() {
        let g = calc();
        let by_name = explain(&g, "parse", "d", false).unwrap();
        let by_id = explain(&g, "fn::crate::parser::parse#7", "d", false).unwrap();
        assert_eq!(by_name, by_id);
        // A file path resolves to the File node.
        let by_path = explain(&g, "src/parser.rs", "d", false).unwrap();
        assert!(
            by_path.starts_with("explain: parser.rs (File) — file::src/parser.rs"),
            "path target must resolve to the File node:\n{by_path}"
        );
    }

    #[test]
    fn ambiguous_name_lists_candidates() {
        let g = calc();
        // `reset` exists both as crate::reset and crate::ops::reset.
        match explain(&g, "reset", "d", false) {
            Err(ExplainError::Ambiguous { target, candidates }) => {
                assert_eq!(target, "reset");
                let ids: Vec<&str> = candidates.iter().map(|c| c.id.as_str()).collect();
                assert!(ids.contains(&"fn::crate::reset#18"), "{ids:?}");
                assert!(ids.contains(&"fn::crate::ops::reset#60"), "{ids:?}");
                // Candidates carry a usable location.
                assert!(
                    candidates.iter().any(|c| c.location == "src/lib.rs:18"),
                    "{candidates:?}"
                );
            }
            other => panic!("expected Ambiguous, got {other:?}"),
        }
    }

    #[test]
    fn unknown_target_suggests_search_hits() {
        let g = calc();
        match explain(&g, "Parsr", "d", false) {
            Err(ExplainError::NotFound {
                target,
                suggestions,
            }) => {
                assert_eq!(target, "Parsr");
                assert!(
                    suggestions.iter().any(|s| s.name.contains("pars")),
                    "embed tier should suggest parse-family hits: {suggestions:?}"
                );
            }
            other => panic!("expected NotFound, got {other:?}"),
        }
    }

    #[test]
    fn json_card_matches_schema_and_is_deterministic() {
        let g = calc();
        let line = explain(&g, "parse", "eval/corpus/calc", true).unwrap();
        assert!(line.contains("\"schema\":\"trailtracker.explain/v1\""));
        for key in [
            "\"identity\":",
            "\"classification\":",
            "\"connectivity\":",
            "\"blast_radius\":",
            "\"neighbors\":",
            "\"fan_in\":",
            "\"fan_out\":",
            "\"qualified_name\":\"crate::parser::parse\"",
            "\"domain\":\"op\"",
            "\"layer\":\"Shared\"",
        ] {
            assert!(line.contains(key), "missing {key} in:\n{line}");
        }
        assert_eq!(
            line,
            explain(&g, "parse", "eval/corpus/calc", true).unwrap()
        );
    }

    #[test]
    fn blast_radius_in_card_matches_the_query_machinery() {
        let g = calc();
        let affected = blast_radius_set(&g, &["fn::crate::parser::parse#7".to_string()]);
        let line = explain(&g, "parse", "d", true).unwrap();
        assert!(
            line.contains(&format!("\"count\":{}", affected.len())),
            "card blast count must equal query blast-radius: {line}"
        );
    }
}
