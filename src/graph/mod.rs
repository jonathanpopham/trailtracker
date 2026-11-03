//! The canonical graph: the product artifact of TrailTracker.
//!
//! Nodes and relationships are language-neutral (the [`crate::ir::ontology`]
//! vocabulary). Output is **deterministic** — nodes are keyed in a `BTreeMap`
//! and edges are de-duplicated and ordered by a stable signature, so the same
//! input always linearizes byte-for-byte identically. JSONL is the baseline
//! stream format for LLM consumption.

use std::collections::BTreeMap;

use crate::core::json::Json;

/// A graph node. `id` is a deterministic, human-readable key (e.g.
/// `fn::core::span::fnv1a_64`). `props` carry source locations and
/// language-specific facts.
#[derive(Clone, Debug)]
pub struct GraphNode {
    pub id: String,
    pub kind: &'static str,
    pub name: String,
    pub props: BTreeMap<String, Json>,
}

/// A relationship. Unresolved/external endpoints are explicit logical nodes,
/// never silent omissions.
#[derive(Clone, Debug)]
pub struct GraphEdge {
    pub from: String,
    pub kind: &'static str,
    pub to: String,
    pub props: BTreeMap<String, Json>,
}

#[derive(Default)]
pub struct Graph {
    nodes: BTreeMap<String, GraphNode>,
    /// Keyed by a stable signature for dedup + deterministic ordering.
    edges: BTreeMap<String, GraphEdge>,
}

impl Graph {
    pub fn new() -> Graph {
        Graph::default()
    }

    /// Insert a node, merging properties if the id already exists (later props
    /// win only for keys not already set, so first-seen source location is
    /// stable).
    pub fn upsert_node(
        &mut self,
        id: impl Into<String>,
        kind: &'static str,
        name: impl Into<String>,
        props: Vec<(&'static str, Json)>,
    ) {
        let id = id.into();
        let entry = self.nodes.entry(id.clone()).or_insert_with(|| GraphNode {
            id,
            kind,
            name: name.into(),
            props: BTreeMap::new(),
        });
        for (k, v) in props {
            entry.props.entry(k.to_string()).or_insert(v);
        }
    }

    pub fn add_edge(
        &mut self,
        from: impl Into<String>,
        kind: &'static str,
        to: impl Into<String>,
        props: Vec<(&'static str, Json)>,
    ) {
        let from = from.into();
        let to = to.into();
        let mut pmap = BTreeMap::new();
        for (k, v) in props {
            pmap.insert(k.to_string(), v);
        }
        self.insert_edge_raw(from, kind, to, pmap);
    }

    /// Rebuild a node exactly as it was serialized (the incremental-cache load
    /// path). Same first-seen-wins semantics as [`Graph::merge`]: an existing id
    /// is kept untouched.
    pub(crate) fn insert_node_raw(
        &mut self,
        id: String,
        kind: &'static str,
        name: String,
        props: BTreeMap<String, Json>,
    ) {
        self.nodes.entry(id.clone()).or_insert(GraphNode {
            id,
            kind,
            name,
            props,
        });
    }

    /// Rebuild an edge exactly as it was serialized (the incremental-cache load
    /// path). The dedup/order key is re-derived by the same [`edge_key`] that
    /// [`Graph::add_edge`] uses, so a reloaded edge sorts and dedups
    /// identically to a freshly lowered one.
    pub(crate) fn insert_edge_raw(
        &mut self,
        from: String,
        kind: &'static str,
        to: String,
        props: BTreeMap<String, Json>,
    ) {
        let key = edge_key(&from, kind, &to, &props);
        self.edges.entry(key).or_insert(GraphEdge {
            from,
            kind,
            to,
            props,
        });
    }

    /// Fold another graph into this one. A node (by id) or edge (by stable
    /// signature) already present is kept as first seen; later contributions only
    /// fill in absent entries. Because both stores are `BTreeMap`s and the merge
    /// is order-independent for a fixed input set, the result stays deterministic
    /// — this is how each language front end's sub-graph is merged into the single
    /// shared graph without any front end clobbering another's facts.
    pub fn merge(&mut self, other: Graph) {
        for (id, node) in other.nodes {
            self.nodes.entry(id).or_insert(node);
        }
        for (key, edge) in other.edges {
            self.edges.entry(key).or_insert(edge);
        }
    }

    pub fn has_node(&self, id: &str) -> bool {
        self.nodes.contains_key(id)
    }

    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }

    pub fn nodes(&self) -> impl Iterator<Item = &GraphNode> {
        self.nodes.values()
    }

    pub fn edges(&self) -> impl Iterator<Item = &GraphEdge> {
        self.edges.values()
    }

    pub fn count_nodes_of(&self, kind: &str) -> usize {
        self.nodes.values().filter(|n| n.kind == kind).count()
    }

    pub fn count_edges_of(&self, kind: &str) -> usize {
        self.edges.values().filter(|e| e.kind == kind).count()
    }

    /// One JSON object per line: nodes first (sorted by id), then edges (sorted
    /// by signature). Deterministic and streamable.
    pub fn to_jsonl(&self) -> String {
        let mut out = String::new();
        for n in self.nodes.values() {
            out.push_str(&node_json(n).to_line());
            out.push('\n');
        }
        for e in self.edges.values() {
            out.push_str(&edge_json(e).to_line());
            out.push('\n');
        }
        out
    }

    /// Whole-graph single JSON object, useful for inspection and fixtures.
    pub fn to_json(&self) -> Json {
        Json::obj([
            (
                "nodes",
                Json::Array(self.nodes.values().map(node_json).collect()),
            ),
            (
                "edges",
                Json::Array(self.edges.values().map(edge_json).collect()),
            ),
        ])
    }
}

/// The stable signature every edge is deduplicated and ordered by. One
/// derivation shared by [`Graph::add_edge`] and [`Graph::insert_edge_raw`], so
/// the cache load path can never drift from the lowering path.
fn edge_key(from: &str, kind: &str, to: &str, props: &BTreeMap<String, Json>) -> String {
    let prop_sig = Json::Object(props.clone()).to_line();
    format!("{from}\u{1}{kind}\u{1}{to}\u{1}{prop_sig}")
}

fn node_json(n: &GraphNode) -> Json {
    Json::obj([
        ("record", Json::str("node")),
        ("id", Json::str(n.id.clone())),
        ("kind", Json::str(n.kind)),
        ("name", Json::str(n.name.clone())),
        ("properties", Json::Object(n.props.clone())),
    ])
}

fn edge_json(e: &GraphEdge) -> Json {
    Json::obj([
        ("record", Json::str("edge")),
        ("from", Json::str(e.from.clone())),
        ("kind", Json::str(e.kind)),
        ("to", Json::str(e.to.clone())),
        ("properties", Json::Object(e.props.clone())),
    ])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn edges_dedup_and_output_is_deterministic() {
        let mut g = Graph::new();
        g.upsert_node("b", "File", "b", vec![]);
        g.upsert_node("a", "File", "a", vec![]);
        g.add_edge("a", "CALLS", "b", vec![("resolved", Json::Bool(true))]);
        g.add_edge("a", "CALLS", "b", vec![("resolved", Json::Bool(true))]);
        assert_eq!(g.edge_count(), 1);
        let first = g.to_jsonl();
        let second = g.to_jsonl();
        assert_eq!(first, second);
        // Node "a" sorts before "b".
        assert!(first.find("\"id\":\"a\"").unwrap() < first.find("\"id\":\"b\"").unwrap());
    }
}
