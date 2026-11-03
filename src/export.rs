//! Ontoloom wire export: serialize any TrailTracker graph (the base graph or
//! an extractor's derived view) in the JSON wire format the Ontoloom editor
//! loads directly.
//!
//! The target shape is defined by Ontoloom's `model.rs`/`import.rs`:
//!
//! ```json
//! {
//!   "name": "calc (hierarchy)",
//!   "nodes": [
//!     {"id":"n1","labels":["Module","Domain"],"caption":"Order",
//!      "properties":{},"x":0,"y":0}
//!   ],
//!   "relationships": [
//!     {"id":"n1__CONTAINS__n2","type":"CONTAINS","from":"n1","to":"n2",
//!      "properties":{}}
//!   ]
//! }
//! ```
//!
//! Mapping:
//! - node → `id` kept, `labels` = `[kind]` plus the Title-cased values of any
//!   `level`/`domain`/`archetype`/`layer` string props (de-duplicated), so the
//!   hierarchy view's groupings are pivotable as Ontoloom labels; `caption` =
//!   node name; `properties` pass through unchanged.
//! - `x`/`y` are a deterministic **seed layout** only — nodes are banded by
//!   `level` (domain, unit, file, symbol, then other kinds) and gridded within
//!   each band so nothing loads as a single stack of points. A real layout
//!   pass is a separate concern (gs-H5).
//! - edge → `id` = `<from>__<kind>__<to>` (a `__N` suffix disambiguates the
//!   rare same-endpoint duplicates that differ only in properties), `type` =
//!   kind, `from`/`to`/`properties` pass through.
//!
//! Ontoloom **hard-rejects** a wire graph whose relationship references a
//! missing node, so an edge with an endpoint absent from the node set is
//! dropped rather than poisoning the whole import. TrailTracker graphs are
//! closed (unresolved endpoints are explicit logical nodes), so in practice
//! nothing is dropped.
//!
//! Deterministic and byte-stable: everything walks the `BTreeMap`-ordered
//! [`Graph`] iterators and serializes through the sorted-key
//! [`crate::core::json`] writer — the same graph always emits identical bytes.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::json::Json;
use crate::graph::{Graph, GraphNode};

/// Grid spacing of the seed layout, in Ontoloom canvas units.
const X_STEP: f64 = 180.0;
const Y_STEP: f64 = 120.0;
/// Vertical gap separating one band (level/kind group) from the next.
const BAND_GAP: f64 = 240.0;

/// Serialize `graph` as a single-line Ontoloom wire JSON document.
/// `name` becomes the graph's human title (drives Ontoloom's export
/// file name); it may be empty.
pub fn ontoloom_wire(graph: &Graph, name: &str) -> String {
    let positions = seed_layout(graph);

    let nodes: Vec<Json> = graph
        .nodes()
        .map(|n| {
            let (x, y) = positions[n.id.as_str()];
            Json::obj([
                ("id", Json::str(n.id.clone())),
                (
                    "labels",
                    Json::Array(labels(n).into_iter().map(Json::Str).collect()),
                ),
                ("caption", Json::str(n.name.clone())),
                ("properties", Json::Object(n.props.clone())),
                ("x", Json::F64(x)),
                ("y", Json::F64(y)),
            ])
        })
        .collect();

    let node_ids: BTreeSet<&str> = graph.nodes().map(|n| n.id.as_str()).collect();
    let mut seen: BTreeMap<String, u64> = BTreeMap::new();
    let mut relationships: Vec<Json> = Vec::new();
    for e in graph.edges() {
        if !node_ids.contains(e.from.as_str()) || !node_ids.contains(e.to.as_str()) {
            continue; // Ontoloom hard-rejects dangling endpoints.
        }
        let base = format!("{}__{}__{}", e.from, e.kind, e.to);
        let n = seen.entry(base.clone()).or_insert(0);
        *n += 1;
        let id = if *n == 1 {
            base
        } else {
            format!("{base}__{n}")
        };
        relationships.push(Json::obj([
            ("id", Json::Str(id)),
            ("type", Json::str(e.kind)),
            ("from", Json::str(e.from.clone())),
            ("to", Json::str(e.to.clone())),
            ("properties", Json::Object(e.props.clone())),
        ]));
    }

    Json::obj([
        ("name", Json::str(name)),
        ("nodes", Json::Array(nodes)),
        ("relationships", Json::Array(relationships)),
    ])
    .to_line()
}

/// Ontoloom labels for a node: its kind first, then the Title-cased value of
/// each grouping prop the extractors emit (`level`, `domain`, `archetype`,
/// `layer`) when present and non-empty, de-duplicated in that order.
fn labels(n: &GraphNode) -> Vec<String> {
    let mut out = vec![n.kind.to_string()];
    for key in ["level", "domain", "archetype", "layer"] {
        if let Some(Json::Str(value)) = n.props.get(key) {
            if value.is_empty() {
                continue;
            }
            let label = title_case(value);
            if !out.contains(&label) {
                out.push(label);
            }
        }
    }
    out
}

/// Uppercase the first character (Unicode-aware), leave the rest untouched:
/// `domain` → `Domain`, `Ordering.API` → `Ordering.API`.
fn title_case(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        Some(first) => first.to_uppercase().chain(chars).collect(),
        None => String::new(),
    }
}

/// Band sort key for the seed layout: hierarchy levels first in their natural
/// top-down order, then any other `level` value, then plain kinds.
fn band(n: &GraphNode) -> (u8, String) {
    if let Some(Json::Str(level)) = n.props.get("level") {
        let rank = match level.as_str() {
            "domain" => 0,
            "unit" => 1,
            "file" => 2,
            "symbol" => 3,
            _ => 4,
        };
        return (rank, level.clone());
    }
    (5, n.kind.to_string())
}

/// Deterministic seed positions: one horizontal band per level/kind group
/// (domains on top, symbols at the bottom), a near-square grid inside each
/// band. Purely a readable starting arrangement — not a layout algorithm.
fn seed_layout(graph: &Graph) -> BTreeMap<&str, (f64, f64)> {
    let mut bands: BTreeMap<(u8, String), Vec<&str>> = BTreeMap::new();
    for n in graph.nodes() {
        bands.entry(band(n)).or_default().push(n.id.as_str());
    }

    let mut positions = BTreeMap::new();
    let mut band_top = 0.0_f64;
    for ids in bands.values() {
        // Near-square grid: ceil(sqrt(n)) columns.
        let cols = ((ids.len() as f64).sqrt().ceil() as usize).max(1);
        let mut rows = 0;
        for (i, id) in ids.iter().enumerate() {
            let (col, row) = (i % cols, i / cols);
            positions.insert(*id, (col as f64 * X_STEP, band_top + row as f64 * Y_STEP));
            rows = row + 1;
        }
        band_top += rows as f64 * Y_STEP + BAND_GAP;
    }
    positions
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::extract::{Extractor, HierarchyExtractor};
    use crate::ir::ontology::{edge, node as ont};

    /// A synthetic already-extracted hierarchy-shaped view graph.
    fn hierarchy_view() -> Graph {
        let mut g = Graph::new();
        g.upsert_node(
            "domain::Order",
            ont::MODULE,
            "Order",
            vec![
                ("level", Json::str("domain")),
                ("domain", Json::str("Order")),
                ("file_count", Json::U64(2)),
            ],
        );
        g.upsert_node(
            "file::src/Order.cs",
            ont::FILE,
            "Order.cs",
            vec![
                ("level", Json::str("file")),
                ("domain", Json::str("Order")),
                ("layer", Json::str("Domain")),
                ("path", Json::str("src/Order.cs")),
            ],
        );
        g.upsert_node(
            "sym::OrdersController",
            ont::TYPE,
            "OrdersController",
            vec![
                ("level", Json::str("symbol")),
                ("domain", Json::str("Order")),
                ("archetype", Json::str("Controller")),
                ("line", Json::U64(12)),
            ],
        );
        g.add_edge(
            "domain::Order",
            edge::CONTAINS,
            "file::src/Order.cs",
            vec![],
        );
        g.add_edge(
            "file::src/Order.cs",
            edge::CONTAINS,
            "sym::OrdersController",
            vec![],
        );
        g
    }

    #[test]
    fn nodes_map_to_ontoloom_shape_with_grouping_labels() {
        let wire = ontoloom_wire(&hierarchy_view(), "test");
        // Domain node: kind label + Title-cased level + domain value.
        assert!(
            wire.contains(
                r#""caption":"Order","id":"domain::Order","labels":["Module","Domain","Order"]"#
            ),
            "domain node shape wrong:\n{wire}"
        );
        // Symbol node: kind + level + domain + archetype.
        assert!(
            wire.contains(
                r#""caption":"OrdersController","id":"sym::OrdersController","labels":["Type","Symbol","Order","Controller"]"#
            ),
            "symbol node labels wrong:\n{wire}"
        );
        // File node: level "file" collapses into the kind label; layer kept.
        assert!(
            wire.contains(
                r#""caption":"Order.cs","id":"file::src/Order.cs","labels":["File","Order","Domain"]"#
            ),
            "file node labels wrong:\n{wire}"
        );
        // Properties pass through untouched.
        assert!(wire.contains(r#""file_count":2"#), "props dropped:\n{wire}");
        assert!(wire.contains(r#""line":12"#), "props dropped:\n{wire}");
    }

    #[test]
    fn label_dedup_keeps_kind_first_and_unique() {
        // level "file" Title-cases to "File" == the kind label; must not repeat.
        let mut g = Graph::new();
        g.upsert_node(
            "file::a",
            ont::FILE,
            "a",
            vec![("level", Json::str("file"))],
        );
        let wire = ontoloom_wire(&g, "");
        assert!(
            wire.contains(r#""labels":["File"]"#),
            "duplicate label not collapsed:\n{wire}"
        );
    }

    #[test]
    fn edges_map_to_relationships_with_type_from_to() {
        let wire = ontoloom_wire(&hierarchy_view(), "test");
        assert!(
            wire.contains(
                r#"{"from":"domain::Order","id":"domain::Order__CONTAINS__file::src/Order.cs","properties":{},"to":"file::src/Order.cs","type":"CONTAINS"}"#
            ),
            "relationship shape wrong:\n{wire}"
        );
    }

    #[test]
    fn duplicate_endpoint_edges_get_unique_relationship_ids() {
        let mut g = Graph::new();
        g.upsert_node("a", ont::MODULE, "a", vec![]);
        g.upsert_node("b", ont::MODULE, "b", vec![]);
        // Same endpoints, different props: two distinct base-graph edges.
        g.add_edge("a", edge::DEPENDS_ON, "b", vec![("count", Json::U64(1))]);
        g.add_edge("a", edge::DEPENDS_ON, "b", vec![("count", Json::U64(2))]);
        let wire = ontoloom_wire(&g, "");
        assert!(wire.contains(r#""id":"a__DEPENDS_ON__b""#), "{wire}");
        assert!(wire.contains(r#""id":"a__DEPENDS_ON__b__2""#), "{wire}");
    }

    #[test]
    fn dangling_edges_are_dropped_so_ontoloom_accepts_the_graph() {
        let mut g = Graph::new();
        g.upsert_node("a", ont::MODULE, "a", vec![]);
        g.add_edge("a", edge::DEPENDS_ON, "ghost", vec![]);
        let wire = ontoloom_wire(&g, "");
        assert!(
            wire.contains(r#""relationships":[]"#),
            "dangling edge must be dropped:\n{wire}"
        );
    }

    #[test]
    fn seed_layout_spreads_nodes_instead_of_stacking_them() {
        let view = hierarchy_view();
        let wire = ontoloom_wire(&view, "test");
        let positions = seed_layout(&view);
        let unique: BTreeSet<String> = positions
            .values()
            .map(|(x, y)| format!("{x},{y}"))
            .collect();
        assert_eq!(unique.len(), positions.len(), "positions collide: {wire}");
        // Levels are banded top-down: domain above file above symbol.
        let y = |id: &str| positions[id].1;
        assert!(y("domain::Order") < y("file::src/Order.cs"));
        assert!(y("file::src/Order.cs") < y("sym::OrdersController"));
    }

    /// Add a File node (with `path`) plus one declared symbol to `g`.
    fn base_file_with_symbol(g: &mut Graph, path: &str, kind: &'static str, sym: &str, line: u64) {
        let file_id = format!("base-file::{path}");
        g.upsert_node(
            file_id.clone(),
            ont::FILE,
            path.rsplit('/').next().unwrap().to_string(),
            vec![("path", Json::str(path))],
        );
        let sym_id = format!("sym::{sym}");
        g.upsert_node(sym_id.clone(), kind, sym, vec![("line", Json::U64(line))]);
        g.add_edge(file_id, edge::DECLARES, sym_id, vec![]);
    }

    #[test]
    fn real_hierarchy_extraction_exports_and_is_deterministic() {
        // Base graph → hierarchy extractor → Ontoloom wire, end to end. Two
        // dependency-less files stay two structural domains (a 2-symbol repo
        // can never merge under the anti-collapse cap); the wire format is
        // what this test pins down.
        let mut base = Graph::new();
        base_file_with_symbol(
            &mut base,
            "src/Ordering.API/OrdersController.cs",
            ont::TYPE,
            "OrdersController",
            12,
        );
        base_file_with_symbol(
            &mut base,
            "src/Ordering.Domain/Order.cs",
            ont::TYPE,
            "Order",
            5,
        );
        let view = HierarchyExtractor.extract(&base);
        let a = ontoloom_wire(&view, "mini (hierarchy)");
        let b = ontoloom_wire(&view, "mini (hierarchy)");
        assert_eq!(a, b, "export must be byte-stable");
        assert!(a.contains(r#""name":"mini (hierarchy)""#));
        // The derived symbol node carries level+domain+archetype labels.
        assert!(
            a.contains(r#""caption":"OrdersController""#),
            "caption missing:\n{a}"
        );
        assert!(
            a.contains(r#""labels":["Type","Symbol","Ordering.API","Controller"]"#),
            "derived labels missing:\n{a}"
        );
        // Unit → File containment survives as a typed relationship.
        assert!(
            a.contains(r#""type":"CONTAINS""#),
            "CONTAINS relationship missing:\n{a}"
        );
    }
}
