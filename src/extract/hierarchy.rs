//! The hierarchy extractor: the **hierarchical emit** — ONE unified graph
//! fusing the domain, layer, and archetype ontologies into a single labeled
//! hierarchy the UI can lazily expand and Ontoloom can ingest directly.
//!
//! Nothing here is re-derived: the domain clustering comes from
//! [`assign_domains`], the unit/layer placement from [`assign_layers`], and
//! per-symbol archetypes from [`archetypes::classify`] — the exact same
//! single-source-of-truth assignments the `domains`, `layers`, and
//! `archetypes` views emit. This pass only *joins* them into four node
//! levels, every node carrying every grouping so the UI can pivot without a
//! second query:
//!
//! - **Domain** (`level: "domain"`, kind [`Module`]) — one node per bounded
//!   context, with `domain`/`label`/`file_count`/`symbol_count`/`kind`
//!   (`business` for clustered code, `infrastructure` for the named groups —
//!   Build & Tooling, Documentation, Generated, Repo root — which also carry
//!   a `reason`: `scaffold`/`docs`/`generated`/`root`).
//! - **Unit** (`level: "unit"`, kind [`Module`]) — one node per top project
//!   segment, with its `layer` and `file_count`/`symbol_count`.
//! - **File** (`level: "file"`, kind [`File`]) — every file with a `path`,
//!   carrying its `domain` (**every** file has one: business domain or named
//!   infrastructure group — zero ungrouped), `unit`, `layer`, and
//!   `symbol_count`.
//! - **Symbol** (`level: "symbol"`, base kind kept) — every non-File node
//!   owned by a file, carrying its `archetype`, `domain`, `unit`, `file`
//!   (path), and `line`.
//!
//! Edges:
//!
//! - `CONTAINS`: Domain→File, Unit→File, File→Symbol. A file deliberately has
//!   **two** containment parents — its domain and its unit — so one graph
//!   serves both the expand-by-domain and the expand-by-project pivot.
//! - `DEPENDS_ON`: counted inter-domain and inter-unit edges, projected from
//!   cross-group [`DEPENDS`]-family base edges by the assignment passes.
//!
//! Pure and deterministic: a function of the base graph only, walking the
//! `BTreeMap`-ordered iterators and writing through the sorted,
//! de-duplicating [`Graph`] API — the same base graph always linearizes
//! byte-identically. The base graph is never mutated.
//!
//! [`Module`]: crate::ir::ontology::node::MODULE
//! [`File`]: crate::ir::ontology::node::FILE
//! [`DEPENDS`]: crate::ir::ontology::relation::DEPENDS
//! [`archetypes::classify`]: super::archetypes::classify

use std::collections::BTreeMap;

use crate::core::json::Json;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont, parent_relation, relation};

use super::archetypes;
use super::domains::assign_domains;
use super::layers::assign_layers;
use super::Extractor;

/// Property key marking a node as belonging to the hierarchy view.
const VIEW: &str = "hierarchy";

/// Fuse domains + layers + archetypes into the one lazily-expandable
/// Domain/Unit/File/Symbol hierarchy.
pub struct HierarchyExtractor;

impl Extractor for HierarchyExtractor {
    fn name(&self) -> &'static str {
        "hierarchy"
    }

    fn extract(&self, graph: &Graph) -> Graph {
        let domains = assign_domains(graph);
        let layers = assign_layers(graph);
        let mut out = Graph::new();

        // --- level: domain --------------------------------------------------
        for (name, info) in &domains.domains {
            let mut props = vec![
                ("view", Json::str(VIEW)),
                ("level", Json::str("domain")),
                ("domain", Json::str(name.clone())),
                ("label", Json::str(info.label.clone())),
                ("file_count", Json::U64(info.file_count)),
                ("symbol_count", Json::U64(info.symbol_count)),
                ("kind", Json::str(info.kind)),
            ];
            if let Some(reason) = info.reason {
                props.push(("reason", Json::str(reason)));
            }
            out.upsert_node(format!("domain::{name}"), ont::MODULE, name.clone(), props);
        }

        // --- level: unit ----------------------------------------------------
        for (unit, layer) in &layers.unit_layer {
            out.upsert_node(
                format!("unit::{unit}"),
                ont::MODULE,
                unit.clone(),
                vec![
                    ("view", Json::str(VIEW)),
                    ("level", Json::str("unit")),
                    ("unit", Json::str(unit.clone())),
                    ("layer", Json::str(layer.clone())),
                    (
                        "file_count",
                        Json::U64(layers.unit_files.get(unit).copied().unwrap_or(0)),
                    ),
                    (
                        "symbol_count",
                        Json::U64(layers.unit_symbols.get(unit).copied().unwrap_or(0)),
                    ),
                ],
            );
        }

        // Symbol → owning-File resolution: the same CONTAINMENT-parent walk
        // the assignment passes use (File parents preferred, first-seen wins
        // among equals — edges iterate in stable signature order).
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
        // Bounded walk to the owning File: containment chains are shallow;
        // the bound only guards against a malformed cyclic containment.
        fn resolve_file<'g>(
            kind_of: &BTreeMap<&'g str, &'static str>,
            parent: &BTreeMap<&'g str, &'g str>,
            mut id: &'g str,
        ) -> Option<&'g str> {
            for _ in 0..64 {
                if kind_of.get(id).copied() == Some(ont::FILE) {
                    return Some(id);
                }
                id = parent.get(id)?;
            }
            None
        }

        // File id → path, for every File node carrying a `path` prop (the
        // same file set `assign_layers` placed into units).
        let mut path_of_file: BTreeMap<&str, &str> = BTreeMap::new();
        for n in graph.nodes().filter(|n| n.kind == ont::FILE) {
            if let Some(Json::Str(path)) = n.props.get("path") {
                path_of_file.insert(n.id.as_str(), path.as_str());
            }
        }

        // --- level: symbol (+ per-file symbol tallies) -----------------------
        let mut file_symbols: BTreeMap<&str, u64> = BTreeMap::new();
        for n in graph.nodes() {
            if n.kind == ont::FILE {
                continue; // files are containers, not symbols.
            }
            let Some(file) = resolve_file(&kind_of, &parent, n.id.as_str()) else {
                continue;
            };
            let (Some(unit), Some(path)) =
                (layers.file_unit.get(file), path_of_file.get(file).copied())
            else {
                continue;
            };
            *file_symbols.entry(file).or_default() += 1;
            let mut props = vec![
                ("view", Json::str(VIEW)),
                ("level", Json::str("symbol")),
                ("symbol_kind", Json::str(n.kind)),
                ("archetype", Json::str(archetypes::classify(n))),
                ("unit", Json::str(unit.clone())),
                ("file", Json::str(path)),
            ];
            if let Some(domain) = domains.file_domain.get(file) {
                props.push(("domain", Json::str(domain.clone())));
            }
            if let Some(line) = n.props.get("line") {
                props.push(("line", line.clone()));
            }
            out.upsert_node(n.id.clone(), n.kind, n.name.clone(), props);
            out.add_edge(
                format!("file::{path}"),
                edge::CONTAINS,
                n.id.clone(),
                vec![],
            );
        }

        // --- level: file (with its two containment parents) ------------------
        for (file, unit) in &layers.file_unit {
            let Some(path) = path_of_file.get(file.as_str()).copied() else {
                continue;
            };
            let layer = layers.unit_layer.get(unit).cloned().unwrap_or_default();
            let mut props = vec![
                ("view", Json::str(VIEW)),
                ("level", Json::str("file")),
                ("path", Json::str(path)),
                ("unit", Json::str(unit.clone())),
                ("layer", Json::str(layer)),
                (
                    "symbol_count",
                    Json::U64(file_symbols.get(file.as_str()).copied().unwrap_or(0)),
                ),
            ];
            if let Some(domain) = domains.file_domain.get(file) {
                props.push(("domain", Json::str(domain.clone())));
                out.add_edge(
                    format!("domain::{domain}"),
                    edge::CONTAINS,
                    format!("file::{path}"),
                    vec![],
                );
            }
            out.upsert_node(
                format!("file::{path}"),
                ont::FILE,
                path.rsplit(['/', '\\']).next().unwrap_or(path),
                props,
            );
            out.add_edge(
                format!("unit::{unit}"),
                edge::CONTAINS,
                format!("file::{path}"),
                vec![],
            );
        }

        // --- DEPENDS_ON projections ------------------------------------------
        for ((from, to), count) in &domains.domain_deps {
            out.add_edge(
                format!("domain::{from}"),
                edge::DEPENDS_ON,
                format!("domain::{to}"),
                vec![("count", Json::U64(*count))],
            );
        }
        for ((from, to), count) in &layers.unit_deps {
            out.add_edge(
                format!("unit::{from}"),
                edge::DEPENDS_ON,
                format!("unit::{to}"),
                vec![("count", Json::U64(*count))],
            );
        }

        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Add a File node with a `path` prop; returns its id.
    fn file(g: &mut Graph, path: &str) -> String {
        let name = path.rsplit('/').next().unwrap().to_string();
        let id = format!("base-file::{path}");
        g.upsert_node(id.clone(), ont::FILE, name, vec![("path", Json::str(path))]);
        id
    }

    /// Add a symbol declared by `file_id`, with a source line; returns its id.
    fn sym(g: &mut Graph, file_id: &str, kind: &'static str, name: &str, line: u64) -> String {
        let id = format!("sym::{name}");
        g.upsert_node(id.clone(), kind, name, vec![("line", Json::U64(line))]);
        g.add_edge(file_id.to_string(), edge::DECLARES, id.clone(), vec![]);
        id
    }

    /// A hand-built eShop-shaped base graph spanning two structural domains
    /// (Ordering = `Ordering.API`+`Ordering.Domain`, coupled by real
    /// dependency mass; `Basket.API` standing alone), with one cross-domain,
    /// cross-unit dependency. Units: `Ordering.API` → Presentation by
    /// archetype; `Ordering.Domain` → Domain by name hint.
    fn sample_base() -> Graph {
        let mut g = Graph::new();

        // Ordering context, two files across two units, heavily coupled.
        let f = file(&mut g, "src/Ordering.API/OrdersController.cs");
        let controller = sym(&mut g, &f, ont::TYPE, "OrdersController", 12);
        let create = sym(&mut g, &f, ont::FUNCTION, "CreateOrder", 30);
        let f = file(&mut g, "src/Ordering.Domain/Order.cs");
        let order = sym(&mut g, &f, ont::TYPE, "Order", 5);
        let order_item = sym(&mut g, &f, ont::TYPE, "OrderItem", 40);
        sym(&mut g, &f, ont::TYPE, "OrderStatus", 80);
        g.add_edge(controller.clone(), edge::USES_TYPE, order, vec![]);
        g.add_edge(create, edge::USES_TYPE, order_item, vec![]);

        // Basket context, two files in one unit, internally coupled. Carries
        // enough symbol mass that the merged Ordering community (5 symbols)
        // stays under the anti-collapse cap of the structural clustering.
        let f = file(&mut g, "src/Basket.API/BasketService.cs");
        let bsvc = sym(&mut g, &f, ont::TYPE, "BasketService", 9);
        let basket_item = sym(&mut g, &f, ont::TYPE, "BasketItem", 55);
        sym(&mut g, &f, ont::TYPE, "BasketRepository", 71);
        let f = file(&mut g, "src/Basket.API/BasketCheckout.cs");
        let checkout = sym(&mut g, &f, ont::TYPE, "BasketCheckout", 7);
        sym(&mut g, &f, ont::FUNCTION, "GetBasketAsync", 21);
        sym(&mut g, &f, ont::FUNCTION, "UpdateBasketAsync", 33);
        g.add_edge(bsvc, edge::USES_TYPE, checkout, vec![]);

        // Cross-domain AND cross-unit dependency: Ordering.API → Basket.API.
        g.add_edge(controller, edge::USES_TYPE, basket_item, vec![]);

        g
    }

    fn node_prop<'a>(g: &'a Graph, id: &str, key: &str) -> &'a Json {
        g.nodes()
            .find(|n| n.id == id)
            .unwrap_or_else(|| panic!("missing node {id}"))
            .props
            .get(key)
            .unwrap_or_else(|| panic!("node {id} has no `{key}` prop"))
    }

    fn has_contains(g: &Graph, from: &str, to: &str) -> bool {
        g.edges()
            .any(|e| e.kind == edge::CONTAINS && e.from == from && e.to == to)
    }

    #[test]
    fn all_four_levels_are_present_with_correct_labels() {
        let derived = HierarchyExtractor.extract(&sample_base());

        // Domain level: both bounded contexts, with structural labels.
        for (id, label) in [
            ("domain::Ordering", "Ordering"),
            ("domain::Basket.API", "Basket.API"),
        ] {
            assert_eq!(node_prop(&derived, id, "level"), &Json::str("domain"));
            assert_eq!(node_prop(&derived, id, "label"), &Json::str(label));
            assert_eq!(node_prop(&derived, id, "view"), &Json::str(VIEW));
        }
        assert_eq!(
            node_prop(&derived, "domain::Ordering", "file_count"),
            &Json::U64(2)
        );
        assert_eq!(
            node_prop(&derived, "domain::Ordering", "symbol_count"),
            &Json::U64(5)
        );

        // Unit level: three units, each carrying its layer.
        for (id, layer) in [
            ("unit::Ordering.API", "Presentation"), // Controller archetype vote
            ("unit::Ordering.Domain", "Domain"),    // `.Domain` name hint
        ] {
            assert_eq!(node_prop(&derived, id, "level"), &Json::str("unit"));
            assert_eq!(node_prop(&derived, id, "layer"), &Json::str(layer));
        }
        assert_eq!(
            node_prop(&derived, "unit::Basket.API", "level"),
            &Json::str("unit")
        );

        // File level: present with a path.
        assert_eq!(
            node_prop(&derived, "file::src/Ordering.Domain/Order.cs", "level"),
            &Json::str("file")
        );

        // Symbol level: present, carried over from the base graph.
        assert_eq!(
            node_prop(&derived, "sym::Order", "level"),
            &Json::str("symbol")
        );
    }

    #[test]
    fn symbols_carry_their_archetype_and_full_lineage() {
        let derived = HierarchyExtractor.extract(&sample_base());

        // Archetypes from the shared rule table.
        assert_eq!(
            node_prop(&derived, "sym::OrdersController", "archetype"),
            &Json::str("Controller")
        );
        assert_eq!(
            node_prop(&derived, "sym::BasketService", "archetype"),
            &Json::str("Service")
        );

        // Full lineage on one symbol: domain, unit, file, line, kind.
        let id = "sym::OrdersController";
        assert_eq!(node_prop(&derived, id, "domain"), &Json::str("Ordering"));
        assert_eq!(node_prop(&derived, id, "unit"), &Json::str("Ordering.API"));
        assert_eq!(
            node_prop(&derived, id, "file"),
            &Json::str("src/Ordering.API/OrdersController.cs")
        );
        assert_eq!(node_prop(&derived, id, "line"), &Json::U64(12));
        assert_eq!(
            node_prop(&derived, id, "symbol_kind"),
            &Json::str(ont::TYPE)
        );
    }

    #[test]
    fn files_carry_domain_unit_and_layer() {
        let derived = HierarchyExtractor.extract(&sample_base());
        let id = "file::src/Ordering.Domain/Order.cs";
        assert_eq!(node_prop(&derived, id, "domain"), &Json::str("Ordering"));
        assert_eq!(
            node_prop(&derived, id, "unit"),
            &Json::str("Ordering.Domain")
        );
        assert_eq!(node_prop(&derived, id, "layer"), &Json::str("Domain"));
        assert_eq!(node_prop(&derived, id, "symbol_count"), &Json::U64(3));
        assert_eq!(
            node_prop(&derived, id, "path"),
            &Json::str("src/Ordering.Domain/Order.cs")
        );
    }

    #[test]
    fn containment_edges_span_all_three_links() {
        let derived = HierarchyExtractor.extract(&sample_base());
        let file_id = "file::src/Ordering.Domain/Order.cs";
        // Domain→File and Unit→File: the deliberate double parent.
        assert!(has_contains(&derived, "domain::Ordering", file_id));
        assert!(has_contains(&derived, "unit::Ordering.Domain", file_id));
        // File→Symbol.
        assert!(has_contains(&derived, file_id, "sym::Order"));
        assert!(has_contains(
            &derived,
            "file::src/Ordering.API/OrdersController.cs",
            "sym::OrdersController"
        ));
    }

    #[test]
    fn cross_group_deps_project_to_counted_edges() {
        let derived = HierarchyExtractor.extract(&sample_base());
        let dep = |from: &str, to: &str| {
            derived
                .edges()
                .find(|e| e.kind == edge::DEPENDS_ON && e.from == from && e.to == to)
                .unwrap_or_else(|| panic!("missing DEPENDS_ON {from} -> {to}"))
        };
        assert_eq!(
            dep("domain::Ordering", "domain::Basket.API")
                .props
                .get("count"),
            Some(&Json::U64(1))
        );
        assert_eq!(
            dep("unit::Ordering.API", "unit::Basket.API")
                .props
                .get("count"),
            Some(&Json::U64(1))
        );
        // No self-loops at either grain.
        assert!(!derived
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.from == e.to));
    }

    #[test]
    fn deterministic_across_runs_and_base_untouched() {
        let base = sample_base();
        let before = base.to_jsonl();
        let a = HierarchyExtractor.extract(&base).to_jsonl();
        let b = HierarchyExtractor.extract(&base).to_jsonl();
        assert_eq!(a, b, "output must be byte-identical across runs");
        assert!(!a.is_empty());
        assert_eq!(base.to_jsonl(), before, "base graph must not change");
    }
}
