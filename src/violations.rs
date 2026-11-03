//! The full layer-violations report: `trailtracker violations`.
//!
//! The layers view ([`crate::extract::layers`]) flags dependency-direction
//! violations, but its derived graph aggregates them into `layer::X →
//! layer::Y` edges with a count — the UNIT identity is lost, so a report of
//! "Domain → Application ×95" names no perpetrators. `arch-verify` names
//! files, but requires a hand-authored spec. This module is the spec-free
//! middle: every layer-violating dependency at **unit grain** — from-unit
//! (name, layer) → to-unit (name, layer), edge count, and bounded file-level
//! example edges — ranked worst-first, with totals per layer pair.
//!
//! The rule is the standard clean-architecture direction rule the layers
//! extractor already applies: ranks Domain(1) < Application(2) <
//! Infrastructure(3) < Presentation(4); an edge from a more-inner layer to a
//! more-outer one violates; Test and Shared are unranked and exempt. Unit and
//! layer placement come from [`assign_layers`] — the same single source of
//! truth the layers view and `arch-verify` consume, never a re-derivation.
//! The evidence walk mirrors `arch-verify`'s (containment walk to the owning
//! File, complete counts), minus the spec, and names both endpoint SYMBOLS
//! (`path:symbol -[KIND]-> path:symbol`), not just files.
//!
//! **Both dependency families count.** A violating edge is any
//! [`DEPENDS`]-family edge (CALLS, USES_TYPE, IMPORTS, DEPENDS_ON, FLOWS_TO,
//! DATA_DEP) *or* [`SPECIALIZES`]-family edge (EXTENDS, IMPLEMENTS) that
//! crosses layers outward: a Domain-layer class that EXTENDS a
//! Presentation-layer class is coupled to that outer layer exactly as hard
//! as one that calls it — harder, in fact (inheritance is the strongest
//! coupling there is). Earlier versions counted only the DEPENDS family and
//! silently omitted inheritance edges; that undercount is fixed.
//!
//! [`DEPENDS`]: crate::ir::ontology::relation::DEPENDS
//! [`SPECIALIZES`]: crate::ir::ontology::relation::SPECIALIZES
//!
//! Pure and deterministic: [`violations_report`] is a function of the base
//! graph alone; iteration follows the graph's stable `BTreeMap` order and
//! all ranking ties break lexicographically, so output is byte-stable.

use std::collections::BTreeMap;

use crate::core::json::Json;
use crate::extract::layers::assign_layers;
use crate::graph::Graph;
use crate::ir::ontology::{node as ont, parent_relation, relation};

/// Schema id of the `--json` report.
pub const REPORT_FORMAT: &str = "trailtracker.violations/v1";

/// One-line statement of the rule, shared by the human and JSON renderings.
const RULE: &str = "dependencies must point inward (Domain < Application < Infrastructure < \
                    Presentation; Test and Shared are exempt); dependency (CALLS, IMPORTS, \
                    USES_TYPE, ...) and inheritance (EXTENDS, IMPLEMENTS) edges both count";

/// Does an edge of this kind count toward the violation scan? Both outbound
/// coupling families do: [`relation::DEPENDS`] and [`relation::SPECIALIZES`].
fn counted_family(edge_kind: &str) -> bool {
    matches!(
        parent_relation(edge_kind),
        Some(relation::DEPENDS | relation::SPECIALIZES)
    )
}

/// Onion rank of a layer name, innermost = 1. `None` for Test/Shared (and
/// anything unknown), which sit outside the direction rule. Kept consistent
/// with the layers extractor's semantics by a unit test that cross-checks a
/// fixture against the derived layers view.
fn rank(layer: &str) -> Option<u8> {
    match layer {
        "Domain" => Some(1),
        "Application" => Some(2),
        "Infrastructure" => Some(3),
        "Presentation" => Some(4),
        _ => None,
    }
}

/// Is a `from`-layer → `to`-layer dependency a direction violation?
/// Violation iff both layers are ranked and the source is more inner.
pub fn is_violation(from_layer: &str, to_layer: &str) -> bool {
    matches!((rank(from_layer), rank(to_layer)), (Some(f), Some(t)) if f < t)
}

/// One violating unit-pair: every DEPENDS- or SPECIALIZES-family edge from
/// `from_unit` to `to_unit` whose layer direction points outward.
#[derive(Clone, Debug)]
pub struct UnitViolation {
    pub from_unit: String,
    pub from_layer: String,
    pub to_unit: String,
    pub to_layer: String,
    /// Complete count of violating edges between the two units.
    pub count: u64,
    /// Symbol-grain `fromPath:fromSymbol -[KIND]-> toPath:toSymbol` evidence,
    /// deterministic order, de-duplicated. Complete by default; an explicit
    /// `--examples N` cap bounds the list (the count stays complete).
    pub examples: Vec<String>,
}

/// Totals for one violating layer pair, aggregated over its unit pairs.
#[derive(Clone, Debug)]
pub struct LayerPairTotal {
    pub from_layer: String,
    pub to_layer: String,
    /// Total violating edge mass across the pair's unit pairs.
    pub edges: u64,
    /// How many distinct unit pairs contribute.
    pub unit_pairs: u64,
}

/// The full report: violating unit pairs ranked worst-first (edge count
/// descending, ties by unit names), plus the total edge mass.
#[derive(Clone, Debug, Default)]
pub struct ViolationsReport {
    pub violations: Vec<UnitViolation>,
    pub total_edges: u64,
}

/// Bounded containment walk to the owning File node — structurally identical
/// to the walk in `arch.rs` and the layers extractor, on purpose.
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

/// Compute the full layer-violations report for an analyzed graph, with
/// complete (uncapped) evidence. Pure and deterministic: same graph, same
/// report.
pub fn violations_report(graph: &Graph) -> ViolationsReport {
    violations_report_capped(graph, None)
}

/// [`violations_report`] with an optional per-unit-pair evidence cap
/// (`--examples N`). `None` = every named edge. Counts are always complete;
/// the cap bounds only the example list.
pub fn violations_report_capped(graph: &Graph, examples_cap: Option<usize>) -> ViolationsReport {
    let assignment = assign_layers(graph);

    // Node kinds + containment parents (preferring a File parent), for the
    // walk from any symbol to its owning file.
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

    // File node id → path, for the example evidence.
    let mut path_of_file: BTreeMap<&str, &str> = BTreeMap::new();
    for n in graph.nodes().filter(|n| n.kind == ont::FILE) {
        if let Some(Json::Str(path)) = n.props.get("path") {
            path_of_file.insert(n.id.as_str(), path.as_str());
        }
    }

    // Node id → display name, for symbol-grain evidence.
    let name_of: BTreeMap<&str, &str> = graph
        .nodes()
        .map(|n| (n.id.as_str(), n.name.as_str()))
        .collect();

    // Tally every DEPENDS- or SPECIALIZES-family edge that crosses a unit
    // boundary in a violating layer direction: complete counts, complete
    // (or explicitly capped) symbol-grain examples.
    let mut pairs: BTreeMap<(&str, &str), (u64, Vec<String>)> = BTreeMap::new();
    for e in graph.edges() {
        if !counted_family(e.kind) {
            continue;
        }
        let (Some(from_file), Some(to_file)) = (
            resolve_file(&kind_of, &parent, e.from.as_str()),
            resolve_file(&kind_of, &parent, e.to.as_str()),
        ) else {
            continue;
        };
        let (Some(from_unit), Some(to_unit)) = (
            assignment.file_unit.get(from_file),
            assignment.file_unit.get(to_file),
        ) else {
            continue;
        };
        if from_unit == to_unit {
            continue;
        }
        let (Some(from_layer), Some(to_layer)) = (
            assignment.unit_layer.get(from_unit),
            assignment.unit_layer.get(to_unit),
        ) else {
            continue;
        };
        if !is_violation(from_layer, to_layer) {
            continue;
        }
        let entry = pairs
            .entry((from_unit.as_str(), to_unit.as_str()))
            .or_default();
        entry.0 += 1;
        if examples_cap.is_none_or(|cap| entry.1.len() < cap) {
            let (from_path, to_path) = (
                path_of_file.get(from_file).copied().unwrap_or(from_file),
                path_of_file.get(to_file).copied().unwrap_or(to_file),
            );
            let (from_sym, to_sym) = (
                name_of
                    .get(e.from.as_str())
                    .copied()
                    .unwrap_or(e.from.as_str()),
                name_of.get(e.to.as_str()).copied().unwrap_or(e.to.as_str()),
            );
            let example = format!("{from_path}:{from_sym} -[{}]-> {to_path}:{to_sym}", e.kind);
            if !entry.1.contains(&example) {
                entry.1.push(example);
            }
        }
    }

    let mut violations: Vec<UnitViolation> = pairs
        .into_iter()
        .map(|((from_unit, to_unit), (count, examples))| UnitViolation {
            from_unit: from_unit.to_string(),
            from_layer: assignment.unit_layer[from_unit].clone(),
            to_unit: to_unit.to_string(),
            to_layer: assignment.unit_layer[to_unit].clone(),
            count,
            examples,
        })
        .collect();
    // Worst-first: edge count descending, ties by (from_unit, to_unit).
    violations.sort_by(|a, b| {
        b.count
            .cmp(&a.count)
            .then_with(|| (&a.from_unit, &a.to_unit).cmp(&(&b.from_unit, &b.to_unit)))
    });
    let total_edges = violations.iter().map(|v| v.count).sum();
    ViolationsReport {
        violations,
        total_edges,
    }
}

impl ViolationsReport {
    /// Totals per violating layer pair, worst-first (edge mass descending,
    /// ties by layer names).
    pub fn layer_pairs(&self) -> Vec<LayerPairTotal> {
        let mut totals: BTreeMap<(&str, &str), (u64, u64)> = BTreeMap::new();
        for v in &self.violations {
            let entry = totals
                .entry((v.from_layer.as_str(), v.to_layer.as_str()))
                .or_default();
            entry.0 += v.count;
            entry.1 += 1;
        }
        let mut pairs: Vec<LayerPairTotal> = totals
            .into_iter()
            .map(|((from, to), (edges, unit_pairs))| LayerPairTotal {
                from_layer: from.to_string(),
                to_layer: to.to_string(),
                edges,
                unit_pairs,
            })
            .collect();
        pairs.sort_by(|a, b| {
            b.edges
                .cmp(&a.edges)
                .then_with(|| (&a.from_layer, &a.to_layer).cmp(&(&b.from_layer, &b.to_layer)))
        });
        pairs
    }

    /// The CLI's exit predicate: 1 when any violation exists, else 0.
    pub fn exit_code(&self) -> u8 {
        u8::from(!self.violations.is_empty())
    }

    /// The `--json` document (schema [`REPORT_FORMAT`]).
    pub fn to_json(&self, dir: &str) -> Json {
        let layer_pairs: Vec<Json> = self
            .layer_pairs()
            .iter()
            .map(|p| {
                Json::obj([
                    ("from_layer", Json::str(&p.from_layer)),
                    ("to_layer", Json::str(&p.to_layer)),
                    ("edges", Json::U64(p.edges)),
                    ("unit_pairs", Json::U64(p.unit_pairs)),
                ])
            })
            .collect();
        let violations: Vec<Json> = self
            .violations
            .iter()
            .map(|v| {
                Json::obj([
                    ("from_unit", Json::str(&v.from_unit)),
                    ("from_layer", Json::str(&v.from_layer)),
                    ("to_unit", Json::str(&v.to_unit)),
                    ("to_layer", Json::str(&v.to_layer)),
                    ("count", Json::U64(v.count)),
                    (
                        "examples",
                        Json::Array(v.examples.iter().map(Json::str).collect()),
                    ),
                ])
            })
            .collect();
        let status = if self.violations.is_empty() {
            "clean"
        } else {
            "violations"
        };
        Json::obj([
            ("schema", Json::str(REPORT_FORMAT)),
            ("dir", Json::str(dir)),
            ("rule", Json::str(RULE)),
            ("total_edges", Json::U64(self.total_edges)),
            ("unit_pairs", Json::U64(self.violations.len() as u64)),
            ("layer_pairs", Json::Array(layer_pairs)),
            ("violations", Json::Array(violations)),
            ("status", Json::str(status)),
            ("exit", Json::U64(u64::from(self.exit_code()))),
        ])
    }

    /// The human report: grouped by layer pair (worst group first), unit
    /// pairs worst-first within each group, evidence indented — readable at
    /// 100+ rows because every group is a self-labeled block.
    pub fn to_text(&self, dir: &str) -> String {
        use std::fmt::Write as _;
        let mut out = String::new();
        let _ = writeln!(out, "trailtracker violations: {dir}");
        let _ = writeln!(out, "rule: {RULE}");
        if self.violations.is_empty() {
            let _ = writeln!(out, "no violations — every layer dependency points inward.");
            let _ = writeln!(out, "status: clean (exit 0)");
            return out;
        }
        let groups = self.layer_pairs();
        let _ = writeln!(
            out,
            "total: {} violating edge(s) across {} unit pair(s) in {} layer pair(s)",
            self.total_edges,
            self.violations.len(),
            groups.len()
        );
        for g in &groups {
            let _ = writeln!(out);
            let _ = writeln!(
                out,
                "{} -> {} ({} edge(s), {} unit pair(s)):",
                g.from_layer, g.to_layer, g.edges, g.unit_pairs
            );
            for v in self
                .violations
                .iter()
                .filter(|v| v.from_layer == g.from_layer && v.to_layer == g.to_layer)
            {
                let _ = writeln!(out, "  [{:>5}] {} -> {}", v.count, v.from_unit, v.to_unit);
                for e in &v.examples {
                    let _ = writeln!(out, "          evidence: {e}");
                }
            }
        }
        let _ = writeln!(out, "\nstatus: violations (exit 1)");
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::extract::{Extractor, LayerExtractor};
    use crate::ir::ontology::edge;

    fn file(g: &mut Graph, path: &str) -> String {
        let name = path.rsplit('/').next().unwrap().to_string();
        let id = format!("file::{path}");
        g.upsert_node(id.clone(), ont::FILE, name, vec![("path", Json::str(path))]);
        id
    }

    fn sym(g: &mut Graph, file_id: &str, kind: &'static str, name: &str) -> String {
        let id = format!("sym::{file_id}::{name}");
        g.upsert_node(id.clone(), kind, name, vec![]);
        g.add_edge(file_id.to_string(), edge::DECLARES, id.clone(), vec![]);
        id
    }

    /// The eShop shape the layers extractor's own tests use: Domain,
    /// Infrastructure, and API units, one deliberate inversion
    /// (Domain → Infrastructure ×2) and one clean edge (API → Domain).
    fn sample() -> Graph {
        let mut g = Graph::new();
        let fd = file(&mut g, "src/Ordering.Domain/Order.cs");
        let order = sym(&mut g, &fd, ont::TYPE, "Order");
        let fd2 = file(&mut g, "src/Ordering.Domain/Status.cs");
        let status = sym(&mut g, &fd2, ont::TYPE, "OrderStatus");
        let fi = file(&mut g, "src/Ordering.Infrastructure/OrderRepository.cs");
        let repo = sym(&mut g, &fi, ont::TYPE, "OrderRepository");
        let fa = file(&mut g, "src/Ordering.API/OrdersController.cs");
        let ctrl = sym(&mut g, &fa, ont::FUNCTION, "Get");
        // The inversion, twice, from two Domain files.
        g.add_edge(order.clone(), edge::USES_TYPE, repo.clone(), vec![]);
        g.add_edge(status, edge::USES_TYPE, repo, vec![]);
        // Clean inward edge.
        g.add_edge(ctrl, edge::USES_TYPE, order, vec![]);
        g
    }

    #[test]
    fn names_the_perpetrating_units_with_file_evidence() {
        let report = violations_report(&sample());
        assert_eq!(report.violations.len(), 1, "{:?}", report.violations);
        let v = &report.violations[0];
        assert_eq!(v.from_unit, "Ordering.Domain");
        assert_eq!(v.from_layer, "Domain");
        assert_eq!(v.to_unit, "Ordering.Infrastructure");
        assert_eq!(v.to_layer, "Infrastructure");
        assert_eq!(v.count, 2);
        assert_eq!(report.total_edges, 2);
        assert_eq!(v.examples.len(), 2);
        assert!(
            v.examples[0].contains("src/Ordering.Domain/Order.cs")
                && v.examples[0].contains("USES_TYPE")
                && v.examples[0].contains("src/Ordering.Infrastructure/OrderRepository.cs"),
            "{:?}",
            v.examples
        );
        assert_eq!(report.exit_code(), 1);
    }

    #[test]
    fn totals_agree_with_the_layers_view_aggregate() {
        // The report's per-layer-pair mass must equal the aggregate count on
        // the layers view's violation-flagged edges — same rule, same data.
        let g = sample();
        let report = violations_report(&g);
        let derived = LayerExtractor.extract(&g);
        for p in report.layer_pairs() {
            let e = derived
                .edges()
                .find(|e| {
                    e.kind == edge::DEPENDS_ON
                        && e.from == format!("layer::{}", p.from_layer)
                        && e.to == format!("layer::{}", p.to_layer)
                })
                .expect("layer edge exists");
            assert_eq!(e.props.get("violation"), Some(&Json::Bool(true)));
            assert_eq!(e.props.get("count"), Some(&Json::U64(p.edges)));
        }
    }

    #[test]
    fn clean_graph_reports_nothing() {
        let mut g = Graph::new();
        let fd = file(&mut g, "src/Shop.Domain/order.cs");
        let order = sym(&mut g, &fd, ont::TYPE, "Order");
        let fa = file(&mut g, "src/Shop.API/controller.cs");
        let ctrl = sym(&mut g, &fa, ont::FUNCTION, "Get");
        g.add_edge(ctrl, edge::USES_TYPE, order, vec![]);
        let report = violations_report(&g);
        assert!(report.violations.is_empty());
        assert_eq!(report.total_edges, 0);
        assert_eq!(report.exit_code(), 0);
        assert!(report.to_text("d").contains("no violations"));
        let json = report.to_json("d").to_line();
        assert!(json.contains("\"status\":\"clean\""), "{json}");
        assert!(json.contains(REPORT_FORMAT), "{json}");
    }

    #[test]
    fn ranked_worst_first_and_deterministic() {
        // Two violating pairs with different mass: heavier first.
        let mut g = Graph::new();
        let fd = file(&mut g, "src/A.Domain/a.cs");
        let a = sym(&mut g, &fd, ont::TYPE, "AThing");
        let fd2 = file(&mut g, "src/B.Domain/b.cs");
        let b = sym(&mut g, &fd2, ont::TYPE, "BThing");
        let fi = file(&mut g, "src/Store.Infrastructure/repo.cs");
        let repo = sym(&mut g, &fi, ont::TYPE, "Repo");
        let fi2 = file(&mut g, "src/Store.Infrastructure/repo2.cs");
        let repo2 = sym(&mut g, &fi2, ont::TYPE, "Repo2");
        // B.Domain → Store.Infrastructure ×2, A.Domain → ×1.
        g.add_edge(b.clone(), edge::USES_TYPE, repo.clone(), vec![]);
        g.add_edge(b, edge::USES_TYPE, repo2, vec![]);
        g.add_edge(a, edge::USES_TYPE, repo, vec![]);
        let report = violations_report(&g);
        assert_eq!(report.violations.len(), 2);
        assert_eq!(report.violations[0].from_unit, "B.Domain");
        assert_eq!(report.violations[0].count, 2);
        assert_eq!(report.violations[1].from_unit, "A.Domain");
        // Byte-determinism of both renderings.
        assert_eq!(
            report.to_json("x").to_line(),
            violations_report(&g).to_json("x").to_line()
        );
        assert_eq!(report.to_text("x"), violations_report(&g).to_text("x"));
    }

    #[test]
    fn inheritance_edges_are_violations_too() {
        // The undercount bug: a Domain-layer class that EXTENDS (or
        // IMPLEMENTS) a Presentation/Infrastructure-layer class is a
        // layering violation exactly like a call — SPECIALIZES-family edges
        // must join the scan.
        let mut g = sample();
        let fd3 = file(&mut g, "src/Ordering.Domain/Special.cs");
        let special = sym(&mut g, &fd3, ont::TYPE, "SpecialOrder");
        let base = "sym::file::src/Ordering.Infrastructure/OrderRepository.cs::OrderRepository";
        g.add_edge(special.clone(), edge::EXTENDS, base.to_string(), vec![]);
        g.add_edge(special, edge::IMPLEMENTS, base.to_string(), vec![]);
        let report = violations_report(&g);
        // 2 USES_TYPE from the sample + EXTENDS + IMPLEMENTS.
        assert_eq!(report.total_edges, 4, "{:?}", report.violations);
        let v = &report.violations[0];
        assert!(
            v.examples
                .iter()
                .any(|e| e.contains("-[EXTENDS]->") && e.contains(":SpecialOrder")),
            "{:?}",
            v.examples
        );
        assert!(
            v.examples.iter().any(|e| e.contains("-[IMPLEMENTS]->")),
            "{:?}",
            v.examples
        );
    }

    #[test]
    fn evidence_is_symbol_grain_and_complete_by_default() {
        // Every violating edge is named `path:symbol -[KIND]-> path:symbol`,
        // and the default report carries ALL of them (no silent 5-edge cap).
        let mut g = Graph::new();
        let fi = file(&mut g, "src/Store.Infrastructure/repo.cs");
        let repo = sym(&mut g, &fi, ont::TYPE, "Repo");
        for i in 0..7 {
            let fd = file(&mut g, &format!("src/Store.Domain/e{i}.cs"));
            let s = sym(&mut g, &fd, ont::TYPE, &format!("Entity{i}"));
            g.add_edge(s, edge::USES_TYPE, repo.clone(), vec![]);
        }
        let report = violations_report(&g);
        assert_eq!(report.total_edges, 7);
        assert_eq!(report.violations.len(), 1);
        assert_eq!(report.violations[0].examples.len(), 7, "no cap by default");
        assert_eq!(
            report.violations[0].examples[0],
            "src/Store.Domain/e0.cs:Entity0 -[USES_TYPE]-> src/Store.Infrastructure/repo.cs:Repo"
        );
        // An explicit cap bounds the evidence, never the count.
        let capped = violations_report_capped(&g, Some(2));
        assert_eq!(capped.total_edges, 7);
        assert_eq!(capped.violations[0].examples.len(), 2);
        assert_eq!(capped.violations[0].count, 7);
    }

    #[test]
    fn direction_rule_matches_the_layers_extractor() {
        assert!(is_violation("Domain", "Application"));
        assert!(is_violation("Domain", "Infrastructure"));
        assert!(is_violation("Domain", "Presentation"));
        assert!(is_violation("Application", "Infrastructure"));
        assert!(is_violation("Application", "Presentation"));
        assert!(is_violation("Infrastructure", "Presentation"));
        assert!(!is_violation("Presentation", "Domain"));
        assert!(!is_violation("Infrastructure", "Application"));
        assert!(!is_violation("Domain", "Domain"));
        assert!(!is_violation("Test", "Presentation"));
        assert!(!is_violation("Domain", "Shared"));
        assert!(!is_violation("Shared", "Presentation"));
    }

    #[test]
    fn grouped_text_report_names_units_under_layer_headers() {
        let text = violations_report(&sample()).to_text("src");
        assert!(
            text.contains("Domain -> Infrastructure (2 edge(s), 1 unit pair(s)):"),
            "{text}"
        );
        assert!(
            text.contains("Ordering.Domain -> Ordering.Infrastructure"),
            "{text}"
        );
        assert!(
            text.contains("evidence: src/Ordering.Domain/Order.cs"),
            "{text}"
        );
        assert!(text.contains("status: violations (exit 1)"), "{text}");
    }
}
