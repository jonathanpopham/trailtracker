//! The org report: an analyst-readable markdown summary of the whole graph.
//!
//! Where [`crate::query`] answers a targeted question, this renders the org (or
//! codebase) at a glance — the document an analyst reads first when handed an
//! inherited Salesforce org:
//!
//! - **Counts** — nodes by kind and edges by kind.
//! - **Flows by depth** — declarative workflows ([`Function`] nodes with
//!   `type_kind: "flow"`) ranked by `depth`; anything `>= 10` is flagged
//!   `DEEP` (the deep-flow maintenance-risk threshold).
//! - **Apex** — class count ([`Type`] nodes with `language: "apex"`) and method
//!   count ([`Function`] nodes with `language: "apex"`).
//! - **SObjects** — each SObject ([`Type`], `type_kind: "sobject"`) with its
//!   declared field count (`DECLARES` edges to a `sobject_field` [`Constant`]).
//! - **Validation rules** — count of `validation_rule` constants.
//! - **Risk flags** — the deep flows, and orphan candidates: flow / Apex
//!   [`Function`] nodes with **zero** incoming edges (nothing invokes them).
//!
//! The whole report is a pure, deterministic function of the graph: every
//! section walks the `BTreeMap`-ordered node/edge iterators and sorts before
//! rendering, so the same graph always produces byte-identical markdown.
//!
//! [`Function`]: crate::ir::ontology::node::FUNCTION
//! [`Type`]: crate::ir::ontology::node::TYPE
//! [`Constant`]: crate::ir::ontology::node::CONSTANT

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use crate::core::json::Json;
use crate::graph::Graph;
use crate::ir::ontology::node as ont;

/// The deep-flow maintenance-risk threshold: a flow whose `depth` is at least
/// this is flagged `DEEP` in the report.
const DEEP_FLOW_DEPTH: u64 = 10;

/// Render the full org report as markdown.
pub fn report(graph: &Graph) -> String {
    let mut out = String::new();
    out.push_str("# TrailTracker org report\n\n");

    counts_section(graph, &mut out);
    flows_section(graph, &mut out);
    apex_section(graph, &mut out);
    sobjects_section(graph, &mut out);
    validation_section(graph, &mut out);
    risk_section(graph, &mut out);

    out
}

/// Node-kind and edge-kind tallies.
fn counts_section(graph: &Graph, out: &mut String) {
    let mut nodes: BTreeMap<&str, usize> = BTreeMap::new();
    for n in graph.nodes() {
        *nodes.entry(n.kind).or_default() += 1;
    }
    let mut edges: BTreeMap<&str, usize> = BTreeMap::new();
    for e in graph.edges() {
        *edges.entry(e.kind).or_default() += 1;
    }

    out.push_str("## Counts\n\n");
    let _ = writeln!(
        out,
        "- {} nodes, {} edges",
        graph.node_count(),
        graph.edge_count()
    );
    out.push_str("\n### Nodes by kind\n\n");
    for (kind, count) in &nodes {
        let _ = writeln!(out, "- {kind}: {count}");
    }
    out.push_str("\n### Edges by kind\n\n");
    for (kind, count) in &edges {
        let _ = writeln!(out, "- {kind}: {count}");
    }
    out.push('\n');
}

/// Flows ranked by depth, deep ones flagged.
fn flows_section(graph: &Graph, out: &mut String) {
    let flows = ranked_flows(graph);
    out.push_str("## Flows by depth\n\n");
    if flows.is_empty() {
        out.push_str("_none_\n\n");
        return;
    }
    for (depth, elements, id, _name) in &flows {
        let flag = if *depth >= DEEP_FLOW_DEPTH {
            "  **DEEP**"
        } else {
            ""
        };
        let _ = writeln!(out, "- {id} — depth {depth}, {elements} elements{flag}");
    }
    out.push('\n');
}

/// Apex class + method counts.
fn apex_section(graph: &Graph, out: &mut String) {
    let mut classes = 0usize;
    let mut methods = 0usize;
    for n in graph.nodes() {
        if prop_str(n.props.get("language")) != "apex" {
            continue;
        }
        match n.kind {
            ont::TYPE => classes += 1,
            ont::FUNCTION => methods += 1,
            _ => {}
        }
    }
    out.push_str("## Apex\n\n");
    let _ = writeln!(out, "- classes: {classes}");
    let _ = writeln!(out, "- methods: {methods}");
    out.push('\n');
}

/// SObjects with their declared-field counts.
fn sobjects_section(graph: &Graph, out: &mut String) {
    // The set of field constants, so we count only sobject_field DECLARES.
    let fields: BTreeSet<&str> = graph
        .nodes()
        .filter(|n| {
            n.kind == ont::CONSTANT && prop_str(n.props.get("type_kind")) == "sobject_field"
        })
        .map(|n| n.id.as_str())
        .collect();

    // sobject id -> declared field count, seeded to 0 for every SObject so a
    // fieldless object still lists.
    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    for n in graph.nodes() {
        if n.kind == ont::TYPE && prop_str(n.props.get("type_kind")) == "sobject" {
            counts.entry(n.id.as_str()).or_insert(0);
        }
    }
    for e in graph
        .edges()
        .filter(|e| e.kind == crate::ir::ontology::edge::DECLARES)
    {
        if fields.contains(e.to.as_str()) {
            if let Some(c) = counts.get_mut(e.from.as_str()) {
                *c += 1;
            }
        }
    }

    out.push_str("## SObjects\n\n");
    if counts.is_empty() {
        out.push_str("_none_\n\n");
        return;
    }
    for (id, count) in &counts {
        let _ = writeln!(out, "- {id} — {count} fields");
    }
    out.push('\n');
}

/// Validation-rule count.
fn validation_section(graph: &Graph, out: &mut String) {
    let count = graph
        .nodes()
        .filter(|n| {
            n.kind == ont::CONSTANT && prop_str(n.props.get("type_kind")) == "validation_rule"
        })
        .count();
    out.push_str("## Validation rules\n\n");
    let _ = writeln!(out, "- {count} rule(s)\n");
}

/// Risk flags: deep flows and orphan flow/Apex functions.
fn risk_section(graph: &Graph, out: &mut String) {
    out.push_str("## Risk flags\n\n");

    // Deep flows.
    let deep: Vec<_> = ranked_flows(graph)
        .into_iter()
        .filter(|(depth, ..)| *depth >= DEEP_FLOW_DEPTH)
        .collect();
    out.push_str("### Deep flows\n\n");
    if deep.is_empty() {
        out.push_str("_none_\n\n");
    } else {
        for (depth, elements, id, _name) in &deep {
            let _ = writeln!(out, "- {id} — depth {depth}, {elements} elements");
        }
        out.push('\n');
    }

    // Orphan candidates: flow / apex Function nodes with zero incoming edges.
    let mut has_incoming: BTreeSet<&str> = BTreeSet::new();
    for e in graph.edges() {
        has_incoming.insert(e.to.as_str());
    }
    let mut orphans: BTreeSet<&str> = BTreeSet::new();
    for n in graph.nodes() {
        if n.kind != ont::FUNCTION {
            continue;
        }
        let is_flow = prop_str(n.props.get("type_kind")) == "flow";
        let is_apex = prop_str(n.props.get("language")) == "apex";
        if (is_flow || is_apex) && !has_incoming.contains(n.id.as_str()) {
            orphans.insert(n.id.as_str());
        }
    }
    out.push_str("### Orphan candidates (no incoming edges)\n\n");
    if orphans.is_empty() {
        out.push_str("_none_\n");
    } else {
        for id in &orphans {
            let _ = writeln!(out, "- {id}");
        }
    }
}

/// Flows ranked deepest-first, ties broken by id ascending. Returns
/// `(depth, element_count, id, name)`.
fn ranked_flows(graph: &Graph) -> Vec<(u64, u64, String, String)> {
    let mut flows: Vec<(u64, u64, String, String)> = graph
        .nodes()
        .filter(|n| n.kind == ont::FUNCTION && prop_str(n.props.get("type_kind")) == "flow")
        .map(|n| {
            (
                prop_u64(n.props.get("depth")),
                prop_u64(n.props.get("element_count")),
                n.id.clone(),
                n.name.clone(),
            )
        })
        .collect();
    flows.sort_by(|a, b| b.0.cmp(&a.0).then_with(|| a.2.cmp(&b.2)));
    flows
}

/// A `Json` property rendered as a string slice (only `Json::Str`), else `""`.
fn prop_str(v: Option<&Json>) -> &str {
    match v {
        Some(Json::Str(s)) => s.as_str(),
        _ => "",
    }
}

/// A `Json` property rendered as a `u64`, tolerating `U64`/`I64`, else `0`.
fn prop_u64(v: Option<&Json>) -> u64 {
    match v {
        Some(Json::U64(n)) => *n,
        Some(Json::I64(n)) if *n >= 0 => *n as u64,
        _ => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::ontology::edge;

    /// A hand-built org: one SObject with a field + a validation rule, a deep
    /// flow (depth 12) and a shallow one, and an Apex class with one method
    /// (orphaned — nothing calls it).
    fn sample() -> Graph {
        let mut g = Graph::new();
        g.upsert_node(
            "sobject::Case__c",
            ont::TYPE,
            "Case__c",
            vec![("type_kind", Json::str("sobject"))],
        );
        g.upsert_node(
            "sobject_field::Case__c.Severity__c",
            ont::CONSTANT,
            "Severity__c",
            vec![("type_kind", Json::str("sobject_field"))],
        );
        g.add_edge(
            "sobject::Case__c",
            edge::DECLARES,
            "sobject_field::Case__c.Severity__c",
            vec![],
        );
        g.upsert_node(
            "validation_rule::Case__c.Severity_Required",
            ont::CONSTANT,
            "Severity_Required",
            vec![("type_kind", Json::str("validation_rule"))],
        );
        g.add_edge(
            "sobject::Case__c",
            edge::DECLARES,
            "validation_rule::Case__c.Severity_Required",
            vec![],
        );
        // Deep flow, referenced by its file so it is not an orphan.
        g.upsert_node(
            "flow::DeepIntake",
            ont::FUNCTION,
            "DeepIntake",
            vec![
                ("type_kind", Json::str("flow")),
                ("depth", Json::U64(12)),
                ("element_count", Json::U64(12)),
            ],
        );
        g.upsert_node("file::flows/DeepIntake", ont::FILE, "DeepIntake", vec![]);
        g.add_edge(
            "file::flows/DeepIntake",
            edge::DECLARES,
            "flow::DeepIntake",
            vec![],
        );
        // Shallow flow.
        g.upsert_node(
            "flow::FollowUp",
            ont::FUNCTION,
            "FollowUp",
            vec![
                ("type_kind", Json::str("flow")),
                ("depth", Json::U64(1)),
                ("element_count", Json::U64(2)),
            ],
        );
        g.add_edge(
            "file::flows/DeepIntake",
            edge::DECLARES,
            "flow::FollowUp",
            vec![],
        );
        // Apex class + one orphan method.
        g.upsert_node(
            "apex::CaseSvc",
            ont::TYPE,
            "CaseSvc",
            vec![
                ("language", Json::str("apex")),
                ("type_kind", Json::str("class")),
            ],
        );
        g.upsert_node(
            "apex::CaseSvc.orphanMethod",
            ont::FUNCTION,
            "orphanMethod",
            vec![("language", Json::str("apex"))],
        );
        g
    }

    #[test]
    fn report_has_counts_and_flags_deep_flow() {
        let md = report(&sample());
        // Counts section present with node/edge tallies.
        assert!(md.contains("## Counts"));
        assert!(md.contains("Function: 3"));
        assert!(md.contains("DECLARES:"));
        // Deep flow is flagged in the flows section AND in risk flags.
        assert!(md.contains("flow::DeepIntake — depth 12, 12 elements  **DEEP**"));
        assert!(md.contains("### Deep flows"));
        // Deepest-first ordering.
        let deep_pos = md.find("flow::DeepIntake — depth 12").unwrap();
        let shallow_pos = md.find("flow::FollowUp — depth 1").unwrap();
        assert!(deep_pos < shallow_pos);
    }

    #[test]
    fn report_counts_apex_and_sobject_fields_and_validation() {
        let md = report(&sample());
        assert!(md.contains("- classes: 1"));
        assert!(md.contains("- methods: 1"));
        // One field on Case__c (the validation rule DECLARES must not be counted).
        assert!(md.contains("sobject::Case__c — 1 fields"));
        assert!(md.contains("## Validation rules\n\n- 1 rule(s)"));
    }

    #[test]
    fn report_flags_orphan_apex_method() {
        let md = report(&sample());
        assert!(md.contains("### Orphan candidates"));
        assert!(md.contains("- apex::CaseSvc.orphanMethod"));
        // The flows have incoming DECLARES edges, so they are not orphans.
        assert!(!md.contains("- flow::DeepIntake\n"));
    }

    #[test]
    fn report_is_deterministic() {
        let g = sample();
        assert_eq!(report(&g), report(&g));
        assert!(!report(&g).is_empty());
    }
}
