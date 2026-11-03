//! Interactive graph queries: the *usable* surface over the canonical graph.
//!
//! The base graph ([`crate::graph::Graph`]) is the product, but an analyst does
//! not want to read 100 lines of JSONL. These queries answer the questions a
//! human actually asks of an inherited codebase or Salesforce org:
//!
//! - **what-touches** — the *incoming* edges to a node: everything that
//!   references it, grouped by relationship kind. "What reads `Case__c`?"
//! - **uses** — the *outgoing* edges: everything the node references. The dual
//!   of `what-touches`.
//! - **blast-radius** — transitive **reverse reachability**: follow incoming
//!   edges outward from the target, so the result is every node that could be
//!   affected if the target changed. "If I rename this field, what breaks?"
//! - **deepest-flows** — the declarative workflows ([`Function`] nodes with
//!   `type_kind: "flow"`) ranked by `depth`, the maintenance-risk signal.
//!
//! Every query is a pure, deterministic function of the graph: targets resolve
//! through the `BTreeMap`-ordered node iterator, result sets are `BTreeSet`s,
//! and rendering walks sorted collections, so the same graph always produces
//! byte-identical output. Text is the default; `--json` emits one machine
//! object built through the deterministic [`Json`] writer.
//!
//! [`Function`]: crate::ir::ontology::node::FUNCTION
//! [`Json`]: crate::core::json::Json

use std::collections::{BTreeMap, BTreeSet};

use crate::core::json::Json;
use crate::graph::Graph;

/// A safety cap on reverse-reachability traversal depth. Real dependency chains
/// in a codebase are shallow; this only exists so a pathological graph cannot
/// spin. It is deep enough that no honest chain is truncated in practice.
const MAX_BLAST_DEPTH: usize = 64;

/// Resolve a user-supplied `target` to concrete node ids. An exact node **id**
/// match wins and resolves to exactly that node; otherwise every node whose
/// **name** equals `target` is returned. Result is sorted and de-duplicated for
/// determinism. Empty means "nothing matched".
fn resolve_targets(graph: &Graph, target: &str) -> Vec<String> {
    if graph.has_node(target) {
        return vec![target.to_string()];
    }
    let mut ids: BTreeSet<String> = BTreeSet::new();
    for n in graph.nodes() {
        if n.name == target {
            ids.insert(n.id.clone());
        }
    }
    ids.into_iter().collect()
}

/// A node's display kind, or `"?"` if the node is absent (e.g. an edge endpoint
/// that is a logical/external id with no node record).
fn kind_of<'a>(graph: &'a Graph, id: &str) -> &'a str {
    graph
        .nodes()
        .find(|n| n.id == id)
        .map(|n| n.kind)
        .unwrap_or("?")
}

/// `what-touches`: the incoming edges to the resolved target(s), grouped by edge
/// kind. Returns the rendered output (text or JSON).
pub fn what_touches(graph: &Graph, target: &str, json: bool) -> Result<String, String> {
    let targets = resolve_targets(graph, target);
    if targets.is_empty() {
        return Err(format!("no node matching '{target}'"));
    }
    let target_set: BTreeSet<&str> = targets.iter().map(String::as_str).collect();

    // edge kind -> sorted set of "from" ids that reference a target.
    let mut by_kind: BTreeMap<&'static str, BTreeSet<&str>> = BTreeMap::new();
    for e in graph.edges() {
        if target_set.contains(e.to.as_str()) {
            by_kind.entry(e.kind).or_default().insert(e.from.as_str());
        }
    }

    if json {
        return Ok(render_grouped_json(
            "what-touches",
            &targets,
            "referenced_by",
            &by_kind,
            graph,
        ));
    }
    Ok(render_grouped_text(
        "what-touches",
        &targets,
        "referenced by",
        &by_kind,
        graph,
    ))
}

/// `uses`: the outgoing edges from the resolved target(s), grouped by edge kind.
pub fn uses(graph: &Graph, target: &str, json: bool) -> Result<String, String> {
    let targets = resolve_targets(graph, target);
    if targets.is_empty() {
        return Err(format!("no node matching '{target}'"));
    }
    let target_set: BTreeSet<&str> = targets.iter().map(String::as_str).collect();

    let mut by_kind: BTreeMap<&'static str, BTreeSet<&str>> = BTreeMap::new();
    for e in graph.edges() {
        if target_set.contains(e.from.as_str()) {
            by_kind.entry(e.kind).or_default().insert(e.to.as_str());
        }
    }

    if json {
        return Ok(render_grouped_json(
            "uses", &targets, "uses", &by_kind, graph,
        ));
    }
    Ok(render_grouped_text(
        "uses", &targets, "uses", &by_kind, graph,
    ))
}

/// The transitive reverse-reachability set from `seeds` (exact node ids):
/// follow incoming edges outward — if `X --edge--> seed`, then `X` is
/// affected, and so is anything that references `X`, and so on. The seeds are
/// excluded from the result (they are the cause, not the impact). Exposed so
/// other surfaces (`explain`) reuse the *same* machinery `query blast-radius`
/// renders — one traversal, never a re-derivation. Pure and deterministic.
pub fn blast_radius_set(graph: &Graph, seeds: &[String]) -> BTreeSet<String> {
    // Reverse adjacency: to -> {from}. Built once, iterated in sorted order.
    let mut incoming: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    for e in graph.edges() {
        incoming
            .entry(e.to.as_str())
            .or_default()
            .insert(e.from.as_str());
    }

    let seed_set: BTreeSet<&str> = seeds.iter().map(String::as_str).collect();
    // Breadth-first, depth-capped. `affected` is the accumulated result;
    // `frontier` is the current wavefront. BTreeSet keeps traversal order and
    // output deterministic regardless of edge insertion order.
    let mut affected: BTreeSet<String> = BTreeSet::new();
    let mut frontier: BTreeSet<&str> = seed_set.clone();
    let mut depth = 0usize;
    while !frontier.is_empty() && depth < MAX_BLAST_DEPTH {
        let mut next: BTreeSet<&str> = BTreeSet::new();
        for node in &frontier {
            if let Some(refs) = incoming.get(node) {
                for r in refs {
                    // Skip seeds (cause, not impact) and anything already found.
                    if seed_set.contains(r) || affected.contains(*r) {
                        continue;
                    }
                    affected.insert((*r).to_string());
                    next.insert(*r);
                }
            }
        }
        frontier = next;
        depth += 1;
    }
    affected
}

/// `blast-radius`: transitive reverse reachability from the target(s). Follows
/// incoming edges outward — if `X --edge--> target`, then `X` is affected, and
/// so is anything that references `X`, and so on. The target seeds are excluded
/// from the affected set (they are the cause, not the impact).
pub fn blast_radius(graph: &Graph, target: &str, json: bool) -> Result<String, String> {
    let seeds = resolve_targets(graph, target);
    if seeds.is_empty() {
        return Err(format!("no node matching '{target}'"));
    }
    let affected = blast_radius_set(graph, &seeds);

    if json {
        let mut nodes: Vec<Json> = Vec::new();
        for id in &affected {
            nodes.push(Json::obj([
                ("id", Json::str(id.clone())),
                ("kind", Json::str(kind_of(graph, id).to_string())),
            ]));
        }
        let obj = Json::obj([
            ("query", Json::str("blast-radius")),
            (
                "target",
                Json::Array(seeds.iter().map(|s| Json::str(s.clone())).collect()),
            ),
            ("affected_count", Json::U64(affected.len() as u64)),
            ("affected", Json::Array(nodes)),
        ]);
        return Ok(obj.to_line());
    }

    let mut out = String::new();
    out.push_str(&format!(
        "blast-radius of {} — {} node(s) affected\n",
        seeds.join(", "),
        affected.len()
    ));
    for id in &affected {
        out.push_str(&format!("  [{}] {}\n", kind_of(graph, id), id));
    }
    Ok(out)
}

/// `deepest-flows`: flows ([`Function`](crate::ir::ontology::node::FUNCTION)
/// nodes with `type_kind: "flow"`) ranked by `depth` descending, ties broken by
/// id ascending. Reports `depth` and `element_count`.
pub fn deepest_flows(graph: &Graph, json: bool) -> String {
    // (depth, element_count, id, name)
    let mut flows: Vec<(u64, u64, String, String)> = Vec::new();
    for n in graph.nodes() {
        if n.kind != crate::ir::ontology::node::FUNCTION {
            continue;
        }
        if prop_str(n.props.get("type_kind")) != "flow" {
            continue;
        }
        let depth = prop_u64(n.props.get("depth"));
        let elements = prop_u64(n.props.get("element_count"));
        flows.push((depth, elements, n.id.clone(), n.name.clone()));
    }
    // Descending depth, then ascending id for a stable total order.
    flows.sort_by(|a, b| b.0.cmp(&a.0).then_with(|| a.2.cmp(&b.2)));

    if json {
        let arr: Vec<Json> = flows
            .iter()
            .map(|(depth, elements, id, name)| {
                Json::obj([
                    ("id", Json::str(id.clone())),
                    ("name", Json::str(name.clone())),
                    ("depth", Json::U64(*depth)),
                    ("element_count", Json::U64(*elements)),
                ])
            })
            .collect();
        return Json::obj([
            ("query", Json::str("deepest-flows")),
            ("flows", Json::Array(arr)),
        ])
        .to_line();
    }

    let mut out = String::new();
    out.push_str(&format!("deepest-flows — {} flow(s)\n", flows.len()));
    for (depth, elements, id, _name) in &flows {
        let flag = if *depth >= 10 { "  DEEP" } else { "" };
        out.push_str(&format!(
            "  depth {depth:>3}  {elements:>3} elements  {id}{flag}\n"
        ));
    }
    out
}

/// Render a grouped-edge result (`what-touches`/`uses`) as readable text.
fn render_grouped_text(
    query: &str,
    targets: &[String],
    verb: &str,
    by_kind: &BTreeMap<&'static str, BTreeSet<&str>>,
    graph: &Graph,
) -> String {
    let total: usize = by_kind.values().map(BTreeSet::len).sum();
    let mut out = String::new();
    out.push_str(&format!(
        "{query}: {} — {total} edge(s) {verb}\n",
        targets.join(", ")
    ));
    for (kind, froms) in by_kind {
        out.push_str(&format!("  {kind} ({})\n", froms.len()));
        for id in froms {
            out.push_str(&format!("    [{}] {}\n", kind_of(graph, id), id));
        }
    }
    out
}

/// Render a grouped-edge result as one deterministic JSON object.
fn render_grouped_json(
    query: &str,
    targets: &[String],
    field: &'static str,
    by_kind: &BTreeMap<&'static str, BTreeSet<&str>>,
    graph: &Graph,
) -> String {
    let mut groups: Vec<Json> = Vec::new();
    for (kind, ids) in by_kind {
        let nodes: Vec<Json> = ids
            .iter()
            .map(|id| {
                Json::obj([
                    ("id", Json::str((*id).to_string())),
                    ("kind", Json::str(kind_of(graph, id).to_string())),
                ])
            })
            .collect();
        groups.push(Json::obj([
            ("kind", Json::str((*kind).to_string())),
            (field, Json::Array(nodes)),
        ]));
    }
    Json::obj([
        ("query", Json::str(query.to_string())),
        (
            "target",
            Json::Array(targets.iter().map(|t| Json::str(t.clone())).collect()),
        ),
        ("groups", Json::Array(groups)),
    ])
    .to_line()
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
    use crate::ir::ontology::{edge, node as ont};

    /// A small hand-built graph: two SObjects, a lookup field with a
    /// `referenceTo` USES_TYPE, a flow (depth 11) whose element touches Case, and
    /// an Apex method that also touches Case — enough to exercise every query.
    fn sample() -> Graph {
        let mut g = Graph::new();
        g.upsert_node(
            "sobject::Case__c",
            ont::TYPE,
            "Case__c",
            vec![("type_kind", Json::str("sobject"))],
        );
        g.upsert_node(
            "sobject::Referral__c",
            ont::TYPE,
            "Referral__c",
            vec![("type_kind", Json::str("sobject"))],
        );
        g.upsert_node(
            "sobject_field::Case__c.Referral__c",
            ont::CONSTANT,
            "Referral__c",
            vec![("type_kind", Json::str("sobject_field"))],
        );
        // Field references the Referral SObject (referenceTo).
        g.add_edge(
            "sobject_field::Case__c.Referral__c",
            edge::USES_TYPE,
            "sobject::Referral__c",
            vec![("via", Json::str("referenceTo"))],
        );
        // Case declares the field.
        g.add_edge(
            "sobject::Case__c",
            edge::DECLARES,
            "sobject_field::Case__c.Referral__c",
            vec![],
        );
        // A flow element touches Case, and the flow declares the element.
        g.upsert_node(
            "flow::Intake",
            ont::FUNCTION,
            "Intake",
            vec![
                ("type_kind", Json::str("flow")),
                ("depth", Json::U64(11)),
                ("element_count", Json::U64(6)),
            ],
        );
        g.upsert_node(
            "flow_element::Intake.Create_Case",
            ont::FUNCTION,
            "Create_Case",
            vec![("type_kind", Json::str("flow_element"))],
        );
        g.add_edge(
            "flow::Intake",
            edge::DECLARES,
            "flow_element::Intake.Create_Case",
            vec![],
        );
        g.add_edge(
            "flow_element::Intake.Create_Case",
            edge::USES_TYPE,
            "sobject::Case__c",
            vec![("via", Json::str("recordCreates"))],
        );
        // An Apex method that also touches Case.
        g.upsert_node(
            "apex::CaseSvc.touch",
            ont::FUNCTION,
            "touch",
            vec![("language", Json::str("apex"))],
        );
        g.add_edge(
            "apex::CaseSvc.touch",
            edge::USES_TYPE,
            "sobject::Case__c",
            vec![("via", Json::str("dml"))],
        );
        g
    }

    #[test]
    fn what_touches_groups_incoming_edges() {
        let g = sample();
        let out = what_touches(&g, "sobject::Case__c", false).unwrap();
        // The DECLARES (from the file/owner) plus the two USES_TYPE referrers.
        assert!(out.contains("USES_TYPE"));
        assert!(out.contains("flow_element::Intake.Create_Case"));
        assert!(out.contains("apex::CaseSvc.touch"));
        // Both USES_TYPE referrers are grouped under one kind heading.
        assert!(out.contains("USES_TYPE (2)"));
    }

    #[test]
    fn what_touches_resolves_by_name() {
        let g = sample();
        // "Case__c" is the *name* of sobject::Case__c (and also the name of the
        // field on Referral, but here the field name is "Referral__c").
        let by_name = what_touches(&g, "Case__c", false).unwrap();
        let by_id = what_touches(&g, "sobject::Case__c", false).unwrap();
        assert_eq!(by_name, by_id);
    }

    #[test]
    fn uses_returns_outgoing_edges() {
        let g = sample();
        let out = uses(&g, "sobject_field::Case__c.Referral__c", false).unwrap();
        assert!(out.contains("USES_TYPE"));
        assert!(out.contains("sobject::Referral__c"));
    }

    #[test]
    fn blast_radius_is_transitive_and_deterministic() {
        let g = sample();
        // Referral is referenced by the field, which is declared by Case, which
        // is touched by the flow element and the apex method (transitively via
        // Case). Reverse reachability from Referral should reach all of them.
        let out = blast_radius(&g, "sobject::Referral__c", false).unwrap();
        assert!(out.contains("sobject_field::Case__c.Referral__c"));
        assert!(out.contains("sobject::Case__c"));
        assert!(out.contains("flow_element::Intake.Create_Case"));
        assert!(out.contains("apex::CaseSvc.touch"));
        // The seed itself is not in the affected set.
        assert!(!out.contains("  [Type] sobject::Referral__c\n"));
        // Deterministic across runs.
        let again = blast_radius(&g, "sobject::Referral__c", false).unwrap();
        assert_eq!(out, again);
    }

    #[test]
    fn blast_radius_json_reports_count() {
        let g = sample();
        let out = blast_radius(&g, "sobject::Case__c", true).unwrap();
        assert!(out.contains("\"query\":\"blast-radius\""));
        assert!(out.contains("\"affected_count\":"));
        // Case is touched by the flow element and apex method (directly) and the
        // flow (via the element's DECLARES-parent). At least those three.
        assert!(out.contains("apex::CaseSvc.touch"));
        assert!(out.contains("flow_element::Intake.Create_Case"));
    }

    #[test]
    fn deepest_flows_sorted_desc_and_flags_deep() {
        let mut g = sample();
        g.upsert_node(
            "flow::Shallow",
            ont::FUNCTION,
            "Shallow",
            vec![
                ("type_kind", Json::str("flow")),
                ("depth", Json::U64(2)),
                ("element_count", Json::U64(3)),
            ],
        );
        let out = deepest_flows(&g, false);
        // Deepest (Intake, depth 11) appears before the shallow one.
        let deep_pos = out.find("flow::Intake").unwrap();
        let shallow_pos = out.find("flow::Shallow").unwrap();
        assert!(deep_pos < shallow_pos);
        // depth 11 >= 10 → flagged DEEP; depth 2 not.
        assert!(
            out.contains("flow::Intake  DEEP")
                || out.contains("flow::Intake") && out.contains("DEEP")
        );
    }

    #[test]
    fn unknown_target_errors() {
        let g = sample();
        assert!(what_touches(&g, "no::such::node", false).is_err());
        assert!(uses(&g, "no::such::node", false).is_err());
        assert!(blast_radius(&g, "no::such::node", false).is_err());
    }
}
