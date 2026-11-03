//! The workflow-spec extractor: turn each declarative workflow into a
//! **reviewable specification** (TT-79, gap G6).
//!
//! The base graph holds a workflow as a *shape*: a flow [`Function`] node
//! (`type_kind: "flow"`, with `depth`/`element_count`/`label`), its per-element
//! [`Function`] nodes (`type_kind: "flow_element"`, each carrying `element_kind`
//! and — from TT-77 — its captured logic as JSON-in-property:
//! `conditions`/`assignments`/`inputAssignments`/`filters`/`queriedFields`),
//! and the edges between them: [`FLOWS_TO`] (control), [`CALLS`] (Apex/subflow),
//! [`USES_TYPE`] (SObject touched) and [`DATA_DEP`] (intra-flow data flow).
//!
//! This pass collapses that shape into **one node per flow** (ontology kind
//! [`Function`], tagged `view: "workflow_spec"`) whose properties are the whole
//! spec:
//!
//! - `trigger` — the entry element (the `<start>`, else the derived root).
//! - `steps` — a deterministic JSON array, in `FLOWS_TO` order from the entry,
//!   of `{name, kind, logic, touches, calls, data_deps}` per element. `logic`
//!   carries the TT-77 captures verbatim; `touches`/`calls`/`data_deps` are the
//!   sorted, de-duplicated targets of the element's `USES_TYPE`/`CALLS`/
//!   `DATA_DEP` edges.
//! - `depth` — the flow's `depth` (longest acyclic element path, TT-65).
//! - `markdown` — the same spec rendered as human-readable text, the clean-room
//!   rebuild input.
//!
//! **Step ordering** is a deterministic walk of `FLOWS_TO` from the entry:
//! iterative DFS pre-order, successors visited in sorted id order, roots being
//! the `<start>` element (else the in-degree-0 elements, else all — sorted).
//! Any element unreachable from the roots is appended in sorted name order, so
//! the order is always total and byte-stable; a fully connected chain reads in
//! execution order, and a graph with no derivable order falls back to sorted
//! names.
//!
//! Pure and deterministic: it walks the `BTreeMap`-ordered node/edge iterators,
//! sorts every collected set, and writes through the sorted [`Graph`] API.
//!
//! [`Function`]: crate::ir::ontology::node::FUNCTION
//! [`FLOWS_TO`]: crate::ir::ontology::edge::FLOWS_TO
//! [`CALLS`]: crate::ir::ontology::edge::CALLS
//! [`USES_TYPE`]: crate::ir::ontology::edge::USES_TYPE
//! [`DATA_DEP`]: crate::ir::ontology::edge::DATA_DEP

use std::collections::{BTreeMap, BTreeSet};

use crate::core::json::Json;
use crate::graph::{Graph, GraphNode};
use crate::ir::ontology::{edge, node as ont};

use super::Extractor;

/// Property key marking a node as belonging to the workflow-spec view.
const VIEW: &str = "workflow_spec";

/// TT-77 logic property keys, in a fixed order, carried verbatim into a step's
/// `logic` object.
const LOGIC_KEYS: &[&str] = &[
    "conditions",
    "assignments",
    "inputAssignments",
    "filters",
    "queriedFields",
];

/// Serialize every declarative workflow into a per-flow specification.
pub struct WorkflowSpecExtractor;

impl Extractor for WorkflowSpecExtractor {
    fn name(&self) -> &'static str {
        "workflow-spec"
    }

    fn extract(&self, graph: &Graph) -> Graph {
        let mut out = Graph::new();

        // id -> node, for target-name lookups and element property reads.
        let by_id: BTreeMap<&str, &GraphNode> = graph.nodes().map(|n| (n.id.as_str(), n)).collect();

        // Per-element outbound facts, collected once. FLOWS_TO keeps target ids
        // (for the ordering walk); the others resolve to sorted target *names*.
        let mut flows_to: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
        let mut touches: BTreeMap<&str, BTreeSet<String>> = BTreeMap::new();
        let mut calls: BTreeMap<&str, BTreeSet<String>> = BTreeMap::new();
        let mut data_deps: BTreeMap<&str, BTreeSet<String>> = BTreeMap::new();
        for e in graph.edges() {
            let name_of = |id: &str| -> String {
                by_id
                    .get(id)
                    .map(|n| n.name.clone())
                    .unwrap_or_else(|| id.to_string())
            };
            match e.kind {
                edge::FLOWS_TO => {
                    flows_to
                        .entry(e.from.as_str())
                        .or_default()
                        .insert(e.to.as_str());
                }
                edge::USES_TYPE => {
                    touches
                        .entry(e.from.as_str())
                        .or_default()
                        .insert(name_of(&e.to));
                }
                edge::CALLS => {
                    calls
                        .entry(e.from.as_str())
                        .or_default()
                        .insert(name_of(&e.to));
                }
                edge::DATA_DEP => {
                    data_deps
                        .entry(e.from.as_str())
                        .or_default()
                        .insert(name_of(&e.to));
                }
                _ => {}
            }
        }

        // flow id -> its element ids, from DECLARES edges whose source is a flow
        // and whose target is a flow_element node.
        let mut flow_elements: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
        for e in graph.edges().filter(|e| e.kind == edge::DECLARES) {
            let Some(src) = by_id.get(e.from.as_str()) else {
                continue;
            };
            if type_kind(src) != "flow" {
                continue;
            }
            if by_id
                .get(e.to.as_str())
                .map(|n| type_kind(n) == "flow_element")
                .unwrap_or(false)
            {
                flow_elements
                    .entry(e.from.as_str())
                    .or_default()
                    .insert(e.to.as_str());
            }
        }

        // One spec node per flow.
        for flow in graph.nodes().filter(|n| type_kind(n) == "flow") {
            let elements = flow_elements
                .get(flow.id.as_str())
                .cloned()
                .unwrap_or_default();
            let flow_name = flow.name.clone();
            let start_id = format!("flow_element::{flow_name}.start");
            let start = elements
                .contains(start_id.as_str())
                .then_some(start_id.as_str());

            let order = order_steps(&elements, &flows_to, start);

            // Build the structured steps + the markdown in a single pass.
            let depth = flow.props.get("depth").cloned().unwrap_or(Json::U64(0));
            let mut md = format!("Flow {flow_name} (depth {})\n", render_num(&depth));
            let mut steps: Vec<Json> = Vec::new();
            for (i, eid) in order.iter().enumerate() {
                let el = by_id.get(*eid).copied();
                let name = el
                    .map(|n| n.name.clone())
                    .unwrap_or_else(|| (*eid).to_string());
                let kind = el.map(element_kind).unwrap_or("").to_string();

                // Logic: the TT-77 captures, carried verbatim, in a fixed order.
                let mut logic_pairs: Vec<(&'static str, Json)> = Vec::new();
                if let Some(n) = el {
                    for &k in LOGIC_KEYS {
                        if let Some(v) = n.props.get(k) {
                            logic_pairs.push((static_key(k), v.clone()));
                        }
                    }
                }
                let logic = if logic_pairs.is_empty() {
                    Json::Null
                } else {
                    Json::obj(logic_pairs)
                };

                let touch_v = sorted_strings(touches.get(*eid));
                let call_v = sorted_strings(calls.get(*eid));
                let dep_v = sorted_strings(data_deps.get(*eid));

                steps.push(Json::obj([
                    ("name", Json::str(name.clone())),
                    ("kind", Json::str(kind.clone())),
                    ("logic", logic.clone()),
                    (
                        "touches",
                        Json::Array(touch_v.iter().cloned().map(Json::str).collect()),
                    ),
                    (
                        "calls",
                        Json::Array(call_v.iter().cloned().map(Json::str).collect()),
                    ),
                    (
                        "data_deps",
                        Json::Array(dep_v.iter().cloned().map(Json::str).collect()),
                    ),
                ]));

                // Markdown line for this step.
                md.push_str(&format!(" {}. {name} [{kind}]", i + 1));
                if let Some(text) = el.and_then(render_logic) {
                    md.push_str(" — ");
                    md.push_str(&text);
                }
                if !touch_v.is_empty() {
                    md.push_str(&format!(" — touches {}", touch_v.join(", ")));
                }
                if !call_v.is_empty() {
                    md.push_str(&format!(" — calls {}", call_v.join(", ")));
                }
                if !dep_v.is_empty() {
                    md.push_str(&format!(" — data_deps {}", dep_v.join(", ")));
                }
                md.push('\n');
            }

            let trigger = order
                .first()
                .and_then(|id| by_id.get(*id))
                .map(|n| Json::str(n.name.clone()))
                .unwrap_or(Json::Null);

            let mut props = vec![
                ("view", Json::str(VIEW)),
                ("trigger", trigger),
                ("steps", Json::Array(steps)),
                ("depth", depth),
                ("markdown", Json::str(md)),
            ];
            if let Some(label) = flow.props.get("label") {
                props.push(("label", label.clone()));
            }
            out.upsert_node(
                format!("workflow_spec::{flow_name}"),
                ont::FUNCTION,
                flow_name.clone(),
                props,
            );
        }

        out
    }
}

/// A node's `type_kind` property as a string slice, or `""` when absent.
fn type_kind(n: &GraphNode) -> &str {
    match n.props.get("type_kind") {
        Some(Json::Str(s)) => s.as_str(),
        _ => "",
    }
}

/// A flow element's `element_kind` (the Salesforce XML tag) as a string slice.
fn element_kind(n: &GraphNode) -> &str {
    match n.props.get("element_kind") {
        Some(Json::Str(s)) => s.as_str(),
        _ => "",
    }
}

/// Deterministic total order over a flow's elements: DFS pre-order along
/// `FLOWS_TO` from the entry, successors in sorted id order, then any element
/// unreachable from the roots appended in sorted order.
fn order_steps<'a>(
    elements: &BTreeSet<&'a str>,
    flows_to: &BTreeMap<&'a str, BTreeSet<&'a str>>,
    start: Option<&'a str>,
) -> Vec<&'a str> {
    // Adjacency restricted to this flow's elements, sorted + de-duplicated.
    let mut adj: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    let mut has_in: BTreeSet<&str> = BTreeSet::new();
    for &from in elements {
        if let Some(tos) = flows_to.get(from) {
            let succ: Vec<&str> = tos
                .iter()
                .copied()
                .filter(|t| elements.contains(t))
                .collect();
            for &t in &succ {
                has_in.insert(t);
            }
            if !succ.is_empty() {
                adj.insert(from, succ);
            }
        }
    }

    // Roots: the <start>, else in-degree-0 elements, else all — always sorted,
    // start first, so the walk is deterministic.
    let mut roots: Vec<&str> = Vec::new();
    if let Some(s) = start {
        roots.push(s);
    }
    for &n in elements {
        if Some(n) == start {
            continue;
        }
        if !has_in.contains(n) {
            roots.push(n);
        }
    }
    if roots.is_empty() {
        roots = elements.iter().copied().collect();
    }

    let mut visited: BTreeSet<&str> = BTreeSet::new();
    let mut order: Vec<&str> = Vec::new();
    for &root in &roots {
        if visited.contains(root) {
            continue;
        }
        let mut stack = vec![root];
        while let Some(n) = stack.pop() {
            if !visited.insert(n) {
                continue;
            }
            order.push(n);
            // Push successors in reverse so the smallest id is popped first.
            if let Some(succ) = adj.get(n) {
                for &s in succ.iter().rev() {
                    if !visited.contains(s) {
                        stack.push(s);
                    }
                }
            }
        }
    }
    // Unreachable elements (e.g. pure cycles with no in-degree-0 root), sorted.
    for &n in elements {
        if !visited.contains(n) {
            order.push(n);
        }
    }
    order
}

/// The sorted vector behind an optional set, or empty.
fn sorted_strings(set: Option<&BTreeSet<String>>) -> Vec<String> {
    set.map(|s| s.iter().cloned().collect()).unwrap_or_default()
}

/// A numeric `Json` rendered for prose (`5`), else `?`.
fn render_num(j: &Json) -> String {
    match j {
        Json::U64(n) => n.to_string(),
        Json::I64(n) => n.to_string(),
        _ => "?".to_string(),
    }
}

/// Map a known logic key back to its `&'static str` (keys come from a static
/// slice, so this is a total, allocation-free lookup).
fn static_key(k: &str) -> &'static str {
    LOGIC_KEYS.iter().copied().find(|&s| s == k).unwrap_or("")
}

// ---- Human-readable logic rendering -----------------------------------------

/// A field of a JSON object as an owned string, or `""`.
fn obj_str(o: &Json, key: &str) -> String {
    match o {
        Json::Object(m) => match m.get(key) {
            Some(Json::Str(s)) => s.clone(),
            _ => String::new(),
        },
        _ => String::new(),
    }
}

/// A nested JSON child of an object, if present.
fn obj_get<'a>(o: &'a Json, key: &str) -> Option<&'a Json> {
    match o {
        Json::Object(m) => m.get(key),
        _ => None,
    }
}

/// A TT-77 `value` wrapper (`{type, value}`) as text; element references are
/// wrapped in braces to flag the data dependency.
fn render_value(v: Option<&Json>) -> String {
    let Some(v) = v else {
        return String::new();
    };
    let val = obj_str(v, "value");
    if obj_str(v, "type") == "elementReference" {
        format!("{{{val}}}")
    } else {
        val
    }
}

/// A one-line, human-readable summary of an element's TT-77 logic, or `None`.
fn render_logic(n: &GraphNode) -> Option<String> {
    let mut parts: Vec<String> = Vec::new();
    if let Some(Json::Array(rules)) = n.props.get("conditions") {
        parts.push(render_conditions(rules));
    }
    if let Some(Json::Array(items)) = n.props.get("assignments") {
        parts.push(render_assignments(items));
    }
    if let Some(Json::Array(ia)) = n.props.get("inputAssignments") {
        parts.push(render_inputs(ia));
    }
    if let Some(Json::Array(f)) = n.props.get("filters") {
        parts.push(render_filters(f));
    }
    if let Some(Json::Array(q)) = n.props.get("queriedFields") {
        let names: Vec<String> = q
            .iter()
            .filter_map(|j| match j {
                Json::Str(s) => Some(s.clone()),
                _ => None,
            })
            .collect();
        parts.push(format!("read [{}]", names.join(", ")));
    }
    let joined = parts
        .into_iter()
        .filter(|p| !p.is_empty())
        .collect::<Vec<_>>()
        .join("; ");
    (!joined.is_empty()).then_some(joined)
}

fn render_conditions(rules: &[Json]) -> String {
    let mut out: Vec<String> = Vec::new();
    for rule in rules {
        let logic = obj_str(rule, "conditionLogic");
        let sep = if logic.is_empty() {
            " and ".to_string()
        } else {
            format!(" {logic} ")
        };
        let conds = match obj_get(rule, "conditions") {
            Some(Json::Array(cs)) => cs
                .iter()
                .map(|c| {
                    format!(
                        "{} {} {}",
                        obj_str(c, "left"),
                        obj_str(c, "operator"),
                        render_value(obj_get(c, "right"))
                    )
                })
                .collect::<Vec<_>>()
                .join(&sep),
            _ => String::new(),
        };
        let target = obj_str(rule, "connector");
        if target.is_empty() {
            out.push(format!("if {conds}"));
        } else {
            out.push(format!("if {conds} → {target}"));
        }
    }
    out.join("; ")
}

fn render_assignments(items: &[Json]) -> String {
    let body = items
        .iter()
        .map(|it| {
            format!(
                "{} {} {}",
                obj_str(it, "assignTo"),
                obj_str(it, "operator"),
                render_value(obj_get(it, "value"))
            )
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!("set {body}")
}

fn render_inputs(items: &[Json]) -> String {
    let body = items
        .iter()
        .map(|it| {
            format!(
                "{}={}",
                obj_str(it, "field"),
                render_value(obj_get(it, "value"))
            )
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!("write {body}")
}

fn render_filters(items: &[Json]) -> String {
    let body = items
        .iter()
        .map(|it| {
            format!(
                "{} {} {}",
                obj_str(it, "field"),
                obj_str(it, "operator"),
                render_value(obj_get(it, "value"))
            )
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!("where {body}")
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A hand-built base graph in the exact shape the Salesforce front end
    /// emits: a flow with a `<start>` and three elements chained by `FLOWS_TO`,
    /// carrying a decision's conditions, an assignment's items, a record op's
    /// `USES_TYPE`, and an `actionCalls` `CALLS`.
    fn sample_base() -> Graph {
        let mut g = Graph::new();
        // Flow node.
        g.upsert_node(
            "flow::Care",
            ont::FUNCTION,
            "Care",
            vec![
                ("type_kind", Json::str("flow")),
                ("label", Json::str("Care Flow")),
                ("depth", Json::U64(4)),
                ("element_count", Json::U64(4)),
            ],
        );
        // Elements: start -> Decide -> Set -> Update.
        let elems: &[(&str, &str)] = &[
            ("start", "start"),
            ("Decide", "decisions"),
            ("Set", "assignments"),
            ("Update", "recordUpdates"),
        ];
        for (name, kind) in elems {
            g.upsert_node(
                format!("flow_element::Care.{name}"),
                ont::FUNCTION,
                *name,
                vec![
                    ("type_kind", Json::str("flow_element")),
                    ("element_kind", Json::str(*kind)),
                    ("flow", Json::str("Care")),
                ],
            );
            g.add_edge(
                "flow::Care",
                edge::DECLARES,
                format!("flow_element::Care.{name}"),
                vec![],
            );
        }
        // Control flow: start -> Decide -> Set -> Update.
        for (from, to) in [("start", "Decide"), ("Decide", "Set"), ("Set", "Update")] {
            g.add_edge(
                format!("flow_element::Care.{from}"),
                edge::FLOWS_TO,
                format!("flow_element::Care.{to}"),
                vec![("via", Json::str("connector"))],
            );
        }
        // Decision logic (conditions).
        g.upsert_node(
            "flow_element::Care.Decide",
            ont::FUNCTION,
            "Decide",
            vec![(
                "conditions",
                Json::Array(vec![Json::obj([
                    ("name", Json::str("Eligible")),
                    ("conditionLogic", Json::str("and")),
                    (
                        "conditions",
                        Json::Array(vec![Json::obj([
                            ("left", Json::str("Patient.Status__c")),
                            ("operator", Json::str("EqualTo")),
                            (
                                "right",
                                Json::obj([
                                    ("type", Json::str("stringValue")),
                                    ("value", Json::str("Active")),
                                ]),
                            ),
                        ])]),
                    ),
                    ("connector", Json::str("Set")),
                ])]),
            )],
        );
        // Assignment logic (assignments) with a data ref.
        g.upsert_node(
            "flow_element::Care.Set",
            ont::FUNCTION,
            "Set",
            vec![(
                "assignments",
                Json::Array(vec![Json::obj([
                    ("assignTo", Json::str("Case.OwnerId")),
                    ("operator", Json::str("Assign")),
                    (
                        "value",
                        Json::obj([
                            ("type", Json::str("elementReference")),
                            ("value", Json::str("Decide")),
                        ]),
                    ),
                ])]),
            )],
        );
        // Data dep Set -> Decide (consumer -> producer).
        g.add_edge(
            "flow_element::Care.Set",
            edge::DATA_DEP,
            "flow_element::Care.Decide",
            vec![("via", Json::str("elementReference"))],
        );
        // Record op touches an SObject.
        g.upsert_node(
            "sobject::Case",
            ont::TYPE,
            "Case",
            vec![("type_kind", Json::str("sobject"))],
        );
        g.add_edge(
            "flow_element::Care.Update",
            edge::USES_TYPE,
            "sobject::Case",
            vec![("via", Json::str("recordUpdates"))],
        );
        // An action call from Decide.
        g.upsert_node(
            "unresolved::sf_action::Notifier",
            ont::UNRESOLVED,
            "Notifier",
            vec![("reference_kind", Json::str("salesforce_action"))],
        );
        g.add_edge(
            "flow_element::Care.Decide",
            edge::CALLS,
            "unresolved::sf_action::Notifier",
            vec![("via", Json::str("actionCalls"))],
        );
        g
    }

    #[test]
    fn emits_one_ordered_spec_per_flow() {
        let derived = WorkflowSpecExtractor.extract(&sample_base());
        assert_eq!(derived.count_nodes_of(ont::FUNCTION), 1);

        let spec = derived
            .nodes()
            .find(|n| n.id == "workflow_spec::Care")
            .expect("spec node");
        assert_eq!(spec.props.get("view"), Some(&Json::str(VIEW)));
        assert_eq!(spec.props.get("trigger"), Some(&Json::str("start")));
        assert_eq!(spec.props.get("depth"), Some(&Json::U64(4)));

        // Steps are in FLOWS_TO order: start, Decide, Set, Update.
        let Json::Array(steps) = spec.props.get("steps").expect("steps") else {
            panic!("steps must be an array");
        };
        let names: Vec<String> = steps.iter().map(|s| obj_str(s, "name")).collect();
        assert_eq!(names, ["start", "Decide", "Set", "Update"]);

        // The decision step carries its captured conditions logic + its CALLS.
        let decide = &steps[1];
        assert!(matches!(obj_get(decide, "logic"), Some(Json::Object(_))));
        let Some(Json::Array(calls)) = obj_get(decide, "calls") else {
            panic!("calls array");
        };
        assert_eq!(calls, &vec![Json::str("Notifier")]);

        // The assignment step records its DATA_DEP; the update step its touch.
        let set = &steps[2];
        let Some(Json::Array(deps)) = obj_get(set, "data_deps") else {
            panic!("data_deps array");
        };
        assert_eq!(deps, &vec![Json::str("Decide")]);
        let update = &steps[3];
        let Some(Json::Array(touch)) = obj_get(update, "touches") else {
            panic!("touches array");
        };
        assert_eq!(touch, &vec![Json::str("Case")]);

        // The markdown is human-readable and ordered.
        let Some(Json::Str(md)) = spec.props.get("markdown") else {
            panic!("markdown string");
        };
        assert!(md.starts_with("Flow Care (depth 4)\n"), "{md}");
        assert!(md.contains(" 1. start [start]"), "{md}");
        assert!(md.contains(" 2. Decide [decisions]"), "{md}");
        assert!(md.contains("Patient.Status__c EqualTo Active"), "{md}");
        assert!(md.contains("calls Notifier"), "{md}");
        assert!(md.contains("touches Case"), "{md}");
    }

    #[test]
    fn deterministic_across_runs() {
        let base = sample_base();
        let a = WorkflowSpecExtractor.extract(&base).to_jsonl();
        let b = WorkflowSpecExtractor.extract(&base).to_jsonl();
        assert_eq!(a, b);
        assert!(!a.is_empty());
    }

    #[test]
    fn falls_back_to_sorted_names_without_a_start() {
        // No <start>, no connectors: order is the sorted element names.
        let mut g = Graph::new();
        g.upsert_node(
            "flow::Bare",
            ont::FUNCTION,
            "Bare",
            vec![("type_kind", Json::str("flow")), ("depth", Json::U64(1))],
        );
        for name in ["Charlie", "Alpha", "Bravo"] {
            g.upsert_node(
                format!("flow_element::Bare.{name}"),
                ont::FUNCTION,
                name,
                vec![
                    ("type_kind", Json::str("flow_element")),
                    ("element_kind", Json::str("assignments")),
                ],
            );
            g.add_edge(
                "flow::Bare",
                edge::DECLARES,
                format!("flow_element::Bare.{name}"),
                vec![],
            );
        }
        let spec = WorkflowSpecExtractor.extract(&g);
        let node = spec
            .nodes()
            .find(|n| n.id == "workflow_spec::Bare")
            .unwrap();
        let Json::Array(steps) = node.props.get("steps").unwrap() else {
            panic!();
        };
        let names: Vec<String> = steps.iter().map(|s| obj_str(s, "name")).collect();
        assert_eq!(names, ["Alpha", "Bravo", "Charlie"]);
        assert_eq!(node.props.get("trigger"), Some(&Json::str("Alpha")));
    }
}
