//! TT-87 rebuild-brief: the "hand it to an agent" deliverable.
//!
//! Where [`crate::report`] renders the whole org and [`crate::query`] answers a
//! targeted question, this assembles ONE self-contained markdown document for a
//! *single* Salesforce workflow — everything an agent needs to rebuild that flow
//! on another platform (Medplum) without ever opening the org.
//!
//! The brief is assembled from two sources, honestly separated:
//!
//! - **the graph** (scope + resolution): which SObjects/fields the flow touches
//!   (its elements' `USES_TYPE` edges), the ordered element graph (`FLOWS_TO`),
//!   the per-element logic captured by TT-77 (conditions / assignments / query
//!   filters+fields / DML field-maps), and the flow→Apex resolution the TT-62
//!   linker produced (`resolved_by="linker"` `CALLS` edges);
//! - **the source files** (actual content + provenance): the element line spans
//!   in the `.flow-meta.xml` (a `file:lineStart-lineEnd` cite per step) and the
//!   inlined body of any resolved Apex method (sliced from its `.cls` by the
//!   apex `span_start`/`span_end` byte offsets).
//!
//! Source access goes through an injected reader (`&dyn Fn(&str) ->
//! Option<String>`) keyed by a File node's `path` prop, so the graph-only
//! assembly is unit-testable with a canned reader (or `|_| None`) and the CLI
//! wires in a real `dir.join(path)` filesystem read. The whole document is a
//! deterministic function of `(graph, reader)`: every collection is a
//! `BTreeMap`/`BTreeSet` and every walk sorts before rendering, so the same
//! inputs always produce byte-identical markdown.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::Path;

use crate::core::json::Json;
use crate::graph::{Graph, GraphNode};
use crate::ir::ontology::{edge, node as ont};

/// A source reader: given a File node's `path` prop, return the file contents (or
/// `None` when it cannot be read). Abstracted so assembly is testable offline.
type Reader<'a> = dyn Fn(&str) -> Option<String> + 'a;

/// Public entry point for the CLI. Analyzes nothing itself — the caller passes an
/// already-built `graph` and the corpus `dir` (for the source reader). `target`
/// is a flow name (`DeepIntake`) or a flow node id (`flow::DeepIntake`).
pub fn rebuild_brief(graph: &Graph, dir: &Path, target: &str) -> Result<String, String> {
    let flow_id = resolve_flow(graph, target)?;
    let dir = dir.to_path_buf();
    let read = move |rel: &str| -> Option<String> { std::fs::read_to_string(dir.join(rel)).ok() };
    Ok(assemble(graph, &flow_id, &read))
}

/// Resolve a user target to a flow node id. An exact id match wins; otherwise the
/// unique flow whose *name* equals `target`. Only `Function` nodes with
/// `type_kind="flow"` qualify (never a subflow reference or an element).
fn resolve_flow(graph: &Graph, target: &str) -> Result<String, String> {
    if let Some(n) = graph.nodes().find(|n| n.id == target) {
        if is_flow(n) {
            return Ok(n.id.clone());
        }
    }
    let mut hits: Vec<String> = graph
        .nodes()
        .filter(|n| is_flow(n) && n.name == target)
        .map(|n| n.id.clone())
        .collect();
    hits.sort();
    hits.dedup();
    match hits.len() {
        0 => Err(format!("no flow matching '{target}'")),
        1 => Ok(hits.remove(0)),
        _ => Err(format!(
            "'{target}' is ambiguous: {} (pass a flow id)",
            hits.join(", ")
        )),
    }
}

fn is_flow(n: &GraphNode) -> bool {
    n.kind == ont::FUNCTION && prop_str(n.props.get("type_kind")) == "flow"
}

/// Assemble the whole markdown brief. Deterministic in `(graph, read)`.
fn assemble(graph: &Graph, flow_id: &str, read: &Reader) -> String {
    let flow = graph.nodes().find(|n| n.id == flow_id).expect("flow node");
    let flow_name = flow.name.clone();

    // The flow's declared elements: real element nodes only (unresolved connector
    // targets are `FLOWS_TO`-reachable but never DECLARES-d).
    let elements: BTreeMap<String, &GraphNode> = graph
        .edges()
        .filter(|e| e.kind == edge::DECLARES && e.from == flow_id)
        .filter_map(|e| graph.nodes().find(|n| n.id == e.to))
        .filter(|n| n.kind == ont::FUNCTION && prop_str(n.props.get("type_kind")) == "flow_element")
        .map(|n| (n.id.clone(), n))
        .collect();

    // The flow's own source file (for line cites) — the File node that DECLARES it.
    let flow_path = declaring_file_path(graph, flow_id);
    let flow_src = flow_path.as_deref().and_then(read);

    let order = ordered_steps(graph, &flow_name, &elements);

    let mut out = String::new();
    header_section(flow, flow_path.as_deref(), &mut out);
    data_model_section(graph, &elements, &mut out);
    steps_section(&elements, &order, flow_src.as_deref(), &mut out);
    called_code_section(graph, &elements, read, &mut out);
    medplum_section(graph, &elements, &order, &mut out);
    out
}

// --- header -----------------------------------------------------------------

fn header_section(flow: &GraphNode, path: Option<&str>, out: &mut String) {
    let _ = writeln!(out, "# Rebuild brief: {}\n", flow.name);
    let ptype = prop_str(flow.props.get("process_type"));
    let ptype = if ptype.is_empty() {
        "(unspecified)"
    } else {
        ptype
    };
    let _ = writeln!(out, "- **Flow:** {}", flow.name);
    let _ = writeln!(
        out,
        "- **Type:** {} / processType `{}`",
        prop_str(flow.props.get("type_kind")),
        ptype
    );
    let _ = writeln!(out, "- **Source:** `{}`", path.unwrap_or("(unknown)"));
    if let Some(l) = flow.props.get("label").and_then(as_str) {
        let _ = writeln!(out, "- **Label:** {l}");
    }
    let _ = writeln!(out, "- **Depth:** {}", prop_u64(flow.props.get("depth")));
    let _ = writeln!(
        out,
        "- **Elements:** {}\n",
        prop_u64(flow.props.get("element_count"))
    );
}

// --- scoped data model ------------------------------------------------------

/// Only the SObjects this flow touches (its elements' `USES_TYPE` targets), each
/// with the fields the flow actually uses and their `field_type` where the graph
/// knows it — not the whole org.
fn data_model_section(graph: &Graph, elements: &BTreeMap<String, &GraphNode>, out: &mut String) {
    // object name -> set of field names the flow uses on it.
    let mut fields_by_obj: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    // Seed every touched object (via USES_TYPE to an sobject node), even fieldless.
    for (eid, el) in elements {
        for tgt in uses_type_objects(graph, eid) {
            fields_by_obj.entry(tgt).or_default();
        }
        collect_element_fields(graph, eid, el, &mut fields_by_obj);
    }

    out.push_str("## Scoped data model\n\n");
    if fields_by_obj.is_empty() {
        out.push_str("_This flow touches no SObjects directly._\n\n");
        return;
    }
    for (obj, fields) in &fields_by_obj {
        let _ = writeln!(out, "### {obj}\n");
        if fields.is_empty() {
            out.push_str("_no specific fields referenced_\n\n");
            continue;
        }
        for field in fields {
            let ftype = field_type(graph, obj, field);
            let _ = writeln!(out, "- `{field}` — {ftype}");
        }
        out.push('\n');
    }
}

/// The sobject names an element depends on via `USES_TYPE` (the record op's object).
fn uses_type_objects(graph: &Graph, element_id: &str) -> Vec<String> {
    let mut out: Vec<String> = graph
        .edges()
        .filter(|e| e.kind == edge::USES_TYPE && e.from == element_id)
        .filter_map(|e| e.to.strip_prefix("sobject::").map(str::to_string))
        .collect();
    out.sort();
    out.dedup();
    out
}

/// Attribute an element's referenced fields to the object it operates on. Record
/// ops (queriedFields / filters.field / inputAssignments.field) attach to the
/// element's `USES_TYPE` object; dotted `Object.Field` references anywhere in the
/// element's logic attach to that object when it is one the flow touches.
fn collect_element_fields(
    graph: &Graph,
    element_id: &str,
    el: &GraphNode,
    fields_by_obj: &mut BTreeMap<String, BTreeSet<String>>,
) {
    let objects = uses_type_objects(graph, element_id);
    let primary = objects.first().cloned();

    if let Some(obj) = &primary {
        let entry = fields_by_obj.entry(obj.clone()).or_default();
        for f in json_strings(el.props.get("queriedFields")) {
            entry.insert(f);
        }
        for f in field_names(el.props.get("filters")) {
            entry.insert(f);
        }
        for f in field_names(el.props.get("inputAssignments")) {
            entry.insert(f);
        }
    }

    // Dotted Object.Field references in assignments / conditions, when the head is
    // an object this flow touches (elsewhere it is an element binding, not a field).
    let known: BTreeSet<&str> = fields_by_obj.keys().map(String::as_str).collect();
    let known: BTreeSet<String> = known.iter().map(|s| s.to_string()).collect();
    for dotted in dotted_refs(el) {
        if let Some((obj, field)) = dotted.split_once('.') {
            if known.contains(obj) {
                fields_by_obj
                    .entry(obj.to_string())
                    .or_default()
                    .insert(field.to_string());
            }
        }
    }
}

/// Every `Object.Field` reference in an element's captured logic: assignment
/// targets, and condition left references.
fn dotted_refs(el: &GraphNode) -> Vec<String> {
    let mut out = Vec::new();
    if let Some(Json::Array(items)) = el.props.get("assignments") {
        for it in items {
            if let Some(s) = obj_get(it, "assignTo").and_then(as_str) {
                out.push(s.to_string());
            }
        }
    }
    if let Some(Json::Array(rules)) = el.props.get("conditions") {
        for rule in rules {
            if let Some(Json::Array(conds)) = obj_get(rule, "conditions") {
                for c in conds {
                    if let Some(s) = obj_get(c, "left").and_then(as_str) {
                        out.push(s.to_string());
                    }
                }
            }
        }
    }
    out
}

/// The `field_type` prop of `sobject_field::<Obj>.<Field>`, or `type unknown`.
fn field_type(graph: &Graph, obj: &str, field: &str) -> String {
    let id = format!("sobject_field::{obj}.{field}");
    graph
        .nodes()
        .find(|n| n.id == id)
        .and_then(|n| n.props.get("field_type"))
        .and_then(as_str)
        .map(|t| format!("type `{t}`"))
        .unwrap_or_else(|| "type unknown".to_string())
}

// --- steps in execution order -----------------------------------------------

/// Execution order: a deterministic preorder DFS from `start` over `FLOWS_TO`
/// (successors visited in sorted order), then any element not reachable from the
/// start appended in id (== name) order. Never loops (visited set), never drops.
fn ordered_steps(
    graph: &Graph,
    flow_name: &str,
    elements: &BTreeMap<String, &GraphNode>,
) -> Vec<String> {
    let mut succ: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    for e in graph.edges().filter(|e| e.kind == edge::FLOWS_TO) {
        if elements.contains_key(&e.from) && elements.contains_key(&e.to) {
            succ.entry(e.from.as_str())
                .or_default()
                .insert(e.to.as_str());
        }
    }

    let mut order: Vec<String> = Vec::new();
    let mut visited: BTreeSet<String> = BTreeSet::new();
    let start_id = format!("flow_element::{flow_name}.start");
    if elements.contains_key(&start_id) {
        dfs(&start_id, &succ, &mut visited, &mut order);
    }
    // Leftovers (unreachable from start, or no start) in deterministic id order.
    for id in elements.keys() {
        if !visited.contains(id) {
            dfs(id, &succ, &mut visited, &mut order);
        }
    }
    order
}

fn dfs(
    node: &str,
    succ: &BTreeMap<&str, BTreeSet<&str>>,
    visited: &mut BTreeSet<String>,
    order: &mut Vec<String>,
) {
    if !visited.insert(node.to_string()) {
        return;
    }
    order.push(node.to_string());
    if let Some(nexts) = succ.get(node) {
        for n in nexts {
            dfs(n, succ, visited, order);
        }
    }
}

fn steps_section(
    elements: &BTreeMap<String, &GraphNode>,
    order: &[String],
    flow_src: Option<&str>,
    out: &mut String,
) {
    out.push_str("## Steps (execution order)\n\n");
    if order.is_empty() {
        out.push_str("_This flow declares no elements._\n\n");
        return;
    }
    for (i, id) in order.iter().enumerate() {
        let Some(el) = elements.get(id) else { continue };
        let kind = prop_str(el.props.get("element_kind"));
        let _ = writeln!(out, "### {}. {} ({})\n", i + 1, el.name, kind);
        render_logic(el, out);
        let cite = locate_element(flow_src, kind, &el.name);
        let _ = writeln!(out, "- source: {}\n", cite);
    }
}

/// Render an element's captured logic (TT-77 props) as readable markdown. Only
/// present properties emit; an element with none says so.
fn render_logic(el: &GraphNode, out: &mut String) {
    let mut wrote = false;
    if let Some(Json::Array(rules)) = el.props.get("conditions") {
        out.push_str("- decision:\n");
        for rule in rules {
            let name = obj_get(rule, "name").and_then(as_str).unwrap_or("");
            let logic = obj_get(rule, "conditionLogic")
                .and_then(as_str)
                .unwrap_or("");
            let conn = obj_get(rule, "connector").and_then(as_str);
            let _ = writeln!(out, "  - rule `{name}` (logic: {logic})");
            if let Some(Json::Array(conds)) = obj_get(rule, "conditions") {
                for c in conds {
                    let left = obj_get(c, "left").and_then(as_str).unwrap_or("");
                    let op = obj_get(c, "operator").and_then(as_str).unwrap_or("");
                    let right = render_value(obj_get(c, "right"));
                    let _ = writeln!(out, "    - `{left}` {op} {right}");
                }
            }
            if let Some(t) = conn {
                let _ = writeln!(out, "    - → then go to `{t}`");
            }
        }
        wrote = true;
    }
    if let Some(Json::Array(items)) = el.props.get("assignments") {
        out.push_str("- assignments:\n");
        for it in items {
            let to = obj_get(it, "assignTo").and_then(as_str).unwrap_or("");
            let op = obj_get(it, "operator").and_then(as_str).unwrap_or("");
            let v = render_value(obj_get(it, "value"));
            let _ = writeln!(out, "  - `{to}` {op} {v}");
        }
        wrote = true;
    }
    if let Some(Json::Array(items)) = el.props.get("inputAssignments") {
        out.push_str("- writes (DML field-map):\n");
        for it in items {
            let field = obj_get(it, "field").and_then(as_str).unwrap_or("");
            let v = render_value(obj_get(it, "value"));
            let _ = writeln!(out, "  - `{field}` ← {v}");
        }
        wrote = true;
    }
    let queried = json_strings(el.props.get("queriedFields"));
    if !queried.is_empty() {
        let _ = writeln!(out, "- query fields: {}", code_join(&queried));
        wrote = true;
    }
    if let Some(Json::Array(items)) = el.props.get("filters") {
        out.push_str("- query WHERE:\n");
        for it in items {
            let field = obj_get(it, "field").and_then(as_str).unwrap_or("");
            let op = obj_get(it, "operator").and_then(as_str).unwrap_or("");
            let v = render_value(obj_get(it, "value"));
            let _ = writeln!(out, "  - `{field}` {op} {v}");
        }
        wrote = true;
    }
    if !wrote {
        out.push_str("- _(no captured logic — control flow only)_\n");
    }
}

/// A wrapped Flow value `{type,value}` → readable text. A `stringValue` is
/// quoted, an `elementReference` shown as a `{binding}`, everything else printed
/// bare with its type noted.
fn render_value(v: Option<&Json>) -> String {
    let Some(Json::Object(map)) = v else {
        return "∅".to_string();
    };
    let ty = map.get("type").and_then(as_str).unwrap_or("");
    let val = map.get("value").and_then(as_str).unwrap_or("");
    match ty {
        "stringValue" => format!("\"{val}\""),
        "elementReference" => format!("{{{val}}}"),
        "booleanValue" | "numberValue" => val.to_string(),
        "" => val.to_string(),
        _ => format!("{val} ({ty})"),
    }
}

/// Locate an element's source span, best-effort, in the flow file. Finds the
/// `<name>Element</name>` occurrence (or `<start` for the nameless entry), then
/// the enclosing `<kind …>`…`</kind>` around it, and renders a
/// `file:lineStart-lineEnd` cite. Falls back to the file alone when not locatable.
fn locate_element(src: Option<&str>, kind: &str, name: &str) -> String {
    let Some(src) = src else {
        return "(source unavailable)".to_string();
    };
    if let Some((s, e)) = element_span(src, kind, name) {
        let ls = line_at(src, s);
        let le = line_at(src, e);
        format!("`:{ls}-{le}`")
    } else {
        "`:` (line span not locatable)".to_string()
    }
}

/// Byte range `[start, end)` of the element whose tag is `<kind>` and which
/// carries `<name>{name}</name>` (or, for the nameless `start`, the `<start`
/// tag). Returns `None` when it cannot be pinned down.
fn element_span(src: &str, kind: &str, name: &str) -> Option<(usize, usize)> {
    if kind.is_empty() {
        return None;
    }
    let open = format!("<{kind}");
    let close = format!("</{kind}>");
    // Anchor: the element's own <name>…</name>, else the opening tag for start.
    let anchor = if name == "start" && kind == "start" {
        src.find(&open)?
    } else {
        src.find(&format!("<name>{name}</name>"))?
    };
    // Nearest opening tag at or before the anchor.
    let start = src[..=anchor.min(src.len().saturating_sub(1))]
        .rfind(&open)
        .or_else(|| src[..anchor].rfind(&open))?;
    // Nearest closing tag after the anchor.
    let rel_end = src[anchor..].find(&close)?;
    let end = anchor + rel_end + close.len();
    Some((start, end))
}

/// 1-based line number containing byte offset `at`.
fn line_at(src: &str, at: usize) -> usize {
    let at = at.min(src.len());
    1 + src[..at].bytes().filter(|b| *b == b'\n').count()
}

// --- called code (inlined) --------------------------------------------------

/// For each resolved Apex `CALLS` (`resolved_by="linker"`) or subflow `CALLS`
/// from this flow's elements, inline the target: the Apex method body sliced from
/// its `.cls`, or the subflow named by its file. Unresolved calls are listed as
/// external/standard actions. Deterministic (edges are BTreeMap-ordered).
fn called_code_section(
    graph: &Graph,
    elements: &BTreeMap<String, &GraphNode>,
    read: &Reader,
    out: &mut String,
) {
    out.push_str("## Called code (inlined)\n\n");

    // Resolved Apex: (element_name, apex_id), deduped + sorted.
    let mut apex_calls: BTreeSet<(String, String)> = BTreeSet::new();
    // Subflows: (element_name, flow_id).
    let mut subflows: BTreeSet<(String, String)> = BTreeSet::new();
    // Unresolved externals: (element_name, action_name).
    let mut externals: BTreeSet<(String, String)> = BTreeSet::new();

    for e in graph.edges().filter(|e| e.kind == edge::CALLS) {
        let Some(el) = elements.get(&e.from) else {
            continue;
        };
        let ename = el.name.clone();
        if prop_str(e.props.get("resolved_by")) == "linker" {
            apex_calls.insert((ename, e.to.clone()));
        } else if prop_str(e.props.get("via")) == "subflows" {
            subflows.insert((ename, e.to.clone()));
        } else if let Some(tgt) = graph.nodes().find(|n| n.id == e.to) {
            // An unresolved action that the linker resolved is covered by its
            // resolved edge above; skip it here to avoid a duplicate listing.
            let resolved = tgt.props.get("resolved") == Some(&Json::Bool(true));
            if tgt.kind == ont::UNRESOLVED && !resolved {
                externals.insert((ename, tgt.name.clone()));
            }
        }
    }

    if apex_calls.is_empty() && subflows.is_empty() && externals.is_empty() {
        out.push_str("_This flow calls no Apex, subflows, or actions._\n\n");
        return;
    }

    for (ename, apex_id) in &apex_calls {
        let _ = writeln!(out, "### Apex: `{apex_id}` (called by `{ename}`)\n");
        inline_apex(graph, apex_id, read, out);
    }
    for (ename, flow_id) in &subflows {
        let target = graph.nodes().find(|n| n.id == *flow_id);
        let name = target.map(|n| n.name.as_str()).unwrap_or("");
        let path = declaring_file_path(graph, flow_id);
        let _ = writeln!(out, "### Subflow: `{name}` (called by `{ename}`)\n");
        match path {
            Some(p) => {
                let _ = writeln!(out, "- defined in `{p}`\n");
            }
            None => {
                let _ = writeln!(out, "- external subflow (not in this package)\n");
            }
        }
    }
    for (ename, action) in &externals {
        let _ = writeln!(
            out,
            "### external/standard action: `{action}` (called by `{ename}`)\n"
        );
    }
}

/// Inline an Apex method's source, sliced from its declaring `.cls` by the
/// `span_start`/`span_end` byte offsets, with a `path:lineStart-lineEnd` cite.
fn inline_apex(graph: &Graph, apex_id: &str, read: &Reader, out: &mut String) {
    let Some(node) = graph.nodes().find(|n| n.id == apex_id) else {
        let _ = writeln!(out, "_target node missing from graph._\n");
        return;
    };
    let path = declaring_file_path(graph, apex_id);
    let start = prop_u64(node.props.get("span_start")) as usize;
    let end = prop_u64(node.props.get("span_end")) as usize;
    let src = path.as_deref().and_then(read);
    match src {
        Some(src) if end > start && end <= src.len() => {
            let body = &src[start..end];
            let ls = line_at(&src, start);
            let le = line_at(&src, end);
            let _ = writeln!(
                out,
                "- provenance: `{}:{ls}-{le}`\n",
                path.as_deref().unwrap_or("?")
            );
            out.push_str("```apex\n");
            out.push_str(body);
            if !body.ends_with('\n') {
                out.push('\n');
            }
            out.push_str("```\n\n");
        }
        _ => {
            // Cannot read the body: still cite what the graph knows.
            let _ = writeln!(
                out,
                "- provenance: `{}` (line {}); source not readable, not inlined\n",
                path.as_deref().unwrap_or("?"),
                prop_u64(node.props.get("line"))
            );
        }
    }
}

// --- Medplum target scaffold ------------------------------------------------

fn medplum_section(
    graph: &Graph,
    elements: &BTreeMap<String, &GraphNode>,
    order: &[String],
    out: &mut String,
) {
    out.push_str("## Medplum target scaffold\n\n");

    // First-touched object: the first step in execution order with a USES_TYPE.
    let trigger = order
        .iter()
        .filter_map(|id| elements.get(id).map(|el| (id, el)))
        .find_map(|(id, _)| uses_type_objects(graph, id).into_iter().next())
        .unwrap_or_else(|| "the triggering record".to_string());

    let _ = writeln!(
        out,
        "This flow → a Medplum Bot (Subscription trigger on `{trigger}`);\n"
    );
    for (i, id) in order.iter().enumerate() {
        let Some(el) = elements.get(id) else { continue };
        let kind = prop_str(el.props.get("element_kind"));
        let hint = medplum_hint(graph, id, kind);
        let _ = writeln!(out, "- {}. `{}` — {}", i + 1, el.name, hint);
    }
    out.push('\n');
}

/// One-line Medplum target hint for an element, keyed by its Salesforce kind.
fn medplum_hint(graph: &Graph, element_id: &str, kind: &str) -> String {
    match kind {
        "recordLookups" => "FHIR search".to_string(),
        "recordCreates" => "FHIR create".to_string(),
        "recordUpdates" => "FHIR update".to_string(),
        "recordDeletes" => "FHIR delete".to_string(),
        "decisions" => "conditional (if/else)".to_string(),
        "assignments" => "in-memory assignment".to_string(),
        "loops" => "iterate (map/for)".to_string(),
        "actionCalls" => {
            // Prefer the resolved apex target, else name the action.
            let resolved = graph.edges().find(|e| {
                e.kind == edge::CALLS
                    && e.from == element_id
                    && prop_str(e.props.get("resolved_by")) == "linker"
            });
            match resolved {
                Some(e) => format!("call to resolved code `{}`", e.to),
                None => "call to external/standard action".to_string(),
            }
        }
        "subflows" => "invoke another Bot / shared function".to_string(),
        "start" => "the Subscription entry point".to_string(),
        _ => "map to a Bot step".to_string(),
    }
}

// --- shared helpers ---------------------------------------------------------

/// The `path` prop of the File node that DECLARES `id`, if any.
fn declaring_file_path(graph: &Graph, id: &str) -> Option<String> {
    graph
        .edges()
        .filter(|e| e.kind == edge::DECLARES && e.to == id && e.from.starts_with("file::"))
        .find_map(|e| {
            graph
                .nodes()
                .find(|n| n.id == e.from)
                .and_then(|n| n.props.get("path"))
                .and_then(as_str)
                .map(str::to_string)
        })
}

/// The `field` value of every object in a `[{field,…}]` array property.
fn field_names(v: Option<&Json>) -> Vec<String> {
    let Some(Json::Array(items)) = v else {
        return Vec::new();
    };
    items
        .iter()
        .filter_map(|it| obj_get(it, "field").and_then(as_str).map(str::to_string))
        .collect()
}

/// Every string in a `["a","b"]` array property.
fn json_strings(v: Option<&Json>) -> Vec<String> {
    match v {
        Some(Json::Array(items)) => items
            .iter()
            .filter_map(as_str)
            .map(str::to_string)
            .collect(),
        _ => Vec::new(),
    }
}

/// A field of a `Json::Object`, by key.
fn obj_get<'a>(j: &'a Json, key: &str) -> Option<&'a Json> {
    match j {
        Json::Object(map) => map.get(key),
        _ => None,
    }
}

fn as_str(j: &Json) -> Option<&str> {
    match j {
        Json::Str(s) => Some(s.as_str()),
        _ => None,
    }
}

fn code_join(items: &[String]) -> String {
    items
        .iter()
        .map(|s| format!("`{s}`"))
        .collect::<Vec<_>>()
        .join(", ")
}

fn prop_str(v: Option<&Json>) -> &str {
    match v {
        Some(Json::Str(s)) => s.as_str(),
        _ => "",
    }
}

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

    /// A small hand-built flow: `start → Lookup → Create`, a touched SObject with
    /// two fields (one typed), one element that resolves to an Apex method, and the
    /// Apex Function + its class File node. Enough to exercise every section
    /// without touching the filesystem.
    fn sample() -> Graph {
        let mut g = Graph::new();

        // Flow + its file.
        g.upsert_node(
            "flow::Intake",
            ont::FUNCTION,
            "Intake",
            vec![
                ("type_kind", Json::str("flow")),
                ("process_type", Json::str("AutoLaunchedFlow")),
                ("depth", Json::U64(3)),
                ("element_count", Json::U64(3)),
                ("path", Json::str("flows/Intake.flow-meta.xml")),
            ],
        );
        g.upsert_node(
            "file::flows/Intake.flow-meta.xml",
            ont::FILE,
            "Intake.flow-meta.xml",
            vec![("path", Json::str("flows/Intake.flow-meta.xml"))],
        );
        g.add_edge(
            "file::flows/Intake.flow-meta.xml",
            edge::DECLARES,
            "flow::Intake",
            vec![],
        );

        // SObject Case__c with a typed field and an untyped one.
        g.upsert_node(
            "sobject::Case__c",
            ont::TYPE,
            "Case__c",
            vec![("type_kind", Json::str("sobject"))],
        );
        g.upsert_node(
            "sobject_field::Case__c.Status__c",
            ont::CONSTANT,
            "Status__c",
            vec![
                ("type_kind", Json::str("sobject_field")),
                ("field_type", Json::str("Picklist")),
            ],
        );
        g.add_edge(
            "sobject::Case__c",
            edge::DECLARES,
            "sobject_field::Case__c.Status__c",
            vec![],
        );

        // Elements: start, Lookup (recordLookups on Case__c), Create (recordCreates).
        for (name, kind) in [
            ("start", "start"),
            ("Lookup", "recordLookups"),
            ("Create", "recordCreates"),
            ("Notify", "actionCalls"),
        ] {
            let id = format!("flow_element::Intake.{name}");
            g.upsert_node(
                id.clone(),
                ont::FUNCTION,
                name,
                vec![
                    ("type_kind", Json::str("flow_element")),
                    ("element_kind", Json::str(kind)),
                    ("flow", Json::str("Intake")),
                ],
            );
            g.add_edge("flow::Intake", edge::DECLARES, id, vec![]);
        }
        // Control flow: start → Lookup → Create → Notify.
        for (a, b) in [
            ("start", "Lookup"),
            ("Lookup", "Create"),
            ("Create", "Notify"),
        ] {
            g.add_edge(
                format!("flow_element::Intake.{a}"),
                edge::FLOWS_TO,
                format!("flow_element::Intake.{b}"),
                vec![],
            );
        }

        // Lookup: queried fields + a filter + USES_TYPE Case__c.
        g.upsert_node(
            "flow_element::Intake.Lookup",
            ont::FUNCTION,
            "Lookup",
            vec![
                (
                    "queriedFields",
                    Json::Array(vec![Json::str("Id"), Json::str("Status__c")]),
                ),
                (
                    "filters",
                    Json::Array(vec![Json::obj([
                        ("field", Json::str("Status__c")),
                        ("operator", Json::str("EqualTo")),
                        (
                            "value",
                            Json::obj([
                                ("type", Json::str("stringValue")),
                                ("value", Json::str("Open")),
                            ]),
                        ),
                    ])]),
                ),
            ],
        );
        g.add_edge(
            "flow_element::Intake.Lookup",
            edge::USES_TYPE,
            "sobject::Case__c",
            vec![("via", Json::str("recordLookups"))],
        );
        // Create: input assignment + USES_TYPE.
        g.upsert_node(
            "flow_element::Intake.Create",
            ont::FUNCTION,
            "Create",
            vec![(
                "inputAssignments",
                Json::Array(vec![Json::obj([
                    ("field", Json::str("Status__c")),
                    (
                        "value",
                        Json::obj([
                            ("type", Json::str("stringValue")),
                            ("value", Json::str("New")),
                        ]),
                    ),
                ])]),
            )],
        );
        g.add_edge(
            "flow_element::Intake.Create",
            edge::USES_TYPE,
            "sobject::Case__c",
            vec![("via", Json::str("recordCreates"))],
        );

        // Notify → resolved Apex (linker edge) + its class file.
        g.upsert_node(
            "fn::CareTeam.notify#10",
            ont::FUNCTION,
            "notify",
            vec![
                ("language", Json::str("apex")),
                ("invocable", Json::Bool(true)),
                ("line", Json::U64(10)),
                ("span_start", Json::U64(25)),
                ("span_end", Json::U64(55)),
            ],
        );
        g.upsert_node(
            "file::classes/CareTeam.cls",
            ont::FILE,
            "CareTeam.cls",
            vec![("path", Json::str("classes/CareTeam.cls"))],
        );
        g.add_edge(
            "file::classes/CareTeam.cls",
            edge::DECLARES,
            "fn::CareTeam.notify#10",
            vec![],
        );
        g.add_edge(
            "flow_element::Intake.Notify",
            edge::CALLS,
            "fn::CareTeam.notify#10",
            vec![
                ("via", Json::str("actionCalls")),
                ("resolved_by", Json::str("linker")),
            ],
        );
        g
    }

    /// A canned reader so assembly is tested without the filesystem. The Apex
    /// class source's bytes [20,63) are the method body.
    fn reader(rel: &str) -> Option<String> {
        match rel {
            "classes/CareTeam.cls" => Some(
                // bytes [25,55) span the method body on line 2.
                "public class CareTeam{\n  void notify(){ notifyImpl(); }\n}\n".to_string(),
            ),
            _ => None,
        }
    }

    #[test]
    fn brief_has_all_sections() {
        let g = sample();
        let md = assemble(&g, "flow::Intake", &reader);
        assert!(md.contains("# Rebuild brief: Intake"));
        assert!(md.contains("## Scoped data model"));
        assert!(md.contains("## Steps (execution order)"));
        assert!(md.contains("## Called code (inlined)"));
        assert!(md.contains("## Medplum target scaffold"));
    }

    #[test]
    fn steps_are_in_execution_order() {
        let g = sample();
        let md = assemble(&g, "flow::Intake", &reader);
        let start = md.find("1. start").unwrap();
        let lookup = md.find("2. Lookup").unwrap();
        let create = md.find("3. Create").unwrap();
        let notify = md.find("4. Notify").unwrap();
        assert!(start < lookup && lookup < create && create < notify, "{md}");
    }

    #[test]
    fn steps_render_logic() {
        let g = sample();
        let md = assemble(&g, "flow::Intake", &reader);
        // Lookup's filter and queried fields.
        assert!(md.contains("query fields: `Id`, `Status__c`"), "{md}");
        assert!(md.contains("`Status__c` EqualTo \"Open\""), "{md}");
        // Create's DML field-map.
        assert!(md.contains("`Status__c` ← \"New\""), "{md}");
    }

    #[test]
    fn data_model_is_scoped_with_types() {
        let g = sample();
        let md = assemble(&g, "flow::Intake", &reader);
        assert!(md.contains("### Case__c"), "{md}");
        // The typed field shows its type; a used-but-untyped one is "unknown".
        assert!(md.contains("`Status__c` — type `Picklist`"), "{md}");
    }

    #[test]
    fn inlines_resolved_apex_with_provenance() {
        let g = sample();
        let md = assemble(&g, "flow::Intake", &reader);
        assert!(md.contains("### Apex: `fn::CareTeam.notify#10`"), "{md}");
        assert!(md.contains("classes/CareTeam.cls:"), "{md}");
        // The inlined body is the byte slice [20,63).
        assert!(md.contains("void notify(){ notifyImpl(); }"), "{md}");
    }

    #[test]
    fn medplum_scaffold_maps_steps() {
        let g = sample();
        let md = assemble(&g, "flow::Intake", &reader);
        assert!(md.contains("Subscription trigger on `Case__c`"), "{md}");
        assert!(md.contains("`Lookup` — FHIR search"), "{md}");
        assert!(md.contains("`Create` — FHIR create"), "{md}");
        assert!(md.contains("`Notify` — call to resolved code"), "{md}");
    }

    #[test]
    fn line_cites_use_the_flow_source() {
        let g = sample();
        // A flow source where Lookup lives on lines 2-4.
        let flow_src = "<Flow>\n  <recordLookups><name>Lookup</name>\n    <object>Case__c</object>\n  </recordLookups>\n</Flow>";
        let (s, e) = element_span(flow_src, "recordLookups", "Lookup").unwrap();
        assert_eq!(line_at(flow_src, s), 2);
        assert_eq!(line_at(flow_src, e), 4);
        // And the whole assembly emits a cite when the flow file reads.
        let read = |rel: &str| -> Option<String> {
            if rel == "flows/Intake.flow-meta.xml" {
                Some(flow_src.to_string())
            } else {
                reader(rel)
            }
        };
        let md = assemble(&g, "flow::Intake", &read);
        assert!(md.contains("source: `:2-4`"), "{md}");
    }

    #[test]
    fn resolve_flow_by_name_and_id() {
        let g = sample();
        assert_eq!(resolve_flow(&g, "Intake").unwrap(), "flow::Intake");
        assert_eq!(resolve_flow(&g, "flow::Intake").unwrap(), "flow::Intake");
        assert!(resolve_flow(&g, "Nope").is_err());
    }

    #[test]
    fn deterministic_output() {
        let g = sample();
        let a = assemble(&g, "flow::Intake", &reader);
        let b = assemble(&g, "flow::Intake", &reader);
        assert_eq!(a, b);
    }

    #[test]
    fn unreadable_source_is_honest() {
        let g = sample();
        // A reader that never returns anything: no line cites, no inlined body,
        // but the brief still assembles from graph-only facts.
        let md = assemble(&g, "flow::Intake", &(|_: &str| None));
        assert!(md.contains("## Steps (execution order)"));
        assert!(md.contains("source: (source unavailable)"), "{md}");
        assert!(md.contains("source not readable, not inlined"), "{md}");
    }
}
