//! Lower Salesforce metadata XML into the canonical graph.
//!
//! The honest mapping (properties over new ontology kinds, so existing golden
//! output is never perturbed):
//!
//! - `CustomObject` (`X.object-meta.xml`) → [`Type`] with `type_kind:
//!   "sobject"`; inline `<fields>` (MDAPI single-file layout) lower like field
//!   files.
//! - `CustomField` (`F.field-meta.xml` under `objects/<Obj>/fields/`) →
//!   [`Constant`] with `type_kind: "sobject_field"`, `DECLARES`-d by its
//!   object; `<referenceTo>` → [`USES_TYPE`] field → target object (lookup /
//!   master-detail data dependency).
//! - `Flow` (`X.flow-meta.xml`) → [`Function`] with `type_kind: "flow"`, plus
//!   `element_count` and `depth` props (TT-65). Each flow element → a
//!   [`Function`] with `type_kind: "flow_element"` (`element_kind` = the XML
//!   tag), `DECLARES`-d by its flow. `<connector>`/`defaultConnector`/
//!   `faultConnector`/loop connectors → [`FLOWS_TO`] control-flow edges
//!   between elements (unresolved targets become explicit UnresolvedSymbols,
//!   never dropped). Record ops (`recordLookups/Creates/Updates/Deletes`) →
//!   [`USES_TYPE`] from the *element* to its SObject; `actionCalls` → [`CALLS`]
//!   element → UnresolvedSymbol (Apex, resolved later by the TT-62 linker);
//!   `subflows` → [`CALLS`] element → flow. `depth` is the longest simple path
//!   through the element graph (back edges pruned) — the "this flow is N deep"
//!   number for the workflow-extraction lane.
//! - `ValidationRule` (`R.validationRule-meta.xml`) → [`Constant`] with
//!   `type_kind: "validation_rule"`, `DECLARES`-d by its object. The
//!   `errorConditionFormula` is parsed by the TT-64 formula grammar
//!   (`super::formula`): its `formula_refs` (sorted field/relationship names)
//!   and `formula_system_refs` (`$`-globals) become properties, and each *bare*
//!   field reference becomes a [`USES_TYPE`] edge to
//!   `sobject_field::<Obj>.<Field>` (`via="formula"`). Formula fields
//!   (`<formula>` on a `CustomField`) are parsed the same way.
//!
//! Object identity comes from the SFDX path convention
//! (`…/objects/<Obj>/…`) or, failing that, the file stem. Every referenced
//! object gets an `sobject::` node (first definition wins; references never
//! clobber definitions because lowering runs definitions first).
//!
//! [`Type`]: crate::ir::ontology::node::TYPE
//! [`Constant`]: crate::ir::ontology::node::CONSTANT
//! [`Function`]: crate::ir::ontology::node::FUNCTION
//! [`UnresolvedSymbol`]: crate::ir::ontology::node::UNRESOLVED
//! [`USES_TYPE`]: crate::ir::ontology::edge::USES_TYPE
//! [`CALLS`]: crate::ir::ontology::edge::CALLS

use crate::core::cst::Node;
use crate::core::json::Json;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::salesforce::MetaKind;
use crate::lang::xml::parser::{
    child_elements, child_named, children_named, tag_name, text_content,
};

pub fn lower(package: &str, files: &[SourceFile<'_>]) -> Graph {
    let mut g = Graph::new();
    let pkg_id = format!("pkg::{package}");
    g.upsert_node(
        pkg_id.clone(),
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("salesforce-metadata"))],
    );

    // Pass 1: definitions (objects, fields, flows, validation rules) so that
    // pass-2 references can distinguish "defined here" from "external".
    for f in files {
        emit_file_node(&mut g, &pkg_id, f);
        match MetaKind::of(&f.rel_path) {
            Some(MetaKind::Object) => lower_object(&mut g, f),
            Some(MetaKind::Field) => lower_field_file(&mut g, f),
            Some(MetaKind::Flow) => lower_flow_def(&mut g, f),
            Some(MetaKind::ValidationRule) => lower_validation_rule(&mut g, f),
            Some(MetaKind::Profile) => super::perm::lower_profile(&mut g, f),
            Some(MetaKind::PermissionSet) => super::perm::lower_permission_set(&mut g, f),
            Some(MetaKind::Workflow) => lower_workflow(&mut g, f),
            None => {}
        }
    }
    // Pass 2: flow reference edges (may target flows/objects defined in pass 1;
    // unresolved targets become explicit logical nodes, never silent drops).
    for f in files {
        if MetaKind::of(&f.rel_path) == Some(MetaKind::Flow) {
            lower_flow_elements(&mut g, f);
        }
    }
    g
}

fn emit_file_node(g: &mut Graph, pkg_id: &str, f: &SourceFile<'_>) {
    let file_id = format!("file::{}", f.rel_path);
    let name = f.rel_path.rsplit('/').next().unwrap_or(&f.rel_path);
    g.upsert_node(
        file_id.clone(),
        ont::FILE,
        name.to_string(),
        vec![
            ("path", Json::str(f.rel_path.clone())),
            ("language", Json::str("salesforce-metadata")),
            ("bytes", Json::U64(f.source.len() as u64)),
        ],
    );
    g.add_edge(pkg_id.to_string(), edge::CONTAINS, file_id, vec![]);
}

pub(super) fn file_id(f: &SourceFile<'_>) -> String {
    format!("file::{}", f.rel_path)
}

/// Root element of the document, if any.
pub(super) fn root_element<'a>(f: &'a SourceFile<'_>) -> Option<&'a Node> {
    child_elements(f.root).next()
}

/// The metadata component name: the file stem before the compound suffix
/// (`Case.object-meta.xml` → `Case`).
pub(super) fn component_name(rel_path: &str, suffix: &str) -> String {
    let name = rel_path.rsplit('/').next().unwrap_or(rel_path);
    name.strip_suffix(suffix).unwrap_or(name).to_string()
}

/// Owning object per the SFDX layout: the path segment following `objects`.
/// Falls back to `None` (caller decides) when the convention is absent.
fn owning_object(rel_path: &str) -> Option<String> {
    let segs: Vec<&str> = rel_path.split('/').collect();
    segs.iter()
        .position(|s| *s == "objects")
        .and_then(|i| segs.get(i + 1))
        .filter(|s| !s.contains('.'))
        .map(|s| s.to_string())
}

pub(super) fn sobject_id(name: &str) -> String {
    format!("sobject::{name}")
}

pub(super) fn ensure_sobject(g: &mut Graph, name: &str) -> String {
    let id = sobject_id(name);
    // References never clobber a definition: upsert fills only absent nodes,
    // and definitions were emitted in pass 1.
    g.upsert_node(
        id.clone(),
        ont::TYPE,
        name.to_string(),
        vec![
            ("type_kind", Json::str("sobject")),
            ("language", Json::str("salesforce-metadata")),
        ],
    );
    id
}

fn lower_object(g: &mut Graph, f: &SourceFile<'_>) {
    let obj_name = component_name(&f.rel_path, ".object-meta.xml");
    let obj_id = ensure_sobject(g, &obj_name);
    if let Some(root) = root_element(f) {
        if let Some(label) = child_named(root, "label", f.source) {
            g.upsert_node(
                obj_id.clone(),
                ont::TYPE,
                obj_name.clone(),
                vec![("label", Json::str(text_content(label, f.source)))],
            );
        }
        // MDAPI single-file layout: inline <fields> definitions.
        for field_el in children_named(root, "fields", f.source) {
            let Some(full) = child_named(field_el, "fullName", f.source) else {
                continue;
            };
            let field_name = text_content(full, f.source);
            if field_name.is_empty() {
                continue;
            }
            emit_field(g, f, &obj_name, &field_name, field_el);
        }
    }
    g.add_edge(file_id(f), edge::DECLARES, obj_id, vec![]);
}

fn lower_field_file(g: &mut Graph, f: &SourceFile<'_>) {
    let stem = component_name(&f.rel_path, ".field-meta.xml");
    let obj_name = owning_object(&f.rel_path).unwrap_or_else(|| "UnknownObject".to_string());
    ensure_sobject(g, &obj_name);
    let root = root_element(f);
    // fullName inside the document wins over the file stem when present.
    let field_name = root
        .and_then(|r| child_named(r, "fullName", f.source))
        .map(|n| text_content(n, f.source))
        .filter(|s| !s.is_empty())
        .unwrap_or(stem);
    if let Some(root) = root {
        emit_field(g, f, &obj_name, &field_name, root);
    }
}

/// Shared field emission for both layouts. `field_el` is the element holding
/// the field's children (`<fields>` inline, or the `CustomField` root).
fn emit_field(
    g: &mut Graph,
    f: &SourceFile<'_>,
    obj_name: &str,
    field_name: &str,
    field_el: &Node,
) {
    let field_id = format!("sobject_field::{obj_name}.{field_name}");
    let mut props = vec![
        ("type_kind", Json::str("sobject_field")),
        ("language", Json::str("salesforce-metadata")),
        ("object", Json::str(obj_name.to_string())),
        ("path", Json::str(f.rel_path.clone())),
    ];
    if let Some(t) = child_named(field_el, "type", f.source) {
        props.push(("field_type", Json::str(text_content(t, f.source))));
    }
    if let Some(l) = child_named(field_el, "label", f.source) {
        props.push(("label", Json::str(text_content(l, f.source))));
    }
    // Formula fields (TT-64): a `<formula>` carries an expression over sibling
    // fields — parse it just like a validation rule.
    let parsed_formula = child_named(field_el, "formula", f.source)
        .map(|el| attach_formula(&mut props, &text_content(el, f.source)));
    g.upsert_node(
        field_id.clone(),
        ont::CONSTANT,
        field_name.to_string(),
        props,
    );
    if let Some(refs) = &parsed_formula {
        emit_formula_field_edges(g, &field_id, obj_name, Some(field_name), refs);
    }
    g.add_edge(
        sobject_id(obj_name),
        edge::DECLARES,
        field_id.clone(),
        vec![],
    );
    g.add_edge(file_id(f), edge::DECLARES, field_id.clone(), vec![]);
    // Lookup / master-detail: a data dependency on the target object.
    for r in children_named(field_el, "referenceTo", f.source) {
        let target = text_content(r, f.source);
        if target.is_empty() {
            continue;
        }
        let target_id = ensure_sobject(g, &target);
        g.add_edge(
            field_id.clone(),
            edge::USES_TYPE,
            target_id,
            vec![("via", Json::str("referenceTo"))],
        );
    }
}

fn flow_id(name: &str) -> String {
    format!("flow::{name}")
}

fn lower_flow_def(g: &mut Graph, f: &SourceFile<'_>) {
    let name = component_name(&f.rel_path, ".flow-meta.xml");
    let id = flow_id(&name);
    let mut props = vec![
        ("type_kind", Json::str("flow")),
        ("language", Json::str("salesforce-metadata")),
        ("path", Json::str(f.rel_path.clone())),
    ];
    if let Some(root) = root_element(f) {
        if let Some(l) = child_named(root, "label", f.source) {
            props.push(("label", Json::str(text_content(l, f.source))));
        }
        if let Some(s) = child_named(root, "status", f.source) {
            props.push(("status", Json::str(text_content(s, f.source))));
        }
        if let Some(t) = child_named(root, "processType", f.source) {
            props.push(("process_type", Json::str(text_content(t, f.source))));
        }
    }
    g.upsert_node(id.clone(), ont::FUNCTION, name, props);
    g.add_edge(file_id(f), edge::DECLARES, id, vec![]);
}

fn binding_id(flow: &str, name: &str) -> String {
    format!("flow_binding::{flow}.{name}")
}

/// TT-86 data environment. A flow's top-level `<variables>`, `<formulas>`,
/// `<constants>`, and `<textTemplates>` are the resources every element reads
/// and writes — the flow's binding scope. Each becomes a [`Constant`] binding
/// node (`type_kind` = `flow_variable` | `flow_formula` | `flow_constant` |
/// `flow_text_template`), [`DECLARES`]-d by the flow, additive over the existing
/// element graph:
///
/// - **variables** carry `dataType`, `isCollection`, `isInput`, `isOutput`; an
///   sObject variable's `<objectType>` becomes a [`USES_TYPE`] edge to the
///   object (`via="objectType"`, `ensure_sobject` so a standard object still
///   resolves).
/// - **formulas** keep the raw `<expression>` verbatim plus the TT-64
///   `formula_refs`; each ref *head* that names a known sObject becomes a
///   best-effort [`USES_TYPE`] edge (`via="flow_formula"`) — never fabricated,
///   flow-scoped refs (variables/elements) simply stay listed in `formula_refs`.
/// - **constants** / **textTemplates** keep their literal `value`/`text`.
///
/// Emitted in pass 2 so every referenced sObject already exists and so the
/// binding nodes are present before element-level `<collectionReference>`
/// data-dependency resolution runs in the same pass.
///
/// [`Constant`]: crate::ir::ontology::node::CONSTANT
/// [`DECLARES`]: crate::ir::ontology::edge::DECLARES
/// [`USES_TYPE`]: crate::ir::ontology::edge::USES_TYPE
fn lower_flow_bindings(g: &mut Graph, f: &SourceFile<'_>, flow_name: &str, fid: &str) {
    let Some(root) = root_element(f) else { return };
    for (tag, type_kind) in [
        ("variables", "flow_variable"),
        ("formulas", "flow_formula"),
        ("constants", "flow_constant"),
        ("textTemplates", "flow_text_template"),
    ] {
        for el in children_named(root, tag, f.source) {
            let Some(name_el) = child_named(el, "name", f.source) else {
                continue;
            };
            let name = text_content(name_el, f.source);
            if name.is_empty() {
                continue;
            }
            let bid = binding_id(flow_name, &name);
            let mut props = vec![
                ("type_kind", Json::str(type_kind)),
                ("language", Json::str("salesforce-metadata")),
                ("flow", Json::str(flow_name.to_string())),
            ];
            if let Some(dt) = child_named(el, "dataType", f.source) {
                props.push(("dataType", Json::str(text_content(dt, f.source))));
            }
            let mut object_type: Option<String> = None;
            let mut formula_refs: Option<crate::lang::salesforce::formula::FormulaRefs> = None;
            match tag {
                "variables" => {
                    for key in ["isCollection", "isInput", "isOutput"] {
                        if let Some(v) = child_named(el, key, f.source) {
                            props.push((key, Json::str(text_content(v, f.source))));
                        }
                    }
                    if let Some(ot) = child_named(el, "objectType", f.source) {
                        let t = text_content(ot, f.source);
                        if !t.is_empty() {
                            props.push(("objectType", Json::str(t.clone())));
                            object_type = Some(t);
                        }
                    }
                }
                "formulas" => {
                    if let Some(expr_el) = child_named(el, "expression", f.source) {
                        let text = text_content(expr_el, f.source);
                        let refs = crate::lang::salesforce::formula::extract(&text);
                        props.push(("expression", Json::str(text)));
                        props.push(("formula_refs", refs_json(&refs.refs)));
                        formula_refs = Some(refs);
                    }
                }
                "constants" | "textTemplates" => {
                    if let Some(v) = child_named(el, "value", f.source) {
                        props.push(("value", value_json(v, f.source)));
                    } else if let Some(t) = child_named(el, "text", f.source) {
                        props.push(("value", Json::str(text_content(t, f.source))));
                    }
                }
                _ => {}
            }
            g.upsert_node(bid.clone(), ont::CONSTANT, name, props);
            g.add_edge(fid.to_string(), edge::DECLARES, bid.clone(), vec![]);
            if let Some(ot) = object_type {
                let target = ensure_sobject(g, &ot);
                g.add_edge(
                    bid.clone(),
                    edge::USES_TYPE,
                    target,
                    vec![("via", Json::str("objectType"))],
                );
            }
            if let Some(refs) = formula_refs {
                for r in &refs.refs {
                    let sid = sobject_id(r);
                    if g.has_node(&sid) {
                        g.add_edge(
                            bid.clone(),
                            edge::USES_TYPE,
                            sid,
                            vec![("via", Json::str("flow_formula"))],
                        );
                    }
                }
            }
        }
    }
}

/// TT-86 data-environment containers: top-level flow children that declare
/// *bindings* (the flow's variables/formulas/constants/text templates), not
/// executable elements. They carry a `<name>` like an element does, so element
/// discovery must skip them explicitly.
const DATA_ENV_TAGS: &[&str] = &["variables", "formulas", "constants", "textTemplates"];

/// The flow element categories that operate on an SObject via `<object>`.
const RECORD_OPS: &[&str] = &[
    "recordLookups",
    "recordCreates",
    "recordUpdates",
    "recordDeletes",
];

/// Connector tags that carry control flow (`<targetReference>` inside).
const CONNECTOR_TAGS: &[&str] = &[
    "connector",
    "defaultConnector",
    "faultConnector",
    "nextValueConnector",
    "noMoreValuesConnector",
];

fn element_id(flow: &str, element: &str) -> String {
    format!("flow_element::{flow}.{element}")
}

/// TT-65: lower a flow's *internal* structure. Every direct child of `<Flow>`
/// carrying a `<name>` is an element (spec-agnostic by design — new element
/// categories Salesforce invents still land in the graph); `<start>` is the
/// nameless entry element. Connectors become [`FLOWS_TO`] control-flow edges,
/// record ops / actions / subflows attach to the *element* that performs them,
/// and the flow node gains `element_count` + `depth` (longest acyclic path
/// from the roots, counted in elements — the "this flow is 60 deep" number).
///
/// [`FLOWS_TO`]: crate::ir::ontology::edge::FLOWS_TO
fn lower_flow_elements(g: &mut Graph, f: &SourceFile<'_>) {
    let flow_name = component_name(&f.rel_path, ".flow-meta.xml");
    let fid = flow_id(&flow_name);
    let Some(root) = root_element(f) else { return };

    // TT-86: the flow's data environment (variables/formulas/constants/text
    // templates) as binding nodes, before element-level `<collectionReference>`
    // resolution below can point at them.
    lower_flow_bindings(g, f, &flow_name, &fid);

    // Element discovery: (element_name, cst node, element_kind).
    let mut elements: Vec<(String, &crate::core::cst::Node, String)> = Vec::new();
    for el in child_elements(root) {
        let Some(kind) = crate::lang::xml::parser::tag_name(el, f.source) else {
            continue;
        };
        if kind == "start" {
            elements.push(("start".to_string(), el, "start".to_string()));
            continue;
        }
        // TT-86: the data-environment containers carry a `<name>` too, but they
        // are the flow's binding scope (lowered by `lower_flow_bindings`), not
        // executable elements — never a control-flow node.
        if DATA_ENV_TAGS.contains(&kind) {
            continue;
        }
        if let Some(n) = child_named(el, "name", f.source) {
            let ename = text_content(n, f.source);
            if !ename.is_empty() {
                elements.push((ename, el, kind.to_string()));
            }
        }
    }

    // Pass A: element nodes, declared by their flow.
    for (ename, _el, kind) in &elements {
        let eid = element_id(&flow_name, ename);
        g.upsert_node(
            eid.clone(),
            ont::FUNCTION,
            ename.clone(),
            vec![
                ("type_kind", Json::str("flow_element")),
                ("element_kind", Json::str(kind.clone())),
                ("flow", Json::str(flow_name.clone())),
                ("language", Json::str("salesforce-metadata")),
            ],
        );
        g.add_edge(fid.clone(), edge::DECLARES, eid, vec![]);
    }
    let defined: std::collections::BTreeSet<&str> =
        elements.iter().map(|(n, _, _)| n.as_str()).collect();

    // Pass B: per-element semantics + control flow.
    let mut flow_edges: Vec<(String, String)> = Vec::new();
    for (ename, el, kind) in &elements {
        let eid = element_id(&flow_name, ename);

        // Record operations: the element's data dependency on an SObject.
        if RECORD_OPS.contains(&kind.as_str()) {
            if let Some(obj) = child_named(el, "object", f.source) {
                let target = text_content(obj, f.source);
                if !target.is_empty() {
                    let target_id = ensure_sobject(g, &target);
                    g.add_edge(
                        eid.clone(),
                        edge::USES_TYPE,
                        target_id,
                        vec![("via", Json::str(kind.clone()))],
                    );
                }
            }
        }

        // TT-86 loops: the `<collectionReference>` names the resource iterated
        // over — a data dependency on a binding (a collection variable) or an
        // element (a query's results). Resolved best-effort to a *defined*
        // element or an existing binding node; never fabricated. The loop's
        // next/noMore/default connectors are control flow, handled by the
        // connector walk below.
        if kind == "loops" {
            if let Some(cr) = child_named(el, "collectionReference", f.source) {
                let target = text_content(cr, f.source);
                let base = target.split('.').next().unwrap_or(&target);
                if !base.is_empty() && base != ename.as_str() {
                    let dep = if defined.contains(base) {
                        Some(element_id(&flow_name, base))
                    } else {
                        let bid = binding_id(&flow_name, base);
                        g.has_node(&bid).then_some(bid)
                    };
                    if let Some(dep_id) = dep {
                        g.add_edge(
                            eid.clone(),
                            edge::DATA_DEP,
                            dep_id,
                            vec![("via", Json::str("collectionReference"))],
                        );
                    }
                }
            }
        }

        // Invocable actions: target usually lives in Apex — another front
        // end's territory — so the endpoint is an explicit UnresolvedSymbol
        // the TT-62 linker resolves later. Never silently dropped.
        if kind == "actionCalls" {
            if let Some(action) = child_named(el, "actionName", f.source) {
                let action_name = text_content(action, f.source);
                if !action_name.is_empty() {
                    let action_type = child_named(el, "actionType", f.source)
                        .map(|t| text_content(t, f.source))
                        .unwrap_or_default();
                    let target_id = format!("unresolved::sf_action::{action_name}");
                    g.upsert_node(
                        target_id.clone(),
                        ont::UNRESOLVED,
                        action_name.clone(),
                        vec![
                            ("reference_kind", Json::str("salesforce_action")),
                            ("action_type", Json::str(action_type)),
                        ],
                    );
                    g.add_edge(
                        eid.clone(),
                        edge::CALLS,
                        target_id,
                        vec![("via", Json::str("actionCalls"))],
                    );
                }
            }
        }

        // Subflows: element-level flow-to-flow call; definition wins over
        // reference because flow nodes were created in the file-level pass 1.
        if kind == "subflows" {
            if let Some(fname_el) = child_named(el, "flowName", f.source) {
                let target = text_content(fname_el, f.source);
                if !target.is_empty() {
                    let target_id = flow_id(&target);
                    if !g.has_node(&target_id) {
                        g.upsert_node(
                            target_id.clone(),
                            ont::UNRESOLVED,
                            target.clone(),
                            vec![("reference_kind", Json::str("salesforce_flow"))],
                        );
                    }
                    g.add_edge(
                        eid.clone(),
                        edge::CALLS,
                        target_id,
                        vec![("via", Json::str("subflows"))],
                    );
                }
            }
        }

        // Control flow: every connector tag anywhere under this element (they
        // nest inside decision <rules>, loop bodies, etc.). A targetReference
        // naming an element this flow never defines still gets an edge — to an
        // explicit UnresolvedSymbol, honestly, never dropped.
        collect_connectors(el, f.source, &mut |tag, target| {
            let target_id = if defined.contains(target) {
                element_id(&flow_name, target)
            } else {
                let uid = element_id(&flow_name, target);
                g.upsert_node(
                    uid.clone(),
                    ont::UNRESOLVED,
                    target.to_string(),
                    vec![
                        ("reference_kind", Json::str("flow_element")),
                        ("flow", Json::str(flow_name.clone())),
                    ],
                );
                uid
            };
            g.add_edge(
                eid.clone(),
                edge::FLOWS_TO,
                target_id,
                vec![("via", Json::str(tag.to_string()))],
            );
            flow_edges.push((ename.clone(), target.to_string()));
        });

        // TT-77: the element's *actual logic*, captured as deterministic
        // JSON-in-property (no new node kinds — goldens stay stable). Only
        // non-empty captures are attached, so elements without logic are
        // undisturbed. `upsert_node` fills absent keys only, so these ride
        // alongside the base props set in Pass A without clobbering them.
        let mut logic: Vec<(&'static str, Json)> = Vec::new();
        match kind.as_str() {
            "decisions" => {
                let rules = decision_rules_json(el, f.source);
                if !rules.is_empty() {
                    logic.push(("conditions", Json::Array(rules)));
                }
            }
            "assignments" => {
                let items = assignment_items_json(el, f.source);
                if !items.is_empty() {
                    logic.push(("assignments", Json::Array(items)));
                }
            }
            "recordCreates" | "recordUpdates" | "recordDeletes" => {
                let inputs = input_assignments_json(el, f.source);
                if !inputs.is_empty() {
                    logic.push(("inputAssignments", Json::Array(inputs)));
                }
                let filters = filters_json(el, f.source);
                if !filters.is_empty() {
                    logic.push(("filters", Json::Array(filters)));
                }
            }
            "recordLookups" => {
                let filters = filters_json(el, f.source);
                if !filters.is_empty() {
                    logic.push(("filters", Json::Array(filters)));
                }
                let fields = queried_fields_json(el, f.source);
                if !fields.is_empty() {
                    logic.push(("queriedFields", Json::Array(fields)));
                }
            }
            "screens" => {
                let fields = screen_fields_json(el, f.source);
                if !fields.is_empty() {
                    logic.push(("screenFields", Json::Array(fields)));
                }
            }
            "waits" => {
                let events = wait_events_json(el, f.source);
                if !events.is_empty() {
                    logic.push(("waitEvents", Json::Array(events)));
                }
            }
            _ => {}
        }
        if !logic.is_empty() {
            g.upsert_node(eid.clone(), ont::FUNCTION, ename.clone(), logic);
        }

        // TT-77 intra-flow data flow: any `<elementReference>` anywhere under
        // this element that names another *defined* element in this flow is a
        // def/use dependency → a DATA_DEP edge (consumer → producer). The
        // `.field` suffix is stripped to the element name; a reference to an
        // element the flow never defines is skipped (not fabricated), and a
        // self-reference is never emitted. Targets are collected into a
        // `BTreeSet` so ordering and dedup are deterministic.
        let mut refs: Vec<String> = Vec::new();
        collect_element_refs(el, f.source, &mut refs);
        let mut dep_targets: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        for r in refs {
            let base = r.split('.').next().unwrap_or(&r);
            if base.is_empty() || base == ename.as_str() {
                continue;
            }
            if defined.contains(base) {
                dep_targets.insert(base.to_string());
            }
        }
        for base in dep_targets {
            g.add_edge(
                eid.clone(),
                edge::DATA_DEP,
                element_id(&flow_name, &base),
                vec![("via", Json::str("elementReference"))],
            );
        }
    }

    // Depth: longest acyclic path (in elements) from the roots, back edges
    // ignored — loops don't inflate it and can't hang it. The headline number:
    // "this flow is N deep".
    let depth = flow_depth(&elements, &flow_edges);
    g.upsert_node(
        fid,
        ont::FUNCTION,
        flow_name.clone(),
        vec![
            ("element_count", Json::U64(elements.len() as u64)),
            ("depth", Json::U64(depth as u64)),
        ],
    );
}

/// Depth-first over an element subtree collecting `(connector_tag,
/// targetReference)` pairs.
fn collect_connectors(el: &crate::core::cst::Node, src: &str, emit: &mut impl FnMut(&str, &str)) {
    for child in child_elements(el) {
        let tag = crate::lang::xml::parser::tag_name(child, src).unwrap_or("");
        if CONNECTOR_TAGS.contains(&tag) {
            if let Some(t) = child_named(child, "targetReference", src) {
                let target = text_content(t, src);
                if !target.is_empty() {
                    emit(tag, &target);
                }
            }
        } else {
            collect_connectors(child, src, emit);
        }
    }
}

/// A Flow `<value>` / `<rightValue>` wrapper → deterministic JSON. Salesforce
/// wraps a typed leaf inside the wrapper (`<stringValue>`, `<elementReference>`,
/// `<booleanValue>`, `<numberValue>`, …); we keep both the leaf's tag (`type`)
/// and its text (`value`) so the spec is lossless. A bare-text wrapper (rare)
/// is reported as a `"literal"`.
fn value_json(wrapper: &Node, src: &str) -> Json {
    if let Some(child) = child_elements(wrapper).next() {
        let ty = tag_name(child, src).unwrap_or("").to_string();
        Json::obj([
            ("type", Json::str(ty)),
            ("value", Json::str(text_content(child, src))),
        ])
    } else {
        Json::obj([
            ("type", Json::str("literal")),
            ("value", Json::str(text_content(wrapper, src))),
        ])
    }
}

/// The `<connector><targetReference>` of an element (or rule), if present.
fn connector_target(el: &Node, src: &str) -> Option<String> {
    child_named(el, "connector", src)
        .and_then(|c| child_named(c, "targetReference", src))
        .map(|t| text_content(t, src))
        .filter(|s| !s.is_empty())
}

/// A decision's `<rules>` → one JSON object per rule: its `conditionLogic`, its
/// `<conditions>` (`left`/`operator`/`right`), and the rule's connector target
/// (the branch it takes when it matches). The decision node's branching
/// predicate, made explicit.
fn decision_rules_json(el: &Node, src: &str) -> Vec<Json> {
    let mut out = Vec::new();
    for rule in children_named(el, "rules", src) {
        let name = child_named(rule, "name", src)
            .map(|n| text_content(n, src))
            .unwrap_or_default();
        let logic = child_named(rule, "conditionLogic", src)
            .map(|n| text_content(n, src))
            .unwrap_or_default();
        let mut conds = Vec::new();
        for cond in children_named(rule, "conditions", src) {
            let left = child_named(cond, "leftValueReference", src)
                .map(|n| text_content(n, src))
                .unwrap_or_default();
            let op = child_named(cond, "operator", src)
                .map(|n| text_content(n, src))
                .unwrap_or_default();
            let right = child_named(cond, "rightValue", src)
                .map(|rv| value_json(rv, src))
                .unwrap_or(Json::Null);
            conds.push(Json::obj([
                ("left", Json::str(left)),
                ("operator", Json::str(op)),
                ("right", right),
            ]));
        }
        out.push(Json::obj([
            ("name", Json::str(name)),
            ("conditionLogic", Json::str(logic)),
            ("conditions", Json::Array(conds)),
            (
                "connector",
                connector_target(rule, src)
                    .map(Json::str)
                    .unwrap_or(Json::Null),
            ),
        ]));
    }
    out
}

/// An assignment's `<assignmentItems>` → `assignTo`/`operator`/`value` triples:
/// what the element sets, and to what.
fn assignment_items_json(el: &Node, src: &str) -> Vec<Json> {
    let mut out = Vec::new();
    for item in children_named(el, "assignmentItems", src) {
        let to = child_named(item, "assignToReference", src)
            .map(|n| text_content(n, src))
            .unwrap_or_default();
        let op = child_named(item, "operator", src)
            .map(|n| text_content(n, src))
            .unwrap_or_default();
        let value = child_named(item, "value", src)
            .map(|v| value_json(v, src))
            .unwrap_or(Json::Null);
        out.push(Json::obj([
            ("assignTo", Json::str(to)),
            ("operator", Json::str(op)),
            ("value", value),
        ]));
    }
    out
}

/// A record op's `<inputAssignments>` → `field ← value` writes.
fn input_assignments_json(el: &Node, src: &str) -> Vec<Json> {
    let mut out = Vec::new();
    for ia in children_named(el, "inputAssignments", src) {
        let field = child_named(ia, "field", src)
            .map(|n| text_content(n, src))
            .unwrap_or_default();
        let value = child_named(ia, "value", src)
            .map(|v| value_json(v, src))
            .unwrap_or(Json::Null);
        out.push(Json::obj([("field", Json::str(field)), ("value", value)]));
    }
    out
}

/// A record op's `<filters>` → `field`/`operator`/`value` — which records the
/// op touches.
fn filters_json(el: &Node, src: &str) -> Vec<Json> {
    let mut out = Vec::new();
    for fl in children_named(el, "filters", src) {
        let field = child_named(fl, "field", src)
            .map(|n| text_content(n, src))
            .unwrap_or_default();
        let op = child_named(fl, "operator", src)
            .map(|n| text_content(n, src))
            .unwrap_or_default();
        let value = child_named(fl, "value", src)
            .map(|v| value_json(v, src))
            .unwrap_or(Json::Null);
        out.push(Json::obj([
            ("field", Json::str(field)),
            ("operator", Json::str(op)),
            ("value", value),
        ]));
    }
    out
}

/// A record lookup's `<queriedFields>` → the list of field API names read.
fn queried_fields_json(el: &Node, src: &str) -> Vec<Json> {
    children_named(el, "queriedFields", src)
        .map(|q| Json::str(text_content(q, src)))
        .filter(|j| j != &Json::str(""))
        .collect()
}

/// TT-86 screens: each `<fields>` → its `name` + `fieldType`. Screen fields are
/// the flow's user I/O (a `DisplayText` is output, an `InputField`/choice is
/// input); the `fieldType` is kept so the direction is recoverable without a new
/// node kind. Direct children only (nested section/column fields are left to a
/// later pass), lossless-tolerant of missing children.
fn screen_fields_json(el: &Node, src: &str) -> Vec<Json> {
    let mut out = Vec::new();
    for fld in children_named(el, "fields", src) {
        let name = child_named(fld, "name", src)
            .map(|n| text_content(n, src))
            .unwrap_or_default();
        let field_type = child_named(fld, "fieldType", src)
            .map(|n| text_content(n, src))
            .unwrap_or_default();
        out.push(Json::obj([
            ("name", Json::str(name)),
            ("fieldType", Json::str(field_type)),
        ]));
    }
    out
}

/// TT-86 waits: the names of the `<waitEvents>` the element pauses on (each
/// event's connector is control flow, handled by the connector walk). Document
/// order, empties skipped.
fn wait_events_json(el: &Node, src: &str) -> Vec<Json> {
    children_named(el, "waitEvents", src)
        .filter_map(|ev| child_named(ev, "name", src))
        .map(|n| text_content(n, src))
        .filter(|s| !s.is_empty())
        .map(Json::str)
        .collect()
}

/// Every `<elementReference>` text under an element, in document order. These
/// are the intra-flow data-flow uses (an assignment value, a condition
/// right-hand side, a filter value…). Recurses through non-reference wrappers;
/// an `elementReference` leaf is captured but not descended into.
fn collect_element_refs(el: &Node, src: &str, out: &mut Vec<String>) {
    for child in child_elements(el) {
        if tag_name(child, src) == Some("elementReference") {
            let t = text_content(child, src);
            if !t.is_empty() {
                out.push(t);
            }
        } else {
            collect_element_refs(child, src, out);
        }
    }
}

/// Flow depth, counted in elements. Exact longest simple path is NP-hard on
/// cyclic graphs, so the metric is **defined** as: prune back edges found by a
/// deterministic DFS (roots first `start`, else in-degree-0 nodes, else all;
/// out-edges in document order), then take the exact longest path of the
/// remaining DAG. Sound (a real path of that length exists), deterministic,
/// and loops can never inflate or hang it.
fn flow_depth(
    elements: &[(String, &crate::core::cst::Node, String)],
    edges: &[(String, String)],
) -> usize {
    use std::collections::{BTreeMap, BTreeSet};
    if elements.is_empty() {
        return 0;
    }
    let names: BTreeSet<&str> = elements.iter().map(|(n, _, _)| n.as_str()).collect();
    let mut out: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    let mut has_in: BTreeSet<&str> = BTreeSet::new();
    for (from, to) in edges {
        if names.contains(from.as_str()) && names.contains(to.as_str()) {
            out.entry(from).or_default().push(to);
            has_in.insert(to);
        }
    }
    let mut roots: Vec<&str> = if names.contains("start") {
        vec!["start"]
    } else {
        names
            .iter()
            .copied()
            .filter(|n| !has_in.contains(n))
            .collect()
    };
    if roots.is_empty() {
        roots = names.iter().copied().collect();
    }
    // Ensure every node gets classified even if unreachable from the roots.
    for n in &names {
        if !roots.contains(n) {
            roots.push(n);
        }
    }

    // Phase 1: iterative DFS (explicit stack; no recursion on hostile input)
    // classifying back edges: target currently on the DFS stack.
    #[derive(Clone, Copy, PartialEq)]
    enum Color {
        White,
        Gray,
        Black,
    }
    let mut color: BTreeMap<&str, Color> = names.iter().map(|n| (*n, Color::White)).collect();
    let mut dag: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for root in &roots {
        if color[*root] != Color::White {
            continue;
        }
        // Stack of (node, next-edge-index).
        let mut stack: Vec<(&str, usize)> = vec![(*root, 0)];
        color.insert(root, Color::Gray);
        while let Some((node, i)) = stack.pop() {
            let nexts = out.get(node).cloned().unwrap_or_default();
            if i < nexts.len() {
                stack.push((node, i + 1));
                let next = nexts[i];
                match color[next] {
                    Color::Gray => {} // back edge: pruned
                    Color::White => {
                        dag.entry(node).or_default().push(next);
                        color.insert(next, Color::Gray);
                        stack.push((next, 0));
                    }
                    Color::Black => {
                        dag.entry(node).or_default().push(next); // forward/cross: kept
                    }
                }
            } else {
                color.insert(node, Color::Black);
            }
        }
    }

    // Phase 2: exact longest path on the pruned DAG. Memoized post-order over
    // an explicit stack (no recursion, so hostile depth can't blow the native
    // stack): a node is finalized only after all its DAG successors are.
    let mut depth: BTreeMap<&str, usize> = BTreeMap::new();
    for root in &names {
        if depth.contains_key(*root) {
            continue;
        }
        let mut stack: Vec<(&str, bool)> = vec![(root, false)];
        while let Some((node, children_done)) = stack.pop() {
            if depth.contains_key(node) {
                continue;
            }
            let succ = dag.get(node).cloned().unwrap_or_default();
            if children_done || succ.is_empty() {
                let best = succ
                    .iter()
                    .filter_map(|s| depth.get(s))
                    .copied()
                    .max()
                    .unwrap_or(0);
                depth.insert(node, 1 + best);
            } else {
                stack.push((node, true));
                for s in succ {
                    if !depth.contains_key(s) {
                        stack.push((s, false));
                    }
                }
            }
        }
    }
    depth.values().copied().max().unwrap_or(1)
}

fn lower_validation_rule(g: &mut Graph, f: &SourceFile<'_>) {
    let rule_name = component_name(&f.rel_path, ".validationRule-meta.xml");
    let obj_name = owning_object(&f.rel_path).unwrap_or_else(|| "UnknownObject".to_string());
    ensure_sobject(g, &obj_name);
    let rule_id = format!("validation_rule::{obj_name}.{rule_name}");
    let mut props = vec![
        ("type_kind", Json::str("validation_rule")),
        ("language", Json::str("salesforce-metadata")),
        ("object", Json::str(obj_name.clone())),
        ("path", Json::str(f.rel_path.clone())),
    ];
    let mut parsed_formula: Option<crate::lang::salesforce::formula::FormulaRefs> = None;
    if let Some(root) = root_element(f) {
        if let Some(active) = child_named(root, "active", f.source) {
            props.push(("active", Json::str(text_content(active, f.source))));
        }
        // The raw formula is kept verbatim; TT-64 now *also* parses it for the
        // field references it depends on (see `attach_formula`).
        if let Some(formula) = child_named(root, "errorConditionFormula", f.source) {
            let text = text_content(formula, f.source);
            parsed_formula = Some(attach_formula(&mut props, &text));
        }
    }
    g.upsert_node(rule_id.clone(), ont::CONSTANT, rule_name, props);
    g.add_edge(
        sobject_id(&obj_name),
        edge::DECLARES,
        rule_id.clone(),
        vec![],
    );
    g.add_edge(file_id(f), edge::DECLARES, rule_id.clone(), vec![]);
    if let Some(refs) = &parsed_formula {
        emit_formula_field_edges(g, &rule_id, &obj_name, None, refs);
    }
}

/// Parse a formula string, push the `formula` / `formula_refs` /
/// `formula_system_refs` properties onto `props`, and hand back the parsed
/// references so the caller can emit `USES_TYPE` edges. Shared by validation
/// rules and formula fields.
fn attach_formula(
    props: &mut Vec<(&'static str, Json)>,
    text: &str,
) -> crate::lang::salesforce::formula::FormulaRefs {
    let refs = crate::lang::salesforce::formula::extract(text);
    props.push(("formula", Json::str(text.to_string())));
    props.push(("formula_refs", refs_json(&refs.refs)));
    if !refs.system_refs.is_empty() {
        props.push(("formula_system_refs", refs_json(&refs.system_refs)));
    }
    refs
}

/// A sorted JSON string array (the input is already sorted+deduped by the
/// parser, so ordering is deterministic).
fn refs_json(names: &[String]) -> Json {
    Json::Array(names.iter().map(|s| Json::str(s.clone())).collect())
}

/// For each *bare* field the formula references, add a `USES_TYPE` edge
/// `from → sobject_field::<Obj>.<Field>` (property `via = "formula"`), when the
/// owning object is known. Dotted-path heads and `$`-system refs are listed in
/// `formula_refs`/`formula_system_refs` but never resolved to a fabricated
/// target. `self_field` suppresses a formula field's self-reference.
fn emit_formula_field_edges(
    g: &mut Graph,
    from_id: &str,
    obj_name: &str,
    self_field: Option<&str>,
    refs: &crate::lang::salesforce::formula::FormulaRefs,
) {
    if obj_name == "UnknownObject" {
        return;
    }
    for field in &refs.bare_fields {
        if Some(field.as_str()) == self_field {
            continue;
        }
        g.add_edge(
            from_id.to_string(),
            edge::USES_TYPE,
            format!("sobject_field::{obj_name}.{field}"),
            vec![("via", Json::str("formula"))],
        );
    }
}

/// TT-78 legacy automation. A `Workflow` metadata file (`<Obj>.workflow-meta.xml`)
/// carries every Workflow Rule, field update, and alert for one SObject — the
/// owning object is the file stem (SFDX names the file after its object). Each
/// `<rules>` becomes a [`Function`] with `type_kind="workflow_rule"`, declared by
/// its object and file. Field references are resolved best-effort to the shared
/// `sobject_field::` ids so Apex, Flows, formulas, permissions, and workflow all
/// point at one field graph:
///
/// - `<criteriaItems><field>Obj.Field</field>` → [`USES_TYPE`] rule →
///   `sobject_field::Obj.Field` (`via="criteria"`).
/// - a rule `<formula>` is parsed by the TT-64 formula grammar; each bare field
///   → an edge to `sobject_field::<Obj>.<Field>` (`via="formula"`).
/// - each `<actions type="FieldUpdate">` names a sibling `<fieldUpdates>`; that
///   field update's `<field>` (on its `<targetObject>`, else this file's object)
///   → an edge `via="field_update"`.
///
/// Unresolvable references (missing dotted object, an action naming an unknown
/// field update) are skipped, never fabricated. Process Builder is a Flow
/// (`processType=Workflow`) and flows through the Flow lowering untouched.
///
/// [`Function`]: crate::ir::ontology::node::FUNCTION
/// [`USES_TYPE`]: crate::ir::ontology::edge::USES_TYPE
fn lower_workflow(g: &mut Graph, f: &SourceFile<'_>) {
    let obj_name = component_name(&f.rel_path, ".workflow-meta.xml");
    ensure_sobject(g, &obj_name);
    let Some(root) = root_element(f) else { return };

    // Map each field update's fullName → (bare field, resolved object). The
    // target object defaults to this file's object when not stated.
    let mut field_updates: std::collections::BTreeMap<String, (String, String)> =
        std::collections::BTreeMap::new();
    for fu in children_named(root, "fieldUpdates", f.source) {
        let Some(full) = child_named(fu, "fullName", f.source) else {
            continue;
        };
        let fu_name = text_content(full, f.source);
        if fu_name.is_empty() {
            continue;
        }
        let field = child_named(fu, "field", f.source)
            .map(|n| text_content(n, f.source))
            .unwrap_or_default();
        let target = child_named(fu, "targetObject", f.source)
            .map(|n| text_content(n, f.source))
            .filter(|s| !s.is_empty())
            .unwrap_or_else(|| obj_name.clone());
        field_updates.insert(fu_name, (field, target));
    }

    for rule in children_named(root, "rules", f.source) {
        let Some(full) = child_named(rule, "fullName", f.source) else {
            continue;
        };
        let rule_name = text_content(full, f.source);
        if rule_name.is_empty() {
            continue;
        }
        let rule_id = format!("workflow_rule::{obj_name}.{rule_name}");
        let mut props = vec![
            ("type_kind", Json::str("workflow_rule")),
            ("language", Json::str("salesforce-metadata")),
            ("object", Json::str(obj_name.clone())),
            ("path", Json::str(f.rel_path.clone())),
        ];
        if let Some(active) = child_named(rule, "active", f.source) {
            props.push(("active", Json::str(text_content(active, f.source))));
        }
        // A criteria `<formula>` reads fields on the workflow's object.
        let parsed_formula = child_named(rule, "formula", f.source)
            .map(|el| text_content(el, f.source))
            .filter(|s| !s.is_empty())
            .map(|text| attach_formula(&mut props, &text));
        g.upsert_node(rule_id.clone(), ont::FUNCTION, rule_name.clone(), props);
        g.add_edge(
            sobject_id(&obj_name),
            edge::DECLARES,
            rule_id.clone(),
            vec![],
        );
        g.add_edge(file_id(f), edge::DECLARES, rule_id.clone(), vec![]);

        if let Some(refs) = &parsed_formula {
            emit_formula_field_edges(g, &rule_id, &obj_name, None, refs);
        }

        // Criteria items: each `<field>` is a dotted `Obj.Field` reference.
        for item in children_named(rule, "criteriaItems", f.source) {
            let Some(fld) = child_named(item, "field", f.source) else {
                continue;
            };
            let dotted = text_content(fld, f.source);
            if let Some((cobj, cfield)) = dotted.split_once('.') {
                if !cobj.is_empty() && !cfield.is_empty() {
                    ensure_sobject(g, cobj);
                    g.add_edge(
                        rule_id.clone(),
                        edge::USES_TYPE,
                        format!("sobject_field::{cobj}.{cfield}"),
                        vec![("via", Json::str("criteria"))],
                    );
                }
            }
        }

        // Actions: a FieldUpdate action resolves to a sibling `<fieldUpdates>`
        // and the field it writes.
        for action in children_named(rule, "actions", f.source) {
            let atype = child_named(action, "type", f.source)
                .map(|n| text_content(n, f.source))
                .unwrap_or_default();
            if atype != "FieldUpdate" {
                continue;
            }
            let aname = child_named(action, "name", f.source)
                .map(|n| text_content(n, f.source))
                .unwrap_or_default();
            if let Some((field, target)) = field_updates.get(&aname) {
                if !field.is_empty() {
                    ensure_sobject(g, target);
                    g.add_edge(
                        rule_id.clone(),
                        edge::USES_TYPE,
                        format!("sobject_field::{target}.{field}"),
                        vec![("via", Json::str("field_update"))],
                    );
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::xml::parser::parse;

    struct Fixture {
        rel: &'static str,
        src: &'static str,
    }

    fn lower_fixtures(fixtures: &[Fixture]) -> Graph {
        let trees: Vec<_> = fixtures.iter().map(|f| parse(f.rel, f.src)).collect();
        let files: Vec<SourceFile> = fixtures
            .iter()
            .zip(&trees)
            .map(|(f, t)| SourceFile {
                rel_path: f.rel.to_string(),
                module_path: Vec::new(),
                source: f.src,
                root: &t.root,
            })
            .collect();
        lower("org", &files)
    }

    const OBJECT: Fixture = Fixture {
        rel: "force-app/main/default/objects/Case/Case.object-meta.xml",
        src: "<?xml version=\"1.0\"?>\n<CustomObject><label>Case</label>\n  <fields><fullName>Severity__c</fullName><type>Picklist</type></fields>\n</CustomObject>",
    };
    const FIELD: Fixture = Fixture {
        rel: "force-app/main/default/objects/Case/fields/Patient__c.field-meta.xml",
        src: "<?xml version=\"1.0\"?>\n<CustomField><fullName>Patient__c</fullName><type>Lookup</type><referenceTo>Contact</referenceTo><label>Patient</label></CustomField>",
    };
    const FLOW: Fixture = Fixture {
        rel: "force-app/main/default/flows/Intake.flow-meta.xml",
        src: "<?xml version=\"1.0\"?>\n<Flow><label>Intake</label><status>Active</status>\n  <recordLookups><name>find</name><object>Contact</object></recordLookups>\n  <recordUpdates><name>upd</name><object>Case</object></recordUpdates>\n  <actionCalls><name>notify</name><actionName>CareTeamNotifier</actionName><actionType>apex</actionType></actionCalls>\n  <subflows><name>sub</name><flowName>FollowUp</flowName></subflows>\n</Flow>",
    };
    const RULE: Fixture = Fixture {
        rel: "force-app/main/default/objects/Case/validationRules/Severity_Required.validationRule-meta.xml",
        src: "<ValidationRule><fullName>Severity_Required</fullName><active>true</active><errorConditionFormula>ISBLANK(TEXT(Severity__c))</errorConditionFormula></ValidationRule>",
    };

    #[test]
    fn object_lowers_to_sobject_type_with_inline_fields() {
        let g = lower_fixtures(&[OBJECT]);
        assert!(g.has_node("sobject::Case"));
        assert!(g.has_node("sobject_field::Case.Severity__c"));
        assert!(g.count_edges_of(edge::DECLARES) >= 2);
        let n = g.nodes().find(|n| n.id == "sobject::Case").unwrap();
        assert_eq!(n.kind, ont::TYPE);
        assert_eq!(
            n.props.get("type_kind").map(|j| j.to_line()),
            Some("\"sobject\"".to_string())
        );
    }

    #[test]
    fn field_file_declares_field_and_reference_edge() {
        let g = lower_fixtures(&[FIELD]);
        assert!(g.has_node("sobject_field::Case.Patient__c"));
        assert!(g.has_node("sobject::Contact"), "referenceTo target exists");
        let uses: Vec<_> = g.edges().filter(|e| e.kind == edge::USES_TYPE).collect();
        assert_eq!(uses.len(), 1);
        assert_eq!(uses[0].from, "sobject_field::Case.Patient__c");
        assert_eq!(uses[0].to, "sobject::Contact");
    }

    #[test]
    fn flow_emits_uses_type_calls_and_unresolved_action() {
        let g = lower_fixtures(&[FLOW]);
        assert!(g.has_node("flow::Intake"));
        let flow = g.nodes().find(|n| n.id == "flow::Intake").unwrap();
        assert_eq!(flow.kind, ont::FUNCTION);
        // Two record ops → two USES_TYPE edges to two objects.
        assert_eq!(g.count_edges_of(edge::USES_TYPE), 2);
        assert!(g.has_node("sobject::Contact") && g.has_node("sobject::Case"));
        // Apex action → CALLS an explicit unresolved endpoint.
        assert!(g.has_node("unresolved::sf_action::CareTeamNotifier"));
        // Subflow target not in batch → unresolved node under the flow id.
        let sub = g.nodes().find(|n| n.id == "flow::FollowUp").unwrap();
        assert_eq!(sub.kind, ont::UNRESOLVED);
        assert_eq!(g.count_edges_of(edge::CALLS), 2);
    }

    #[test]
    fn subflow_to_defined_flow_lands_on_the_real_node() {
        const FOLLOWUP: Fixture = Fixture {
            rel: "force-app/main/default/flows/FollowUp.flow-meta.xml",
            src: "<Flow><label>Follow Up</label></Flow>",
        };
        let g = lower_fixtures(&[FLOW, FOLLOWUP]);
        let sub = g.nodes().find(|n| n.id == "flow::FollowUp").unwrap();
        assert_eq!(sub.kind, ont::FUNCTION, "definition wins over reference");
    }

    #[test]
    fn validation_rule_lowers_with_opaque_formula() {
        let g = lower_fixtures(&[RULE]);
        let rule = g
            .nodes()
            .find(|n| n.id == "validation_rule::Case.Severity_Required")
            .unwrap();
        assert_eq!(rule.kind, ont::CONSTANT);
        assert!(rule.props.contains_key("formula"));
        assert!(g.has_node("sobject::Case"));
    }

    // TT-64: the formula is parsed for field references, which become a
    // deterministic `formula_refs` property and a `USES_TYPE` edge to the
    // owning object's field. `$Permission.Bypass` lands in system refs, not as
    // a fabricated field edge.
    #[test]
    fn validation_rule_formula_extracts_field_refs_and_edge() {
        const SYS_RULE: Fixture = Fixture {
            rel: "force-app/main/default/objects/Case/validationRules/Sev.validationRule-meta.xml",
            src: "<ValidationRule><fullName>Sev</fullName>\
                  <errorConditionFormula><![CDATA[ISBLANK(TEXT(Severity__c)) && NOT($Permission.Bypass)]]></errorConditionFormula>\
                  </ValidationRule>",
        };
        let g = lower_fixtures(&[SYS_RULE]);
        let rule = g
            .nodes()
            .find(|n| n.id == "validation_rule::Case.Sev")
            .unwrap();
        assert_eq!(
            rule.props.get("formula_refs").unwrap().to_line(),
            "[\"Severity__c\"]"
        );
        assert_eq!(
            rule.props.get("formula_system_refs").unwrap().to_line(),
            "[\"$Permission.Bypass\"]"
        );
        let uses: Vec<_> = g
            .edges()
            .filter(|e| e.kind == edge::USES_TYPE && e.from == "validation_rule::Case.Sev")
            .collect();
        assert_eq!(uses.len(), 1);
        assert_eq!(uses[0].to, "sobject_field::Case.Severity__c");
        assert_eq!(
            uses[0].props.get("via").map(|j| j.to_line()),
            Some("\"formula\"".to_string())
        );
    }

    // TT-64: a formula field parses the same way; its own name is never a
    // self-USES_TYPE edge.
    #[test]
    fn formula_field_extracts_refs() {
        const FORMULA_FIELD: Fixture = Fixture {
            rel: "force-app/main/default/objects/Case/fields/Total__c.field-meta.xml",
            src: "<CustomField><fullName>Total__c</fullName><type>Formula</type>\
                  <formula>Amount__c + Tax__c - Total__c</formula></CustomField>",
        };
        let g = lower_fixtures(&[FORMULA_FIELD]);
        let field = g
            .nodes()
            .find(|n| n.id == "sobject_field::Case.Total__c")
            .unwrap();
        assert_eq!(
            field.props.get("formula_refs").unwrap().to_line(),
            "[\"Amount__c\",\"Tax__c\",\"Total__c\"]"
        );
        let targets: std::collections::BTreeSet<&str> = g
            .edges()
            .filter(|e| e.kind == edge::USES_TYPE && e.from == "sobject_field::Case.Total__c")
            .map(|e| e.to.as_str())
            .collect();
        // Amount__c and Tax__c resolve; the self-reference Total__c does not.
        assert!(targets.contains("sobject_field::Case.Amount__c"));
        assert!(targets.contains("sobject_field::Case.Tax__c"));
        assert!(!targets.contains("sobject_field::Case.Total__c"));
    }

    const DEEP: Fixture = Fixture {
        rel: "force-app/main/default/flows/Deep.flow-meta.xml",
        src: "<Flow><label>Deep</label>\
              <start><connector><targetReference>A</targetReference></connector></start>\
              <assignments><name>A</name><connector><targetReference>B</targetReference></connector></assignments>\
              <decisions><name>B</name>\
                <rules><name>hot</name><connector><targetReference>C</targetReference></connector></rules>\
                <defaultConnector><targetReference>D</targetReference></defaultConnector>\
              </decisions>\
              <loops><name>C</name>\
                <nextValueConnector><targetReference>D</targetReference></nextValueConnector>\
                <noMoreValuesConnector><targetReference>E</targetReference></noMoreValuesConnector>\
              </loops>\
              <assignments><name>D</name><connector><targetReference>C</targetReference></connector></assignments>\
              <recordUpdates><name>E</name><object>Case</object>\
                <faultConnector><targetReference>Ghost</targetReference></faultConnector>\
              </recordUpdates>\
              </Flow>",
    };

    #[test]
    fn elements_become_nodes_with_flows_to_edges() {
        let g = lower_fixtures(&[DEEP]);
        for e in ["start", "A", "B", "C", "D", "E"] {
            assert!(g.has_node(&format!("flow_element::Deep.{e}")), "{e}");
        }
        // 8 connectors: start→A, A→B, B→C (rule), B→D (default), C→D (nextValue),
        // C→E (noMoreValues), D→C, E→Ghost (fault, to an unresolved target).
        let flows: Vec<_> = g.edges().filter(|e| e.kind == edge::FLOWS_TO).collect();
        assert_eq!(flows.len(), 8, "{flows:?}");
        // The fault target doesn't exist: explicit unresolved, never dropped.
        let ghost = g
            .nodes()
            .find(|n| n.id == "flow_element::Deep.Ghost")
            .expect("unresolved connector target");
        assert_eq!(ghost.kind, ont::UNRESOLVED);
        // Record op attaches to the element, not the flow.
        let uses: Vec<_> = g.edges().filter(|e| e.kind == edge::USES_TYPE).collect();
        assert_eq!(uses[0].from, "flow_element::Deep.E");
    }

    #[test]
    fn depth_counts_longest_acyclic_path_and_survives_loops() {
        let g = lower_fixtures(&[DEEP]);
        let flow = g.nodes().find(|n| n.id == "flow::Deep").unwrap();
        // DAG after pruning the D→C back edge: start→A→B→C→{D,E}. Longest
        // simple path start,A,B,C,D (or …,E) = 5 elements. The loop (D→C) is
        // correctly excluded — it can neither inflate the number nor hang.
        assert_eq!(flow.props.get("depth").unwrap().to_line(), "5");
        assert_eq!(flow.props.get("element_count").unwrap().to_line(), "6");
    }

    #[test]
    fn flow_without_connectors_still_has_depth_one() {
        let g = lower_fixtures(&[FLOW]);
        let flow = g.nodes().find(|n| n.id == "flow::Intake").unwrap();
        assert_eq!(flow.props.get("depth").unwrap().to_line(), "1");
        assert_eq!(flow.props.get("element_count").unwrap().to_line(), "4");
    }

    #[test]
    fn deterministic_output_across_runs() {
        let a = lower_fixtures(&[OBJECT, FIELD, FLOW, RULE]).to_jsonl();
        let b = lower_fixtures(&[OBJECT, FIELD, FLOW, RULE]).to_jsonl();
        assert_eq!(a, b);
    }

    // TT-77: a flow carrying real logic — a decision with a conditions block,
    // an assignment whose value is an `<elementReference>` to another element
    // (intra-flow data flow), a record create with inputAssignments, and a
    // record lookup with filters + queriedFields.
    const LOGIC: Fixture = Fixture {
        rel: "force-app/main/default/flows/Verify.flow-meta.xml",
        src: "<Flow><label>Verify</label>\
              <start><connector><targetReference>GenerateVerificationCode</targetReference></connector></start>\
              <assignments><name>GenerateVerificationCode</name>\
                <assignmentItems>\
                  <assignToReference>codeVar</assignToReference>\
                  <operator>Assign</operator>\
                  <value><stringValue>1234</stringValue></value>\
                </assignmentItems>\
                <connector><targetReference>Lookup</targetReference></connector>\
              </assignments>\
              <recordLookups><name>Lookup</name><object>Contact</object>\
                <queriedFields>Id</queriedFields>\
                <queriedFields>Email</queriedFields>\
                <filters><field>Email</field><operator>EqualTo</operator>\
                  <value><stringValue>x@y.z</stringValue></value></filters>\
                <connector><targetReference>DoesUserExist</targetReference></connector>\
              </recordLookups>\
              <decisions><name>DoesUserExist</name>\
                <rules><name>Exists</name>\
                  <conditionLogic>and</conditionLogic>\
                  <conditions>\
                    <leftValueReference>Lookup.Id</leftValueReference>\
                    <operator>IsNull</operator>\
                    <rightValue><booleanValue>false</booleanValue></rightValue>\
                  </conditions>\
                  <connector><targetReference>SetVerificationCode</targetReference></connector>\
                </rules>\
                <defaultConnector><targetReference>Create</targetReference></defaultConnector>\
              </decisions>\
              <assignments><name>SetVerificationCode</name>\
                <assignmentItems>\
                  <assignToReference>Contact.Code__c</assignToReference>\
                  <operator>Assign</operator>\
                  <value><elementReference>GenerateVerificationCode.verificationCode</elementReference></value>\
                </assignmentItems>\
              </assignments>\
              <recordCreates><name>Create</name><object>Contact</object>\
                <inputAssignments><field>Code__c</field>\
                  <value><elementReference>GenerateVerificationCode</elementReference></value>\
                </inputAssignments>\
              </recordCreates>\
              </Flow>",
    };

    fn element<'g>(g: &'g Graph, flow: &str, name: &str) -> &'g crate::graph::GraphNode {
        let id = format!("flow_element::{flow}.{name}");
        g.nodes().find(|n| n.id == id).expect(&id)
    }

    #[test]
    fn decision_captures_its_conditions() {
        let g = lower_fixtures(&[LOGIC]);
        let dec = element(&g, "Verify", "DoesUserExist");
        let conds = dec
            .props
            .get("conditions")
            .expect("decision carries a conditions property")
            .to_line();
        // The rule, its and/or logic, the condition triple, and the branch it
        // takes are all present in the deterministic JSON.
        assert!(conds.contains("\"conditionLogic\":\"and\""), "{conds}");
        assert!(conds.contains("\"left\":\"Lookup.Id\""), "{conds}");
        assert!(conds.contains("\"operator\":\"IsNull\""), "{conds}");
        assert!(conds.contains("\"type\":\"booleanValue\""), "{conds}");
        assert!(
            conds.contains("\"connector\":\"SetVerificationCode\""),
            "{conds}"
        );
    }

    #[test]
    fn assignment_captures_its_items() {
        let g = lower_fixtures(&[LOGIC]);
        let asn = element(&g, "Verify", "SetVerificationCode");
        let items = asn
            .props
            .get("assignments")
            .expect("assignment carries an assignments property")
            .to_line();
        assert!(
            items.contains("\"assignTo\":\"Contact.Code__c\""),
            "{items}"
        );
        assert!(items.contains("\"operator\":\"Assign\""), "{items}");
        assert!(items.contains("\"type\":\"elementReference\""), "{items}");
        assert!(
            items.contains("GenerateVerificationCode.verificationCode"),
            "{items}"
        );
    }

    #[test]
    fn record_ops_capture_inputs_filters_and_fields() {
        let g = lower_fixtures(&[LOGIC]);
        let lookup = element(&g, "Verify", "Lookup");
        let filters = lookup.props.get("filters").expect("filters").to_line();
        assert!(filters.contains("\"field\":\"Email\""), "{filters}");
        let fields = lookup
            .props
            .get("queriedFields")
            .expect("queriedFields")
            .to_line();
        assert_eq!(fields, "[\"Id\",\"Email\"]");
        let create = element(&g, "Verify", "Create");
        let inputs = create
            .props
            .get("inputAssignments")
            .expect("inputAssignments")
            .to_line();
        assert!(inputs.contains("\"field\":\"Code__c\""), "{inputs}");
    }

    #[test]
    fn element_reference_creates_data_dep_edge() {
        let g = lower_fixtures(&[LOGIC]);
        let deps: Vec<_> = g.edges().filter(|e| e.kind == edge::DATA_DEP).collect();
        // The assignment's value references GenerateVerificationCode (the
        // `.verificationCode` suffix stripped) → one DATA_DEP edge to it.
        assert!(
            deps.iter()
                .any(|e| e.from == "flow_element::Verify.SetVerificationCode"
                    && e.to == "flow_element::Verify.GenerateVerificationCode"),
            "{deps:?}"
        );
        // The record create's elementReference input also flows from the
        // generator. Every DATA_DEP points at a *defined* element, never a
        // fabricated one.
        assert!(deps.iter().all(|e| g
            .nodes()
            .find(|n| n.id == e.to)
            .map(|n| n.kind == ont::FUNCTION)
            .unwrap_or(false)));
    }

    #[test]
    fn data_dep_skips_undefined_and_self_references() {
        // `Solo`'s value references an element the flow never defines and also
        // itself: neither becomes a DATA_DEP edge (no fabrication, no self-loop).
        const SOLO: Fixture = Fixture {
            rel: "force-app/main/default/flows/Solo.flow-meta.xml",
            src: "<Flow><label>Solo</label>\
                  <assignments><name>Solo</name>\
                    <assignmentItems><assignToReference>v</assignToReference><operator>Assign</operator>\
                      <value><elementReference>Ghost.x</elementReference></value></assignmentItems>\
                    <assignmentItems><assignToReference>w</assignToReference><operator>Assign</operator>\
                      <value><elementReference>Solo.y</elementReference></value></assignmentItems>\
                  </assignments></Flow>",
        };
        let g = lower_fixtures(&[SOLO]);
        assert_eq!(g.count_edges_of(edge::DATA_DEP), 0);
    }

    // TT-78: a Workflow Rule becomes a Function node; its criteria field and the
    // field written by its FieldUpdate action resolve to shared sobject_field ids.
    const WORKFLOW: Fixture = Fixture {
        rel: "force-app/main/default/workflows/Case__c.workflow-meta.xml",
        src: "<?xml version=\"1.0\"?>\n<Workflow>\
              <rules>\
                <fullName>Escalate High Severity</fullName>\
                <active>true</active>\
                <criteriaItems><field>Case__c.Severity__c</field><operation>equals</operation><value>High</value></criteriaItems>\
                <actions><name>Set_Priority</name><type>FieldUpdate</type></actions>\
              </rules>\
              <fieldUpdates>\
                <fullName>Set_Priority</fullName>\
                <field>Priority__c</field>\
                <targetObject>Case__c</targetObject>\
              </fieldUpdates>\
              </Workflow>",
    };

    #[test]
    fn workflow_rule_becomes_function_with_field_edges() {
        let g = lower_fixtures(&[WORKFLOW]);
        let rule = g
            .nodes()
            .find(|n| n.id == "workflow_rule::Case__c.Escalate High Severity")
            .expect("workflow rule node");
        assert_eq!(rule.kind, ont::FUNCTION);
        assert_eq!(
            rule.props.get("type_kind").map(|j| j.to_line()),
            Some("\"workflow_rule\"".to_string())
        );
        // Criteria field → USES_TYPE to the shared field id.
        let crit = g
            .edges()
            .find(|e| {
                e.kind == edge::USES_TYPE
                    && e.from == rule.id
                    && e.to == "sobject_field::Case__c.Severity__c"
            })
            .expect("criteria field edge");
        assert_eq!(
            crit.props.get("via").map(|j| j.to_line()),
            Some("\"criteria\"".to_string())
        );
        // FieldUpdate action → USES_TYPE to the field it writes.
        let upd = g
            .edges()
            .find(|e| {
                e.kind == edge::USES_TYPE
                    && e.from == rule.id
                    && e.to == "sobject_field::Case__c.Priority__c"
            })
            .expect("field update edge");
        assert_eq!(
            upd.props.get("via").map(|j| j.to_line()),
            Some("\"field_update\"".to_string())
        );
        // Declared by both its object and its file.
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DECLARES && e.from == "sobject::Case__c" && e.to == rule.id));
    }

    // TT-86: a flow's data environment. An input Text variable, an sObject
    // collection variable, a formula, and a constant become typed binding nodes;
    // a loop over the collection variable takes a DATA_DEP on it.
    const ENV: Fixture = Fixture {
        rel: "force-app/main/default/flows/Env.flow-meta.xml",
        src: "<Flow><label>Env</label>\
              <variables><name>patientName</name><dataType>String</dataType>\
                <isCollection>false</isCollection><isInput>true</isInput><isOutput>false</isOutput></variables>\
              <variables><name>caseList</name><dataType>SObject</dataType>\
                <objectType>Case__c</objectType><isCollection>true</isCollection></variables>\
              <formulas><name>greeting</name><dataType>String</dataType>\
                <expression>IF(ISBLANK(patientName), TEXT(Case__c.Id), patientName)</expression></formulas>\
              <constants><name>DefaultStatus</name><dataType>String</dataType>\
                <value><stringValue>Open</stringValue></value></constants>\
              <textTemplates><name>Summary</name><text>Reviewed {!patientName}</text></textTemplates>\
              <start><connector><targetReference>Process</targetReference></connector></start>\
              <loops><name>Process</name><collectionReference>caseList</collectionReference>\
                <nextValueConnector><targetReference>Touch</targetReference></nextValueConnector>\
                <noMoreValuesConnector><targetReference>Done</targetReference></noMoreValuesConnector></loops>\
              <recordUpdates><name>Touch</name><object>Case__c</object>\
                <connector><targetReference>Process</targetReference></connector>\
                <faultConnector><targetReference>Done</targetReference></faultConnector></recordUpdates>\
              <assignments><name>Done</name></assignments>\
              </Flow>",
    };

    // The object referenced by the sObject variable and the formula head, so
    // `sobject::Case__c` is a real definition when the USES_TYPE edges resolve.
    const ENV_OBJECT: Fixture = Fixture {
        rel: "force-app/main/default/objects/Case__c/Case__c.object-meta.xml",
        src: "<CustomObject><label>Case</label></CustomObject>",
    };

    #[test]
    fn flow_variable_becomes_typed_binding() {
        let g = lower_fixtures(&[ENV, ENV_OBJECT]);
        let v = g
            .nodes()
            .find(|n| n.id == "flow_binding::Env.patientName")
            .expect("variable binding node");
        assert_eq!(v.kind, ont::CONSTANT);
        assert_eq!(
            v.props.get("type_kind").map(|j| j.to_line()),
            Some("\"flow_variable\"".to_string())
        );
        assert_eq!(
            v.props.get("dataType").map(|j| j.to_line()),
            Some("\"String\"".to_string())
        );
        assert_eq!(
            v.props.get("isInput").map(|j| j.to_line()),
            Some("\"true\"".to_string())
        );
        // Declared by the flow.
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DECLARES && e.from == "flow::Env" && e.to == v.id));
        // The sObject collection variable's objectType is a USES_TYPE on the object.
        assert!(g.edges().any(|e| e.kind == edge::USES_TYPE
            && e.from == "flow_binding::Env.caseList"
            && e.to == "sobject::Case__c"));
    }

    #[test]
    fn flow_formula_binding_captured() {
        let g = lower_fixtures(&[ENV, ENV_OBJECT]);
        let fo = g
            .nodes()
            .find(|n| n.id == "flow_binding::Env.greeting")
            .expect("formula binding node");
        assert_eq!(
            fo.props.get("type_kind").map(|j| j.to_line()),
            Some("\"flow_formula\"".to_string())
        );
        assert!(fo.props.contains_key("expression"));
        assert!(fo.props.contains_key("formula_refs"));
        // The formula's `Case__c.Id` head resolves to the known object.
        assert!(g.edges().any(|e| e.kind == edge::USES_TYPE
            && e.from == fo.id
            && e.to == "sobject::Case__c"
            && e.props.get("via").map(|j| j.to_line()) == Some("\"flow_formula\"".to_string())));
    }

    #[test]
    fn flow_constant_and_text_template_captured() {
        let g = lower_fixtures(&[ENV]);
        let c = g
            .nodes()
            .find(|n| n.id == "flow_binding::Env.DefaultStatus")
            .expect("constant binding node");
        assert_eq!(
            c.props.get("type_kind").map(|j| j.to_line()),
            Some("\"flow_constant\"".to_string())
        );
        assert!(c.props.get("value").unwrap().to_line().contains("Open"));
        let t = g
            .nodes()
            .find(|n| n.id == "flow_binding::Env.Summary")
            .expect("text template binding node");
        assert_eq!(
            t.props.get("type_kind").map(|j| j.to_line()),
            Some("\"flow_text_template\"".to_string())
        );
    }

    #[test]
    fn loop_collection_reference_emits_data_dep() {
        let g = lower_fixtures(&[ENV]);
        // The loop iterates the `caseList` collection variable: a DATA_DEP from
        // the loop element onto the binding.
        assert!(g.edges().any(|e| e.kind == edge::DATA_DEP
            && e.from == "flow_element::Env.Process"
            && e.to == "flow_binding::Env.caseList"
            && e.props.get("via").map(|j| j.to_line())
                == Some("\"collectionReference\"".to_string())));
    }

    #[test]
    fn fault_connector_on_any_element_flows_to() {
        let g = lower_fixtures(&[ENV]);
        // The recordUpdates element's faultConnector is a control-flow edge like
        // any other connector — verified here since TT-86 leans on it.
        assert!(g.edges().any(|e| e.kind == edge::FLOWS_TO
            && e.from == "flow_element::Env.Touch"
            && e.to == "flow_element::Env.Done"
            && e.props.get("via").map(|j| j.to_line()) == Some("\"faultConnector\"".to_string())));
    }
}
