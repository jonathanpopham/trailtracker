//! TT-62 cross-provider linker: resolve `Unresolved` endpoints that one front
//! end could only name but another front end actually defines.
//!
//! Each language front end lowers in isolation, so a Salesforce Flow's
//! `actionCalls` to an Apex `@InvocableMethod` can only be recorded as an
//! explicit `unresolved::sf_action::<Name>` node ([`crate::lang::salesforce::lower`]) —
//! the Apex method lives in another provider's sub-graph. This pass runs once
//! over the *merged* graph, after every front end has lowered, and closes those
//! holes by qualified name.
//!
//! Resolution is **additive and provenanced**, never destructive: rather than
//! rewriting the original `CALLS`→unresolved edge (which would erase the honest
//! "this was unresolved at lowering time" fact), the linker
//!
//! - adds a *new* resolved `CALLS` edge from the same source element to the real
//!   target, tagged `resolved_by="linker"`, and
//! - marks the unresolved node `resolved=true` with a `resolved_target` pointer.
//!
//! The old edge and node remain, so provenance is preserved and output stays
//! deterministic (both stores are `BTreeMap`s; we only ever *add*, and every
//! `upsert_node` fills absent keys only). When a name has **no** match it is
//! left exactly as-is; when it has **more than one** match the linker never
//! guesses — it marks the node `ambiguous=true` and adds no resolved edge.

use crate::core::json::Json;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};

/// The prefix Salesforce flow lowering uses for an unresolved invocable action.
const SF_ACTION_PREFIX: &str = "unresolved::sf_action::";

/// Link cross-provider references on the merged graph in place. Currently:
/// flow `actionCalls` → the Apex `@InvocableMethod` of the same name. Runs at
/// the end of `analyze_dir`; deterministic (sorted iteration, additive writes).
pub fn link_cross_provider(graph: &mut Graph) {
    link_sf_actions_to_apex(graph);
    link_graphql_schema_to_resolvers(graph);
}

/// The front-end `language` prop values whose symbols count as GraphQL
/// *implementations*. A resolver / model for an SDL schema is written in the
/// server's host language; in the bio corpus that is TypeScript (and its
/// JavaScript siblings).
const IMPL_LANGUAGES: &[&str] = &["typescript", "javascript"];

/// TT-63 GraphQL → resolver linker: connect a GraphQL SDL schema element to the
/// host-language code symbol that implements it, by unambiguous same-name match.
///
/// A schema stands apart from the code that serves it: the GraphQL front end
/// lowers `civic-schema.graphql` into `Type` nodes (`type::Assertion`) and
/// root-operation `Function` nodes (`fn::Query::assertions#…`), while the
/// resolvers/models live in another front end's sub-graph entirely. Without a
/// bridge the schema domain floats semi-detached and blast-radius on a resolver
/// never reaches the schema it satisfies. This pass, run once over the merged
/// graph, adds the bridge:
///
/// - a schema **field** (root-operation `Function`) links to the same-named
///   host-language `Function` (the field resolver / handler);
/// - a schema **type** (`Type`) links to the same-named host-language `Type`
///   (the generated / hand-written model for that type).
///
/// The edge is [`edge::IMPLEMENTED_BY`], directed schema → implementation, so
/// (a) blast-radius of the implementation reaches the schema consumers and
/// (b) the schema's domain gains honest coupling to the implementer's domain.
///
/// Matching is **exact-case** (both languages are case-sensitive and the
/// same-name convention is exact) and kind-aligned (field↔function, type↔type)
/// — no prefix-stripping of `resolveX`/`registerX` guesswork. Like the call
/// resolution ladder and the Salesforce action linker, ambiguity is preserved,
/// never resolved by guessing: a schema element with exactly one same-name,
/// same-kind implementation gets the edge; **more than one** leaves the schema
/// node flagged `resolver_ambiguous=true` with a `resolver_candidate_count`, and
/// **zero** matches leaves it untouched (an honest hole).
fn link_graphql_schema_to_resolvers(graph: &mut Graph) {
    // Index host-language implementation symbols by exact simple name, split by
    // kind. `BTreeMap`/sorted pushes keep every downstream decision — and thus
    // golden output — deterministic. A name with >1 entry is genuinely
    // ambiguous and is never auto-linked.
    let mut impl_fns: std::collections::BTreeMap<String, Vec<String>> =
        std::collections::BTreeMap::new();
    let mut impl_types: std::collections::BTreeMap<String, Vec<String>> =
        std::collections::BTreeMap::new();
    for n in graph.nodes() {
        let is_impl_lang = matches!(
            n.props.get("language"),
            Some(Json::Str(s)) if IMPL_LANGUAGES.contains(&s.as_str())
        );
        if !is_impl_lang {
            continue;
        }
        match n.kind {
            ont::FUNCTION => impl_fns
                .entry(n.name.clone())
                .or_default()
                .push(n.id.clone()),
            ont::TYPE => impl_types
                .entry(n.name.clone())
                .or_default()
                .push(n.id.clone()),
            _ => {}
        }
    }

    // Collect the GraphQL schema nodes to consider (id, name, kind). `nodes()`
    // is BTreeMap-ordered so this list is already sorted by id.
    struct Schema {
        id: String,
        name: String,
        is_field: bool,
    }
    let schema: Vec<Schema> = graph
        .nodes()
        .filter(|n| n.props.get("language") == Some(&Json::str("graphql")))
        .filter(|n| n.kind == ont::FUNCTION || n.kind == ont::TYPE)
        .map(|n| Schema {
            id: n.id.clone(),
            name: n.name.clone(),
            is_field: n.kind == ont::FUNCTION,
        })
        .collect();

    for s in schema {
        let index = if s.is_field { &impl_fns } else { &impl_types };
        match index.get(&s.name).map(Vec::as_slice) {
            // Exactly one same-name, same-kind implementation: bridge it.
            Some([impl_id]) => {
                graph.add_edge(
                    s.id.clone(),
                    edge::IMPLEMENTED_BY,
                    impl_id.clone(),
                    vec![
                        (
                            "match_kind",
                            Json::str(if s.is_field { "field" } else { "type" }),
                        ),
                        ("name", Json::str(s.name.clone())),
                        ("resolved_by", Json::str("linker")),
                    ],
                );
            }
            // More than one candidate: preserve ambiguity, add no edge, flag the
            // schema node so the candidate set stays visible and honest.
            Some(multiple) if multiple.len() > 1 => {
                graph.upsert_node(
                    s.id.clone(),
                    if s.is_field { ont::FUNCTION } else { ont::TYPE },
                    s.name.clone(),
                    vec![
                        ("resolver_ambiguous", Json::Bool(true)),
                        ("resolver_candidate_count", Json::U64(multiple.len() as u64)),
                    ],
                );
            }
            // Zero matches (or empty slice, defensively): leave as-is.
            _ => {}
        }
    }
}

/// Build a case-folded index from an invocable Apex method's simple name to the
/// ids of every `@InvocableMethod` carrying that name. A name with more than one
/// entry is genuinely ambiguous (two invocables the same name) and is never
/// auto-resolved. `BTreeMap` keeps the index — and thus every downstream
/// decision — deterministic.
fn invocable_index(graph: &Graph) -> std::collections::BTreeMap<String, Vec<String>> {
    let mut index: std::collections::BTreeMap<String, Vec<String>> =
        std::collections::BTreeMap::new();
    for n in graph.nodes() {
        if n.kind == ont::FUNCTION && n.props.get("invocable") == Some(&Json::Bool(true)) {
            index
                .entry(n.name.to_ascii_lowercase())
                .or_default()
                .push(n.id.clone());
        }
    }
    index
}

fn link_sf_actions_to_apex(graph: &mut Graph) {
    let index = invocable_index(graph);

    // Collect the unresolved sf_action nodes (id + the action name to match on).
    // `nodes()` is BTreeMap-ordered, so this list is already sorted by id.
    let actions: Vec<(String, String)> = graph
        .nodes()
        .filter(|n| n.kind == ont::UNRESOLVED && n.id.starts_with(SF_ACTION_PREFIX))
        .map(|n| (n.id.clone(), n.name.clone()))
        .collect();

    for (action_id, action_name) in actions {
        let matches = index.get(&action_name.to_ascii_lowercase());
        match matches.map(|m| m.as_slice()) {
            // Exactly one invocable: resolve it. Re-point by *adding* a resolved
            // edge from every source element that called the unresolved node,
            // then flag the node resolved with a pointer to its real target.
            Some([apex_id]) => {
                let callers: Vec<String> = graph
                    .edges()
                    .filter(|e| e.kind == edge::CALLS && e.to == action_id)
                    .map(|e| e.from.clone())
                    .collect();
                for from in callers {
                    graph.add_edge(
                        from,
                        edge::CALLS,
                        apex_id.clone(),
                        vec![
                            ("via", Json::str("actionCalls")),
                            ("resolved_by", Json::str("linker")),
                        ],
                    );
                }
                graph.upsert_node(
                    action_id.clone(),
                    ont::UNRESOLVED,
                    action_name.clone(),
                    vec![
                        ("resolved", Json::Bool(true)),
                        ("resolved_target", Json::str(apex_id.clone())),
                    ],
                );
            }
            // More than one invocable of this name: never guess. Flag ambiguous,
            // add no resolved edge — the hole stays honest.
            Some(multiple) if multiple.len() > 1 => {
                graph.upsert_node(
                    action_id.clone(),
                    ont::UNRESOLVED,
                    action_name.clone(),
                    vec![("ambiguous", Json::Bool(true))],
                );
            }
            // Zero matches (or an empty slice, defensively): leave as-is.
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Minimal stand-ins for what the real front ends emit: one flow element
    /// that CALLS an `unresolved::sf_action::<Name>`, plus zero or more Apex
    /// invocable Function nodes of a given simple name.
    fn action_node(g: &mut Graph, name: &str) -> String {
        let id = format!("{SF_ACTION_PREFIX}{name}");
        g.upsert_node(
            id.clone(),
            ont::UNRESOLVED,
            name.to_string(),
            vec![("reference_kind", Json::str("salesforce_action"))],
        );
        // The source flow element and its CALLS edge to the unresolved node.
        let element = format!("flow_element::F.{name}Call");
        g.upsert_node(
            element.clone(),
            ont::FUNCTION,
            format!("{name}Call"),
            vec![("type_kind", Json::str("flow_element"))],
        );
        g.add_edge(
            element,
            edge::CALLS,
            id.clone(),
            vec![("via", Json::str("actionCalls"))],
        );
        id
    }

    fn invocable(g: &mut Graph, id: &str, name: &str) {
        g.upsert_node(
            id.to_string(),
            ont::FUNCTION,
            name.to_string(),
            vec![
                ("language", Json::str("apex")),
                ("invocable", Json::Bool(true)),
            ],
        );
    }

    fn resolved_edge_to<'g>(g: &'g Graph, apex_id: &str) -> Option<&'g crate::graph::GraphEdge> {
        g.edges().find(|e| {
            e.kind == edge::CALLS
                && e.to == apex_id
                && e.props.get("resolved_by") == Some(&Json::str("linker"))
        })
    }

    #[test]
    fn matching_invocable_resolves_case_insensitively() {
        let mut g = Graph::new();
        // Flow names the action `VerifyContact`; Apex method is `verifyContact`.
        let action_id = action_node(&mut g, "VerifyContact");
        invocable(
            &mut g,
            "fn::ContactVerification.verifyContact#5",
            "verifyContact",
        );

        link_cross_provider(&mut g);

        // A resolved CALLS edge now points at the real Apex Function node…
        let e = resolved_edge_to(&g, "fn::ContactVerification.verifyContact#5")
            .expect("resolved linker edge");
        assert_eq!(e.from, "flow_element::F.VerifyContactCall");
        assert_eq!(e.props.get("via"), Some(&Json::str("actionCalls")));
        // …and the unresolved node is flagged resolved with a target pointer.
        let node = g.nodes().find(|n| n.id == action_id).unwrap();
        assert_eq!(node.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(
            node.props.get("resolved_target"),
            Some(&Json::str("fn::ContactVerification.verifyContact#5"))
        );
        // The original unresolved CALLS edge is preserved (provenance).
        assert!(g
            .edges()
            .any(|e| e.kind == edge::CALLS && e.to == action_id));
    }

    #[test]
    fn no_matching_invocable_stays_unresolved() {
        let mut g = Graph::new();
        let action_id = action_node(&mut g, "CareTeamNotifier");
        // A different invocable that must not match.
        invocable(&mut g, "fn::Other.somethingElse#1", "somethingElse");

        link_cross_provider(&mut g);

        let node = g.nodes().find(|n| n.id == action_id).unwrap();
        assert_eq!(node.props.get("resolved"), None);
        assert_eq!(node.props.get("ambiguous"), None);
        assert!(
            g.edges().all(|e| !e.props.contains_key("resolved_by")),
            "no linker edge for an unmatched action"
        );
    }

    #[test]
    fn ambiguous_invocables_do_not_resolve() {
        let mut g = Graph::new();
        let action_id = action_node(&mut g, "Verify");
        // Two invocables share the same simple name → ambiguous, never guessed.
        invocable(&mut g, "fn::A.verify#1", "Verify");
        invocable(&mut g, "fn::B.verify#2", "verify");

        link_cross_provider(&mut g);

        let node = g.nodes().find(|n| n.id == action_id).unwrap();
        assert_eq!(node.props.get("ambiguous"), Some(&Json::Bool(true)));
        assert_eq!(node.props.get("resolved"), None);
        assert!(
            g.edges().all(|e| !e.props.contains_key("resolved_by")),
            "no resolved edge is added for an ambiguous action"
        );
    }

    // --- GraphQL schema → resolver linkage ---------------------------------

    /// A GraphQL SDL `Type` node, as the graphql front end emits it.
    fn gql_type(g: &mut Graph, name: &str) -> String {
        let id = format!("type::{name}");
        g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.to_string(),
            vec![("language", Json::str("graphql"))],
        );
        id
    }

    /// A GraphQL root-operation field `Function` node.
    fn gql_field(g: &mut Graph, root: &str, name: &str) -> String {
        let id = format!("fn::{root}::{name}#1");
        g.upsert_node(
            id.clone(),
            ont::FUNCTION,
            name.to_string(),
            vec![
                ("language", Json::str("graphql")),
                ("is_field", Json::Bool(true)),
                ("parent_type", Json::str(root.to_string())),
            ],
        );
        id
    }

    /// A host-language (TypeScript) implementation node of a given kind.
    fn ts_node(g: &mut Graph, id: &str, kind: &'static str, name: &str) {
        g.upsert_node(
            id.to_string(),
            kind,
            name.to_string(),
            vec![("language", Json::str("typescript"))],
        );
    }

    fn implemented_by<'g>(g: &'g Graph, schema_id: &str) -> Option<&'g crate::graph::GraphEdge> {
        g.edges()
            .find(|e| e.kind == edge::IMPLEMENTED_BY && e.from == schema_id)
    }

    #[test]
    fn schema_type_links_to_lone_ts_model() {
        let mut g = Graph::new();
        let ty = gql_type(&mut g, "Assertion");
        ts_node(&mut g, "type::civic::Assertion", ont::TYPE, "Assertion");

        link_cross_provider(&mut g);

        let e = implemented_by(&g, &ty).expect("schema type should link to its TS model");
        assert_eq!(e.to, "type::civic::Assertion");
        assert_eq!(e.props.get("match_kind"), Some(&Json::str("type")));
        assert_eq!(e.props.get("resolved_by"), Some(&Json::str("linker")));
    }

    #[test]
    fn schema_field_links_to_lone_ts_resolver() {
        let mut g = Graph::new();
        let field = gql_field(&mut g, "Query", "assertions");
        ts_node(
            &mut g,
            "fn::civic::assertions#12",
            ont::FUNCTION,
            "assertions",
        );

        link_cross_provider(&mut g);

        let e = implemented_by(&g, &field).expect("schema field should link to its TS resolver");
        assert_eq!(e.to, "fn::civic::assertions#12");
        assert_eq!(e.props.get("match_kind"), Some(&Json::str("field")));
    }

    #[test]
    fn no_matching_symbol_leaves_schema_bare() {
        let mut g = Graph::new();
        let ty = gql_type(&mut g, "Assertion");
        // A same-name symbol of the *wrong* kind (function, not type) must not match.
        ts_node(&mut g, "fn::civic::Assertion#3", ont::FUNCTION, "Assertion");

        link_cross_provider(&mut g);

        assert!(implemented_by(&g, &ty).is_none());
        let node = g.nodes().find(|n| n.id == ty).unwrap();
        assert_eq!(node.props.get("resolver_ambiguous"), None);
    }

    #[test]
    fn kind_alignment_field_does_not_match_type() {
        let mut g = Graph::new();
        let field = gql_field(&mut g, "Query", "organization");
        // A TS *type* named organization must not satisfy a schema *field*.
        ts_node(
            &mut g,
            "type::civic::organization",
            ont::TYPE,
            "organization",
        );

        link_cross_provider(&mut g);

        assert!(implemented_by(&g, &field).is_none());
    }

    #[test]
    fn ambiguous_candidates_preserve_ambiguity() {
        let mut g = Graph::new();
        let ty = gql_type(&mut g, "Event");
        ts_node(&mut g, "type::a::Event", ont::TYPE, "Event");
        ts_node(&mut g, "type::b::Event", ont::TYPE, "Event");

        link_cross_provider(&mut g);

        assert!(
            implemented_by(&g, &ty).is_none(),
            "two candidates must never be guessed"
        );
        let node = g.nodes().find(|n| n.id == ty).unwrap();
        assert_eq!(
            node.props.get("resolver_ambiguous"),
            Some(&Json::Bool(true))
        );
        assert_eq!(
            node.props.get("resolver_candidate_count"),
            Some(&Json::U64(2))
        );
    }

    #[test]
    fn matching_is_exact_case() {
        let mut g = Graph::new();
        let ty = gql_type(&mut g, "Event");
        // Different case must not match — both languages are case-sensitive.
        ts_node(&mut g, "fn::civic::event#7", ont::FUNCTION, "event");
        ts_node(&mut g, "type::civic::event", ont::TYPE, "event");

        link_cross_provider(&mut g);

        assert!(implemented_by(&g, &ty).is_none());
    }

    #[test]
    fn implemented_by_is_a_specializes_family_edge() {
        use crate::ir::ontology::{parent_relation, relation};
        assert_eq!(
            parent_relation(edge::IMPLEMENTED_BY),
            Some(relation::SPECIALIZES),
            "coupling and blast-radius depend on this classification",
        );
    }
}
