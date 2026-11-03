//! The data-ontology extractor: recover the **data model** from the base graph.
//!
//! Clients and Ontoloom want the entity/relationship schema hiding inside a
//! codebase — the Salesforce SObjects and their lookups, the structs and their
//! type references — not the whole call graph. This extractor projects exactly
//! that view:
//!
//! - **Entity** — every [`Type`] node becomes an entity (kind kept as `Type`,
//!   tagged `view: "data_ontology"`). Salesforce SObjects (`type_kind:
//!   "sobject"`) and general struct/record/class types from any front end are
//!   all data types in this sense; their language and `type_kind` are carried
//!   through so a reader can tell an SObject from a Rust struct.
//! - **Attribute** — every [`Constant`] a data type *declares* (a base-graph
//!   `DECLARES` edge from an entity to a `Constant`) becomes a child attribute
//!   node, `DECLARES`-linked to its entity in the derived graph. This captures
//!   Salesforce `sobject_field`s and, generally, any language whose type
//!   members lower to declared constants. The field's `type_kind`, `field_type`
//!   and `label` ride along.
//! - **Relationship** — a base-graph [`USES_TYPE`] edge whose target is an
//!   entity is lifted to an **entity → entity** edge (kind [`USES_TYPE`],
//!   `via: "reference"`). Salesforce `referenceTo` edges live on the *field*
//!   (`sobject_field → target SObject`); we route them up to the owning entity
//!   so the data model reads object-to-object. Direct type→type references are
//!   passed through as-is. Edges whose source is neither an entity nor an
//!   entity's attribute (e.g. a flow element's record-op `USES_TYPE`) are *not*
//!   promoted — the derived graph stays a clean entity/attribute/relationship
//!   view.
//!
//! The pass is a pure, deterministic function of the base graph: it walks the
//! `BTreeMap`-ordered node/edge iterators and writes through the sorted,
//! de-duplicating [`Graph`] API, so the output is byte-stable across runs.
//!
//! [`Type`]: crate::ir::ontology::node::TYPE
//! [`Constant`]: crate::ir::ontology::node::CONSTANT
//! [`USES_TYPE`]: crate::ir::ontology::edge::USES_TYPE

use std::collections::{BTreeMap, BTreeSet};

use crate::core::json::Json;
use crate::graph::{Graph, GraphNode};
use crate::ir::ontology::{edge, node as ont};

use super::Extractor;

/// Property key marking a node as belonging to the data-ontology view.
const VIEW: &str = "data_ontology";

/// Recover the entity/attribute/relationship data model from the base graph.
pub struct DataOntologyExtractor;

impl Extractor for DataOntologyExtractor {
    fn name(&self) -> &'static str {
        "data-ontology"
    }

    fn extract(&self, graph: &Graph) -> Graph {
        let mut out = Graph::new();

        // The entities: every Type node. Collected first so relationship
        // routing can test membership.
        let entities: BTreeSet<&str> = graph
            .nodes()
            .filter(|n| n.kind == ont::TYPE)
            .map(|n| n.id.as_str())
            .collect();

        // attribute id -> owning entity id, from DECLARES edges whose source is
        // an entity. First entity to declare a node wins (deterministic: edges
        // are iterated in stable signature order). A field is also DECLARES-d by
        // its File, but a File is not an entity, so the entity always wins.
        let mut owner: BTreeMap<&str, &str> = BTreeMap::new();
        for e in graph.edges().filter(|e| e.kind == edge::DECLARES) {
            if entities.contains(e.from.as_str()) {
                owner.entry(e.to.as_str()).or_insert(e.from.as_str());
            }
        }

        // Entity nodes.
        for n in graph.nodes().filter(|n| n.kind == ont::TYPE) {
            let mut props = vec![("view", Json::str(VIEW))];
            carry(&mut props, n, "type_kind");
            carry(&mut props, n, "language");
            carry(&mut props, n, "label");
            out.upsert_node(n.id.clone(), ont::TYPE, n.name.clone(), props);
        }

        // Attribute nodes: Constants an entity declares.
        for n in graph.nodes().filter(|n| n.kind == ont::CONSTANT) {
            let Some(entity_id) = owner.get(n.id.as_str()) else {
                continue;
            };
            let mut props = vec![("view", Json::str(VIEW))];
            carry(&mut props, n, "type_kind");
            carry(&mut props, n, "field_type");
            carry(&mut props, n, "label");
            carry(&mut props, n, "object");
            out.upsert_node(n.id.clone(), ont::CONSTANT, n.name.clone(), props);
            out.add_edge(
                (*entity_id).to_string(),
                edge::DECLARES,
                n.id.clone(),
                vec![],
            );
        }

        // Relationship edges: USES_TYPE lifted to entity → entity.
        for e in graph.edges().filter(|e| e.kind == edge::USES_TYPE) {
            // Target must itself be an entity.
            if !entities.contains(e.to.as_str()) {
                continue;
            }
            // Source: the entity directly, or the entity that owns the source
            // attribute (Salesforce referenceTo lives on the field). Anything
            // else (e.g. a flow element's record op) is not entity-to-entity and
            // is left out of the data model.
            let source = if entities.contains(e.from.as_str()) {
                Some(e.from.as_str())
            } else {
                owner.get(e.from.as_str()).copied()
            };
            if let Some(src) = source {
                out.add_edge(
                    src.to_string(),
                    edge::USES_TYPE,
                    e.to.clone(),
                    vec![("via", Json::str("reference"))],
                );
            }
        }

        out
    }
}

/// Copy prop `key` from base node `n` into `props` if present.
fn carry(props: &mut Vec<(&'static str, Json)>, n: &GraphNode, key: &'static str) {
    if let Some(v) = n.props.get(key) {
        props.push((key, v.clone()));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A hand-built base graph: two SObjects (Account, Contact), a couple of
    /// `sobject_field` constants, and a `referenceTo` USES_TYPE from the field
    /// up to the target object — the exact shape the Salesforce front end emits.
    fn sample_base() -> Graph {
        let mut g = Graph::new();
        // Entities.
        g.upsert_node(
            "sobject::Account",
            ont::TYPE,
            "Account",
            vec![
                ("type_kind", Json::str("sobject")),
                ("language", Json::str("salesforce-metadata")),
            ],
        );
        g.upsert_node(
            "sobject::Contact",
            ont::TYPE,
            "Contact",
            vec![
                ("type_kind", Json::str("sobject")),
                ("language", Json::str("salesforce-metadata")),
            ],
        );
        // Fields.
        g.upsert_node(
            "sobject_field::Account.Name",
            ont::CONSTANT,
            "Name",
            vec![
                ("type_kind", Json::str("sobject_field")),
                ("field_type", Json::str("Text")),
                ("object", Json::str("Account")),
            ],
        );
        g.upsert_node(
            "sobject_field::Contact.AccountId",
            ont::CONSTANT,
            "AccountId",
            vec![
                ("type_kind", Json::str("sobject_field")),
                ("field_type", Json::str("Lookup")),
                ("object", Json::str("Contact")),
            ],
        );
        // Declarations (entity -> field), as the front end emits them.
        g.add_edge(
            "sobject::Account",
            edge::DECLARES,
            "sobject_field::Account.Name",
            vec![],
        );
        g.add_edge(
            "sobject::Contact",
            edge::DECLARES,
            "sobject_field::Contact.AccountId",
            vec![],
        );
        // referenceTo: the lookup field points at the target object.
        g.add_edge(
            "sobject_field::Contact.AccountId",
            edge::USES_TYPE,
            "sobject::Account",
            vec![("via", Json::str("referenceTo"))],
        );
        g
    }

    #[test]
    fn emits_entities_attributes_and_a_lifted_relationship() {
        let derived = DataOntologyExtractor.extract(&sample_base());

        // Two entities, tagged for the data-ontology view.
        for id in ["sobject::Account", "sobject::Contact"] {
            let n = derived.nodes().find(|n| n.id == id).expect(id);
            assert_eq!(n.kind, ont::TYPE);
            assert_eq!(n.props.get("view"), Some(&Json::str(VIEW)));
        }
        assert_eq!(derived.count_nodes_of(ont::TYPE), 2);

        // Both attributes present and DECLARES-linked to their entities.
        assert!(derived.has_node("sobject_field::Account.Name"));
        assert!(derived.has_node("sobject_field::Contact.AccountId"));
        assert_eq!(derived.count_edges_of(edge::DECLARES), 2);

        // The referenceTo is lifted to an entity -> entity relationship.
        let rels: Vec<_> = derived
            .edges()
            .filter(|e| e.kind == edge::USES_TYPE)
            .collect();
        assert_eq!(rels.len(), 1);
        assert_eq!(rels[0].from, "sobject::Contact");
        assert_eq!(rels[0].to, "sobject::Account");
        assert_eq!(rels[0].props.get("via"), Some(&Json::str("reference")));
    }

    #[test]
    fn deterministic_across_runs() {
        let base = sample_base();
        let a = DataOntologyExtractor.extract(&base).to_jsonl();
        let b = DataOntologyExtractor.extract(&base).to_jsonl();
        assert_eq!(a, b);
        assert!(!a.is_empty());
    }

    #[test]
    fn non_entity_source_edges_are_not_promoted() {
        // A flow element (Function) with a record-op USES_TYPE onto an SObject
        // must NOT become a data-model relationship: it is not entity-to-entity.
        let mut g = Graph::new();
        g.upsert_node(
            "sobject::Case",
            ont::TYPE,
            "Case",
            vec![("type_kind", Json::str("sobject"))],
        );
        g.upsert_node(
            "flow_element::Intake.upd",
            ont::FUNCTION,
            "upd",
            vec![("type_kind", Json::str("flow_element"))],
        );
        g.add_edge(
            "flow_element::Intake.upd",
            edge::USES_TYPE,
            "sobject::Case",
            vec![("via", Json::str("recordUpdates"))],
        );

        let derived = DataOntologyExtractor.extract(&g);
        assert!(derived.has_node("sobject::Case"));
        assert!(!derived.has_node("flow_element::Intake.upd"));
        assert_eq!(derived.count_edges_of(edge::USES_TYPE), 0);
    }
}
