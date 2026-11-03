//! Extractors: deterministic passes that project **derived views** out of the
//! one canonical base graph.
//!
//! The base graph ([`crate::graph::Graph`]) is the always-on, language-neutral
//! product: files, functions, types, calls. An [`Extractor`] reads that graph
//! (never the source, never the CST) and emits a *new* graph that answers one
//! question — the data model, the call graph, the type graph, domain clusters,
//! … — in a shape a non-author can load directly into Ontoloom. Extractors are
//! additive: a new one is a new view, never a change to the base graph or its
//! golden output.
//!
//! Every extractor is a pure function of the base graph and must be
//! **deterministic** — it walks the graph through the `BTreeMap`-ordered
//! [`Graph::nodes`]/[`Graph::edges`] iterators and builds its output through the
//! same de-duplicating, sorted [`Graph`] API, so the same base graph always
//! linearizes to byte-identical JSONL.
//!
//! [`Graph`]: crate::graph::Graph
//! [`Graph::nodes`]: crate::graph::Graph::nodes
//! [`Graph::edges`]: crate::graph::Graph::edges

use crate::graph::Graph;

pub mod archetypes;
pub mod data_ontology;
pub mod domains;
pub mod hierarchy;
pub mod layers;
pub mod lexicon;
pub mod workflow_spec;

pub use archetypes::ArchetypeExtractor;
pub use data_ontology::DataOntologyExtractor;
pub use domains::DomainExtractor;
pub use hierarchy::HierarchyExtractor;
pub use layers::LayerExtractor;
pub use lexicon::LexiconExtractor;
pub use workflow_spec::WorkflowSpecExtractor;

/// A deterministic derivation from the base graph to a focused view graph.
pub trait Extractor {
    /// Stable, kebab-case identifier used to select the extractor on the CLI
    /// (e.g. `data-ontology`). Never changes for a given extractor.
    fn name(&self) -> &'static str;

    /// Run the pass over the base `graph`, returning a new derived view graph.
    /// Must not mutate the input and must be a pure, deterministic function of
    /// it: same input graph → byte-identical [`Graph::to_jsonl`] output.
    ///
    /// [`Graph::to_jsonl`]: crate::graph::Graph::to_jsonl
    fn extract(&self, graph: &Graph) -> Graph;
}

/// The registry of built-in extractors, in a stable order.
pub fn extractors() -> Vec<Box<dyn Extractor>> {
    vec![
        Box::new(DataOntologyExtractor),
        Box::new(LayerExtractor),
        Box::new(LexiconExtractor),
        Box::new(WorkflowSpecExtractor),
        Box::new(ArchetypeExtractor),
        Box::new(DomainExtractor),
        Box::new(HierarchyExtractor),
    ]
}

/// Look up a built-in extractor by its [`Extractor::name`].
pub fn extractor_by_name(name: &str) -> Option<Box<dyn Extractor>> {
    extractors().into_iter().find(|e| e.name() == name)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn registry_names_are_unique_and_resolvable() {
        let mut names: Vec<&str> = extractors().iter().map(|e| e.name()).collect();
        let count = names.len();
        names.sort();
        names.dedup();
        assert_eq!(names.len(), count, "extractor names must be unique");
        for n in names {
            assert!(extractor_by_name(n).is_some(), "{n} must resolve");
        }
        assert!(extractor_by_name("no-such-extractor").is_none());
    }
}
