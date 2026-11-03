//! The TrailTracker ontology: the language-neutral vocabulary that every front
//! end lowers into. It is rooted in lambda-calculus-accessible concepts so that
//! cross-language reasoning has a stable foundation, with practical codebase
//! concepts layered on top.
//!
//! Lambda mapping:
//! - [`FUNCTION`] ≈ abstraction (λ).
//! - [`CALLS`] ≈ application.
//! - [`CONSTANT`] ≈ value / literal binding.
//! - [`TYPE`] ≈ type, type declaration, type usage.
//! - [`MODULE`] / [`FILE`] / [`PACKAGE`] ≈ scopes / environments.
//!
//! These are intentionally `&'static str` so they double as the graph's
//! on-the-wire labels with zero translation.

/// Node kinds.
pub mod node {
    /// A source file on disk.
    pub const FILE: &str = "File";
    /// A module / namespace scope.
    pub const MODULE: &str = "Module";
    /// A function, method, or associated function (an abstraction).
    pub const FUNCTION: &str = "Function";
    /// A type declaration: struct, enum, trait, union, or alias.
    pub const TYPE: &str = "Type";
    /// A const or static binding (a value).
    pub const CONSTANT: &str = "Constant";
    /// A crate / assembly / project.
    pub const PACKAGE: &str = "Package";
    /// A logical node for a dependency not held in the project.
    pub const EXTERNAL_DEPENDENCY: &str = "ExternalDependency";
    /// A logical node for a referenced symbol that could not be resolved.
    pub const UNRESOLVED: &str = "UnresolvedSymbol";
    /// A macro definition or invocation target.
    pub const MACRO: &str = "Macro";
    /// One statement inside a function body — the fine-grained unit of the
    /// opt-in CPG overlay (ADR-0003). Emitted only by the `cpg` analysis
    /// path, never by the base graph; carried by [`super::edge::FLOWS_TO`]
    /// (control flow) and [`super::edge::DATA_DEP`] (def-use) edges.
    pub const STATEMENT: &str = "Statement";
}

/// Relationship kinds.
pub mod edge {
    /// Structural containment (package→file, module→module).
    pub const CONTAINS: &str = "CONTAINS";
    /// A scope declares a definition (file/module→function/type/const).
    pub const DECLARES: &str = "DECLARES";
    /// A function applies another function (call site).
    pub const CALLS: &str = "CALLS";
    /// A function reads a module-level constant binding.
    pub const READS: &str = "READS";
    /// A file imports a path (`use` / `using`).
    pub const IMPORTS: &str = "IMPORTS";
    /// A package/file depends on an external dependency.
    pub const DEPENDS_ON: &str = "DEPENDS_ON";
    /// A function or type references a type.
    pub const USES_TYPE: &str = "USES_TYPE";
    /// An impl associates a type with a trait it implements.
    pub const IMPLEMENTS: &str = "IMPLEMENTS";
    /// A type owns a method (associated function with a receiver).
    pub const HAS_METHOD: &str = "HAS_METHOD";
    /// A subtype extends a supertype (class inheritance). Reserved for
    /// inheritance languages (Python, Java, Kotlin, …); **not emitted by the
    /// Rust front end** (Rust has no inheritance). Kept distinct from
    /// [`IMPLEMENTS`] (conforms-to) — see `docs/ir-atlas.md`.
    pub const EXTENDS: &str = "EXTENDS";
    /// Control flow between steps of a declarative workflow (e.g. Salesforce
    /// Flow connectors). Directed: execution proceeds from → to. Distinct from
    /// [`CALLS`] (application of an abstraction): a connector transfers
    /// control, it does not apply the target.
    pub const FLOWS_TO: &str = "FLOWS_TO";
    /// Data flow: a def/use dependency where the *from* element consumes a value
    /// produced by the *to* element (e.g. a Salesforce Flow assignment whose
    /// value is an `<elementReference>` to another element, or a decision whose
    /// condition reads another element's output). Directed: data flows from the
    /// referenced (producer) element into the referencing (consumer) one, so the
    /// edge points consumer → producer — the dependency direction, mirroring
    /// [`USES_TYPE`] and [`CALLS`]. Distinct from [`FLOWS_TO`] (control): a
    /// value reference moves data, not the program counter. The CPG data-flow
    /// overlay (TT-72) applied intra-flow (TT-77).
    pub const DATA_DEP: &str = "DATA_DEP";
    /// Cross-language realization: a declarative schema element (e.g. a GraphQL
    /// SDL type or a root-operation field) is *implemented by* a code symbol in
    /// another front end (e.g. the TypeScript resolver / model of the same
    /// name). Emitted only by the cross-provider [`crate::pipeline::linker`]
    /// over the merged graph, never by a single front end — the two sides live
    /// in different sub-graphs. Directed **schema → implementation**: the
    /// contract points at the code that realizes it, so blast-radius of the
    /// implementation (reverse reachability) now reaches the schema consumers,
    /// and the schema's domain gains honest coupling to the implementer's
    /// domain. An `IMPLEMENTS`-family relation (see [`super::relation::SPECIALIZES`]):
    /// like [`IMPLEMENTS`] it links a specification to a conforming party, but
    /// oriented spec → impl rather than impl → interface. Ambiguity-preserving:
    /// the linker adds it only when exactly one same-name implementation exists;
    /// multiple candidates leave the schema node flagged, never guessed.
    pub const IMPLEMENTED_BY: &str = "IMPLEMENTED_BY";
}

/// Abstract **super-relations**: a small lattice layered over the concrete
/// [`edge`] kinds so downstream queries can reason at a coarser grain — "does A
/// depend on B?", "what does this scope contain?" — without enumerating every
/// concrete edge.
///
/// These are a *read-side taxonomy only*: they are **never emitted on the wire**.
/// The graph always carries the precise [`edge`] label; [`parent_relation`] maps
/// a concrete kind up to the super-relation that subsumes it. Keeping the
/// emitted labels untouched means the lattice can grow without ever perturbing
/// golden output.
pub mod relation {
    /// Any outbound dependency. Subsumes [`super::edge::CALLS`],
    /// [`super::edge::USES_TYPE`], [`super::edge::IMPORTS`],
    /// [`super::edge::DEPENDS_ON`].
    pub const DEPENDS: &str = "DEPENDS";
    /// Any structural nesting. Subsumes [`super::edge::CONTAINS`],
    /// [`super::edge::DECLARES`], [`super::edge::HAS_METHOD`].
    pub const CONTAINMENT: &str = "CONTAINMENT";
    /// Any subtype / realization relationship. Subsumes [`super::edge::IMPLEMENTS`],
    /// the reserved [`super::edge::EXTENDS`], and the cross-language
    /// [`super::edge::IMPLEMENTED_BY`].
    pub const SPECIALIZES: &str = "SPECIALIZES";
}

/// The super-relation that subsumes a concrete [`edge`] kind, or `None` when the
/// edge stands on its own. The mapping is total over the [`edge`] constants
/// (including the reserved [`edge::EXTENDS`]); it never fabricates a parent for
/// an unknown label, so a future edge kind is `None` until it is deliberately
/// placed in the lattice here.
pub fn parent_relation(edge_kind: &str) -> Option<&'static str> {
    match edge_kind {
        edge::CALLS
        | edge::READS
        | edge::USES_TYPE
        | edge::IMPORTS
        | edge::DEPENDS_ON
        | edge::FLOWS_TO
        | edge::DATA_DEP => Some(relation::DEPENDS),
        edge::CONTAINS | edge::DECLARES | edge::HAS_METHOD => Some(relation::CONTAINMENT),
        edge::IMPLEMENTS | edge::EXTENDS | edge::IMPLEMENTED_BY => Some(relation::SPECIALIZES),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn depends_subsumes_dependency_edges() {
        for e in [
            edge::CALLS,
            edge::USES_TYPE,
            edge::IMPORTS,
            edge::DEPENDS_ON,
            edge::FLOWS_TO,
            edge::DATA_DEP,
            edge::READS,
        ] {
            assert_eq!(parent_relation(e), Some(relation::DEPENDS), "edge {e}");
        }
    }

    #[test]
    fn containment_subsumes_structural_edges() {
        for e in [edge::CONTAINS, edge::DECLARES, edge::HAS_METHOD] {
            assert_eq!(parent_relation(e), Some(relation::CONTAINMENT), "edge {e}");
        }
    }

    #[test]
    fn specializes_subsumes_implements_and_reserved_extends() {
        assert_eq!(
            parent_relation(edge::IMPLEMENTS),
            Some(relation::SPECIALIZES)
        );
        assert_eq!(parent_relation(edge::EXTENDS), Some(relation::SPECIALIZES));
        assert_eq!(
            parent_relation(edge::IMPLEMENTED_BY),
            Some(relation::SPECIALIZES)
        );
    }

    #[test]
    fn unknown_edges_have_no_parent() {
        assert_eq!(parent_relation("NOT_A_REAL_EDGE"), None);
        assert_eq!(parent_relation(""), None);
    }
}
