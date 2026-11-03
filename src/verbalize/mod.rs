//! Deterministic verbalization of the recovered graph (epic E-V).
//!
//! The verbalizer renders graph facts as retrieval-safe sentences — the
//! proven vocabulary-templates-with-variable-slots pattern, no model
//! anywhere. Module map:
//!
//! - [`grammar`] (V4): the ADR-0008 contract and its conformance checker —
//!   the quality bar every emitted sentence must pass.
//! - [`templates`] (V1): the versioned template registry, one function per
//!   fact family.
//! - [`facts`] (V1): read-only projection of the existing passes (domains,
//!   layers, archetypes, violations, blast radius) into typed facts.
//! - [`glossary`] (V1): value-ranked, dense handle assignment (R3/R5).
//! - [`render`] (V1): the document assembler behind `trailtracker
//!   verbalize` — views, ordering, dedup, budget honesty. Library entry
//!   point: [`render::verbalize`].

pub mod facts;
pub mod glossary;
pub mod grammar;
pub mod render;
pub mod templates;

pub use render::{verbalize, verbalize_target, Document, Options, View};
