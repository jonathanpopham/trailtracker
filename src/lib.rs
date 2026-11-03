//! TrailTracker: an airgap-safe, std-only code ontology and graph
//! extractor. It ingests inherited codebases and emits an ontology-backed graph
//! that supports reasoning and eventual isomorphic rebuilds.
//!
//! Layering (all language-neutral except `lang::*`):
//! - [`core`]: spans, the lossless untyped CST, deterministic JSON.
//! - [`lang`]: per-language front ends (lexer + parser → CST).
//! - [`ir`]: the lambda-rooted ontology every language lowers into.
//! - [`graph`]: the canonical graph (nodes + relationships) and JSONL output.
//! - [`pipeline`]: discover → parse → lower → graph → linearize.
//! - [`extract`]: deterministic passes projecting derived views (e.g. the
//!   data-ontology entity/relationship model) out of the base graph.
//! - [`enrich`]: the optional LLM naming pass over the deterministic domain
//!   clusters (deterministic membership + attested semantics). COMPILED OUT
//!   by default: it exists only behind the `enrich` cargo feature (internal
//!   tooling builds), so the shipped/airgap binary contains no code that
//!   invokes a model or reaches outside the airgap.
//! - [`export`]: serializers for external tools (Ontoloom wire JSON).
//! - [`dossier`]: the client-ready deliverable — one self-contained,
//!   airgap-grade HTML report composing the brief, the interactive code map,
//!   optional enriched domains, and layer violations.
//! - [`doctor`]: self-diagnosis (`trailtracker doctor`) — read-only health
//!   checks of the tool + environment with agent-ergonomic reporting.
//! - [`arch`]: continuous architecture verification (ADR-0005) — a
//!   human-authored `.trailtracker-arch.json` spec of INTENDED architecture,
//!   verified against the ACTUAL recovered graph; drift gates CI.
//! - [`violations`]: the spec-free full layer-violations report — every
//!   direction-violating dependency or inheritance edge at unit grain with
//!   symbol-grain evidence, ranked worst-first (`trailtracker violations`).
//! - [`report_full`]: the full evidence report (`trailtracker report --full`)
//!   — Markdown + self-contained HTML where every count expands to named
//!   evidence; the interactive map is demoted to a domains-only appendix.

// Crown-jewel guarantee for a defense-grade analysis tool: the entire runtime
// crate is memory-safe by construction. `unsafe` is a compile error here (and
// via `[lints.rust]` in Cargo.toml for every target, including tests/examples).
#![forbid(unsafe_code)]

pub mod arch;
pub mod brief;
pub mod brief_generated;
pub mod brief_projects;
pub mod core;
pub mod deadcode;
pub mod doctor;
pub mod dossier;
#[cfg(feature = "enrich")]
pub mod enrich;
pub mod explain;
pub mod export;
pub mod extract;
pub mod graph;
pub mod ir;
pub mod lang;
pub mod nav;
pub mod pipeline;
pub mod query;
pub mod report;
pub mod report_brief;
pub mod report_full; // R3: the full evidence report (`report --full`, MD + HTML)
pub mod rewrite;
pub mod search;
pub mod verbalize;
pub mod violations; // V4: ADR-0008 grammar contract + conformance checker (V1 grows the engine here)
