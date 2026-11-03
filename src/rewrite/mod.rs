//! The rewrite engine (ADR-0006): TrailTracker's first code-MODIFYING
//! capability, governed by the propose-then-approve contract.
//!
//! Design law (Jonathan, 2026-07-07): rewrites need approval just like agents
//! do. `propose` analyzes and emits a reviewable, hash-bound
//! `trailtracker.rewrite-proposal/v1` document plus a unified diff — it never
//! writes source. `apply` is the only writing path and refuses unless the
//! proposal verifies (hash) and the target file is byte-identical to the file
//! the proposal was made from (fingerprint). No flag skips the two-step.
//!
//! Layering:
//! - [`edit`]: the span-edit primitive over the lossless CST — replace byte
//!   ranges, prove every byte outside them untouched.
//! - [`proposal`]: the proposal document — fingerprints, canonical hash,
//!   parse/serialize, and the unified diff renderer.
//! - [`rules`]: the rule registry — conservative recognizers over the same
//!   statement segmentation the CPG uses, emitting edits with why-safe
//!   arguments grounded in real CPG facts.

pub mod cert;
pub mod edit;
pub mod proposal;
pub mod rules;
