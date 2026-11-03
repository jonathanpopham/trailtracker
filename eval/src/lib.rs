//! TrailTracker verification harness — development/CI tooling, never shipped.
//!
//! Provides the layers of the eval pipeline: a hermetic property/fuzz harness
//! ([`property`]), self-analysis regression ([`regression`]), a deterministic
//! hash-attestable report ([`report`] + [`sha256`]), and bounded formal proofs
//! ([`kani_proofs`], compiled only under `cargo kani`).

// The harness matches the runtime crate's memory-safety guarantee; `unsafe` is
// a compile error (also enforced for all targets via `[lints.rust]`).
#![forbid(unsafe_code)]

pub mod atlas;
pub mod fuzz_extractors;
pub mod golden;
pub mod metamorphic;
pub mod property;
pub mod regression;
pub mod report;
pub mod sha256;

#[cfg(kani)]
pub mod kani_proofs;
