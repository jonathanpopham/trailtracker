//! Hybrid code search over the canonical graph — std-only, clean-room.
//!
//! Per the 2026-07-06 decision in `docs/plan-remaining.md`, zero dependencies
//! is absolute: no frankensearch, no external ranker. Search is built from the
//! literature on top of the crate's own primitives. The tiers:
//!
//! - **G1a ([`bm25`]):** a lexical BM25 tier. One in-memory inverted index
//!   over the graph's searchable nodes, tokenized with the same
//!   [`crate::extract::lexicon::tokenize`] used for the Lexicon ontology, so
//!   queries and documents always agree on vocabulary.
//! - **G1b ([`embed`]):** deterministic hash embeddings — signed
//!   character-n-gram feature hashing into [`embed::DIM`] dimensions,
//!   bit-exact across runs and platforms. Catches typos and morphological
//!   near-misses that exact tokens cannot.
//! - **G1c ([`fuse`]):** reciprocal-rank fusion of the two tiers plus a
//!   graph-structural proximity signal (BFS over DEPENDS-family edges from
//!   the top lexical anchors). [`fuse::search`] is the public entry point;
//!   [`fuse::HybridIndex`] is the reusable prebuilt form.
//!
//! Everything here is a pure, deterministic function of the base graph:
//! construction walks the `BTreeMap`-ordered node iterator, ranking breaks
//! score ties by node id, and BFS walks sorted adjacency, so the same graph
//! and query always produce the same ranked list, byte for byte.

pub mod bm25;
pub mod embed;
pub mod fuse;

pub use bm25::{DocView, Posting, ScoredHit, SearchIndex};
pub use embed::{cosine, embed, embed_node, rank, DIM};
pub use fuse::{search, HybridIndex, SearchResult};
