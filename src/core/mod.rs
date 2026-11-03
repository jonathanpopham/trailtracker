//! Language-neutral foundations shared by every front end: spans, the lossless
//! CST, and deterministic JSON. Nothing here knows about Rust or C#.

pub mod cst;
pub mod json;
pub mod span;
