//! A tiny calculator crate used as a fixed regression corpus for TrailTracker.
//! It deliberately exercises every rung of the call-resolution ladder.

pub mod ops;
pub mod parser;

use crate::ops::Engine;
use crate::parser::parse;

/// Top-level entry: import-resolved call to `parse`, then a receiver call.
pub fn evaluate(input: &str) -> i64 {
    let program = parse(input);
    let mut engine = Engine::new();
    engine.run(&program)
}

/// A name that also exists in `ops` — exercises ambiguity at the global level.
pub fn reset() -> i64 {
    0
}
