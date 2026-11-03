//! Parser: turns a source string into a list of steps. Exercises imported-name
//! calls and a global call into another module.

use crate::ops::{OpKind, Step};

/// Parse a whitespace-separated program like "+ 2 * 3" into steps.
pub fn parse(input: &str) -> Vec<Step> {
    let mut steps = Vec::new();
    let mut tokens = input.split_whitespace();
    while let Some(sym) = tokens.next() {
        let op = symbol(sym);
        let value = tokens
            .next()
            .and_then(|v| v.parse::<i64>().ok())
            .unwrap_or(0);
        steps.push(Step { op, value });
    }
    steps
}

/// Local helper resolved within this module.
fn symbol(sym: &str) -> OpKind {
    match sym {
        "*" => OpKind::Mul,
        _ => OpKind::Add,
    }
}
