//! A hermetic, std-only property/fuzz harness.
//!
//! No external fuzzing crate: a deterministic xorshift PRNG drives a set of
//! input generators, and every generated input is checked against the
//! invariants that must hold for *all* inputs:
//!
//! - **No panic.** Parsing is isolated with `catch_unwind`; a panic is a failure,
//!   not a crash.
//! - **Lossless.** The CST reconstructs the source byte-for-byte.
//! - **Deterministic.** Parsing the same input twice yields identical output.
//!
//! Failures carry the seed + sample so they reproduce exactly — important for a
//! tool where correctness is safety-critical.

use std::panic::{catch_unwind, AssertUnwindSafe};

use trailtracker::lang::rust::parser::parse;

/// Deterministic 64-bit xorshift PRNG. Reproducible across machines.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Rng {
        Rng(seed | 1)
    }
    pub fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            0
        } else {
            (self.next_u64() % n as u64) as usize
        }
    }
}

#[derive(Debug)]
pub struct Failure {
    pub seed: u64,
    pub kind: &'static str,
    pub sample: String,
}

#[derive(Default)]
pub struct PropertyOutcome {
    pub cases: usize,
    pub failures: Vec<Failure>,
}

impl PropertyOutcome {
    pub fn passed(&self) -> bool {
        self.failures.is_empty()
    }
}

/// Run `cases` generated inputs derived from `seed`, mutating samples drawn from
/// `corpus` (real source strings). Stops collecting after a cap of failures to
/// keep reports bounded.
pub fn run(seed: u64, cases: usize, corpus: &[String]) -> PropertyOutcome {
    let mut outcome = PropertyOutcome::default();
    const FAILURE_CAP: usize = 25;
    for i in 0..cases {
        let case_seed = seed ^ (i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15);
        let mut rng = Rng::new(case_seed);
        let input = match i % 3 {
            0 => gen_random_chars(&mut rng),
            1 => gen_token_soup(&mut rng),
            _ => gen_mutation(&mut rng, corpus),
        };
        outcome.cases += 1;
        if let Some(kind) = check_invariants(&input) {
            if outcome.failures.len() < FAILURE_CAP {
                outcome.failures.push(Failure {
                    seed: case_seed,
                    kind,
                    sample: truncate(&input, 200),
                });
            }
        }
    }
    outcome
}

/// Returns `Some(kind)` on the first violated invariant, else `None`.
pub fn check_invariants(input: &str) -> Option<&'static str> {
    let owned = input.to_string();
    let first = catch_unwind(AssertUnwindSafe(|| {
        let tree = parse("fuzz.rs", &owned);
        (tree.is_lossless(), tree.to_json().to_line())
    }));
    let (lossless, json1) = match first {
        Ok(v) => v,
        Err(_) => return Some("panic"),
    };
    if !lossless {
        return Some("not_lossless");
    }
    // Determinism: a second parse must produce identical output.
    let owned2 = input.to_string();
    let json2 = match catch_unwind(AssertUnwindSafe(|| {
        parse("fuzz.rs", &owned2).to_json().to_line()
    })) {
        Ok(v) => v,
        Err(_) => return Some("panic"),
    };
    if json1 != json2 {
        return Some("nondeterministic");
    }
    None
}

/// Diverse characters including multi-byte UTF-8 and structural punctuation.
fn gen_random_chars(rng: &mut Rng) -> String {
    const ALPHABET: &[char] = &[
        'a', 'b', 'Z', '_', '0', '9', ' ', '\n', '\t', '{', '}', '(', ')', '[', ']', '<', '>', ':',
        ';', ',', '.', '"', '\'', '/', '*', '#', '!', '&', '|', '=', '-', 'λ', '☃', '€', '🦀',
    ];
    let len = rng.below(80);
    let mut s = String::new();
    for _ in 0..len {
        s.push(ALPHABET[rng.below(ALPHABET.len())]);
    }
    s
}

/// Sequences drawn from a Rust-ish token alphabet — stresses the real grammar
/// paths (items, paths, calls, strings, comments, nesting).
fn gen_token_soup(rng: &mut Rng) -> String {
    const TOKENS: &[&str] = &[
        "fn ",
        "struct ",
        "enum ",
        "impl ",
        "trait ",
        "mod ",
        "use ",
        "pub ",
        "const ",
        "let ",
        "self",
        "Self",
        "::",
        "->",
        "=>",
        "foo",
        "Bar",
        "()",
        "{}",
        "[]",
        "<T>",
        "\"s\"",
        "'a",
        "// c\n",
        "/* b */",
        "r#\"x\"#",
        "1.5e3",
        "0xFF",
        ";",
        ",",
        ".",
        "match ",
        "where ",
        "&mut ",
        "macro_rules!",
        "#[derive(X)]",
        "(((",
        ")))",
    ];
    let len = rng.below(40);
    let mut s = String::new();
    for _ in 0..len {
        s.push_str(TOKENS[rng.below(TOKENS.len())]);
    }
    s
}

/// Byte-level mutations of real source: the highest-signal generator, since it
/// keeps inputs near-valid where bugs hide.
fn gen_mutation(rng: &mut Rng, corpus: &[String]) -> String {
    if corpus.is_empty() {
        return gen_token_soup(rng);
    }
    let base = &corpus[rng.below(corpus.len())];
    // Operate on a window to keep cases small and fast.
    let mut bytes: Vec<u8> = {
        let start = rng.below(base.len().max(1));
        let end = (start + 1 + rng.below(400)).min(base.len());
        base.as_bytes()[start..end.max(start)].to_vec()
    };
    let edits = 1 + rng.below(6);
    for _ in 0..edits {
        if bytes.is_empty() {
            break;
        }
        match rng.below(3) {
            0 => {
                let at = rng.below(bytes.len());
                bytes[at] = (rng.next_u64() & 0x7f) as u8; // ASCII flip
            }
            1 => {
                let punct = b"{}()[]<>;,\"'";
                let at = rng.below(bytes.len() + 1);
                bytes.insert(at.min(bytes.len()), punct[rng.below(punct.len())]);
            }
            _ => {
                let at = rng.below(bytes.len());
                bytes.remove(at);
            }
        }
    }
    String::from_utf8_lossy(&bytes).into_owned()
}

fn truncate(s: &str, max: usize) -> String {
    if s.len() <= max {
        return s.to_string();
    }
    let mut end = max;
    while !s.is_char_boundary(end) {
        end -= 1;
    }
    format!("{}…", &s[..end])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fuzz_holds_invariants() {
        // Deterministic seed; fixed case count for a fast, reproducible gate.
        let out = run(0xC0FFEE, 4000, &[]);
        assert!(out.passed(), "property failures: {:?}", out.failures);
        assert_eq!(out.cases, 4000);
    }
}
