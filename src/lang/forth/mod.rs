//! Forth front end: lossless lexer + CST parser + lowering, wired to the shared
//! IR through the [`LanguageFrontEnd`] seam.
//!
//! Forth is a whitespace-delimited stack language with almost no syntax: a file
//! is a stream of space-separated words. The lexer stays purely lossless — every
//! byte is covered, whitespace and both comment forms (`\ …`, `( … )`) are trivia
//! tokens, `." …"` / `s" …"` strings and numeric words are single tokens, and
//! anything unclassifiable (e.g. an unterminated string) becomes an `error`
//! token. The parser lifts the one structural shape that matters — the colon
//! definition `: name … ;` — plus nested control-flow groups (so there is a real
//! recursion to depth-guard). The lowering maps definitions → `Function`,
//! `CONSTANT`/`VARIABLE`/`VALUE` → `Constant`, `INCLUDE`/`REQUIRE` → `IMPORTS`,
//! and in-body word references → `CALLS` resolved (case-insensitively) against
//! the project's word table. Forth has no class-like constructs, so no
//! `Type`/`HAS_METHOD`/`EXTENDS` are emitted.
//!
//! Extensions claimed: `fth`, `4th`, `frt`. Deliberately **not** `f` (Fortran)
//! or `fs` (F#), which other front ends own.
//!
//! NOTE: activating this front end requires two one-line registrations in shared
//! files (out of scope for this module): `pub mod forth;` in `src/lang/mod.rs`
//! and `Box::new(crate::lang::forth::ForthFrontEnd)` in
//! `src/lang/frontend.rs::front_ends`. See `docs/vir.md` §4.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Forth language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct ForthFrontEnd;

impl LanguageFrontEnd for ForthFrontEnd {
    fn name(&self) -> &'static str {
        "forth"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["fth", "4th", "frt"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once to resolve word references across files); merge it
        // into the shared graph the pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn front_end_identity() {
        let fe = ForthFrontEnd;
        assert_eq!(fe.name(), "forth");
        assert_eq!(fe.extensions(), &["fth", "4th", "frt"]);
    }

    #[test]
    fn round_trips_a_representative_program() {
        // Both comment forms, both string forms, numeric literals with base
        // prefixes, a constant, a variable, two definitions with nested control
        // flow, a stack-effect comment, and an include.
        let src = "\
\\ ring buffer demo
( base prefixes ) $FF #100 %1010 -3 constant unused

42 constant answer
variable counter

: square ( n -- n^2 ) dup * ;

: classify ( n -- )
    dup 0 < if
        .\" negative\" cr
    else
        .\" non-negative\" cr
    then
    drop ;

: countdown ( n -- )
    begin
        dup . square drop
        1 - dup 0 =
    until
    drop ;

s\" extra.fth\" required
include helpers.frt
answer countdown
";
        let fe = ForthFrontEnd;
        let tree = fe.parse("demo.fth", src);
        assert!(
            tree.is_lossless(),
            "the parsed CST must reconstruct the source byte-for-byte"
        );
        // Lexing classified everything: no bytes fell into `error` tokens.
        assert_eq!(
            tree.root.error_token_count(),
            0,
            "representative program should lex cleanly with zero error tokens"
        );
    }

    #[test]
    fn lossless_on_edge_inputs() {
        // Empty file, lone markers, unterminated forms, non-ASCII — all must
        // round-trip byte-for-byte even when classified as errors.
        for src in [
            "",
            "   \n\t  ",
            "\\",
            "(",
            ".\" unterminated string",
            "( unterminated paren",
            ": noend dup *",
            "λ ☃ € \\ unicode\n",
            ": x if if if then then then ;",
        ] {
            let fe = ForthFrontEnd;
            let tree = fe.parse("edge.fth", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
