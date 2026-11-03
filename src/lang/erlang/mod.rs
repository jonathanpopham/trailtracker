//! Erlang front end: lossless lexer + CST parser + lowering, wired to the shared
//! IR through the [`LanguageFrontEnd`] seam.
//!
//! Erlang is a flat, module-per-file language: the module identity comes from the
//! `-module(M)` attribute (not the file path), so there is no directory/file scope
//! convention and [`LanguageFrontEnd::module_path`] keeps its empty default — the
//! lowering derives the module name from `-module` (falling back to the file stem).
//!
//! The surface is dot-terminated forms: attributes (`-module`, `-export`,
//! `-import`, `-include`, `-record`, `-define`, `-type`, …) and function
//! definitions (clauses `name(Args) -> Body` separated by `;`). The lexer flags
//! the clause-terminating `.` distinctly from record-access `.`; the parser groups
//! a function's clauses into one node and tracks `case`/`if`/`receive`/`try`/
//! `begin`/`fun … end` block depth so an inner `;` is never mistaken for a clause
//! separator. The lowering maps `name/arity` → `Function`, `-module` → `Module`,
//! `-record`/`-type`/`-opaque` → `Type`, `-define` → `Constant`,
//! `-import`/`-include`/`-behaviour` → `IMPORTS`, and uses a name/arity scope
//! ladder for `CALLS`. See `lower.rs` for the honest-mapping notes.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Erlang language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct ErlangFrontEnd;

impl LanguageFrontEnd for ErlangFrontEnd {
    fn name(&self) -> &'static str {
        "erlang"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["erl", "hrl"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once for the resolution ladder); merge it into the shared
        // graph the pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn front_end_identity() {
        let fe = ErlangFrontEnd;
        assert_eq!(fe.name(), "erlang");
        assert_eq!(fe.extensions(), &["erl", "hrl"]);
        // Flat language: no path-derived module scope.
        assert!(fe.module_path("src/foo.erl").is_empty());
    }

    /// Required lossless round-trip: parsing then reconstructing yields the source
    /// byte-for-byte, including comments, whitespace, and unusual constructs.
    #[test]
    fn lossless_round_trip() {
        let sources = [
            "\
%%% A representative module exercising the whole surface.
-module(geo).
-behaviour(gen_server).
-export([norm/1, scale/2, run/0]).
-import(math, [sqrt/1]).
-include_lib(\"kernel/include/file.hrl\").
-record(point, {x = 0 :: number(), y = 0 :: number()}).
-define(PI, 3.14159).
-type vector() :: {number(), number()}.

-spec norm(#point{}) -> number().
norm(#point{x = X, y = Y}) ->
    sqrt(X * X + Y * Y).

scale(P = #point{x = X, y = Y}, K) when K > 0 ->
    case K of
        1 -> P;
        _ -> #point{x = X * K, y = Y * K}
    end;
scale(P, _) ->
    P.

run() ->
    Doubler = fun(N) -> N * 2 end,
    Ref = fun lists:map/2,
    Bin = <<1, 2, 3>>,
    Ch = $a,
    Hex = 16#FF,
    _ = Ref(Doubler, [1, 2, 3]),
    {ok, Bin, Ch, Hex}.
",
            // Edge cases: empty, comment-only, unterminated, unicode, stray bytes.
            "",
            "%% just a comment, no newline at EOF",
            "f() -> \"unterminated string\n",
            "λ() -> '☃ €'.  %% unicode atoms and strings\n",
            "broken @ & ^ tokens.\nf() -> ok.\n",
            "-endif.\n-else.\n-ifdef(DEBUG).\n",
        ];
        for src in sources {
            let tree = parser::parse("rt.erl", src);
            let mut rebuilt = String::with_capacity(src.len());
            tree.root.reconstruct(&tree.source, &mut rebuilt);
            assert_eq!(rebuilt, *src, "not lossless for: {src:?}");
            assert!(tree.is_lossless(), "is_lossless() false for: {src:?}");
        }
    }
}
