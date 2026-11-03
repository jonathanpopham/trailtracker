//! Prolog front end: lossless lexer + CST parser + lowering, wired to the shared
//! IR through the [`LanguageFrontEnd`] seam.
//!
//! Prolog is a flat, module-per-file language: the module identity comes from the
//! `:- module(M, Exports)` directive (not the file path), so there is no
//! directory/file scope convention and [`LanguageFrontEnd::module_path`] keeps its
//! empty default — the lowering derives the module name from `:- module(...)`
//! (falling back to the file stem).
//!
//! # Extensions and the `.pl` ambiguity (deliberate)
//!
//! This front end claims `["pro", "P", "prolog"]` and **does not** claim Prolog's
//! most common extension, `.pl`. `.pl` is irreducibly ambiguous: it is also the
//! canonical Perl extension, and the Perl front end ([`crate::lang::perl`]) already
//! claims `pl` (along with `pm`/`t`). The pipeline dispatches a file to the *first*
//! registered front end that claims its extension, so claiming `pl` here would
//! either silently steal Perl files or be silently shadowed by Perl, depending on
//! registry order — both dishonest. The disjoint-extensions invariant
//! (`registry_has_unique_names_and_extensions`) forbids the collision outright.
//! `.P` (XSB Prolog) and `.pro` (Visual Prolog / generic Prolog) are unambiguous
//! Prolog extensions; `.prolog` is an explicit long form. Projects that use `.pl`
//! for Prolog can be disambiguated by a future content sniffer or a per-project
//! override — not by a hard-coded extension grab. The `.pl` ambiguity is therefore
//! recorded here as a known coverage gap rather than papered over.
//!
//! The surface is `.`-terminated forms (the lexer flags the clause-terminating
//! lone `.` distinctly from the float/list/dict `.`): **directives** (`:- Goal.` /
//! `?- Goal.`) and **clauses** — facts (`head.`) and rules (`head :- body.` /
//! DCG rules `head --> body.`). The parser parses each clause head precisely and
//! captures bodies as balanced groups; the lowering groups clauses sharing a
//! predicate name/arity into one `Function` (like Erlang), maps `:- module(...)`
//! → `Module`, `:- use_module`/`:- ensure_loaded`/… → `IMPORTS`, and uses a
//! name/arity scope ladder for `CALLS`. See `lower.rs` for the honest-mapping
//! notes and punts.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Prolog language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct PrologFrontEnd;

impl LanguageFrontEnd for PrologFrontEnd {
    fn name(&self) -> &'static str {
        "prolog"
    }

    fn extensions(&self) -> &'static [&'static str] {
        // NOTE: `.pl` is intentionally NOT claimed — it collides with Perl. See the
        // module-level docs.
        &["pro", "P", "prolog"]
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
        let fe = PrologFrontEnd;
        assert_eq!(fe.name(), "prolog");
        assert_eq!(fe.extensions(), &["pro", "P", "prolog"]);
        // The `.pl` ambiguity: Prolog's usual extension is deliberately unclaimed.
        assert!(!fe.extensions().contains(&"pl"));
        // Flat language: no path-derived module scope.
        assert!(fe.module_path("src/foo.pro").is_empty());
    }

    /// Required lossless round-trip: parsing then reconstructing yields the source
    /// byte-for-byte, including comments, whitespace, and unusual constructs.
    #[test]
    fn lossless_round_trip() {
        let sources = [
            "\
%%% A representative module exercising the whole surface.
:- module(geo, [norm/2, scale/3, run/1]).
:- use_module(library(lists)).
:- use_module(library(apply), [maplist/3]).
:- dynamic cached/2.

%! norm(+Point, -Norm) is det.
norm(point(X, Y), N) :-
    N is sqrt(X * X + Y * Y).

scale(point(X, Y), K, point(X2, Y2)) :-
    K > 0,
    X2 is X * K,
    Y2 is Y * K.

run(Result) :-
    Doubler = [X, Y]>>(Y is X * 2),
    maplist(Doubler, [1, 2, 3], Result),
    Code = 0'a,
    Hex = 0x1F,
    T =.. [point, 1, 2],
    ( Code > 0 -> true ; throw(bad_code) ),
    format(\"~w ~w ~w~n\", [Hex, T, Result]).

digits([]) --> [].
digits([D|T]) --> [D], { code_type(D, digit) }, digits(T).

?- run(_).
",
            // Edge cases: empty, comment-only, unterminated, unicode, stray bytes.
            "",
            "% just a comment, no newline at EOF",
            "f(X) :- \"unterminated string\n",
            "λ('☃ €').  % unicode atoms and strings\n",
            "broken @ unknown € tokens.\nf(ok).\n",
            ":- set_prolog_flag(double_quotes, chars).\n",
            "/* block */ foo. /* trailing */\n",
        ];
        for src in sources {
            let tree = parser::parse("rt.pro", src);
            let mut rebuilt = String::with_capacity(src.len());
            tree.root.reconstruct(&tree.source, &mut rebuilt);
            assert_eq!(rebuilt, *src, "not lossless for: {src:?}");
            assert!(tree.is_lossless(), "is_lossless() false for: {src:?}");
        }
    }
}
