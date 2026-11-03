//! C# front end: lossless lexer + CST parser + lowering, wired to the shared IR
//! through the [`LanguageFrontEnd`] seam.
//!
//! C# is brace-delimited (like Rust) but its *members* (methods, fields,
//! properties) carry no leading keyword, so the parser classifies them by header
//! shape. The lexer stays purely lossless — every byte is covered, with trivia
//! (whitespace, comments, doc comments, preprocessor directives) retained and
//! unclassifiable bytes preserved as `error` tokens. The lowering maps
//! `class`/`struct`/`interface`/`enum`/`record`/`delegate` → `Type` (with an apt
//! `type_kind`), method → `Function`, `namespace` → `Module`, field/property →
//! `Constant`, base lists → `EXTENDS`/`IMPLEMENTS`, and `using` → `IMPORTS`,
//! reusing a deterministic scope-resolution ladder for `CALLS`.

pub mod cpg;
pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The C# language front end. Zero-sized: all state lives in the parse trees and
/// the lowering pass.
pub struct CSharpFrontEnd;

impl LanguageFrontEnd for CSharpFrontEnd {
    fn name(&self) -> &'static str {
        "csharp"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["cs"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    // `module_path` uses the default (flat) implementation: C# scope comes from
    // explicit `namespace` declarations in the source, not the file path, so the
    // module hierarchy is built during lowering from the CST.

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once for the resolution ladder); merge it into the shared
        // graph the pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }

    fn lower_cpg(&self, input: &LoweredInput, graph: &mut Graph) {
        // Base lowering plus the deterministic CPG overlay (ADR-0003): the base
        // sub-graph is byte-identical to `lower`'s; Statement nodes and
        // FLOWS_TO/DATA_DEP edges are strictly additive.
        let sub = lower::lower_with_cpg(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn front_end_identity() {
        let fe = CSharpFrontEnd;
        assert_eq!(fe.name(), "csharp");
        assert_eq!(fe.extensions(), &["cs"]);
    }

    #[test]
    fn parse_round_trips_through_the_seam() {
        let fe = CSharpFrontEnd;
        let src = "namespace N { public class C { public int M(int x) => x + 1; } }";
        let tree = fe.parse("N.cs", src);
        assert!(tree.is_lossless(), "front-end parse must be lossless");
    }
}
