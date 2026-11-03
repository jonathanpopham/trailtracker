//! Visual Basic .NET front end: lossless lexer + CST parser + lowering, wired to
//! the shared IR through the [`LanguageFrontEnd`] seam.
//!
//! VB.NET is a case-insensitive, keyword-delimited .NET language: blocks are
//! `Keyword … End Keyword` (e.g. `Sub … End Sub`, `Class … End Class`) rather than
//! brace-delimited, and physical newlines terminate statements. The lexer stays
//! purely lossless — every byte is covered, with trivia (whitespace, `'` and `REM`
//! comments, `#` preprocessor directives, and `_` line-continuations) retained and
//! unclassifiable bytes preserved as `error` tokens. The lowering maps
//! `Namespace`/`Module` → `Module`, `Class`/`Structure`/`Interface`/`Enum`/
//! `Delegate` → `Type` (with an apt `type_kind`), `Sub`/`Function`/`Operator` →
//! `Function`, fields/properties/events → `Constant`, `Inherits`/`Implements` →
//! `EXTENDS`/`IMPLEMENTS`, and `Imports` → `IMPORTS`, reusing a deterministic
//! scope-resolution ladder for `CALLS`.
//!
//! Closest analogue is the C# front end ([`crate::lang::csharp`]); this module
//! follows the same parse/lower contract, adapted to VB's surface syntax.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The VB.NET language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct VisualBasicFrontEnd;

impl LanguageFrontEnd for VisualBasicFrontEnd {
    fn name(&self) -> &'static str {
        "vbnet"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["vb"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    // `module_path` uses the default (flat) implementation: VB scope comes from
    // explicit `Namespace`/`Module` declarations in the source, not the file path,
    // so the module hierarchy is built during lowering from the CST.

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
        let fe = VisualBasicFrontEnd;
        assert_eq!(fe.name(), "vbnet");
        assert_eq!(fe.extensions(), &["vb"]);
    }

    #[test]
    fn parse_round_trips_through_the_seam() {
        let fe = VisualBasicFrontEnd;
        let src = "Namespace N\n Public Class C\n  Public Function M(x As Integer) As Integer\n   Return x + 1\n  End Function\n End Class\nEnd Namespace\n";
        let tree = fe.parse("N.vb", src);
        assert!(tree.is_lossless(), "front-end parse must be lossless");
    }

    /// Byte-for-byte lossless round-trip over a spread of VB.NET surface syntax —
    /// the core guarantee every front end must honor (see `docs/vir.md` §2).
    #[test]
    fn lossless_round_trip_corpus() {
        let corpus = [
            "",
            "' lone comment with no newline",
            "REM old-style remark\n",
            "Option Strict On\nOption Explicit On\n",
            "Imports System\nImports System.Collections.Generic\n",
            "Dim total = 1 + _\n      2 + _\n      3\n",
            "Public Const PI As Double = 3.14159\nDim hex = &HFF_u\nDim dt = #2020-01-01#\n",
            "Module Util\n  Public Function Twice(n As Integer) As Integer\n    Return n * 2\n  End Function\nEnd Module\n",
            "Namespace App\n  <Serializable>\n  Public Class Widget\n    Inherits Base\n    Implements IDisposable, IComparable\n\n    Private _name As String = \"w\"\n    Public Property Size As Integer\n\n    Public Sub New(name As String)\n      _name = name\n    End Sub\n\n    Public Sub Dispose() Implements IDisposable.Dispose\n      Console.WriteLine($\"disposing {_name}\")\n    End Sub\n  End Class\n\n  Public Interface IShape\n    Function Area() As Double\n    ReadOnly Property Name As String\n  End Interface\n\n  Public Enum Color\n    Red\n    Green = 2\n    Blue\n  End Enum\nEnd Namespace\n",
            "Class C\n  Sub Broken(\n",                 // unterminated paren + block
            "Class C : Dim s = \"a\"\"b\"\"c\" : End Class\n", // doubled quotes + colon separators
            "λ ☃ €\n",                                  // non-ascii → error tokens
        ];
        for src in corpus {
            let tree = parser::parse("corpus.vb", src);
            let mut rebuilt = String::new();
            tree.root.reconstruct(src, &mut rebuilt);
            assert_eq!(
                rebuilt, src,
                "round-trip must be byte-identical for {src:?}"
            );
            assert!(tree.is_lossless(), "is_lossless must hold for {src:?}");
        }
    }
}
