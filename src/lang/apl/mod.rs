//! APL front end: lossless lexer + CST parser + lowering, wired to the shared IR
//! through the [`LanguageFrontEnd`] seam.
//!
//! APL is a terse, glyph-dense, largely *anonymous* array language: a program is
//! mostly expressions, and named definitions are the exception, not the rule.
//! The front end is built around that reality and around APL's defining technical
//! hazard — the source is full of multi-byte Unicode glyphs (`⍴ ⌽ ⍳ ∇ ⍝ ← ¯ ⍵ ⍺`
//! …), so the [`lexer`] iterates strictly by `char` and never slices a string at a
//! non-`char` boundary.
//!
//! Honest coverage, mapped sparingly (see [`lower`] for the full rationale):
//!   - `∇ … ∇` tradfns and `name←{…}` dfns → [`Function`](crate::ir::ontology::node::FUNCTION).
//!   - top-level `name←value` (non-dfn RHS) → [`Constant`](crate::ir::ontology::node::CONSTANT).
//!   - `:Namespace Name` → [`Module`](crate::ir::ontology::node::MODULE) (noted).
//!   - references to a defined function inside a body → [`CALLS`](crate::ir::ontology::edge::CALLS),
//!     resolved against the project function table; ambiguity is preserved, never
//!     guessed.
//!
//! Heavy, deliberate punts (APL gives a single script no honest token-level
//! signal for these): argument/return types, inheritance, and dependency imports.
//! `)COPY` / `⎕CY` workspace pulls are recognized as a punt and *not* modelled as
//! `IMPORTS`. Top-level (non-function) call sites are not attributed. A script
//! that defines little will correctly produce just a `File` and a few nodes — the
//! honest result.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The APL language front end. Zero-sized: all state lives in the parse trees and
/// the lowering pass.
pub struct AplFrontEnd;

impl LanguageFrontEnd for AplFrontEnd {
    fn name(&self) -> &'static str {
        "apl"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["apl", "aplf", "apln", "dyalog"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once to resolve cross-file calls); merge it into the
        // shared graph the pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn front_end_identity() {
        let fe = AplFrontEnd;
        assert_eq!(fe.name(), "apl");
        assert_eq!(fe.extensions(), &["apl", "aplf", "apln", "dyalog"]);
    }

    #[test]
    fn lossless_round_trip_on_representative_snippet() {
        // A representative slice of real APL: a comment, system-var assignment, a
        // dfn bound to a name, a `⋄`-joined line, a tradfn with a dyadic header
        // and a localization list, a char vector with a doubled quote, high-minus
        // and complex numerals, a namespace, and a control structure.
        let src = "\
⍝ inventory utilities
⎕IO←0 ⋄ ⎕ML←1

avg←{(+/⍵)÷≢⍵}
scale←{⍺×⍵}

∇ R←items total;subtotal
 subtotal←+/items
 R←subtotal
∇

:Namespace Stats
  mean←{avg ⍵}
:EndNamespace

note←'it''s ¯3.5 and 2J3'
prices←10 20 ¯5 1E3
report←avg prices
";
        let fe = AplFrontEnd;
        let tree = fe.parse("inventory.apl", src);
        assert!(
            tree.is_lossless(),
            "the APL front end must reconstruct source byte-for-byte"
        );
        assert_eq!(tree.error_byte_ratio(), 0.0, "no bytes should be errors");

        // And the lowering produces a non-trivial, deterministic graph.
        let file = crate::lang::frontend::SourceFile {
            rel_path: "inventory.apl".to_string(),
            module_path: vec![],
            source: &tree.source,
            root: &tree.root,
        };
        let input = LoweredInput {
            package: "demo",
            manifest_deps: &[],
            files: vec![file],
        };
        let mut g = Graph::new();
        fe.lower(&input, &mut g);
        assert!(g.node_count() > 0);

        // Determinism: lowering the same input twice is byte-identical.
        let mut g2 = Graph::new();
        let file2 = crate::lang::frontend::SourceFile {
            rel_path: "inventory.apl".to_string(),
            module_path: vec![],
            source: &tree.source,
            root: &tree.root,
        };
        let input2 = LoweredInput {
            package: "demo",
            manifest_deps: &[],
            files: vec![file2],
        };
        fe.lower(&input2, &mut g2);
        assert_eq!(
            g.to_jsonl(),
            g2.to_jsonl(),
            "lowering must be deterministic"
        );
    }
}
