//! Ada front end: lossless lexer + CST parser + lowering, wired to the shared
//! IR through the [`LanguageFrontEnd`] seam.
//!
//! Ada is keyword-block delimited (not whitespace-significant) and
//! case-insensitive: `package [body] X is … end X;`,
//! `procedure P (…) is … begin … end P;`,
//! `function F (…) return T is … begin … end F;`, `type X is …;`, and the
//! `task`/`protected`/`entry`/`generic` units all open with a keyword and close
//! with `end`; a newline is ordinary trivia. The lexer stays purely lossless
//! (`--` line comments, `"…"` strings with the doubled-quote escape, decimal and
//! based numerals `16#FF#`, the char-literal `'x'` vs attribute-tick `X'Range`
//! split) with a per-iteration progress guard. The parser captures declarations,
//! signatures and context clauses precisely while keeping executable regions as
//! balanced token blocks, depth-guarded against hostile nesting. The lowering
//! maps `package`→`Module`, `procedure`/`function`/`entry`→`Function`,
//! `type`/`subtype`→`Type`, `X : constant … := …`→`Constant`, `with`→`IMPORTS`
//! (+ `ExternalDependency`), and `: T` annotations→`USES_TYPE`, emitting `CALLS`
//! only for `name (…)` references that resolve to a known project subprogram
//! (the call-vs-array-index ambiguity is never guessed — the Fortran approach).

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Ada language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct AdaFrontEnd;

impl LanguageFrontEnd for AdaFrontEnd {
    fn name(&self) -> &'static str {
        "ada"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["adb", "ads", "ada"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once for the resolution ladder and the with-clause
        // internal/external decision); merge it into the shared graph.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn front_end_identity() {
        let fe = AdaFrontEnd;
        assert_eq!(fe.name(), "ada");
        assert_eq!(fe.extensions(), &["adb", "ads", "ada"]);
    }

    #[test]
    fn lossless_round_trip_and_deterministic_lowering() {
        // A representative slice of real Ada: a context clause, a package body
        // with a type, a constant, a function and a procedure, control flow, a
        // string with a doubled quote, a char literal, an attribute tick, and a
        // based literal.
        let src = "\
-- Geometry demo
with Ada.Text_IO;
use Ada.Text_IO;

package body Geometry is

   type Shape is (Circle, Square);

   Tau  : constant Float   := 6.283185;
   Mask : constant Integer := 16#FF#;

   function Area (R : Float) return Float is
   begin
      return Tau * R * R / 2.0;
   end Area;

   procedure Describe (R : Float) is
      A     : Float     := Area (R);
      Label : Character := 'b';
      N     : Integer   := Shape'Pos (Circle);
   begin
      if A > 10.0 then
         Put_Line (\"big \"\"shape\"\"\");
      else
         Put_Line (\"small\");
      end if;
   end Describe;

end Geometry;
";
        let fe = AdaFrontEnd;
        let tree = fe.parse("geometry.adb", src);
        assert!(
            tree.is_lossless(),
            "the Ada front end must reconstruct source byte-for-byte"
        );

        let build = || {
            let tree = fe.parse("geometry.adb", src);
            let file = crate::lang::frontend::SourceFile {
                rel_path: "geometry.adb".to_string(),
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
            // The borrow of `tree` must outlive `input`; keep it alive here.
            fe.lower(&input, &mut g);
            g.to_jsonl()
        };

        let first = build();
        let second = build();
        assert_eq!(first, second, "lowering must be deterministic across runs");
        assert!(!first.is_empty(), "lowering must produce a non-empty graph");
    }
}
