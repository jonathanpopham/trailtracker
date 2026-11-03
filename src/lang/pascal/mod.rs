//! Object Pascal / Delphi front end: lossless lexer + CST parser + lowering,
//! wired to the shared IR through the [`LanguageFrontEnd`] seam.
//!
//! Pascal is keyword-block delimited (not whitespace-significant) and
//! case-insensitive. A unit is `unit X; interface … implementation … end.`; a
//! program/library is `program X; … begin … end.`. Definitions are grouped in
//! `type` / `const` / `var` sections, routines are `procedure`/`function …`, and
//! blocks open with `begin`/`case`/`try`/`asm`/`record`/`class`/… and close with
//! `end`. The lexer stays purely lossless (`//`, `{ … }`, and `(* … *)` comments,
//! `'…'` strings with the doubled-quote escape, `#65`/`#$41` char codes, `$FF`
//! hex / `&`-octal / `%`-binary numerals) with a per-iteration progress guard.
//! The parser captures definition headers precisely while keeping bodies and
//! member regions as balanced token blocks, depth-guarded against hostile
//! nesting. The lowering maps `unit`/`program`/`library`→`Module`,
//! `class`/`record`/`object`/`interface`→`Type` (with a `type_kind` and an
//! ancestor→`EXTENDS`/`IMPLEMENTS`), routines→`Function` (with `HAS_METHOD` for
//! class methods and qualified `T.M` implementations), `const`→`Constant`,
//! `uses`→`IMPORTS` (+ `ExternalDependency`/`DEPENDS_ON`), type annotations→
//! `USES_TYPE`, and parenthesised call sites→`CALLS`, preserving overload
//! ambiguity rather than inventing a single target.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Object Pascal / Delphi language front end. Zero-sized: all state lives in
/// the parse trees and the lowering pass.
pub struct PascalFrontEnd;

impl LanguageFrontEnd for PascalFrontEnd {
    fn name(&self) -> &'static str {
        "pascal"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["pas", "pp", "dpr", "dpk", "lpr"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn module_path(&self, rel_path: &str) -> Vec<String> {
        module_path_for(rel_path)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once for call resolution); merge it into the shared graph
        // the pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

/// Map a repo-relative Pascal path to a best-effort scope hint: a leading `src/`
/// is stripped, directory segments are kept, and the file stem contributes a
/// segment. Pascal's real module identity comes from the `unit`/`program`
/// declaration in the file (which the lowering reads directly), so these segments
/// are only a fallback hint.
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = rel.strip_prefix("src/").unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = match file.rsplit_once('.') {
        Some((s, _)) => s,
        None => file,
    };
    let mut module: Vec<String> = parts.iter().map(|s| s.to_string()).collect();
    if !stem.is_empty() {
        module.push(stem.to_string());
    }
    module
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn front_end_identity() {
        let fe = PascalFrontEnd;
        assert_eq!(fe.name(), "pascal");
        assert_eq!(fe.extensions(), &["pas", "pp", "dpr", "dpk", "lpr"]);
    }

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("foo.pas"), vec!["foo"]);
        assert_eq!(module_path_for("a/b/c.dpr"), vec!["a", "b", "c"]);
        assert_eq!(module_path_for("src/units/util.pp"), vec!["units", "util"]);
    }

    #[test]
    fn lossless_round_trip_on_representative_snippet() {
        // A representative slice of real Pascal: line + brace + paren-star
        // comments, a unit with interface/implementation, a uses clause, an
        // abstract base class and a derived class with a constructor and an
        // overriding method, a const, a qualified method implementation with a
        // body, control flow, strings with the doubled-quote escape, char codes,
        // and hex/real numerals.
        let src = "\
// Geometry demo
unit Geometry;

interface

uses
  SysUtils, Math;

{ The shape hierarchy }
type
  TShape = class
  public
    function Area: Double; virtual; abstract;
  end;

  TCircle = class(TShape)
  private
    FRadius: Double;
  public
    constructor Create(ARadius: Double);
    function Area: Double; override;
    function Describe: string;
  end;

const
  TAU = 6.283185;
  MASK = $FF;

implementation

constructor TCircle.Create(ARadius: Double);
begin
  FRadius := ARadius;
end;

function TCircle.Area: Double;
begin
  Result := TAU * FRadius * FRadius / 2;
end;

(* Build a human-readable label *)
function TCircle.Describe: string;
var
  A: Double;
begin
  A := Area;
  if A > 10.0 then
    Result := 'big: ' + FloatToStr(A) + #13#10
  else
    Result := 'small';
end;

end.
";
        let fe = PascalFrontEnd;
        let tree = fe.parse("Geometry.pas", src);
        assert!(
            tree.is_lossless(),
            "the Pascal front end must reconstruct source byte-for-byte"
        );

        // And the lowering produces a non-trivial, deterministic graph.
        let file = crate::lang::frontend::SourceFile {
            rel_path: "Geometry.pas".to_string(),
            module_path: module_path_for("Geometry.pas"),
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

        let mut g2 = Graph::new();
        let tree2 = fe.parse("Geometry.pas", src);
        let file2 = crate::lang::frontend::SourceFile {
            rel_path: "Geometry.pas".to_string(),
            module_path: module_path_for("Geometry.pas"),
            source: &tree2.source,
            root: &tree2.root,
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
            "lowering must be deterministic across runs"
        );
    }
}
