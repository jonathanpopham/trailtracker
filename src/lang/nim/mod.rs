//! Nim front end: lossless lexer + CST parser + lowering, wired to the shared IR
//! through the [`LanguageFrontEnd`] seam.
//!
//! Nim is indentation-significant, like Python. The lexer stays purely lossless —
//! every byte is covered, newlines are emitted as structural `newline` tokens and
//! leading indentation as `whitespace` trivia (plus `#` line and nestable
//! `#[ ]#` block comments) — and the parser derives block structure from those.
//! Declaration *headers* (`proc`/`func`/…/`type`/`const`/`let`/`var`/`import`)
//! are parsed precisely; bodies are captured as lossless flat token regions.
//!
//! The lowering maps every routine keyword → `Function` (`routine_kind`
//! property), `type X = object|enum|tuple|…` → `Type`, `object of Base` →
//! `EXTENDS`, module-level `const`/`let`/`var` → `Constant`, and
//! `import`/`from … import` → `IMPORTS`. Calls use a deterministic scope ladder;
//! Nim's UFCS (`x.f()` ≡ `f(x)`) is resolved by name, with ambiguity preserved.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Nim language front end. Zero-sized: all state lives in the parse trees and
/// the lowering pass.
pub struct NimFrontEnd;

impl LanguageFrontEnd for NimFrontEnd {
    fn name(&self) -> &'static str {
        "nim"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["nim", "nims"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn module_path(&self, rel_path: &str) -> Vec<String> {
        module_path_for(rel_path)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once for the resolution ladder); merge it into the shared
        // graph the pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

/// Map a repo-relative Nim path to its module path. Nim has no special index file
/// (unlike Python's `__init__.py` or Rust's `mod.rs`): the module is the file
/// stem, scoped by its directory segments. A `src/` layout root is stripped.
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = rel.strip_prefix("src/").unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file
        .strip_suffix(".nims")
        .or_else(|| file.strip_suffix(".nim"))
        .unwrap_or(file);
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
    fn module_paths() {
        assert_eq!(module_path_for("foo.nim"), vec!["foo"]);
        assert_eq!(module_path_for("a/b/c.nim"), vec!["a", "b", "c"]);
        assert_eq!(module_path_for("src/pkg/mod.nim"), vec!["pkg", "mod"]);
        assert_eq!(module_path_for("build.nims"), vec!["build"]);
    }

    #[test]
    fn front_end_identity() {
        let fe = NimFrontEnd;
        assert_eq!(fe.name(), "nim");
        assert_eq!(fe.extensions(), &["nim", "nims"]);
    }

    #[test]
    fn end_to_end_lossless_round_trip() {
        // A representative snippet exercising doc/line/block comments, imports, an
        // object with inheritance, an enum, constants/vars, a generic proc, an
        // accent-quoted operator routine, pragmas, UFCS calls, raw/triple strings,
        // char and suffixed numeric literals — must reconstruct byte-for-byte.
        let src = "\
## Module docs.
import os, strutils
from sequtils import map, filter

const
  MaxItems = 100
  Name = \"default\"

var errCount = 0'i32

type
  Item = ref object of RootObj
    id: int
    name: string
  Color = enum
    red, green, blue

proc label[T](it: Item, sep: string): string {.inline.} =
  result = $it.id & sep & it.name

func `+`(a, b: int): int = a + b

method describe(self: Item): string {.base.} =
  let raw = r\"C:\\path\"
  let multi = \"\"\"line1
line2\"\"\"
  echo 'x', multi, raw
  self.label(\":\")

for i in 0 ..< MaxItems:
  if i mod 2 == 0:
    echo i
";
        let tree = parser::parse("store.nim", src);
        assert!(tree.is_lossless(), "Nim front end must round-trip source");
    }
}
