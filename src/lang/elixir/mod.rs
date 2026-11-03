//! Elixir front end: lossless lexer + CST parser + lowering, wired to the shared
//! IR through the [`LanguageFrontEnd`] seam.
//!
//! Elixir blocks are `do … end` / `fn … end` delimited (with the `def f(x), do:
//! expr` keyword form), not brace- or indentation-delimited. The lexer stays
//! purely lossless — every byte is covered, `newline` is a structural (non-trivia)
//! token, and the rich surface (sigils vs operators, `:atoms` vs `key:`, heredocs,
//! module attributes) is disambiguated locally. The lowering maps
//! `def`/`defp`/`defmacro`/`defmacrop` → `Function` (a function inside a module →
//! `HAS_METHOD` from the module `Type`), `defmodule` → `Type` (`type_kind:
//! module`), `defprotocol` → `Type` (`type_kind: protocol`), `defimpl` → `Type`
//! (`type_kind: impl`), `import`/`alias`/`require`/`use` → `IMPORTS`, module-level
//! `@attr value` → `Constant`, and reuses a deterministic scope-resolution ladder
//! for `CALLS`.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Elixir language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct ElixirFrontEnd;

impl LanguageFrontEnd for ElixirFrontEnd {
    fn name(&self) -> &'static str {
        "elixir"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["ex", "exs"]
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

/// Map a repo-relative Elixir path to a scope path. A leading `lib/` or `test/`
/// source root is stripped (the common Mix layout); the remaining directories
/// plus the file stem become the segments.
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = rel
        .strip_prefix("lib/")
        .or_else(|| rel.strip_prefix("test/"))
        .unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file
        .strip_suffix(".exs")
        .or_else(|| file.strip_suffix(".ex"))
        .unwrap_or(file);
    let mut module: Vec<String> = parts.iter().map(|s| s.to_string()).collect();
    module.push(stem.to_string());
    module
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("foo.ex"), vec!["foo"]);
        assert_eq!(module_path_for("a/b/c.ex"), vec!["a", "b", "c"]);
        assert_eq!(module_path_for("lib/pkg/mod.ex"), vec!["pkg", "mod"]);
        assert_eq!(
            module_path_for("test/pkg/mod_test.exs"),
            vec!["pkg", "mod_test"]
        );
    }

    #[test]
    fn front_end_identity() {
        let fe = ElixirFrontEnd;
        assert_eq!(fe.name(), "elixir");
        assert_eq!(fe.extensions(), &["ex", "exs"]);
    }
}
