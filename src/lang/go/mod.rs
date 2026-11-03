//! Go front end: lossless lexer + CST parser + lowering, wired to the shared IR
//! through the [`LanguageFrontEnd`] seam.
//!
//! Go is brace-delimited (so blocks and struct/interface bodies are delimiter
//! groups, as in Rust), but its top-level declarations and grouped specs are
//! newline-terminated, so the lexer emits `newline` as a structural token and the
//! parser stops single specs at a newline. The lowering maps `func`→`Function`
//! (a func with a receiver → `HAS_METHOD` from its receiver `Type`), `type`→`Type`
//! with a `type_kind` of `struct`/`interface`/`alias`/`defined`, package-level
//! `const`/`var`→`Constant`, embedded interfaces→`EXTENDS`, and reuses the
//! deterministic scope-resolution ladder for `CALLS`.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Go language front end. Zero-sized: all state lives in the parse trees and
/// the lowering pass.
pub struct GoFrontEnd;

impl LanguageFrontEnd for GoFrontEnd {
    fn name(&self) -> &'static str {
        "go"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["go"]
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

/// Map a repo-relative `.go` path to its package path. In Go a package is a
/// directory: every `.go` file in a directory shares one package, so the module
/// path is the directory segments and the file name contributes no segment.
fn module_path_for(rel: &str) -> Vec<String> {
    let mut parts: Vec<&str> = rel.split('/').collect();
    parts.pop(); // drop the file name
    parts.iter().map(|s| s.to_string()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("main.go"), Vec::<String>::new());
        assert_eq!(module_path_for("util/helper.go"), vec!["util"]);
        assert_eq!(module_path_for("pkg/db/conn.go"), vec!["pkg", "db"]);
    }

    #[test]
    fn front_end_identity() {
        let fe = GoFrontEnd;
        assert_eq!(fe.name(), "go");
        assert_eq!(fe.extensions(), &["go"]);
    }

    #[test]
    fn end_to_end_lossless_round_trip() {
        // A representative snippet exercising comments, imports, a struct, an
        // interface with an embed, a method, a plain func, constants, raw and
        // interpreted strings, and a variety of literals — must reconstruct
        // byte-for-byte.
        let src = "\
// Package store persists things.
package store

import (
\t\"errors\"
\tf \"fmt\"
)

const (
\tMaxItems = 100
\tName     = `default`
)

var ErrMissing = errors.New(\"missing\")

type Item struct {
\tID   int
\tName string
}

type Repo interface {
\tGet(id int) (*Item, error)
\tfmt.Stringer
}

func (it *Item) Label() string {
\treturn f.Sprintf(\"%d:%s\", it.ID, it.Name)
}

func New() *Item {
\treturn &Item{ID: 0, Name: \"x\\n\"}
}
";
        let tree = parser::parse("store.go", src);
        assert!(tree.is_lossless(), "Go front end must round-trip source");
    }
}
