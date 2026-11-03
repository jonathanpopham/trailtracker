//! Mojo front end: lossless lexer + CST parser + lowering, wired to the shared
//! IR through the [`LanguageFrontEnd`] seam.
//!
//! Mojo is a Python superset, so this front end is built directly on the Python
//! model: an indentation-significant, purely-lossless lexer (`#` line comments and
//! leading indentation are trivia, `newline` is a structural non-trivia token),
//! and a parser that derives INDENT/DEDENT from those tokens, parsing item headers
//! precisely while capturing bodies as balanced token regions.
//!
//! The lowering maps Mojo honestly onto the shared ontology: `fn` **and** `def`
//! → `Function` (a method → `HAS_METHOD` from its enclosing type); `struct`/`trait`
//! → `Type` (`type_kind: struct|trait`), with struct conformances → `IMPLEMENTS`
//! and trait super-traits → `EXTENDS`; `class` → `Type` (`type_kind: class`,
//! Python-superset compatibility); `alias` and module-level `var`/`let` →
//! `Constant`; `import`/`from … import` → `IMPORTS` (plus `ExternalDependency`);
//! and calls → `CALLS` via the deterministic scope-resolution ladder.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Mojo language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct MojoFrontEnd;

impl LanguageFrontEnd for MojoFrontEnd {
    fn name(&self) -> &'static str {
        "mojo"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["mojo"]
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

/// Map a repo-relative Mojo path to its dotted module path. `__init__.mojo`
/// contributes the package directory but no extra segment; every other directory
/// or file stem does. A `src/` layout root is stripped if present. Mojo also
/// permits the `.🔥` extension, but the registry claims only `mojo`, so paths here
/// always carry the `.mojo` stem.
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = rel.strip_prefix("src/").unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file.strip_suffix(".mojo").unwrap_or(file);
    let mut module: Vec<String> = parts.iter().map(|s| s.to_string()).collect();
    match stem {
        "__init__" => {} // package marker: contributes no extra segment
        other => module.push(other.to_string()),
    }
    module
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("foo.mojo"), vec!["foo"]);
        assert_eq!(module_path_for("a/b/c.mojo"), vec!["a", "b", "c"]);
        assert_eq!(module_path_for("a/b/__init__.mojo"), vec!["a", "b"]);
        assert_eq!(module_path_for("src/pkg/mod.mojo"), vec!["pkg", "mod"]);
    }

    #[test]
    fn front_end_identity() {
        let fe = MojoFrontEnd;
        assert_eq!(fe.name(), "mojo");
        assert_eq!(fe.extensions(), &["mojo"]);
    }

    #[test]
    fn front_end_parse_is_lossless() {
        let fe = MojoFrontEnd;
        let src = "@value\nstruct Point(Stringable):\n    var x: Int\n    fn __init__(inout self, x: Int):\n        self.x = x\n";
        let tree = fe.parse("point.mojo", src);
        assert!(tree.is_lossless(), "front-end parse must round-trip");
    }
}
