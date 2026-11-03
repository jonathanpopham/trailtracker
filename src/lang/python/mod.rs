//! Python front end: lossless lexer + CST parser + lowering, wired to the shared
//! IR through the [`LanguageFrontEnd`] seam.
//!
//! Python is whitespace-significant. The lexer stays purely lossless — every byte
//! is covered, newlines are emitted as structural `NEWLINE` tokens and leading
//! indentation as `whitespace` trivia — and the parser derives INDENT/DEDENT
//! structure from those, so the lexer never has to fabricate zero-width tokens.
//! The lowering maps `def`→`Function`, `class`→`Type` (`type_kind: class`),
//! module-level bindings→`Constant`, inheritance→`EXTENDS`, and reuses the
//! deterministic scope-resolution ladder for `CALLS`.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Python language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct PythonFrontEnd;

impl LanguageFrontEnd for PythonFrontEnd {
    fn name(&self) -> &'static str {
        "python"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["py", "pyi"]
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

/// Map a repo-relative Python path to its dotted module path. `__init__.py`
/// contributes the package directory but no extra segment; every other directory
/// or file stem does. A `src/` layout root is stripped if present.
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = rel.strip_prefix("src/").unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file
        .strip_suffix(".pyi")
        .or_else(|| file.strip_suffix(".py"))
        .unwrap_or(file);
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
        assert_eq!(module_path_for("foo.py"), vec!["foo"]);
        assert_eq!(module_path_for("a/b/c.py"), vec!["a", "b", "c"]);
        assert_eq!(module_path_for("a/b/__init__.py"), vec!["a", "b"]);
        assert_eq!(module_path_for("src/pkg/mod.py"), vec!["pkg", "mod"]);
        assert_eq!(module_path_for("stubs/x.pyi"), vec!["stubs", "x"]);
    }

    #[test]
    fn front_end_identity() {
        let fe = PythonFrontEnd;
        assert_eq!(fe.name(), "python");
        assert_eq!(fe.extensions(), &["py", "pyi"]);
    }
}
