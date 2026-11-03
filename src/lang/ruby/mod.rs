//! Ruby front end: lossless lexer + CST parser + lowering, wired to the shared IR
//! through the [`LanguageFrontEnd`] seam.
//!
//! Ruby's blocks are `end`-delimited (with `do…end` / `{…}` method blocks), not
//! brace- or indentation-delimited. The lexer stays purely lossless — every byte
//! is covered, `newline` is a structural (non-trivia) token, and the rich
//! context-sensitive surface (regex vs division, `%w[]` vs modulo, heredocs vs
//! left-shift) is disambiguated with a single value-position bit. The lowering
//! maps `def`→`Function`, `class`→`Type` (`type_kind: class`), `module`→`Type`
//! (`type_kind: module`), `class C < Base`→`EXTENDS`, `include`/`extend`/
//! `prepend`→`IMPLEMENTS`, `require`→`IMPORTS`, and reuses the deterministic
//! scope-resolution ladder for `CALLS`.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Ruby language front end. Zero-sized: all state lives in the parse trees and
/// the lowering pass.
pub struct RubyFrontEnd;

impl LanguageFrontEnd for RubyFrontEnd {
    fn name(&self) -> &'static str {
        "ruby"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["rb", "rake", "gemspec"]
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

/// Map a repo-relative Ruby path to a scope path. A leading `lib/` or `app/`
/// source root is stripped (the common gem / Rails layouts); the remaining
/// directories plus the file stem become the segments.
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = rel
        .strip_prefix("lib/")
        .or_else(|| rel.strip_prefix("app/"))
        .unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file
        .strip_suffix(".rb")
        .or_else(|| file.strip_suffix(".rake"))
        .or_else(|| file.strip_suffix(".gemspec"))
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
        assert_eq!(module_path_for("foo.rb"), vec!["foo"]);
        assert_eq!(module_path_for("a/b/c.rb"), vec!["a", "b", "c"]);
        assert_eq!(module_path_for("lib/pkg/mod.rb"), vec!["pkg", "mod"]);
        assert_eq!(
            module_path_for("app/models/user.rb"),
            vec!["models", "user"]
        );
        assert_eq!(module_path_for("Rakefile.rake"), vec!["Rakefile"]);
    }

    #[test]
    fn front_end_identity() {
        let fe = RubyFrontEnd;
        assert_eq!(fe.name(), "ruby");
        assert_eq!(fe.extensions(), &["rb", "rake", "gemspec"]);
    }
}
