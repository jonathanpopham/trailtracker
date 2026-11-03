//! TypeScript front end: lossless lexer + CST parser + lowering, wired to the
//! shared IR through the [`LanguageFrontEnd`] seam.
//!
//! TypeScript (and TSX) is brace-delimited, so the parser's shape is closest to
//! the Rust front end: definition *headers* are parsed precisely while bodies and
//! expression regions are captured as balanced token-tree groups. The two
//! ECMAScript-specific hazards — interpolated/nested template literals and the
//! regex-vs-division ambiguity — are handled in the lexer without ever risking
//! losslessness (see [`lexer`]). The lowering maps `function`/arrow-valued
//! bindings → `Function`, `class`/`interface`/`enum`/`type` → `Type` (with an apt
//! `type_kind`), `namespace` → `Module`, plain bindings → `Constant`,
//! `extends`/`implements` → `EXTENDS`/`IMPLEMENTS`, and reuses the deterministic
//! scope-resolution ladder for `CALLS`.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The TypeScript language front end. Zero-sized: all state lives in the parse
/// trees and the lowering pass.
pub struct TypeScriptFrontEnd;

impl LanguageFrontEnd for TypeScriptFrontEnd {
    fn name(&self) -> &'static str {
        "typescript"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["ts", "tsx"]
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

/// Map a repo-relative TypeScript path to its module path. `index.{ts,tsx}` is a
/// directory's barrel module and contributes no extra segment; every other file
/// stem does. A `src/` layout root is stripped if present, and the `.d.ts`,
/// `.tsx`, `.ts` suffixes are removed.
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = rel.strip_prefix("src/").unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file
        .strip_suffix(".d.ts")
        .or_else(|| file.strip_suffix(".tsx"))
        .or_else(|| file.strip_suffix(".ts"))
        .unwrap_or(file);
    let mut module: Vec<String> = parts.iter().map(|s| s.to_string()).collect();
    match stem {
        "index" => {} // barrel module: contributes no extra segment
        other => module.push(other.to_string()),
    }
    module
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("foo.ts"), vec!["foo"]);
        assert_eq!(module_path_for("a/b/c.ts"), vec!["a", "b", "c"]);
        assert_eq!(module_path_for("a/b/index.ts"), vec!["a", "b"]);
        assert_eq!(module_path_for("src/pkg/util.ts"), vec!["pkg", "util"]);
        assert_eq!(module_path_for("ui/Button.tsx"), vec!["ui", "Button"]);
        assert_eq!(module_path_for("types/api.d.ts"), vec!["types", "api"]);
    }

    #[test]
    fn front_end_identity() {
        let fe = TypeScriptFrontEnd;
        assert_eq!(fe.name(), "typescript");
        assert_eq!(fe.extensions(), &["ts", "tsx"]);
    }

    #[test]
    fn parses_and_lowers_end_to_end() {
        let tree = parser::parse(
            "demo.ts",
            "export class A { m() { f(); } }\nfunction f() {}\n",
        );
        assert!(tree.is_lossless());
        let file = crate::lang::frontend::SourceFile {
            rel_path: "demo.ts".to_string(),
            module_path: module_path_for("demo.ts"),
            source: &tree.source,
            root: &tree.root,
        };
        let input = LoweredInput {
            package: "demo",
            manifest_deps: &[],
            files: vec![file],
        };
        let mut g = Graph::new();
        TypeScriptFrontEnd.lower(&input, &mut g);
        assert!(g.node_count() > 0, "lowering should populate the graph");
    }
}
