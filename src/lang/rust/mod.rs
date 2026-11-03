//! Rust front end: lossless lexer + CST parser, plus the [`LanguageFrontEnd`]
//! that wires them to the shared lowering in `crate::ir::lower`.

pub mod lexer;
pub mod parser;

use crate::graph::Graph;
use crate::ir::lower;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Rust language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct RustFrontEnd;

impl LanguageFrontEnd for RustFrontEnd {
    fn name(&self) -> &'static str {
        "rust"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["rs"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn module_path(&self, rel_path: &str) -> Vec<String> {
        module_path_for(rel_path)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-crate lowering produces a self-contained sub-graph (it needs
        // every file at once for the resolution ladder); merge it into the shared
        // graph the pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }

    fn lower_cpg(&self, input: &LoweredInput, graph: &mut Graph) {
        // Base lowering plus the deterministic CPG overlay (ADR-0003): the base
        // sub-graph is byte-identical to `lower`'s; Statement nodes and
        // FLOWS_TO/DATA_DEP edges are strictly additive.
        let sub = lower::lower_with_cpg(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

/// Map a repo-relative `.rs` path to a crate-relative module path. `lib.rs`,
/// `main.rs`, and `mod.rs` contribute no extra segment; every other directory or
/// file name does.
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = rel.strip_prefix("src/").unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file.strip_suffix(".rs").unwrap_or(file);
    let mut module: Vec<String> = parts.iter().map(|s| s.to_string()).collect();
    match stem {
        "lib" | "main" | "mod" => {} // these contribute no extra segment
        other => module.push(other.to_string()),
    }
    module
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("src/lib.rs"), Vec::<String>::new());
        assert_eq!(module_path_for("src/main.rs"), Vec::<String>::new());
        assert_eq!(module_path_for("src/core/mod.rs"), vec!["core"]);
        assert_eq!(module_path_for("src/core/span.rs"), vec!["core", "span"]);
        assert_eq!(
            module_path_for("src/lang/rust/lexer.rs"),
            vec!["lang", "rust", "lexer"]
        );
    }

    #[test]
    fn front_end_identity() {
        let fe = RustFrontEnd;
        assert_eq!(fe.name(), "rust");
        assert_eq!(fe.extensions(), &["rs"]);
    }
}
