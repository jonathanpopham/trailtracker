//! Haskell front end: lossless lexer + CST parser + lowering, wired to the shared
//! IR through the [`LanguageFrontEnd`] seam.
//!
//! Haskell is layout-sensitive, which makes a full grammar expensive; this front
//! end keeps the lexer fully lossless (every byte is a token, trivia and nested
//! block comments preserved, anything unclassifiable is an `error` token) and
//! parses *top-level* structure with a pragmatic, layout-free rule: a declaration
//! head is a token in byte-column 0, and an item runs to the next column-0 head
//! (balanced delimiter groups consumed whole). See [`parser`] for the full
//! rationale and [`lower`] for the honest ontology mapping and the deliberate
//! punts (nested bindings, fixity, foreign, superclass `EXTENDS`, `USES_TYPE`).

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Haskell language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct HaskellFrontEnd;

impl LanguageFrontEnd for HaskellFrontEnd {
    fn name(&self) -> &'static str {
        "haskell"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["hs", "lhs"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn module_path(&self, rel_path: &str) -> Vec<String> {
        module_path_for(rel_path)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once for the global function table); merge it into the
        // shared graph the pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

/// Map a repo-relative `.hs`/`.lhs` path to a fallback scope path: the directory
/// segments plus the file name with its extension stripped (Haskell's module
/// `Data.Map` lives at `Data/Map.hs`). This is only a fallback — the lowering
/// prefers the file's own `module X where` header when present, since the source
/// root that would be trimmed from the front of the path is not known here.
fn module_path_for(rel: &str) -> Vec<String> {
    let mut parts: Vec<String> = rel.split('/').map(|s| s.to_string()).collect();
    if let Some(last) = parts.last_mut() {
        if let Some((head, _ext)) = last.rsplit_once('.') {
            *last = head.to_string();
        }
    }
    parts.retain(|s| !s.is_empty());
    parts
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn front_end_identity() {
        let fe = HaskellFrontEnd;
        assert_eq!(fe.name(), "haskell");
        assert_eq!(fe.extensions(), &["hs", "lhs"]);
    }

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("Main.hs"), vec!["Main"]);
        assert_eq!(module_path_for("Data/Map.hs"), vec!["Data", "Map"]);
        assert_eq!(
            module_path_for("src/Data/Map.lhs"),
            vec!["src", "Data", "Map"]
        );
    }

    #[test]
    fn parse_is_lossless_via_trait() {
        let fe = HaskellFrontEnd;
        let src = "module M where\nf x = x + 1\n";
        let tree = fe.parse("M.hs", src);
        assert!(tree.is_lossless());
    }
}
