//! Elm front end: lossless lexer + CST parser + lowering, wired to the shared IR
//! through the [`LanguageFrontEnd`] seam.
//!
//! Elm's surface is an ML-family, Haskell-adjacent language: `--` line comments,
//! nested `{- -}` block comments, uppercase constructors vs lowercase variables,
//! and a top level whose declarations all begin in byte-column 0. This front end
//! keeps the lexer fully lossless (every byte is a token, trivia and nested block
//! comments preserved, anything unclassifiable is an `error` token) and parses
//! *top-level* structure with the same pragmatic, layout-free rule the Haskell
//! front end uses — a declaration head is a token in byte-column 0, and an item
//! runs to the next column-0 head (balanced delimiter groups consumed whole). See
//! [`parser`] for the rationale and [`lower`] for the honest ontology mapping and
//! the deliberate punts (type signatures, ports, constructors, nested bindings,
//! `USES_TYPE`).

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Elm language front end. Zero-sized: all state lives in the parse trees and
/// the lowering pass.
pub struct ElmFrontEnd;

impl LanguageFrontEnd for ElmFrontEnd {
    fn name(&self) -> &'static str {
        "elm"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["elm"]
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

/// Map a repo-relative `.elm` path to a fallback scope path: the directory
/// segments plus the file name with its extension stripped (Elm's module
/// `Json.Decode` lives at `Json/Decode.elm`). This is only a fallback — the
/// lowering prefers the file's own `module X exposing …` header when present,
/// since the source root that would be trimmed from the front of the path is not
/// known here.
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
        let fe = ElmFrontEnd;
        assert_eq!(fe.name(), "elm");
        assert_eq!(fe.extensions(), &["elm"]);
    }

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("Main.elm"), vec!["Main"]);
        assert_eq!(module_path_for("Json/Decode.elm"), vec!["Json", "Decode"]);
        assert_eq!(
            module_path_for("src/Data/Example.elm"),
            vec!["src", "Data", "Example"]
        );
    }

    #[test]
    fn parse_is_lossless_via_trait() {
        let fe = ElmFrontEnd;
        let src = "module M exposing (..)\nf x =\n    x + 1\n";
        let tree = fe.parse("M.elm", src);
        assert!(tree.is_lossless());
    }
}
