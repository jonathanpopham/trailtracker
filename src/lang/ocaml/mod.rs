//! OCaml front end: lossless lexer + CST parser + lowering, wired to the shared
//! IR through the [`LanguageFrontEnd`] seam. This front end also stands in for the
//! wider ML / Caml family (its `.ml`/`.mli` surface and ML binding semantics).
//!
//! OCaml has a large grammar, so — like the Haskell front end — this keeps the
//! lexer fully lossless (every byte is a token; `(* nested *)` comments, `"..."`
//! and `{|quoted|}` strings, and char-vs-type-variable `'` are all handled; the
//! catch-all is an `error` token) and parses *top-level structure items* with a
//! pragmatic, layout-free rule: an item begins with a column-0 item-head keyword
//! (`let`, `module`, `type`, `open`, …) and runs to the next such head, with
//! `struct/sig/begin/object … end` blocks and bracket groups consumed whole. See
//! [`parser`] for the rationale and [`lower`] for the honest ontology mapping and
//! the deliberate punts (`val`/`exception`/`external`, nested bindings, sub-module
//! bodies, `USES_TYPE`, inheritance).

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The OCaml language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct OcamlFrontEnd;

impl LanguageFrontEnd for OcamlFrontEnd {
    fn name(&self) -> &'static str {
        "ocaml"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["ml", "mli"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once for the global function table); merge it into the
        // shared graph the pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn front_end_identity() {
        let fe = OcamlFrontEnd;
        assert_eq!(fe.name(), "ocaml");
        assert_eq!(fe.extensions(), &["ml", "mli"]);
    }

    #[test]
    fn parse_is_lossless_via_trait() {
        let fe = OcamlFrontEnd;
        let src = "let f x = x + 1\nlet () = print_int (f 41)\n";
        let tree = fe.parse("m.ml", src);
        assert!(tree.is_lossless());
    }
}
