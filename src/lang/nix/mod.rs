//! Nix front end: lossless lexer + CST parser + lowering, wired to the shared IR
//! through the [`LanguageFrontEnd`] seam.
//!
//! Nix is a functional configuration language with no named classes, no static
//! types, and no declaration-site inheritance — it maps **coarsely** to the
//! shared ontology, and this front end is deliberately honest about that rather
//! than inventing structure. Its one pervasive construct is the attribute binding
//! `name = expr;`, so the lexer covers Nix's surface in full (both string forms
//! with `${ }` interpolation, paths and `<…>` search paths, the operator set),
//! the parser recognizes the binding-bearing scopes (`{ … }` attribute sets,
//! `let … in`, lambda formals) precisely while capturing values as balanced
//! token regions, and the lowering maps an attribute binding → [`Constant`], a
//! binding whose value is a lambda → [`Function`], `import`/`<…>` → `IMPORTS`
//! (plus `ExternalDependency` for search paths), and a function application whose
//! head is a known binding → `CALLS`. See [`lower`] for the full mapping and the
//! list of intentional punts (`inherit`, dynamic attrs, `with`/`let` scoping).

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Nix language front end. Zero-sized: all state lives in the parse trees and
/// the lowering pass.
pub struct NixFrontEnd;

impl LanguageFrontEnd for NixFrontEnd {
    fn name(&self) -> &'static str {
        "nix"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["nix"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph; merge it
        // into the shared graph the pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn front_end_identity() {
        let fe = NixFrontEnd;
        assert_eq!(fe.name(), "nix");
        assert_eq!(fe.extensions(), &["nix"]);
    }

    #[test]
    fn lossless_round_trip_on_representative_snippet() {
        // A representative slice of real Nix: a flake/derivation-style file with
        // comments, both string forms with interpolation, paths and search paths,
        // a function (formals lambda), `let … in`, `with`, `inherit`, lists,
        // nested `rec` attribute sets, and the update operator.
        let src = "\
# package definition
{ pkgs ? import <nixpkgs> { }, lib, ... }:

let
  version = \"2.4.1\";
  src = ./src;
  message = ''
    Building demo v${version}
    path is ''${PWD} and an escaped quote: '''
  '';
  patches = [ ./fix.patch ../shared/common.patch ];
  helper = name: pkgs.lib.toUpper name;
in
pkgs.stdenv.mkDerivation rec {
  pname = \"demo\";
  inherit version src;
  buildInputs = with pkgs; [ openssl zlib ];
  meta = {
    description = helper \"demo\";
    extra = { a = 1; } // { b = 2; };
  };
}
";
        let fe = NixFrontEnd;
        let tree = fe.parse("default.nix", src);
        assert!(
            tree.is_lossless(),
            "the Nix front end must reconstruct source byte-for-byte"
        );
        assert_eq!(tree.error_byte_ratio(), 0.0, "no bytes should be errors");

        // And the lowering produces a non-trivial, deterministic graph.
        let file = crate::lang::frontend::SourceFile {
            rel_path: "default.nix".to_string(),
            module_path: vec![],
            source: &tree.source,
            root: &tree.root,
        };
        let input = LoweredInput {
            package: "demo",
            manifest_deps: &[],
            files: vec![file],
        };
        let mut g = Graph::new();
        fe.lower(&input, &mut g);
        assert!(g.node_count() > 0);
        let again = {
            let file = crate::lang::frontend::SourceFile {
                rel_path: "default.nix".to_string(),
                module_path: vec![],
                source: &tree.source,
                root: &tree.root,
            };
            let input = LoweredInput {
                package: "demo",
                manifest_deps: &[],
                files: vec![file],
            };
            let mut g2 = Graph::new();
            fe.lower(&input, &mut g2);
            g2
        };
        assert_eq!(
            g.to_jsonl(),
            again.to_jsonl(),
            "lowering must be deterministic"
        );
    }
}
