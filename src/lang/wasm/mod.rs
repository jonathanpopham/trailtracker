//! WebAssembly text format (WAT / WAST) front end: lossless lexer +
//! s-expression CST parser + lowering, wired to the shared IR through the
//! [`LanguageFrontEnd`] seam.
//!
//! WAT is fully-parenthesized s-expressions (the textual encoding of a Wasm
//! module). The lexer stays purely lossless — every byte is covered, whitespace,
//! `;;` line comments and `(; ;)` **nested** block comments are trivia, and
//! unclassifiable bytes (including unterminated strings/comments) become `error`
//! tokens — and the parser models the single balanced delimiter form `(…)` as
//! nested `SExpr` groups, leaving atoms as leaves. The lowering maps
//! `(module …)` → `Module`, `(func …)` → `Function`, `(type …)` → `Type`,
//! `(global …)` → `Constant`, `(import …)` → `IMPORTS` + `ExternalDependency`,
//! `(export …)` → marks the target exported, and folded/flat `call` → `CALLS`.
//!
//! Wiring (the two one-line registrations described in `docs/vir.md`) lives
//! outside this module:
//!   - `src/lang/mod.rs`: add `pub mod wasm;`
//!   - `src/lang/frontend.rs`: add `Box::new(crate::lang::wasm::WasmFrontEnd)` to
//!     the `front_ends()` registry vec.
//!
//! The `wat` / `wast` extensions are disjoint from every existing front end.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The WebAssembly text format language front end. Zero-sized: all state lives in
/// the parse trees and the lowering pass.
pub struct WasmFrontEnd;

impl LanguageFrontEnd for WasmFrontEnd {
    fn name(&self) -> &'static str {
        "wasm"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["wat", "wast"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn module_path(&self, rel_path: &str) -> Vec<String> {
        // WASM modules name themselves; the file stem is only a fallback for the
        // implicit (unwrapped) module of a file with no `(module …)` form.
        let file = rel_path.rsplit('/').next().unwrap_or(rel_path);
        let stem = match file.rsplit_once('.') {
            Some((stem, _)) if !stem.is_empty() => stem,
            _ => file,
        };
        if stem.is_empty() {
            Vec::new()
        } else {
            vec![stem.to_string()]
        }
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (calls are
        // resolved per module across each file's forms); merge it into the shared
        // graph the pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn front_end_identity() {
        let fe = WasmFrontEnd;
        assert_eq!(fe.name(), "wasm");
        assert_eq!(fe.extensions(), &["wat", "wast"]);
    }

    #[test]
    fn module_paths() {
        let fe = WasmFrontEnd;
        assert_eq!(fe.module_path("lib.wat"), vec!["lib"]);
        assert_eq!(fe.module_path("src/pkg/mod.wast"), vec!["mod"]);
    }

    #[test]
    fn parse_is_lossless_round_trip() {
        let fe = WasmFrontEnd;
        let src = "\
;; a representative module
(module $demo
  (import \"env\" \"log\" (func $log (param i32)))
  (; a (; nested ;) block comment ;)
  (type $unary (func (param i32) (result i32)))
  (global $answer i32 (i32.const 42))
  (func $double (export \"double\") (param $a i32) (result i32)
    local.get $a
    local.get $a
    i32.add)
  (func $main (result i32)
    (call $double (global.get $answer))
    (call $log)
    call $double)
  (export \"main\" (func $main)))
";
        let tree = fe.parse("src/demo.wat", src);
        let mut rebuilt = String::new();
        tree.root.reconstruct(&tree.source, &mut rebuilt);
        assert_eq!(
            rebuilt, src,
            "front end parse must reconstruct byte-for-byte"
        );
        assert!(tree.is_lossless());
        assert_eq!(tree.root.error_token_count(), 0, "clean source, no errors");
    }
}
