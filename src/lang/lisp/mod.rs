//! Lisp front end: one lossless s-expression lexer + CST parser + lowering for the
//! Lisp family, wired to the shared IR through the [`LanguageFrontEnd`] seam.
//!
//! A single reader covers Common Lisp (`.lisp`, `.cl`), Scheme (`.scm`, `.ss`),
//! and Emacs Lisp (`.el`): these dialects share a lexical structure — balanced
//! delimiters, `"…"` strings, `#\` character literals, `;` line comments,
//! `#| … |#` *nested* block comments, `#;` datum comments, ratios/radix numbers,
//! and the quote family of reader macros. (Clojure has its own front end and
//! claims `.clj`/`.cljs`/`.cljc`/`.edn`, so this front end deliberately does not.)
//!
//! The lexer stays purely lossless — every byte is covered, comments and datum
//! markers are trivia, unclassifiable bytes (e.g. an unterminated block comment)
//! become `error` tokens — and the parser models the balanced delimiter forms as
//! nested groups, leaving atoms and reader macros as leaves. The lowering maps
//! `defun`/`defmethod`/`defmacro`/`defgeneric` and Scheme `(define (f …) …)` /
//! `(define f (lambda …))` → `Function`; `defclass`/`defstruct`/`deftype` /
//! `define-record-type` → `Type`; `defvar`/`defparameter`/`defconstant` and a
//! non-lambda `(define x …)` → `Constant`; `require`/`use-package`/`load`/`import`
//! → `IMPORTS`; and resolved head-symbol applications → `CALLS`.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Lisp language front end. Zero-sized: all state lives in the parse trees and
/// the lowering pass.
pub struct LispFrontEnd;

impl LanguageFrontEnd for LispFrontEnd {
    fn name(&self) -> &'static str {
        "lisp"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["lisp", "cl", "el", "scm", "ss"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn module_path(&self, rel_path: &str) -> Vec<String> {
        module_path_for(rel_path)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once to resolve calls); merge it into the shared graph the
        // pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

/// Map a repo-relative Lisp path to scope segments. Lisp has no portable
/// filename→namespace convention (Common Lisp uses `defpackage`/`in-package`,
/// Scheme uses libraries, Emacs Lisp uses features), so we fall back to the
/// directory structure: a `src/` source root is stripped if present and the file
/// extension is dropped. This is a deterministic, honest scope, not a claim about
/// the language's real package system.
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = rel.strip_prefix("src/").unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file
        .strip_suffix(".lisp")
        .or_else(|| file.strip_suffix(".cl"))
        .or_else(|| file.strip_suffix(".el"))
        .or_else(|| file.strip_suffix(".scm"))
        .or_else(|| file.strip_suffix(".ss"))
        .unwrap_or(file);
    let mut module: Vec<String> = parts.iter().map(|s| s.to_string()).collect();
    if !stem.is_empty() {
        module.push(stem.to_string());
    }
    module
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("core.lisp"), vec!["core"]);
        assert_eq!(
            module_path_for("src/my/app/core.lisp"),
            vec!["my", "app", "core"]
        );
        assert_eq!(module_path_for("lib/util.scm"), vec!["lib", "util"]);
        assert_eq!(module_path_for("init.el"), vec!["init"]);
    }

    #[test]
    fn front_end_identity() {
        let fe = LispFrontEnd;
        assert_eq!(fe.name(), "lisp");
        assert_eq!(fe.extensions(), &["lisp", "cl", "el", "scm", "ss"]);
    }

    #[test]
    fn parse_is_lossless_round_trip() {
        let fe = LispFrontEnd;
        let src = "\
;;; my/app/core.lisp  -*- lexical-binding: t -*-
(defpackage :my.app (:use :cl))
(in-package :my.app)

#| a block
   #| nested |# comment |#

;; a constant
(defparameter *answer* 42 \"the answer\")

(defclass point ()
  ((x :initarg :x :reader point-x)
   (y :initarg :y :reader point-y)))

(defun greet (name)
  \"Returns a greeting.\"
  (format nil \"hello, ~a #\\\\~a\" name #\\!))

(define (square x) (* x x))
(define cube (lambda (x) (* x x x)))

(require 'cl-lib)
(import (scheme base))
(list #xFF #b1010 1/2 'sym `(a ,b ,@c) #;(ignored))
";
        let tree = fe.parse("src/my/app/core.lisp", src);
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
