//! Clojure front end: lossless lexer + s-expression CST parser + lowering, wired
//! to the shared IR through the [`LanguageFrontEnd`] seam.
//!
//! Clojure (and its dialects ClojureScript `.cljs`, reader-conditional `.cljc`,
//! and the EDN data format `.edn`) is homoiconic s-expressions. The lexer stays
//! purely lossless — every byte is covered, commas and `;` comments and `#_`
//! discards are trivia, unclassifiable bytes become `error` tokens — and the
//! parser models the three balanced delimiter forms as nested groups, leaving
//! atoms and reader macros as leaves. The lowering maps `defn`/`defn-`/`defmacro`
//! → `Function`, `def`/`defonce` → `Constant`, `ns` → `Module`,
//! `defrecord`/`deftype`/`defprotocol` → `Type`, `:require`/`:use`/`:import` →
//! `IMPORTS`, and resolved head-symbol applications → `CALLS`.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Clojure language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct ClojureFrontEnd;

impl LanguageFrontEnd for ClojureFrontEnd {
    fn name(&self) -> &'static str {
        "clojure"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["clj", "cljs", "cljc", "edn"]
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

/// Map a repo-relative Clojure path to its namespace segments. A `src/` (or
/// `test/`) source root is stripped if present, the file extension is dropped, and
/// Clojure's filename munging is reversed (`_` in a path segment is `-` in the
/// namespace). The authoritative namespace is the file's `ns` form; this is the
/// fallback used when a file declares none.
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = rel
        .strip_prefix("src/")
        .or_else(|| rel.strip_prefix("test/"))
        .unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file
        .strip_suffix(".cljc")
        .or_else(|| file.strip_suffix(".cljs"))
        .or_else(|| file.strip_suffix(".clj"))
        .or_else(|| file.strip_suffix(".edn"))
        .unwrap_or(file);
    let mut module: Vec<String> = parts.iter().map(|s| s.replace('_', "-")).collect();
    if !stem.is_empty() {
        module.push(stem.replace('_', "-"));
    }
    module
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("core.clj"), vec!["core"]);
        assert_eq!(
            module_path_for("src/my/app/core.clj"),
            vec!["my", "app", "core"]
        );
        assert_eq!(
            module_path_for("src/my_app/util.cljc"),
            vec!["my-app", "util"]
        );
        assert_eq!(
            module_path_for("test/demo/core_test.clj"),
            vec!["demo", "core-test"]
        );
        assert_eq!(module_path_for("config.edn"), vec!["config"]);
    }

    #[test]
    fn front_end_identity() {
        let fe = ClojureFrontEnd;
        assert_eq!(fe.name(), "clojure");
        assert_eq!(fe.extensions(), &["clj", "cljs", "cljc", "edn"]);
    }

    #[test]
    fn parse_is_lossless_round_trip() {
        let fe = ClojureFrontEnd;
        let src = "\
(ns my.app.core
  (:require [clojure.string :as str]
            [my.app.util :refer [helper]])
  (:import (java.util Date)))

;; a constant, with metadata
(def ^:private answer 42)

(defrecord Point [x y])

(defn greet
  \"Returns a greeting.\"
  [name]
  (str \"hello, \" name \", \" (helper answer)))

(defn- secret [] #_(ignored) {:k [1 2 3], :ch \\newline})
";
        let tree = fe.parse("src/my/app/core.clj", src);
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
