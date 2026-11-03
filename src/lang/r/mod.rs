//! R front end: lossless lexer + CST parser + lowering, wired to the shared IR
//! through the [`LanguageFrontEnd`] seam.
//!
//! R has no definition keywords — a function is an ordinary value bound by
//! assignment (`name <- function(args) body`, also `=`/`<<-`/`->`, and the R 4.1
//! `\(args) body` lambda). The lexer stays purely lossless (both string forms,
//! raw strings `r"(…)"`, backtick names, hex/decimal/complex numerals, the full
//! operator set including `%…%` infix and the `|>` pipe), and the parser segments
//! statements while keeping function definitions, brace blocks, and balanced
//! groups first-class. The lowering maps assignment-of-a-function → `Function`,
//! other top-level assignment → `Constant`, `library`/`require` → `IMPORTS`
//! (+ `ExternalDependency`/`DEPENDS_ON`), `setClass`/`setRefClass`/`R6Class` →
//! `Type`, and `f(...)`/`pkg::f(...)`/`obj$m(...)` → `CALLS`, resolved through a
//! deterministic scope ladder. R has no static inheritance or type annotations
//! reachable from a file's tokens, so no `EXTENDS`/`IMPLEMENTS`/`USES_TYPE` edges
//! are fabricated.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The R language front end. Zero-sized: all state lives in the parse trees and
/// the lowering pass.
pub struct RFrontEnd;

impl LanguageFrontEnd for RFrontEnd {
    fn name(&self) -> &'static str {
        "r"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["r", "R"]
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

/// Map a repo-relative `.R`/`.r` path to its scope segments. A leading `R/` (the
/// canonical package source directory) or `src/` is stripped; the `.R`/`.r`
/// extension is dropped from the final segment. R's package namespace is actually
/// flat (every `R/*.R` file shares one namespace), so this per-file grouping is a
/// CONTAINS convenience — cross-file calls still resolve at the "global" level.
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = rel
        .strip_prefix("R/")
        .or_else(|| rel.strip_prefix("src/"))
        .unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file
        .strip_suffix(".R")
        .or_else(|| file.strip_suffix(".r"))
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
        assert_eq!(module_path_for("foo.R"), vec!["foo"]);
        assert_eq!(module_path_for("R/utils.R"), vec!["utils"]);
        assert_eq!(module_path_for("R/model/fit.r"), vec!["model", "fit"]);
        assert_eq!(module_path_for("src/pkg/mod.R"), vec!["pkg", "mod"]);
    }

    #[test]
    fn front_end_identity() {
        let fe = RFrontEnd;
        assert_eq!(fe.name(), "r");
        assert_eq!(fe.extensions(), &["r", "R"]);
    }

    #[test]
    fn lossless_round_trip_on_representative_snippet() {
        // A representative slice of real R: comments, library imports, an R6 class,
        // S4 setClass, named/lambda functions, the pipe, raw strings, method
        // access, right-assignment, and control flow.
        let src = "\
# inventory module
library(dplyr)
require(R6)

Item <- R6Class(\"Item\",
  public = list(
    name = NULL,
    qty = 0,
    initialize = function(name, qty = 0) {
      self$name <- name
      self$qty <- qty
    },
    add = function(n) {
      self$qty <- self$qty + n
      invisible(self)
    }
  )
)

setClass(\"Point\", representation(x = \"numeric\", y = \"numeric\"))

make_summary <- function(items) {
  totals <- sapply(items, function(it) it$qty)
  data.frame(name = names(items), qty = totals) %>%
    dplyr::filter(qty > 0) -> kept
  kept
}

note <- r\"(raw \"string\" with )-ish content)\"
.config <- list(verbose = TRUE)
VERSION <- '1.2.3'

total <- make_summary(inventory)
";
        let fe = RFrontEnd;
        let tree = fe.parse("inventory.R", src);
        assert!(
            tree.is_lossless(),
            "the R front end must reconstruct source byte-for-byte"
        );
        assert_eq!(tree.error_byte_ratio(), 0.0, "no bytes should be errors");

        // And the lowering produces a non-trivial, deterministic graph.
        let file = crate::lang::frontend::SourceFile {
            rel_path: "inventory.R".to_string(),
            module_path: module_path_for("inventory.R"),
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
    }
}
