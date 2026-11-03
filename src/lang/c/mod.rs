//! C front end: lossless lexer + CST parser + lowering, wired to the shared IR
//! through the [`LanguageFrontEnd`] seam.
//!
//! C is free-form except for the preprocessor, whose directives are line-based.
//! The lexer stays purely lossless — every byte is covered, `NEWLINE` is emitted
//! as a structural (non-trivia) token so directive boundaries are visible, and
//! backslash–newline continuations are trivia so a multi-line `#define` is one
//! logical line. The parser collects each top-level *declaration unit* and
//! classifies it after the fact (function definition vs aggregate vs typedef vs
//! object declaration vs prototype), capturing bodies and parameter lists as
//! balanced token-tree groups. The lowering maps function definitions → `Function`,
//! `struct`/`union`/`enum` → `Type` (`type_kind`), `typedef` → `Type`
//! (`type_kind: typedef`), `#define` → `Macro`, top-level objects → `Constant`,
//! and `#include` → `IMPORTS` (plus `ExternalDependency`/`DEPENDS_ON` for system
//! headers), reusing a deterministic scope-resolution ladder for `CALLS`.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The C language front end. Zero-sized: all state lives in the parse trees and
/// the lowering pass.
pub struct CFrontEnd;

impl LanguageFrontEnd for CFrontEnd {
    fn name(&self) -> &'static str {
        "c"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["c", "h"]
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

/// Map a repo-relative C path to its scope segments: the directory components plus
/// the file stem (without the `.c`/`.h` extension). Unlike Rust/Python there is no
/// file that collapses into its directory, so each translation unit and header is
/// its own leaf scope. A `src/` layout root is stripped if present.
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = rel.strip_prefix("src/").unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file
        .strip_suffix(".c")
        .or_else(|| file.strip_suffix(".h"))
        .unwrap_or(file);
    let mut module: Vec<String> = parts.iter().map(|s| s.to_string()).collect();
    module.push(stem.to_string());
    module
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("main.c"), vec!["main"]);
        assert_eq!(module_path_for("a/b/c.c"), vec!["a", "b", "c"]);
        assert_eq!(module_path_for("src/util/io.h"), vec!["util", "io"]);
        assert_eq!(module_path_for("include/types.h"), vec!["include", "types"]);
    }

    #[test]
    fn front_end_identity() {
        let fe = CFrontEnd;
        assert_eq!(fe.name(), "c");
        assert_eq!(fe.extensions(), &["c", "h"]);
    }

    /// Lossless round-trip on a representative C snippet exercising comments, all
    /// string/char forms, numbers, preprocessor directives (including a multi-line
    /// `#define`), aggregates, typedefs, a global, and a function with calls.
    #[test]
    fn parse_round_trips_byte_for_byte() {
        let src = "\
/* trailtracker C front-end self-test */
#include <stdio.h>
#include \"geometry.h\"

#define PI 3.14159
#define AREA(r) \\
    (PI * (r) * (r))

typedef struct Circle {
    double radius;
    char   label[16];
} Circle;

enum Status { OK = 0, FAIL = -1 };

static const char *GREETING = \"hello\\tworld\\n\";

double circle_area(const Circle *c) {
    return AREA(c->radius);
}

int main(void) {
    Circle c = { .radius = 2.0, .label = L\"x\" };
    printf(\"%f\\n\", circle_area(&c));
    return 0;
}
";
        let fe = CFrontEnd;
        let tree = fe.parse("selftest.c", src);
        assert!(
            tree.is_lossless(),
            "C front end must reconstruct source byte-for-byte"
        );
        // Sanity: the reconstruction equals the input exactly.
        let mut rebuilt = String::new();
        tree.root.reconstruct(&tree.source, &mut rebuilt);
        assert_eq!(rebuilt, src);
    }
}
