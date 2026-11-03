//! Zig front end: lossless lexer + CST parser + lowering, wired to the shared IR
//! through the [`LanguageFrontEnd`] seam.
//!
//! Zig is brace-delimited (so function bodies and container bodies are delimiter
//! groups, as in Rust/Go), but its defining idiom is that **types are values**:
//! `const Foo = struct {…}` / `enum {…}` / `union {…}` / `opaque {…}`. The parser
//! recognizes this pattern and parses the container body as a recursive item list,
//! so a `fn` inside a struct const stays a first-class node and lowers to a
//! `Function` with a `HAS_METHOD` edge from its `Type`. Top-level non-type
//! `const`/`var` lower to `Constant`; `const x = @import("…")` lowers to `IMPORTS`
//! (with an `ExternalDependency`/`DEPENDS_ON` for `std`/packages, and an internal
//! module import for relative `.zig` paths). Calls reuse the deterministic
//! scope-resolution ladder for `CALLS`.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Zig language front end. Zero-sized: all state lives in the parse trees and
/// the lowering pass.
pub struct ZigFrontEnd;

impl LanguageFrontEnd for ZigFrontEnd {
    fn name(&self) -> &'static str {
        "zig"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["zig"]
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

/// Map a repo-relative `.zig` path to its module path. Each Zig file is its own
/// namespace (a file is itself a struct), so the module path is the directory
/// segments plus the file stem — e.g. `src/util/math.zig` → `["src","util","math"]`.
fn module_path_for(rel: &str) -> Vec<String> {
    let mut parts: Vec<&str> = rel.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file.strip_suffix(".zig").unwrap_or(file);
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
        assert_eq!(module_path_for("main.zig"), vec!["main"]);
        assert_eq!(module_path_for("util/helper.zig"), vec!["util", "helper"]);
        assert_eq!(
            module_path_for("src/lang/zig.zig"),
            vec!["src", "lang", "zig"]
        );
    }

    #[test]
    fn front_end_identity() {
        let fe = ZigFrontEnd;
        assert_eq!(fe.name(), "zig");
        assert_eq!(fe.extensions(), &["zig"]);
    }

    #[test]
    fn end_to_end_lossless_round_trip() {
        let src = "\
//! A small module.
const std = @import(\"std\");

const Vec2 = struct {
    x: f32,
    y: f32,

    pub fn add(self: Vec2, other: Vec2) Vec2 {
        return Vec2{ .x = self.x + other.x, .y = self.y + other.y };
    }
};

const Tag = enum(u2) { a, b, c };
const Err = error{ Bad, Worse };

pub const ORIGIN = Vec2{ .x = 0, .y = 0 };
threadlocal var tick: u64 = 0;

const text =
    \\\\multi
    \\\\line
;

pub fn main() void {
    const v = ORIGIN.add(ORIGIN);
    _ = v;
}

test \"vec add\" {
    _ = ORIGIN.add(ORIGIN);
}
";
        let tree = parser::parse("vec.zig", src);
        assert!(tree.is_lossless(), "Zig front end must round-trip source");
    }
}
