//! Swift front end: lossless lexer + CST parser + lowering, wired to the shared
//! IR through the [`LanguageFrontEnd`] seam.
//!
//! Swift is brace-delimited (newlines are ordinary trivia, like Rust), so the
//! lexer stays purely lossless and the parser recovers structure from braces —
//! type/extension bodies are recursive member lists, function bodies are opaque
//! balanced token-tree blocks. The lowering maps `func`/`init`/`deinit`/
//! `subscript`→`Function`, `class`/`struct`/`enum`/`protocol`/`actor`→`Type`
//! (distinguished by `type_kind`), `typealias`→`Type` (`type_kind: alias`),
//! file-scope `let`/`var`→`Constant`, and `import`→`IMPORTS`+`ExternalDependency`.
//! Class inheritance lowers to `EXTENDS`, protocol conformance to `IMPLEMENTS`,
//! and `extension` members to `HAS_METHOD` on the extended type.
//!
//! Swift symbols are module-global (one module ≈ the package), so unlike Python
//! there is no per-file module scope; [`LanguageFrontEnd::module_path`] keeps the
//! flat default and call resolution runs against the whole batch at once.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Swift language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct SwiftFrontEnd;

impl LanguageFrontEnd for SwiftFrontEnd {
    fn name(&self) -> &'static str {
        "swift"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["swift"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once for module-global call/type resolution); merge it
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
        let fe = SwiftFrontEnd;
        assert_eq!(fe.name(), "swift");
        assert_eq!(fe.extensions(), &["swift"]);
    }

    #[test]
    fn round_trip_reconstructs_source_byte_for_byte() {
        // A representative snippet exercising comments, every string form,
        // numbers, attributes, all type-like constructs, inheritance, an
        // extension, generics, async, and interpolation.
        let src = "\
#!/usr/bin/swift
// TrailTracker Swift round-trip fixture
import Foundation
import struct Core.Buffer

/// A documented constant.
let version = \"1.0\"
let raw = #\"a \\#(version) literal\"#
let multi = \"\"\"
  line one
  line two \\(version)
  \"\"\"

@objc
public final class Point<T>: NSObject, Codable where T: Equatable {
    var x: Double = 0.0
    var y: Double = 0x1.8p1

    init?(x: Double, y: Double) {
        self.x = x
        self.y = y
    }

    deinit { cleanup() }

    func norm() async -> Double {
        return sqrt(self.x * self.x + self.y * self.y)
    }

    subscript(i: Int) -> Double { x }
}

protocol Shape {
    func area() -> Double
}

struct Circle: Shape {
    let r: Double
    func area() -> Double { 3.14159 * r * r }
}

enum Direction {
    case north, south
    case east
    func opposite() -> Direction { self }
}

actor Counter {
    private var n = 0
    func bump() { n += 1 }
}

extension Circle: Equatable {
    func describe() -> String { \"circle of \\(r)\" }
}

typealias Meters = Double

func add(_ a: Int, _ b: Int) -> Int { a + b /* inline */ }
";
        let tree = parser::parse("fixture.swift", src);
        assert!(
            tree.is_lossless(),
            "Swift CST must reconstruct the source byte-for-byte"
        );
        // The byte-for-byte reconstruction, made explicit.
        let mut rebuilt = String::new();
        tree.root.reconstruct(&tree.source, &mut rebuilt);
        assert_eq!(rebuilt, src);
        // No bytes should have landed in error tokens for clean source.
        assert_eq!(tree.root.error_token_count(), 0, "no error tokens expected");
    }

    #[test]
    fn front_end_parse_is_lossless() {
        let fe = SwiftFrontEnd;
        let src = "func f() { g() }\nfunc g() {}\n";
        let tree = fe.parse("f.swift", src);
        assert!(tree.is_lossless());
    }
}
