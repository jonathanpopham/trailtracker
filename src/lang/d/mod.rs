//! D front end: lossless lexer + CST parser + lowering, wired to the shared IR
//! through the [`LanguageFrontEnd`] seam.
//!
//! D is free-form (no significant whitespace) and, like C/C++, has no `function`
//! keyword for ordinary functions: the lexer stays purely lossless — every byte
//! is covered, all three comment forms (`//`, `/* */`, and the **nesting**
//! `/+ +/`) plus whitespace are trivia, and the full string zoo (`"..."`,
//! `` `wysiwyg` ``, `r"..."`, `x"..."`, `q{...}`, `q"..."`) is recognized — while
//! the parser recognizes definitions by their declarator shape (`name ( params )`
//! ⇒ function). The lowering maps `module a.b.c;` → a `Module` chain,
//! function/method → `Function`, `class`/`struct`/`interface`/`union`/`enum`/
//! `template` → `Type`, manifest `enum X = v;` / `const` / `immutable` →
//! `Constant`, `alias` → `Type` (alias), `import` → `IMPORTS`, base lists →
//! `EXTENDS`/`IMPLEMENTS`, and `new T(...)` + ordinary calls → `CALLS` via a
//! deterministic scope-resolution ladder.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The D language front end. Zero-sized: all state lives in the parse trees and
/// the lowering pass.
pub struct DFrontEnd;

impl LanguageFrontEnd for DFrontEnd {
    fn name(&self) -> &'static str {
        "d"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["d"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once for the resolution ladder); merge it into the shared
        // graph the pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::frontend::SourceFile;

    const SAMPLE: &str = "\
// shapes.d — a representative D module
module geo.shapes;

import std.math;
import std.stdio : writeln;

interface Drawable {
    void draw();
}

class Shape : Drawable {
    private double scale;
    this(double s) { this.scale = s; }
    double area() const { return 0.0; }
    void draw() { writeln(\"shape\"); }
    ~this() {}
}

struct Vec2(T) {
    T x, y;
    T dot(Vec2!T o) { return x * o.x + y * o.y; }
}

enum Color : int { Red, Green = 2, Blue }

enum PI = 3.14159;

immutable int K = 42;

alias Real = double;

double hypot2(double a, double b) {
    return std.math.sqrt(a * a + b * b);
}

void run() {
    auto s = new Shape(2.0);
    auto h = hypot2(3, 4);
}

/+ a /+ nested +/ comment +/
unittest {
    assert(hypot2(3, 4) == 5);
}
";

    #[test]
    fn front_end_identity() {
        let fe = DFrontEnd;
        assert_eq!(fe.name(), "d");
        assert_eq!(fe.extensions(), &["d"]);
    }

    #[test]
    fn round_trips_byte_for_byte() {
        let tree = parser::parse("shapes.d", SAMPLE);
        assert!(
            tree.is_lossless(),
            "the CST must reconstruct the source byte-for-byte"
        );
        // No bytes should have escaped into error tokens for ordinary D.
        assert_eq!(
            tree.root.error_token_count(),
            0,
            "well-formed D should produce no error tokens"
        );
    }

    /// The lossless round-trip contract, exercised across a spread of edge cases
    /// directly through the [`LanguageFrontEnd`] seam.
    #[test]
    fn lossless_round_trip_across_edge_cases() {
        let cases = [
            SAMPLE,
            "",
            "module m;\n",
            "auto q = q{ a + b }; auto d = q\"(nested (parens))\";\n",
            "auto r = r\"C:\\path\\file\"; auto b = `back\"tick`;\n",
            "int x = 0xDEAD_BEEF; double y = 1_000.5e-3f; auto z = 1 .. 10;\n",
            "/+ /+ deeply /+ nested +/ +/ +/ int n;\n",
            "char c = '\\'';\nstring s = \"line\\n\";\n",
            "#!/usr/bin/env rdmd\nvoid main() {}\n",
            "@safe @nogc pure nothrow void f() {}\n",
            "}}} stray )) ]]",
        ];
        let fe = DFrontEnd;
        for src in cases {
            let tree = fe.parse("case.d", src);
            assert!(tree.is_lossless(), "must round-trip byte-for-byte: {src:?}");
        }
    }

    #[test]
    fn lowering_produces_expected_kinds() {
        let tree = parser::parse("shapes.d", SAMPLE);
        let file = SourceFile {
            rel_path: "shapes.d".to_string(),
            module_path: Vec::new(),
            source: &tree.source,
            root: &tree.root,
        };
        let mut g = Graph::new();
        DFrontEnd.lower(
            &LoweredInput {
                package: "demo",
                manifest_deps: &[],
                files: vec![file],
            },
            &mut g,
        );
        use crate::ir::ontology::node as ont;
        assert!(
            g.count_nodes_of(ont::FUNCTION) >= 4,
            "ctor + dtor + area + draw + dot + hypot2 + run …"
        );
        assert!(
            g.count_nodes_of(ont::TYPE) >= 4,
            "Drawable, Shape, Vec2, Color, Real"
        );
        assert!(g.count_nodes_of(ont::MODULE) >= 2, "geo + geo.shapes");
        assert!(
            g.count_nodes_of(ont::CONSTANT) >= 4,
            "PI + K + Red/Green/Blue"
        );
        assert!(g.has_node("ext::std.math"), "import dependency");
    }
}
