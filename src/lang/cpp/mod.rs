//! C++ front end: lossless lexer + CST parser + lowering, wired to the shared IR
//! through the [`LanguageFrontEnd`] seam.
//!
//! C++ is free-form (no significant whitespace) but has no function keyword: the
//! lexer stays purely lossless — every byte is covered, comments and whitespace
//! are trivia, and a whole preprocessor directive line is one non-trivia
//! `preprocessor` token — while the parser recognizes definitions by their
//! declarator shape (`name ( params )` ⇒ function). The lowering maps
//! function/method → `Function`, `class`/`struct`/`union` → `Type`, `enum` →
//! `Type` (+ enumerator `Constant`s), `namespace` → `Module`, `using`/`typedef` →
//! `Type` (alias), `const`/`constexpr` → `Constant`, `#include` → `IMPORTS`,
//! `#define` → `Macro`, and base classes → `EXTENDS`, reusing a deterministic
//! scope-resolution ladder for `CALLS`.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The C++ language front end. Zero-sized: all state lives in the parse trees and
/// the lowering pass.
pub struct CppFrontEnd;

impl LanguageFrontEnd for CppFrontEnd {
    fn name(&self) -> &'static str {
        "cpp"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["cpp", "cc", "cxx", "hpp", "hh"]
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
// point.hpp — a representative translation unit
#pragma once
#include <cmath>
#include \"vec.h\"

namespace geo {

template <typename T>
struct Vec2 {
    T x, y;
    Vec2(T x, T y) : x(x), y(y) {}
    T dot(const Vec2<T>& o) const { return x * o.x + y * o.y; }
};

class Shape : public Vec2<double> {
public:
    virtual double area() const = 0;
    ~Shape() {}
};

enum class Color : int { Red, Green = 2, Blue };

constexpr double PI = 3.14159;

using Real = double;

double hypot2(double a, double b) {
    return std::sqrt(a * a + b * b);
}

}  // namespace geo

#define SQUARE(x) ((x) * (x))
";

    #[test]
    fn front_end_identity() {
        let fe = CppFrontEnd;
        assert_eq!(fe.name(), "cpp");
        assert_eq!(fe.extensions(), &["cpp", "cc", "cxx", "hpp", "hh"]);
    }

    #[test]
    fn round_trips_byte_for_byte() {
        let tree = parser::parse("point.hpp", SAMPLE);
        assert!(
            tree.is_lossless(),
            "the CST must reconstruct the source byte-for-byte"
        );
        // No bytes should have escaped into error tokens for ordinary C++.
        assert_eq!(
            tree.root.error_token_count(),
            0,
            "well-formed C++ should produce no error tokens"
        );
    }

    #[test]
    fn lowering_produces_expected_kinds() {
        let tree = parser::parse("point.hpp", SAMPLE);
        let file = SourceFile {
            rel_path: "point.hpp".to_string(),
            module_path: Vec::new(),
            source: &tree.source,
            root: &tree.root,
        };
        let mut g = Graph::new();
        CppFrontEnd.lower(
            &LoweredInput {
                package: "demo",
                manifest_deps: &[],
                files: vec![file],
            },
            &mut g,
        );
        use crate::ir::ontology::node as ont;
        assert!(
            g.count_nodes_of(ont::FUNCTION) >= 3,
            "ctor + dot + hypot2 …"
        );
        assert!(g.count_nodes_of(ont::TYPE) >= 3, "Vec2, Shape, Color, Real");
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "namespace geo");
        assert!(g.count_nodes_of(ont::MACRO) >= 1, "SQUARE");
        assert!(g.count_nodes_of(ont::CONSTANT) >= 1, "PI + enumerators");
        assert!(g.has_node("ext::cmath"), "system include dependency");
    }
}
