//! Julia front end: lossless lexer + CST parser + lowering, wired to the shared
//! IR through the [`LanguageFrontEnd`] seam.
//!
//! Julia is keyword-block delimited (not whitespace-significant): `function`,
//! `macro`, `struct`/`mutable struct`, `abstract type`, `primitive type`,
//! `module`/`baremodule`, `begin`, `quote`, `let`, `if`, `for`, `while`, `try`,
//! and the call-trailing `do` all open a block closed by `end`; a newline is
//! ordinary trivia used only as a soft statement separator. The lexer stays
//! purely lossless (nested `#= … =#` comments, `"…"`/`"""…"""` strings with
//! `$` interpolation, char-vs-transpose `'`, command literals, hex/oct/bin and
//! float numerals, `@macro` names) with a per-iteration progress guard. The
//! parser captures definitions, control structure, imports and calls precisely
//! while keeping expression bodies as balanced token groups. The lowering maps
//! `function`/short-form `f(x)=…`→`Function`, `macro`→`Macro`,
//! `struct`/`abstract type`/`primitive type`→`Type` (with a `type_kind`), a
//! `<:` supertype→`EXTENDS`, `using`/`import`→`IMPORTS`, `const`→`Constant`,
//! and `::Type` annotations→`USES_TYPE`, reusing a deterministic
//! scope-resolution ladder for `CALLS` (ambiguity from multiple dispatch is
//! preserved, never invented away).

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Julia language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct JuliaFrontEnd;

impl LanguageFrontEnd for JuliaFrontEnd {
    fn name(&self) -> &'static str {
        "julia"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["jl"]
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

/// Map a repo-relative `.jl` path to a dotted module path. A leading `src/` is
/// stripped if present (the standard Julia package layout). The file stem
/// contributes a segment, except a top-level package entry file (`src/Foo.jl`)
/// is handled the same as any other stem — Julia's module identity comes from
/// `module` declarations in the file, which the lowering tracks separately, so
/// the path segments are a best-effort scope hint only.
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = rel.strip_prefix("src/").unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file.strip_suffix(".jl").unwrap_or(file);
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
        assert_eq!(module_path_for("foo.jl"), vec!["foo"]);
        assert_eq!(module_path_for("a/b/c.jl"), vec!["a", "b", "c"]);
        assert_eq!(module_path_for("src/Pkg/util.jl"), vec!["Pkg", "util"]);
    }

    #[test]
    fn front_end_identity() {
        let fe = JuliaFrontEnd;
        assert_eq!(fe.name(), "julia");
        assert_eq!(fe.extensions(), &["jl"]);
    }

    #[test]
    fn lossless_round_trip_on_representative_snippet() {
        // A representative slice of real Julia: comments (incl. nested block),
        // imports, abstract/concrete types with a supertype, a const, long-form
        // and short-form functions, a method with a type annotation, control
        // flow, a do-block, strings with interpolation, a char, transpose, a
        // macro use, and a comprehension.
        let src = "\
# Geometry demo
module Geometry

using LinearAlgebra
import Base: show

#= a nested
   #= block =# comment =#

abstract type Shape end

mutable struct Circle <: Shape
    radius::Float64
end

const TAU = 6.283185

function area(c::Circle)
    return TAU * c.radius^2 / 2
end

scale(c::Circle, k) = Circle(c.radius * k)

function describe(c::Circle)
    a = area(c)
    label = if a > 10.0
        \"big: $(round(a; digits=2))\"
    else
        \"small\"
    end
    @info label
    println('•', label)
    M = [1.0 2.0; 3.0 4.0]
    Mt = M'
    sizes = map([1, 2, 3]) do n
        n * c.radius
    end
    squares = [x^2 for x in 1:3]
    return (label, Mt, sizes, squares)
end

end
";
        let fe = JuliaFrontEnd;
        let tree = fe.parse("Geometry.jl", src);
        assert!(
            tree.is_lossless(),
            "the Julia front end must reconstruct source byte-for-byte"
        );

        // And the lowering produces a non-trivial, deterministic graph.
        let file = crate::lang::frontend::SourceFile {
            rel_path: "Geometry.jl".to_string(),
            module_path: module_path_for("Geometry.jl"),
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

        let mut g2 = Graph::new();
        let tree2 = fe.parse("Geometry.jl", src);
        let file2 = crate::lang::frontend::SourceFile {
            rel_path: "Geometry.jl".to_string(),
            module_path: module_path_for("Geometry.jl"),
            source: &tree2.source,
            root: &tree2.root,
        };
        let input2 = LoweredInput {
            package: "demo",
            manifest_deps: &[],
            files: vec![file2],
        };
        fe.lower(&input2, &mut g2);
        assert_eq!(
            g.to_jsonl(),
            g2.to_jsonl(),
            "lowering must be deterministic across runs"
        );
    }
}
