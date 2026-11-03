//! Crystal front end: lossless lexer + CST parser + lowering, wired to the shared
//! IR through the [`LanguageFrontEnd`] seam.
//!
//! Crystal is a Ruby-family language: `end`-delimited blocks (with `do…end` /
//! `{…}` method blocks), `def`/`class`/`module`, and the same rich context-sensitive
//! surface (regex vs division, `%w[]` vs modulo, heredocs). The lexer stays purely
//! lossless — every byte is covered, `newline` is a structural (non-trivia) token —
//! while honouring the ways Crystal departs from Ruby (single-quoted `Char`
//! literals, no `=begin` block comments, `<<-` heredocs, numeric type suffixes).
//!
//! The lowering maps honestly (see the IR Atlas): `def`→`Function`, `macro`→`Macro`,
//! `class`/`struct`/`enum`/`annotation`→`Type` (distinguished by `type_kind`),
//! `module`/`lib`→`Module`, `class C < Base`→`EXTENDS`, `include`/`extend`→
//! `IMPLEMENTS`, `require`→`IMPORTS`, and reuses the deterministic scope-resolution
//! ladder for `CALLS`.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Crystal language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct CrystalFrontEnd;

impl LanguageFrontEnd for CrystalFrontEnd {
    fn name(&self) -> &'static str {
        "crystal"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["cr"]
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

/// Map a repo-relative Crystal path to a scope path. A leading `src/` or `lib/`
/// source root is stripped (the common shards / Crystal project layout); the
/// remaining directories plus the file stem become the segments.
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = rel
        .strip_prefix("src/")
        .or_else(|| rel.strip_prefix("lib/"))
        .unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file.strip_suffix(".cr").unwrap_or(file);
    let mut module: Vec<String> = parts.iter().map(|s| s.to_string()).collect();
    module.push(stem.to_string());
    module
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::frontend::SourceFile;

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("foo.cr"), vec!["foo"]);
        assert_eq!(module_path_for("a/b/c.cr"), vec!["a", "b", "c"]);
        assert_eq!(module_path_for("src/pkg/mod.cr"), vec!["pkg", "mod"]);
        assert_eq!(module_path_for("lib/dep/thing.cr"), vec!["dep", "thing"]);
    }

    #[test]
    fn front_end_identity() {
        let fe = CrystalFrontEnd;
        assert_eq!(fe.name(), "crystal");
        assert_eq!(fe.extensions(), &["cr"]);
    }

    /// End-to-end lossless round-trip through the front end's `parse`: the CST must
    /// reconstruct the source byte-for-byte across a spread of Crystal surface
    /// syntax (chars, heredocs, percent literals, generics, macros, lib bindings,
    /// annotations, unicode, and unterminated edge cases).
    #[test]
    fn parse_is_lossless_round_trip() {
        let fe = CrystalFrontEnd;
        let cases = [
            "# leading comment\nrequire \"json\"\nrequire \"./util\"\n",
            "VERSION = \"1.2.3\"\nMAX : Int32 = 10\n",
            "module Geo\n  class Point < Base\n    include Comparable\n    def initialize(@x : Int32, @y : Int32)\n    end\n    def self.origin : Point\n      new(0, 0)\n    end\n    def <=>(other)\n      @x <=> other.x\n    end\n  end\nend\n",
            "struct Vec2(T)\n  abstract def length : T\nend\n",
            "enum Color : UInt8\n  Red\n  Green\n  Blue\nend\n",
            "@[Link(\"c\")]\nlib LibC\n  fun printf(fmt : UInt8*, ...) : Int32\nend\n",
            "macro define(name)\n  def {{name}}\n    {% if true %}\n      42\n    {% end %}\n  end\nend\n",
            "ch = 'a'\nnl = '\\n'\ns = \"interp #{ch} end\"\n",
            "doc = <<-SQL\n  select 1\nSQL\nputs doc\n",
            "w = %w[a b c]\ni = %i(x y)\nr = /ab+/i\n",
            "n = 0xFF_u8 + 1.5e3_f64 + 42i64\n",
            "[1, 2, 3].each do |x|\n  puts x if x > 1\nend\n",
            "λ = \"☃ €\"  # unicode\n",
            "",
            "\n\n   \n# only trivia\n",
            "def broken(\n  x = (1, 2\n",
            "c = 'oops\nx = <<-EOF\n  body\n",
        ];
        for src in cases {
            let tree = fe.parse("sample.cr", src);
            let mut rebuilt = String::new();
            tree.root.reconstruct(&tree.source, &mut rebuilt);
            assert_eq!(rebuilt, src, "front-end parse must round-trip: {src:?}");
            assert!(tree.is_lossless(), "is_lossless must hold: {src:?}");
        }
    }

    #[test]
    fn lower_produces_a_graph() {
        let fe = CrystalFrontEnd;
        let src = "require \"json\"\nclass Greeter\n  def hello\n    puts(\"hi\")\n  end\nend\n";
        let tree = fe.parse("greeter.cr", src);
        let file = SourceFile {
            rel_path: "greeter.cr".to_string(),
            module_path: fe.module_path("greeter.cr"),
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
        // A File node, a Type (Greeter), a Function (hello), and a json dependency.
        assert!(g.nodes().any(|n| n.kind == crate::ir::ontology::node::TYPE));
        assert!(g
            .nodes()
            .any(|n| n.kind == crate::ir::ontology::node::FUNCTION));
        assert!(g.has_node("ext::json"));
    }
}
