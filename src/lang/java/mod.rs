//! Java front end: lossless lexer + CST parser + lowering, wired to the shared
//! IR through the [`LanguageFrontEnd`] seam.
//!
//! Java is brace-delimited like Rust, so the parser follows the Rust strategy
//! (precise headers, balanced token-tree bodies) while the lowering follows the
//! Python strategy (an object model with inheritance). The lowering maps
//! `class`/`interface`/`enum`/`record`/`@interface`→`Type` (distinguished by a
//! `type_kind`), methods/constructors→`Function` (`HAS_METHOD` from the enclosing
//! type), fields/record-components→`Constant`, `extends`→`EXTENDS`,
//! `implements`→`IMPLEMENTS`, and `import`→`IMPORTS`, reusing a deterministic
//! scope-resolution ladder for `CALLS`.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Java language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct JavaFrontEnd;

impl LanguageFrontEnd for JavaFrontEnd {
    fn name(&self) -> &'static str {
        "java"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["java"]
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

/// Map a repo-relative Java path to its package path (dotted segments). The
/// conventional Maven/Gradle source roots (`src/main/java/`, `src/test/java/`)
/// and a bare `src/` root are stripped if present; the directory chain that
/// remains is the package, and the file stem contributes no segment (a Java file
/// is not itself a scope — its top-level types are).
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = ["src/main/java/", "src/test/java/", "src/"]
        .iter()
        .find_map(|p| rel.strip_prefix(p))
        .unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    parts.pop(); // the file name itself contributes no package segment
    parts.iter().map(|s| s.to_string()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_paths() {
        assert_eq!(
            module_path_for("src/main/java/com/foo/Bar.java"),
            vec!["com", "foo"]
        );
        assert_eq!(
            module_path_for("src/test/java/com/foo/BarTest.java"),
            vec!["com", "foo"]
        );
        assert_eq!(module_path_for("com/foo/Bar.java"), vec!["com", "foo"]);
        assert_eq!(module_path_for("Bar.java"), Vec::<String>::new());
        assert_eq!(module_path_for("src/App.java"), Vec::<String>::new());
    }

    #[test]
    fn front_end_identity() {
        let fe = JavaFrontEnd;
        assert_eq!(fe.name(), "java");
        assert_eq!(fe.extensions(), &["java"]);
    }

    #[test]
    fn lossless_round_trip() {
        // A representative file exercising comments, generics, annotations, a text
        // block, a constructor, an interface, an enum, and a record.
        let src = "\
// banner comment
package com.example.app;

import java.util.List;
import static java.lang.Math.max;

/** A 2D point. */
@Deprecated
public final class Point implements Comparable<Point> {
    private final int x;
    private int y;
    static final String NOTE = \"\"\"
        a text
        block\"\"\";

    public Point(int x, int y) {
        this.x = x;
        this.y = y;
    }

    @Override
    public int compareTo(Point other) {
        return max(this.x, other.x);
    }

    interface Named { String name(); }

    enum Kind { CARTESIAN, POLAR }
}

record Pair(int a, int b) implements Point.Named {
    public String name() { return \"pair\"; }
}
";
        let tree = parser::parse("Point.java", src);
        assert!(
            tree.is_lossless(),
            "Java front end must reconstruct source byte-for-byte"
        );
        // And the lowering of it stays deterministic.
        let file = crate::lang::frontend::SourceFile {
            rel_path: "src/main/java/com/example/app/Point.java".to_string(),
            module_path: JavaFrontEnd.module_path("src/main/java/com/example/app/Point.java"),
            source: &tree.source,
            root: &tree.root,
        };
        let g1 = lower::lower("app", std::slice::from_ref(&file), &[]);
        let g2 = lower::lower("app", std::slice::from_ref(&file), &[]);
        assert_eq!(g1.to_jsonl(), g2.to_jsonl());
    }
}
