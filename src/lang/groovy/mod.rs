//! Groovy front end: lossless lexer + CST parser + lowering, wired to the shared
//! IR through the [`LanguageFrontEnd`] seam.
//!
//! Groovy is a JVM language and brace-delimited like Java, so the parser follows
//! the Java strategy (precise headers, balanced token-tree bodies) and the
//! lowering follows the Java object model (inheritance, `HAS_METHOD`). The two
//! places Groovy diverges and the front end adapts:
//!
//! - **Optional statement terminators.** A newline ends a statement, so the
//!   parser's region collectors stop at depth-0 newlines as well as `;`.
//! - **Scripts and the Gradle DSL.** `.gradle` files (claimed alongside
//!   `.groovy`) are top-level statement bodies of DSL method calls with closure
//!   arguments. Those calls are attributed to a synthetic per-file *script*
//!   `Function` so the call graph stays honest.
//!
//! Mappings: `class`/`interface`/`enum`/`trait`/`@interface` → `Type`
//! (distinguished by `type_kind`); `def name(...)` and typed methods →
//! `Function` (`HAS_METHOD` from the enclosing type); fields and `def` bindings →
//! `Constant`; `extends` → `EXTENDS`; `implements` → `IMPLEMENTS`; `import`
//! (incl. `import static`) → `IMPORTS` (+ `ExternalDependency`/`DEPENDS_ON`);
//! call sites → `CALLS`.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Groovy language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct GroovyFrontEnd;

impl LanguageFrontEnd for GroovyFrontEnd {
    fn name(&self) -> &'static str {
        "groovy"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["groovy", "gradle"]
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

/// Map a repo-relative Groovy path to its package path (dotted segments). The
/// conventional Gradle/Maven source roots (`src/main/groovy/`, `src/test/groovy/`)
/// and a bare `src/` root are stripped if present; the directory chain that
/// remains is the package, and the file stem contributes no segment (a Groovy
/// file is not itself a scope — its top-level types are). Build scripts at the
/// repo root (e.g. `build.gradle`) yield an empty package.
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = ["src/main/groovy/", "src/test/groovy/", "src/"]
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
            module_path_for("src/main/groovy/com/foo/Bar.groovy"),
            vec!["com", "foo"]
        );
        assert_eq!(
            module_path_for("src/test/groovy/com/foo/BarTest.groovy"),
            vec!["com", "foo"]
        );
        assert_eq!(module_path_for("com/foo/Bar.groovy"), vec!["com", "foo"]);
        assert_eq!(module_path_for("Bar.groovy"), Vec::<String>::new());
        assert_eq!(module_path_for("build.gradle"), Vec::<String>::new());
        assert_eq!(module_path_for("src/App.groovy"), Vec::<String>::new());
    }

    #[test]
    fn front_end_identity() {
        let fe = GroovyFrontEnd;
        assert_eq!(fe.name(), "groovy");
        assert_eq!(fe.extensions(), &["groovy", "gradle"]);
    }

    #[test]
    fn lossless_round_trip() {
        // A representative file exercising comments, annotations, generics, a
        // GString, a triple-quoted string, a slashy string, a trait, an enum, a
        // constructor, a typed method, and a `def` method.
        let src = "\
// banner comment
package com.example.app

import groovy.transform.CompileStatic
import static java.lang.Math.max

/** A 2D point. */
@CompileStatic
class Point implements Comparable<Point> {
    final int x
    int y
    static final String NOTE = '''
        a text
        block'''

    Point(int x, int y) {
        this.x = x
        this.y = y
    }

    @Override
    int compareTo(Point other) {
        return max(this.x, other.x)
    }

    def describe() { \"point(${x}, ${y})\" }

    interface Named { String name() }

    enum Kind { CARTESIAN, POLAR }
}

trait Greeter {
    String greet(String who) { \"hi $who\" }
}

def pattern = /[a-z]+/
def add(a, b) { a + b }
";
        let tree = parser::parse("Point.groovy", src);
        assert!(
            tree.is_lossless(),
            "Groovy front end must reconstruct source byte-for-byte"
        );

        // A Gradle build script (claimed by the same front end) round-trips too.
        let gradle = "\
plugins { id 'groovy' }

repositories {
    mavenCentral()
}

dependencies {
    implementation 'org.codehaus.groovy:groovy-all:3.0.9'
}

task hello {
    doLast { println \"Hello from ${project.name}\" }
}
";
        let gtree = parser::parse("build.gradle", gradle);
        assert!(
            gtree.is_lossless(),
            "Gradle script must reconstruct source byte-for-byte"
        );

        // And the lowering of the Groovy file stays deterministic.
        let file = crate::lang::frontend::SourceFile {
            rel_path: "src/main/groovy/com/example/app/Point.groovy".to_string(),
            module_path: GroovyFrontEnd.module_path("src/main/groovy/com/example/app/Point.groovy"),
            source: &tree.source,
            root: &tree.root,
        };
        let g1 = lower::lower("app", std::slice::from_ref(&file), &[]);
        let g2 = lower::lower("app", std::slice::from_ref(&file), &[]);
        assert_eq!(g1.to_jsonl(), g2.to_jsonl());
    }
}
