//! Scala front end: lossless lexer + CST parser + lowering, wired to the shared
//! IR through the [`LanguageFrontEnd`] seam.
//!
//! Scala is brace-delimited (the dominant style) with light newline inference.
//! The lexer stays purely lossless — every byte is covered, nestable block
//! comments, all string forms (plain, triple-quoted, interpolated), char/symbol
//! literals, backtick identifiers, and operator-identifier runs are classified,
//! and anything else becomes an `error` token. The parser recognizes the
//! definition forms (`class`/`case class`/`trait`/`object`/`enum`, `def`,
//! `val`/`var`, `type`, `given`, `extension`), `package` and `import`/`export`
//! declarations, and captures bodies as nested statement blocks so members and
//! call sites are discoverable. The lowering maps `def`→`Function`, the
//! type-like forms→`Type` (with an apt `type_kind`), `val`/`var`/`given`→
//! `Constant`, `extends`→`EXTENDS` and `with`→`IMPLEMENTS`, and reuses the
//! deterministic scope-resolution ladder for `CALLS`.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Scala language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct ScalaFrontEnd;

impl LanguageFrontEnd for ScalaFrontEnd {
    fn name(&self) -> &'static str {
        "scala"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["scala", "sc"]
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

/// Map a repo-relative Scala path to a directory-based module path, used only as
/// a fallback when a file declares no `package`. Scala's authoritative scope is
/// the `package` declaration (handled in the lowering); this strips the standard
/// SBT/Maven source roots and uses the directory segments (the file stem does
/// *not* contribute a module segment — unlike Python, a Scala file name has no
/// package meaning).
fn module_path_for(rel: &str) -> Vec<String> {
    let mut rest = rel;
    for prefix in [
        "src/main/scala-3/",
        "src/main/scala-2/",
        "src/main/scala/",
        "src/test/scala/",
        "src/main/java/",
        "src/",
    ] {
        if let Some(s) = rest.strip_prefix(prefix) {
            rest = s;
            break;
        }
    }
    let mut parts: Vec<&str> = rest.split('/').collect();
    parts.pop(); // drop the file name
    parts
        .into_iter()
        .filter(|s| !s.is_empty())
        .map(|s| s.to_string())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::cst::ParseTree;

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("Foo.scala"), Vec::<String>::new());
        assert_eq!(module_path_for("a/b/C.scala"), vec!["a", "b"]);
        assert_eq!(
            module_path_for("src/main/scala/com/example/App.scala"),
            vec!["com", "example"]
        );
        assert_eq!(module_path_for("src/test/scala/x/Y.scala"), vec!["x"]);
        assert_eq!(module_path_for("script.sc"), Vec::<String>::new());
    }

    #[test]
    fn front_end_identity() {
        let fe = ScalaFrontEnd;
        assert_eq!(fe.name(), "scala");
        assert_eq!(fe.extensions(), &["scala", "sc"]);
    }

    /// Lossless round-trip on a representative Scala snippet exercising packages,
    /// imports with selectors, annotations, case classes, traits with `extends`/
    /// `with`, an `object` with a `main`, interpolated and triple-quoted strings,
    /// operator-named methods, symbol/char/backtick literals, and nested comments.
    #[test]
    fn lossless_round_trip() {
        let src = "\
package com.example.app

import scala.collection.mutable.{Map => MMap, Set}
import java.util._

/** Doc comment. /* nested */ */
@SerialVersionUID(1L)
sealed abstract class Shape extends Serializable {
  def area: Double
  def label: String = s\"shape with area ${area}\"
}

case class Circle(r: Double) extends Shape with Drawable {
  val pi = 3.14159
  def area: Double = pi * r * r
  def +(o: Circle): Circle = Circle(r + o.r)
  private val banner =
    \"\"\"multi
      |line \"quoted\" here\"\"\".stripMargin
}

object App {
  val tag = 'scalaTag
  val ch = 'x'
  val `weird name` = 42

  def main(args: Array[String]): Unit = {
    val c = Circle(2.0)
    println(c.area)
    println(c.label)
  }
}
";
        let tree: ParseTree = parser::parse("App.scala", src);
        assert!(
            tree.is_lossless(),
            "Scala CST must reconstruct the source byte-for-byte"
        );
        // The full byte coverage is the real contract; assert it explicitly too.
        let mut rebuilt = String::new();
        tree.root.reconstruct(&tree.source, &mut rebuilt);
        assert_eq!(rebuilt, src, "reconstruction must equal the source");
    }
}
