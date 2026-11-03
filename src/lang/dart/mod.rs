//! Dart front end: lossless lexer + CST parser + lowering, wired to the shared
//! IR through the [`LanguageFrontEnd`] seam.
//!
//! Dart is brace-delimited like Java, so the parser follows the Java/Rust
//! strategy (precise headers, balanced token-tree bodies) while the lowering
//! follows the Java strategy (an object model with inheritance). The lowering
//! maps `class`/`mixin`/`enum`/`extension`/`typedef` → `Type` (distinguished by
//! a `type_kind`), functions/methods/getters/setters/constructors → `Function`
//! (`HAS_METHOD` from the enclosing type), fields/top-level variables/enum
//! constants → `Constant`, `extends` → `EXTENDS`, `with`/`implements` →
//! `IMPLEMENTS`, and `import`/`export`/`part` → `IMPORTS`, reusing a
//! deterministic scope-resolution ladder for `CALLS`.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Dart language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct DartFrontEnd;

impl LanguageFrontEnd for DartFrontEnd {
    fn name(&self) -> &'static str {
        "dart"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["dart"]
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

/// Map a repo-relative Dart path to its module path (directory segments). The
/// conventional Dart source roots (`lib/`, `bin/`, `test/`, `web/`, `example/`)
/// are stripped if present; the directory chain that remains is the module, and
/// the file stem contributes no segment (a Dart file is not itself a scope — its
/// top-level declarations are).
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = ["lib/", "bin/", "test/", "web/", "example/"]
        .iter()
        .find_map(|p| rel.strip_prefix(p))
        .unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    parts.pop(); // the file name itself contributes no module segment
    parts.iter().map(|s| s.to_string()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("lib/src/foo/bar.dart"), vec!["src", "foo"]);
        assert_eq!(module_path_for("test/unit/foo_test.dart"), vec!["unit"]);
        assert_eq!(module_path_for("bar.dart"), Vec::<String>::new());
        assert_eq!(module_path_for("lib/main.dart"), Vec::<String>::new());
        assert_eq!(module_path_for("test/foo_test.dart"), Vec::<String>::new());
    }

    #[test]
    fn front_end_identity() {
        let fe = DartFrontEnd;
        assert_eq!(fe.name(), "dart");
        assert_eq!(fe.extensions(), &["dart"]);
    }

    #[test]
    fn lossless_round_trip() {
        // A representative file exercising comments, doc comments, imports,
        // generics, annotations, an interpolated string, a triple-quoted string,
        // a constructor, a getter, an arrow body, a mixin, an enum, an extension,
        // and a typedef.
        let src = "\
// banner comment
library example;

import 'dart:math';
import 'package:meta/meta.dart';
import '../util.dart' as util show clamp hide noop;

/// A 2D point.
@immutable
abstract class Point<T extends num> implements Comparable<Point<T>> {
  final T x;
  T y;
  static const String note = '''
    a text
    block''';

  Point(this.x, this.y);
  Point.origin() : x = zero(), y = zero();

  @override
  int compareTo(Point<T> other) => '${x}'.length - other.hashCode;

  T get first => x;

  void describe() {
    print('point at ($x, ${y + 1})');
  }
}

mixin Loggable on Point {
  void log() => print('log');
}

enum Shape { circle, square, triangle }

extension Doubling on int {
  int get doubled => this * 2;
}

typedef Mapper = int Function(int);

void main() {
  final p = Point(1, 2);
  p.describe();
}
";
        let tree = parser::parse("point.dart", src);
        assert!(
            tree.is_lossless(),
            "Dart front end must reconstruct source byte-for-byte"
        );
        // And the lowering of it stays deterministic.
        let file = crate::lang::frontend::SourceFile {
            rel_path: "lib/point.dart".to_string(),
            module_path: DartFrontEnd.module_path("lib/point.dart"),
            source: &tree.source,
            root: &tree.root,
        };
        let g1 = lower::lower("example", std::slice::from_ref(&file), &[]);
        let g2 = lower::lower("example", std::slice::from_ref(&file), &[]);
        assert_eq!(g1.to_jsonl(), g2.to_jsonl());
    }
}
