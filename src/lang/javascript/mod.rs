//! JavaScript front end: lossless lexer + CST parser + lowering, wired to the
//! shared IR through the [`LanguageFrontEnd`] seam.
//!
//! JavaScript is brace-delimited (not whitespace-significant) but has no
//! mandatory semicolons. The lexer stays purely lossless — every byte is covered,
//! line terminators are emitted as `newline` trivia and other whitespace as
//! `whitespace` trivia — and the parser recovers ASI statement boundaries from
//! those newline tokens. Template literals and regex/division ambiguity are
//! handled in the lexer without ever dropping bytes. The lowering maps
//! `function`→`Function`, `class`→`Type` (`type_kind: class`), methods→`Function`
//! with `HAS_METHOD`, top-level `const`/`let`/`var`→`Constant`, `extends`→`EXTENDS`,
//! and `import`/`export … from`→`IMPORTS` (+ `ExternalDependency`/`DEPENDS_ON`),
//! reusing a deterministic scope-resolution ladder for `CALLS`.
//!
//! `.jsx` files lex and parse losslessly; JSX element markup is captured as
//! ordinary tokens (a breadth gap — JSX structure is not modeled — but never a
//! lossiness or correctness lie).

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The JavaScript language front end. Zero-sized: all state lives in the parse
/// trees and the lowering pass.
pub struct JavaScriptFrontEnd;

impl LanguageFrontEnd for JavaScriptFrontEnd {
    fn name(&self) -> &'static str {
        "javascript"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["js", "jsx", "mjs", "cjs"]
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

/// Map a repo-relative JavaScript path to its module path. `index.{js,…}`
/// contributes the directory but no extra segment (it is the directory's entry
/// point); every other file stem does. A `src/` layout root is stripped.
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = rel.strip_prefix("src/").unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file
        .strip_suffix(".jsx")
        .or_else(|| file.strip_suffix(".mjs"))
        .or_else(|| file.strip_suffix(".cjs"))
        .or_else(|| file.strip_suffix(".js"))
        .unwrap_or(file);
    let mut module: Vec<String> = parts.iter().map(|s| s.to_string()).collect();
    match stem {
        "index" => {} // directory entry point: contributes no extra segment
        other => module.push(other.to_string()),
    }
    module
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("foo.js"), vec!["foo"]);
        assert_eq!(module_path_for("a/b/c.mjs"), vec!["a", "b", "c"]);
        assert_eq!(module_path_for("a/b/index.js"), vec!["a", "b"]);
        assert_eq!(module_path_for("src/pkg/mod.jsx"), vec!["pkg", "mod"]);
        assert_eq!(module_path_for("lib/util.cjs"), vec!["lib", "util"]);
    }

    #[test]
    fn front_end_identity() {
        let fe = JavaScriptFrontEnd;
        assert_eq!(fe.name(), "javascript");
        assert_eq!(fe.extensions(), &["js", "jsx", "mjs", "cjs"]);
    }

    /// The substrate-level guarantee: a representative module reconstructs its
    /// source byte-for-byte from the parsed CST leaves.
    #[test]
    fn lossless_round_trip() {
        let src = "\
#!/usr/bin/env node
// Trail tracker demo module
import { readFile } from 'fs/promises';
import Logger, { Level } from '@scope/logger';

export const TAU = 6.283_185n;
let pattern = /^\\/(\\w+)\\/$/gi;

@instrument
export default class Tracker extends EventEmitter {
  #points = [];

  constructor(name = `tracker-${Date.now()}`) {
    super();
    this.name = name;
  }

  async record(p) {
    this.#points.push(p);
    return await this.flush(p);
  }

  static *range(n) { for (let i = 0; i < n; i++) yield i; }
}

function helper(x) {
  const y = x / 2;       // division, not regex
  return Tracker.range(y);
}

const t = helper(10);
";
        let tree = parser::parse("tracker.js", src);
        assert!(
            tree.is_lossless(),
            "JavaScript CST must reconstruct source byte-for-byte"
        );
        let mut rebuilt = String::new();
        tree.root.reconstruct(&tree.source, &mut rebuilt);
        assert_eq!(rebuilt, src, "byte-for-byte round trip");
    }
}
