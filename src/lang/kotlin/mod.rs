//! Kotlin front end: lossless lexer + CST parser + lowering, wired to the shared
//! IR through the [`LanguageFrontEnd`] seam.
//!
//! Kotlin is brace-delimited (so the parser follows the Rust front end's
//! header-precise / body-as-token-tree strategy) but uses newline-based statement
//! inference (so, like the Python front end, the lexer emits `newline` as a
//! significant token and the parser uses it to terminate imports, expression
//! bodies, property initializers, and abstract members). The lowering maps
//! `fun`→`Function`, `class`/`interface`/`object`/`enum class`/`typealias`→`Type`
//! (distinguished by `type_kind`), top-level `val`/`var`→`Constant`, the
//! supertype list→`EXTENDS` (superclass) / `IMPLEMENTS` (interface), and reuses a
//! deterministic scope-resolution ladder for `CALLS`.
//!
//! Module scope comes from the in-file `package` declaration (Kotlin's source of
//! truth), not the directory layout, so [`module_path`](KotlinFrontEnd::module_path)
//! is only a path-based fallback used when a file omits its `package`.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Kotlin language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct KotlinFrontEnd;

impl LanguageFrontEnd for KotlinFrontEnd {
    fn name(&self) -> &'static str {
        "kotlin"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["kt", "kts"]
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

/// Path-based module fallback for a `.kt`/`.kts` file, used only when the file has
/// no `package` declaration. Strips the conventional `src/main/kotlin`,
/// `src/test/kotlin`, or bare `src` source roots, then takes the directory
/// segments (the file stem is dropped — Kotlin files do not name a module).
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = rel
        .strip_prefix("src/main/kotlin/")
        .or_else(|| rel.strip_prefix("src/test/kotlin/"))
        .or_else(|| rel.strip_prefix("src/"))
        .unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    parts.pop(); // drop the file name
    parts.iter().map(|s| s.to_string()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("Main.kt"), Vec::<String>::new());
        assert_eq!(module_path_for("a/b/C.kt"), vec!["a", "b"]);
        assert_eq!(
            module_path_for("src/main/kotlin/com/acme/App.kt"),
            vec!["com", "acme"]
        );
        assert_eq!(module_path_for("src/util/Helper.kts"), vec!["util"]);
    }

    #[test]
    fn front_end_identity() {
        let fe = KotlinFrontEnd;
        assert_eq!(fe.name(), "kotlin");
        assert_eq!(fe.extensions(), &["kt", "kts"]);
    }
}
