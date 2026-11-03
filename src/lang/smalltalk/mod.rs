//! Smalltalk front end: lossless lexer + CST parser + lowering, wired to the
//! shared IR through the [`LanguageFrontEnd`] seam.
//!
//! Smalltalk has no single canonical file syntax, so this front end handles the
//! two surfaces that appear in `.st` files — the classic **fileout / chunk**
//! format (`!Class methodsFor: 'cat'! … ! !`) and free-standing statements
//! (`Object subclass: #Foo …`, Pharo `Class >> sel [ … ]`). The lexer is purely
//! lossless and leans into Smalltalk's two famous traps: a **double-quoted**
//! `"…"` run is a **comment** (trivia) and a **single-quoted** `'…'` run is a
//! **string**. The lowering maps class definitions → `Type` (`type_kind: class`),
//! method definitions → `Function` (+`HAS_METHOD`, selector built from the
//! message pattern), `subclass:` → `EXTENDS`, and message sends → `CALLS`
//! resolved purely by selector (Smalltalk has no static receiver type). It is
//! deliberately coarse and honest; the mapping never fabricates targets.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Smalltalk language front end. Zero-sized: all state lives in the parse
/// trees and the lowering pass.
pub struct SmalltalkFrontEnd;

impl LanguageFrontEnd for SmalltalkFrontEnd {
    fn name(&self) -> &'static str {
        "smalltalk"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["st"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn module_path(&self, rel_path: &str) -> Vec<String> {
        module_path_for(rel_path)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once for selector resolution); merge it into the shared
        // graph the pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

/// Map a repo-relative `.st` path to a scope path: the directory segments plus the
/// file stem (with the `.st` suffix stripped).
fn module_path_for(rel: &str) -> Vec<String> {
    let mut parts: Vec<&str> = rel.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file.strip_suffix(".st").unwrap_or(file);
    let mut module: Vec<String> = parts.iter().map(|s| s.to_string()).collect();
    module.push(stem.to_string());
    module
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("Point.st"), vec!["Point"]);
        assert_eq!(
            module_path_for("kernel/Collection.st"),
            vec!["kernel", "Collection"]
        );
        assert_eq!(module_path_for("a/b/c.st"), vec!["a", "b", "c"]);
    }

    #[test]
    fn front_end_identity() {
        let fe = SmalltalkFrontEnd;
        assert_eq!(fe.name(), "smalltalk");
        assert_eq!(fe.extensions(), &["st"]);
    }

    #[test]
    fn parse_round_trips_byte_for_byte() {
        let fe = SmalltalkFrontEnd;
        let src = "\
\"A fileout chunk file.\"
Object subclass: #Stack
    instanceVariableNames: 'items'
    classVariableNames: ''
    package: 'Collections'!

!Stack methodsFor: 'adding'!
push: anObject
    \"Push onto the stack.\"
    items addLast: anObject.
    ^anObject!
pop
    ^items removeLast! !

Stack >> isEmpty [ ^items isEmpty ]
";
        let tree = fe.parse("Stack.st", src);
        assert!(
            tree.is_lossless(),
            "front-end parse must reconstruct source"
        );
    }
}
