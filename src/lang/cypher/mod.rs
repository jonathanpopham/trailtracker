//! Cypher (Neo4j query language) front end: lossless lexer + CST parser +
//! lowering, wired to the shared IR through the [`LanguageFrontEnd`] seam.
//!
//! Cypher is a graph **query** language, not a definition language, so it maps
//! **sparsely** to the shared ontology, and this front end is deliberately honest
//! about that rather than fabricating definitions. The one guarantee that matters
//! most here is losslessness: the lexer covers Cypher's surface in full (both
//! string forms, backtick-quoted names with the doubled-backtick escape, numbers,
//! parameters `$x`, `//` and `/* */` comments, and the pattern punctuators), the
//! parser splits statements and captures the pattern delimiters as balanced
//! token-tree groups, and the lowering reads only what a query honestly states:
//! node labels and relationship types → [`Type`] references (`USES_TYPE`), and
//! procedure / function calls → [`ExternalDependency`] targets (`CALLS`). A query
//! that defines nothing correctly yields just a `File` node plus its references.
//! See [`lower`] for the full mapping and the list of intentional punts.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Cypher language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct CypherFrontEnd;

impl LanguageFrontEnd for CypherFrontEnd {
    fn name(&self) -> &'static str {
        "cypher"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["cypher", "cql"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph; merge it
        // into the shared graph the pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn front_end_identity() {
        let fe = CypherFrontEnd;
        assert_eq!(fe.name(), "cypher");
        assert_eq!(fe.extensions(), &["cypher", "cql"]);
    }

    #[test]
    fn lossless_round_trip_on_representative_snippet() {
        // A representative slice of real Cypher: comments, both string forms, a
        // backtick-quoted label, parameters, a property map, a variable-length
        // relationship with an alternation, an aggregation function, a procedure
        // CALL … YIELD, and multiple `;`-separated statements.
        let src = "\
// load and relate people
LOAD CSV WITH HEADERS FROM 'file:///people.csv' AS row
MERGE (p:Person {id: row.id, name: row.name});

MATCH (a:Person {name: $name})-[r:KNOWS|`FOLLOWS`*1..3]->(b:`Cool Person`)
WHERE a.age >= 18 AND b.name STARTS WITH \"A\"
WITH a, count(b) AS friends
CALL db.labels() YIELD label
RETURN a.name, friends, label
ORDER BY friends DESC
LIMIT 10;
";
        let fe = CypherFrontEnd;
        let tree = fe.parse("queries.cypher", src);
        assert!(
            tree.is_lossless(),
            "the Cypher front end must reconstruct source byte-for-byte"
        );
        assert_eq!(tree.error_byte_ratio(), 0.0, "no bytes should be errors");

        // And the lowering produces a non-trivial, deterministic graph.
        let file = crate::lang::frontend::SourceFile {
            rel_path: "queries.cypher".to_string(),
            module_path: vec![],
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

        let again = {
            let file = crate::lang::frontend::SourceFile {
                rel_path: "queries.cypher".to_string(),
                module_path: vec![],
                source: &tree.source,
                root: &tree.root,
            };
            let input = LoweredInput {
                package: "demo",
                manifest_deps: &[],
                files: vec![file],
            };
            let mut g2 = Graph::new();
            fe.lower(&input, &mut g2);
            g2
        };
        assert_eq!(
            g.to_jsonl(),
            again.to_jsonl(),
            "lowering must be deterministic"
        );
    }
}
