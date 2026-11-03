//! GraphQL (SDL — schema definition language) front end: lossless lexer + CST
//! parser + lowering, wired to the shared IR through the [`LanguageFrontEnd`]
//! seam.
//!
//! GraphQL is brace-delimited (object/interface/input/enum bodies and the schema
//! operation map are delimiter groups, as in Rust and Go), but its top-level
//! definitions carry no statement terminator — they are delimited by the next
//! definition keyword. The parser captures headers precisely and bodies as
//! balanced token groups; the lowering maps `type`/`interface`/`input`/`enum`/
//! `union`/`scalar` → `Type` (a `type_kind` property keeps each honest),
//! `implements` → `IMPLEMENTS`, and root `Query`/`Mutation`/`Subscription` fields
//! that take arguments → `Function` (+`HAS_METHOD`). SDL is declarative, so **no
//! `CALLS` are ever fabricated**.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The GraphQL language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct GraphQlFrontEnd;

impl LanguageFrontEnd for GraphQlFrontEnd {
    fn name(&self) -> &'static str {
        "graphql"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["graphql", "gql"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-schema lowering produces a self-contained sub-graph (it needs
        // every file at once so type references resolve across files); merge it
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
        let fe = GraphQlFrontEnd;
        assert_eq!(fe.name(), "graphql");
        assert_eq!(fe.extensions(), &["graphql", "gql"]);
    }

    #[test]
    fn end_to_end_lossless_round_trip() {
        // A representative schema exercising descriptions, block strings,
        // comments, commas, an interface + implements, directives, a union, an
        // enum, an input, a scalar, a root type with argument fields, an
        // extension, and the schema definition — must reconstruct byte-for-byte.
        let src = "\
\"\"\"Root query.\"\"\"
type Query {
  # canonical greeting
  hello: String
  user(id: ID!, verbose: Boolean = false): User
}

interface Node { id: ID! }

type User implements Node @key(fields: \"id\") {
  id: ID!
  name: String!
  posts(first: Int = 10): [Post!]!
}

type Post { id: ID!, title: String! }

input NewUser { name: String!, age: Int = 0 }

enum Role { ADMIN, USER GUEST }

union SearchResult = User | Post

scalar DateTime @specifiedBy(url: \"https://example.com/dt\")

directive @key(fields: String!) repeatable on OBJECT | INTERFACE

extend type Query { health: Boolean }

schema { query: Query }
";
        let fe = GraphQlFrontEnd;
        let tree = fe.parse("schema.graphql", src);
        assert!(
            tree.is_lossless(),
            "GraphQL front end must round-trip source byte-for-byte"
        );
        assert!(
            tree.diagnostics.is_empty(),
            "a well-formed schema should parse without diagnostics"
        );
    }
}
