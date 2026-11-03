//! GraphQL (SDL) parser producing the language-neutral lossless CST.
//!
//! Strategy (honest, breadth-growable, mirroring the Rust parser): definition
//! *headers* are parsed precisely — we always know a type's keyword, its name,
//! its `implements`/directives header, and (for object/interface/input/enum)
//! its brace body. The body is captured as a balanced delimiter group
//! (`Brace`/`Paren`/`Bracket`), which is perfectly lossless; the field-level
//! facts (type references, root-field functions) are extracted from those real
//! token groups in the lowering pass, never invented.
//!
//! GraphQL SDL has no statement terminator: definitions are delimited by the
//! next top-level definition keyword (or a description string that introduces
//! one). [`GraphQlParser::at_def_boundary`] encodes that, and header regions
//! stop there. Anything unrecognized becomes an `ErrorItem` node that still
//! contains its exact source tokens, plus a `Diagnostic`.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::graphql::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views / the lowering interpret these.
pub mod node {
    pub const DOCUMENT: &str = "Document";
    pub const SCHEMA: &str = "SchemaDef";
    pub const SCALAR: &str = "ScalarDef";
    pub const OBJECT: &str = "ObjectDef";
    pub const INTERFACE: &str = "InterfaceDef";
    pub const INPUT: &str = "InputDef";
    pub const ENUM: &str = "EnumDef";
    pub const UNION: &str = "UnionDef";
    pub const DIRECTIVE: &str = "DirectiveDef";
    /// `extend <def>` — wraps the inner definition node it extends.
    pub const EXTENSION: &str = "Extension";
    pub const ERROR_ITEM: &str = "ErrorItem";

    pub const NAME: &str = "Name";
    /// Everything between the name and the body / next definition: an
    /// `implements` clause, directives, union members (`= A | B`), directive
    /// arguments and locations.
    pub const HEADER: &str = "Header";
    /// A brace body: object/interface/input fields, enum values, schema
    /// operation map.
    pub const FIELDS: &str = "Fields";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Top-level keywords that begin a definition. Used as the boundary that ends a
/// header region (SDL has no `;` terminator).
const DEF_KEYWORDS: &[&str] = &[
    "schema",
    "scalar",
    "type",
    "interface",
    "input",
    "enum",
    "union",
    "directive",
    "extend",
];

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remaining group iteratively. Mirrors the Rust parser's guard: a
/// `catch_unwind` cannot catch a stack overflow, so this is the real defense
/// against hostile deeply-nested delimiters.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = GraphQlParser {
        src: source,
        toks,
        i: 0,
        diags: Vec::new(),
        depth: 0,
    };
    let root = p.parse_document();
    ParseTree {
        source_id: SourceId::from_path(path),
        path: path.to_string(),
        source: source.to_string(),
        root,
        diagnostics: p.diags,
    }
}

struct GraphQlParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    depth: usize,
}

impl<'s> GraphQlParser<'s> {
    // --- cursor primitives --------------------------------------------------

    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
        }
    }

    fn peek_kind(&self) -> Option<&'static str> {
        let mut j = self.i;
        while j < self.toks.len() && self.toks[j].trivia {
            j += 1;
        }
        self.toks.get(j).map(|t| t.kind)
    }

    fn peek_text(&self) -> Option<&str> {
        let mut j = self.i;
        while j < self.toks.len() && self.toks[j].trivia {
            j += 1;
        }
        self.toks.get(j).map(|t| t.span.text(self.src))
    }

    fn at(&self, s: &str) -> bool {
        self.peek_text() == Some(s)
    }

    fn at_name(&self) -> bool {
        self.peek_kind() == Some(tk::NAME)
    }

    fn at_string(&self) -> bool {
        matches!(self.peek_kind(), Some(k) if k == tk::STRING || k == tk::BLOCK_STRING)
    }

    fn at_open(&self) -> bool {
        self.at("(") || self.at("[") || self.at("{")
    }

    /// At the start of a new top-level definition? A description string also
    /// begins one (it is always immediately followed by a definition keyword),
    /// so it ends the preceding header region.
    fn at_def_boundary(&self) -> bool {
        if self.at_string() {
            return true;
        }
        matches!(self.peek_text(), Some(t) if DEF_KEYWORDS.contains(&t))
    }

    fn cur_offset(&self) -> usize {
        self.toks
            .get(self.i)
            .map(|t| t.span.start as usize)
            .unwrap_or(self.src.len())
    }

    fn make_node(&self, kind: &'static str, children: Vec<Child>) -> Node {
        let span =
            children_span(&children).unwrap_or_else(|| ByteSpan::empty_at(self.cur_offset()));
        Node::new(kind, span, children)
    }

    // --- top level ----------------------------------------------------------

    fn parse_document(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            let before = self.i;
            let def = self.parse_definition();
            c.push(Child::Node(def));
            // Progress guard: every definition path consumes at least one
            // significant token, but a non-advancing iteration would loop
            // forever. Force one token of progress if it ever happens.
            if self.i == before {
                let mut ec = Vec::new();
                self.ws(&mut ec);
                self.eat(&mut ec);
                if !ec.is_empty() {
                    let n = self.make_node(node::ERROR_ITEM, ec);
                    c.push(Child::Node(n));
                } else {
                    break;
                }
            }
        }
        self.make_node(node::DOCUMENT, c)
    }

    fn parse_definition(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        // Leading description: a string or block string introducing the def.
        if self.at_string() {
            self.eat(&mut c);
        }
        self.ws(&mut c);
        if self.at("extend") {
            return self.finish_extension(c);
        }
        self.dispatch_def(c)
    }

    fn dispatch_def(&mut self, c: Vec<Child>) -> Node {
        if self.at("schema") {
            self.finish_braced(c, node::SCHEMA, false)
        } else if self.at("scalar") {
            self.finish_flat(c, node::SCALAR)
        } else if self.at("type") {
            self.finish_braced(c, node::OBJECT, true)
        } else if self.at("interface") {
            self.finish_braced(c, node::INTERFACE, true)
        } else if self.at("input") {
            self.finish_braced(c, node::INPUT, true)
        } else if self.at("enum") {
            self.finish_braced(c, node::ENUM, true)
        } else if self.at("union") {
            self.finish_flat(c, node::UNION)
        } else if self.at("directive") {
            self.finish_directive(c)
        } else {
            self.finish_error_item(c)
        }
    }

    fn finish_extension(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // extend
        self.ws(&mut c);
        let inner = self.dispatch_def(Vec::new());
        c.push(Child::Node(inner));
        self.make_node(node::EXTENSION, c)
    }

    /// A definition with an optional brace body: object/interface/input/enum and
    /// `schema`. `has_name` is false only for `schema`, which is anonymous.
    fn finish_braced(&mut self, mut c: Vec<Child>, kind: &'static str, has_name: bool) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // keyword
        if has_name {
            self.ws(&mut c);
            if self.at_name() {
                let n = self.name_node();
                c.push(Child::Node(n));
            }
        }
        if let Some(h) = self.collect_region(node::HEADER, &["{"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_delimited(Some(node::FIELDS));
            c.push(Child::Node(b));
        }
        self.make_node(kind, c)
    }

    /// A definition with no brace body: `scalar` and `union`. The header carries
    /// directives (scalar) or `= A | B` members (union).
    fn finish_flat(&mut self, mut c: Vec<Child>, kind: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // keyword
        self.ws(&mut c);
        if self.at_name() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(h) = self.collect_region(node::HEADER, &[]) {
            c.push(Child::Node(h));
        }
        self.make_node(kind, c)
    }

    /// `directive @Name(args) [repeatable] on LOC | LOC`. The name is preceded by
    /// `@`; arguments and locations are captured in the header.
    fn finish_directive(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // directive
        self.ws(&mut c);
        if self.at("@") {
            self.eat(&mut c); // @
        }
        self.ws(&mut c);
        if self.at_name() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(h) = self.collect_region(node::HEADER, &[]) {
            c.push(Child::Node(h));
        }
        self.make_node(node::DIRECTIVE, c)
    }

    fn finish_error_item(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        if self.at_open() {
            let g = self.parse_delimited(None);
            c.push(Child::Node(g));
        } else {
            // Consume exactly one significant token to guarantee progress.
            self.eat(&mut c);
        }
        self.diags.push(Diagnostic {
            code: "graphql.unrecognized_definition",
            message: "token(s) not recognized as a GraphQL definition".to_string(),
            span: children_span(&c).unwrap_or_else(|| ByteSpan::empty_at(self.cur_offset())),
        });
        self.make_node(node::ERROR_ITEM, c)
    }

    // --- shared helpers -----------------------------------------------------

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.eat(&mut c); // the name token (cursor is at it after caller ws)
        self.make_node(node::NAME, c)
    }

    /// Collect tokens (descending into balanced groups) until a stop token, a
    /// definition boundary, or EOF — all at delimiter depth 0.
    fn collect_region(&mut self, label: &'static str, stops: &[&str]) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            if self.peek_kind().is_none() {
                break;
            }
            if stops.iter().any(|s| self.at(s)) {
                break;
            }
            if self.at_def_boundary() {
                break;
            }
            if self.at_open() {
                self.ws(&mut c);
                let inner = self.parse_delimited(None);
                c.push(Child::Node(inner));
            } else {
                self.ws(&mut c);
                self.eat(&mut c);
            }
        }
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(label, c))
        }
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`.
    fn parse_delimited(&mut self, label_override: Option<&'static str>) -> Node {
        let mut g = Vec::new();
        self.ws(&mut g);
        let (close, default_label) = if self.at("(") {
            (")", node::PAREN)
        } else if self.at("[") {
            ("]", node::BRACKET)
        } else if self.at("{") {
            ("}", node::BRACE)
        } else {
            // Defensive: not actually at an opener.
            return self.make_node(label_override.unwrap_or(node::ERROR_ITEM), g);
        };
        let label = label_override.unwrap_or(default_label);
        self.eat(&mut g); // opener
        loop {
            self.ws(&mut g);
            if self.peek_kind().is_none() {
                break; // unterminated; still lossless
            }
            if self.at(close) {
                self.eat(&mut g);
                break;
            }
            if self.at_open() {
                if self.depth < MAX_DEPTH {
                    self.depth += 1;
                    let inner = self.parse_delimited(None);
                    self.depth -= 1;
                    g.push(Child::Node(inner));
                } else {
                    // Depth cap: flatten the nested group rather than recursing.
                    self.eat(&mut g); // opener
                    self.consume_balanced_flat(&mut g);
                    self.note_depth_limit();
                }
            } else {
                self.eat(&mut g);
            }
        }
        self.make_node(label, g)
    }

    /// Iteratively consume a balanced delimiter run (the opener already eaten),
    /// appending every token as a flat leaf. Used at the depth cap so arbitrarily
    /// deep nesting is handled without further recursion.
    fn consume_balanced_flat(&mut self, out: &mut Vec<Child>) {
        let mut balance: i32 = 1;
        while balance > 0 {
            self.ws(out);
            if self.peek_kind().is_none() {
                break;
            }
            if self.at("(") || self.at("[") || self.at("{") {
                balance += 1;
            } else if self.at(")") || self.at("]") || self.at("}") {
                balance -= 1;
            }
            self.eat(out);
        }
    }

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "graphql.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; group flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }
}

fn children_span(children: &[Child]) -> Option<ByteSpan> {
    let mut it = children.iter().map(child_span);
    let first = it.next()?;
    Some(it.fold(first, |a, b| a.merge(b)))
}

fn child_span(c: &Child) -> ByteSpan {
    match c {
        Child::Node(n) => n.span,
        Child::Token(t) => t.span,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_and_is_lossless() {
        let src = "\
\"\"\"
The root query type.
\"\"\"
type Query {
  # the canonical greeting
  hello: String
  user(id: ID!): User
}

interface Node {
  id: ID!
}

type User implements Node & Timestamped @key(fields: \"id\") {
  id: ID!
  name: String!
  posts(first: Int = 10): [Post!]!
}

input NewUser { name: String!, age: Int = 0 }

enum Role { ADMIN, USER GUEST }

union SearchResult = User | Post

scalar DateTime @specifiedBy(url: \"https://example.com\")

directive @auth(role: Role!) repeatable on FIELD_DEFINITION | OBJECT

extend type Query {
  health: Boolean
}

schema { query: Query }
";
        let tree = parse("schema.graphql", src);
        assert!(
            tree.is_lossless(),
            "tree must reconstruct source byte-for-byte"
        );
    }

    #[test]
    fn finds_top_level_definitions() {
        let src = "type A { x: Int } interface I { y: Int } input In { z: Int } \
                   enum E { A B } union U = A | B scalar S directive @d on FIELD \
                   schema { query: A } extend type A { w: Int }";
        let tree = parse("t.graphql", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::OBJECT));
        assert!(kinds.contains(&node::INTERFACE));
        assert!(kinds.contains(&node::INPUT));
        assert!(kinds.contains(&node::ENUM));
        assert!(kinds.contains(&node::UNION));
        assert!(kinds.contains(&node::SCALAR));
        assert!(kinds.contains(&node::DIRECTIVE));
        assert!(kinds.contains(&node::SCHEMA));
        assert!(kinds.contains(&node::EXTENSION));
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        // Far deeper than MAX_DEPTH; must not stack-overflow and stay lossless.
        let depth = 10_000;
        let src = format!(
            "type X {{ f: Int @x(v: {}{}) }}",
            "[".repeat(depth),
            "]".repeat(depth)
        );
        let tree = parse("deep.graphql", &src);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics
                .iter()
                .any(|d| d.code == "graphql.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }

    #[test]
    fn unrecognized_top_level_is_error_item() {
        let tree = parse("bad.graphql", "%%% type A { x: Int }");
        assert!(tree.is_lossless());
        assert!(tree.root.child_nodes().any(|n| n.kind == node::ERROR_ITEM));
        assert!(tree.root.child_nodes().any(|n| n.kind == node::OBJECT));
    }
}
