//! Cypher parser producing the language-neutral lossless CST.
//!
//! Strategy (honest, and appropriate for a *query* language): Cypher files are a
//! sequence of statements separated by `;`. There is nothing to "define" the way
//! a programming language defines functions and types, so the parser stays thin:
//! it splits the token stream into [`node::STATEMENT`] runs and captures the
//! pattern delimiters `(...)`, `[...]`, `{...}` as balanced **token-tree** groups
//! ([`node::PAREN`] / [`node::BRACKET`] / [`node::BRACE`]). Those groups are
//! exactly where the graph-meaningful facts live (node labels in parens,
//! relationship types in brackets, property maps in braces), and the lowering
//! reads them from the real tokens — never invented.
//!
//! Everything is lossless: trivia is retained, unbalanced or unterminated input
//! still round-trips, and the delimiter recursion is depth-guarded at
//! [`MAX_DEPTH`] (a `catch_unwind` cannot catch a stack overflow, so the guard is
//! the real defense).

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::cypher::lexer::lex;

/// CST node-kind labels.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    /// A single query statement (tokens up to and including a top-level `;`, or
    /// to EOF for the final unterminated statement).
    pub const STATEMENT: &str = "Statement";
    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum delimiter-nesting depth before the parser stops recursing and
/// consumes the remaining group iteratively. Mirrors the Rust front end so the
/// whole substrate shares one bound. Protects against stack overflow on hostile
/// inputs; far beyond any realistic query.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = CypherParser {
        src: source,
        toks,
        i: 0,
        diags: Vec::new(),
        depth: 0,
    };
    let root = p.parse_source_file();
    ParseTree {
        source_id: SourceId::from_path(path),
        path: path.to_string(),
        source: source.to_string(),
        root,
        diagnostics: p.diags,
    }
}

struct CypherParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> CypherParser<'s> {
    // --- cursor primitives --------------------------------------------------

    /// Append the current token (trivia or not) to `out` and advance.
    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading trivia tokens into `out`.
    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
        }
    }

    /// Kind of the next significant token.
    fn peek_kind(&self) -> Option<&'static str> {
        let mut j = self.i;
        while j < self.toks.len() && self.toks[j].trivia {
            j += 1;
        }
        self.toks.get(j).map(|t| t.kind)
    }

    /// True if the next significant token's text equals `s`.
    fn at(&self, s: &str) -> bool {
        let mut j = self.i;
        while j < self.toks.len() && self.toks[j].trivia {
            j += 1;
        }
        self.toks
            .get(j)
            .map(|t| t.span.text(self.src) == s)
            .unwrap_or(false)
    }

    fn at_open(&self) -> bool {
        self.at("(") || self.at("[") || self.at("{")
    }

    fn cur_offset(&self) -> usize {
        self.toks
            .get(self.i)
            .map(|t| t.span.start as usize)
            .unwrap_or_else(|| self.toks.last().map(|t| t.span.end as usize).unwrap_or(0))
    }

    fn make_node(&self, kind: &'static str, children: Vec<Child>) -> Node {
        let span =
            children_span(&children).unwrap_or_else(|| ByteSpan::empty_at(self.cur_offset()));
        Node::new(kind, span, children)
    }

    // --- grammar ------------------------------------------------------------

    fn parse_source_file(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            let stmt = self.parse_statement();
            c.push(Child::Node(stmt));
        }
        self.make_node(node::SOURCE_FILE, c)
    }

    /// Collect tokens (descending into balanced groups) until a top-level `;`
    /// (consumed into the statement) or EOF. Always consumes at least one
    /// significant token so the caller's loop makes progress.
    fn parse_statement(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            if self.at(";") {
                self.eat(&mut c);
                break;
            }
            if self.at_open() {
                let g = self.parse_delimited();
                c.push(Child::Node(g));
            } else {
                self.eat(&mut c);
            }
        }
        self.make_node(node::STATEMENT, c)
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`. Cursor is
    /// at (or before trivia preceding) the opener.
    fn parse_delimited(&mut self) -> Node {
        let mut g = Vec::new();
        self.ws(&mut g);
        let (close, label) = if self.at("(") {
            (")", node::PAREN)
        } else if self.at("[") {
            ("]", node::BRACKET)
        } else if self.at("{") {
            ("}", node::BRACE)
        } else {
            // Defensive: not actually at an opener.
            return self.make_node(node::PAREN, g);
        };
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
                    let inner = self.parse_delimited();
                    self.depth -= 1;
                    g.push(Child::Node(inner));
                } else {
                    // Depth cap: flatten the nested group into this one rather
                    // than recursing. Lossless; protects against stack overflow.
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
            code: "cypher.depth_limit",
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

/// Re-export so callers can name the keyword helper via the parser module too.
pub use super::lexer::is_keyword;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_and_is_lossless() {
        let src = "\
// find people who know each other
MATCH (a:Person {name: $name})-[:KNOWS]->(b:Person)
WHERE a.age > 30
RETURN a.name, count(b) AS friends
ORDER BY friends DESC;

CREATE (c:Company {name: 'Acme'});
";
        let tree = parse("test.cypher", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
        assert_eq!(tree.error_byte_ratio(), 0.0, "no bytes should be errors");
    }

    #[test]
    fn splits_statements_on_semicolons() {
        let src = "MATCH (n) RETURN n; CREATE (m); MERGE (k)";
        let tree = parse("q.cql", src);
        let stmts = tree
            .root
            .child_nodes()
            .filter(|n| n.kind == node::STATEMENT)
            .count();
        assert_eq!(stmts, 3, "three statements expected");
    }

    #[test]
    fn captures_delimiter_groups() {
        let src = "MATCH (n:Label {p: [1, 2, 3]}) RETURN n";
        let tree = parse("q.cypher", src);
        let has_paren = tree.root.walk().any(|n| n.kind == node::PAREN);
        let has_brace = tree.root.walk().any(|n| n.kind == node::BRACE);
        let has_bracket = tree.root.walk().any(|n| n.kind == node::BRACKET);
        assert!(has_paren && has_brace && has_bracket);
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        // Far deeper than MAX_DEPTH; must not stack-overflow and must stay lossless.
        let depth = 10_000;
        let src = format!("RETURN {}{}", "(".repeat(depth), ")".repeat(depth));
        let tree = parse("deep.cypher", &src);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics
                .iter()
                .any(|d| d.code == "cypher.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }

    #[test]
    fn empty_input_is_lossless() {
        let tree = parse("empty.cypher", "");
        assert!(tree.is_lossless());
        assert_eq!(tree.root.kind, node::SOURCE_FILE);
    }
}
