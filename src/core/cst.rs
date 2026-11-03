//! Language-neutral, lossless concrete syntax tree.
//!
//! This is the architectural heart of TrailTracker: one uniform tree shape that
//! every language front end (Rust, C#, manifests) produces. It is **lossless** —
//! every byte of source, including whitespace, comments, and unparsed regions,
//! is present as a leaf token. Concatenating the leaves in order reconstructs
//! the original source exactly (verified by round-trip tests).
//!
//! Typed views (`is fn`, `is struct`, …) are thin interpretations layered on
//! top of `Node::kind`; the tree itself stays untyped so it can hold any
//! language and so downstream passes can prune to graph views without ever
//! losing source-level information.

use crate::core::json::Json;
use crate::core::span::{ByteSpan, LineIndex, SourceId};

/// A leaf token. `kind` is a language-supplied label (e.g. `"kw_fn"`,
/// `"ident"`, `"whitespace"`); `trivia` marks tokens the parser skips for
/// structure but must retain for losslessness.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Token {
    pub kind: &'static str,
    pub span: ByteSpan,
    pub trivia: bool,
}

/// A node or token slot in the tree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Child {
    Node(Node),
    Token(Token),
}

/// An interior node. `kind` is an open `&'static str` label so the tree is
/// uniform across languages and trivially JSON-encodable.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Node {
    pub kind: &'static str,
    pub span: ByteSpan,
    pub children: Vec<Child>,
}

impl Node {
    pub fn new(kind: &'static str, span: ByteSpan, children: Vec<Child>) -> Node {
        Node {
            kind,
            span,
            children,
        }
    }

    /// Direct child nodes (skips tokens). Used by typed views and lowering.
    pub fn child_nodes(&self) -> impl Iterator<Item = &Node> {
        self.children.iter().filter_map(|c| match c {
            Child::Node(n) => Some(n),
            Child::Token(_) => None,
        })
    }

    /// Direct child nodes of a given kind.
    pub fn children_of<'a>(&'a self, kind: &'a str) -> impl Iterator<Item = &'a Node> + 'a {
        self.child_nodes().filter(move |n| n.kind == kind)
    }

    /// First direct child node of a given kind.
    pub fn child(&self, kind: &str) -> Option<&Node> {
        self.child_nodes().find(|n| n.kind == kind)
    }

    /// First direct child token of a given kind.
    pub fn token(&self, kind: &str) -> Option<&Token> {
        self.children.iter().find_map(|c| match c {
            Child::Token(t) if t.kind == kind => Some(t),
            _ => None,
        })
    }

    /// All non-trivia child tokens.
    pub fn tokens(&self) -> impl Iterator<Item = &Token> {
        self.children.iter().filter_map(|c| match c {
            Child::Token(t) if !t.trivia => Some(t),
            _ => None,
        })
    }

    /// Walk every node in the subtree (pre-order, includes self).
    pub fn walk(&self) -> NodeWalk<'_> {
        NodeWalk { stack: vec![self] }
    }

    /// Append each leaf token's source text to `out`, in order. Concatenating
    /// across the whole tree reproduces the original source.
    pub fn reconstruct(&self, source: &str, out: &mut String) {
        for child in &self.children {
            match child {
                Child::Node(n) => n.reconstruct(source, out),
                Child::Token(t) => out.push_str(t.span.text(source)),
            }
        }
    }

    /// Count leaf tokens flagged with `kind == "error"` in the subtree.
    pub fn error_token_count(&self) -> usize {
        let mut n = 0;
        for child in &self.children {
            match child {
                Child::Node(node) => n += node.error_token_count(),
                Child::Token(t) if t.kind == "error" => n += 1,
                Child::Token(_) => {}
            }
        }
        n
    }
}

/// Pre-order iterator over interior nodes.
pub struct NodeWalk<'a> {
    stack: Vec<&'a Node>,
}

impl<'a> Iterator for NodeWalk<'a> {
    type Item = &'a Node;
    fn next(&mut self) -> Option<&'a Node> {
        let node = self.stack.pop()?;
        // Push children in reverse so iteration is left-to-right pre-order.
        for child in node.children.iter().rev() {
            if let Child::Node(n) = child {
                self.stack.push(n);
            }
        }
        Some(node)
    }
}

/// A parse diagnostic — an honest record that the parser saw something it could
/// not fully resolve. Diagnostics never silently drop input; the corresponding
/// bytes still live in the tree as `error` tokens / `Error` nodes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Diagnostic {
    pub code: &'static str,
    pub message: String,
    pub span: ByteSpan,
}

/// Result of parsing one source file.
pub struct ParseTree {
    pub source_id: SourceId,
    pub path: String,
    pub source: String,
    pub root: Node,
    pub diagnostics: Vec<Diagnostic>,
}

impl ParseTree {
    /// True if the tree reproduces the source byte-for-byte. The lossless
    /// guarantee that everything downstream relies on.
    pub fn is_lossless(&self) -> bool {
        let mut rebuilt = String::with_capacity(self.source.len());
        self.root.reconstruct(&self.source, &mut rebuilt);
        rebuilt == self.source
    }

    /// Fraction of source bytes that landed in `error` tokens. 0.0 means the
    /// grammar covered everything it was handed; reported, never hidden.
    pub fn error_byte_ratio(&self) -> f64 {
        if self.source.is_empty() {
            return 0.0;
        }
        let err_bytes = error_bytes(&self.root);
        err_bytes as f64 / self.source.len() as f64
    }

    /// Encode the tree to JSON with resolved line/column locations — useful for
    /// inspection and golden fixtures.
    pub fn to_json(&self) -> Json {
        let index = LineIndex::new(&self.source);
        Json::obj([
            ("source_id", Json::U64(self.source_id.0)),
            ("path", Json::str(self.path.clone())),
            ("lossless", Json::Bool(self.is_lossless())),
            ("tree", node_to_json(&self.root, &self.source, &index)),
        ])
    }
}

fn error_bytes(node: &Node) -> usize {
    let mut n = 0;
    for child in &node.children {
        match child {
            Child::Node(inner) => n += error_bytes(inner),
            Child::Token(t) if t.kind == "error" => n += t.span.len(),
            Child::Token(_) => {}
        }
    }
    n
}

fn node_to_json(node: &Node, source: &str, index: &LineIndex) -> Json {
    let start = index.line_col(node.span.start);
    let children: Vec<Json> = node
        .children
        .iter()
        .map(|c| match c {
            Child::Node(n) => node_to_json(n, source, index),
            Child::Token(t) => Json::obj([
                ("token", Json::str(t.kind)),
                ("text", Json::str(t.span.text(source))),
                ("trivia", Json::Bool(t.trivia)),
            ]),
        })
        .collect();
    Json::obj([
        ("node", Json::str(node.kind)),
        ("line", Json::U64(start.line as u64)),
        ("col", Json::U64(start.column as u64)),
        ("children", Json::Array(children)),
    ])
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tok(kind: &'static str, start: usize, end: usize, trivia: bool) -> Child {
        Child::Token(Token {
            kind,
            span: ByteSpan::new(start, end),
            trivia,
        })
    }

    #[test]
    fn round_trip_reconstructs_source() {
        let src = "fn x";
        let root = Node::new(
            "SourceFile",
            ByteSpan::new(0, 4),
            vec![
                tok("kw_fn", 0, 2, false),
                tok("whitespace", 2, 3, true),
                tok("ident", 3, 4, false),
            ],
        );
        let mut out = String::new();
        root.reconstruct(src, &mut out);
        assert_eq!(out, src);
    }
}
