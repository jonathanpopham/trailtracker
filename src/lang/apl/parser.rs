//! APL parser producing the language-neutral lossless CST.
//!
//! APL is terse, line-oriented, and largely anonymous, so the parse is honest and
//! shallow: the source file is segmented into **statements** (split on newlines
//! and the `⋄` diamond) and **del-defined functions** (`∇ header … ∇`). Balanced
//! bracket groups (`(…)`, `[…]`, `{…}`) are captured as real, recursively-parsed
//! token trees — the dfn brace `{…}` is exactly such a group — which is perfectly
//! lossless and gives the lowering concrete structure to read.
//!
//! No graph facts are invented here: names, dfns, and call sites are extracted
//! from these real token trees in the lowering pass. Everything the parser sees
//! is retained; there is no token it can fail to place.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::apl::lexer::{kind as tk, lex};

/// CST node-kind labels.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    /// A `∇ … ∇` tradfn.
    pub const DEL_FN: &str = "DelFn";
    /// The header line of a tradfn (everything up to the first newline).
    pub const HEADER: &str = "Header";
    /// The statement list inside a tradfn.
    pub const BODY: &str = "Body";
    /// One logical statement (a line, or a `⋄`-separated segment).
    pub const STMT: &str = "Stmt";
    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remaining group iteratively. Mirrors the Rust front end: a `catch_unwind`
/// cannot catch a stack overflow, so this guard is the real defense against
/// hostile delimiter nesting.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = AplParser {
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

struct AplParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    depth: usize,
}

impl<'s> AplParser<'s> {
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

    fn cur(&self) -> Option<&Token> {
        self.toks.get(self.i)
    }

    fn cur_text(&self) -> &str {
        self.cur().map(|t| t.span.text(self.src)).unwrap_or("")
    }

    /// Kind of the next significant (non-trivia) token.
    fn peek_kind(&self) -> Option<&'static str> {
        let mut j = self.i;
        while j < self.toks.len() && self.toks[j].trivia {
            j += 1;
        }
        self.toks.get(j).map(|t| t.kind)
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

    fn parse_source_file(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            let before = self.i;
            let item = if self.peek_kind() == Some(tk::DEL) {
                self.parse_del_fn()
            } else {
                self.parse_stmt()
            };
            c.push(Child::Node(item));
            // Main-loop progress guard: every item must consume at least one
            // token; if not, force one token through so the loop cannot spin.
            if self.i == before {
                self.eat(&mut c);
            }
        }
        self.make_node(node::SOURCE_FILE, c)
    }

    /// Parse `∇ header … body … ∇`.
    fn parse_del_fn(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // opening ∇
        if let Some(h) = self.collect_header() {
            c.push(Child::Node(h));
        }
        let body = self.parse_del_body();
        c.push(Child::Node(body));
        self.ws(&mut c);
        if self.peek_kind() == Some(tk::DEL) {
            self.eat(&mut c); // closing ∇
        }
        self.make_node(node::DEL_FN, c)
    }

    /// Collect the tradfn header: everything up to (not including) the first
    /// newline, the diamond `⋄`, a closing `∇`, or EOF. Descends into groups.
    fn collect_header(&mut self) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            let before = self.i;
            let Some(t) = self.cur() else { break };
            if t.kind == tk::DEL {
                break;
            }
            if t.kind == tk::WHITESPACE && t.span.text(self.src).contains('\n') {
                break;
            }
            if t.trivia {
                self.eat(&mut c);
            } else {
                let text = t.span.text(self.src);
                if text == "⋄" {
                    break;
                }
                if is_open(text) {
                    let g = self.parse_delimited();
                    c.push(Child::Node(g));
                } else {
                    self.eat(&mut c);
                }
            }
            if self.i == before {
                break;
            }
        }
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(node::HEADER, c))
        }
    }

    /// Parse statements until a closing `∇` or EOF.
    fn parse_del_body(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            match self.peek_kind() {
                // Closing ∇ (handled by the caller) or EOF ends the body.
                None => break,
                Some(k) if k == tk::DEL => break,
                Some(_) => {
                    let before = self.i;
                    let s = self.parse_stmt();
                    c.push(Child::Node(s));
                    if self.i == before {
                        self.eat(&mut c);
                    }
                }
            }
        }
        self.make_node(node::BODY, c)
    }

    /// Parse one statement: tokens up to a newline, a `⋄` (consumed), a `∇`
    /// (left for the caller), or EOF. Descends into balanced groups.
    fn parse_stmt(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            let before = self.i;
            let Some(t) = self.cur() else { break };
            if t.kind == tk::DEL {
                break;
            }
            if t.kind == tk::WHITESPACE && t.span.text(self.src).contains('\n') {
                break;
            }
            if t.trivia {
                self.eat(&mut c); // intra-line whitespace / comment
            } else {
                let text = t.span.text(self.src);
                if text == "⋄" {
                    self.eat(&mut c); // diamond terminates this statement
                    break;
                }
                if is_open(text) {
                    let g = self.parse_delimited();
                    c.push(Child::Node(g));
                } else {
                    self.eat(&mut c);
                }
            }
            if self.i == before {
                break;
            }
        }
        self.make_node(node::STMT, c)
    }

    /// Parse a balanced delimiter group, depth-guarded. The cursor is at the
    /// opening `(`, `[`, or `{`.
    fn parse_delimited(&mut self) -> Node {
        let (close, label) = match self.cur_text() {
            "(" => (")", node::PAREN),
            "[" => ("]", node::BRACKET),
            "{" => ("}", node::BRACE),
            _ => {
                // Defensive: not actually at an opener.
                let mut g = Vec::new();
                self.eat(&mut g);
                return self.make_node(node::PAREN, g);
            }
        };
        let mut g = Vec::new();
        self.eat(&mut g); // opener
        loop {
            let before = self.i;
            let Some(t) = self.cur() else { break };
            if t.trivia {
                self.eat(&mut g);
                continue;
            }
            let text = t.span.text(self.src);
            if text == close {
                self.eat(&mut g); // closer
                break;
            }
            if is_open(text) {
                if self.depth < MAX_DEPTH {
                    self.depth += 1;
                    let inner = self.parse_delimited();
                    self.depth -= 1;
                    g.push(Child::Node(inner));
                } else {
                    // Depth cap: flatten the nested group rather than recurse.
                    self.eat(&mut g); // opener
                    self.consume_balanced_flat(&mut g);
                    self.note_depth_limit();
                }
            } else {
                self.eat(&mut g);
            }
            if self.i == before {
                break; // unterminated; still lossless
            }
        }
        self.make_node(label, g)
    }

    /// Iteratively consume a balanced delimiter run (opener already eaten),
    /// appending every token flat. Used at the depth cap so arbitrarily deep
    /// nesting never recurses further. Counts all delimiter kinds uniformly.
    fn consume_balanced_flat(&mut self, out: &mut Vec<Child>) {
        let mut balance: i32 = 1;
        while balance > 0 {
            let before = self.i;
            let Some(t) = self.cur() else { break };
            if !t.trivia {
                let text = t.span.text(self.src);
                if is_open(text) {
                    balance += 1;
                } else if is_close(text) {
                    balance -= 1;
                }
            }
            self.eat(out);
            if self.i == before {
                break;
            }
        }
    }

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "apl.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; group flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }
}

fn is_open(text: &str) -> bool {
    matches!(text, "(" | "[" | "{")
}

fn is_close(text: &str) -> bool {
    matches!(text, ")" | "]" | "}")
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
⍝ statistics
⎕IO←0
avg←{(+/⍵)÷≢⍵}

∇ R←fac N
 R←×/⍳N
∇

mean←avg 1 2 3 4
";
        let tree = parse("stats.apl", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
        assert_eq!(tree.error_byte_ratio(), 0.0, "no bytes should be errors");
    }

    #[test]
    fn finds_del_fn_and_statements() {
        let src = "x←1 ⋄ y←2\n∇ foo\n  x←3\n∇\n";
        let tree = parse("t.apl", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::DEL_FN), "should find the tradfn");
        assert!(kinds.contains(&node::STMT), "should find statements");
        // The diamond split two statements out of one line.
        let stmt_count = tree
            .root
            .child_nodes()
            .filter(|n| n.kind == node::STMT)
            .count();
        assert!(stmt_count >= 2, "⋄ should split statements");
    }

    #[test]
    fn dfn_brace_is_a_group() {
        let src = "f←{⍺+⍵}";
        let tree = parse("t.apl", src);
        let has_brace = tree.root.walk().any(|n| n.kind == node::BRACE);
        assert!(has_brace, "dfn body should be a Brace group");
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let depth = 10_000;
        let src = format!("x←{}{}", "(".repeat(depth), ")".repeat(depth));
        let tree = parse("deep.apl", &src);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics.iter().any(|d| d.code == "apl.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }
}
