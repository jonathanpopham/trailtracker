//! Smalltalk parser producing the language-neutral lossless CST.
//!
//! Smalltalk has no single canonical surface syntax. This parser handles the two
//! that matter in `.st` files, coarsely but losslessly:
//!
//! 1. **Fileout / chunk format.** Chunks are separated by `!`. A method category
//!    group is `!Class methodsFor: 'cat'!  m1 ! m2 ! !` — a *header* chunk, then
//!    one chunk per method body, terminated by an empty (`! !`) chunk. We model
//!    this as a [`node::METHODS_CHUNK`] holding a [`node::HEADER`] and a sequence
//!    of [`node::METHOD`] nodes, each split into a [`node::SELECTOR`] (the message
//!    pattern) and a [`node::BODY`] (the temps + statements).
//! 2. **Free-standing statements.** Everything not introduced by a leading `!` —
//!    class definitions (`Object subclass: #Foo …`), Pharo-style method
//!    definitions (`Class >> selector [ … ]`), and top-level do-its — is captured
//!    as a [`node::STATEMENT`] terminated by a top-level `.` or `!`. The lowering
//!    inspects these for `subclass:` and `>>`; the CST stays flat and honest.
//!
//! Method bodies and any bracketed/parenthesised regions are captured as balanced
//! token-tree groups ([`node::PAREN`] / [`node::BRACKET`] / [`node::BRACE`]),
//! which are perfectly lossless. Graph facts are extracted from these real tokens
//! in the lowering pass — never invented. The parser is depth-guarded at
//! [`MAX_DEPTH`]: beyond the cap it consumes nested groups as a flat balanced run
//! (a `catch_unwind` cannot catch a stack overflow, so the guard is the real
//! defense).

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::smalltalk::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views (the lowering) interpret these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    /// A `!Class methodsFor: …!  …  ! !` method-category group.
    pub const METHODS_CHUNK: &str = "MethodsChunk";
    /// The header expression of a methods chunk (`Class methodsFor: 'cat'`).
    pub const HEADER: &str = "Header";
    /// One method definition within a methods chunk.
    pub const METHOD: &str = "Method";
    /// A method's message pattern (`at: i put: v`, `+ other`, or `size`).
    pub const SELECTOR: &str = "Selector";
    /// A method's temps + statements.
    pub const BODY: &str = "Body";
    /// A free-standing top-level statement (class def, `>>` method, or do-it).
    pub const STATEMENT: &str = "Statement";
    pub const ERROR_ITEM: &str = "ErrorItem";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum nesting depth before the parser stops recursing into delimiter groups
/// and consumes the remainder as a flat balanced run. Mirrors the Rust parser's
/// cap so behaviour is uniform across front ends.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = StParser {
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

struct StParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    depth: usize,
}

impl<'s> StParser<'s> {
    // --- cursor primitives --------------------------------------------------

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

    fn peek_kind(&self) -> Option<&'static str> {
        let mut j = self.i;
        while j < self.toks.len() && self.toks[j].trivia {
            j += 1;
        }
        self.toks.get(j).map(|t| t.kind)
    }

    fn at_kind(&self, k: &str) -> bool {
        self.peek_kind() == Some(k)
    }

    fn at_open(&self) -> bool {
        matches!(
            self.peek_kind(),
            Some(tk::LPAREN) | Some(tk::LBRACKET) | Some(tk::LBRACE)
        )
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
            match self.peek_kind() {
                None => break,
                Some(tk::BANG) => {
                    let chunk = self.parse_methods_chunk();
                    c.push(Child::Node(chunk));
                }
                Some(_) => {
                    let stmt = self.parse_statement();
                    c.push(Child::Node(stmt));
                }
            }
        }
        self.make_node(node::SOURCE_FILE, c)
    }

    /// Parse a `!Header!  m1 ! m2 ! !` method-category group. Cursor is at the
    /// opening `!`.
    fn parse_methods_chunk(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // opening !
        if let Some(h) = self.collect_region(node::HEADER, &[tk::BANG]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at_kind(tk::BANG) {
            self.eat(&mut c); // close-header !
        }
        // Method chunks until the empty (`! !`) chunk or EOF.
        loop {
            self.ws(&mut c);
            match self.peek_kind() {
                None => break,
                Some(tk::BANG) => {
                    // Empty chunk -> the closing `!` of `! !`.
                    self.eat(&mut c);
                    break;
                }
                Some(_) => {
                    let m = self.parse_one_method();
                    c.push(Child::Node(m));
                }
            }
        }
        self.make_node(node::METHODS_CHUNK, c)
    }

    /// One method body chunk (cursor at the first significant token; not a `!`).
    /// Consumes through the trailing `!` if present.
    fn parse_one_method(&mut self) -> Node {
        let mut c = Vec::new();
        let sel = self.parse_message_pattern();
        c.push(Child::Node(sel));
        if let Some(b) = self.collect_region(node::BODY, &[tk::BANG]) {
            c.push(Child::Node(b));
        }
        self.ws(&mut c);
        if self.at_kind(tk::BANG) {
            self.eat(&mut c); // chunk terminator
        }
        self.make_node(node::METHOD, c)
    }

    /// Parse a method message pattern: a keyword pattern (`at: i put: v`), a
    /// binary pattern (`+ other`), or a unary selector (`size`). Stops before the
    /// method body. Always returns a [`node::SELECTOR`] (possibly empty).
    fn parse_message_pattern(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        match self.peek_kind() {
            Some(tk::KEYWORD) => {
                while self.at_kind(tk::KEYWORD) {
                    self.eat(&mut c); // keyword token
                    self.ws(&mut c);
                    if self.at_kind(tk::IDENT) {
                        self.eat(&mut c); // argument name
                    }
                    self.ws(&mut c);
                }
            }
            Some(tk::BINARY) => {
                self.eat(&mut c); // binary selector
                self.ws(&mut c);
                if self.at_kind(tk::IDENT) {
                    self.eat(&mut c); // argument name
                }
            }
            Some(tk::IDENT) => {
                self.eat(&mut c); // unary selector
            }
            _ => {}
        }
        self.make_node(node::SELECTOR, c)
    }

    /// A free-standing statement: collect (descending into balanced groups) until
    /// a top-level `.` or `!`, consuming that terminator.
    fn parse_statement(&mut self) -> Node {
        let mut c = Vec::new();
        let mut saw_significant = false;
        loop {
            self.ws(&mut c);
            match self.peek_kind() {
                None => break,
                Some(tk::PERIOD) | Some(tk::BANG) => {
                    self.eat(&mut c); // terminator stays with the statement
                    break;
                }
                Some(_) if self.at_open() => {
                    let g = self.parse_delimited(None);
                    c.push(Child::Node(g));
                    saw_significant = true;
                }
                Some(_) => {
                    self.eat(&mut c);
                    saw_significant = true;
                }
            }
        }
        let _ = saw_significant;
        self.make_node(node::STATEMENT, c)
    }

    // --- shared helpers -----------------------------------------------------

    /// Collect tokens (descending into balanced groups) until a significant stop
    /// token at delimiter depth 0. The stop token is **not** consumed.
    fn collect_region(&mut self, label: &'static str, stops: &[&str]) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            match self.peek_kind() {
                None => break,
                Some(k) if stops.contains(&k) => break,
                Some(_) if self.at_open() => {
                    self.ws(&mut c);
                    let g = self.parse_delimited(None);
                    c.push(Child::Node(g));
                }
                Some(_) => {
                    self.ws(&mut c);
                    self.eat(&mut c);
                }
            }
        }
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(label, c))
        }
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`. Cursor is at
    /// (or before trivia preceding) the opener.
    fn parse_delimited(&mut self, label_override: Option<&'static str>) -> Node {
        let mut g = Vec::new();
        self.ws(&mut g);
        let (close, default_label) = match self.peek_kind() {
            Some(tk::LPAREN) => (tk::RPAREN, node::PAREN),
            Some(tk::LBRACKET) => (tk::RBRACKET, node::BRACKET),
            Some(tk::LBRACE) => (tk::RBRACE, node::BRACE),
            _ => return self.make_node(label_override.unwrap_or(node::ERROR_ITEM), g),
        };
        let label = label_override.unwrap_or(default_label);
        self.eat(&mut g); // opener
        loop {
            self.ws(&mut g);
            match self.peek_kind() {
                None => break, // unterminated; still lossless
                Some(k) if k == close => {
                    self.eat(&mut g);
                    break;
                }
                Some(_) if self.at_open() => {
                    if self.depth < MAX_DEPTH {
                        self.depth += 1;
                        let inner = self.parse_delimited(None);
                        self.depth -= 1;
                        g.push(Child::Node(inner));
                    } else {
                        // Depth cap: flatten the nested group rather than recurse.
                        self.eat(&mut g); // opener
                        self.consume_balanced_flat(&mut g);
                        self.note_depth_limit();
                    }
                }
                Some(_) => self.eat(&mut g),
            }
        }
        self.make_node(label, g)
    }

    /// Iteratively consume a balanced delimiter run (opener already eaten),
    /// appending every token as a flat leaf. Used at the depth cap so arbitrarily
    /// deep nesting is handled without further recursion.
    fn consume_balanced_flat(&mut self, out: &mut Vec<Child>) {
        let mut balance: i32 = 1;
        while balance > 0 {
            self.ws(out);
            match self.peek_kind() {
                None => break,
                Some(tk::LPAREN) | Some(tk::LBRACKET) | Some(tk::LBRACE) => {
                    balance += 1;
                    self.eat(out);
                }
                Some(tk::RPAREN) | Some(tk::RBRACKET) | Some(tk::RBRACE) => {
                    balance -= 1;
                    self.eat(out);
                }
                Some(_) => self.eat(out),
            }
        }
    }

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "smalltalk.depth_limit",
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
Object subclass: #Counter
    instanceVariableNames: 'count'
    classVariableNames: ''
    package: 'Demo'!

!Counter methodsFor: 'accessing'!
count
    ^count!
increment
    count := count + 1.
    ^self! !

!Counter class methodsFor: 'instance creation'!
new
    ^super new init! !
";
        let tree = parse("Counter.st", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_methods_chunk_and_methods() {
        let src = "!Counter methodsFor: 'a'!\ncount\n\t^count!\nreset\n\tcount := 0! !\n";
        let tree = parse("c.st", src);
        let chunk = tree
            .root
            .child(node::METHODS_CHUNK)
            .expect("a methods chunk");
        let methods: Vec<&Node> = chunk.children_of(node::METHOD).collect();
        assert_eq!(methods.len(), 2, "two methods");
        // Each method has a selector and body.
        assert!(methods[0].child(node::SELECTOR).is_some());
        assert!(methods[0].child(node::BODY).is_some());
    }

    #[test]
    fn class_definition_is_a_statement() {
        let src = "Object subclass: #Point instanceVariableNames: 'x y'!";
        let tree = parse("p.st", src);
        assert!(tree.root.child(node::STATEMENT).is_some());
    }

    #[test]
    fn comment_does_not_break_chunking() {
        let src = "!C methodsFor: 'x'!\nm\n\t\"a ! in a comment\"\n\t^1! !\n";
        let tree = parse("c.st", src);
        assert!(tree.is_lossless());
        let chunk = tree.root.child(node::METHODS_CHUNK).unwrap();
        assert_eq!(chunk.children_of(node::METHOD).count(), 1);
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let depth = 10_000;
        let src = format!("foo bar: {}{}.", "[".repeat(depth), "]".repeat(depth));
        let tree = parse("deep.st", &src);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics
                .iter()
                .any(|d| d.code == "smalltalk.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }
}
