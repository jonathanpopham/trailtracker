//! Forth parser producing the language-neutral lossless CST.
//!
//! Forth is almost flat: a source file is a stream of whitespace-delimited words.
//! The one structural shape worth lifting is the colon definition — `: name … ;`
//! — which the lowering turns into a `Function`. The other shape with real
//! nesting is the control-flow words (`if … then`, `begin … repeat`,
//! `do … loop`, `case … endcase`, …); these are captured as recursive
//! `Control` groups so the parser has a genuine recursion to depth-guard.
//!
//! Strategy (honest, coarse): definition *headers* (the name) are parsed
//! precisely; bodies are collected as token runs with control-flow groups nested
//! inside. Everything else at the top level is kept as flat tokens — the
//! lowering reads constants, includes, and call sites off these real tokens,
//! never inventing them. Nothing is dropped: every token (including trivia) lands
//! in the tree, so it round-trips byte-for-byte.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::forth::lexer::lex;

/// CST node-kind labels. The lowering interprets these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    /// A `: name … ;` colon definition.
    pub const DEFINITION: &str = "Definition";
    /// The defined word's name.
    pub const NAME: &str = "Name";
    /// A definition's body (between the name and `;`).
    pub const BODY: &str = "Body";
    /// A nested control-flow structure (`if…then`, `begin…repeat`, …).
    pub const CONTROL: &str = "Control";
}

/// Maximum nesting depth before the parser stops recursing into control
/// structures and consumes the remainder as a flat balanced run. Mirrors the
/// Rust parser's guard: a `catch_unwind` cannot catch a stack overflow, so this
/// is the real defense against hostile nesting (`if if if … then then then`).
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = ForthParser {
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

struct ForthParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current control-structure recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> ForthParser<'s> {
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

    /// Lowercased text of the next significant token (Forth is case-insensitive).
    fn peek_lower(&self) -> Option<String> {
        let mut j = self.i;
        while j < self.toks.len() && self.toks[j].trivia {
            j += 1;
        }
        self.toks
            .get(j)
            .map(|t| t.span.text(self.src).to_ascii_lowercase())
    }

    fn at(&self, s: &str) -> bool {
        self.peek_lower().as_deref() == Some(s)
    }

    fn at_significant(&self) -> bool {
        self.peek_kind().is_some()
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
            if !self.at_significant() {
                break;
            }
            if self.at(":") {
                let d = self.parse_definition();
                c.push(Child::Node(d));
            } else if self.peek_lower().as_deref().map(is_opener).unwrap_or(false) {
                let ctrl = self.parse_control();
                c.push(Child::Node(ctrl));
            } else {
                // Any other top-level word is kept as a flat token. Consuming one
                // significant token guarantees loop progress.
                self.eat(&mut c);
            }
        }
        self.make_node(node::SOURCE_FILE, c)
    }

    // --- definitions --------------------------------------------------------

    /// `: name body ;` — the name is the first significant token after `:`; the
    /// body runs to the matching `;` (or EOF, recorded as a diagnostic).
    fn parse_definition(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // ':'
        self.ws(&mut c);
        if self.at_significant() && !self.at(";") {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(body) = self.parse_body() {
            c.push(Child::Node(body));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        } else {
            self.diags.push(Diagnostic {
                code: "forth.unterminated_definition",
                message: "colon definition reached end of input without ';'".to_string(),
                span: children_span(&c).unwrap_or_else(|| ByteSpan::empty_at(self.cur_offset())),
            });
        }
        self.make_node(node::DEFINITION, c)
    }

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.eat(&mut c); // the name token (cursor is at it after caller ws)
        self.make_node(node::NAME, c)
    }

    /// Collect a definition body: tokens up to (but not consuming) the `;`
    /// terminator, recursing into control structures so nesting stays first-class.
    fn parse_body(&mut self) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            match self.peek_lower() {
                None => break,
                Some(t) if t == ";" => break,
                Some(t) if is_opener(&t) => {
                    let ctrl = self.parse_control();
                    c.push(Child::Node(ctrl));
                }
                Some(_) => self.eat(&mut c),
            }
        }
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(node::BODY, c))
        }
    }

    // --- control structures -------------------------------------------------

    /// Parse one control structure, cursor at the opener. Recurses on nested
    /// openers; closes on the first balancing closer word. At [`MAX_DEPTH`] it
    /// switches to a flat, iterative consume so arbitrarily deep nesting cannot
    /// overflow the stack.
    fn parse_control(&mut self) -> Node {
        if self.depth >= MAX_DEPTH {
            let mut c = Vec::new();
            self.ws(&mut c);
            self.eat(&mut c); // opener
            self.consume_control_flat(&mut c);
            self.note_depth_limit();
            return self.make_node(node::CONTROL, c);
        }
        self.depth += 1;
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // opener
        loop {
            self.ws(&mut c);
            match self.peek_lower() {
                None => break,
                // A `;` terminates the enclosing definition; never swallow it.
                Some(t) if t == ";" => break,
                Some(t) if is_closer(&t) => {
                    self.eat(&mut c); // closer
                    break;
                }
                Some(t) if is_opener(&t) => {
                    let inner = self.parse_control();
                    c.push(Child::Node(inner));
                }
                Some(_) => self.eat(&mut c),
            }
        }
        let n = self.make_node(node::CONTROL, c);
        self.depth -= 1;
        n
    }

    /// Iteratively consume a balanced control run (opener already eaten),
    /// counting opener/closer words. Used at the depth cap to avoid recursion.
    fn consume_control_flat(&mut self, out: &mut Vec<Child>) {
        let mut balance: i32 = 1;
        loop {
            self.ws(out);
            match self.peek_lower() {
                None => break,
                Some(t) if t == ";" => break,
                Some(t) if is_opener(&t) => {
                    balance += 1;
                    self.eat(out);
                }
                Some(t) if is_closer(&t) => {
                    balance -= 1;
                    self.eat(out);
                    if balance <= 0 {
                        break;
                    }
                }
                Some(_) => self.eat(out),
            }
        }
    }

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "forth.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; group flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }
}

/// Control-flow words that open a nestable structure.
pub fn is_opener(lower: &str) -> bool {
    matches!(lower, "if" | "begin" | "do" | "?do" | "case" | "of")
}

/// Control-flow words that close a structure. Matching is by balance count, not
/// by opener/closer pairing — a coarse but lossless approximation of Forth's
/// control flow.
pub fn is_closer(lower: &str) -> bool {
    matches!(
        lower,
        "then" | "until" | "again" | "repeat" | "loop" | "+loop" | "endof" | "endcase"
    )
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
\\ a small vocabulary
42 constant answer
variable counter

: square ( n -- n^2 ) dup * ;

: classify ( n -- )
    dup 0 < if .\" negative\" else .\" non-negative\" then drop ;

: countdown ( n -- )
    begin dup . 1 - dup 0 = until drop ;

include extra.fth
square
";
        let tree = parse("test.fth", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_definitions_and_names() {
        let src = ": foo 1 ; : bar foo ;";
        let tree = parse("t.fth", src);
        let defs: Vec<&Node> = tree
            .root
            .child_nodes()
            .filter(|n| n.kind == node::DEFINITION)
            .collect();
        assert_eq!(defs.len(), 2);
        let names: Vec<String> = defs
            .iter()
            .filter_map(|d| d.child(node::NAME))
            .filter_map(|n| n.tokens().next())
            .map(|t| t.span.text(src).to_string())
            .collect();
        assert_eq!(names, vec!["foo", "bar"]);
    }

    #[test]
    fn empty_definition_has_no_name() {
        let src = ": ;";
        let tree = parse("t.fth", src);
        let def = tree
            .root
            .child_nodes()
            .find(|n| n.kind == node::DEFINITION)
            .expect("a definition");
        assert!(def.child(node::NAME).is_none());
        assert!(tree.is_lossless());
    }

    #[test]
    fn nested_control_is_first_class() {
        let src = ": f if begin again then ;";
        let tree = parse("t.fth", src);
        assert!(tree.is_lossless());
        let has_control = tree.root.walk().any(|n| n.kind == node::CONTROL);
        assert!(has_control, "control structures should be Control nodes");
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        // Far deeper than MAX_DEPTH; must not stack-overflow and must round-trip.
        let depth = 10_000;
        let src = format!(": deep {}{} ;", "if ".repeat(depth), "then ".repeat(depth));
        let tree = parse("deep.fth", &src);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics
                .iter()
                .any(|d| d.code == "forth.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }
}
