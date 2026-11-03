//! WebAssembly text format parser producing the language-neutral lossless CST.
//!
//! WAT source is fully-parenthesized s-expressions, so the parser is deliberately
//! coarse: it models the single balanced delimiter form — the parenthesized list
//! `(…)` — as nested `SExpr` groups, and leaves every atom (keyword, identifier,
//! number, string) as a flat leaf token in its enclosing form. This is perfectly
//! lossless and is all the lowering needs: section forms (`module`, `func`,
//! `import`, …) are recognised by the first keyword of a list, and that keyword
//! is a real token on the tree.
//!
//! Anything unbalanced or unexpected still lands in the tree as its exact tokens
//! (a stray closer becomes a leaf), so the result always round-trips
//! byte-for-byte. Recursion is depth-guarded at [`MAX_DEPTH`] against hostile
//! nesting — a `catch_unwind` cannot catch a stack overflow, so the guard is the
//! real defense; beyond the cap a group is consumed as a flat balanced run.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::wasm::lexer::{self, kind as tk, lex};

/// CST node-kind labels. The lowering interprets these.
pub mod node {
    pub const SOURCE: &str = "Source";
    /// A parenthesized s-expression list `(…)`.
    pub const SEXPR: &str = "SExpr";
}

/// Maximum structural nesting depth before the parser stops recursing and
/// consumes the remaining group iteratively as a flat balanced run. Mirrors the
/// Rust parser's guard exactly — s-expression nesting can be arbitrarily deep, and
/// a `catch_unwind` cannot catch a stack overflow.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = WasmParser {
        toks,
        i: 0,
        src: source,
        diags: Vec::new(),
        depth: 0,
    };
    let root = p.parse_source();
    ParseTree {
        source_id: SourceId::from_path(path),
        path: path.to_string(),
        source: source.to_string(),
        root,
        diagnostics: p.diags,
    }
}

struct WasmParser<'s> {
    toks: Vec<Token>,
    i: usize,
    src: &'s str,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> WasmParser<'s> {
    // --- cursor primitives --------------------------------------------------

    /// Append the current token (trivia or not) to `out` and advance.
    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading trivia tokens (whitespace, comments) into `out`.
    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
        }
    }

    /// Kind of the next significant (non-trivia) token.
    fn peek_kind(&self) -> Option<&'static str> {
        let mut j = self.i;
        while j < self.toks.len() && self.toks[j].trivia {
            j += 1;
        }
        self.toks.get(j).map(|t| t.kind)
    }

    fn at_open(&self) -> bool {
        matches!(self.peek_kind(), Some(k) if lexer::is_open_delim(k))
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

    fn parse_source(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            if self.at_open() {
                let g = self.parse_sexpr();
                c.push(Child::Node(g));
            } else {
                // An atom or stray token at the top level: keep it as a leaf.
                self.eat(&mut c);
            }
        }
        self.make_node(node::SOURCE, c)
    }

    /// Parse a balanced `(…)` group. The cursor is at (or before trivia preceding)
    /// the opener.
    fn parse_sexpr(&mut self) -> Node {
        let mut g = Vec::new();
        self.ws(&mut g);
        if self.peek_kind() != Some(tk::PAREN_OPEN) {
            return self.make_node(node::SEXPR, g); // defensive: not an opener
        }
        self.eat(&mut g); // opener
        loop {
            self.ws(&mut g);
            match self.peek_kind() {
                None => break, // unterminated; still lossless
                Some(k) if k == tk::PAREN_CLOSE => {
                    self.eat(&mut g); // matching closer
                    break;
                }
                _ if self.at_open() => {
                    if self.depth < MAX_DEPTH {
                        self.depth += 1;
                        let inner = self.parse_sexpr();
                        self.depth -= 1;
                        g.push(Child::Node(inner));
                    } else {
                        // Depth cap: flatten the nested group rather than recursing.
                        self.eat(&mut g); // opener
                        self.consume_balanced_flat(&mut g);
                        self.note_depth_limit();
                    }
                }
                // Any other token — an atom or stray byte — is kept as a leaf.
                _ => self.eat(&mut g),
            }
        }
        self.make_node(node::SEXPR, g)
    }

    /// Iteratively consume a balanced delimiter run (the opener already eaten),
    /// appending every token as a flat leaf. Used at the depth cap so arbitrarily
    /// deep nesting is handled without further recursion. On unbalanced input it
    /// stops at EOF.
    fn consume_balanced_flat(&mut self, out: &mut Vec<Child>) {
        let mut balance: i32 = 1;
        while balance > 0 {
            self.ws(out);
            match self.peek_kind() {
                None => break,
                Some(k) if lexer::is_open_delim(k) => balance += 1,
                Some(k) if lexer::is_close_delim(k) => balance -= 1,
                _ => {}
            }
            self.eat(out);
        }
    }

    /// Record that the depth cap flattened structure — reported, never silent.
    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "wasm.depth_limit",
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
;; a small module
(module $demo
  (import \"env\" \"log\" (func $log (param i32)))
  (type $unary (func (param i32) (result i32)))
  (global $answer i32 (i32.const 42))
  (func $add (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.add
    (call $log))
  (export \"add\" (func $add)))
";
        let tree = parse("demo.wat", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn groups_are_balanced() {
        let src = "(module (func (param i32)))";
        let tree = parse("t.wat", src);
        let module = tree
            .root
            .children_of(node::SEXPR)
            .next()
            .expect("a top-level sexpr");
        assert!(module.child(node::SEXPR).is_some(), "func nested in module");
        let func = module.child(node::SEXPR).unwrap();
        assert!(func.child(node::SEXPR).is_some(), "param nested in func");
    }

    #[test]
    fn finds_top_level_forms() {
        let src = "(module) (func) (global)";
        let tree = parse("t.wat", src);
        let count = tree.root.children_of(node::SEXPR).count();
        assert_eq!(count, 3, "three top-level s-expressions");
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "(func $f (param i32)", // unterminated list
            "(module",              // unterminated module
            "(func (; λ ☃ ;) $f)",  // multi-byte comment bytes
            "",                     // empty file
            ")) ((",                // stray closers / openers
        ] {
            let tree = parse("edge.wat", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        // Far deeper than MAX_DEPTH; must not stack-overflow and must stay lossless.
        let depth = 10_000;
        let src = format!("{}{}", "(".repeat(depth), ")".repeat(depth));
        let tree = parse("deep.wat", &src);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics
                .iter()
                .any(|d| d.code == "wasm.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }
}
