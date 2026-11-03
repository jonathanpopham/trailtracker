//! Lossless WebAssembly text format (WAT / WAST) lexer.
//!
//! WAT is fully-parenthesized s-expressions: the reader sees only `(` / `)`
//! delimiters, string/number/keyword/identifier atoms, and two comment forms.
//! This lexer stays purely lossless, matching the contract of the Rust, Python,
//! and Clojure lexers:
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (whitespace, `;;` line comments, and `(; ;)` **nested** block
//!   comments) are emitted as `trivia` tokens, never discarded.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped (an unterminated string or block
//!   comment becomes an `error` token, mirroring the Clojure lexer).
//!
//! Progress guard: the main run loop records `pos` at the top of every iteration
//! and, if a (defensive) branch failed to advance, consumes a single char as an
//! `error` token. A non-advancing loop would spin forever and exhaust memory, so
//! this guard is load-bearing, not decoration.
//!
//! Coverage note (honest): the `keyword`/`number` split is decided by inspecting
//! the leading shape of an idchar run (`inf`/`nan` and digit-leading runs are
//! numbers, everything else is a keyword). This is a pragmatic classification,
//! not the full WAT numeric grammar — but it is not a correctness lie: every byte
//! still lands in the tree under its true span, so losslessness holds regardless.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Token kind labels, stored on the CST as `&'static str`.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const LINE_COMMENT: &str = "line_comment";
    pub const BLOCK_COMMENT: &str = "block_comment";
    pub const STRING: &str = "string_literal";
    pub const IDENTIFIER: &str = "identifier";
    pub const NUMBER: &str = "number_literal";
    pub const KEYWORD: &str = "keyword";
    pub const PAREN_OPEN: &str = "paren_open";
    pub const PAREN_CLOSE: &str = "paren_close";
    pub const ERROR: &str = "error";
}

/// True if `k` is an opening delimiter token kind.
pub fn is_open_delim(k: &str) -> bool {
    k == kind::PAREN_OPEN
}

/// True if `k` is a closing delimiter token kind.
pub fn is_close_delim(k: &str) -> bool {
    k == kind::PAREN_CLOSE
}

pub fn lex(source: &str) -> Vec<Token> {
    Lexer::new(source).run()
}

struct Lexer<'s> {
    src: &'s str,
    bytes: &'s [u8],
    pos: usize,
    tokens: Vec<Token>,
}

impl<'s> Lexer<'s> {
    fn new(src: &'s str) -> Self {
        Lexer {
            src,
            bytes: src.as_bytes(),
            pos: 0,
            tokens: Vec::new(),
        }
    }

    fn run(mut self) -> Vec<Token> {
        while self.pos < self.bytes.len() {
            let start = self.pos;
            let c = self.peek();
            match c {
                c if c.is_whitespace() => {
                    self.eat_while(|c| c.is_whitespace());
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                // `(;` opens a (nestable) block comment; a bare `(` is a paren.
                '(' if self.byte_at(1) == Some(b';') => self.block_comment(start),
                '(' => self.single(start, kind::PAREN_OPEN),
                ')' => self.single(start, kind::PAREN_CLOSE),
                // `;;` opens a line comment; a lone `;` is unclassifiable.
                ';' if self.byte_at(1) == Some(b';') => self.line_comment(start),
                ';' => {
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
                '"' => self.string(start),
                c if is_idchar(c) => self.name_or_number(start),
                _ => {
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }

            // Progress guard: if no branch advanced (a defensive impossibility),
            // consume one char as an error so the loop can never spin forever.
            if self.pos == start {
                self.bump();
                self.push(kind::ERROR, start, self.pos, false);
            }
        }
        self.tokens
    }

    // --- scanners -----------------------------------------------------------

    fn single(&mut self, start: usize, k: &'static str) {
        self.bump();
        self.push(k, start, self.pos, false);
    }

    fn line_comment(&mut self, start: usize) {
        let end = self.find_line_end(start);
        self.pos = end;
        self.push(kind::LINE_COMMENT, start, end, true);
    }

    /// `(; … ;)` block comment. WAT block comments **nest**, so a depth counter is
    /// tracked: `(;` increments, `;)` decrements. A terminated comment is trivia;
    /// an unterminated one (EOF before depth returns to zero) becomes an `error`
    /// token so nothing is silently swallowed.
    fn block_comment(&mut self, start: usize) {
        self.pos += 2; // consume "(;"
        let mut depth = 1usize;
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let b0 = self.bytes[self.pos];
            let b1 = self.byte_at(1);
            if b0 == b'(' && b1 == Some(b';') {
                self.pos += 2;
                depth += 1;
            } else if b0 == b';' && b1 == Some(b')') {
                self.pos += 2;
                depth -= 1;
                if depth == 0 {
                    terminated = true;
                    break;
                }
            } else {
                self.bump();
            }
        }
        let k = if terminated {
            kind::BLOCK_COMMENT
        } else {
            kind::ERROR
        };
        self.push(k, start, self.pos, terminated);
    }

    /// A `"…"` string with backslash escapes. An unterminated literal becomes an
    /// `error` token over the exact bytes (mirrors the Clojure/Rust lexers).
    fn string(&mut self, start: usize) {
        self.bump(); // opening quote
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '\\' {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
            } else if c == '"' {
                self.bump();
                terminated = true;
                break;
            } else {
                self.bump();
            }
        }
        let k = if terminated {
            kind::STRING
        } else {
            kind::ERROR
        };
        self.push(k, start, self.pos, false);
    }

    /// An idchar run: a `$`-led run is an identifier; a digit/sign/`.`-led run (or
    /// `inf`/`nan`) is a number; everything else is a keyword (`module`, `func`,
    /// `i32.const`, …). The run is read first, then classified by shape.
    fn name_or_number(&mut self, start: usize) {
        self.eat_while(is_idchar);
        let text = &self.src[start..self.pos];
        let k = if text.starts_with('$') {
            kind::IDENTIFIER
        } else if looks_like_number(text) {
            kind::NUMBER
        } else {
            kind::KEYWORD
        };
        self.push(k, start, self.pos, false);
    }

    // --- primitives ---------------------------------------------------------

    fn peek(&self) -> char {
        self.src[self.pos..].chars().next().unwrap_or('\0')
    }

    fn byte_at(&self, n: usize) -> Option<u8> {
        self.bytes.get(self.pos + n).copied()
    }

    fn bump(&mut self) {
        let c = self.peek();
        self.pos += c.len_utf8().max(1);
    }

    fn eat_while(&mut self, mut pred: impl FnMut(char) -> bool) {
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if pred(c) {
                self.pos += c.len_utf8().max(1);
            } else {
                break;
            }
        }
    }

    fn find_line_end(&self, from: usize) -> usize {
        match self.src[from..].find('\n') {
            Some(i) => from + i,
            None => self.bytes.len(),
        }
    }

    fn push(&mut self, kind: &'static str, start: usize, end: usize, trivia: bool) {
        self.tokens.push(Token {
            kind,
            span: ByteSpan::new(start, end),
            trivia,
        });
    }
}

/// A WAT idchar: the characters that may appear in keywords, identifiers, and
/// reserved tokens. Excludes whitespace, the `(`/`)` delimiters, the `"` string
/// quote, and `;` (which only ever leads a comment or is an error byte).
fn is_idchar(c: char) -> bool {
    c.is_ascii_alphanumeric()
        || matches!(
            c,
            '!' | '#'
                | '$'
                | '%'
                | '&'
                | '\''
                | '*'
                | '+'
                | '-'
                | '.'
                | '/'
                | ':'
                | '<'
                | '='
                | '>'
                | '?'
                | '@'
                | '\\'
                | '^'
                | '_'
                | '`'
                | '|'
                | '~'
        )
}

/// Pragmatic numeric classification over an already-read idchar run: a digit
/// after an optional `+`/`-` sign or leading `.`, or the float keywords
/// `inf`/`nan` (with optional sign and `nan:0x…` payload). Coarse but lossless —
/// a mis-shaped numeric still landed as one covered token.
fn looks_like_number(text: &str) -> bool {
    let s = text
        .strip_prefix('+')
        .or_else(|| text.strip_prefix('-'))
        .unwrap_or(text);
    let mut chars = s.chars();
    match chars.next() {
        Some(c) if c.is_ascii_digit() => true,
        Some('.') => chars.next().map(|c| c.is_ascii_digit()).unwrap_or(false),
        _ => s == "inf" || s == "nan" || s.starts_with("nan:"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn texts(src: &str) -> Vec<(&'static str, String)> {
        lex(src)
            .into_iter()
            .map(|t| (t.kind, t.span.text(src).to_string()))
            .collect()
    }

    fn covers_all(src: &str) -> bool {
        let toks = lex(src);
        let mut pos = 0;
        for t in &toks {
            if t.span.start as usize != pos {
                return false;
            }
            pos = t.span.end as usize;
        }
        pos == src.len()
    }

    #[test]
    fn contiguous_coverage_is_lossless() {
        for src in [
            "(module (func $f (param i32) (result i32) local.get 0))",
            ";; a line comment\n(global $g i32 (i32.const 42))",
            "(; a (; nested ;) block comment ;)(func)",
            "(import \"env\" \"log\" (func $log (param i32)))",
            "i32.const 0xFF f64.const 1.5e-3 -42 +7 inf nan:0x1",
            "(call $a) (call_indirect (type $t))",
            "λ ☃ €", // non-ascii reserved/unknown bytes still covered
            "",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("(func $f i32.const 1)");
        assert!(t.contains(&(kind::PAREN_OPEN, "(".to_string())));
        assert!(t.contains(&(kind::KEYWORD, "func".to_string())));
        assert!(t.contains(&(kind::IDENTIFIER, "$f".to_string())));
        assert!(t.contains(&(kind::KEYWORD, "i32.const".to_string())));
        assert!(t.contains(&(kind::NUMBER, "1".to_string())));
        assert!(t.contains(&(kind::PAREN_CLOSE, ")".to_string())));
    }

    #[test]
    fn strings_and_numbers() {
        let t = texts("\"hi\" 0x10 -3.5 inf nan");
        assert!(t.contains(&(kind::STRING, "\"hi\"".to_string())));
        assert!(t.contains(&(kind::NUMBER, "0x10".to_string())));
        assert!(t.contains(&(kind::NUMBER, "-3.5".to_string())));
        assert!(t.contains(&(kind::NUMBER, "inf".to_string())));
        assert!(t.contains(&(kind::NUMBER, "nan".to_string())));
    }

    #[test]
    fn nested_block_comment_is_trivia() {
        let t = lex("(; outer (; inner ;) still ;)");
        assert_eq!(t.len(), 1);
        assert_eq!(t[0].kind, kind::BLOCK_COMMENT);
        assert!(t[0].trivia, "block comment is trivia");
    }

    #[test]
    fn line_comment_is_trivia() {
        let t = lex(";; hello\n");
        assert!(t
            .iter()
            .any(|tok| tok.kind == kind::LINE_COMMENT && tok.trivia));
    }

    #[test]
    fn unterminated_string_is_error_not_dropped() {
        let t = lex("\"oops");
        assert_eq!(t.len(), 1);
        assert_eq!(t[0].kind, kind::ERROR);
        assert_eq!(t[0].span.text("\"oops"), "\"oops");
    }

    #[test]
    fn unterminated_block_comment_is_error() {
        let src = "(; never closed";
        let t = lex(src);
        assert_eq!(t.len(), 1);
        assert_eq!(t[0].kind, kind::ERROR);
        assert_eq!(t[0].span.text(src), src);
    }

    #[test]
    fn lone_semicolon_is_error() {
        let t = texts("; )");
        assert!(t.contains(&(kind::ERROR, ";".to_string())));
        assert!(t.contains(&(kind::PAREN_CLOSE, ")".to_string())));
    }
}
