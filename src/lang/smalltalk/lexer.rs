//! Lossless Smalltalk lexer.
//!
//! Smalltalk's lexical surface is small but has two famous traps that this lexer
//! handles head-on:
//!   - a **double-quoted** `"..."` run is a **comment** (trivia), with `""` an
//!     escaped quote inside it — *not* a string;
//!   - a **single-quoted** `'...'` run is a **string literal**, with `''` an
//!     escaped quote inside it.
//!
//! Other notable tokens: `$c` character literals (the byte after `$` is taken
//! verbatim, space and `$` included), `#sym` / `#at:put:` / `#'quoted'` symbols,
//! `#(` / `#[` literal-array openers (lexed as a bare `hash` so the parser can
//! treat the body as an ordinary balanced group), `:=` assignment, `^` return,
//! `;` cascade, `.` statement separator, `!` fileout-chunk separator, and
//! `keyword:` tokens (an identifier immediately followed by a single `:` that is
//! not the start of `:=`) which are the atoms keyword selectors are built from.
//!
//! Guarantees (identical to every other front end):
//! - Every byte is covered by exactly one token (contiguous spans), so the token
//!   stream reconstructs the source verbatim.
//! - Whitespace and comments are emitted as `trivia` tokens, never dropped.
//! - Anything unclassifiable becomes an `error` token over its exact bytes.
//! - The scanner advances on every iteration; an explicit main-loop progress
//!   guard converts any (defensive, should-be-impossible) non-advance into a
//!   one-byte error token so the loop can never spin.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Smalltalk pseudo-variables. Not reserved words in the grammatical sense, but
/// they are never user-defined message sends or class names, so the lowering
/// excludes them from call / type detection.
pub const KEYWORDS: &[&str] = &["self", "super", "nil", "true", "false", "thisContext"];

/// True for a Smalltalk pseudo-variable (`self`, `super`, `nil`, …).
pub fn is_pseudo_var(text: &str) -> bool {
    KEYWORDS.contains(&text)
}

/// Token kind labels, stored on the CST as `&'static str`.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    /// A `"..."` double-quoted comment (trivia).
    pub const COMMENT: &str = "comment";
    /// A `'...'` single-quoted string literal.
    pub const STRING: &str = "string";
    /// A `$c` character literal.
    pub const CHAR: &str = "char";
    /// A `#name` / `#at:put:` / `#+` / `#'quoted'` symbol literal.
    pub const SYMBOL: &str = "symbol";
    /// A bare identifier.
    pub const IDENT: &str = "ident";
    /// An identifier immediately followed by `:` (a keyword-message atom).
    pub const KEYWORD: &str = "keyword";
    /// A numeric literal (decimal, radix `16rFF`, float, scaled).
    pub const NUMBER: &str = "number";
    /// A run of binary-selector characters (`+`, `<=`, `,`, `|`, …).
    pub const BINARY: &str = "binary";
    /// The `:=` assignment operator.
    pub const ASSIGN: &str = "assign";
    /// The `^` method-return operator.
    pub const CARET: &str = "caret";
    /// A `.` statement separator.
    pub const PERIOD: &str = "period";
    /// A `;` cascade separator.
    pub const SEMICOLON: &str = "semicolon";
    /// A lone `:` (e.g. a block argument marker `[:x | …]`).
    pub const COLON: &str = "colon";
    /// A bare `#` (literal-array opener `#(`/`#[`, or otherwise unattached).
    pub const HASH: &str = "hash";
    /// The `!` fileout-chunk separator.
    pub const BANG: &str = "bang";
    pub const LPAREN: &str = "lparen";
    pub const RPAREN: &str = "rparen";
    pub const LBRACKET: &str = "lbracket";
    pub const RBRACKET: &str = "rbracket";
    pub const LBRACE: &str = "lbrace";
    pub const RBRACE: &str = "rbrace";
    pub const ERROR: &str = "error";
}

/// Characters that make up binary selectors. `!` is deliberately excluded: it is
/// the fileout-chunk separator, which the parser depends on.
const BINARY_CHARS: &str = "+-*/~<>=&|@%,?\\";

fn is_binary_char(c: char) -> bool {
    BINARY_CHARS.contains(c)
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
            self.scan_one(start);
            // Progress guard: `scan_one` always advances. If it ever failed to
            // (it cannot, but defense code stays honest), force one byte as an
            // error token so the main loop can never spin forever.
            if self.pos == start {
                self.bump();
                self.push(kind::ERROR, start, self.pos, false);
            }
        }
        self.tokens
    }

    fn scan_one(&mut self, start: usize) {
        let c = self.peek();
        match c {
            c if c.is_whitespace() => {
                self.eat_while(|c| c.is_whitespace());
                self.push(kind::WHITESPACE, start, self.pos, true);
            }
            '"' => self.comment(start),
            '\'' => self.string(start),
            '$' => self.char_literal(start),
            '#' => self.hash(start),
            ':' => {
                if self.peek_at(1) == Some('=') {
                    self.pos += 2;
                    self.push(kind::ASSIGN, start, self.pos, false);
                } else {
                    self.bump();
                    self.push(kind::COLON, start, self.pos, false);
                }
            }
            '^' => {
                self.bump();
                self.push(kind::CARET, start, self.pos, false);
            }
            '.' => {
                self.bump();
                self.push(kind::PERIOD, start, self.pos, false);
            }
            ';' => {
                self.bump();
                self.push(kind::SEMICOLON, start, self.pos, false);
            }
            '!' => {
                self.bump();
                self.push(kind::BANG, start, self.pos, false);
            }
            '(' => self.single(start, kind::LPAREN),
            ')' => self.single(start, kind::RPAREN),
            '[' => self.single(start, kind::LBRACKET),
            ']' => self.single(start, kind::RBRACKET),
            '{' => self.single(start, kind::LBRACE),
            '}' => self.single(start, kind::RBRACE),
            c if is_ident_start(c) => self.ident_or_keyword(start),
            c if c.is_ascii_digit() => self.number(start),
            c if is_binary_char(c) => {
                self.eat_while(is_binary_char);
                self.push(kind::BINARY, start, self.pos, false);
            }
            _ => {
                // Unknown byte/char — preserve it as an explicit error token.
                self.bump();
                self.push(kind::ERROR, start, self.pos, false);
            }
        }
    }

    // --- scanners -----------------------------------------------------------

    /// `"..."` is a comment. `""` is an escaped quote inside it. An unterminated
    /// comment still covers to EOF (lossless).
    fn comment(&mut self, start: usize) {
        self.bump(); // opening "
        while self.pos < self.bytes.len() {
            if self.peek() == '"' {
                if self.peek_at(1) == Some('"') {
                    self.pos += 2; // escaped quote
                } else {
                    self.bump(); // closing "
                    break;
                }
            } else {
                self.bump();
            }
        }
        self.push(kind::COMMENT, start, self.pos, true);
    }

    /// `'...'` is a string. `''` is an escaped quote inside it.
    fn string(&mut self, start: usize) {
        self.bump(); // opening '
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            if self.peek() == '\'' {
                if self.peek_at(1) == Some('\'') {
                    self.pos += 2; // escaped quote
                } else {
                    self.bump(); // closing '
                    terminated = true;
                    break;
                }
            } else {
                self.bump();
            }
        }
        // An unterminated string keeps its real bytes but is flagged honestly.
        let k = if terminated {
            kind::STRING
        } else {
            kind::ERROR
        };
        self.push(k, start, self.pos, false);
    }

    /// `$c` — the byte after `$` is taken verbatim (space, `$`, anything). A lone
    /// trailing `$` is still a (degenerate) char token covering its byte.
    fn char_literal(&mut self, start: usize) {
        self.bump(); // $
        if self.pos < self.bytes.len() {
            self.bump(); // the character
        }
        self.push(kind::CHAR, start, self.pos, false);
    }

    /// `#...` — symbol, quoted symbol, or a bare `hash` opener for `#(` / `#[`.
    fn hash(&mut self, start: usize) {
        match self.peek_at(1) {
            Some('\'') => {
                // #'quoted symbol' — scan the single-quoted body.
                self.bump(); // #
                self.string_body();
                self.push(kind::SYMBOL, start, self.pos, false);
            }
            Some(c) if is_ident_start(c) => {
                // #foo or keyword symbol #at:put: — ident, then any number of
                // (`:` ident) groups, plus a trailing `:`.
                self.bump(); // #
                loop {
                    self.eat_while(is_ident_continue);
                    if self.peek() == ':' {
                        self.bump();
                    } else {
                        break;
                    }
                }
                self.push(kind::SYMBOL, start, self.pos, false);
            }
            Some(c) if is_binary_char(c) => {
                // #+ , #<= — a binary selector symbol.
                self.bump(); // #
                self.eat_while(is_binary_char);
                self.push(kind::SYMBOL, start, self.pos, false);
            }
            _ => {
                // Bare `#` (literal-array opener `#(`/`#[`, or unattached). The
                // following `(`/`[` is lexed separately so the parser treats the
                // body as an ordinary balanced group.
                self.bump(); // #
                self.push(kind::HASH, start, self.pos, false);
            }
        }
    }

    /// Scan a `'...'` body (cursor at the opening `'`). Shared by strings and
    /// quoted symbols. Tolerant of an unterminated run (stops at EOF).
    fn string_body(&mut self) {
        self.bump(); // opening '
        while self.pos < self.bytes.len() {
            if self.peek() == '\'' {
                if self.peek_at(1) == Some('\'') {
                    self.pos += 2;
                } else {
                    self.bump();
                    break;
                }
            } else {
                self.bump();
            }
        }
    }

    fn ident_or_keyword(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        // A trailing `:` that is not the start of `:=` makes this a keyword atom.
        if self.peek() == ':' && self.peek_at(1) != Some('=') {
            self.bump(); // the ':'
            self.push(kind::KEYWORD, start, self.pos, false);
        } else {
            self.push(kind::IDENT, start, self.pos, false);
        }
    }

    /// Numbers: decimal, radix (`16rFF`, `2r1010`), float (`3.14`, `1e10`),
    /// scaled decimal (`3.14s2`). Coarse but byte-honest; a trailing `.` that
    /// begins the next statement is never eaten (a fractional dot must be
    /// followed by a digit).
    fn number(&mut self, start: usize) {
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        if self.peek() == 'r' {
            // Radix literal: digits/letters of the given base.
            self.bump(); // r
            self.eat_while(|c| c.is_ascii_alphanumeric() || c == '_');
            if self.peek() == '.'
                && self
                    .peek_at(1)
                    .map(|c| c.is_ascii_alphanumeric())
                    .unwrap_or(false)
            {
                self.bump(); // .
                self.eat_while(|c| c.is_ascii_alphanumeric() || c == '_');
            }
        } else if self.peek() == '.' && self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false)
        {
            self.bump(); // .
            self.eat_while(|c| c.is_ascii_digit() || c == '_');
        }
        // Exponent: e / d / q [sign] digits.
        if matches!(self.peek(), 'e' | 'd' | 'q') {
            let sign_len = match self.peek_at(1) {
                Some('+') | Some('-') => 1,
                _ => 0,
            };
            if self
                .src
                .get(self.pos + 1 + sign_len..)
                .and_then(|s| s.chars().next())
                .map(|c| c.is_ascii_digit())
                .unwrap_or(false)
            {
                self.bump(); // e/d/q
                if sign_len == 1 {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit() || c == '_');
            }
        }
        // Scaled decimal: `s` optionally followed by a scale.
        if self.peek() == 's' && self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(true) {
            self.bump(); // s
            self.eat_while(|c| c.is_ascii_digit());
        }
        self.push(kind::NUMBER, start, self.pos, false);
    }

    fn single(&mut self, start: usize, k: &'static str) {
        self.bump();
        self.push(k, start, self.pos, false);
    }

    // --- primitives ---------------------------------------------------------

    fn peek(&self) -> char {
        self.src[self.pos..].chars().next().unwrap_or('\0')
    }

    fn peek_at(&self, n: usize) -> Option<char> {
        self.src[self.pos..].chars().nth(n)
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

    fn push(&mut self, kind: &'static str, start: usize, end: usize, trivia: bool) {
        self.tokens.push(Token {
            kind,
            span: ByteSpan::new(start, end),
            trivia,
        });
    }
}

fn is_ident_start(c: char) -> bool {
    c == '_' || c.is_alphabetic()
}

fn is_ident_continue(c: char) -> bool {
    c == '_' || c.is_alphanumeric()
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
            "Object subclass: #Point",
            "\"a comment with \"\"quotes\"\" inside\" x",
            "'a string with '' an escaped quote' next",
            "$a $  $$ $'",
            "#foo #at:put: #+ #'quoted sym' #(1 2 3) #[1 2]",
            "x := y + 1. ^x foo: 3 bar: 4",
            "16rFF 2r1010 3.14 1e10 3.14s2",
            "| a b | a := 1.",
            "!Counter methodsFor: 'access'!\nvalue\n\t^count! !",
            "λ ☃ €", // non-ascii idents / unknowns still covered
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn double_quote_is_comment_single_quote_is_string() {
        let t = texts("\"comment\" 'string'");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::COMMENT && s == "\"comment\""));
        assert!(t.iter().any(|(k, s)| *k == kind::STRING && s == "'string'"));
    }

    #[test]
    fn keyword_vs_assignment() {
        let t = texts("at: x := 1");
        assert!(t.contains(&(kind::KEYWORD, "at:".to_string())));
        assert!(t.contains(&(kind::ASSIGN, ":=".to_string())));
    }

    #[test]
    fn symbols_and_chars() {
        let t = texts("#at:put: $a");
        assert!(t.contains(&(kind::SYMBOL, "#at:put:".to_string())));
        assert!(t.contains(&(kind::CHAR, "$a".to_string())));
    }

    #[test]
    fn literal_array_opener_is_bare_hash() {
        let t = texts("#(1 2)");
        assert_eq!(t[0], (kind::HASH, "#".to_string()));
        assert_eq!(t[1], (kind::LPAREN, "(".to_string()));
    }
}
