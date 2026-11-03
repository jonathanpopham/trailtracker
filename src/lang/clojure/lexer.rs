//! Lossless Clojure (EDN / clj / cljs / cljc) lexer.
//!
//! Clojure is s-expressions: the reader sees delimiters, atoms, and a handful of
//! reader macros. This lexer stays purely lossless, matching the contract of the
//! Rust and Python lexers:
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (whitespace — which in Clojure *includes commas* — `;` line comments,
//!   and `#_` discard markers) are emitted as `trivia` tokens, never discarded.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//!
//! Progress guard: the main run loop records `pos` at the top of every iteration
//! and, if a (defensive) branch failed to advance, consumes a single char as an
//! `error` token. A non-advancing loop would spin forever and exhaust memory, so
//! this guard is load-bearing, not decoration.
//!
//! Coverage note (honest): identifier/symbol constituents use a pragmatic
//! character class rather than the full Clojure reader spec (e.g. a trailing `'`
//! in a symbol like `x'` lexes as a separate quote token). This is a breadth gap,
//! not a correctness lie: every byte still lands in the tree with its true span.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Token kind labels, stored on the CST as `&'static str`.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const COMMENT: &str = "line_comment";
    pub const DISCARD: &str = "discard";
    pub const SYMBOL: &str = "symbol";
    pub const KEYWORD: &str = "keyword";
    pub const STRING: &str = "string_literal";
    pub const REGEX: &str = "regex_literal";
    pub const CHAR: &str = "char_literal";
    pub const NUMBER: &str = "number_literal";
    pub const READER: &str = "reader_macro";
    pub const PAREN_OPEN: &str = "paren_open";
    pub const PAREN_CLOSE: &str = "paren_close";
    pub const BRACKET_OPEN: &str = "bracket_open";
    pub const BRACKET_CLOSE: &str = "bracket_close";
    pub const BRACE_OPEN: &str = "brace_open";
    pub const BRACE_CLOSE: &str = "brace_close";
    pub const ERROR: &str = "error";
}

/// True if `k` is an opening delimiter token kind.
pub fn is_open_delim(k: &str) -> bool {
    k == kind::PAREN_OPEN || k == kind::BRACKET_OPEN || k == kind::BRACE_OPEN
}

/// True if `k` is a closing delimiter token kind.
pub fn is_close_delim(k: &str) -> bool {
    k == kind::PAREN_CLOSE || k == kind::BRACKET_CLOSE || k == kind::BRACE_CLOSE
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
                c if is_ws(c) => {
                    self.eat_while(is_ws);
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                ';' => self.line_comment(start),
                '"' => self.scan_string_body(start, kind::STRING),
                '\\' => self.char_literal(start),
                ':' => self.keyword(start),
                '(' => self.single(start, kind::PAREN_OPEN),
                ')' => self.single(start, kind::PAREN_CLOSE),
                '[' => self.single(start, kind::BRACKET_OPEN),
                ']' => self.single(start, kind::BRACKET_CLOSE),
                '{' => self.single(start, kind::BRACE_OPEN),
                '}' => self.single(start, kind::BRACE_CLOSE),
                '\'' | '`' | '@' | '^' => self.single(start, kind::READER),
                '~' => {
                    self.bump(); // ~
                    if self.peek() == '@' {
                        self.bump(); // unquote-splicing ~@
                    }
                    self.push(kind::READER, start, self.pos, false);
                }
                '#' => self.dispatch(start),
                c if c.is_ascii_digit() => self.number(start),
                '+' | '-' if self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) => {
                    self.number(start)
                }
                '.' if self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) => {
                    self.number(start)
                }
                c if is_sym_constituent(c) => self.symbol(start),
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
        self.push(kind::COMMENT, start, end, true);
    }

    /// Reader dispatch on `#`: `#_` discard (trivia), `#"..."` regex, otherwise a
    /// bare `#` reader token (so `#{`, `#(`, `#'foo` fall out naturally as a `#`
    /// token followed by the next form).
    fn dispatch(&mut self, start: usize) {
        match self.peek_at(1) {
            Some('_') => {
                self.pos += 2; // #_
                self.push(kind::DISCARD, start, self.pos, true);
            }
            Some('"') => {
                self.bump(); // #
                self.scan_string_body(start, kind::REGEX);
            }
            _ => {
                self.bump(); // #
                self.push(kind::READER, start, self.pos, false);
            }
        }
    }

    /// Scan a `"..."` body. The cursor is at the opening quote (the `#` of a regex
    /// has already been consumed by the caller, but `start` covers it). Handles
    /// backslash escapes; an unterminated literal becomes an `error` token.
    fn scan_string_body(&mut self, start: usize, k: &'static str) {
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
        let token_kind = if terminated { k } else { kind::ERROR };
        self.push(token_kind, start, self.pos, false);
    }

    /// Clojure character literal: `\a`, `\newline`, `\space`, `\tab`, `\uNNNN`,
    /// `\oNNN`, or `\<single-char>` such as `\(`. A named/escape char is an
    /// alphanumeric run; any other single char is taken literally.
    fn char_literal(&mut self, start: usize) {
        self.bump(); // backslash
        if self.pos < self.bytes.len() {
            if self.peek().is_alphanumeric() {
                self.eat_while(|c| c.is_alphanumeric());
            } else {
                self.bump(); // a single literal char (e.g. `\(`)
            }
        }
        self.push(kind::CHAR, start, self.pos, false);
    }

    /// `:kw`, `::kw`, `:ns/kw` — a colon (or two) followed by symbol constituents.
    fn keyword(&mut self, start: usize) {
        self.bump(); // :
        self.eat_while(is_sym_constituent);
        self.push(kind::KEYWORD, start, self.pos, false);
    }

    fn symbol(&mut self, start: usize) {
        self.eat_while(is_sym_constituent);
        self.push(kind::SYMBOL, start, self.pos, false);
    }

    /// Numbers: integers, floats, ratios (`22/7`), radix (`2r1010`), hex (`0xFF`),
    /// with optional leading sign and `e`/`E` exponent. Coarse but lossless: a
    /// mis-shaped numeric still lands as one covered token.
    fn number(&mut self, start: usize) {
        if matches!(self.peek(), '+' | '-') {
            self.bump();
        }
        let mut prev = '\0';
        while self.pos < self.bytes.len() {
            let c = self.peek();
            let ok = c.is_ascii_alphanumeric()
                || c == '.'
                || c == '/'
                || ((c == '+' || c == '-') && (prev == 'e' || prev == 'E'));
            if !ok {
                break;
            }
            prev = c;
            self.pos += c.len_utf8().max(1);
        }
        self.push(kind::NUMBER, start, self.pos, false);
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

/// Whitespace in Clojure includes the comma, which the reader treats as blank.
fn is_ws(c: char) -> bool {
    c == ',' || c.is_whitespace()
}

/// A symbol/keyword constituent: anything that is not whitespace, a delimiter, a
/// string quote, a comment `;`, or a reader-macro lead char. `:` and `#` are
/// constituents (they only carry special meaning in the *leading* position, which
/// the run loop handles before reaching a symbol).
fn is_sym_constituent(c: char) -> bool {
    !c.is_whitespace()
        && !matches!(
            c,
            ',' | '('
                | ')'
                | '['
                | ']'
                | '{'
                | '}'
                | '"'
                | ';'
                | '\''
                | '`'
                | '~'
                | '@'
                | '^'
                | '\\'
        )
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
            "(defn add [a b] (+ a b))",
            ":keyword ::ns-kw :ns/kw",
            "; a comment\n(def x 1)",
            "#_ (ignored form) [1 2 3]",
            "{:a 1, :b 2}",
            "\\newline \\space \\a \\( \\u0041",
            "#\"re[0-9]+\" #{1 2} #(+ % 1) #'var",
            "'quoted `syntax ~unq ~@spliced @deref ^:meta",
            "22/7 0xFF 2r1010 1.5e-3 -42 +7",
            "λ ☃ €", // non-ascii symbols / unknowns still covered
            "",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("(defn f [x] x)");
        assert!(t.contains(&(kind::PAREN_OPEN, "(".to_string())));
        assert!(t.contains(&(kind::SYMBOL, "defn".to_string())));
        assert!(t.contains(&(kind::BRACKET_OPEN, "[".to_string())));
        assert!(t.contains(&(kind::PAREN_CLOSE, ")".to_string())));
    }

    #[test]
    fn commas_are_whitespace_trivia() {
        let t = lex("[1, 2, 3]");
        assert!(t
            .iter()
            .any(|tok| tok.kind == kind::WHITESPACE && tok.trivia));
    }

    #[test]
    fn keywords_and_strings() {
        let t = texts(":foo \"bar\" #\"rx\"");
        assert!(t.contains(&(kind::KEYWORD, ":foo".to_string())));
        assert!(t.contains(&(kind::STRING, "\"bar\"".to_string())));
        assert!(t.contains(&(kind::REGEX, "#\"rx\"".to_string())));
    }

    #[test]
    fn discard_is_trivia() {
        let t = lex("#_ x");
        assert!(t.iter().any(|tok| tok.kind == kind::DISCARD && tok.trivia));
    }

    #[test]
    fn char_named_and_single() {
        let t = texts("\\newline \\(");
        assert!(t.contains(&(kind::CHAR, "\\newline".to_string())));
        assert!(t.contains(&(kind::CHAR, "\\(".to_string())));
    }

    #[test]
    fn unterminated_string_is_error_not_dropped() {
        let t = lex("\"oops");
        assert_eq!(t.len(), 1);
        assert_eq!(t[0].kind, kind::ERROR);
        assert_eq!(t[0].span.text("\"oops"), "\"oops");
    }
}
