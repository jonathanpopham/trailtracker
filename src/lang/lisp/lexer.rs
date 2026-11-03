//! Lossless Lisp lexer — one s-expression reader covering Common Lisp (`.lisp`,
//! `.cl`), Scheme (`.scm`, `.ss`), and Emacs Lisp (`.el`). These dialects share a
//! lexical structure: balanced delimiters, atoms, `"…"` strings, `#\` character
//! literals, `;` line comments, `#| … |#` *nested* block comments, `#;` datum
//! comments, and the quote family of reader macros (`'`, `` ` ``, `,`, `,@`).
//!
//! The lexer is purely lossless, matching the contract of the Rust, Python, and
//! Clojure lexers:
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia — whitespace, `;` line comments, `#| |#` block comments, and `#;`
//!   datum-comment markers — are emitted as `trivia` tokens, never discarded.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes (e.g. an unterminated string or block comment). Input is never
//!   silently dropped.
//!
//! Progress guard: the main run loop records `pos` at the top of every iteration
//! and, if a (defensive) branch failed to advance, consumes a single char as an
//! `error` token. A non-advancing loop would spin forever and exhaust memory, so
//! this guard is load-bearing, not decoration.
//!
//! Coverage note (honest): symbol/atom constituents use a pragmatic character
//! class rather than any one dialect's full reader spec, and Common Lisp's
//! single-escape `\` and multi-escape `|…|` are handled inside symbol scanning so
//! escaped delimiters never unbalance the tree. The `#;` datum comment is treated
//! as a two-byte trivia marker (the datum it would discard is still read) — this
//! is a breadth gap, not a correctness lie: every byte lands in the tree with its
//! true span.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Token kind labels, stored on the CST as `&'static str`.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const COMMENT: &str = "line_comment";
    pub const BLOCK_COMMENT: &str = "block_comment";
    pub const DATUM_COMMENT: &str = "datum_comment";
    pub const SYMBOL: &str = "symbol";
    pub const KEYWORD: &str = "keyword";
    pub const STRING: &str = "string_literal";
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
                c if c.is_whitespace() => {
                    self.eat_while(|c| c.is_whitespace());
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                ';' => self.line_comment(start),
                '"' => self.string(start),
                '#' => self.dispatch(start),
                ':' => self.keyword(start),
                '(' => self.single(start, kind::PAREN_OPEN),
                ')' => self.single(start, kind::PAREN_CLOSE),
                '[' => self.single(start, kind::BRACKET_OPEN),
                ']' => self.single(start, kind::BRACKET_CLOSE),
                '{' => self.single(start, kind::BRACE_OPEN),
                '}' => self.single(start, kind::BRACE_CLOSE),
                '\'' | '`' => self.single(start, kind::READER),
                ',' => {
                    self.bump(); // ,
                    if self.peek() == '@' {
                        self.bump(); // unquote-splicing ,@
                    }
                    self.push(kind::READER, start, self.pos, false);
                }
                // Common Lisp single-escape (`\x`) and multi-escape (`|…|`) start a
                // symbol; handling them in the symbol scanner keeps escaped
                // delimiters from unbalancing the tree.
                '\\' | '|' => self.symbol(start),
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

    /// Reader dispatch on `#`:
    /// - `#| … |#` → nested block comment (trivia)
    /// - `#;`      → datum-comment marker (trivia, two bytes; the datum is read)
    /// - `#\X`     → character literal (named like `#\newline` or single `#\(`)
    /// - `#xFF` / `#b1010` / `#o17` / `#16rFF` / `#e1.5` … → radix/exactness number
    /// - `#'foo`   → function-quote reader macro
    /// - otherwise → a bare `#` reader token (so `#(`, `#:`, `#+`, `#.` fall out as
    ///   a `#` token followed by the next form)
    fn dispatch(&mut self, start: usize) {
        match self.peek_at(1) {
            Some('|') => self.block_comment(start),
            Some(';') => {
                self.pos += 2; // #;
                self.push(kind::DATUM_COMMENT, start, self.pos, true);
            }
            Some('\\') => self.char_literal(start),
            Some('\'') => {
                self.pos += 2; // #'
                self.push(kind::READER, start, self.pos, false);
            }
            Some(c) if is_radix_lead(c) => self.number(start),
            _ => {
                self.bump(); // #
                self.push(kind::READER, start, self.pos, false);
            }
        }
    }

    /// `#| … |#` block comment with *nested* support. An unterminated comment is
    /// flagged as an `error` token (non-trivia) so the problem is not hidden, while
    /// still covering its exact bytes.
    fn block_comment(&mut self, start: usize) {
        self.pos += 2; // #|
        let mut depth: u32 = 1;
        while self.pos < self.bytes.len() && depth > 0 {
            if self.peek() == '#' && self.peek_at(1) == Some('|') {
                self.pos += 2;
                depth += 1;
            } else if self.peek() == '|' && self.peek_at(1) == Some('#') {
                self.pos += 2;
                depth -= 1;
            } else {
                self.bump();
            }
        }
        if depth == 0 {
            self.push(kind::BLOCK_COMMENT, start, self.pos, true);
        } else {
            // Unterminated: covered, but reported as an error rather than swallowed.
            self.push(kind::ERROR, start, self.pos, false);
        }
    }

    /// Scan a `"…"` string. Handles backslash escapes; an unterminated literal
    /// becomes an `error` token.
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

    /// Character literal `#\X`: a named char (`#\newline`, `#\Space`, `#\x41`) is
    /// an alphanumeric run; any other single char is taken literally (`#\(`, `#\ `,
    /// `#\\`). The cursor is at the leading `#`.
    fn char_literal(&mut self, start: usize) {
        self.pos += 2; // #\
        if self.pos < self.bytes.len() {
            if self.peek().is_alphanumeric() {
                self.eat_while(|c| c.is_alphanumeric());
            } else {
                self.bump(); // a single literal char (e.g. `#\(`)
            }
        }
        self.push(kind::CHAR, start, self.pos, false);
    }

    /// `:kw` — a leading colon followed by symbol constituents (Common Lisp /
    /// Emacs Lisp keyword symbol). Internal colons in `pkg:sym` are constituents
    /// and stay part of a regular symbol.
    fn keyword(&mut self, start: usize) {
        self.bump(); // :
        self.eat_while(is_sym_constituent);
        self.push(kind::KEYWORD, start, self.pos, false);
    }

    /// A symbol, including Common Lisp single-escape `\c` (one char escaped) and
    /// multi-escape `|…|` (everything until the matching bar, escapes honored).
    /// Escaped delimiters never unbalance the surrounding s-expression.
    fn symbol(&mut self, start: usize) {
        loop {
            let c = self.peek();
            if self.pos >= self.bytes.len() {
                break;
            }
            if c == '\\' {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump(); // the escaped char
                }
            } else if c == '|' {
                self.bump(); // opening bar
                while self.pos < self.bytes.len() {
                    let d = self.peek();
                    if d == '\\' {
                        self.bump();
                        if self.pos < self.bytes.len() {
                            self.bump();
                        }
                    } else if d == '|' {
                        self.bump(); // closing bar
                        break;
                    } else {
                        self.bump();
                    }
                }
            } else if is_sym_constituent(c) {
                self.bump();
            } else {
                break;
            }
        }
        self.push(kind::SYMBOL, start, self.pos, false);
    }

    /// Numbers: integers, floats, ratios (`1/2`), signed values, exponents
    /// (`1.5e-3`), and `#`-prefixed radix/exactness forms (`#xFF`, `#b1010`,
    /// `#o17`, `#16rFF`, `#e1.5`, `#i#xA`). Coarse but lossless: a mis-shaped
    /// numeric still lands as one covered token.
    fn number(&mut self, start: usize) {
        // Leading `#`-prefix chain: `#x`, `#e#x`, `#16r`, …
        while self.peek() == '#' {
            self.bump(); // #
            if self.pos < self.bytes.len() {
                self.bump(); // radix/exactness char (or digit count start)
            }
        }
        if matches!(self.peek(), '+' | '-') {
            self.bump();
        }
        let mut prev = '\0';
        while self.pos < self.bytes.len() {
            let c = self.peek();
            let ok = c.is_ascii_alphanumeric()
                || c == '.'
                || c == '/'
                || c == '#'
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

/// True if `c`, immediately after `#`, leads a radix/exactness number: a radix
/// indicator (`x b o d`), an exactness indicator (`e i`), or a digit (radix count
/// as in `#16rFF`).
fn is_radix_lead(c: char) -> bool {
    matches!(
        c,
        'x' | 'X' | 'b' | 'B' | 'o' | 'O' | 'd' | 'D' | 'e' | 'E' | 'i' | 'I'
    ) || c.is_ascii_digit()
}

/// A symbol constituent: anything that is not whitespace, a delimiter, a string
/// quote, a comment `;`, a reader-macro lead (`'`, `` ` ``, `,`, `#`), or an escape
/// lead (`\`, `|`). Note `:` is a constituent (special only in leading position,
/// which the run loop handles before reaching a symbol).
fn is_sym_constituent(c: char) -> bool {
    !c.is_whitespace()
        && !matches!(
            c,
            '(' | ')' | '[' | ']' | '{' | '}' | '"' | ';' | '\'' | '`' | ',' | '#' | '\\' | '|'
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
            "(defun add (a b) (+ a b))",
            "(define (f x) (* x x))",
            ":keyword :foo-bar",
            "; a comment\n(defvar x 1)",
            "#| outer #| nested |# still |# (list 1 2 3)",
            "#;(ignored datum) (real)",
            "#\\newline #\\space #\\a #\\( #\\x41",
            "#xFF #b1010 #o17 #16rFF #e1.5 1/2 -42 +7 1.5e-3",
            "'quoted `quasi ,unquote ,@spliced #'fn-quote #(1 2 3)",
            "|weird symbol| foo\\ bar a.b.c <=> 1+",
            "\"a string with \\\" escape\"",
            "λ ☃ €", // non-ascii symbols still covered
            "",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("(defun f (x) x)");
        assert!(t.contains(&(kind::PAREN_OPEN, "(".to_string())));
        assert!(t.contains(&(kind::SYMBOL, "defun".to_string())));
        assert!(t.contains(&(kind::SYMBOL, "f".to_string())));
        assert!(t.contains(&(kind::PAREN_CLOSE, ")".to_string())));
    }

    #[test]
    fn keywords_and_strings() {
        let t = texts(":foo \"bar\"");
        assert!(t.contains(&(kind::KEYWORD, ":foo".to_string())));
        assert!(t.contains(&(kind::STRING, "\"bar\"".to_string())));
    }

    #[test]
    fn nested_block_comment_is_trivia() {
        let t = lex("#| a #| b |# c |# x");
        let bc = t
            .iter()
            .find(|tok| tok.kind == kind::BLOCK_COMMENT)
            .expect("a block comment");
        assert!(bc.trivia);
        assert_eq!(bc.span.text("#| a #| b |# c |# x"), "#| a #| b |# c |#");
    }

    #[test]
    fn unterminated_block_comment_is_error_not_dropped() {
        let t = lex("#| never closed");
        assert_eq!(t.len(), 1);
        assert_eq!(t[0].kind, kind::ERROR);
        assert_eq!(t[0].span.text("#| never closed"), "#| never closed");
    }

    #[test]
    fn datum_comment_is_trivia_marker() {
        let t = lex("#;(x)");
        assert_eq!(t[0].kind, kind::DATUM_COMMENT);
        assert!(t[0].trivia);
        assert_eq!(t[0].span.text("#;(x)"), "#;");
    }

    #[test]
    fn char_named_and_single() {
        let t = texts("#\\newline #\\(");
        assert!(t.contains(&(kind::CHAR, "#\\newline".to_string())));
        assert!(t.contains(&(kind::CHAR, "#\\(".to_string())));
    }

    #[test]
    fn radix_and_ratio_numbers() {
        let t = texts("#xFF #b1010 1/2 #16rZZ");
        assert!(t.contains(&(kind::NUMBER, "#xFF".to_string())));
        assert!(t.contains(&(kind::NUMBER, "#b1010".to_string())));
        assert!(t.contains(&(kind::NUMBER, "1/2".to_string())));
        assert!(t.contains(&(kind::NUMBER, "#16rZZ".to_string())));
    }

    #[test]
    fn pipe_escaped_symbol_does_not_unbalance() {
        // The `(` inside the bars is part of the symbol, not a delimiter.
        let t = texts("|a (b| c");
        assert!(t.contains(&(kind::SYMBOL, "|a (b|".to_string())));
    }

    #[test]
    fn unterminated_string_is_error_not_dropped() {
        let t = lex("\"oops");
        assert_eq!(t.len(), 1);
        assert_eq!(t[0].kind, kind::ERROR);
        assert_eq!(t[0].span.text("\"oops"), "\"oops");
    }
}
