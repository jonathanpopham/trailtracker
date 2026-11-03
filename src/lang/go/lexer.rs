//! Lossless Go lexer, grounded in the Go language specification's token grammar.
//!
//! Guarantees (identical contract to the Rust and Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs, line and block comments) are emitted as `trivia`
//!   tokens, never discarded. `newline` is emitted as a *non-trivia* token: Go's
//!   grammar is brace-delimited, but top-level declarations and grouped
//!   `import`/`const`/`var`/`type` specs are newline-terminated, so the parser
//!   needs newlines as structural boundaries (it does *not* reimplement Go's
//!   automatic semicolon-insertion rules — losslessness does not require it).
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_` as a pragmatic stand-in for the full Unicode
//! letter/digit tables the Go spec references — anything outside still lands in
//! the tree as a covered token, never dropped.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Go's 25 keywords. Like the Rust/Python lexers these lex as `ident` tokens; the
/// parser distinguishes them via [`is_keyword`]. Predeclared identifiers
/// (`true`, `false`, `nil`, `iota`, `len`, …) are deliberately *not* keywords —
/// they are ordinary identifiers in Go.
pub const KEYWORDS: &[&str] = &[
    "break",
    "case",
    "chan",
    "const",
    "continue",
    "default",
    "defer",
    "else",
    "fallthrough",
    "for",
    "func",
    "go",
    "goto",
    "if",
    "import",
    "interface",
    "map",
    "package",
    "range",
    "return",
    "select",
    "struct",
    "switch",
    "type",
    "var",
];

pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.contains(&text)
}

/// Token kind labels. Stored on the CST as `&'static str` so the tree stays
/// uniform and JSON-friendly.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const NEWLINE: &str = "newline";
    pub const LINE_COMMENT: &str = "line_comment";
    pub const BLOCK_COMMENT: &str = "block_comment";
    pub const IDENT: &str = "ident";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const RUNE: &str = "rune_literal";
    pub const STRING: &str = "string_literal";
    pub const RAW_STRING: &str = "raw_string_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators/punctuation, longest first so the scanner is
/// greedy-correct (`&^=` before `&^` before `&=` before the single-char `&`).
const OPERATORS: &[&str] = &[
    "<<=", ">>=", "&^=", "...", "&&", "||", "<-", "++", "--", "==", "!=", "<=", ">=", ":=", "<<",
    ">>", "&^", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=",
];

const SINGLE_PUNCT: &str = "+-*/%&|^<>=!~()[]{},;:.";

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
                '\n' => {
                    self.bump();
                    self.push(kind::NEWLINE, start, self.pos, false);
                }
                '\r' => {
                    self.bump();
                    if self.peek() == '\n' {
                        self.bump();
                    }
                    self.push(kind::NEWLINE, start, self.pos, false);
                }
                ' ' | '\t' | '\x0c' | '\x0b' => {
                    self.eat_while(|c| matches!(c, ' ' | '\t' | '\x0c' | '\x0b'));
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                '/' if self.peek_at(1) == Some('/') => self.line_comment(start),
                '/' if self.peek_at(1) == Some('*') => self.block_comment(start),
                '"' => self.interpreted_string(start),
                '`' => self.raw_string(start),
                '\'' => self.rune(start),
                c if is_ident_start(c) => self.ident(start),
                c if c.is_ascii_digit() => self.number(start),
                '.' if self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) => {
                    self.number(start)
                }
                c if SINGLE_PUNCT.contains(c) => self.punct(start),
                _ => {
                    // Unknown byte/char — preserve it as an explicit error token.
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }
        }
        self.tokens
    }

    // --- scanners -----------------------------------------------------------

    fn line_comment(&mut self, start: usize) {
        let end = self.find_line_end(start);
        self.pos = end;
        self.push(kind::LINE_COMMENT, start, end, true);
    }

    /// Go block comments do **not** nest (unlike Rust). Scan to the first `*/`.
    fn block_comment(&mut self, start: usize) {
        self.pos += 2; // /*
        while self.pos < self.bytes.len() {
            if self.src[self.pos..].starts_with("*/") {
                self.pos += 2;
                break;
            }
            self.bump();
        }
        // Unterminated block comment still covers to EOF — lossless, still trivia.
        self.push(kind::BLOCK_COMMENT, start, self.pos, true);
    }

    fn ident(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        self.push(kind::IDENT, start, self.pos, false);
    }

    /// Interpreted string `"..."`: backslash escapes, may not span a raw newline
    /// (a newline ends an unterminated literal, recorded as `error`).
    fn interpreted_string(&mut self, start: usize) {
        self.bump(); // opening "
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
            } else if c == '\n' {
                break; // interpreted strings cannot contain a literal newline
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

    /// Raw string `` `...` ``: no escapes, spans newlines, ends at the next
    /// backtick.
    fn raw_string(&mut self, start: usize) {
        self.bump(); // opening `
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            if self.peek() == '`' {
                self.bump();
                terminated = true;
                break;
            }
            self.bump();
        }
        let k = if terminated {
            kind::RAW_STRING
        } else {
            kind::ERROR
        };
        self.push(k, start, self.pos, false);
    }

    /// Rune literal `'x'` / `'\n'` / `'é'`: backslash escapes; an
    /// unterminated literal (or one broken by a newline) becomes an `error`.
    fn rune(&mut self, start: usize) {
        self.bump(); // opening '
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '\\' {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
            } else if c == '\'' {
                self.bump();
                terminated = true;
                break;
            } else if c == '\n' {
                break;
            } else {
                self.bump();
            }
        }
        let k = if terminated { kind::RUNE } else { kind::ERROR };
        self.push(k, start, self.pos, false);
    }

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        if self.peek() == '0' && matches!(self.peek_at(1), Some('x') | Some('X')) {
            self.pos += 2;
            self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
            if self.peek() == '.' {
                is_float = true;
                self.bump();
                self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
            }
            // Hex floats use a binary exponent `p`/`P`.
            if matches!(self.peek(), 'p' | 'P') {
                is_float = true;
                self.eat_exponent();
            }
        } else if self.peek() == '0' && matches!(self.peek_at(1), Some('o') | Some('O')) {
            self.pos += 2;
            self.eat_while(|c| ('0'..='7').contains(&c) || c == '_');
        } else if self.peek() == '0' && matches!(self.peek_at(1), Some('b') | Some('B')) {
            self.pos += 2;
            self.eat_while(|c| c == '0' || c == '1' || c == '_');
        } else {
            self.eat_while(|c| c.is_ascii_digit() || c == '_');
            // Fractional part only when a digit follows the dot, so a selector
            // never gets swallowed. This also covers a leading `.digit` literal
            // (e.g. `.5`), where the digit run above consumed nothing and the dot
            // is current.
            if self.peek() == '.' && self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) {
                is_float = true;
                self.bump();
                self.eat_while(|c| c.is_ascii_digit() || c == '_');
            }
            if matches!(self.peek(), 'e' | 'E') {
                is_float = true;
                self.eat_exponent();
            }
        }
        // Imaginary suffix applies to any numeric literal.
        if self.peek() == 'i' {
            is_float = true;
            self.bump();
        }
        let k = if is_float { kind::FLOAT } else { kind::INT };
        self.push(k, start, self.pos, false);
    }

    /// Consume a decimal/binary exponent: the `e`/`E`/`p`/`P` marker, an optional
    /// sign, and the digit run. Only called when the marker is current.
    fn eat_exponent(&mut self) {
        self.bump(); // e / E / p / P
        if matches!(self.peek(), '+' | '-') {
            self.bump();
        }
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
    }

    fn punct(&mut self, start: usize) {
        for op in OPERATORS {
            if self.src[self.pos..].starts_with(op) {
                self.pos += op.len();
                return self.push(kind::PUNCT, start, self.pos, false);
            }
        }
        self.bump();
        self.push(kind::PUNCT, start, self.pos, false);
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
            "package main\n\nfunc main() {}\n",
            "x := 0xFF_00 + 1.5e3 + 3i\n",
            "s := \"interp\\n\" + `raw\nstring` + 'r'\n",
            "// line comment\n/* block */ var y = 0b1010\n",
            "a &^= b; c <- d; e := f...\n",
            "λ := \"☃ €\" // unicode\n",
            "0x1p-2 0o17 0b11 .5 1_000\n",
            "",
            "\n\n   \n// trailing\n",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("func add(a int, b int) int { return a + b }");
        assert!(t.contains(&(kind::IDENT, "func".to_string())));
        assert!(t.contains(&(kind::IDENT, "add".to_string())));
        assert!(t.contains(&(kind::PUNCT, "(".to_string())));
        assert!(is_keyword("func"));
        assert!(is_keyword("interface"));
        assert!(!is_keyword("add"));
        // `nil`/`true` are predeclared identifiers, not keywords.
        assert!(!is_keyword("nil"));
        assert!(!is_keyword("true"));
    }

    #[test]
    fn raw_string_spans_newlines() {
        let t = texts("x := `a\nb\nc`\n");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::RAW_STRING && s == "`a\nb\nc`"));
    }

    #[test]
    fn andnot_operators() {
        let t = texts("a &^ b &^= c");
        assert!(t.contains(&(kind::PUNCT, "&^".to_string())));
        assert!(t.contains(&(kind::PUNCT, "&^=".to_string())));
        assert!(t.iter().all(|(k, _)| *k != kind::ERROR));
    }

    #[test]
    fn channel_and_walrus_and_variadic() {
        let t = texts("ch <- x; y := z; f(a...)");
        assert!(t.contains(&(kind::PUNCT, "<-".to_string())));
        assert!(t.contains(&(kind::PUNCT, ":=".to_string())));
        assert!(t.contains(&(kind::PUNCT, "...".to_string())));
    }

    #[test]
    fn numbers() {
        let t = texts("0b1010 0o17 0xAF 10_000 3.14 2e10 5i 0x1p-2");
        assert!(t.contains(&(kind::INT, "0b1010".to_string())));
        assert!(t.contains(&(kind::INT, "0xAF".to_string())));
        assert!(t.contains(&(kind::INT, "10_000".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14".to_string())));
        assert!(t.contains(&(kind::FLOAT, "5i".to_string())));
        assert!(t.contains(&(kind::FLOAT, "0x1p-2".to_string())));
    }

    #[test]
    fn rune_vs_string() {
        let t = texts("'a' '\\n' \"str\"");
        assert!(t.contains(&(kind::RUNE, "'a'".to_string())));
        assert!(t.contains(&(kind::RUNE, "'\\n'".to_string())));
        assert!(t.contains(&(kind::STRING, "\"str\"".to_string())));
    }

    #[test]
    fn block_comment_does_not_nest() {
        // Go block comments stop at the first `*/`; the trailing `*/` is separate.
        let t = texts("/* a /* b */");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::BLOCK_COMMENT && s == "/* a /* b */"));
    }
}
