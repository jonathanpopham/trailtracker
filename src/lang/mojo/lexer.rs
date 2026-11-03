//! Lossless Mojo lexer.
//!
//! Mojo is a Python superset: it shares Python's lexical grammar (indentation,
//! `#` line comments, `"..."` / `'''...'''` strings, the same number and operator
//! shapes) and adds keywords such as `fn`, `struct`, `trait`, `alias`, `var`,
//! and the argument conventions (`owned`, `borrowed`, `inout`, `ref`). The lexer
//! therefore mirrors the Python lexer's contract exactly:
//!
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs, `#` comments, line continuations) are emitted as
//!   `trivia` tokens, never discarded. `newline` is a *non-trivia* token because
//!   it is structurally significant (statement and block boundaries).
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//! - The main loop advances `pos` on every iteration (the catch-all `error` arm
//!   bumps at least one char), so the scanner always terminates.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_` as a pragmatic stand-in for the full Unicode
//! identifier tables — anything outside still lands in the tree as a covered
//! token, never dropped. Character handling is done char-by-char (never
//! byte-slicing a `char`) so multi-byte identifiers round-trip safely.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Mojo keywords: Python's set plus Mojo-specific declaration/convention words.
/// Like the Python lexer, these lex as `name` tokens; the parser and lowering
/// distinguish them via [`is_keyword`].
pub const KEYWORDS: &[&str] = &[
    // Python heritage
    "False",
    "None",
    "True",
    "and",
    "as",
    "assert",
    "async",
    "await",
    "break",
    "class",
    "continue",
    "def",
    "del",
    "elif",
    "else",
    "except",
    "finally",
    "for",
    "from",
    "global",
    "if",
    "import",
    "in",
    "is",
    "lambda",
    "nonlocal",
    "not",
    "or",
    "pass",
    "raise",
    "return",
    "try",
    "while",
    "with",
    "yield",
    "match",
    "case",
    // Mojo additions
    "fn",
    "struct",
    "trait",
    "alias",
    "var",
    "let",
    "owned",
    "borrowed",
    "inout",
    "ref",
    "raises",
    "capturing",
    "self",
    "Self",
];

pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.contains(&text)
}

pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const NEWLINE: &str = "newline";
    pub const COMMENT: &str = "comment";
    pub const LINE_CONTINUATION: &str = "line_continuation";
    pub const NAME: &str = "name";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const STRING: &str = "string_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
const OPERATORS: &[&str] = &[
    "**=", "//=", ">>=", "<<=", "...", "!=", ">=", "<=", "==", "->", ":=", "**", "//", ">>", "<<",
    "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "@=",
];

const SINGLE_PUNCT: &str = "+-*/%@&|^~<>=()[]{}:,.;!";

/// String prefixes (case-insensitive): r, b, f, u and the two-letter combos.
/// Works char-by-char (never byte-slices) so a non-ASCII identifier like `Héllo`
/// is handled safely — string prefixes are all ASCII, so any non-`r/b/f/u` start
/// (including a multi-byte char) returns immediately.
fn string_prefix_len(rest: &str) -> Option<usize> {
    let mut chars = rest.chars();
    let c0 = chars.next()?.to_ascii_lowercase();
    if !matches!(c0, 'r' | 'b' | 'f' | 'u') {
        return None;
    }
    let c1 = chars.next();
    // Two-letter prefixes (rb/br/rf/fr) followed by a quote.
    if let Some(c1c) = c1 {
        let two = [c0, c1c.to_ascii_lowercase()];
        if matches!(two, ['r', 'b'] | ['b', 'r'] | ['r', 'f'] | ['f', 'r']) {
            if let Some(q) = chars.next() {
                if q == '"' || q == '\'' {
                    return Some(2);
                }
            }
        }
    }
    // One-letter prefix followed by a quote.
    if matches!(c1, Some('"') | Some('\'')) {
        return Some(1);
    }
    None
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
                '\\' if matches!(self.peek_at(1), Some('\n') | Some('\r')) => {
                    // Explicit line continuation: backslash-newline joins lines.
                    self.bump(); // backslash
                    if self.peek() == '\r' {
                        self.bump();
                    }
                    if self.peek() == '\n' {
                        self.bump();
                    }
                    self.push(kind::LINE_CONTINUATION, start, self.pos, true);
                }
                ' ' | '\t' | '\x0c' => {
                    self.eat_while(|c| c == ' ' || c == '\t' || c == '\x0c');
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                '#' => {
                    let end = self.find_line_end(start);
                    self.pos = end;
                    self.push(kind::COMMENT, start, end, true);
                }
                '"' | '\'' => self.string(start, 0),
                c if is_ident_start(c) => {
                    // Could be a string prefix (r"", f'', rb"", …) or a name.
                    if let Some(plen) = string_prefix_len(&self.src[start..]) {
                        let raw = self.src[start..start + plen].to_lowercase().contains('r');
                        self.pos += plen;
                        self.string(start, if raw { 1 } else { 0 });
                    } else {
                        self.name(start);
                    }
                }
                c if c.is_ascii_digit() => self.number(start),
                '.' if self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) => {
                    self.number(start)
                }
                c if SINGLE_PUNCT.contains(c) => self.punct(start),
                _ => {
                    // Catch-all: guarantees progress every iteration. The exact
                    // bytes stay in the tree as an `error` token, never dropped.
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }
        }
        self.tokens
    }

    fn name(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        self.push(kind::NAME, start, self.pos, false);
    }

    /// Scan a string literal. Handles both single (`'`/`"`) and triple
    /// (`'''`/`"""`) quotes; triple strings span newlines. The opening prefix (if
    /// any) has already been consumed. `_raw` is accepted for call-site symmetry
    /// with the prefix scanner: a backslash still prevents the very next char from
    /// closing the string in both raw and non-raw forms (per CPython/Mojo), and
    /// the bytes are retained verbatim regardless, so scanning is identical.
    fn string(&mut self, start: usize, _raw: usize) {
        let quote = self.peek();
        // Triple-quoted?
        let triple = self.peek_at(1) == Some(quote) && self.peek_at(2) == Some(quote);
        if triple {
            self.pos += 3;
        } else {
            self.bump();
        }
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '\\' {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
                continue;
            }
            if c == quote {
                if triple {
                    if self.peek_at(1) == Some(quote) && self.peek_at(2) == Some(quote) {
                        self.pos += 3;
                        terminated = true;
                        break;
                    }
                    self.bump();
                } else {
                    self.bump();
                    terminated = true;
                    break;
                }
            } else if c == '\n' && !triple {
                // Unterminated single-line string ends at the newline.
                break;
            } else {
                self.bump();
            }
        }
        let token_kind = if terminated {
            kind::STRING
        } else {
            kind::ERROR
        };
        self.push(token_kind, start, self.pos, false);
    }

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        if self.peek() == '0' {
            match self.peek_at(1) {
                Some('x') | Some('X') => {
                    self.pos += 2;
                    self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
                    return self.push(kind::INT, start, self.pos, false);
                }
                Some('o') | Some('O') => {
                    self.pos += 2;
                    self.eat_while(|c| ('0'..='7').contains(&c) || c == '_');
                    return self.push(kind::INT, start, self.pos, false);
                }
                Some('b') | Some('B') => {
                    self.pos += 2;
                    self.eat_while(|c| c == '0' || c == '1' || c == '_');
                    return self.push(kind::INT, start, self.pos, false);
                }
                _ => {}
            }
        }
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        if self.peek() == '.' {
            is_float = true;
            self.bump();
            self.eat_while(|c| c.is_ascii_digit() || c == '_');
        }
        if matches!(self.peek(), 'e' | 'E') {
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
                is_float = true;
                self.bump();
                if sign_len == 1 {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit() || c == '_');
            }
        }
        // Imaginary suffix.
        if matches!(self.peek(), 'j' | 'J') {
            is_float = true;
            self.bump();
        }
        let k = if is_float { kind::FLOAT } else { kind::INT };
        self.push(k, start, self.pos, false);
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
            "fn add(x: Int, y: Int) -> Int:\n    return x + y\n",
            "def f(x):\n    return x\n",
            "struct Point(Stringable):\n    var x: Int\n",
            "trait Shape(Drawable):\n    fn area(self) -> Float64:\n        ...\n",
            "alias PI = 3.14159\nvar count = 0\n",
            "x = 0xFF_00 + 1.5e3 + 3j\n",
            "s = r\"raw\\n\" + f'{x}' + '''multi\nline''' + b\"bytes\"\n",
            "a = b  # comment\nfoo \\\n  + bar\n",
            "λ = '☃ €'  # unicode\n",
            "y := 1; z **= 2",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_mojo_keywords() {
        let t = texts("fn add(a: Int, b: Int) -> Int:\n    return a + b\n");
        assert!(t.contains(&(kind::NAME, "fn".to_string())));
        assert!(t.contains(&(kind::NAME, "add".to_string())));
        assert!(t.contains(&(kind::PUNCT, "->".to_string())));
        assert!(t.iter().any(|(k, _)| *k == kind::NEWLINE));
        assert!(is_keyword("fn"));
        assert!(is_keyword("struct"));
        assert!(is_keyword("trait"));
        assert!(is_keyword("alias"));
        assert!(!is_keyword("add"));
    }

    #[test]
    fn triple_quoted_spans_newlines() {
        let t = texts("x = \"\"\"a\nb\nc\"\"\"\n");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "\"\"\"a\nb\nc\"\"\""));
    }

    #[test]
    fn string_prefixes() {
        for (src, lit) in [
            ("r\"a\\b\"", "r\"a\\b\""),
            ("f'{x}'", "f'{x}'"),
            ("rb\"x\"", "rb\"x\""),
            ("b'bytes'", "b'bytes'"),
        ] {
            let t = texts(src);
            assert!(
                t.iter().any(|(k, s)| *k == kind::STRING && s == lit),
                "prefix string not recognized: {src}"
            );
        }
    }

    #[test]
    fn not_equal_is_one_operator() {
        let t = texts("a != b");
        assert!(t.contains(&(kind::PUNCT, "!=".to_string())));
        assert!(t.iter().all(|(k, _)| *k != kind::ERROR));
    }

    #[test]
    fn numbers() {
        let t = texts("0b1010 0o17 0xAF 10_000 3.14 2e10 5j");
        assert!(t.contains(&(kind::INT, "0b1010".to_string())));
        assert!(t.contains(&(kind::INT, "0xAF".to_string())));
        assert!(t.contains(&(kind::INT, "10_000".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14".to_string())));
        assert!(t.contains(&(kind::FLOAT, "5j".to_string())));
    }
}
