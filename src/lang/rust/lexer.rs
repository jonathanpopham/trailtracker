//! Lossless Rust lexer, grounded in the Rust Reference token grammar.
//!
//! Guarantees:
//! - Every byte of input is covered by exactly one token (contiguous spans),
//!   so the token stream reconstructs the source verbatim.
//! - Trivia (whitespace, comments, shebang) are emitted as `trivia` tokens, not
//!   discarded — the parser skips them for structure but the tree keeps them.
//! - Anything the lexer cannot classify becomes an `error` token covering the
//!   exact bytes. Input is never silently dropped.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_` as a pragmatic stand-in for the full Unicode
//! XID tables. This is a breadth gap, not a correctness lie: anything outside it
//! still lands in the tree as an `error` token with its true span.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// The 50 strict + reserved Rust keywords. Contextual keywords (`union`, `dyn`,
/// etc.) are handled by the parser, not the lexer.
pub const KEYWORDS: &[&str] = &[
    "as", "break", "const", "continue", "crate", "else", "enum", "extern", "false", "fn", "for",
    "if", "impl", "in", "let", "loop", "match", "mod", "move", "mut", "pub", "ref", "return",
    "self", "Self", "static", "struct", "super", "trait", "true", "type", "unsafe", "use", "where",
    "while", "async", "await", "dyn", "abstract", "become", "box", "do", "final", "macro",
    "override", "priv", "typeof", "unsized", "virtual", "yield", "try",
];

pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.contains(&text)
}

/// Token kind labels. Stored on the CST as `&'static str` so the tree stays
/// uniform and JSON-friendly.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const LINE_COMMENT: &str = "line_comment";
    pub const BLOCK_COMMENT: &str = "block_comment";
    pub const SHEBANG: &str = "shebang";
    pub const IDENT: &str = "ident";
    pub const RAW_IDENT: &str = "raw_ident";
    pub const LIFETIME: &str = "lifetime";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const CHAR: &str = "char_literal";
    pub const BYTE: &str = "byte_literal";
    pub const STRING: &str = "string_literal";
    pub const BYTE_STRING: &str = "byte_string_literal";
    pub const C_STRING: &str = "c_string_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
const OPERATORS: &[&str] = &[
    "...", "..=", "<<=", ">>=", "->", "=>", "::", "==", "!=", "<=", ">=", "&&", "||", "..", "+=",
    "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<", ">>",
];

const SINGLE_PUNCT: &str = "+-*/%!&|^<>=.,;:()[]{}@#?$~";

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
        // Shebang: only a leading `#!` that is not an inner attribute `#![`.
        if self.src.starts_with("#!") && self.src.as_bytes().get(2) != Some(&b'[') {
            let end = self.find_line_end(2);
            self.push(kind::SHEBANG, 0, end, true);
            self.pos = end;
        }

        while self.pos < self.bytes.len() {
            let start = self.pos;
            let c = self.peek();
            match c {
                c if c == ' ' || c == '\t' || c == '\n' || c == '\r' || c.is_whitespace() => {
                    self.eat_while(|c| c.is_whitespace());
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                '/' if self.peek_at(1) == Some('/') => self.line_comment(start),
                '/' if self.peek_at(1) == Some('*') => self.block_comment(start),
                '"' => self.string_literal(start, kind::STRING, 1),
                '\'' => self.char_or_lifetime(start),
                'r' if matches!(self.peek_at(1), Some('"') | Some('#')) => {
                    self.raw_string(start, kind::STRING, 1)
                }
                'b' if self.peek_at(1) == Some('\'') => self.byte_char(start),
                'b' if self.peek_at(1) == Some('"') => {
                    self.bump(); // b
                    self.string_literal(start, kind::BYTE_STRING, 1)
                }
                'b' if self.peek_at(1) == Some('r')
                    && matches!(self.peek_at(2), Some('"') | Some('#')) =>
                {
                    self.bump(); // b
                    self.raw_string(start, kind::BYTE_STRING, 1)
                }
                'c' if self.peek_at(1) == Some('"') => {
                    self.bump(); // c
                    self.string_literal(start, kind::C_STRING, 1)
                }
                'c' if self.peek_at(1) == Some('r')
                    && matches!(self.peek_at(2), Some('"') | Some('#')) =>
                {
                    self.bump(); // c
                    self.raw_string(start, kind::C_STRING, 1)
                }
                'r' if self.peek_at(1) == Some('#') && starts_ident(self.peek_at(2)) => {
                    self.raw_ident(start)
                }
                c if is_ident_start(c) => self.ident(start),
                c if c.is_ascii_digit() => self.number(start),
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

    fn block_comment(&mut self, start: usize) {
        // Rust block comments nest.
        self.pos += 2; // /*
        let mut depth = 1usize;
        while self.pos < self.bytes.len() && depth > 0 {
            if self.src[self.pos..].starts_with("/*") {
                depth += 1;
                self.pos += 2;
            } else if self.src[self.pos..].starts_with("*/") {
                depth -= 1;
                self.pos += 2;
            } else {
                self.bump();
            }
        }
        // Unterminated block comment is still trivia covering to EOF — lossless.
        self.push(kind::BLOCK_COMMENT, start, self.pos, true);
    }

    fn ident(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        self.push(kind::IDENT, start, self.pos, false);
    }

    fn raw_ident(&mut self, start: usize) {
        self.pos += 2; // r#
        self.eat_while(is_ident_continue);
        self.push(kind::RAW_IDENT, start, self.pos, false);
    }

    fn char_or_lifetime(&mut self, start: usize) {
        // `'` may begin a char literal or a lifetime/label.
        let after = self.peek_at(1);
        if starts_ident(after) {
            // `'x'` is a char literal; `'a`, `'static`, `'_` are lifetimes. The
            // discriminator is whether a closing quote immediately follows the
            // single identifier-start char.
            let id_char_len = after.map(|c| c.len_utf8()).unwrap_or(0);
            let next = self.src[start + 1 + id_char_len..].chars().next();
            if next == Some('\'') {
                return self.char_literal(start, kind::CHAR);
            }
            // Lifetime / label: `'` then ident-continue chars.
            self.bump(); // '
            self.eat_while(is_ident_continue);
            self.push(kind::LIFETIME, start, self.pos, false);
            return;
        }
        self.char_literal(start, kind::CHAR);
    }

    fn byte_char(&mut self, start: usize) {
        self.bump(); // b
        self.char_literal(start, kind::BYTE);
    }

    /// Scan a `'...'` literal body (already positioned at the opening `'` for
    /// chars, or just past `b` for byte chars). Handles escapes; an unterminated
    /// literal becomes an error token over what was consumed.
    fn char_literal(&mut self, start: usize, kind: &'static str) {
        // Consume opening quote.
        self.bump();
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
        let token_kind = if terminated { kind } else { kind::ERROR };
        self.push(token_kind, start, self.pos, false);
    }

    /// Scan a `"..."` literal. `prefix_consumed` records bytes already eaten
    /// (e.g. the `b`/`c` prefix) for span bookkeeping only.
    fn string_literal(&mut self, start: usize, kind: &'static str, _prefix_consumed: usize) {
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
            } else {
                self.bump();
            }
        }
        // Optional suffix (e.g. none for strings, but stay permissive).
        let token_kind = if terminated { kind } else { kind::ERROR };
        self.push(token_kind, start, self.pos, false);
    }

    /// Scan a raw string `r"..."`, `r#"..."#`, … positioned at the `r`/`br`/`cr`
    /// prefix already (with byte/c prefix bumped by caller).
    fn raw_string(&mut self, start: usize, kind: &'static str, _prefix: usize) {
        self.bump(); // r
        let mut hashes = 0usize;
        while self.peek() == '#' {
            hashes += 1;
            self.bump();
        }
        if self.peek() != '"' {
            // Not actually a raw string after all — emit error over the prefix.
            self.push(kind::ERROR, start, self.pos, false);
            return;
        }
        self.bump(); // opening "
        let closing = format!("\"{}", "#".repeat(hashes));
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            if self.src[self.pos..].starts_with(&closing) {
                self.pos += closing.len();
                terminated = true;
                break;
            }
            self.bump();
        }
        let token_kind = if terminated { kind } else { kind::ERROR };
        self.push(token_kind, start, self.pos, false);
    }

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        if self.peek() == '0' {
            match self.peek_at(1) {
                Some('x') | Some('X') => {
                    self.pos += 2;
                    self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
                    self.eat_suffix();
                    return self.push(kind::INT, start, self.pos, false);
                }
                Some('o') | Some('O') => {
                    self.pos += 2;
                    self.eat_while(|c| ('0'..='7').contains(&c) || c == '_');
                    self.eat_suffix();
                    return self.push(kind::INT, start, self.pos, false);
                }
                Some('b') | Some('B') => {
                    self.pos += 2;
                    self.eat_while(|c| c == '0' || c == '1' || c == '_');
                    self.eat_suffix();
                    return self.push(kind::INT, start, self.pos, false);
                }
                _ => {}
            }
        }
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        // Fractional part only if a digit follows the dot — keeps `1..2` and
        // tuple access `x.0` lexing as expected.
        if self.peek() == '.' && self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) {
            is_float = true;
            self.bump(); // .
            self.eat_while(|c| c.is_ascii_digit() || c == '_');
        }
        // Exponent.
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
                self.bump(); // e
                if sign_len == 1 {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit() || c == '_');
            }
        }
        self.eat_suffix();
        let k = if is_float { kind::FLOAT } else { kind::INT };
        self.push(k, start, self.pos, false);
    }

    /// Numeric suffix is an identifier-continue run (e.g. `u32`, `f64`). A
    /// trailing `.` is never part of the suffix.
    fn eat_suffix(&mut self) {
        if starts_ident(Some(self.peek())) {
            self.eat_while(is_ident_continue);
        }
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

fn starts_ident(c: Option<char>) -> bool {
    c.map(is_ident_start).unwrap_or(false)
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
            "fn main() {}",
            "let x = 1.5e3;",
            "// comment\nlet y = 0xFF_u8;",
            "/* nested /* block */ */ x",
            "r#\"raw\"# 'a' 'static b\"bytes\" c\"cs\"",
            "#!/bin/sh\nfn x(){}",
            "1..2 x.0 1.method",
            "λ ☃ €", // non-ascii idents / unknowns still covered
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("fn add(a: i32) -> i32 { a }");
        assert!(t.contains(&(kind::IDENT, "fn".to_string())));
        assert!(t.contains(&(kind::PUNCT, "->".to_string())));
        assert!(is_keyword("fn"));
    }

    #[test]
    fn lifetime_vs_char() {
        let t = texts("'a 'static 'x'");
        assert!(t.contains(&(kind::LIFETIME, "'a".to_string())));
        assert!(t.contains(&(kind::LIFETIME, "'static".to_string())));
        assert!(t.contains(&(kind::CHAR, "'x'".to_string())));
    }

    #[test]
    fn raw_string_with_hashes() {
        let t = texts("r##\"a\"#b\"##");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "r##\"a\"#b\"##"));
    }

    #[test]
    fn ranges_do_not_eat_dots() {
        let t = texts("1..2");
        assert_eq!(
            t,
            vec![
                (kind::INT, "1".to_string()),
                (kind::PUNCT, "..".to_string()),
                (kind::INT, "2".to_string()),
            ]
        );
    }
}
