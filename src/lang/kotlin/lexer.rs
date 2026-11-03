//! Lossless Kotlin lexer, grounded in the Kotlin language specification's lexical
//! grammar.
//!
//! Guarantees (identical contract to the Rust and Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs, comments, the optional `#!` shebang of `.kts` scripts)
//!   are emitted as `trivia` tokens, never discarded. `NEWLINE` is emitted as a
//!   *non-trivia* token because Kotlin's semicolon inference makes line breaks
//!   structurally significant (they terminate statements, abstract members, and
//!   expression bodies). The parser derives statement boundaries from them.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//!
//! Kotlin specifics handled here:
//! - Nested block comments (`/* /* */ */`), like Rust.
//! - Three string forms: regular `"..."` (with `\` escapes), triple-quoted raw
//!   `"""..."""` spanning newlines, and `'c'` character literals. Both string
//!   forms carry `$name` / `${ expr }` interpolation; an interpolation block is
//!   scanned brace-balanced (iteratively, so hostile nesting cannot overflow)
//!   while treating any nested string as opaque, so an inner `"` cannot
//!   prematurely close the literal.
//! - Backtick-escaped identifiers (`` `is` ``, `` `weird name` ``) as `ident`.
//! - Numbers: decimal / `0x` hex / `0b` binary, `_` digit separators, fraction
//!   and exponent, and the `f`/`F`/`L`/`u`/`U` (and combination) suffixes.
//!
//! Coverage note (honest, mirroring the other front ends): identifier
//! start/continue uses `char::is_alphabetic` / `is_alphanumeric` plus `_` as a
//! pragmatic stand-in for the full Unicode identifier tables. Anything outside
//! still lands in the tree as a covered token, never dropped.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Kotlin hard keywords plus the modifier/soft keywords the lowering needs to
/// recognize so they are never mistaken for call targets. Like the Rust and
/// Python lexers, these all lex as `ident` tokens; the parser and lowering
/// distinguish them via [`is_keyword`].
pub const KEYWORDS: &[&str] = &[
    // Hard keywords.
    "as",
    "break",
    "class",
    "continue",
    "do",
    "else",
    "false",
    "for",
    "fun",
    "if",
    "in",
    "interface",
    "is",
    "null",
    "object",
    "package",
    "return",
    "super",
    "this",
    "throw",
    "true",
    "try",
    "typealias",
    "typeof",
    "val",
    "var",
    "when",
    "while",
    // Soft / modifier keywords.
    "by",
    "catch",
    "constructor",
    "delegate",
    "dynamic",
    "field",
    "file",
    "finally",
    "get",
    "import",
    "init",
    "param",
    "property",
    "receiver",
    "set",
    "setparam",
    "value",
    "where",
    "abstract",
    "annotation",
    "companion",
    "const",
    "crossinline",
    "data",
    "enum",
    "expect",
    "external",
    "final",
    "infix",
    "inline",
    "inner",
    "internal",
    "lateinit",
    "noinline",
    "open",
    "operator",
    "out",
    "override",
    "private",
    "protected",
    "public",
    "reified",
    "sealed",
    "suspend",
    "tailrec",
    "vararg",
    "actual",
];

pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.contains(&text)
}

/// Token kind labels, stored on the CST as `&'static str`.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const NEWLINE: &str = "newline";
    pub const LINE_COMMENT: &str = "line_comment";
    pub const BLOCK_COMMENT: &str = "block_comment";
    pub const SHEBANG: &str = "shebang";
    pub const IDENT: &str = "ident";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const CHAR: &str = "char_literal";
    pub const STRING: &str = "string_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
/// Kotlin has no bitwise symbol operators (`shl`/`and`/… are infix words), so
/// `<<`/`>>` are absent.
const OPERATORS: &[&str] = &[
    "===", "!==", "..<", "?:", "::", "->", "==", "!=", "<=", ">=", "&&", "||", "++", "--", "+=",
    "-=", "*=", "/=", "%=", "!!", "?.", "..",
];

const SINGLE_PUNCT: &str = "+-*/%=<>!&|?:.,;()[]{}@$~^#";

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
        // `.kts` scripts may begin with a `#!` shebang line.
        if self.src.starts_with("#!") {
            let end = self.find_line_end(0);
            self.push(kind::SHEBANG, 0, end, true);
            self.pos = end;
        }

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
                c if c != '\n' && c != '\r' && c.is_whitespace() => {
                    self.eat_while(|c| c != '\n' && c != '\r' && c.is_whitespace());
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                '/' if self.peek_at(1) == Some('/') => self.line_comment(start),
                '/' if self.peek_at(1) == Some('*') => self.block_comment(start),
                '"' if self.peek_at(1) == Some('"') && self.peek_at(2) == Some('"') => {
                    self.triple_string(start)
                }
                '"' => self.string(start),
                '\'' => self.char_literal(start),
                '`' => self.backtick_ident(start),
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
        // Kotlin block comments nest.
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
        // An unterminated block comment is still trivia covering to EOF.
        self.push(kind::BLOCK_COMMENT, start, self.pos, true);
    }

    fn ident(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        self.push(kind::IDENT, start, self.pos, false);
    }

    /// A backtick-escaped identifier `` `name` ``. Runs to the closing backtick
    /// on the same line; unterminated content becomes an `error` token.
    fn backtick_ident(&mut self, start: usize) {
        self.bump(); // opening `
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '`' {
                self.bump();
                terminated = true;
                break;
            } else if c == '\n' || c == '\r' {
                break;
            }
            self.bump();
        }
        let k = if terminated { kind::IDENT } else { kind::ERROR };
        self.push(k, start, self.pos, false);
    }

    /// Regular string `"..."`. Honors `\` escapes and `$name` / `${ expr }`
    /// interpolation. An unterminated literal (EOF or bare newline) becomes an
    /// `error` token over the bytes consumed.
    fn string(&mut self, start: usize) {
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
            } else if c == '\n' || c == '\r' {
                break; // unterminated single-line string ends at the newline
            } else if c == '$' && self.peek_at(1) == Some('{') {
                self.skip_interpolation();
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

    /// Triple-quoted raw string `"""..."""`. No escape processing; spans
    /// newlines; ends at the first `"""`. Supports `${ expr }` interpolation.
    fn triple_string(&mut self, start: usize) {
        self.pos += 3; // opening """
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            if self.src[self.pos..].starts_with("\"\"\"") {
                self.pos += 3;
                terminated = true;
                break;
            }
            if self.peek() == '$' && self.peek_at(1) == Some('{') {
                self.skip_interpolation();
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

    /// Skip a `${ ... }` interpolation block, cursor positioned at the `$`.
    /// Brace-balanced and fully iterative (no recursion) so deeply nested
    /// interpolation cannot overflow the stack. Nested string literals are
    /// treated as opaque content so their braces never affect the balance and an
    /// inner `"` cannot escape the block.
    fn skip_interpolation(&mut self) {
        self.bump(); // $
        self.bump(); // {
        let mut depth = 1i32;
        // 0 = code, 1 = inside a regular "string", 2 = inside a triple string.
        let mut mode = 0u8;
        while self.pos < self.bytes.len() && depth > 0 {
            match mode {
                0 => {
                    let c = self.peek();
                    if c == '{' {
                        depth += 1;
                        self.bump();
                    } else if c == '}' {
                        depth -= 1;
                        self.bump();
                    } else if c == '"' {
                        if self.peek_at(1) == Some('"') && self.peek_at(2) == Some('"') {
                            self.pos += 3;
                            mode = 2;
                        } else {
                            self.bump();
                            mode = 1;
                        }
                    } else if c == '\'' {
                        // A char literal: skip its escaped body.
                        self.bump();
                        while self.pos < self.bytes.len() {
                            let d = self.peek();
                            if d == '\\' {
                                self.bump();
                                if self.pos < self.bytes.len() {
                                    self.bump();
                                }
                            } else if d == '\'' || d == '\n' {
                                self.bump();
                                break;
                            } else {
                                self.bump();
                            }
                        }
                    } else {
                        self.bump();
                    }
                }
                1 => {
                    let c = self.peek();
                    if c == '\\' {
                        self.bump();
                        if self.pos < self.bytes.len() {
                            self.bump();
                        }
                    } else if c == '"' {
                        self.bump();
                        mode = 0;
                    } else if c == '\n' || c == '\r' {
                        mode = 0; // unterminated nested string; bail back to code
                    } else {
                        self.bump();
                    }
                }
                _ => {
                    if self.src[self.pos..].starts_with("\"\"\"") {
                        self.pos += 3;
                        mode = 0;
                    } else {
                        self.bump();
                    }
                }
            }
        }
    }

    /// A `'...'` character literal, cursor at the opening quote. Handles escapes;
    /// an unterminated literal becomes an `error` token.
    fn char_literal(&mut self, start: usize) {
        self.bump(); // '
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
        let k = if terminated { kind::CHAR } else { kind::ERROR };
        self.push(k, start, self.pos, false);
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
        // Fraction only if a digit follows the dot, so `1..2` and `1.toString()`
        // keep lexing as expected.
        if self.peek() == '.' && self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) {
            is_float = true;
            self.bump(); // .
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
                self.bump(); // e
                if sign_len == 1 {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit() || c == '_');
            }
        }
        // A trailing `f`/`F` makes the literal a float; `L`/`u`/`U` keep it an int.
        if matches!(self.peek(), 'f' | 'F') {
            is_float = true;
        }
        self.eat_suffix();
        let k = if is_float { kind::FLOAT } else { kind::INT };
        self.push(k, start, self.pos, false);
    }

    /// A numeric suffix is an identifier-continue run (`L`, `f`, `uL`, …). A
    /// trailing `.` is never part of the suffix.
    fn eat_suffix(&mut self) {
        if is_ident_start(self.peek()) {
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
            "fun main() {}\n",
            "val x = 0xFF_00 + 1.5e3 + 42L + 3.14f\n",
            "// line\n/* nested /* block */ */ class C\n",
            "val s = \"hi $name and ${greet(\"x\")}!\"\n",
            "val t = \"\"\"multi\nline ${expr}\"\"\"\n",
            "val c = 'a'; val n = '\\n'\n",
            "`weird name`.foo()\n",
            "a ?: b?.c !! d ..< e\n",
            "λ = '☃ €' // unicode\n",
            "#!/usr/bin/env kotlin\nprintln(1)\n",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("fun add(a: Int, b: Int): Int = a + b\n");
        assert!(t.contains(&(kind::IDENT, "fun".to_string())));
        assert!(t.contains(&(kind::IDENT, "add".to_string())));
        assert!(t.contains(&(kind::PUNCT, "(".to_string())));
        assert!(t.iter().any(|(k, _)| *k == kind::NEWLINE));
        assert!(is_keyword("fun"));
        assert!(is_keyword("class"));
        assert!(!is_keyword("add"));
    }

    #[test]
    fn interpolation_with_nested_string_is_one_token() {
        let t = texts("\"a ${f(\"x\")} b\"");
        assert!(
            t.iter()
                .any(|(k, s)| *k == kind::STRING && s == "\"a ${f(\"x\")} b\""),
            "interpolated string with a nested string literal must be one token: {t:?}"
        );
    }

    #[test]
    fn triple_string_spans_newlines() {
        let t = texts("\"\"\"a\nb\nc\"\"\"");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "\"\"\"a\nb\nc\"\"\""));
    }

    #[test]
    fn numbers() {
        let t = texts("0b1010 0xAF 10_000 3.14 2e10 42L 3.14f 7u");
        assert!(t.contains(&(kind::INT, "0b1010".to_string())));
        assert!(t.contains(&(kind::INT, "0xAF".to_string())));
        assert!(t.contains(&(kind::INT, "10_000".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14".to_string())));
        assert!(t.contains(&(kind::INT, "42L".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14f".to_string())));
        assert!(t.contains(&(kind::INT, "7u".to_string())));
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

    #[test]
    fn elvis_and_safe_call_operators() {
        let t = texts("a?.b ?: c");
        assert!(t.contains(&(kind::PUNCT, "?.".to_string())));
        assert!(t.contains(&(kind::PUNCT, "?:".to_string())));
    }

    #[test]
    fn backtick_identifier() {
        let t = texts("`is`(x)");
        assert!(t.contains(&(kind::IDENT, "`is`".to_string())));
    }
}
