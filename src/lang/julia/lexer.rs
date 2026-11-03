//! Lossless Julia lexer, grounded in the Julia manual's lexical grammar.
//!
//! Guarantees (identical contract to the Rust, Lua, and Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs, newlines, `#` line comments, `#= … =#` block comments
//!   which **nest**) are emitted as `trivia` tokens, not discarded. Julia is
//!   *not* whitespace-significant for block structure (blocks are `keyword … end`),
//!   so a newline is ordinary `newline` trivia; the parser uses it only as a soft
//!   statement-separator heuristic.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped — an unterminated string or comment
//!   is emitted as a token spanning to end of input.
//!
//! Progress guard: the main run loop asserts forward motion on every iteration —
//! if a scanner ever failed to advance `pos`, one char is consumed as an `error`
//! token rather than spinning forever (a non-advancing loop is an OOM). The
//! nested block-comment scanner and the string/command scanners likewise advance
//! on every character they inspect.
//!
//! Julia-specific surface the lexer covers:
//! - `#` line comments and nested `#= … =#` block comments.
//! - Strings: `"…"`, triple `"""…"""` (spanning newlines), with `\` escapes and
//!   `$name` / `$(…)` interpolation (the `$(…)` body is consumed with balanced
//!   parens — a documented breadth gap: a `)` inside a string *inside* the
//!   interpolation is not specially handled).
//! - Command literals: `` `…` `` and triple ``` ```…``` ```.
//! - Char literals `'x'` / `'\n'`, disambiguated from the postfix transpose
//!   operator `'` (which follows a value) via a running "previous was a value"
//!   flag — the mirror of the Rust lexer's char-vs-lifetime split.
//! - Numbers: decimal, `0x` hex (incl. hex floats `0x1.8p3`), `0o` octal, `0b`
//!   binary, decimal floats with exponents (`1.5e-3`), and `_` digit separators.
//!   The rational operator `//` is lexed as an operator between two ints, not as
//!   part of a numeral.
//! - Macros `@name` are lexed as a single `macro_name` token.
//! - A pragmatic set of ASCII multi-char operators (including broadcast `.`
//!   forms, `<:`, `>:`, `::`, `->`, `===`, `!==`, …).
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_` (and `!` as an identifier-continue, per Julia's
//! `push!`-style names) as a pragmatic superset of Julia's Unicode rule.
//! Non-ASCII *operator* symbols (e.g. `∈`, `≤`, `→`) are not in the punctuation
//! set and land in the tree as `error` tokens — covered, never dropped, but a
//! known classification gap.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Julia reserved words. Like the other lexers these lex as `ident` tokens; the
/// parser distinguishes them via [`is_keyword`].
pub const KEYWORDS: &[&str] = &[
    "baremodule",
    "begin",
    "break",
    "catch",
    "const",
    "continue",
    "do",
    "else",
    "elseif",
    "end",
    "export",
    "false",
    "finally",
    "for",
    "function",
    "global",
    "if",
    "import",
    "in",
    "isa",
    "let",
    "local",
    "macro",
    "module",
    "mutable",
    "primitive",
    "quote",
    "return",
    "struct",
    "true",
    "try",
    "type",
    "using",
    "where",
    "while",
];

pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.contains(&text)
}

/// Token kind labels. Stored on the CST as `&'static str`.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const NEWLINE: &str = "newline";
    pub const LINE_COMMENT: &str = "line_comment";
    pub const BLOCK_COMMENT: &str = "block_comment";
    pub const IDENT: &str = "ident";
    pub const MACRO_NAME: &str = "macro_name";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const STRING: &str = "string_literal";
    pub const CHAR: &str = "char_literal";
    pub const CMD: &str = "command_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
const OPERATORS: &[&str] = &[
    ">>>=", "<<=", ">>=", ">>>", "...", "===", "!==", "//=", "÷=", ".//", ".==", ".!=", ".<=",
    ".>=", ".^", ".+", ".-", ".*", "./", ".\\", ".%", ".=", "->", "=>", "<:", ">:", "::", "==",
    "!=", "<=", ">=", "&&", "||", "<<", ">>", "//", "+=", "-=", "*=", "/=", "^=", "%=", "\\=",
    "&=", "|=", "~=", "..",
];

// Note: `'` is included so the postfix transpose operator (reached only when the
// preceding token closed a value, i.e. the char-literal arm did not fire) lexes
// as punctuation rather than an error token.
const SINGLE_PUNCT: &str = "+-*/\\%^!&|~<>=(){}[];:,.?$'";

pub fn lex(source: &str) -> Vec<Token> {
    Lexer::new(source).run()
}

struct Lexer<'s> {
    src: &'s str,
    bytes: &'s [u8],
    pos: usize,
    tokens: Vec<Token>,
    /// True when the previously emitted significant token closes a value, so a
    /// following `'` is the postfix transpose operator rather than a char literal.
    prev_value: bool,
}

impl<'s> Lexer<'s> {
    fn new(src: &'s str) -> Self {
        Lexer {
            src,
            bytes: src.as_bytes(),
            pos: 0,
            tokens: Vec::new(),
            prev_value: false,
        }
    }

    fn run(mut self) -> Vec<Token> {
        while self.pos < self.bytes.len() {
            let start = self.pos;
            let c = self.peek();
            match c {
                '\n' => {
                    self.bump();
                    self.push(kind::NEWLINE, start, self.pos, true);
                }
                '\r' => {
                    self.bump();
                    if self.peek() == '\n' {
                        self.bump();
                    }
                    self.push(kind::NEWLINE, start, self.pos, true);
                }
                ' ' | '\t' | '\x0b' | '\x0c' => {
                    self.eat_while(|c| matches!(c, ' ' | '\t' | '\x0b' | '\x0c'));
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                '#' if self.peek_at(1) == Some('=') => self.block_comment(start),
                '#' => self.line_comment(start),
                '"' => self.string_literal(start),
                '`' => self.command_literal(start),
                '\'' if !self.prev_value => self.char_literal(start),
                '@' if starts_ident(self.peek_at(1)) => self.macro_name(start),
                c if c.is_ascii_digit() => self.number(start),
                '.' if self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) => {
                    self.number(start)
                }
                c if is_ident_start(c) => self.ident(start),
                c if SINGLE_PUNCT.contains(c) => self.punct(start),
                _ => {
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }

            // Progress guard: a non-advancing iteration would loop forever (OOM).
            // No scanner above can leave `pos` unmoved, but defend anyway.
            if self.pos == start {
                self.bump();
                if self.pos == start {
                    // Truly stuck (empty remainder mid-string is impossible, but
                    // guarantee termination regardless).
                    self.pos = self.bytes.len();
                }
                self.push(kind::ERROR, start, self.pos, false);
            }
        }
        self.tokens
    }

    // --- scanners -----------------------------------------------------------

    fn line_comment(&mut self, start: usize) {
        let end = self.find_line_end(self.pos);
        self.pos = end;
        self.push(kind::LINE_COMMENT, start, end, true);
    }

    /// A `#= … =#` block comment. These **nest**, so track depth. Advances on
    /// every character; an unterminated comment runs to EOF (still trivia, still
    /// fully covered → lossless).
    fn block_comment(&mut self, start: usize) {
        self.pos += 2; // #=
        let mut depth = 1usize;
        while self.pos < self.bytes.len() && depth > 0 {
            if self.src[self.pos..].starts_with("#=") {
                depth += 1;
                self.pos += 2;
            } else if self.src[self.pos..].starts_with("=#") {
                depth -= 1;
                self.pos += 2;
            } else {
                self.bump();
            }
        }
        self.push(kind::BLOCK_COMMENT, start, self.pos, true);
    }

    fn ident(&mut self, start: usize) {
        // Julia identifiers allow a trailing `!` (`push!`, `sort!`), but `!=` is
        // an operator — so consume `!` only when it is not part of `!=`.
        self.bump(); // start char (already ident-start)
        loop {
            let c = self.peek();
            // ident-continue, or a trailing `!` that isn't the `!=` operator.
            if c == '_' || c.is_alphanumeric() || (c == '!' && self.peek_at(1) != Some('=')) {
                self.bump();
            } else {
                break;
            }
        }
        self.push(kind::IDENT, start, self.pos, false);
        // A following `'` is the transpose operator only after a *value*. Most
        // keywords are not values (so `if 'c'` lexes `'c'` as a char literal), but
        // `true`/`false`/`end` are, so a `'` after them is transpose.
        let text = &self.src[start..self.pos];
        let is_value = !is_keyword(text) || matches!(text, "true" | "false" | "end");
        self.set_prev_value(is_value);
    }

    /// `@name` macro identifier (the `@` plus an identifier run).
    fn macro_name(&mut self, start: usize) {
        self.bump(); // @
        self.eat_while(|c| c == '_' || c == '!' || c.is_alphanumeric());
        self.push(kind::MACRO_NAME, start, self.pos, false);
        self.set_prev_value(true);
    }

    /// A `"…"` or triple `"""…"""` string with `\` escapes and `$` interpolation.
    fn string_literal(&mut self, start: usize) {
        let triple = self.src[self.pos..].starts_with("\"\"\"");
        if triple {
            self.pos += 3;
        } else {
            self.bump(); // opening "
        }
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            if triple {
                if self.src[self.pos..].starts_with("\"\"\"") {
                    self.pos += 3;
                    terminated = true;
                    break;
                }
            } else if self.peek() == '"' {
                self.bump();
                terminated = true;
                break;
            }
            let c = self.peek();
            if c == '\\' {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
                continue;
            }
            if c == '$' {
                self.bump(); // $
                if self.peek() == '(' {
                    self.consume_balanced_parens();
                }
                continue;
            }
            if !triple && (c == '\n' || c == '\r') {
                // A raw newline ends an unterminated single-line string.
                break;
            }
            self.bump();
        }
        let token_kind = if terminated {
            kind::STRING
        } else {
            kind::ERROR
        };
        self.push(token_kind, start, self.pos, false);
        self.set_prev_value(true);
    }

    /// A `` `…` `` or triple ``` ```…``` ``` command literal.
    fn command_literal(&mut self, start: usize) {
        let triple = self.src[self.pos..].starts_with("```");
        if triple {
            self.pos += 3;
        } else {
            self.bump(); // opening `
        }
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            if triple {
                if self.src[self.pos..].starts_with("```") {
                    self.pos += 3;
                    terminated = true;
                    break;
                }
            } else if self.peek() == '`' {
                self.bump();
                terminated = true;
                break;
            }
            let c = self.peek();
            if c == '\\' {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
                continue;
            }
            if c == '$' {
                self.bump();
                if self.peek() == '(' {
                    self.consume_balanced_parens();
                }
                continue;
            }
            if !triple && (c == '\n' || c == '\r') {
                break;
            }
            self.bump();
        }
        let token_kind = if terminated { kind::CMD } else { kind::ERROR };
        self.push(token_kind, start, self.pos, false);
        self.set_prev_value(true);
    }

    /// Consume a balanced `( … )` run, cursor positioned at the opening `(`. Used
    /// for `$( … )` string/command interpolation. Advances on every character.
    fn consume_balanced_parens(&mut self) {
        if self.peek() != '(' {
            return;
        }
        self.bump(); // (
        let mut depth = 1usize;
        while self.pos < self.bytes.len() && depth > 0 {
            let c = self.peek();
            if c == '(' {
                depth += 1;
            } else if c == ')' {
                depth -= 1;
            }
            self.bump();
        }
    }

    /// A `'x'` / `'\n'` char literal. Caller has already decided (via
    /// `prev_value`) that this `'` is not the transpose operator. An unterminated
    /// literal (newline / EOF before the closing quote) becomes an `error` token.
    fn char_literal(&mut self, start: usize) {
        self.bump(); // opening '
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
            if c == '\'' {
                self.bump();
                terminated = true;
                break;
            }
            if c == '\n' || c == '\r' {
                break;
            }
            self.bump();
        }
        let token_kind = if terminated { kind::CHAR } else { kind::ERROR };
        self.push(token_kind, start, self.pos, false);
        self.set_prev_value(true);
    }

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        if self.peek() == '0' {
            match self.peek_at(1) {
                Some('x') | Some('X') => {
                    self.pos += 2;
                    self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
                    if self.peek() == '.' {
                        is_float = true;
                        self.bump();
                        self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
                    }
                    if matches!(self.peek(), 'p' | 'P') {
                        is_float = true;
                        self.bump();
                        if matches!(self.peek(), '+' | '-') {
                            self.bump();
                        }
                        self.eat_while(|c| c.is_ascii_digit() || c == '_');
                    }
                    let k = if is_float { kind::FLOAT } else { kind::INT };
                    self.push(k, start, self.pos, false);
                    self.set_prev_value(true);
                    return;
                }
                Some('o') | Some('O') => {
                    self.pos += 2;
                    self.eat_while(|c| ('0'..='7').contains(&c) || c == '_');
                    self.push(kind::INT, start, self.pos, false);
                    self.set_prev_value(true);
                    return;
                }
                Some('b') | Some('B') => {
                    self.pos += 2;
                    self.eat_while(|c| c == '0' || c == '1' || c == '_');
                    self.push(kind::INT, start, self.pos, false);
                    self.set_prev_value(true);
                    return;
                }
                _ => {}
            }
        }
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        // Fractional part only when a digit follows the dot, so `1:2` ranges and
        // field access stay separate tokens.
        if self.peek() == '.' && self.peek_at(1).map(is_after_dot_digit).unwrap_or(false) {
            is_float = true;
            self.bump(); // .
            self.eat_while(|c| c.is_ascii_digit() || c == '_');
        } else if self.peek() == '.' && !self.peek_at(1).map(is_dot_continue).unwrap_or(false) {
            // A trailing dot float like `1.` (not `1..` range, not `1.foo`).
            is_float = true;
            self.bump();
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
        let k = if is_float { kind::FLOAT } else { kind::INT };
        self.push(k, start, self.pos, false);
        self.set_prev_value(true);
    }

    fn punct(&mut self, start: usize) {
        for op in OPERATORS {
            if self.src[self.pos..].starts_with(op) {
                self.pos += op.len();
                self.push(kind::PUNCT, start, self.pos, false);
                self.set_prev_value(closes_value(op));
                return;
            }
        }
        let c = self.peek();
        self.bump();
        self.push(kind::PUNCT, start, self.pos, false);
        let text = &self.src[start..self.pos];
        // Closers and the transpose operator close a value; openers/operators do
        // not (so a following `'` is a char literal after `(`, `=`, `,`, …).
        self.set_prev_value(matches!(c, ')' | ']' | '}' | '\'') || closes_value(text));
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
        match self.src[from..].find(['\n', '\r']) {
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

    /// Update the value-context flag (trivia tokens never change it).
    fn set_prev_value(&mut self, v: bool) {
        self.prev_value = v;
    }
}

fn is_ident_start(c: char) -> bool {
    c == '_' || c.is_alphabetic()
}

fn starts_ident(c: Option<char>) -> bool {
    c.map(is_ident_start).unwrap_or(false)
}

/// A digit immediately after a `.` makes a fraction (`1.5`).
fn is_after_dot_digit(c: char) -> bool {
    c.is_ascii_digit()
}

/// Characters after a `.` that mean the dot is *not* a trailing-float dot:
/// another `.` (range/`..`) or an identifier/`(` (field access / call).
fn is_dot_continue(c: char) -> bool {
    c == '.' || c == '_' || c == '(' || c.is_alphabetic()
}

/// Whether an operator text closes a value (so a following `'` is transpose).
/// Only the postfix `...` splat does among multi-char operators; assignment and
/// binary operators expect a right operand.
fn closes_value(op: &str) -> bool {
    op == "..."
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
            "function f(x)\n  return x\nend\n",
            "# line comment\nx = 1\n",
            "#= block #= nested =# still =# y = 2\n",
            "s = \"\"\"triple\nstring $(a + b)\"\"\" * \"x\\n\"\n",
            "n = 0xFF + 0x1.8p3 + 1.5e-3 + 3 // 4 + 0o17 + 0b101\n",
            "c = 'a'; d = '\\n'; M = A'\n",
            "@assert x > 0\n",
            "v = [1, 2, 3]; t = (1, 2); d = Dict{Int,String}()\n",
            "push!(xs, 1)\n",
            "λ = '☃'  # unicode\n",
            "",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("function add(a, b)\n  return a + b\nend\n");
        assert!(t.contains(&(kind::IDENT, "function".to_string())));
        assert!(t.contains(&(kind::IDENT, "add".to_string())));
        assert!(t.contains(&(kind::PUNCT, "(".to_string())));
        assert!(t.iter().any(|(k, _)| *k == kind::NEWLINE));
        assert!(is_keyword("function"));
        assert!(is_keyword("end"));
        assert!(!is_keyword("add"));
    }

    #[test]
    fn nested_block_comments() {
        let t = texts("#= a #= b =# c =# x");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::BLOCK_COMMENT && s == "#= a #= b =# c =#"));
        assert!(t.contains(&(kind::IDENT, "x".to_string())));
    }

    #[test]
    fn transpose_vs_char() {
        // `A'` is transpose (A is a value); `'x'` standalone is a char literal.
        let t = texts("A' + 'x'");
        assert!(t.contains(&(kind::CHAR, "'x'".to_string())));
        // The transpose apostrophe is a single punct token.
        assert!(t.contains(&(kind::PUNCT, "'".to_string())));
    }

    #[test]
    fn bang_in_identifier_but_not_neq() {
        let t = texts("push!(x)");
        assert!(t.contains(&(kind::IDENT, "push!".to_string())));
        let t = texts("a!=b");
        assert!(t.contains(&(kind::IDENT, "a".to_string())));
        assert!(t.contains(&(kind::PUNCT, "!=".to_string())));
    }

    #[test]
    fn macro_name_is_one_token() {
        let t = texts("@inbounds y[i]");
        assert!(t.contains(&(kind::MACRO_NAME, "@inbounds".to_string())));
    }

    #[test]
    fn numbers() {
        let t = texts("0xFF 0o17 0b101 10 3.14 1.5e-3 .5 1//2");
        assert!(t.contains(&(kind::INT, "0xFF".to_string())));
        assert!(t.contains(&(kind::INT, "0o17".to_string())));
        assert!(t.contains(&(kind::INT, "0b101".to_string())));
        assert!(t.contains(&(kind::INT, "10".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14".to_string())));
        assert!(t.contains(&(kind::FLOAT, "1.5e-3".to_string())));
        assert!(t.contains(&(kind::FLOAT, ".5".to_string())));
        // `1//2` is `1`, `//`, `2` (rational operator).
        assert!(t.contains(&(kind::INT, "1".to_string())));
        assert!(t.contains(&(kind::PUNCT, "//".to_string())));
    }

    #[test]
    fn unterminated_string_is_error_but_covered() {
        let src = "x = \"open\n";
        let t = texts(src);
        assert!(t.iter().any(|(k, _)| *k == kind::ERROR));
        assert!(covers_all(src));
    }

    #[test]
    fn operators() {
        let t = texts("a <: b >: c :: d -> e => f === g !== h .+ i .== j");
        for op in ["<:", ">:", "::", "->", "=>", "===", "!==", ".+", ".=="] {
            assert!(
                t.contains(&(kind::PUNCT, op.to_string())),
                "missing operator {op}"
            );
        }
    }
}
