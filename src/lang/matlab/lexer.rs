//! Lossless MATLAB lexer.
//!
//! Guarantees (identical contract to the Rust, Julia, Python, and Fortran
//! lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs, newlines, `%` line comments, `%{ … %}` block
//!   comments, and `...` line continuations) are emitted as `trivia` tokens,
//!   never discarded.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped — an unterminated string or block
//!   comment is emitted as a token spanning to end of input.
//!
//! Progress guard: the main run loop asserts forward motion on every iteration —
//! if a scanner ever failed to advance `pos`, one byte is consumed as an `error`
//! token rather than spinning forever (a non-advancing loop is an OOM). Every
//! scanner advances on each character it inspects.
//!
//! ## The apostrophe hazard (the central MATLAB lexing problem)
//!
//! `'` is overloaded: it both delimits a single-quoted char array (`'text'`)
//! **and** is the postfix complex-conjugate transpose operator (`A'`). They are
//! disambiguated by *context*: an apostrophe that immediately follows a value —
//! an identifier, `)`, `]`, `}`, a numeric literal, a string/char literal, or a
//! preceding transpose `'`/`.'` — is the transpose operator (lexed as `punct`);
//! otherwise it opens a char literal. This mirrors the Julia lexer's
//! char-vs-transpose split and the Rust lexer's char-vs-lifetime split. Get this
//! wrong and code gets swallowed as a string, so the `prev_value` flag below is
//! load-bearing. A real newline resets `prev_value` (a MATLAB statement ends at
//! the newline, so a leading `'` on the next line opens a string), but a `...`
//! continuation does **not** (it joins the two physical lines).
//!
//! MATLAB-specific surface the lexer covers:
//! - `%` line comments and `%{ … %}` block comments. Per the MATLAB rule, a
//!   block comment opens only when `%{` is alone on its line (preceded by nothing
//!   but whitespace, followed by nothing but whitespace); otherwise `%{` is an
//!   ordinary line comment. Block comments nest (each line that is just `%{`
//!   opens a level, each `%}` closes one) and run to EOF if unterminated.
//! - `...` line continuation: the `...` plus the rest of the physical line and
//!   its newline are one `line_continuation` trivia token (so the logical
//!   statement continues).
//! - Single-quoted char arrays `'…'` with `''` as an escaped quote, and
//!   double-quoted strings `"…"` with `""` as an escaped quote. (MATLAB has no
//!   backslash escapes in either form — `\` is a literal byte.)
//! - Numbers: decimal, `0x` hex, `0b` binary, decimal floats with `e`/`E`
//!   exponents, and a trailing imaginary `i`/`j` suffix.
//! - A pragmatic ASCII operator set including the element-wise dotted forms
//!   (`.^`, `.*`, `./`, `.\`), the non-conjugate transpose `.'`, comparisons,
//!   the short-circuit `&&`/`||`, and the R2021b compound assignments
//!   (`+=`, `-=`, `*=`, `/=`, `^=`).
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_` as a pragmatic superset of MATLAB's ASCII-only
//! identifier rule. A leading `!` (the shell-escape `!command`) is lexed as an
//! ordinary `punct`, not specially consumed to end of line — a documented gap.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// MATLAB reserved words. Like the other lexers these lex as `ident` tokens; the
/// parser distinguishes them via [`is_keyword`].
pub const KEYWORDS: &[&str] = &[
    "break",
    "case",
    "catch",
    "classdef",
    "continue",
    "else",
    "elseif",
    "end",
    "enumeration",
    "events",
    "for",
    "function",
    "global",
    "if",
    "import",
    "methods",
    "otherwise",
    "parfor",
    "persistent",
    "properties",
    "return",
    "spmd",
    "switch",
    "try",
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
    pub const CONTINUATION: &str = "line_continuation";
    pub const IDENT: &str = "ident";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const STRING: &str = "string_literal";
    pub const CHAR: &str = "char_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
const OPERATORS: &[&str] = &[
    "...", ".^", ".*", "./", ".\\", ".'", "==", "~=", "<=", ">=", "&&", "||", "+=", "-=", "*=",
    "/=", "^=",
];

// Note: `'` is included so the postfix transpose operator (reached only when the
// preceding token closed a value, i.e. the char-literal arm did not fire) lexes
// as punctuation rather than an error token.
const SINGLE_PUNCT: &str = "+-*/\\^~<>=(){}[];:,.?@'&|!";

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
                    // A statement ends at a real newline: the next `'` opens a
                    // char array, not a transpose.
                    self.prev_value = false;
                }
                '\r' => {
                    self.bump();
                    if self.peek() == '\n' {
                        self.bump();
                    }
                    self.push(kind::NEWLINE, start, self.pos, true);
                    self.prev_value = false;
                }
                ' ' | '\t' | '\x0b' | '\x0c' => {
                    self.eat_while(|c| matches!(c, ' ' | '\t' | '\x0b' | '\x0c'));
                    self.push(kind::WHITESPACE, start, self.pos, true);
                    // Whitespace does not reset value context: `A '` is still a
                    // transpose of `A` (a documented pragmatic choice).
                }
                // `...` line continuation: the dots, the rest of the physical
                // line, and its newline form one trivia token that joins lines.
                '.' if self.src[self.pos..].starts_with("...") => self.continuation(start),
                // `%{` alone on its line opens a (nesting) block comment; any
                // other `%` is a line comment.
                '%' if self.peek_at(1) == Some('{') && self.block_comment_opener() => {
                    self.block_comment(start)
                }
                '%' => self.line_comment(start),
                '"' => self.string_literal(start),
                '\'' if !self.prev_value => self.char_literal(start),
                c if c.is_ascii_digit() => self.number(start),
                '.' if self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) => {
                    self.number(start)
                }
                c if is_ident_start(c) => self.ident(start),
                c if SINGLE_PUNCT.contains(c) => self.punct(start),
                _ => {
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                    self.prev_value = false;
                }
            }

            // Progress guard: a non-advancing iteration would loop forever (OOM).
            // No scanner above can leave `pos` unmoved, but defend anyway.
            if self.pos == start {
                self.bump();
                if self.pos == start {
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

    /// True when the `%{` at the cursor is alone on its line: only whitespace
    /// precedes it on the line and only whitespace follows the `{` before the
    /// line break. This is MATLAB's rule for opening a real block comment.
    fn block_comment_opener(&self) -> bool {
        // Everything before `%` on this line must be whitespace.
        let mut b = self.pos;
        while b > 0 {
            let ch = self.bytes[b - 1];
            if ch == b'\n' || ch == b'\r' {
                break;
            }
            if ch != b' ' && ch != b'\t' {
                return false;
            }
            b -= 1;
        }
        // Everything after `%{` on this line must be whitespace.
        let after = self.pos + 2; // past "%{"
        let line_end = self.find_line_end(after);
        self.src[after..line_end]
            .bytes()
            .all(|c| c == b' ' || c == b'\t')
    }

    /// A `%{ … %}` block comment. Opener and closer markers must each be alone on
    /// their line; markers nest. Advances line by line; an unterminated comment
    /// runs to EOF (still trivia, still fully covered → lossless).
    fn block_comment(&mut self, start: usize) {
        let mut depth: usize = 0;
        while self.pos < self.bytes.len() {
            let line_start = self.pos;
            let line_end = self.find_line_end(self.pos);
            let trimmed = self.src[line_start..line_end].trim_matches(|c| c == ' ' || c == '\t');
            if trimmed == "%{" {
                depth += 1;
            } else if trimmed == "%}" {
                depth = depth.saturating_sub(1);
            }
            // Advance past this line including its newline.
            self.pos = self.consume_newline_at(line_end);
            if depth == 0 {
                break;
            }
        }
        self.push(kind::BLOCK_COMMENT, start, self.pos, true);
        self.prev_value = false;
    }

    /// `...` continuation: consume the dots, the trailing line content, and the
    /// newline as one trivia token. `prev_value` is intentionally left unchanged
    /// — the logical statement spans the join.
    fn continuation(&mut self, start: usize) {
        let line_end = self.find_line_end(self.pos);
        self.pos = self.consume_newline_at(line_end);
        self.push(kind::CONTINUATION, start, self.pos, true);
    }

    fn ident(&mut self, start: usize) {
        self.bump(); // start char (already ident-start)
        self.eat_while(|c| c == '_' || c.is_alphanumeric());
        self.push(kind::IDENT, start, self.pos, false);
        // A following `'` is transpose only after a *value*. Keywords are not
        // values, except `end` (used as an index, e.g. `a(end)'`).
        let text = &self.src[start..self.pos];
        let is_value = !is_keyword(text) || text == "end";
        self.prev_value = is_value;
    }

    /// A single-quoted `'…'` char array. `''` is an escaped quote (does not
    /// terminate). A raw newline or EOF before the closing quote → `error`.
    fn char_literal(&mut self, start: usize) {
        self.bump(); // opening '
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '\'' {
                // `''` is a literal quote; a lone `'` closes.
                if self.peek_at(1) == Some('\'') {
                    self.bump();
                    self.bump();
                    continue;
                }
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
        self.prev_value = true;
    }

    /// A double-quoted `"…"` string. `""` is an escaped quote. A raw newline or
    /// EOF before the closing quote → `error`.
    fn string_literal(&mut self, start: usize) {
        self.bump(); // opening "
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '"' {
                if self.peek_at(1) == Some('"') {
                    self.bump();
                    self.bump();
                    continue;
                }
                self.bump();
                terminated = true;
                break;
            }
            if c == '\n' || c == '\r' {
                break;
            }
            self.bump();
        }
        let token_kind = if terminated { kind::STRING } else { kind::ERROR };
        self.push(token_kind, start, self.pos, false);
        self.prev_value = true;
    }

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        if self.peek() == '0' {
            match self.peek_at(1) {
                Some('x') | Some('X') => {
                    self.pos += 2;
                    self.eat_while(|c| c.is_ascii_hexdigit());
                    self.finish_number(start, false);
                    return;
                }
                Some('b') | Some('B') => {
                    self.pos += 2;
                    self.eat_while(|c| c == '0' || c == '1');
                    self.finish_number(start, false);
                    return;
                }
                _ => {}
            }
        }
        self.eat_while(|c| c.is_ascii_digit());
        // Fractional part only when a digit follows the dot, so `1.*x`
        // (elementwise) keeps `1` and `.*` separate, and `1:end` ranges stay
        // distinct tokens.
        if self.peek() == '.' && self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) {
            is_float = true;
            self.bump(); // .
            self.eat_while(|c| c.is_ascii_digit());
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
                self.eat_while(|c| c.is_ascii_digit());
            }
        }
        self.finish_number(start, is_float);
    }

    /// Consume an optional trailing imaginary suffix (`i`/`j`, when not the start
    /// of a longer identifier) and push the numeric token.
    fn finish_number(&mut self, start: usize, is_float: bool) {
        if matches!(self.peek(), 'i' | 'j')
            && !self
                .peek_at(1)
                .map(|c| c == '_' || c.is_alphanumeric())
                .unwrap_or(false)
        {
            self.bump();
        }
        let k = if is_float { kind::FLOAT } else { kind::INT };
        self.push(k, start, self.pos, false);
        self.prev_value = true;
    }

    fn punct(&mut self, start: usize) {
        for op in OPERATORS {
            if self.src[self.pos..].starts_with(op) {
                self.pos += op.len();
                self.push(kind::PUNCT, start, self.pos, false);
                // Only the non-conjugate transpose `.'` closes a value.
                self.prev_value = *op == ".'";
                return;
            }
        }
        let c = self.peek();
        self.bump();
        self.push(kind::PUNCT, start, self.pos, false);
        // Closers and the transpose operator close a value; everything else
        // (openers, binary operators, `;`, `,`, `=`) does not — so a following
        // `'` opens a char literal.
        self.prev_value = matches!(c, ')' | ']' | '}' | '\'');
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

    /// Byte offset of the next line break at or after `from` (exclusive of the
    /// break itself), or end of input.
    fn find_line_end(&self, from: usize) -> usize {
        match self.src[from..].find(['\n', '\r']) {
            Some(i) => from + i,
            None => self.bytes.len(),
        }
    }

    /// Given an offset positioned at a line break (or EOF), return the offset just
    /// past the break (handles `\n`, `\r`, and `\r\n`).
    fn consume_newline_at(&self, at: usize) -> usize {
        if at >= self.bytes.len() {
            return self.bytes.len();
        }
        match self.bytes[at] {
            b'\n' => at + 1,
            b'\r' => {
                if self.bytes.get(at + 1) == Some(&b'\n') {
                    at + 2
                } else {
                    at + 1
                }
            }
            _ => at,
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
            "function y = f(x)\n  y = x + 1;\nend\n",
            "% line comment\nx = 1;\n",
            "%{\nblock comment\n%}\ny = 2;\n",
            "z = a + ...\n    b;\n",
            "s = \"a \"\"quote\"\"\"; c = 'it''s';\n",
            "n = 0xFF + 0b101 + 1.5e-3 + 3i + .5;\n",
            "M = A'; v = [1 2 3].';\n",
            "h = @(x) x.^2;\n",
            "classdef C < handle\n  properties\n    x\n  end\nend\n",
            "λ = 1;  % unicode ident\n",
            "",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("function add(a, b)\n  c = a + b;\nend\n");
        assert!(t.contains(&(kind::IDENT, "function".to_string())));
        assert!(t.contains(&(kind::IDENT, "add".to_string())));
        assert!(t.contains(&(kind::PUNCT, "(".to_string())));
        assert!(t.iter().any(|(k, _)| *k == kind::NEWLINE));
        assert!(is_keyword("function"));
        assert!(is_keyword("end"));
        assert!(!is_keyword("add"));
    }

    #[test]
    fn transpose_vs_char_array() {
        // `A'` is transpose (A is a value); a leading `'x'` is a char array.
        let t = texts("A' == 'x'");
        assert!(t.contains(&(kind::CHAR, "'x'".to_string())));
        assert!(t.contains(&(kind::PUNCT, "'".to_string())));
    }

    #[test]
    fn newline_resets_value_context() {
        // After `5` and a newline, the leading `'` opens a char array.
        let t = texts("x = 5\n'hello'\n");
        assert!(t.contains(&(kind::CHAR, "'hello'".to_string())));
    }

    #[test]
    fn continuation_joins_lines_and_is_trivia() {
        let t = texts("z = a + ...\n  b;\n");
        assert!(t.iter().any(|(k, s)| *k == kind::CONTINUATION && s.starts_with("...")));
    }

    #[test]
    fn doubled_quotes_are_escapes() {
        let t = texts("c = 'it''s'; s = \"a\"\"b\";");
        assert!(t.contains(&(kind::CHAR, "'it''s'".to_string())));
        assert!(t.contains(&(kind::STRING, "\"a\"\"b\"".to_string())));
    }

    #[test]
    fn block_comment_must_be_alone_on_line() {
        // Real block comment.
        let t = texts("%{\nhidden\n%}\nx = 1;\n");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::BLOCK_COMMENT && s.contains("hidden")));
        // `%{` not alone on its line is just a line comment.
        let t2 = texts("x = 1; %{ not a block\n");
        assert!(t2.iter().any(|(k, _)| *k == kind::LINE_COMMENT));
        assert!(!t2.iter().any(|(k, _)| *k == kind::BLOCK_COMMENT));
    }

    #[test]
    fn numbers() {
        let t = texts("0xFF 0b101 10 3.14 1.5e-3 .5 3i 2.0j");
        assert!(t.contains(&(kind::INT, "0xFF".to_string())));
        assert!(t.contains(&(kind::INT, "0b101".to_string())));
        assert!(t.contains(&(kind::INT, "10".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14".to_string())));
        assert!(t.contains(&(kind::FLOAT, "1.5e-3".to_string())));
        assert!(t.contains(&(kind::FLOAT, ".5".to_string())));
        assert!(t.contains(&(kind::INT, "3i".to_string())));
        assert!(t.contains(&(kind::FLOAT, "2.0j".to_string())));
    }

    #[test]
    fn dotted_operators_and_non_conjugate_transpose() {
        let t = texts("A.^2 .* B ./ C; D.'");
        for op in [".^", ".*", "./", ".'"] {
            assert!(
                t.contains(&(kind::PUNCT, op.to_string())),
                "missing operator {op}"
            );
        }
    }

    #[test]
    fn unterminated_string_is_error_but_covered() {
        let src = "x = 'open\n";
        let t = texts(src);
        assert!(t.iter().any(|(k, _)| *k == kind::ERROR));
        assert!(covers_all(src));
    }
}
