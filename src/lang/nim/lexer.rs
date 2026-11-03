//! Lossless Nim lexer.
//!
//! Guarantees (identical contract to the Rust and Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs, line `#` comments, nestable `#[ ]#` block comments and
//!   their doc variants) are emitted as `trivia` tokens, never discarded.
//!   `NEWLINE` is emitted as a *non-trivia* token because Nim is
//!   indentation-significant (statement and block boundaries).
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//! - The main loop advances `pos` on every iteration; a trailing progress guard
//!   force-consumes one byte if a branch somehow made none, so the lexer can
//!   never spin.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_` as a pragmatic stand-in for the full Unicode
//! identifier tables — anything outside still lands in the tree as a covered
//! token, never dropped.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Nim's keywords. Like the Rust/Python lexers, these lex as `name` tokens; the
/// parser distinguishes them via [`is_keyword`].
pub const KEYWORDS: &[&str] = &[
    "addr",
    "and",
    "as",
    "asm",
    "bind",
    "block",
    "break",
    "case",
    "cast",
    "concept",
    "const",
    "continue",
    "converter",
    "defer",
    "discard",
    "distinct",
    "div",
    "do",
    "elif",
    "else",
    "end",
    "enum",
    "except",
    "export",
    "finally",
    "for",
    "from",
    "func",
    "if",
    "import",
    "in",
    "include",
    "interface",
    "is",
    "isnot",
    "iterator",
    "let",
    "macro",
    "method",
    "mixin",
    "mod",
    "nil",
    "not",
    "notin",
    "object",
    "of",
    "or",
    "out",
    "proc",
    "ptr",
    "raise",
    "ref",
    "return",
    "shl",
    "shr",
    "static",
    "template",
    "try",
    "tuple",
    "type",
    "using",
    "var",
    "when",
    "while",
    "xor",
    "yield",
];

pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.contains(&text)
}

pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const NEWLINE: &str = "newline";
    pub const COMMENT: &str = "comment";
    pub const NAME: &str = "name";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const STRING: &str = "string_literal";
    pub const CHAR: &str = "char_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Characters Nim permits inside an operator. A maximal run of these lexes as a
/// single `punct` token (so `..`, `==`, `+=`, `->`, `.` all stay whole), which
/// matches Nim's own operator tokenization. Structural delimiters `()[]{},;` are
/// *not* in this set, so they always stand alone.
const OP_CHARS: &str = "=+-*/<>@$~&%|!?^.:";

/// Single-character structural delimiters (never merged into operator runs).
const DELIMS: &str = "()[]{},;";

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
                    self.eat_while(|c| c == ' ' || c == '\t' || c == '\x0c' || c == '\x0b');
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                '#' => self.comment(start),
                '"' => self.string(start, false),
                '\'' => self.char_literal(start),
                '`' => self.backtick(start),
                c if is_ident_start(c) => self.name(start),
                c if c.is_ascii_digit() => self.number(start),
                c if OP_CHARS.contains(c) => {
                    self.eat_while(|c| OP_CHARS.contains(c));
                    self.push(kind::PUNCT, start, self.pos, false);
                }
                c if DELIMS.contains(c) => {
                    self.bump();
                    self.push(kind::PUNCT, start, self.pos, false);
                }
                _ => {
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }
            // Progress guard: a branch must always advance. If somehow none did
            // (defensive — should be unreachable), consume one byte as `error`
            // so the loop cannot spin and the byte is never dropped.
            if self.pos == start {
                self.bump();
                self.push(kind::ERROR, start, self.pos, false);
            }
        }
        self.tokens
    }

    /// `# line`, `## doc line`, nestable `#[ … ]#` block, and `##[ … ]##` doc
    /// block comments. All are trivia, all stay lossless.
    fn comment(&mut self, start: usize) {
        // `##[ … ]##` doc block (closer `]##`).
        if self.peek_at(1) == Some('#') && self.peek_at(2) == Some('[') {
            self.pos += 3;
            self.scan_to_seq("]##");
            return self.push(kind::COMMENT, start, self.pos, true);
        }
        // `#[ … ]#` nestable block comment (closer `]#`).
        if self.peek_at(1) == Some('[') {
            self.pos += 2;
            let mut depth = 1usize;
            while self.pos < self.bytes.len() && depth > 0 {
                if self.src[self.pos..].starts_with("#[") {
                    self.pos += 2;
                    depth += 1;
                } else if self.src[self.pos..].starts_with("]#") {
                    self.pos += 2;
                    depth -= 1;
                } else {
                    self.bump();
                }
            }
            return self.push(kind::COMMENT, start, self.pos, true);
        }
        // Ordinary line comment (`#` or `##`): to end of line.
        let end = self.find_line_end(start);
        self.pos = end;
        self.push(kind::COMMENT, start, end, true);
    }

    /// Scan forward until just past the next occurrence of `seq` (or to EOF).
    fn scan_to_seq(&mut self, seq: &str) {
        while self.pos < self.bytes.len() {
            if self.src[self.pos..].starts_with(seq) {
                self.pos += seq.len();
                return;
            }
            self.bump();
        }
    }

    fn name(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        // Generalized raw string literal: an identifier immediately followed by a
        // quote (`r"…"`, `re"…"`, `fmt"…"`) is Nim's raw-string call form. Emit the
        // identifier, then scan the following string with raw semantics.
        if self.peek() == '"' {
            self.push(kind::NAME, start, self.pos, false);
            let s = self.pos;
            return self.string(s, true);
        }
        self.push(kind::NAME, start, self.pos, false);
    }

    /// Accent-quoted identifier `` `op` `` (lets an operator be used as a name, e.g.
    /// `` proc `+`(a, b: int) ``). Lexed as a `name` so the parser treats it as the
    /// routine's name. Unterminated → `error`, still lossless.
    fn backtick(&mut self, start: usize) {
        self.bump(); // opening backtick
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '\n' {
                break; // accent quotes do not span lines
            }
            self.bump();
            if c == '`' {
                terminated = true;
                break;
            }
        }
        let k = if terminated { kind::NAME } else { kind::ERROR };
        self.push(k, start, self.pos, false);
    }

    /// Scan a `"`-delimited string. Handles single and triple (`"""`) quotes;
    /// triple strings span newlines and are always raw. `raw` (from `r"…"` /
    /// generalized raw prefixes) disables backslash escaping and treats `""` as an
    /// escaped quote. The opening prefix (if any) has already been consumed.
    fn string(&mut self, start: usize, raw: bool) {
        let triple = self.peek_at(1) == Some('"') && self.peek_at(2) == Some('"');
        if triple {
            self.pos += 3;
            // Triple-quoted: raw-by-nature, ends at the next `"""`.
            let mut terminated = false;
            while self.pos < self.bytes.len() {
                if self.src[self.pos..].starts_with("\"\"\"") {
                    self.pos += 3;
                    terminated = true;
                    break;
                }
                self.bump();
            }
            let k = if terminated {
                kind::STRING
            } else {
                kind::ERROR
            };
            return self.push(k, start, self.pos, false);
        }
        self.bump(); // opening quote
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '\\' && !raw {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
                continue;
            }
            if c == '"' {
                if raw && self.peek_at(1) == Some('"') {
                    // Raw string: doubled quote is an escaped quote, not the end.
                    self.pos += 2;
                    continue;
                }
                self.bump();
                terminated = true;
                break;
            }
            if c == '\n' {
                break; // unterminated single-line string ends at the newline
            }
            self.bump();
        }
        let k = if terminated {
            kind::STRING
        } else {
            kind::ERROR
        };
        self.push(k, start, self.pos, false);
    }

    /// Character literal `'a'`, `'\n'`, `'\x41'`. Numeric type suffixes (`1'u8`)
    /// are handled in [`Lexer::number`], so a leading `'` here is always a char.
    fn char_literal(&mut self, start: usize) {
        self.bump(); // opening quote
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
            if c == '\n' {
                break;
            }
            self.bump();
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
                    return self.finish_number(start, false);
                }
                Some('o') | Some('O') => {
                    self.pos += 2;
                    self.eat_while(|c| ('0'..='7').contains(&c) || c == '_');
                    return self.finish_number(start, false);
                }
                Some('b') | Some('B') => {
                    self.pos += 2;
                    self.eat_while(|c| c == '0' || c == '1' || c == '_');
                    return self.finish_number(start, false);
                }
                _ => {}
            }
        }
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
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
        self.finish_number(start, is_float);
    }

    /// Consume an optional Nim numeric type suffix (`'i64`, `'u8`, `'f32`, `'d`)
    /// then push the literal. A `'f…` suffix forces float classification.
    fn finish_number(&mut self, start: usize, mut is_float: bool) {
        if self.peek() == '\'' && self.peek_at(1).map(is_ident_start).unwrap_or(false) {
            self.bump(); // '
            let suf_start = self.pos;
            self.eat_while(is_ident_continue);
            let suffix = self.src.get(suf_start..self.pos).unwrap_or("");
            if suffix.starts_with('f') || suffix.starts_with('F') || suffix.starts_with('d') {
                is_float = true;
            }
        }
        let k = if is_float { kind::FLOAT } else { kind::INT };
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
            "proc add(a, b: int): int =\n  result = a + b\n",
            "type Point = object\n  x, y: float\n",
            "const Answer = 42'i64\n",
            "let s = r\"raw\\n\" & \"esc\\t\" & \"\"\"multi\nline\"\"\"\n",
            "var c = 'a'  # a char\nx = 0xFF_00 + 1.5e3\n",
            "echo \"héllo ☃ €\"  ## doc\n",
            "proc `+`(a, b: T): T = a\n",
            "x = 1 ..< 10\n",
            "#[ a #[ nested ]# block ]#\nval = re\"[0-9]+\"\n",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("proc add(a, b: int): int =\n  a + b\n");
        assert!(t.contains(&(kind::NAME, "proc".to_string())));
        assert!(t.contains(&(kind::NAME, "add".to_string())));
        assert!(t.contains(&(kind::PUNCT, "(".to_string())));
        assert!(t.contains(&(kind::PUNCT, ":".to_string())));
        assert!(t.iter().any(|(k, _)| *k == kind::NEWLINE));
        assert!(is_keyword("proc"));
        assert!(is_keyword("type"));
        assert!(!is_keyword("add"));
    }

    #[test]
    fn triple_and_raw_strings() {
        let t = texts("a = \"\"\"x\ny\"\"\"\nb = r\"a\"\"b\"\n");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "\"\"\"x\ny\"\"\""));
        // `r"a""b"` lexes as a name `r` plus a raw string whose doubled quote is
        // an escaped quote, not a terminator.
        assert!(t.contains(&(kind::NAME, "r".to_string())));
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "\"a\"\"b\""));
    }

    #[test]
    fn char_vs_numeric_suffix() {
        let t = texts("c = 'x'\nn = 12'u8\nf = 1.0'f32\n");
        assert!(t.contains(&(kind::CHAR, "'x'".to_string())));
        assert!(t.contains(&(kind::INT, "12'u8".to_string())));
        assert!(t.contains(&(kind::FLOAT, "1.0'f32".to_string())));
    }

    #[test]
    fn nestable_block_comment() {
        let t = texts("#[ outer #[ inner ]# still ]# x");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::COMMENT && s == "#[ outer #[ inner ]# still ]#"));
        assert!(t.contains(&(kind::NAME, "x".to_string())));
    }

    #[test]
    fn operator_runs_stay_whole() {
        let t = texts("a ..< b += c");
        assert!(t.contains(&(kind::PUNCT, "..<".to_string())));
        assert!(t.contains(&(kind::PUNCT, "+=".to_string())));
    }

    #[test]
    fn accent_quoted_identifier() {
        let t = texts("proc `<=`(a, b: int): bool = true\n");
        assert!(t.contains(&(kind::NAME, "`<=`".to_string())));
    }

    #[test]
    fn unterminated_inputs_round_trip() {
        for src in ["x = \"unterminated\n", "c = 'a\n", "`oops\n", "#[ open"] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }
}
