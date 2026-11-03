//! Lossless Lua lexer, grounded in the Lua 5.4 reference lexer (`llex.c`).
//!
//! Guarantees (identical contract to the Rust and Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs, newlines, line and block comments) are emitted as
//!   `trivia` tokens, not discarded. Unlike Python, Lua is *not*
//!   whitespace-significant, so a newline is ordinary `newline` trivia; the
//!   parser uses it only as a soft statement-separator heuristic.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped — an unterminated string or long
//!   bracket is emitted as an `error` token spanning to end of input.
//!
//! Lua-specific surface the lexer covers in full:
//! - Long brackets `[[ … ]]`, `[=[ … ]=]`, `[==[ … ]==]` … for both long
//!   strings and (with a `--` prefix) long block comments. These span newlines
//!   and contain no escapes.
//! - Both short string forms (`"…"`, `'…'`) with backslash escapes.
//! - Decimal and hexadecimal numerals, including hex floats with binary
//!   exponents (`0x1.8p3`) and decimal floats with exponents (`1.5e-3`).
//! - The full Lua 5.4 operator set, including `//` (floor div), `~=` (not
//!   equal), `..`/`...` (concat / varargs), `::` (label delimiter), and the
//!   bitwise operators `& | ~ << >>`.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_` as a pragmatic superset of Lua's ASCII-only
//! identifier rule — anything outside still lands in the tree as a covered
//! token, never dropped.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Lua's reserved words (5.4). Like the other lexers, these lex as `name`
/// tokens; the parser distinguishes them via [`is_keyword`].
pub const KEYWORDS: &[&str] = &[
    "and", "break", "do", "else", "elseif", "end", "false", "for", "function", "goto", "if", "in",
    "local", "nil", "not", "or", "repeat", "return", "then", "true", "until", "while",
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
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
const OPERATORS: &[&str] = &["...", "..", "::", "<<", ">>", "//", "==", "~=", "<=", ">="];

const SINGLE_PUNCT: &str = "+-*/%^#&~|<>=(){}[];:,.";

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
                '-' if self.peek_at(1) == Some('-') => self.comment(start),
                '[' if self.long_bracket_level(self.pos).is_some() => {
                    let level = self.long_bracket_level(self.pos).unwrap();
                    self.long_bracket(start, level, kind::STRING);
                }
                '"' | '\'' => self.short_string(start),
                c if c.is_ascii_digit() => self.number(start),
                '.' if self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) => {
                    self.number(start)
                }
                c if is_ident_start(c) => self.name(start),
                c if SINGLE_PUNCT.contains(c) => self.punct(start),
                _ => {
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

    /// A `--` comment: a long block comment if `--[[`/`--[=[`… follows, else a
    /// line comment running to (but not including) the next newline.
    fn comment(&mut self, start: usize) {
        self.pos += 2; // the two dashes
        if self.peek() == '[' {
            if let Some(level) = self.long_bracket_level(self.pos) {
                self.long_bracket(start, level, kind::COMMENT);
                return;
            }
        }
        let end = self.find_line_end(self.pos);
        self.pos = end;
        self.push(kind::COMMENT, start, end, true);
    }

    /// If position `at` begins a long-bracket opener `[` `=`* `[`, return its
    /// level (the number of `=`), else `None`.
    fn long_bracket_level(&self, at: usize) -> Option<usize> {
        let rest = self.src.get(at..)?;
        let mut it = rest.char_indices();
        if it.next()?.1 != '[' {
            return None;
        }
        let mut level = 0;
        for (_, ch) in it {
            match ch {
                '=' => level += 1,
                '[' => return Some(level),
                _ => return None,
            }
        }
        None
    }

    /// Scan a long bracket of the given `level`, opener at `start` already
    /// confirmed. Terminates at the matching `]` `=`{level} `]`; if none is
    /// found the run reaches end of input and is reported as an `error` token
    /// (comments stay `comment` trivia regardless, since the bytes are still
    /// fully covered and an unterminated comment is recoverable).
    fn long_bracket(&mut self, start: usize, level: usize, ok_kind: &'static str) {
        // Consume the opener: `[` `=`{level} `[`.
        self.pos += level + 2;
        let terminated = self.scan_to_long_close(level);
        let token_kind = if terminated || ok_kind == kind::COMMENT {
            ok_kind
        } else {
            kind::ERROR
        };
        self.push(token_kind, start, self.pos, ok_kind == kind::COMMENT);
    }

    /// Advance to just past a long-bracket closer `]` `=`{level} `]`. Returns
    /// whether a closer was found; on failure the cursor is left at end of input.
    fn scan_to_long_close(&mut self, level: usize) -> bool {
        while self.pos < self.bytes.len() {
            if self.peek() == ']' {
                let mut j = self.pos + 1;
                let mut eqs = 0;
                while self.bytes.get(j) == Some(&b'=') {
                    eqs += 1;
                    j += 1;
                }
                if eqs == level && self.bytes.get(j) == Some(&b']') {
                    self.pos = j + 1;
                    return true;
                }
            }
            self.bump();
        }
        false
    }

    /// A short string `"…"` / `'…'` with backslash escapes. Unterminated strings
    /// (hitting a newline or end of input) become `error` tokens over their bytes.
    fn short_string(&mut self, start: usize) {
        let quote = self.peek();
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
            if c == quote {
                self.bump();
                terminated = true;
                break;
            }
            if c == '\n' || c == '\r' {
                // A raw newline ends an unterminated short string.
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
    }

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        if self.peek() == '0' && matches!(self.peek_at(1), Some('x') | Some('X')) {
            self.pos += 2;
            self.eat_while(|c| c.is_ascii_hexdigit());
            if self.peek() == '.' {
                is_float = true;
                self.bump();
                self.eat_while(|c| c.is_ascii_hexdigit());
            }
            // Binary exponent `p`/`P` with optional sign.
            if matches!(self.peek(), 'p' | 'P') {
                is_float = true;
                self.bump();
                if matches!(self.peek(), '+' | '-') {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit());
            }
            let k = if is_float { kind::FLOAT } else { kind::INT };
            return self.push(k, start, self.pos, false);
        }
        self.eat_while(|c| c.is_ascii_digit());
        if self.peek() == '.' {
            is_float = true;
            self.bump();
            self.eat_while(|c| c.is_ascii_digit());
        }
        if matches!(self.peek(), 'e' | 'E') {
            is_float = true;
            self.bump();
            if matches!(self.peek(), '+' | '-') {
                self.bump();
            }
            self.eat_while(|c| c.is_ascii_digit());
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
            "local function f(x)\n  return x\nend\n",
            "-- line comment\nx = 1\n",
            "--[[ block\ncomment ]]\ny = 2\n",
            "s = [==[ raw\nlong ]==] .. 'a' .. \"b\"\n",
            "n = 0xFF + 0x1.8p3 + 1.5e-3 + 3 // 2\n",
            "t = { a = 1, ['b'] = 2, [3] = 4 }\n",
            "if a ~= b then a = a | b end\n",
            "λ = '☃ €'  -- unicode\n",
            "::lbl:: goto lbl",
            "",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("local function add(a, b)\n  return a + b\nend\n");
        assert!(t.contains(&(kind::NAME, "local".to_string())));
        assert!(t.contains(&(kind::NAME, "function".to_string())));
        assert!(t.contains(&(kind::NAME, "add".to_string())));
        assert!(t.contains(&(kind::PUNCT, "(".to_string())));
        assert!(t.iter().any(|(k, _)| *k == kind::NEWLINE));
        assert!(is_keyword("function"));
        assert!(is_keyword("end"));
        assert!(!is_keyword("add"));
    }

    #[test]
    fn long_strings_and_comments_span_newlines() {
        let t = texts("x = [[a\nb\nc]]\n");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "[[a\nb\nc]]"));
        let t = texts("--[==[ a\nb ]==]\n");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::COMMENT && s == "--[==[ a\nb ]==]"));
    }

    #[test]
    fn long_bracket_levels_must_match() {
        // A `]=]` does not close a level-0 `[[` bracket; only `]]` does.
        let t = texts("x = [[ a ]=] b ]]\n");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "[[ a ]=] b ]]"));
    }

    #[test]
    fn unterminated_long_string_is_error() {
        let t = texts("x = [[ unterminated\n");
        assert!(t.iter().any(|(k, _)| *k == kind::ERROR));
        // Still fully covered.
        assert!(covers_all("x = [[ unterminated\n"));
    }

    #[test]
    fn operators() {
        let t = texts("a // b ~= c .. d ... << >> == <= >= ::");
        for op in ["//", "~=", "..", "...", "<<", ">>", "==", "<=", ">=", "::"] {
            assert!(
                t.contains(&(kind::PUNCT, op.to_string())),
                "missing operator {op}"
            );
        }
    }

    #[test]
    fn numbers() {
        let t = texts("0xFF 0x1.8p3 10 3.14 1.5e-3 .5");
        assert!(t.contains(&(kind::INT, "0xFF".to_string())));
        assert!(t.contains(&(kind::FLOAT, "0x1.8p3".to_string())));
        assert!(t.contains(&(kind::INT, "10".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14".to_string())));
        assert!(t.contains(&(kind::FLOAT, "1.5e-3".to_string())));
        assert!(t.contains(&(kind::FLOAT, ".5".to_string())));
    }

    #[test]
    fn line_comment_stops_at_newline() {
        let t = texts("-- hi\nx");
        assert!(t.contains(&(kind::COMMENT, "-- hi".to_string())));
        assert!(t.iter().any(|(k, _)| *k == kind::NEWLINE));
        assert!(t.contains(&(kind::NAME, "x".to_string())));
    }
}
