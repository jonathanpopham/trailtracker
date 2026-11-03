//! Lossless GraphQL (SDL) lexer, grounded in the GraphQL specification's
//! "Lexical Tokens" and "Ignored Tokens" sections.
//!
//! Guarantees (identical contract to the Rust/Go/Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (whitespace, `#` line comments, and commas — which are *insignificant*
//!   in GraphQL) are emitted as `trivia` tokens, never discarded. The parser
//!   skips them for structure but the tree keeps them.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//! - `pos` advances on every loop iteration (a tail progress guard backs every
//!   scanner), so the lexer can never spin without consuming input.
//!
//! Coverage note (honest): name start/continue uses `_` plus
//! `char::is_alphabetic`/`is_alphanumeric` as a pragmatic stand-in for the
//! spec's ASCII `NameStart`/`NameContinue` classes. The spec is ASCII-only here,
//! so any non-ASCII letter is technically out of grammar — but it still lands in
//! the tree as a covered `name` token rather than being dropped, which keeps the
//! losslessness guarantee whole.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Token kind labels. Stored on the CST as `&'static str` so the tree stays
/// uniform and JSON-friendly.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const COMMENT: &str = "comment";
    /// Commas are ignored tokens in GraphQL; kept as trivia for losslessness.
    pub const COMMA: &str = "comma";
    pub const NAME: &str = "name";
    pub const INT: &str = "int_value";
    pub const FLOAT: &str = "float_value";
    pub const STRING: &str = "string_value";
    pub const BLOCK_STRING: &str = "block_string_value";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// The single-character punctuators of GraphQL SDL. The only multi-character
/// punctuator is `...` (the spread), handled explicitly before this set.
const SINGLE_PUNCT: &str = "!$&():=@[]{}|";

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
                ',' => {
                    self.bump();
                    self.push(kind::COMMA, start, self.pos, true);
                }
                '#' => {
                    let end = self.find_line_end(start);
                    self.pos = end;
                    self.push(kind::COMMENT, start, end, true);
                }
                '"' if self.src[self.pos..].starts_with("\"\"\"") => self.block_string(start),
                '"' => self.string(start),
                '-' if self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) => {
                    self.number(start)
                }
                c if c.is_ascii_digit() => self.number(start),
                c if is_name_start(c) => self.name(start),
                '.' if self.src[self.pos..].starts_with("...") => {
                    self.pos += 3;
                    self.push(kind::PUNCT, start, self.pos, false);
                }
                c if SINGLE_PUNCT.contains(c) => {
                    self.bump();
                    self.push(kind::PUNCT, start, self.pos, false);
                }
                _ => {
                    // Unknown byte/char (lone `.`, `-`, control char, stray
                    // unicode punctuation) — preserve it as an explicit error.
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }
            // Progress guard: every arm above advances `pos`, but a non-advancing
            // iteration would mean an infinite loop / OOM. Force one byte of
            // progress, recorded honestly as an error token, if it ever happens.
            if self.pos == start {
                self.pos = (start + 1).min(self.bytes.len());
                self.push(kind::ERROR, start, self.pos, false);
            }
        }
        self.tokens
    }

    // --- scanners -----------------------------------------------------------

    fn name(&mut self, start: usize) {
        self.eat_while(is_name_continue);
        self.push(kind::NAME, start, self.pos, false);
    }

    /// `"..."` single-line string with `\` escapes. Terminates on the closing
    /// quote or a line break (unterminated → error token over what was read).
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

    /// `"""..."""` block string. The only escape inside is `\"""` (an escaped
    /// triple-quote); everything else, including newlines, is literal.
    fn block_string(&mut self, start: usize) {
        self.pos += 3; // opening """
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            if self.src[self.pos..].starts_with("\\\"\"\"") {
                self.pos += 4; // escaped \"""
                continue;
            }
            if self.src[self.pos..].starts_with("\"\"\"") {
                self.pos += 3;
                terminated = true;
                break;
            }
            self.bump();
        }
        let k = if terminated {
            kind::BLOCK_STRING
        } else {
            kind::ERROR
        };
        self.push(k, start, self.pos, false);
    }

    /// IntValue / FloatValue. GraphQL numbers carry no `_` separators; a leading
    /// `-` is the only sign and only the dispatcher routes it here with a digit
    /// following. A fractional or exponent part promotes the token to a float.
    fn number(&mut self, start: usize) {
        if self.peek() == '-' {
            self.bump();
        }
        self.eat_while(|c| c.is_ascii_digit());
        let mut is_float = false;
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
            let digit_after = self
                .src
                .get(self.pos + 1 + sign_len..)
                .and_then(|s| s.chars().next())
                .map(|c| c.is_ascii_digit())
                .unwrap_or(false);
            if digit_after {
                is_float = true;
                self.bump(); // e/E
                if sign_len == 1 {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit());
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

fn is_name_start(c: char) -> bool {
    c == '_' || c.is_alphabetic()
}

fn is_name_continue(c: char) -> bool {
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
            "type Query { hello: String }",
            "# a comment\nscalar Date @specifiedBy(url: \"x\")",
            "\"\"\"\nblock\ndesc with \\\"\"\" inside\n\"\"\"\ntype T { x: Int }",
            "input I { n: Int = -3, f: Float = 1.5e10 }",
            "union U = A | B | C",
            "λ ☃ €", // non-ascii names / unknowns still covered
            "a, b ,c",
            "directive @d(if: Boolean!) on FIELD | OBJECT",
            "\"unterminated",
            "...",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn commas_and_comments_are_trivia() {
        let toks = lex("a, # c\nb");
        assert!(toks.iter().any(|t| t.kind == kind::COMMA && t.trivia));
        assert!(toks.iter().any(|t| t.kind == kind::COMMENT && t.trivia));
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("type X { a(b: Int): Float! }");
        assert!(t.contains(&(kind::NAME, "type".to_string())));
        assert!(t.contains(&(kind::PUNCT, "!".to_string())));
        assert!(t.contains(&(kind::PUNCT, ":".to_string())));
    }

    #[test]
    fn spread_is_one_token() {
        let t = texts("...Frag");
        assert_eq!(t[0], (kind::PUNCT, "...".to_string()));
        assert_eq!(t[1], (kind::NAME, "Frag".to_string()));
    }

    #[test]
    fn block_string_with_escaped_quotes() {
        let src = "\"\"\"a \\\"\"\" b\"\"\"";
        let t = texts(src);
        assert_eq!(t.len(), 1);
        assert_eq!(t[0].0, kind::BLOCK_STRING);
        assert_eq!(t[0].1, src);
    }

    #[test]
    fn numbers_int_vs_float() {
        let t = texts("1 -2 3.5 4e2 -5.0e-1");
        assert!(t.contains(&(kind::INT, "1".to_string())));
        assert!(t.contains(&(kind::INT, "-2".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.5".to_string())));
        assert!(t.contains(&(kind::FLOAT, "4e2".to_string())));
        assert!(t.contains(&(kind::FLOAT, "-5.0e-1".to_string())));
    }
}
