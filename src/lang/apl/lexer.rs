//! Lossless APL lexer.
//!
//! APL source is dense with multi-byte Unicode glyphs (`⍴ ⌽ ⍳ ∇ ⍝ ← ¯ ⍵ ⍺` …),
//! so this lexer is rigorously Unicode-safe: it iterates by `char`, only ever
//! advances `pos` by whole `char` byte-lengths, and never slices the source at a
//! non-`char` boundary. (A prior bug in this codebase panicked by byte-indexing
//! into the middle of a glyph — that mistake is structurally impossible here.)
//!
//! Guarantees, identical to every other front end:
//! - **Contiguous & lossless** — every byte is covered by exactly one token, so
//!   concatenating the token texts reproduces the source verbatim.
//! - **Trivia retained** — whitespace and `⍝` comments are emitted as `trivia`
//!   tokens, never dropped.
//! - **No silent drops** — anything the lexer cannot classify becomes an `error`
//!   token over its exact bytes.
//! - **Progress guaranteed** — the main loop advances `pos` on every iteration;
//!   a fallback guard turns any non-advancing state into a single-char `error`
//!   token so the lexer can never spin.
//!
//! Coverage note (honest): name start/continue uses `char::is_alphabetic` /
//! `is_alphanumeric` plus `_` and the APL letters `∆`/`⍙`, a pragmatic stand-in
//! for the full APL identifier rules. The glyph table below is broad but not
//! exhaustive; any glyph outside it still lands losslessly as an `error` token
//! with its true span, which is reported, never hidden.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Token kind labels, stored on the CST as `&'static str`.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const COMMENT: &str = "comment";
    pub const STRING: &str = "string_literal";
    pub const NUMBER: &str = "number_literal";
    pub const NAME: &str = "name";
    /// The assignment arrow `←`.
    pub const ASSIGN: &str = "assign";
    /// The del `∇` that opens/closes a tradfn.
    pub const DEL: &str = "del";
    /// Any other glyph or ASCII operator/bracket.
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// APL control words (the identifier that follows a leading `:`), e.g. `:If`,
/// `:EndNamespace`. Used by the lowering to avoid mistaking a control keyword for
/// a function reference. Not exhaustive; missing words simply fall through as
/// ordinary names.
pub const CONTROL_WORDS: &[&str] = &[
    "If",
    "Else",
    "ElseIf",
    "AndIf",
    "OrIf",
    "EndIf",
    "While",
    "EndWhile",
    "Repeat",
    "Until",
    "EndRepeat",
    "For",
    "EndFor",
    "Select",
    "Case",
    "CaseList",
    "EndSelect",
    "Namespace",
    "EndNamespace",
    "Class",
    "EndClass",
    "Function",
    "EndFunction",
    "Return",
    "Continue",
    "Leave",
    "GoTo",
    "Trap",
    "EndTrap",
    "With",
    "EndWith",
    "Hold",
    "EndHold",
    "Section",
    "EndSection",
    "Signal",
    "Access",
    "Field",
    "Property",
    "EndProperty",
    "Implements",
    "Using",
    "Interface",
    "EndInterface",
    "Attribute",
    "Include",
];

/// True if `text` (without the leading `:`) is a recognized APL control word.
pub fn is_control_word(text: &str) -> bool {
    CONTROL_WORDS.contains(&text)
}

/// ASCII operator / bracket / separator characters APL uses directly. `_` is a
/// name char, `'` opens a string, and `\` is the APL expand/scan operator.
const ASCII_PUNCT: &str = "+-*/\\<>=()[]{};:.,?!|~@#$%^&\"`";

/// A broad table of APL function/operator glyphs classified as `punct`. The
/// special-cased glyphs handled earlier in the scanner (`← ∇ ⍝ '`) are absent;
/// `¯` is present so a high-minus that is *not* part of a number still classifies.
const APL_GLYPHS: &str =
    "×÷⍟⌹○⍱⍲≠≤≥≡≢∨∧⌈⌊⊥⊤⊣⊢↑↓⊂⊃⊆⊇⌷⍋⍒⍳⍸∊⍷∪∩⌿⍀⍪⍴⌽⊖⍉¨⍨⍣⍡∘⍤⍥⌶⍠⌸⌺⋄→⍺⍵⍶⍹⍎⍕⊙∆⍙¯⍫⍩⍇⍈⍐⍗⍞⎕⌾⍭⍔⍓⍌⍏⍖⊙⍮⍦⍧⍯⍰";

pub fn lex(source: &str) -> Vec<Token> {
    Lexer::new(source).run()
}

struct Lexer<'s> {
    src: &'s str,
    len: usize,
    pos: usize,
    tokens: Vec<Token>,
}

impl<'s> Lexer<'s> {
    fn new(src: &'s str) -> Self {
        Lexer {
            src,
            len: src.len(),
            pos: 0,
            tokens: Vec::new(),
        }
    }

    fn run(mut self) -> Vec<Token> {
        while self.pos < self.len {
            let start = self.pos;
            let c = self.peek();
            match c {
                c if c.is_whitespace() => {
                    self.eat_while(|c| c.is_whitespace());
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                '⍝' => self.comment(start),
                '\'' => self.string(start),
                '←' => {
                    self.bump();
                    self.push(kind::ASSIGN, start, self.pos, false);
                }
                '∇' => {
                    self.bump();
                    self.push(kind::DEL, start, self.pos, false);
                }
                c if c.is_ascii_digit() => self.number(start),
                '¯' if self.next_is_number_continuation() => self.number(start),
                '.' if self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) => {
                    self.number(start)
                }
                '⎕' | '⍞' if starts_name(self.peek_at(1)) => self.name(start),
                c if is_name_start(c) => self.name(start),
                c if is_punct_char(c) => {
                    self.bump();
                    self.push(kind::PUNCT, start, self.pos, false);
                }
                _ => {
                    // Unclassifiable glyph/byte — preserved as an explicit error.
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }

            // Progress guard: no arm may leave `pos` unmoved, but if one ever did
            // we force a single-char advance so the loop can never spin.
            if self.pos == start {
                self.bump();
                self.push(kind::ERROR, start, self.pos, false);
            }
        }
        self.tokens
    }

    // --- scanners -----------------------------------------------------------

    fn comment(&mut self, start: usize) {
        let end = self.find_line_end(start);
        self.pos = end;
        self.push(kind::COMMENT, start, end, true);
    }

    /// `'...'` char/string literal with the doubled `''` escape.
    fn string(&mut self, start: usize) {
        self.bump(); // opening '
        let mut terminated = false;
        while self.pos < self.len {
            if self.peek() == '\'' {
                if self.peek_at(1) == Some('\'') {
                    self.bump();
                    self.bump(); // escaped quote
                } else {
                    self.bump();
                    terminated = true;
                    break;
                }
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

    fn number(&mut self, start: usize) {
        self.real_part();
        // Complex literal `aJb` / `ajb`.
        if matches!(self.peek(), 'J' | 'j') {
            self.bump();
            self.real_part();
        }
        self.push(kind::NUMBER, start, self.pos, false);
    }

    /// One real component: `[¯]digits[.digits][E[¯|+|-]digits]`.
    fn real_part(&mut self) {
        if self.peek() == '¯' {
            self.bump();
        }
        self.eat_while(|c| c.is_ascii_digit());
        if self.peek() == '.' && self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) {
            self.bump(); // .
            self.eat_while(|c| c.is_ascii_digit());
        }
        if matches!(self.peek(), 'e' | 'E') {
            let sign_len = match self.peek_at(1) {
                Some('¯') | Some('+') | Some('-') => 1,
                _ => 0,
            };
            let digit_follows = self
                .peek_at(1 + sign_len)
                .map(|c| c.is_ascii_digit())
                .unwrap_or(false);
            if digit_follows {
                self.bump(); // E
                if sign_len == 1 {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit());
            }
        }
    }

    fn name(&mut self, start: usize) {
        self.bump(); // the start char (letter, `_`, `∆`, `⍙`, `⎕`, or `⍞`)
        self.eat_while(is_name_continue);
        self.push(kind::NAME, start, self.pos, false);
    }

    // --- primitives ---------------------------------------------------------

    fn peek(&self) -> char {
        self.src[self.pos..].chars().next().unwrap_or('\0')
    }

    fn peek_at(&self, n: usize) -> Option<char> {
        self.src[self.pos..].chars().nth(n)
    }

    /// A `¯` introduces a number only when a digit or `.digit` follows it.
    fn next_is_number_continuation(&self) -> bool {
        match self.peek_at(1) {
            Some(c) if c.is_ascii_digit() => true,
            Some('.') => self.peek_at(2).map(|c| c.is_ascii_digit()).unwrap_or(false),
            _ => false,
        }
    }

    fn bump(&mut self) {
        let c = self.peek();
        self.pos += c.len_utf8().max(1);
    }

    fn eat_while(&mut self, mut pred: impl FnMut(char) -> bool) {
        while self.pos < self.len {
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
            None => self.len,
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
    c == '_' || c == '∆' || c == '⍙' || c.is_alphabetic()
}

fn is_name_continue(c: char) -> bool {
    c == '_' || c == '∆' || c == '⍙' || c.is_alphanumeric()
}

fn starts_name(c: Option<char>) -> bool {
    c.map(|c| c.is_alphabetic() || c == '_').unwrap_or(false)
}

fn is_punct_char(c: char) -> bool {
    ASCII_PUNCT.contains(c) || APL_GLYPHS.contains(c)
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
            "avg←{(+/⍵)÷≢⍵}",
            "⍝ a comment\nx←⍳10",
            "r←3 4⍴⍳12 ⋄ ⌽r",
            "'it''s a string'",
            "¯3.14 1E¯3 2J3 ¯1.5e2",
            "∇ R←fac N\n R←×/⍳N\n∇",
            "⎕IO←0 ⋄ ⎕CY 'ws'",
            ":Namespace Foo\n:EndNamespace",
            "λ ☃ € \u{0007}", // alpha-ish idents and a truly unknown control char
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("avg←{(+/⍵)÷≢⍵}");
        assert!(t.contains(&(kind::NAME, "avg".to_string())));
        assert!(t.contains(&(kind::ASSIGN, "←".to_string())));
        assert!(t.contains(&(kind::PUNCT, "{".to_string())));
        assert!(t.iter().any(|(k, s)| *k == kind::PUNCT && s == "÷"));
    }

    #[test]
    fn comment_and_string_are_one_token_each() {
        let t = texts("x ⍝ note\n'a''b'");
        assert!(t.iter().any(|(k, s)| *k == kind::COMMENT && s == "⍝ note"));
        assert!(t.iter().any(|(k, s)| *k == kind::STRING && s == "'a''b'"));
    }

    #[test]
    fn numbers_with_high_minus_and_complex() {
        let t = texts("¯3.14 2J¯3 1E3");
        assert!(t.iter().any(|(k, s)| *k == kind::NUMBER && s == "¯3.14"));
        assert!(t.iter().any(|(k, s)| *k == kind::NUMBER && s == "2J¯3"));
        assert!(t.iter().any(|(k, s)| *k == kind::NUMBER && s == "1E3"));
    }

    #[test]
    fn del_and_quad_name() {
        let t = texts("∇foo ⎕IO");
        assert!(t.iter().any(|(k, s)| *k == kind::DEL && s == "∇"));
        assert!(t.iter().any(|(k, s)| *k == kind::NAME && s == "⎕IO"));
    }

    #[test]
    fn unknown_char_is_error_not_panic() {
        // A control char outside any class must round-trip as an error token.
        let t = texts("\u{0007}");
        assert_eq!(t, vec![(kind::ERROR, "\u{0007}".to_string())]);
    }
}
