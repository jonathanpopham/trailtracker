//! Lossless Forth lexer.
//!
//! Forth is a whitespace-delimited stack language: the "grammar" is, almost
//! entirely, *space-separated words*. The few lexical shapes that swallow
//! whitespace and therefore cannot be recovered from a naive word split are
//! handled here as first-class tokens:
//!
//! - `\ …` line comments — `\` is a word, so it only opens a comment when it is
//!   itself whitespace-delimited (followed by whitespace or end-of-file).
//! - `( … )` paren comments — likewise `(` must be followed by whitespace.
//! - `." …"` and `s" …"` strings — the string word (`."`/`s"`) must be followed
//!   by whitespace, then the body runs to the closing `"`.
//! - numbers — a whitespace-delimited word that parses as a Forth numeric literal
//!   (decimal, `$hex`, `#decimal`, `%binary`, optional sign, optional `.`).
//!
//! Guarantees (the same the property harness enforces for every front end):
//! - Every byte is covered by exactly one token (contiguous spans), so the token
//!   stream reconstructs the source verbatim.
//! - Whitespace and both comment forms are emitted as `trivia` tokens, never
//!   dropped.
//! - Anything that cannot be classified becomes an `error` token over its exact
//!   bytes (e.g. an unterminated string). Input is never silently dropped.
//!
//! Scanning is byte-indexed. Token boundaries fall only on ASCII whitespace,
//! `"`, `)`, and `\n` — all single-byte — so a multi-byte UTF-8 word/comment is
//! never split mid-character and losslessness holds for non-ASCII source.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Token kind labels, stored on the CST as `&'static str`.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    /// `\ …` to end of line.
    pub const LINE_COMMENT: &str = "line_comment";
    /// `( … )` inline comment.
    pub const PAREN_COMMENT: &str = "paren_comment";
    /// `." …"` or `s" …"` string literal.
    pub const STRING: &str = "string";
    /// A numeric literal word.
    pub const NUMBER: &str = "number";
    /// Any other whitespace-delimited word.
    pub const WORD: &str = "word";
    /// Unclassifiable bytes (e.g. an unterminated string).
    pub const ERROR: &str = "error";
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
            let b = self.bytes[start];
            if b.is_ascii_whitespace() {
                self.whitespace(start);
            } else if b == b'\\' && self.delim_after(start + 1) {
                self.line_comment(start);
            } else if b == b'(' && self.delim_after(start + 1) {
                self.paren_comment(start);
            } else if (b == b'.' || b == b's' || b == b'S')
                && self.byte_at(start + 1) == Some(b'"')
                && self.delim_after(start + 2)
            {
                self.string(start, start + 2);
            } else {
                self.word(start);
            }

            // Main-loop progress guard: every iteration must advance `pos`. If a
            // branch somehow failed to, consume one byte as an error so the loop
            // can never spin.
            if self.pos == start {
                self.pos = start + 1;
                self.push(kind::ERROR, start, self.pos, false);
            }
        }
        self.tokens
    }

    // --- scanners -----------------------------------------------------------

    fn whitespace(&mut self, start: usize) {
        while self.pos < self.bytes.len() && self.bytes[self.pos].is_ascii_whitespace() {
            self.pos += 1;
        }
        self.push(kind::WHITESPACE, start, self.pos, true);
    }

    /// `\ …` — runs to (but not including) the next newline; the newline is left
    /// for the whitespace scanner. Unterminated at EOF is fine (lossless).
    fn line_comment(&mut self, start: usize) {
        self.pos = start;
        while self.pos < self.bytes.len() && self.bytes[self.pos] != b'\n' {
            self.pos += 1;
        }
        self.push(kind::LINE_COMMENT, start, self.pos, true);
    }

    /// `( … )` — runs to and including the closing `)`. Unterminated at EOF stays
    /// trivia covering the remainder (lossless), mirroring the Rust block comment.
    fn paren_comment(&mut self, start: usize) {
        self.pos = start + 1; // past '('
        while self.pos < self.bytes.len() && self.bytes[self.pos] != b')' {
            self.pos += 1;
        }
        if self.pos < self.bytes.len() {
            self.pos += 1; // closing ')'
        }
        self.push(kind::PAREN_COMMENT, start, self.pos, true);
    }

    /// `." …"` / `s" …"` — `body_start` is just past the opener. Runs to the
    /// closing `"`; an unterminated literal becomes an `error` token.
    fn string(&mut self, start: usize, body_start: usize) {
        self.pos = body_start;
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            if self.bytes[self.pos] == b'"' {
                self.pos += 1;
                terminated = true;
                break;
            }
            self.pos += 1;
        }
        let k = if terminated {
            kind::STRING
        } else {
            kind::ERROR
        };
        self.push(k, start, self.pos, false);
    }

    /// A whitespace-delimited word, classified as a number when it parses as a
    /// Forth numeric literal, otherwise a plain word.
    fn word(&mut self, start: usize) {
        self.pos = start;
        while self.pos < self.bytes.len() && !self.bytes[self.pos].is_ascii_whitespace() {
            self.pos += 1;
        }
        let text = &self.src[start..self.pos];
        let k = if is_number(text) {
            kind::NUMBER
        } else {
            kind::WORD
        };
        self.push(k, start, self.pos, false);
    }

    // --- primitives ---------------------------------------------------------

    fn byte_at(&self, i: usize) -> Option<u8> {
        self.bytes.get(i).copied()
    }

    /// True if position `i` is end-of-input or ASCII whitespace — the condition a
    /// word-marker (`\`, `(`, `."`, `s"`) needs after it to be that marker rather
    /// than part of a longer word.
    fn delim_after(&self, i: usize) -> bool {
        match self.byte_at(i) {
            None => true,
            Some(c) => c.is_ascii_whitespace(),
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

/// True if `s` parses as a Forth numeric literal. Honest scope: decimal with an
/// optional `$`/`#`/`%` base prefix, an optional leading sign, and an optional
/// single `.` (the double-cell marker). It does not chase every vendor extension
/// (`'c'` character literals, `0x…`, locale digits); those simply classify as
/// words, never lost.
fn is_number(s: &str) -> bool {
    let b = s.as_bytes();
    if b.is_empty() {
        return false;
    }
    let mut i = 0usize;
    let mut base: u32 = 10;
    match b[0] {
        b'$' => {
            base = 16;
            i = 1;
        }
        b'#' => {
            base = 10;
            i = 1;
        }
        b'%' => {
            base = 2;
            i = 1;
        }
        _ => {}
    }
    if i < b.len() && (b[i] == b'-' || b[i] == b'+') {
        i += 1;
    }
    let mut digits = 0usize;
    let mut seen_dot = false;
    while i < b.len() {
        let c = b[i];
        if c == b'.' {
            if seen_dot {
                return false;
            }
            seen_dot = true;
            i += 1;
            continue;
        }
        match digit_value(c) {
            Some(v) if v < base => digits += 1,
            _ => return false,
        }
        i += 1;
    }
    digits >= 1
}

fn digit_value(c: u8) -> Option<u32> {
    match c {
        b'0'..=b'9' => Some((c - b'0') as u32),
        b'a'..=b'f' => Some((c - b'a' + 10) as u32),
        b'A'..=b'F' => Some((c - b'A' + 10) as u32),
        _ => None,
    }
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
            ": square dup * ;",
            "\\ a line comment\n42 constant answer",
            "( inline comment ) variable counter",
            ".\" hello world\" cr",
            "s\" path/to/file.fth\" included",
            "\\foo \\ not-a-comment-word then a comment\n",
            "$ff #10 %1010 -7 3.14 +0",
            "λ ☃ €",            // non-ascii words still covered
            ".\" unterminated", // unterminated string -> error, still covered
            "",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn backslash_word_vs_comment() {
        // `\` followed by whitespace is a comment; `\foo` is an ordinary word.
        let t = texts("\\ comment\n\\foo");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::LINE_COMMENT && s == "\\ comment"));
        assert!(t.iter().any(|(k, s)| *k == kind::WORD && s == "\\foo"));
    }

    #[test]
    fn paren_must_be_delimited() {
        // `(` + space opens a comment; `(foo)` is a single word.
        let t = texts("( a comment ) (foo)");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::PAREN_COMMENT && s == "( a comment )"));
        assert!(t.iter().any(|(k, s)| *k == kind::WORD && s == "(foo)"));
    }

    #[test]
    fn strings_capture_bodies() {
        let t = texts(".\" hi there\" s\" file.fth\"");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == ".\" hi there\""));
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "s\" file.fth\""));
    }

    #[test]
    fn classifies_numbers() {
        assert!(is_number("42"));
        assert!(is_number("-7"));
        assert!(is_number("$FF"));
        assert!(is_number("%1010"));
        assert!(is_number("#99"));
        assert!(is_number("3.14"));
        assert!(!is_number("."));
        assert!(!is_number("dup"));
        assert!(!is_number("face")); // hex letters need a $ prefix
        assert!(!is_number("+"));
    }

    #[test]
    fn unterminated_string_is_error() {
        let t = texts(".\" oops");
        assert!(t.iter().any(|(k, s)| *k == kind::ERROR && s == ".\" oops"));
    }
}
