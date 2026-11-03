//! Lossless XML lexer — the shared token layer for XML-carried formats
//! (Salesforce metadata today; MSBuild project files and HTML-adjacent tiers
//! later). Not a validating XML processor: a coverage-honest tokenizer for
//! well-formed-ish documents.
//!
//! Guarantees (identical contract to every other TrailTracker lexer):
//! - Every byte lands in exactly one token (contiguous spans): concatenating
//!   token texts reconstructs the source verbatim.
//! - Trivia (whitespace between markup, comments) is kept, never discarded.
//! - Unclassifiable bytes become `error` tokens over the exact bytes.
//! - `pos` advances every loop iteration — the lexer cannot spin.
//!
//! The lexer is modal: between markup it emits `text` runs; inside a tag it
//! emits names, `=`, and quoted strings. Character-data runs that are entirely
//! whitespace are trivia (inter-element formatting); mixed text is not.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Token kind labels stored on the CST.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    /// Character data between markup that is not all-whitespace.
    pub const TEXT: &str = "text";
    /// `<!-- … -->` (trivia).
    pub const COMMENT: &str = "comment";
    /// `<![CDATA[ … ]]>` — kept as one covered token, semantically text.
    pub const CDATA: &str = "cdata";
    /// `<? … ?>` processing instruction / XML declaration.
    pub const PI: &str = "pi";
    /// `<! … >` declaration (DOCTYPE et al.), one covered token.
    pub const DOCTYPE: &str = "doctype";
    pub const LT: &str = "lt";
    pub const LT_SLASH: &str = "lt_slash";
    pub const GT: &str = "gt";
    pub const SLASH_GT: &str = "slash_gt";
    /// Tag or attribute name (XML name chars incl. `:`, `-`, `.`).
    pub const NAME: &str = "name";
    pub const EQ: &str = "eq";
    /// Quoted attribute value, quotes included.
    pub const STRING: &str = "string";
    pub const ERROR: &str = "error";
}

pub fn lex(source: &str) -> Vec<Token> {
    Lexer {
        bytes: source.as_bytes(),
        pos: 0,
        in_tag: false,
        tokens: Vec::new(),
    }
    .run()
}

struct Lexer<'s> {
    bytes: &'s [u8],
    pos: usize,
    in_tag: bool,
    tokens: Vec<Token>,
}

impl<'s> Lexer<'s> {
    fn run(mut self) -> Vec<Token> {
        while self.pos < self.bytes.len() {
            let start = self.pos;
            if self.in_tag {
                self.lex_in_tag(start);
            } else {
                self.lex_content(start);
            }
            debug_assert!(self.pos > start, "lexer must always advance");
            if self.pos == start {
                // Belt-and-braces progress guard for release builds.
                self.pos += 1;
                self.push(kind::ERROR, start, self.pos, false);
            }
        }
        self.tokens
    }

    fn lex_content(&mut self, start: usize) {
        if self.bytes[start] == b'<' {
            if self.starts_with(start, b"<!--") {
                let end = self
                    .find(start + 4, b"-->")
                    .map_or(self.bytes.len(), |i| i + 3);
                self.pos = end;
                self.push(kind::COMMENT, start, end, true);
            } else if self.starts_with(start, b"<![CDATA[") {
                let end = self
                    .find(start + 9, b"]]>")
                    .map_or(self.bytes.len(), |i| i + 3);
                self.pos = end;
                self.push(kind::CDATA, start, end, false);
            } else if self.starts_with(start, b"<?") {
                let end = self
                    .find(start + 2, b"?>")
                    .map_or(self.bytes.len(), |i| i + 2);
                self.pos = end;
                self.push(kind::PI, start, end, false);
            } else if self.starts_with(start, b"<!") {
                let end = self.bytes[start..]
                    .iter()
                    .position(|&b| b == b'>')
                    .map_or(self.bytes.len(), |i| start + i + 1);
                self.pos = end;
                self.push(kind::DOCTYPE, start, end, false);
            } else if self.starts_with(start, b"</") {
                self.pos = start + 2;
                self.push(kind::LT_SLASH, start, self.pos, false);
                self.in_tag = true;
            } else {
                self.pos = start + 1;
                self.push(kind::LT, start, self.pos, false);
                self.in_tag = true;
            }
            return;
        }
        // Character data: run to the next `<` (or EOF). All-whitespace runs are
        // trivia (inter-element formatting); anything else is real text.
        let end = self.bytes[start..]
            .iter()
            .position(|&b| b == b'<')
            .map_or(self.bytes.len(), |i| start + i);
        self.pos = end;
        let all_ws = self.bytes[start..end]
            .iter()
            .all(|b| b.is_ascii_whitespace());
        if all_ws {
            self.push(kind::WHITESPACE, start, end, true);
        } else {
            self.push(kind::TEXT, start, end, false);
        }
    }

    fn lex_in_tag(&mut self, start: usize) {
        let b = self.bytes[start];
        match b {
            b'>' => {
                self.pos = start + 1;
                self.push(kind::GT, start, self.pos, false);
                self.in_tag = false;
            }
            b'/' if self.starts_with(start, b"/>") => {
                self.pos = start + 2;
                self.push(kind::SLASH_GT, start, self.pos, false);
                self.in_tag = false;
            }
            b'=' => {
                self.pos = start + 1;
                self.push(kind::EQ, start, self.pos, false);
            }
            b'"' | b'\'' => {
                let quote = b;
                let end = self.bytes[start + 1..]
                    .iter()
                    .position(|&c| c == quote)
                    .map_or(self.bytes.len(), |i| start + 1 + i + 1);
                self.pos = end;
                self.push(kind::STRING, start, end, false);
            }
            c if c.is_ascii_whitespace() => {
                let end = self.bytes[start..]
                    .iter()
                    .position(|&c| !c.is_ascii_whitespace())
                    .map_or(self.bytes.len(), |i| start + i);
                self.pos = end;
                self.push(kind::WHITESPACE, start, end, true);
            }
            c if is_name_byte(c) => {
                let end = self.bytes[start..]
                    .iter()
                    .position(|&c| !is_name_byte(c))
                    .map_or(self.bytes.len(), |i| start + i);
                self.pos = end;
                self.push(kind::NAME, start, end, false);
            }
            _ => {
                self.pos = start + 1;
                self.push(kind::ERROR, start, self.pos, false);
            }
        }
    }

    fn starts_with(&self, at: usize, pat: &[u8]) -> bool {
        self.bytes[at..].starts_with(pat)
    }

    /// Byte offset of `pat` at or after `from`, if any.
    fn find(&self, from: usize, pat: &[u8]) -> Option<usize> {
        if from >= self.bytes.len() {
            return None;
        }
        self.bytes[from..]
            .windows(pat.len())
            .position(|w| w == pat)
            .map(|i| from + i)
    }

    fn push(&mut self, kind: &'static str, start: usize, end: usize, trivia: bool) {
        self.tokens.push(Token {
            kind,
            span: ByteSpan::new(start, end),
            trivia,
        });
    }
}

/// XML name characters, pragmatically ASCII plus anything non-ASCII (kept as a
/// covered name rather than an error, preserving losslessness for exotic
/// documents).
fn is_name_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || matches!(b, b'_' | b':' | b'-' | b'.') || b >= 0x80
}

#[cfg(test)]
mod tests {
    use super::*;

    fn text_of(src: &str, toks: &[Token]) -> String {
        toks.iter().map(|t| t.span.text(src)).collect()
    }

    #[test]
    fn round_trips_every_byte() {
        let src =
            "<?xml version=\"1.0\"?>\n<!-- c -->\n<a x='1'>\n  hi <b/> <![CDATA[raw <>]]>\n</a>\n";
        let toks = lex(src);
        assert_eq!(text_of(src, &toks), src);
        // Contiguous coverage.
        let mut pos = 0usize;
        for t in &toks {
            assert_eq!(t.span.start as usize, pos, "gap before {:?}", t.kind);
            pos = t.span.end as usize;
        }
        assert_eq!(pos, src.len());
    }

    #[test]
    fn classifies_markup_kinds() {
        let src = "<a b=\"v\"><c/></a>";
        let toks = lex(src);
        let kinds: Vec<&str> = toks.iter().map(|t| t.kind).collect();
        assert_eq!(
            kinds,
            vec![
                kind::LT,
                kind::NAME, // a
                kind::WHITESPACE,
                kind::NAME, // b
                kind::EQ,
                kind::STRING,
                kind::GT,
                kind::LT,
                kind::NAME, // c
                kind::SLASH_GT,
                kind::LT_SLASH,
                kind::NAME, // a
                kind::GT,
            ]
        );
    }

    #[test]
    fn whitespace_only_text_is_trivia_mixed_is_not() {
        let src = "<a>\n  </a><b>hi</b>";
        let toks = lex(src);
        let ws = toks.iter().find(|t| t.kind == kind::WHITESPACE).unwrap();
        assert!(ws.trivia);
        let text = toks.iter().find(|t| t.kind == kind::TEXT).unwrap();
        assert!(!text.trivia);
        assert_eq!(text.span.text(src), "hi");
    }

    #[test]
    fn unterminated_constructs_cover_to_eof() {
        for src in ["<!-- open", "<![CDATA[ open", "<?pi open", "<a b=\"open"] {
            let toks = lex(src);
            assert_eq!(text_of(src, &toks), src, "src: {src}");
        }
    }
}
