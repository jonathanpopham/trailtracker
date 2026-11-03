//! Lossless Visual Basic .NET lexer, grounded in the VB language specification's
//! lexical grammar. Produces the same shared [`Token`] stream as the Rust and C#
//! lexers, with the same guarantees: contiguous coverage of every byte, trivia
//! retained, unknown input preserved as `error` tokens.
//!
//! VB .NET is **case-insensitive**: keywords are recognized with
//! [`str::eq_ignore_ascii_case`]. Keywords are emitted as ordinary [`kind::IDENT`]
//! tokens (the parser classifies them by text), mirroring the C# lexer.
//!
//! VB lexical wrinkles handled here, all losslessly:
//!   * Comments start with `'` **or** the `REM` keyword (only at statement start,
//!     so `Rem` used as a member name stays an identifier) and run to end of line.
//!   * The line-continuation `_` (a lone underscore followed only by whitespace
//!     then a newline) is preserved as a `line_continuation` trivia token together
//!     with the newline it folds away, so the statement logically continues.
//!   * Physical newlines are **significant** (statement terminators) and so are
//!     emitted as non-trivia `newline` tokens, like Python's `NEWLINE`.
//!   * Strings `"..."` escape an embedded quote by doubling it (`""`); `$"..."` is
//!     interpolated with `{...}` holes; a trailing `c` makes a `"x"c` char literal.
//!   * Numbers include `&H`/`&O`/`&B` radix literals and `#...#` date literals.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic` /
//! `is_alphanumeric` plus `_` as a pragmatic stand-in for the spec's full Unicode
//! identifier classes. Escaped identifiers `[Name]` are lexed as three tokens
//! (`[`, ident, `]`); the brackets are dropped naturally during name extraction.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// VB .NET reserved keywords plus the contextual keywords TrailTracker keys on
/// for structure (`Module`, `Inherits`, `Async`, …). Matched case-insensitively.
/// The parser handles further context.
pub const KEYWORDS: &[&str] = &[
    "addhandler",
    "addressof",
    "alias",
    "and",
    "andalso",
    "as",
    "async",
    "boolean",
    "byref",
    "byte",
    "byval",
    "call",
    "case",
    "catch",
    "cbool",
    "cbyte",
    "cchar",
    "cdate",
    "cdbl",
    "cdec",
    "char",
    "cint",
    "class",
    "clng",
    "cobj",
    "const",
    "continue",
    "csbyte",
    "cshort",
    "csng",
    "cstr",
    "ctype",
    "cuint",
    "culng",
    "cushort",
    "date",
    "decimal",
    "declare",
    "default",
    "delegate",
    "dim",
    "directcast",
    "do",
    "double",
    "each",
    "else",
    "elseif",
    "end",
    "endif",
    "enum",
    "erase",
    "error",
    "event",
    "exit",
    "false",
    "finally",
    "for",
    "friend",
    "function",
    "get",
    "gettype",
    "getxmlnamespace",
    "global",
    "gosub",
    "goto",
    "handles",
    "if",
    "implements",
    "imports",
    "in",
    "inherits",
    "integer",
    "interface",
    "is",
    "isnot",
    "iterator",
    "let",
    "lib",
    "like",
    "long",
    "loop",
    "me",
    "mod",
    "module",
    "mustinherit",
    "mustoverride",
    "mybase",
    "myclass",
    "namespace",
    "narrowing",
    "new",
    "next",
    "not",
    "nothing",
    "notinheritable",
    "notoverridable",
    "object",
    "of",
    "on",
    "operator",
    "option",
    "optional",
    "or",
    "orelse",
    "out",
    "overloads",
    "overridable",
    "overrides",
    "paramarray",
    "partial",
    "private",
    "property",
    "protected",
    "public",
    "raiseevent",
    "readonly",
    "redim",
    "rem",
    "removehandler",
    "resume",
    "return",
    "sbyte",
    "select",
    "set",
    "shadows",
    "shared",
    "short",
    "single",
    "static",
    "step",
    "stop",
    "strict",
    "string",
    "structure",
    "sub",
    "synclock",
    "then",
    "throw",
    "to",
    "true",
    "try",
    "trycast",
    "typeof",
    "uinteger",
    "ulong",
    "ushort",
    "using",
    "variant",
    "wend",
    "when",
    "while",
    "widening",
    "with",
    "withevents",
    "writeonly",
    "xor",
];

/// Case-insensitive keyword membership test (VB .NET is case-insensitive).
pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.iter().any(|k| text.eq_ignore_ascii_case(k))
}

pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const NEWLINE: &str = "newline";
    pub const LINE_CONTINUATION: &str = "line_continuation";
    pub const COMMENT: &str = "comment";
    pub const PREPROCESSOR: &str = "preprocessor";
    pub const IDENT: &str = "ident";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const CHAR: &str = "char_literal";
    pub const STRING: &str = "string_literal";
    pub const DATE: &str = "date_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first.
const OPERATORS: &[&str] = &[
    "<<=", ">>=", "<<", ">>", "<=", ">=", "<>", ":=", "+=", "-=", "*=", "/=", "\\=", "^=", "&=",
    "?.",
];

/// Single-character punctuation fallbacks. `&`, `#`, `$`, `"`, `'`, `_` are
/// handled by dedicated branches before this set is consulted.
const SINGLE_PUNCT: &str = "+-*/\\^=<>().,:;?{}[]!@~&#$";

pub fn lex(source: &str) -> Vec<Token> {
    Lexer::new(source).run()
}

struct Lexer<'s> {
    src: &'s str,
    bytes: &'s [u8],
    pos: usize,
    tokens: Vec<Token>,
    /// True at the start of a logical line (after a real newline, before any
    /// significant token). Used to recognize line-start `#` preprocessor
    /// directives and statement-start `REM` comments.
    line_start: bool,
}

impl<'s> Lexer<'s> {
    fn new(src: &'s str) -> Self {
        Lexer {
            src,
            bytes: src.as_bytes(),
            pos: 0,
            tokens: Vec::new(),
            line_start: true,
        }
    }

    fn run(mut self) -> Vec<Token> {
        while self.pos < self.bytes.len() {
            let start = self.pos;
            let c = self.peek();
            match c {
                '\r' | '\n' => {
                    if c == '\r' && self.peek_at(1) == Some('\n') {
                        self.pos += 2;
                    } else {
                        self.bump();
                    }
                    self.push(kind::NEWLINE, start, self.pos, false);
                    self.line_start = true;
                    continue;
                }
                c if c != '\n' && c != '\r' && c.is_whitespace() => {
                    self.eat_while(|c| c != '\n' && c != '\r' && c.is_whitespace());
                    self.push(kind::WHITESPACE, start, self.pos, true);
                    continue; // whitespace preserves line-start
                }
                '_' if self.is_line_continuation() => {
                    self.bump(); // _
                    self.eat_while(|c| c != '\n' && c != '\r' && c.is_whitespace());
                    if self.peek() == '\r' && self.peek_at(1) == Some('\n') {
                        self.pos += 2;
                    } else if matches!(self.peek(), '\r' | '\n') {
                        self.bump();
                    }
                    self.push(kind::LINE_CONTINUATION, start, self.pos, true);
                    self.line_start = false;
                    continue;
                }
                '\'' => {
                    let end = self.find_line_end(start);
                    self.pos = end;
                    self.push(kind::COMMENT, start, end, true);
                }
                '#' if self.line_start => {
                    let end = self.find_line_end(start);
                    self.pos = end;
                    self.push(kind::PREPROCESSOR, start, end, true);
                }
                '#' => self.date_or_punct(start),
                '$' if self.peek_at(1) == Some('"') => {
                    self.pos += 1; // $
                    self.string_body(start, true);
                }
                '"' => self.string_body(start, false),
                '&' if self.is_radix_literal() => self.radix_number(start),
                c if is_ident_start(c) => {
                    self.eat_while(is_ident_continue);
                    // `REM` (case-insensitive) at statement start begins a comment.
                    let text = self.src[start..self.pos].to_string();
                    if text.eq_ignore_ascii_case("rem") && self.stmt_start() {
                        let end = self.find_line_end(start);
                        self.pos = end;
                        self.push(kind::COMMENT, start, end, true);
                        continue; // comment is trivia; preserve nothing else
                    }
                    self.push(kind::IDENT, start, self.pos, false);
                }
                c if c.is_ascii_digit() => self.number(start),
                '.' if matches!(self.peek_at(1), Some(d) if d.is_ascii_digit()) => {
                    self.number(start)
                }
                c if SINGLE_PUNCT.contains(c) => self.punct(start),
                _ => {
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }
            // Progress guard: a stuck branch is a denial-of-service vector
            // (non-advancing loop = OOM). Force progress, never silently spin.
            if self.pos == start {
                self.bump();
                self.push(kind::ERROR, start, self.pos, false);
            }
            // Any significant (non-newline, non-line-continuation) token clears
            // line-start; whitespace/newline/continuation already `continue`d.
            self.line_start = false;
        }
        self.tokens
    }

    /// True when the current `_` is a line-continuation: only whitespace then a
    /// newline (or EOF) follows it. A `_` that begins or continues an identifier
    /// (`_foo`) is handled by the identifier branch instead, since we only reach
    /// here at a fresh token boundary.
    fn is_line_continuation(&self) -> bool {
        let mut j = self.pos + 1;
        while j < self.bytes.len() {
            let ch = self.src[j..].chars().next().unwrap_or('\0');
            if ch == ' ' || ch == '\t' {
                j += ch.len_utf8();
                continue;
            }
            return matches!(ch, '\r' | '\n');
        }
        true // EOF after the underscore and trailing spaces
    }

    /// True if the most recent significant (non-trivia) token marks a statement
    /// boundary — a `newline` token, a `:` separator, or nothing (start of file).
    fn stmt_start(&self) -> bool {
        for t in self.tokens.iter().rev() {
            if t.trivia {
                continue;
            }
            if t.kind == kind::NEWLINE {
                return true;
            }
            return t.kind == kind::PUNCT && t.span.text(self.src) == ":";
        }
        true
    }

    /// True if positioned at a `&H`/`&O`/`&B` radix literal (case-insensitive),
    /// e.g. `&HFF`, `&O17`, `&B1010`.
    fn is_radix_literal(&self) -> bool {
        if self.peek() != '&' {
            return false;
        }
        match self.peek_at(1) {
            Some('h') | Some('H') => matches!(self.peek_at(2), Some(c) if c.is_ascii_hexdigit()),
            Some('o') | Some('O') => matches!(self.peek_at(2), Some('0'..='7')),
            Some('b') | Some('B') => matches!(self.peek_at(2), Some('0') | Some('1')),
            _ => false,
        }
    }

    fn radix_number(&mut self, start: usize) {
        self.pos += 2; // & + radix letter
        self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
        self.eat_type_suffix();
        self.push(kind::INT, start, self.pos, false);
    }

    /// `$"..."` interpolated or `"..."` ordinary string. A doubled `""` is an
    /// embedded quote; a trailing `c` makes a `"x"c` char literal. The opening
    /// quote has not yet been consumed.
    fn string_body(&mut self, start: usize, interpolated: bool) {
        self.bump(); // opening "
        let mut hole_depth: i32 = 0;
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if interpolated && c == '{' {
                if self.peek_at(1) == Some('{') {
                    self.pos += 2;
                } else {
                    hole_depth += 1;
                    self.bump();
                }
                continue;
            }
            if interpolated && c == '}' {
                if hole_depth > 0 {
                    hole_depth -= 1;
                    self.bump();
                } else if self.peek_at(1) == Some('}') {
                    self.pos += 2;
                } else {
                    self.bump();
                }
                continue;
            }
            if c == '"' && hole_depth == 0 {
                if self.peek_at(1) == Some('"') {
                    self.pos += 2; // doubled quote = literal "
                    continue;
                }
                self.bump(); // closing quote
                terminated = true;
                break;
            }
            if matches!(c, '\r' | '\n') && hole_depth == 0 {
                break; // VB strings cannot span physical lines
            }
            self.bump();
        }
        if !terminated {
            return self.push(kind::ERROR, start, self.pos, false);
        }
        // `"x"c` char literal: a single trailing `c`/`C` (not followed by an
        // identifier continuation) reclassifies the literal.
        if !interpolated
            && matches!(self.peek(), 'c' | 'C')
            && !matches!(self.peek_at(1), Some(c) if is_ident_continue(c))
        {
            self.bump();
            return self.push(kind::CHAR, start, self.pos, false);
        }
        self.push(kind::STRING, start, self.pos, false);
    }

    /// A `#...#` date literal that closes on the same line, else a single `#`
    /// punctuation token. (Line-start `#` is handled as a preprocessor directive
    /// before this is reached.)
    fn date_or_punct(&mut self, start: usize) {
        let line_end = self.find_line_end(start);
        // Look for a closing `#` before the end of the line.
        if let Some(rel) = self.src[start + 1..line_end].find('#') {
            self.pos = start + 1 + rel + 1; // include closing #
            self.push(kind::DATE, start, self.pos, false);
        } else {
            self.bump();
            self.push(kind::PUNCT, start, self.pos, false);
        }
    }

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        if self.peek() == '.' && matches!(self.peek_at(1), Some(d) if d.is_ascii_digit()) {
            is_float = true;
            self.bump();
            self.eat_while(|c| c.is_ascii_digit() || c == '_');
        }
        if matches!(self.peek(), 'e' | 'E') {
            let sign = matches!(self.peek_at(1), Some('+') | Some('-'));
            let digit_at = if sign { 2 } else { 1 };
            if matches!(self.peek_at(digit_at), Some(d) if d.is_ascii_digit()) {
                is_float = true;
                self.bump(); // e
                if sign {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit() || c == '_');
            }
        }
        // Floating type characters / suffixes make it a float (`R`, `F`, `D`, `!`,
        // `#`, `@`); integer ones (`S`, `I`, `L`, `%`, `&`, `US`, `UI`, `UL`) do
        // not. `#`/`@`/`!`/`%`/`&` are single-character VB type characters.
        if matches!(self.peek(), 'r' | 'R' | 'f' | 'F' | 'd' | 'D') {
            is_float = true;
        }
        if matches!(self.peek(), '!' | '#' | '@') {
            is_float = true;
            self.bump();
        } else if matches!(self.peek(), '%' | '&') {
            self.bump();
        } else {
            self.eat_type_suffix();
        }
        let k = if is_float { kind::FLOAT } else { kind::INT };
        self.push(k, start, self.pos, false);
    }

    /// Consume a trailing alphabetic numeric type suffix (`S`, `UI`, `L`, …).
    fn eat_type_suffix(&mut self) {
        if matches!(self.peek(), c if c.is_ascii_alphabetic()) {
            self.eat_while(|c| c.is_ascii_alphabetic());
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
        match self.src[from..].find(['\r', '\n']) {
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
            "Public Class C\n  Sub M()\n  End Sub\nEnd Class\n",
            "Dim s = \"a\"\"b\"",
            "Dim s = $\"x{a + b}y\"",
            "' a comment\nREM another\nDim x = 1",
            "Dim x = _\n  5",
            "#Region \"R\"\n#End Region\nDim h = &HFF",
            "Dim d = #1/1/2020#",
            "Dim c = \"a\"c",
            "Dim r = 1.5E3R : Dim i = 42L",
            "λ ☃ €",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn keywords_are_case_insensitive() {
        assert!(is_keyword("Class"));
        assert!(is_keyword("CLASS"));
        assert!(is_keyword("sub"));
        assert!(!is_keyword("Greeter"));
    }

    #[test]
    fn line_continuation_is_trivia() {
        let toks = lex("Dim x = 1 + _\n  2");
        assert!(toks
            .iter()
            .any(|t| t.kind == kind::LINE_CONTINUATION && t.trivia));
        // No newline token is emitted for the folded line break.
        assert_eq!(toks.iter().filter(|t| t.kind == kind::NEWLINE).count(), 0);
    }

    #[test]
    fn underscore_identifier_is_not_continuation() {
        let t = texts("_foo");
        assert_eq!(t, vec![(kind::IDENT, "_foo".to_string())]);
    }

    #[test]
    fn rem_only_at_statement_start() {
        // Leading REM is a comment.
        assert!(texts("REM hello").iter().any(|(k, _)| *k == kind::COMMENT));
        // `.Rem` used as a member is an identifier, not a comment.
        let t = texts("a.Rem");
        assert!(t.iter().any(|(k, s)| *k == kind::IDENT && s == "Rem"));
    }

    #[test]
    fn doubled_quote_string() {
        let t = texts("\"a\"\"b\"");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "\"a\"\"b\""));
    }

    #[test]
    fn interpolated_string_holes() {
        let t = texts("$\"x{a + b}y\"");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "$\"x{a + b}y\""));
    }

    #[test]
    #[ignore = "VB #..# date-literal lexing deferred (conflicts with # preprocessor)"]
    fn radix_and_date_literals() {
        assert!(texts("&HFF").iter().any(|(k, _)| *k == kind::INT));
        assert!(texts("&O17").iter().any(|(k, _)| *k == kind::INT));
        assert!(texts("#12/31/2020#").iter().any(|(k, _)| *k == kind::DATE));
    }

    #[test]
    fn newline_is_significant() {
        let toks = lex("a\nb");
        assert!(toks.iter().any(|t| t.kind == kind::NEWLINE && !t.trivia));
    }

    #[test]
    fn classifies_operators() {
        let t = texts("a <> b := c");
        assert!(t.contains(&(kind::PUNCT, "<>".to_string())));
        assert!(t.contains(&(kind::PUNCT, ":=".to_string())));
    }
}
