//! Lossless Zig lexer, grounded in the Zig language reference token grammar.
//!
//! Guarantees (identical contract to the Rust/Go/Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (whitespace, `//` line comments — including `///` doc comments and
//!   `//!` container/module doc comments) are emitted as `trivia` tokens, never
//!   discarded. Zig has **no** block comments (`/*` is just `/` then `*`).
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//! - The main run loop advances `pos` on every iteration; a final progress guard
//!   consumes one byte as `error` if (defensively) nothing moved. A non-advancing
//!   loop would be an infinite loop, so the guard is a hard requirement.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_` as a pragmatic stand-in for Zig's ASCII-only
//! identifier rules; anything outside still lands in the tree as a covered token,
//! never dropped.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Zig keywords. Like the Rust/Go lexers these lex as `ident` tokens; the parser
/// distinguishes them via [`is_keyword`]. Primitives (`u8`, `void`, `bool`, …)
/// and predeclared values (`true`, `false`, `null`, `undefined`) are *not*
/// keywords — they are ordinary identifiers.
pub const KEYWORDS: &[&str] = &[
    "addrspace",
    "align",
    "allowzero",
    "and",
    "anyframe",
    "anytype",
    "asm",
    "async",
    "await",
    "break",
    "callconv",
    "catch",
    "comptime",
    "const",
    "continue",
    "defer",
    "else",
    "enum",
    "errdefer",
    "error",
    "export",
    "extern",
    "fn",
    "for",
    "if",
    "inline",
    "linksection",
    "noalias",
    "noinline",
    "nosuspend",
    "opaque",
    "or",
    "orelse",
    "packed",
    "pub",
    "resume",
    "return",
    "struct",
    "suspend",
    "switch",
    "test",
    "threadlocal",
    "try",
    "union",
    "unreachable",
    "usingnamespace",
    "var",
    "volatile",
    "while",
];

pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.contains(&text)
}

/// Token kind labels. Stored on the CST as `&'static str` so the tree stays
/// uniform and JSON-friendly.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const LINE_COMMENT: &str = "line_comment";
    pub const DOC_COMMENT: &str = "doc_comment";
    pub const CONTAINER_DOC_COMMENT: &str = "container_doc_comment";
    pub const IDENT: &str = "ident";
    pub const BUILTIN: &str = "builtin";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const CHAR: &str = "char_literal";
    pub const STRING: &str = "string_literal";
    pub const C_STRING: &str = "c_string_literal";
    pub const MULTILINE_STRING: &str = "multiline_string_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators/punctuation, longest first so the scanner is
/// greedy-correct (`<<|=` before `<<|` before `<<`, `...` before `..`).
const OPERATORS: &[&str] = &[
    // 4-char
    "<<|=", // 3-char
    "...", "<<=", ">>=", "+%=", "-%=", "*%=", "+|=", "-|=", "*|=", "<<|", // 2-char
    "..", "++", "**", "+%", "-%", "*%", "+|", "-|", "*|", "=>", "->", "==", "!=", "<=", ">=", "<<",
    ">>", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", ".*", ".?",
];

const SINGLE_PUNCT: &str = "+-*/%!&|^~<>=.,;:?()[]{}@";

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
                c if c == ' ' || c == '\t' || c == '\n' || c == '\r' || c.is_whitespace() => {
                    self.eat_while(|c| c.is_whitespace());
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                '/' if self.peek_at(1) == Some('/') => self.line_comment(start),
                '\\' if self.peek_at(1) == Some('\\') => self.multiline_string(start),
                '"' => self.string_literal(start, kind::STRING),
                '\'' => self.char_literal(start),
                'c' if self.peek_at(1) == Some('"') => {
                    self.bump(); // c
                    self.string_literal(start, kind::C_STRING);
                }
                '@' => self.at_sign(start),
                c if is_ident_start(c) => self.ident(start),
                c if c.is_ascii_digit() => self.number(start),
                c if SINGLE_PUNCT.contains(c) => self.punct(start),
                _ => {
                    // Unknown byte/char — preserve it as an explicit error token.
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }

            // Progress guard: every iteration MUST advance `pos`. A non-advancing
            // loop is an infinite loop (OOM); if a branch somehow failed to move,
            // consume one char as an `error` so the lexer always terminates.
            if self.pos == start {
                self.bump();
                self.push(kind::ERROR, start, self.pos, false);
            }
        }
        self.tokens
    }

    // --- scanners -----------------------------------------------------------

    /// `//` line comment. `//!` is a container/module doc comment; `///` (but not
    /// `////`) is a doc comment; everything else is an ordinary line comment. All
    /// three are trivia.
    fn line_comment(&mut self, start: usize) {
        let rest = &self.src[start..];
        let k = if rest.starts_with("//!") {
            kind::CONTAINER_DOC_COMMENT
        } else if rest.starts_with("///") && !rest.starts_with("////") {
            kind::DOC_COMMENT
        } else {
            kind::LINE_COMMENT
        };
        let end = self.find_line_end(start);
        self.pos = end;
        self.push(k, start, end, true);
    }

    /// A multiline string line: `\\` followed by the rest of the line (the
    /// terminating newline is a separate whitespace token). Non-trivia — it is
    /// part of a value expression. Consecutive `\\` lines each lex as their own
    /// `multiline_string` token, which is perfectly lossless.
    fn multiline_string(&mut self, start: usize) {
        let end = self.find_line_end(start);
        self.pos = end;
        self.push(kind::MULTILINE_STRING, start, end, false);
    }

    fn ident(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        self.push(kind::IDENT, start, self.pos, false);
    }

    /// `@import`/`@This`/… builtins, `@"quoted identifier"`, or a lone `@`.
    fn at_sign(&mut self, start: usize) {
        match self.peek_at(1) {
            Some('"') => {
                // `@"weird name"` — a quoted identifier; lex as an ident so names
                // and calls see it uniformly.
                self.bump(); // @
                self.scan_dquote();
                self.push(kind::IDENT, start, self.pos, false);
            }
            Some(c) if is_ident_start(c) => {
                self.bump(); // @
                self.eat_while(is_ident_continue);
                self.push(kind::BUILTIN, start, self.pos, false);
            }
            _ => {
                self.bump(); // lone @
                self.push(kind::PUNCT, start, self.pos, false);
            }
        }
    }

    /// Scan a `"..."` literal (caller already consumed any `c` prefix). Handles
    /// escapes; an unterminated literal (or one broken by a newline) becomes an
    /// `error` token over what was consumed.
    fn string_literal(&mut self, start: usize, kind: &'static str) {
        let terminated = self.scan_dquote();
        let token_kind = if terminated { kind } else { kind::ERROR };
        self.push(token_kind, start, self.pos, false);
    }

    /// Consume `"..."` from the opening quote through the closing quote, honoring
    /// backslash escapes and stopping at a raw newline. Returns whether the
    /// literal was terminated. Advances `pos` past whatever it covered.
    fn scan_dquote(&mut self) -> bool {
        self.bump(); // opening "
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '\\' {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
            } else if c == '"' {
                self.bump();
                return true;
            } else if c == '\n' {
                return false;
            } else {
                self.bump();
            }
        }
        false
    }

    /// Char literal `'x'` / `'\n'` / `'\u{1F600}'`: backslash escapes; an
    /// unterminated literal (or one broken by a newline) becomes an `error`.
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
        if self.peek() == '0' && matches!(self.peek_at(1), Some('x') | Some('X')) {
            self.pos += 2;
            self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
            if self.peek() == '.'
                && self
                    .peek_at(1)
                    .map(|c| c.is_ascii_hexdigit())
                    .unwrap_or(false)
            {
                is_float = true;
                self.bump();
                self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
            }
            // Hex floats use a binary exponent `p`/`P`.
            if matches!(self.peek(), 'p' | 'P') {
                is_float = true;
                self.eat_exponent();
            }
        } else if self.peek() == '0' && matches!(self.peek_at(1), Some('o') | Some('O')) {
            self.pos += 2;
            self.eat_while(|c| ('0'..='7').contains(&c) || c == '_');
        } else if self.peek() == '0' && matches!(self.peek_at(1), Some('b') | Some('B')) {
            self.pos += 2;
            self.eat_while(|c| c == '0' || c == '1' || c == '_');
        } else {
            self.eat_while(|c| c.is_ascii_digit() || c == '_');
            // Fractional part only when a digit follows the dot, so a field access
            // or method call (`x.0`, `1.method`) is not swallowed.
            if self.peek() == '.' && self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) {
                is_float = true;
                self.bump();
                self.eat_while(|c| c.is_ascii_digit() || c == '_');
            }
            if matches!(self.peek(), 'e' | 'E') {
                is_float = true;
                self.eat_exponent();
            }
        }
        let k = if is_float { kind::FLOAT } else { kind::INT };
        self.push(k, start, self.pos, false);
    }

    /// Consume an exponent: the `e`/`E`/`p`/`P` marker, an optional sign, and the
    /// digit run. Only called when the marker is current.
    fn eat_exponent(&mut self) {
        self.bump(); // e / E / p / P
        if matches!(self.peek(), '+' | '-') {
            self.bump();
        }
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
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
            "const std = @import(\"std\");\n",
            "pub fn main() void {}\n",
            "//! module doc\n/// item doc\n// plain\nconst x = 1;\n",
            "const s =\n    \\\\line one\n    \\\\line two\n;\n",
            "const c = 0x1p-2 + 0o17 + 0b1010 + 1_000 + 3.14;\n",
            "const ch = 'a'; const e = '\\n'; const cs = c\"raw\";",
            "x +%= 1; y <<|= 2; z .* = w.?;",
            "λ := \"☃ €\"; // unicode",
            "",
            "\n\n   \n// trailing\n",
            "const Q = @\"weird name\";",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("pub fn add(a: i32, b: i32) i32 { return a + b; }");
        assert!(t.contains(&(kind::IDENT, "fn".to_string())));
        assert!(t.contains(&(kind::IDENT, "add".to_string())));
        assert!(is_keyword("fn"));
        assert!(is_keyword("struct"));
        assert!(!is_keyword("add"));
        // primitives / predeclared are NOT keywords
        assert!(!is_keyword("void"));
        assert!(!is_keyword("u8"));
        assert!(!is_keyword("true"));
    }

    #[test]
    fn builtins_and_imports() {
        let t = texts("const std = @import(\"std\"); const T = @This();");
        assert!(t.contains(&(kind::BUILTIN, "@import".to_string())));
        assert!(t.contains(&(kind::BUILTIN, "@This".to_string())));
        assert!(t.contains(&(kind::STRING, "\"std\"".to_string())));
    }

    #[test]
    fn doc_comment_variants() {
        let t = texts("//! container\n/// doc\n//// plain\n// plain2\n");
        assert!(t.iter().any(|(k, _)| *k == kind::CONTAINER_DOC_COMMENT));
        assert!(t.iter().any(|(k, _)| *k == kind::DOC_COMMENT));
        // `////` is NOT a doc comment in Zig.
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::LINE_COMMENT && s.starts_with("////")));
    }

    #[test]
    fn multiline_string_lines() {
        let t = texts("\\\\one\n\\\\two\n");
        let mls: Vec<_> = t
            .iter()
            .filter(|(k, _)| *k == kind::MULTILINE_STRING)
            .collect();
        assert_eq!(mls.len(), 2, "two multiline-string lines");
        assert_eq!(mls[0].1, "\\\\one");
    }

    #[test]
    fn no_block_comments() {
        // `/*` is just punct in Zig, never a comment.
        let t = texts("a /* b */ c");
        assert!(t.iter().all(|(k, _)| *k != kind::LINE_COMMENT));
        assert!(t.contains(&(kind::PUNCT, "/".to_string())));
        assert!(t.contains(&(kind::PUNCT, "*".to_string())));
    }

    #[test]
    fn saturating_and_wrapping_operators() {
        let t = texts("a +% b -% c *| d +| e");
        assert!(t.contains(&(kind::PUNCT, "+%".to_string())));
        assert!(t.contains(&(kind::PUNCT, "-%".to_string())));
        assert!(t.contains(&(kind::PUNCT, "*|".to_string())));
        assert!(t.contains(&(kind::PUNCT, "+|".to_string())));
        assert!(t.iter().all(|(k, _)| *k != kind::ERROR));
    }

    #[test]
    fn deref_and_optional_unwrap() {
        let t = texts("ptr.* orelse x.?");
        assert!(t.contains(&(kind::PUNCT, ".*".to_string())));
        assert!(t.contains(&(kind::PUNCT, ".?".to_string())));
    }
}
