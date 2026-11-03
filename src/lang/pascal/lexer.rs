//! Lossless Object Pascal / Delphi lexer.
//!
//! Guarantees (identical contract to the Rust, Julia, Lua, and Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs, newlines, `//` line comments, `{ … }` and `(* … *)`
//!   block comments — which include `{$…}` compiler directives, kept as ordinary
//!   block comments) are emitted as `trivia` tokens, never discarded. Pascal is
//!   not whitespace-significant; a newline is ordinary `newline` trivia.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped — an unterminated string or comment
//!   is emitted as a token spanning to end of input (string) or as a comment that
//!   runs to EOF.
//!
//! Progress guard: the main run loop asserts forward motion on every iteration —
//! if a scanner ever failed to advance `pos`, one byte is consumed as an `error`
//! token rather than spinning forever (a non-advancing loop is an OOM).
//!
//! Pascal-specific surface the lexer covers:
//! - `//` line comments; `{ … }` and `(* … *)` block comments. Pascal block
//!   comments do **not** nest (a documented language rule), so each runs to its
//!   own closer; a `{`-opened comment closes only on `}`, a `(*` only on `*)`.
//! - Strings `'…'` with the doubled-quote escape `''`; a raw newline ends an
//!   unterminated string as an `error` token (Pascal strings are single-line).
//! - Character codes `#65` (decimal) and `#$41` (hex) — each `#…` is one token,
//!   so `#13#10` lexes as two `char_code` tokens.
//! - Numbers: decimal integers, reals (`3.14`, `1.5e-3`, `1e10`), `$FF` hex,
//!   FPC `&777` octal and `%1010` binary literals.
//! - Identifiers: letter/`_` start, alphanumeric/`_` continue, plus the Delphi
//!   `&`-escaped identifier form (`&begin`) which lexes as an identifier.
//! - A pragmatic set of ASCII operators (`:=`, `<=`, `>=`, `<>`, `..`, the
//!   compound-assignments `+= -= *= /=`, FPC `**`) plus single-char punctuation.
//!
//! Case note: Pascal is case-insensitive. The lexer emits keyword-looking words
//! as plain `ident` tokens; the parser distinguishes them via [`is_keyword`],
//! which compares case-insensitively.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_` as a pragmatic superset of Pascal's ASCII rule.
//! The alternative bracket digraphs `(.` / `.)` are lexed as their component
//! tokens (`(` `.` / `.` `)`) rather than as `[` / `]` — a documented breadth gap
//! that is still byte-for-byte lossless.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Object Pascal / Delphi reserved words and common directives. These lex as
/// `ident` tokens; the parser distinguishes them via [`is_keyword`] (which is
/// case-insensitive). The list is a pragmatic superset covering Delphi and Free
/// Pascal; over-inclusion only affects the parser's keyword test, never
/// losslessness.
pub const KEYWORDS: &[&str] = &[
    "and",
    "array",
    "as",
    "asm",
    "begin",
    "case",
    "class",
    "const",
    "constructor",
    "destructor",
    "dispinterface",
    "div",
    "do",
    "downto",
    "else",
    "end",
    "except",
    "exports",
    "file",
    "finalization",
    "finally",
    "for",
    "function",
    "goto",
    "if",
    "implementation",
    "in",
    "inherited",
    "initialization",
    "inline",
    "interface",
    "is",
    "label",
    "library",
    "mod",
    "nil",
    "not",
    "object",
    "of",
    "operator",
    "or",
    "out",
    "packed",
    "package",
    "procedure",
    "program",
    "property",
    "raise",
    "record",
    "repeat",
    "resourcestring",
    "set",
    "shl",
    "shr",
    "string",
    "then",
    "threadvar",
    "to",
    "try",
    "type",
    "unit",
    "until",
    "uses",
    "var",
    "while",
    "with",
    "xor",
];

/// Case-insensitive reserved-word test (Pascal is case-insensitive).
pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.iter().any(|k| text.eq_ignore_ascii_case(k))
}

/// Token kind labels. Stored on the CST as `&'static str`.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const NEWLINE: &str = "newline";
    pub const LINE_COMMENT: &str = "line_comment";
    pub const BLOCK_COMMENT: &str = "block_comment";
    pub const IDENT: &str = "ident";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const STRING: &str = "string_literal";
    pub const CHAR_CODE: &str = "char_code";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
const OPERATORS: &[&str] = &["**", ":=", "<=", ">=", "<>", "..", "+=", "-=", "*=", "/="];

/// Single-character punctuation. `'` (string), `#` (char code), `$`/`&`/`%`
/// (number prefixes) are handled by dedicated scanners, not here.
const SINGLE_PUNCT: &str = "+-*/=<>()[].,:;^@";

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
                '/' if self.peek_at(1) == Some('/') => self.line_comment(start),
                '{' => self.brace_comment(start),
                '(' if self.peek_at(1) == Some('*') => self.paren_comment(start),
                '\'' => self.string_literal(start),
                '#' => self.char_code(start),
                '$' => self.number(start),
                '&' if self.peek_at(1).map(is_ident_start).unwrap_or(false) => self.ident(start),
                '&' if self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) => {
                    self.number(start)
                }
                '%' if self
                    .peek_at(1)
                    .map(|c| c == '0' || c == '1')
                    .unwrap_or(false) =>
                {
                    self.number(start)
                }
                c if c.is_ascii_digit() => self.number(start),
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

    /// A `{ … }` block comment (including `{$…}` directives). Does not nest; runs
    /// to the next `}` or to EOF. Always trivia, always fully covered → lossless.
    fn brace_comment(&mut self, start: usize) {
        self.bump(); // {
        while self.pos < self.bytes.len() {
            let c = self.peek();
            self.bump();
            if c == '}' {
                break;
            }
        }
        self.push(kind::BLOCK_COMMENT, start, self.pos, true);
    }

    /// A `(* … *)` block comment. Does not nest; runs to the next `*)` or to EOF.
    fn paren_comment(&mut self, start: usize) {
        self.pos += 2; // (*
        while self.pos < self.bytes.len() {
            if self.src[self.pos..].starts_with("*)") {
                self.pos += 2;
                break;
            }
            self.bump();
        }
        self.push(kind::BLOCK_COMMENT, start, self.pos, true);
    }

    /// An identifier (optionally `&`-escaped, e.g. `&begin`). A trailing run of
    /// alphanumerics / `_`.
    fn ident(&mut self, start: usize) {
        if self.peek() == '&' {
            self.bump(); // escape
        }
        self.bump(); // start char (already ident-start)
        self.eat_while(|c| c == '_' || c.is_alphanumeric());
        self.push(kind::IDENT, start, self.pos, false);
    }

    /// A `'…'` string with the doubled-quote escape `''`. A raw newline or EOF
    /// before the closing quote yields an `error` token (still fully covered).
    fn string_literal(&mut self, start: usize) {
        self.bump(); // opening '
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '\'' {
                // A doubled quote is an escaped quote, not the terminator.
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
                break; // unterminated single-line string
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

    /// A `#65` (decimal) or `#$41` (hex) character code. A lone `#` with no digit
    /// is an `error` token.
    fn char_code(&mut self, start: usize) {
        self.bump(); // #
        let ok = if self.peek() == '$' {
            self.bump();
            let before = self.pos;
            self.eat_while(|c| c.is_ascii_hexdigit());
            self.pos > before
        } else {
            let before = self.pos;
            self.eat_while(|c| c.is_ascii_digit());
            self.pos > before
        };
        let token_kind = if ok { kind::CHAR_CODE } else { kind::ERROR };
        self.push(token_kind, start, self.pos, false);
    }

    fn number(&mut self, start: usize) {
        match self.peek() {
            '$' => {
                self.bump();
                self.eat_while(|c| c.is_ascii_hexdigit());
                self.push(kind::INT, start, self.pos, false);
                return;
            }
            '&' => {
                self.bump();
                self.eat_while(|c| ('0'..='7').contains(&c));
                self.push(kind::INT, start, self.pos, false);
                return;
            }
            '%' => {
                self.bump();
                self.eat_while(|c| c == '0' || c == '1');
                self.push(kind::INT, start, self.pos, false);
                return;
            }
            _ => {}
        }
        let mut is_float = false;
        self.eat_while(|c| c.is_ascii_digit());
        // Fractional part only when a digit follows the dot, so `1..10` ranges and
        // `rec.field` access stay separate tokens.
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
        let k = if is_float { kind::FLOAT } else { kind::INT };
        self.push(k, start, self.pos, false);
    }

    fn punct(&mut self, start: usize) {
        for op in OPERATORS {
            if self.src[self.pos..].starts_with(op) {
                self.pos += op.len();
                self.push(kind::PUNCT, start, self.pos, false);
                return;
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
            "procedure Foo;\nbegin\n  Bar;\nend;\n",
            "// line comment\nx := 1;\n",
            "{ a brace comment with {$IFDEF} inside } y := 2;\n",
            "(* a paren-star comment *) z := 3;\n",
            "s := 'it''s a test'#13#10;\n",
            "n := $FF + &17 + %1010 + 1.5e-3 + 10;\n",
            "if (a <= b) and (c <> d) then x := y;\n",
            "type TArr = array[0..9] of Integer;\n",
            "α := 1; // unicode ident\n",
            "",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("function Add(a, b: Integer): Integer;\n");
        assert!(t.contains(&(kind::IDENT, "function".to_string())));
        assert!(t.contains(&(kind::IDENT, "Add".to_string())));
        assert!(t.contains(&(kind::PUNCT, "(".to_string())));
        assert!(t.contains(&(kind::PUNCT, ":".to_string())));
        assert!(is_keyword("FUNCTION"));
        assert!(is_keyword("Begin"));
        assert!(!is_keyword("Add"));
    }

    #[test]
    fn strings_with_doubled_quote_escape() {
        let t = texts("s := 'it''s';\n");
        assert!(t.contains(&(kind::STRING, "'it''s'".to_string())));
    }

    #[test]
    fn char_codes() {
        let t = texts("#13#10#$41");
        assert!(t.contains(&(kind::CHAR_CODE, "#13".to_string())));
        assert!(t.contains(&(kind::CHAR_CODE, "#10".to_string())));
        assert!(t.contains(&(kind::CHAR_CODE, "#$41".to_string())));
    }

    #[test]
    fn numbers() {
        let t = texts("$FF &17 %1010 10 3.14 1.5e-3 1e10");
        assert!(t.contains(&(kind::INT, "$FF".to_string())));
        assert!(t.contains(&(kind::INT, "&17".to_string())));
        assert!(t.contains(&(kind::INT, "%1010".to_string())));
        assert!(t.contains(&(kind::INT, "10".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14".to_string())));
        assert!(t.contains(&(kind::FLOAT, "1.5e-3".to_string())));
        assert!(t.contains(&(kind::FLOAT, "1e10".to_string())));
    }

    #[test]
    fn range_is_not_a_float() {
        // `1..10` must be 1, .., 10 — not a malformed real.
        let t = texts("1..10");
        assert!(t.contains(&(kind::INT, "1".to_string())));
        assert!(t.contains(&(kind::PUNCT, "..".to_string())));
        assert!(t.contains(&(kind::INT, "10".to_string())));
    }

    #[test]
    fn operators() {
        let t = texts("a := b; c <= d; e >= f; g <> h; i .. j");
        for op in [":=", "<=", ">=", "<>", ".."] {
            assert!(
                t.contains(&(kind::PUNCT, op.to_string())),
                "missing operator {op}"
            );
        }
    }

    #[test]
    fn escaped_identifier() {
        let t = texts("&begin := 1;");
        assert!(t.contains(&(kind::IDENT, "&begin".to_string())));
        assert!(!is_keyword("&begin"));
    }

    #[test]
    fn unterminated_string_is_error_but_covered() {
        let src = "x := 'open\n";
        let t = texts(src);
        assert!(t.iter().any(|(k, _)| *k == kind::ERROR));
        assert!(covers_all(src));
    }

    #[test]
    fn unterminated_block_comment_runs_to_eof() {
        let src = "{ never closed";
        let t = texts(src);
        assert!(t.iter().any(|(k, _)| *k == kind::BLOCK_COMMENT));
        assert!(covers_all(src));
    }
}
