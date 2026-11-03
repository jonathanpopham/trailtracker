//! Lossless Ada lexer, grounded in the Ada Reference Manual's lexical grammar.
//!
//! Guarantees (identical contract to the Rust, Julia, and Fortran lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (whitespace incl. newlines, `--` line comments) are emitted as
//!   `trivia` tokens, never discarded — Ada is *not* whitespace-significant, so a
//!   newline is ordinary `whitespace` trivia (line comments simply end at it).
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped — an unterminated string or based
//!   literal is emitted as an `error` token spanning what was consumed.
//!
//! Progress guard: the main run loop asserts forward motion on every iteration —
//! if a scanner ever failed to advance `pos`, one char is consumed as an `error`
//! token rather than spinning forever (a non-advancing loop is an OOM).
//!
//! Ada-specific surface the lexer covers:
//! - `--` line comments.
//! - Strings `"…"` with the **doubled-quote** escape (`""` is one embedded `"`);
//!   a raw newline ends an unterminated single-line string (Ada strings cannot
//!   span lines).
//! - Numbers: decimal `123_456`, decimal reals `3.14`, exponents `1E10` /
//!   `1.0e-5`, and **based** literals `16#FF#`, `2#1010#`, `16#F.FF#E+2`.
//! - The character-literal `'x'` vs the attribute tick `X'Range` ambiguity is
//!   resolved with a running "previous token was a value" flag (the mirror of the
//!   Rust lexer's char-vs-lifetime and the Julia lexer's char-vs-transpose
//!   splits): a `'` immediately after an identifier or a closing `)`/`]` is an
//!   attribute tick (lexed as a `punct`), never a char-literal open. When the
//!   `'` is *not* in value position it opens a char literal only when it forms
//!   the exact `'<char>'` shape; otherwise it stays a lone `punct` tick (still
//!   lossless), so code is never swallowed as a string.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_` as a pragmatic stand-in for Ada's full Unicode
//! letter rule. Non-ASCII *operator* symbols are not in the punctuation set and
//! land in the tree as `error` tokens — covered, never dropped, but a known
//! classification gap.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Ada 2012 reserved words, stored lowercase. Ada is case-insensitive, so
/// [`is_keyword`] compares with `eq_ignore_ascii_case`. They lex as `ident`
/// tokens; the parser distinguishes them via case-insensitive text checks.
pub const KEYWORDS: &[&str] = &[
    "abort",
    "abs",
    "abstract",
    "accept",
    "access",
    "aliased",
    "all",
    "and",
    "array",
    "at",
    "begin",
    "body",
    "case",
    "constant",
    "declare",
    "delay",
    "delta",
    "digits",
    "do",
    "else",
    "elsif",
    "end",
    "entry",
    "exception",
    "exit",
    "for",
    "function",
    "generic",
    "goto",
    "if",
    "in",
    "interface",
    "is",
    "limited",
    "loop",
    "mod",
    "new",
    "not",
    "null",
    "of",
    "or",
    "others",
    "out",
    "overriding",
    "package",
    "pragma",
    "private",
    "procedure",
    "protected",
    "raise",
    "range",
    "record",
    "rem",
    "renames",
    "requeue",
    "return",
    "reverse",
    "select",
    "separate",
    "some",
    "subtype",
    "synchronized",
    "tagged",
    "task",
    "terminate",
    "then",
    "type",
    "until",
    "use",
    "when",
    "while",
    "with",
    "xor",
];

/// Case-insensitive reserved-word test (Ada identifiers are case-insensitive).
pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.iter().any(|k| text.eq_ignore_ascii_case(k))
}

/// Token kind labels. Stored on the CST as `&'static str`.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const LINE_COMMENT: &str = "line_comment";
    pub const IDENT: &str = "ident";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const STRING: &str = "string_literal";
    pub const CHAR: &str = "char_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character delimiters, longest first so the scanner is greedy-correct.
/// Ada compound delimiters: `:=`, `=>`, `..`, `**`, `/=`, `>=`, `<=`, `<>`, and
/// the label brackets `<<` / `>>`.
const OPERATORS: &[&str] = &[":=", "=>", "..", "**", "/=", ">=", "<=", "<>", "<<", ">>"];

/// Single-character delimiters. `'` is handled before this set is consulted (the
/// char-vs-tick split); it is listed here only for defensive completeness.
const SINGLE_PUNCT: &str = "&'()*+,-./:;<=>|@[]#";

pub fn lex(source: &str) -> Vec<Token> {
    Lexer::new(source).run()
}

struct Lexer<'s> {
    src: &'s str,
    bytes: &'s [u8],
    pos: usize,
    tokens: Vec<Token>,
    /// True when the previously emitted significant token closes a value, so a
    /// following `'` is the attribute tick rather than a char-literal open.
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
                c if c.is_whitespace() => {
                    self.eat_while(|c| c.is_whitespace());
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                '-' if self.peek_at(1) == Some('-') => self.line_comment(start),
                '"' => self.string_literal(start),
                '\'' => self.char_or_tick(start),
                c if c.is_ascii_digit() => self.number(start),
                c if is_ident_start(c) => self.ident(start),
                c if SINGLE_PUNCT.contains(c) => self.punct(start),
                _ => {
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                    self.set_prev_value(false);
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
        // Trivia never changes the value-context flag.
    }

    /// A `"…"` string with the `""` doubled-quote escape. A raw newline ends an
    /// unterminated single-line string (Ada strings cannot span lines).
    fn string_literal(&mut self, start: usize) {
        self.bump(); // opening "
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '"' {
                if self.peek_at(1) == Some('"') {
                    // Doubled quote = one embedded ", stays inside the string.
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
        let k = if terminated {
            kind::STRING
        } else {
            kind::ERROR
        };
        self.push(k, start, self.pos, false);
        self.set_prev_value(true);
    }

    /// Disambiguate a `'`: an attribute tick (value position) vs a char literal.
    fn char_or_tick(&mut self, start: usize) {
        if self.prev_value {
            // `X'Range`, `Arr'Length`, `Foo(I)'Image` — an attribute tick.
            self.bump();
            self.push(kind::PUNCT, start, self.pos, false);
            // The attribute designator that follows is an identifier, which will
            // re-set the value flag; a tick itself is not a value.
            self.set_prev_value(false);
            return;
        }
        // Not in value position: only the exact `'<char>'` shape is a char
        // literal. Ada char literals carry a single graphic char and have no
        // backslash escapes, so `'<x>'` ⟺ the 3rd char is the closing quote.
        if self.peek_at(1).is_some() && self.peek_at(2) == Some('\'') {
            self.bump(); // '
            self.bump(); // the character (one char, may be multi-byte)
            self.bump(); // closing '
            self.push(kind::CHAR, start, self.pos, false);
            self.set_prev_value(true);
            return;
        }
        // Unsure: keep the `'` as a lone punct tick — still lossless, and we
        // never swallow following code as a string.
        self.bump();
        self.push(kind::PUNCT, start, self.pos, false);
        self.set_prev_value(false);
    }

    fn ident(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        self.push(kind::IDENT, start, self.pos, false);
        // After any identifier (including reserved words such as `all` in
        // `Ptr.all'Size`), a `'` is an attribute tick — treat idents as values.
        self.set_prev_value(true);
    }

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        if self.peek() == '#' {
            // Based literal: base#based_numeral#[exponent].
            self.bump(); // opening #
            let mut saw_dot = false;
            while self.pos < self.bytes.len() {
                let c = self.peek();
                if c == '#' {
                    break;
                } else if c == '.' {
                    saw_dot = true;
                    self.bump();
                } else if c.is_ascii_alphanumeric() || c == '_' {
                    self.bump();
                } else {
                    break;
                }
            }
            if self.peek() == '#' {
                self.bump(); // closing #
            } else {
                // Unterminated based literal — still covered, reported as error.
                self.push(kind::ERROR, start, self.pos, false);
                self.set_prev_value(true);
                return;
            }
            if saw_dot {
                is_float = true;
            }
            self.eat_exponent();
            let k = if is_float { kind::FLOAT } else { kind::INT };
            self.push(k, start, self.pos, false);
            self.set_prev_value(true);
            return;
        }
        // Decimal real: a `.` followed by a digit (keeps `1..2` ranges and
        // `Rec.Field` access as separate tokens).
        if self.peek() == '.' && self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) {
            is_float = true;
            self.bump(); // .
            self.eat_while(|c| c.is_ascii_digit() || c == '_');
        }
        self.eat_exponent();
        let k = if is_float { kind::FLOAT } else { kind::INT };
        self.push(k, start, self.pos, false);
        self.set_prev_value(true);
    }

    /// Consume an `E[+/-]digits` exponent if present. Does not flip the int/float
    /// classification: `1E6` is an Ada integer literal, only a `.` makes a real.
    fn eat_exponent(&mut self) {
        if matches!(self.peek(), 'e' | 'E') {
            let signed = matches!(self.peek_at(1), Some('+') | Some('-'));
            let digit_at = if signed { 2 } else { 1 };
            if self
                .peek_at(digit_at)
                .map(|c| c.is_ascii_digit())
                .unwrap_or(false)
            {
                self.bump(); // e
                if signed {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit() || c == '_');
            }
        }
    }

    fn punct(&mut self, start: usize) {
        for op in OPERATORS {
            if self.src[self.pos..].starts_with(op) {
                self.pos += op.len();
                self.push(kind::PUNCT, start, self.pos, false);
                // A box `<>` closes a value; assignment/relational operators do
                // not (so a following `'` after `:=` opens a char literal).
                self.set_prev_value(*op == "<>");
                return;
            }
        }
        let c = self.peek();
        self.bump();
        self.push(kind::PUNCT, start, self.pos, false);
        // Closers `)` / `]` close a value so a following `'` is an attribute tick.
        self.set_prev_value(matches!(c, ')' | ']'));
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

    fn set_prev_value(&mut self, v: bool) {
        self.prev_value = v;
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
            "procedure P is\nbegin\n   null;\nend P;\n",
            "-- a comment\nX : Integer := 16#FF#;\n",
            "S : String := \"he said \"\"hi\"\"\";\n",
            "C : Character := 'a';  N := Arr'Length;\n",
            "R : Float := 1.5e-3 + 2#1010# + 16#1.8#E4;\n",
            "for I in 1 .. 10 loop A (I) := B'Range; end loop;\n",
            "λ : Integer := 1;  -- unicode ident\n",
            "",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("function Add (A : Integer) return Integer is");
        assert!(t.contains(&(kind::IDENT, "function".to_string())));
        assert!(t.contains(&(kind::IDENT, "Add".to_string())));
        assert!(t.contains(&(kind::PUNCT, "(".to_string())));
        assert!(is_keyword("FUNCTION"));
        assert!(is_keyword("return"));
        assert!(!is_keyword("Add"));
    }

    #[test]
    fn char_literal_vs_attribute_tick() {
        // `'a'` standalone is a char literal; `X'Range` is an attribute tick.
        let t = texts("C := 'a'; R := X'Range;");
        assert!(t.contains(&(kind::CHAR, "'a'".to_string())));
        // The attribute tick lexes as a single punct, not a char-literal open.
        assert!(t.contains(&(kind::PUNCT, "'".to_string())));
        assert!(t.contains(&(kind::IDENT, "Range".to_string())));
    }

    #[test]
    fn tick_after_paren_is_attribute() {
        // `Foo (I)'Image` — the `'` follows a closing paren, so it is a tick.
        let t = texts("S := Foo (I)'Image;");
        assert!(t.contains(&(kind::PUNCT, "'".to_string())));
        assert!(!t.iter().any(|(k, _)| *k == kind::CHAR));
    }

    #[test]
    fn doubled_quote_escape_stays_in_string() {
        let t = texts("\"a\"\"b\"");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "\"a\"\"b\""));
    }

    #[test]
    fn based_and_decimal_numbers() {
        let t = texts("16#FF# 2#1010# 16#1.8#E4 1_000 3.14 1E6");
        assert!(t.contains(&(kind::INT, "16#FF#".to_string())));
        assert!(t.contains(&(kind::INT, "2#1010#".to_string())));
        assert!(t.contains(&(kind::FLOAT, "16#1.8#E4".to_string())));
        assert!(t.contains(&(kind::INT, "1_000".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14".to_string())));
        assert!(t.contains(&(kind::INT, "1E6".to_string())));
    }

    #[test]
    fn range_does_not_eat_dots() {
        let t = texts("1..2");
        assert_eq!(
            t,
            vec![
                (kind::INT, "1".to_string()),
                (kind::PUNCT, "..".to_string()),
                (kind::INT, "2".to_string()),
            ]
        );
    }

    #[test]
    fn unterminated_string_is_error_but_covered() {
        let src = "X := \"open\n";
        let t = texts(src);
        assert!(t.iter().any(|(k, _)| *k == kind::ERROR));
        assert!(covers_all(src));
    }
}
