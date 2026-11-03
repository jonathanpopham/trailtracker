//! Lossless COBOL lexer, covering both fixed-form and free-form source.
//!
//! Guarantees (identical contract to the Fortran/Rust/Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs, newlines, `*>` inline comments, and — in fixed form — a
//!   `*`/`/` in the column-7 indicator area marking a whole comment line) are
//!   emitted as `trivia` tokens, never discarded.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped — an unterminated string runs to the
//!   end of its line and is emitted as a token spanning those bytes.
//!
//! Progress guard: the main run loop asserts forward motion on every iteration —
//! if a scanner ever failed to advance `pos`, one char is consumed as an `error`
//! token rather than spinning forever (a non-advancing loop is an OOM). Every
//! scanner advances on each character it inspects.
//!
//! COBOL is **case-insensitive**: keywords are recognised case-insensitively by
//! the parser (the lexer emits a single `ident` kind and lets the parser compare
//! lowercased text).
//!
//! COBOL column model (fixed form), handled *leniently* — correctness over
//! completeness:
//!   - cols 1-6: sequence area (blank or digits);
//!   - col 7: indicator — `*`/`/` marks a comment line, `-` a continuation,
//!     `D`/`d` a debug line;
//!   - cols 8-72: code (Area A / Area B);
//!   - cols 73+: identification area, ignored by the compiler.
//!
//! The lexer recognises a column-7 `*`/`/` comment line **only when columns 1-6
//! are a legitimate sequence area** (all blank/tab/digit), which avoids
//! misreading a free-form multiplication that happens to land on byte column 7.
//! The strict continuation (col-7 `-`) and column-73 truncation rules are not
//! enforced — every byte still lands in the tree, so the round-trip holds
//! regardless. Free-form `*>` inline comments are recognised everywhere, in both
//! forms.
//!
//! COBOL surface the lexer covers:
//! - `*>` inline comments and fixed-form column-7 `*`/`/` comment lines.
//! - Strings `"…"` and `'…'` with doubled-quote escapes (`""` / `''`).
//! - Numeric literals: integers, decimals (`3.14` — only when a digit follows the
//!   `.`, so a sentence-terminating period is never absorbed), and `E` exponents.
//! - COBOL words that may start with a digit and contain hyphens (`100-MAIN`,
//!   `WS-COUNT-1`) lex as a single `ident`; a pure-digit run is a numeric literal
//!   (so a level number `01`/`88` stays an `int_literal`).
//! - A pragmatic set of multi-char operators (`**`, `>=`, `<=`, `<>`, `==`).
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_`/`-` as a pragmatic stand-in; PIC picture-strings
//! are not modelled specially — they tokenise into ordinary words/numbers/groups,
//! which is lossless but means the parser does not understand picture syntax.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Source form. Derived from the file extension by the parser.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Form {
    /// Free-form source: no column rules; `*>` inline comments only.
    Free,
    /// Fixed-form source: column-7 `*`/`/` comment lines (when cols 1-6 are a
    /// sequence area) plus `*>` inline comments.
    Fixed,
}

/// COBOL reserved/verb words. COBOL *does* reserve a large word list; this is a
/// pragmatic subset used by the parser for contextual classification (excluding
/// statement verbs from being mistaken for paragraph names) and by the lowering
/// to avoid treating verbs as call operands. Compared case-insensitively.
pub const KEYWORDS: &[&str] = &[
    "identification",
    "id",
    "environment",
    "data",
    "procedure",
    "division",
    "section",
    "program-id",
    "author",
    "installation",
    "date-written",
    "date-compiled",
    "security",
    "configuration",
    "source-computer",
    "object-computer",
    "special-names",
    "input-output",
    "file-control",
    "i-o-control",
    "file",
    "working-storage",
    "local-storage",
    "linkage",
    "screen",
    "report",
    "fd",
    "sd",
    "rd",
    "select",
    "assign",
    "copy",
    "replacing",
    "by",
    "of",
    "in",
    "pic",
    "picture",
    "value",
    "values",
    "occurs",
    "redefines",
    "renames",
    "usage",
    "comp",
    "comp-1",
    "comp-2",
    "comp-3",
    "computational",
    "binary",
    "packed-decimal",
    "display",
    "filler",
    "blank",
    "justified",
    "sign",
    "synchronized",
    "sync",
    "level",
    "accept",
    "add",
    "call",
    "cancel",
    "close",
    "compute",
    "continue",
    "delete",
    "divide",
    "else",
    "end",
    "end-if",
    "end-perform",
    "end-evaluate",
    "end-read",
    "end-call",
    "evaluate",
    "exit",
    "go",
    "goto",
    "goback",
    "if",
    "initialize",
    "inspect",
    "move",
    "multiply",
    "open",
    "perform",
    "read",
    "release",
    "return",
    "rewrite",
    "search",
    "set",
    "sort",
    "start",
    "stop",
    "string",
    "subtract",
    "then",
    "to",
    "unstring",
    "until",
    "using",
    "varying",
    "when",
    "with",
    "write",
    "thru",
    "through",
    "from",
    "into",
    "giving",
    "run",
    "true",
    "false",
    "zero",
    "zeros",
    "zeroes",
    "space",
    "spaces",
    "not",
    "and",
    "or",
    "test",
    "times",
];

/// Case-insensitive keyword test.
pub fn is_keyword(text: &str) -> bool {
    let lower = text.to_ascii_lowercase();
    KEYWORDS.contains(&lower.as_str())
}

/// Token kind labels. Stored on the CST as `&'static str`.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const NEWLINE: &str = "newline";
    /// Fixed-form sequence area (cols 1-6) — retained as trivia so it never
    /// pollutes statement classification, but kept byte-for-byte.
    pub const SEQUENCE: &str = "sequence";
    pub const COMMENT: &str = "comment";
    pub const IDENT: &str = "ident";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const STRING: &str = "string_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest-first so the scanner is greedy-correct.
/// (`*>` is handled separately as an inline comment.)
const OPERATORS: &[&str] = &["**", ">=", "<=", "<>", "=="];

const SINGLE_PUNCT: &str = ".,;:()+-*/<>=&";

/// Lex `source` under the given `form`.
pub fn lex(source: &str, form: Form) -> Vec<Token> {
    Lexer::new(source, form).run()
}

struct Lexer<'s> {
    src: &'s str,
    bytes: &'s [u8],
    pos: usize,
    form: Form,
    /// Byte offset of the start of the current physical line. Used to compute the
    /// indicator column for fixed-form comment-line detection.
    line_start: usize,
    tokens: Vec<Token>,
}

impl<'s> Lexer<'s> {
    fn new(src: &'s str, form: Form) -> Self {
        Lexer {
            src,
            bytes: src.as_bytes(),
            pos: 0,
            form,
            line_start: 0,
            tokens: Vec::new(),
        }
    }

    fn run(mut self) -> Vec<Token> {
        while self.pos < self.bytes.len() {
            let start = self.pos;

            // Fixed-form sequence area (cols 1-6): when the file is fixed form and
            // the cursor sits at a physical line start, a leading all-blank/digit
            // run of up to six columns is the sequence area — emitted as trivia so
            // a sequence number like `000100` never becomes a statement token. A
            // run containing letters (free-form code starting in Area A) is left
            // for the normal scanners, so free-form source is handled correctly.
            if self.form == Form::Fixed && self.pos == self.line_start {
                let seq_end = self.fixed_sequence_end();
                if seq_end > start {
                    self.push(kind::SEQUENCE, start, seq_end, true);
                    self.pos = seq_end;
                    continue;
                }
            }

            let c = self.peek();
            let col = self.pos - self.line_start; // 0-based byte column

            // Fixed-form column-7 indicator (`*`/`/`) comment line, but only when
            // columns 1-6 are a legitimate sequence area.
            if self.form == Form::Fixed
                && col == 6
                && matches!(c, '*' | '/')
                && self.seq_area_blank()
            {
                self.comment_to_eol(start);
            } else {
                match c {
                    '\n' => {
                        self.bump();
                        self.push(kind::NEWLINE, start, self.pos, true);
                        self.line_start = self.pos;
                    }
                    '\r' => {
                        self.bump();
                        if self.peek() == '\n' {
                            self.bump();
                        }
                        self.push(kind::NEWLINE, start, self.pos, true);
                        self.line_start = self.pos;
                    }
                    ' ' | '\t' | '\x0b' | '\x0c' => {
                        self.eat_while(|c| matches!(c, ' ' | '\t' | '\x0b' | '\x0c'));
                        self.push(kind::WHITESPACE, start, self.pos, true);
                    }
                    '*' if self.peek_at(1) == Some('>') => self.comment_to_eol(start),
                    '"' | '\'' => self.string_literal(start, c),
                    c if c.is_ascii_digit() => self.word_or_number(start),
                    c if is_ident_start(c) => self.word_or_number(start),
                    c if SINGLE_PUNCT.contains(c) => self.punct(start),
                    _ => {
                        self.bump();
                        self.push(kind::ERROR, start, self.pos, false);
                    }
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

    /// True if columns 1-6 of the current physical line are all blank/tab/digit
    /// (a legitimate fixed-form sequence area). Only called when `pos - line_start
    /// == 6`, so the six bytes are guaranteed present.
    fn seq_area_blank(&self) -> bool {
        let s = self.line_start;
        self.bytes[s..s + 6]
            .iter()
            .all(|&b| b == b' ' || b == b'\t' || b.is_ascii_digit())
    }

    /// End offset of the fixed-form sequence area at the current line start: the
    /// first six columns (clamped to the line) when they are all blank/tab/digit,
    /// else `line_start` (no sequence area — leave the bytes to normal scanners).
    fn fixed_sequence_end(&self) -> usize {
        let line_end = self.find_line_end(self.line_start);
        let cap = (self.line_start + 6).min(line_end);
        if cap <= self.line_start {
            return self.line_start;
        }
        let all_seq = self.bytes[self.line_start..cap]
            .iter()
            .all(|&b| b == b' ' || b == b'\t' || b.is_ascii_digit());
        if all_seq {
            cap
        } else {
            self.line_start
        }
    }

    /// A comment from `start` to the end of the physical line (newline excluded).
    /// Covers both `*>` inline comments and fixed-form column-7 comment lines.
    fn comment_to_eol(&mut self, start: usize) {
        let end = self.find_line_end(self.pos);
        self.pos = end;
        self.push(kind::COMMENT, start, end, true);
    }

    /// A COBOL word (`ident`) or a numeric literal. A word run is alphanumerics
    /// (plus `_`) joined by an internal `-`; a pure-digit run is a number, which
    /// may extend with a `.`-fraction (only if a digit follows) and an `E`
    /// exponent.
    fn word_or_number(&mut self, start: usize) {
        loop {
            let c = self.peek();
            if is_word_char(c) || (c == '-' && self.peek_at(1).map(is_word_char).unwrap_or(false)) {
                self.bump();
            } else {
                break;
            }
        }
        let run = &self.src[start..self.pos];
        let pure_digits = !run.is_empty() && run.bytes().all(|b| b.is_ascii_digit());
        if !pure_digits {
            self.push(kind::IDENT, start, self.pos, false);
            return;
        }
        let mut is_float = false;
        // Fractional part: `.` only when a digit follows, so a sentence-ending
        // period is never absorbed into the literal.
        if self.peek() == '.' && self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) {
            is_float = true;
            self.bump(); // .
            self.eat_while(|c| c.is_ascii_digit());
        }
        // Exponent: `e`/`E` with optional sign, only when a digit follows.
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
                self.bump(); // exponent letter
                if sign_len == 1 {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit());
            }
        }
        let k = if is_float { kind::FLOAT } else { kind::INT };
        self.push(k, start, self.pos, false);
    }

    /// A `'…'` or `"…"` string. COBOL escapes the quote character by doubling it.
    /// A raw newline (or EOF) ends an unterminated string, emitted as an `error`
    /// token over what was consumed.
    fn string_literal(&mut self, start: usize, quote: char) {
        self.bump(); // opening quote
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == quote {
                self.bump();
                if self.peek() == quote {
                    // Doubled quote: an escaped quote, not a terminator.
                    self.bump();
                    continue;
                }
                terminated = true;
                break;
            }
            if c == '\n' || c == '\r' {
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

fn is_word_char(c: char) -> bool {
    c == '_' || c.is_alphanumeric()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn texts(src: &str, form: Form) -> Vec<(&'static str, String)> {
        lex(src, form)
            .into_iter()
            .map(|t| (t.kind, t.span.text(src).to_string()))
            .collect()
    }

    fn covers_all(src: &str, form: Form) -> bool {
        let toks = lex(src, form);
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
    fn contiguous_coverage_is_lossless_free() {
        for src in [
            "       PROGRAM-ID. HELLO.\n",
            "      *> an inline comment\n       DISPLAY \"HI\".\n",
            "       MOVE 3.14 TO WS-AMT.\n",
            "       01 WS-COUNT PIC 9(4) VALUE 0.\n",
            "       PERFORM 100-MAIN THRU 100-EXIT.\n",
            "       CALL \"SUBPROG\" USING WS-REC.\n",
            "       IF A = B AND C <= D THEN CONTINUE END-IF.\n",
            "λ = 1 *> unicode ident lands as error but is covered\n",
            "",
        ] {
            assert!(covers_all(src, Form::Free), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn contiguous_coverage_is_lossless_fixed() {
        for src in [
            "000100* a fixed comment line\n       MOVE 1 TO X.\n",
            "      * blank sequence area comment\n",
            "      /  form-feed comment\n",
            "       MOVE A TO B.\n",
        ] {
            assert!(covers_all(src, Form::Fixed), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn fixed_column_seven_comment() {
        // `*` at column 7 with a blank sequence area is a comment line.
        let t = texts("      * a comment\n", Form::Fixed);
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::COMMENT && s == "* a comment"));
        // A `*` that is NOT at column 7 over a non-sequence area is multiplication.
        let t2 = texts("MOVE A*B\n", Form::Fixed);
        assert!(t2.iter().any(|(k, s)| *k == kind::PUNCT && s == "*"));
    }

    #[test]
    fn inline_comment_star_gt() {
        let t = texts("       DISPLAY X. *> trailing\n", Form::Free);
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::COMMENT && s == "*> trailing"));
    }

    #[test]
    fn hyphenated_and_numeric_words() {
        let t = texts("WS-COUNT-1 100-MAIN 01 88\n", Form::Free);
        assert!(t.contains(&(kind::IDENT, "WS-COUNT-1".to_string())));
        assert!(t.contains(&(kind::IDENT, "100-MAIN".to_string())));
        assert!(t.contains(&(kind::INT, "01".to_string())));
        assert!(t.contains(&(kind::INT, "88".to_string())));
    }

    #[test]
    fn period_not_absorbed_as_decimal() {
        // `5.` at end of a statement is a terminator period, not a float.
        let t = texts("MOVE 5 TO X.\n", Form::Free);
        assert!(t.contains(&(kind::INT, "5".to_string())));
        assert!(t.contains(&(kind::PUNCT, ".".to_string())));
        // But `3.14` is a real decimal literal.
        let t2 = texts("MOVE 3.14 TO Y.\n", Form::Free);
        assert!(t2.contains(&(kind::FLOAT, "3.14".to_string())));
    }

    #[test]
    fn doubled_quote_escape() {
        let t = texts("MOVE 'it''s' TO X.\n", Form::Free);
        assert!(t.contains(&(kind::STRING, "'it''s'".to_string())));
        let t2 = texts("MOVE \"a\"\"b\" TO X.\n", Form::Free);
        assert!(t2.contains(&(kind::STRING, "\"a\"\"b\"".to_string())));
    }

    #[test]
    fn operators_and_keywords() {
        let t = texts("IF A >= B AND C <> D THEN X = Y ** 2\n", Form::Free);
        for op in [">=", "<>", "**"] {
            assert!(
                t.contains(&(kind::PUNCT, op.to_string())),
                "missing operator {op}"
            );
        }
        assert!(is_keyword("PERFORM"));
        assert!(is_keyword("Move"));
        assert!(!is_keyword("WS-COUNTER"));
    }

    #[test]
    fn unterminated_string_is_error_but_covered() {
        let src = "MOVE 'open\n";
        let t = texts(src, Form::Free);
        assert!(t.iter().any(|(k, _)| *k == kind::ERROR));
        assert!(covers_all(src, Form::Free));
    }
}
