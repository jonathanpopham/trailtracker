//! Lossless Fortran lexer, covering both free-form (`.f90`/`.f95`/`.f03`) and
//! fixed-form (`.f`/`.for`) source.
//!
//! Guarantees (identical contract to the Rust/Julia/Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs, newlines, `!` line comments, and — in fixed form — a
//!   `C`/`c`/`*` in column 1 marking a whole comment line) are emitted as
//!   `trivia` tokens, never discarded.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped — an unterminated string runs to the
//!   end of its line and is emitted as a token spanning those bytes.
//!
//! Progress guard: the main run loop asserts forward motion on every iteration —
//! if a scanner ever failed to advance `pos`, one char is consumed as an `error`
//! token rather than spinning forever (a non-advancing loop is an OOM). Every
//! scanner advances on each character it inspects.
//!
//! Fortran is **case-insensitive**: keywords are recognised case-insensitively by
//! the parser (the lexer emits a single `ident` kind and lets the parser compare
//! lowercased text). Fixed-form is handled *leniently* (correctness over
//! completeness): column-1 comment lines are recognised, `!` inline comments are
//! recognised, and otherwise the line is tokenised exactly like free form. The
//! strict column-6 continuation / column-73 truncation rules are not enforced —
//! every byte still lands in the tree, so the result stays lossless regardless.
//!
//! Fortran surface the lexer covers:
//! - `!` line comments (both forms) and fixed-form column-1 `C`/`c`/`*` comments.
//! - Strings `'…'` and `"…"` with doubled-quote escapes (`''` / `""`).
//! - Numbers: integers with optional kind suffix (`1_8`, `1_ik`), reals with
//!   `.`, exponents `e`/`E`/`d`/`D` (`1.0d0`, `3.14e-2`), trailing-dot floats
//!   (`1.`), and `_` is *not* a digit separator in Fortran so it only begins a
//!   kind suffix.
//! - Dotted forms `.true.`, `.false.`, and `.op.` operators (`.and.`, `.eq.`, …).
//! - A pragmatic set of multi-char operators (`**`, `//`, `==`, `/=`, `<=`,
//!   `>=`, `=>`, `::`).
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_` as a pragmatic stand-in; non-ASCII operator
//! glyphs are not in the punctuation set and land in the tree as `error` tokens
//! — covered, never dropped, but a known classification gap.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Source form. Derived from the file extension by the parser.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Form {
    /// Free-form source (`.f90` / `.f95` / `.f03`).
    Free,
    /// Fixed-form source (`.f` / `.for`).
    Fixed,
}

/// Fortran statement keywords. Fortran has *no reserved words* — these double as
/// ordinary identifiers in many contexts — so this list is only a pragmatic aid
/// for the parser's contextual classification and for excluding obvious
/// non-callables from call detection. Compared case-insensitively.
pub const KEYWORDS: &[&str] = &[
    "program",
    "module",
    "submodule",
    "subroutine",
    "function",
    "end",
    "endprogram",
    "endmodule",
    "endsubroutine",
    "endfunction",
    "endtype",
    "endinterface",
    "enddo",
    "endif",
    "endselect",
    "endwhere",
    "endblock",
    "endassociate",
    "endforall",
    "contains",
    "use",
    "only",
    "import",
    "include",
    "interface",
    "abstract",
    "procedure",
    "type",
    "class",
    "implicit",
    "none",
    "parameter",
    "integer",
    "real",
    "double",
    "precision",
    "complex",
    "logical",
    "character",
    "dimension",
    "allocatable",
    "pointer",
    "target",
    "intent",
    "in",
    "out",
    "inout",
    "optional",
    "save",
    "external",
    "intrinsic",
    "public",
    "private",
    "protected",
    "sequence",
    "common",
    "data",
    "equivalence",
    "namelist",
    "call",
    "return",
    "stop",
    "continue",
    "go",
    "goto",
    "if",
    "then",
    "else",
    "elseif",
    "endwhile",
    "do",
    "while",
    "where",
    "elsewhere",
    "forall",
    "select",
    "case",
    "default",
    "associate",
    "block",
    "cycle",
    "exit",
    "where",
    "result",
    "bind",
    "extends",
    "deferred",
    "nopass",
    "pass",
    "pure",
    "impure",
    "elemental",
    "recursive",
    "print",
    "write",
    "read",
    "open",
    "close",
    "allocate",
    "deallocate",
    "nullify",
    "format",
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
    pub const COMMENT: &str = "comment";
    pub const IDENT: &str = "ident";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const STRING: &str = "string_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
const OPERATORS: &[&str] = &["**", "//", "==", "/=", "<=", ">=", "=>", "::"];

const SINGLE_PUNCT: &str = "+-*/%<>=:,()[]&;%.?";

/// Lex `source` under the given `form`.
pub fn lex(source: &str, form: Form) -> Vec<Token> {
    Lexer::new(source, form).run()
}

struct Lexer<'s> {
    src: &'s str,
    bytes: &'s [u8],
    pos: usize,
    form: Form,
    /// True when the cursor sits in column 1 (start of a physical line). Used to
    /// recognise fixed-form column-1 comment lines.
    at_line_start: bool,
    tokens: Vec<Token>,
}

impl<'s> Lexer<'s> {
    fn new(src: &'s str, form: Form) -> Self {
        Lexer {
            src,
            bytes: src.as_bytes(),
            pos: 0,
            form,
            at_line_start: true,
            tokens: Vec::new(),
        }
    }

    fn run(mut self) -> Vec<Token> {
        while self.pos < self.bytes.len() {
            let start = self.pos;
            let c = self.peek();

            // Fixed-form column-1 comment line: a `C`/`c`/`*` in the first column
            // makes the whole physical line a comment.
            if self.at_line_start && self.form == Form::Fixed && matches!(c, 'C' | 'c' | '*') {
                self.fixed_comment_line(start);
            } else {
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
                    '!' => self.line_comment(start),
                    '"' | '\'' => self.string_literal(start, c),
                    c if c.is_ascii_digit() => self.number(start),
                    '.' if self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) => {
                        self.number(start)
                    }
                    '.' if self.peek_at(1).map(|c| c.is_alphabetic()).unwrap_or(false) => {
                        self.dotted_word(start)
                    }
                    c if is_ident_start(c) => self.ident(start),
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

    /// A `!` line comment, to the end of the physical line (not including the
    /// newline).
    fn line_comment(&mut self, start: usize) {
        let end = self.find_line_end(self.pos);
        self.pos = end;
        self.push(kind::COMMENT, start, end, true);
    }

    /// A fixed-form column-1 comment line (`C`/`c`/`*` … to end of line).
    fn fixed_comment_line(&mut self, start: usize) {
        let end = self.find_line_end(self.pos);
        self.pos = end;
        self.push(kind::COMMENT, start, end, true);
    }

    fn ident(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        self.push(kind::IDENT, start, self.pos, false);
    }

    /// A `.word.` operator/logical literal (`.true.`, `.and.`, `.eq.`, …). The
    /// closing `.` is consumed when present; a bare `.word` (no closer) still
    /// rounds-trips as the bytes it covered.
    fn dotted_word(&mut self, start: usize) {
        self.bump(); // opening .
        self.eat_while(|c| c.is_alphabetic());
        if self.peek() == '.' {
            self.bump(); // closing .
        }
        self.push(kind::PUNCT, start, self.pos, false);
    }

    /// A `'…'` or `"…"` string. Fortran escapes the quote character by doubling
    /// it (`''` inside `'…'`). A raw newline (or EOF) ends an unterminated
    /// string, which is emitted as an `error` token over what was consumed.
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

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        // Integer part.
        self.eat_while(|c| c.is_ascii_digit());
        // Fractional part: a `.` followed by a digit, OR a trailing-dot float
        // `1.` that is not the start of a `.op.` form (`1.and.`) or `..`.
        if self.peek() == '.' {
            match self.peek_at(1) {
                Some(c) if c.is_ascii_digit() => {
                    is_float = true;
                    self.bump(); // .
                    self.eat_while(|c| c.is_ascii_digit());
                }
                Some(c) if !c.is_alphabetic() && c != '.' => {
                    // Trailing-dot float `1.` followed by punctuation / EOF.
                    is_float = true;
                    self.bump(); // .
                }
                None => {
                    is_float = true;
                    self.bump(); // .
                }
                _ => {} // `1.and.` etc. — leave the dot for the dotted-word scan.
            }
        }
        // Exponent: e/E/d/D with optional sign, only when a digit follows.
        if matches!(self.peek(), 'e' | 'E' | 'd' | 'D') {
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
        // Kind suffix: `_8` or `_ik` (no digit grouping in Fortran).
        if self.peek() == '_'
            && self
                .peek_at(1)
                .map(|c| c.is_alphanumeric() || c == '_')
                .unwrap_or(false)
        {
            self.bump(); // _
            self.eat_while(is_ident_continue);
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
        // A token right after a newline begins a new line at column 1; anything
        // else (including leading whitespace) leaves column 1.
        self.at_line_start = kind == kind::NEWLINE;
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
            "program p\n  integer :: x\nend program p\n",
            "! a comment\nx = 1.0d0 + 2_8\n",
            "s = 'it''s' // \"a\"\"b\"\n",
            "if (a .and. b) call foo(x, y)\n",
            "real, parameter :: pi = 3.14159e0\n",
            "z = .true.\n",
            "λ = 1  ! unicode ident lands as error but is covered\n",
            "",
        ] {
            assert!(covers_all(src, Form::Free), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn contiguous_coverage_is_lossless_fixed() {
        for src in [
            "C this is a fixed comment\n      x = 1\n",
            "*     another comment\n      call foo(x)\n",
            "      print *, 'hi'\n",
        ] {
            assert!(covers_all(src, Form::Fixed), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn fixed_column_one_comment() {
        let t = texts("C comment\n      x = 1\n", Form::Fixed);
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::COMMENT && s == "C comment"));
        // The same `C` mid-line is an identifier, not a comment, in fixed form.
        let t2 = texts("      C = 1\n", Form::Fixed);
        assert!(t2.iter().any(|(k, s)| *k == kind::IDENT && s == "C"));
    }

    #[test]
    fn doubled_quote_escape() {
        let t = texts("s = 'it''s'\n", Form::Free);
        assert!(t.contains(&(kind::STRING, "'it''s'".to_string())));
    }

    #[test]
    fn numbers_with_kinds_and_d_exponent() {
        let t = texts("a = 1.0d0\nb = 2_8\nc = 3.14e-2\nd = 1.\n", Form::Free);
        assert!(t.contains(&(kind::FLOAT, "1.0d0".to_string())));
        assert!(t.contains(&(kind::INT, "2_8".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14e-2".to_string())));
        assert!(t.contains(&(kind::FLOAT, "1.".to_string())));
    }

    #[test]
    fn dotted_operators() {
        let t = texts("x = a .and. .true.\n", Form::Free);
        assert!(t.contains(&(kind::PUNCT, ".and.".to_string())));
        assert!(t.contains(&(kind::PUNCT, ".true.".to_string())));
    }

    #[test]
    fn operators_and_keywords() {
        let t = texts("integer :: x => y ** 2 // z\n", Form::Free);
        for op in ["::", "=>", "**", "//"] {
            assert!(
                t.contains(&(kind::PUNCT, op.to_string())),
                "missing operator {op}"
            );
        }
        assert!(is_keyword("INTEGER"));
        assert!(is_keyword("Function"));
        assert!(!is_keyword("myvar"));
    }

    #[test]
    fn unterminated_string_is_error_but_covered() {
        let src = "x = 'open\n";
        let t = texts(src, Form::Free);
        assert!(t.iter().any(|(k, _)| *k == kind::ERROR));
        assert!(covers_all(src, Form::Free));
    }
}
