//! Lossless, **deliberately coarse, dialect-agnostic** assembly lexer.
//!
//! Assembly is not one language: x86 (Intel *and* AT&T), ARM (A32/T32/A64),
//! RISC-V, MIPS, … each rendered by a different assembler (GAS, NASM, MASM, armasm)
//! with mutually incompatible lexical conventions. There is no single correct
//! tokenization. This lexer therefore makes **one** coarse, lossless pass that is
//! "good enough" for symbol/label/directive/call extraction across dialects, and
//! is honest about everything it punts. The only hard guarantee is the one the
//! whole substrate relies on:
//!
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs, newlines, every accepted comment form) are emitted as
//!   `trivia` tokens, never dropped. A newline is its own trivia kind so the
//!   line-oriented parser can find statement boundaries; it is otherwise not
//!   structurally significant.
//! - Anything unclassifiable becomes an `error` token over its exact bytes.
//! - The main loop advances `pos` on every iteration; a final progress guard
//!   force-consumes one char as an `error` token if no scanner moved the cursor,
//!   so malformed input can never spin into an infinite loop / OOM.
//!
//! ## Comment forms (coarse, per spec)
//! Accepted as comments: `;` (Intel/NASM/MASM), `//` and `/* */` (GAS/C), and a
//! line-leading `#` *unless* it is immediately followed by a word — in which case
//! the `#` is emitted as a punctuation **directive marker** (`#include`,
//! `#define`) and the rest of the line lexes normally. Every other `#` (mid-line,
//! or line-leading followed by non-word) is a line comment to end of line.
//!
//! ## Heavy punts (documented dishonesty avoidance — these are *known* coarse)
//! - **ARM `@` / `!` line comments are NOT treated as comments.** The spec's
//!   accept-list is `;`, `#`, `//`, `/* */` only; `@`/`!` lex as ordinary
//!   punctuation/identifier bytes. (`@` is folded into identifier characters so
//!   `printf@PLT` and MASM `@@` stay single tokens.)
//! - **ARM immediate `#1` is read as a comment**, not an immediate, because the
//!   coarse rule "mid-line `#` → comment" wins. This is the documented casualty of
//!   a genuinely unresolvable cross-dialect conflict (`#` = comment in some GAS
//!   vs `#` = immediate prefix in ARM). Losslessness is preserved either way.
//! - **GAS `;` as a statement separator is NOT supported** — `;` is always a
//!   comment (NASM/Intel reading).
//! - Identifier characters are a coarse superset (`_ . $ ? @ %`) so that
//!   directive names (`.section`, `%macro`), AT&T registers (`%eax`), NASM/MASM
//!   locals (`.L1`, `@@`), and relocation suffixes (`sym@PLT`) survive as single
//!   tokens. This means a few non-symbol uses of those bytes (e.g. `%` as modulo)
//!   fold into "identifier" tokens — coarse, but always lossless.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Token kind labels. Stored on the CST as `&'static str` so the tree stays
/// uniform and JSON-friendly.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const NEWLINE: &str = "newline";
    pub const LINE_COMMENT: &str = "line_comment";
    pub const BLOCK_COMMENT: &str = "block_comment";
    pub const IDENT: &str = "ident";
    pub const NUMBER: &str = "number";
    pub const STRING: &str = "string_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
/// Coarse: assembly expression operators vary by assembler; this covers the
/// common shared set. Anything not listed falls back to single-char punctuation.
const OPERATORS: &[&str] = &["<<", ">>", "==", "!=", "<=", ">=", "&&", "||", "::", "->"];

/// Single-char punctuation. `.`, `$`, `?`, `@`, `%` are intentionally absent: they
/// are folded into identifiers (see module docs). `#` is handled by a dedicated
/// arm (directive marker vs comment), `;` by the comment arm.
const SINGLE_PUNCT: &str = "+-*/&|^<>=!~,:()[]{}\\`";

pub fn lex(source: &str) -> Vec<Token> {
    Lexer::new(source).run()
}

struct Lexer<'s> {
    src: &'s str,
    bytes: &'s [u8],
    pos: usize,
    tokens: Vec<Token>,
    /// True while only trivia has been seen since the last newline (or start of
    /// input): the basis for the line-leading `#` directive-vs-comment decision.
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
                ';' => self.line_comment(start),
                '/' if self.peek_at(1) == Some('/') => self.line_comment(start),
                '/' if self.peek_at(1) == Some('*') => self.block_comment(start),
                // Line-leading `#word` → directive marker; any other `#` → comment.
                '#' if self.line_start && starts_ident(self.peek_at(1)) => {
                    self.bump(); // #
                    self.push(kind::PUNCT, start, self.pos, false);
                }
                '#' => self.line_comment(start),
                '"' | '\'' => self.string_literal(start, c),
                c if c.is_ascii_digit() => self.number(start),
                c if is_ident_start(c) => self.ident(start),
                c if SINGLE_PUNCT.contains(c) => self.punct(start),
                _ => {
                    // Unknown byte/char — preserve it as an explicit error token.
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }

            // Progress guard: a non-advancing iteration would be an infinite loop
            // (and an OOM, since `tokens` would never grow past it). Under the
            // current arms this is unreachable, but it is the real defense against
            // a future edit that forgets to advance the cursor.
            if self.pos == start {
                self.bump();
                if self.pos == start {
                    break; // cannot even bump (empty remainder) — stop spinning.
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

    /// A `/* … */` block comment (C/GAS style — does **not** nest). An
    /// unterminated comment still covers to EOF and stays trivia — lossless.
    fn block_comment(&mut self, start: usize) {
        self.pos += 2; // /*
        while self.pos < self.bytes.len() {
            if self.src[self.pos..].starts_with("*/") {
                self.pos += 2;
                break;
            }
            self.bump();
        }
        self.push(kind::BLOCK_COMMENT, start, self.pos, true);
    }

    /// A `"..."` or `'...'` literal. Coarse: both quote styles are handled
    /// identically, backslash escapes are honored, and a raw newline (or EOF)
    /// terminates an unterminated literal — which is then an `error` token over
    /// exactly what was consumed. Lossless regardless.
    fn string_literal(&mut self, start: usize, quote: char) {
        self.bump(); // opening quote
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '\\' {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
            } else if c == quote {
                self.bump();
                terminated = true;
                break;
            } else if c == '\n' {
                break; // raw newline ends an unterminated literal
            } else {
                self.bump();
            }
        }
        let token_kind = if terminated {
            kind::STRING
        } else {
            kind::ERROR
        };
        self.push(token_kind, start, self.pos, false);
    }

    /// A numeric literal. Coarse coverage of the common forms across dialects:
    /// `0x1F`/`0b1010`/`0o17` prefixes, plain decimals, simple reals (`1.5`,
    /// `1.5e-3`), and the MASM/NASM trailing radix suffix (`0FFh`, `1010b`,
    /// `777o`, `123d`). See the module docs for the `0b…` vs `0BEEFh` punt.
    fn number(&mut self, start: usize) {
        if self.peek() == '0' {
            match self.peek_at(1) {
                Some('x') | Some('X') => {
                    self.pos += 2;
                    self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
                    return self.push(kind::NUMBER, start, self.pos, false);
                }
                Some('b') | Some('B') => {
                    self.pos += 2;
                    self.eat_while(|c| c == '0' || c == '1' || c == '_');
                    return self.push(kind::NUMBER, start, self.pos, false);
                }
                Some('o') | Some('O') => {
                    self.pos += 2;
                    self.eat_while(|c| ('0'..='7').contains(&c) || c == '_');
                    return self.push(kind::NUMBER, start, self.pos, false);
                }
                _ => {}
            }
        }
        // General run: hex-ish digits so `0FFh` / `1010b` keep their bodies.
        self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
        // Real fractional part (only when a digit follows the dot).
        if self.peek() == '.' && self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) {
            self.bump(); // .
            self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
        }
        // Trailing radix suffix letter (h/o/d/t/y; b and d are already hex digits
        // and get absorbed above). Only when not part of a following identifier.
        if matches!(
            self.peek(),
            'h' | 'H' | 'o' | 'O' | 'd' | 'D' | 't' | 'T' | 'y' | 'Y'
        ) && !is_ident_continue(self.peek_at(1).unwrap_or(' '))
        {
            self.bump();
        }
        self.push(kind::NUMBER, start, self.pos, false);
    }

    fn ident(&mut self, start: usize) {
        // First char already validated as ident-start; consume the run.
        self.bump();
        self.eat_while(is_ident_continue);
        self.push(kind::IDENT, start, self.pos, false);
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
        // Maintain the line-start flag for the directive-marker heuristic.
        if kind == self::kind::NEWLINE {
            self.line_start = true;
        } else if !trivia {
            self.line_start = false;
        }
        self.tokens.push(Token {
            kind,
            span: ByteSpan::new(start, end),
            trivia,
        });
    }
}

/// Identifier start (coarse superset, see module docs): a letter, `_`, or one of
/// the dialect symbol-prefix characters `. $ ? @ %`.
pub fn is_ident_start(c: char) -> bool {
    c == '_' || c == '.' || c == '$' || c == '?' || c == '@' || c == '%' || c.is_alphabetic()
}

/// Identifier continuation: identifier-start chars plus digits (but not `%`,
/// which only appears as a prefix).
pub fn is_ident_continue(c: char) -> bool {
    c == '_' || c == '.' || c == '$' || c == '?' || c == '@' || c.is_alphanumeric()
}

fn starts_ident(c: Option<char>) -> bool {
    c.map(is_ident_start).unwrap_or(false)
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
            "mov eax, 1 ; load one",
            ".section .text\n.global _start\n_start:\n  ret\n",
            "section .data\nmsg: db \"hi\", 0\nlen equ $-msg\n",
            "  movq %rax, %rbx   # gas comment\n  call printf@PLT\n",
            "/* block\ncomment */ add r0, r1, r2",
            "#include \"macros.inc\"\n#define WIDTH 8\n",
            "ldr r0, =label\nbl  func\nb   .loop\n",
            "val: dd 0xDEADBEEF, 1010b, 0FFh, 777o, 123\n",
            "@@: jmp @b", // MASM anon labels (coarse: @ folds into idents)
            "λ ☃ €",      // non-ascii / unknown still covered
            "",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn comment_forms() {
        assert!(texts("a ; c\n")
            .iter()
            .any(|(k, s)| *k == kind::LINE_COMMENT && s == "; c"));
        assert!(texts("a // c\n")
            .iter()
            .any(|(k, s)| *k == kind::LINE_COMMENT && s == "// c"));
        assert!(texts("a /* c */ b")
            .iter()
            .any(|(k, s)| *k == kind::BLOCK_COMMENT && s == "/* c */"));
    }

    #[test]
    fn line_leading_hash_is_directive_marker_else_comment() {
        // Line-leading `#include` -> `#` punct + ident.
        let t = texts("#include \"x\"\n");
        assert!(t.iter().any(|(k, s)| *k == kind::PUNCT && s == "#"));
        assert!(t.iter().any(|(k, s)| *k == kind::IDENT && s == "include"));
        // Mid-line `#` -> comment (documented ARM-immediate casualty).
        let t = texts("mov r0, #1\n");
        assert!(t.iter().any(|(k, s)| *k == kind::LINE_COMMENT && s == "#1"));
    }

    #[test]
    fn numbers_common_forms() {
        let t = texts("0x1F 0b1010 0o17 42 1_000 1.5 0FFh 1010b 777o 123d");
        for n in [
            "0x1F", "0b1010", "0o17", "42", "1_000", "1.5", "0FFh", "1010b", "777o", "123d",
        ] {
            assert!(
                t.contains(&(kind::NUMBER, n.to_string())),
                "missing number {n}"
            );
        }
    }

    #[test]
    fn symbol_shaped_identifiers() {
        // Directive names, AT&T registers, relocation suffixes, locals stay whole.
        let t = texts(".global %eax printf@PLT .L1 %macro");
        for id in [".global", "%eax", "printf@PLT", ".L1", "%macro"] {
            assert!(
                t.contains(&(kind::IDENT, id.to_string())),
                "missing ident {id}"
            );
        }
    }

    #[test]
    fn unterminated_string_is_error_but_covered() {
        let t = texts("db \"unterminated\n");
        assert!(t.iter().any(|(k, _)| *k == kind::ERROR));
        assert!(covers_all("db \"unterminated\n"));
    }
}
