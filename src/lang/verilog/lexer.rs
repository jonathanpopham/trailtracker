//! Lossless Verilog / SystemVerilog lexer, grounded in the IEEE 1364 (Verilog)
//! and 1800 (SystemVerilog) lexical grammars.
//!
//! Guarantees (identical contract to the Rust, Lua, and C lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs, newlines, `//` line comments and `/* */` block
//!   comments) are emitted as `trivia` tokens, not discarded. A newline is its
//!   own trivia kind so the parser can find directive-line boundaries; it is
//!   *not* structurally significant otherwise (Verilog is free-form).
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped — an unterminated string or block
//!   comment is emitted spanning to end of input.
//! - The main run loop advances `pos` on every iteration; a final progress guard
//!   force-consumes one char as an `error` token if no scanner moved the cursor,
//!   so a malformed input can never spin into an infinite loop / OOM.
//!
//! Verilog-specific surface the lexer covers:
//! - Compiler directives and macro uses: a backtick followed by an identifier
//!   (`` `define ``, `` `include ``, `` `ifdef ``, `` `timescale ``, `` `MY_MACRO ``)
//!   lex as one `directive` token.
//! - System tasks / functions: `$` followed by an identifier (`$display`,
//!   `$finish`, `$time`) lex as one `system_ident` token.
//! - Numbers in every form: plain decimals (`42`, `1_000`), reals (`1.5`,
//!   `1.5e-3`, `3.0E10`), sized/based literals (`8'hFF`, `4'b1010`, `12'd34`),
//!   and unsized based literals (`'1`, `'0`, `'hFF`, `'x`).
//! - Strings `"…"` with backslash escapes.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_` and `$` (legal in Verilog identifier
//! continuation). Escaped identifiers (`\foo+bar ` terminated by whitespace) are
//! handled explicitly. Anything outside still lands in the tree as a covered
//! token, never dropped.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// A representative set of Verilog / SystemVerilog reserved words. These lex as
/// `ident` tokens; the parser distinguishes them via text. The list is broad but
/// not exhaustive — unknown words simply parse as ordinary identifiers, which is
/// the honest, lossless behavior.
pub const KEYWORDS: &[&str] = &[
    "module",
    "macromodule",
    "endmodule",
    "function",
    "endfunction",
    "task",
    "endtask",
    "class",
    "endclass",
    "package",
    "endpackage",
    "interface",
    "endinterface",
    "program",
    "endprogram",
    "begin",
    "end",
    "generate",
    "endgenerate",
    "case",
    "casex",
    "casez",
    "endcase",
    "primitive",
    "endprimitive",
    "config",
    "endconfig",
    "clocking",
    "endclocking",
    "property",
    "endproperty",
    "sequence",
    "endsequence",
    "covergroup",
    "endgroup",
    "specify",
    "endspecify",
    "parameter",
    "localparam",
    "import",
    "export",
    "extends",
    "implements",
    "virtual",
    "automatic",
    "static",
    "extern",
    "pure",
    "typedef",
    "enum",
    "struct",
    "union",
    "logic",
    "reg",
    "wire",
    "input",
    "output",
    "inout",
    "assign",
    "always",
    "always_comb",
    "always_ff",
    "always_latch",
    "initial",
    "if",
    "else",
    "for",
    "while",
    "repeat",
    "forever",
    "return",
];

pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.contains(&text)
}

/// Token kind labels. Stored on the CST as `&'static str` so the tree stays
/// uniform and JSON-friendly.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const NEWLINE: &str = "newline";
    pub const LINE_COMMENT: &str = "line_comment";
    pub const BLOCK_COMMENT: &str = "block_comment";
    pub const IDENT: &str = "ident";
    /// A `$`-prefixed system task / function name (`$display`).
    pub const SYSTEM_IDENT: &str = "system_ident";
    /// A backtick-prefixed compiler directive or macro use (`` `define ``).
    pub const DIRECTIVE: &str = "directive";
    pub const STRING: &str = "string_literal";
    /// Any numeric literal: decimal, real, or sized/based.
    pub const NUMBER: &str = "number";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
const OPERATORS: &[&str] = &[
    "<<<=", ">>>=", "<<<", ">>>", "<<=", ">>=", "===", "!==", "==?", "!=?", "->>", "<->", "==",
    "!=", "<=", ">=", "&&", "||", "<<", ">>", "**", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=",
    "~&", "~|", "~^", "^~", "::", "++", "--", "->", "=>", "*>", "+:", "-:", ".*",
];

const SINGLE_PUNCT: &str = "+-*/%!&|^~<>=?:;,.()[]{}@#'";

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
                '/' if self.peek_at(1) == Some('*') => self.block_comment(start),
                '"' => self.string_literal(start),
                '`' if starts_ident(self.peek_at(1)) => self.directive(start),
                '$' if starts_ident(self.peek_at(1)) => self.system_ident(start),
                '\\' => self.escaped_ident(start),
                '\'' if is_based_follow(self.peek_at(1)) => self.based_number(start),
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
            // (and an OOM as `tokens` never grows past it). If somehow no scanner
            // moved the cursor, force-consume one char as an error token. Under
            // the current arms this is unreachable, but it is the real defense
            // against a future edit that forgets to advance.
            if self.pos == start {
                self.bump();
                if self.pos == start {
                    // Cannot even bump (empty remainder); break to avoid spinning.
                    break;
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

    /// A `/* … */` block comment. Verilog block comments do **not** nest. An
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

    fn string_literal(&mut self, start: usize) {
        self.bump(); // opening "
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '\\' {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
            } else if c == '"' {
                self.bump();
                terminated = true;
                break;
            } else if c == '\n' {
                // A raw newline ends an unterminated string literal.
                break;
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

    /// A backtick directive / macro use: `` ` `` followed by identifier chars.
    fn directive(&mut self, start: usize) {
        self.bump(); // `
        self.eat_while(is_ident_continue);
        self.push(kind::DIRECTIVE, start, self.pos, false);
    }

    /// A `$`-prefixed system task / function name.
    fn system_ident(&mut self, start: usize) {
        self.bump(); // $
        self.eat_while(is_ident_continue);
        self.push(kind::SYSTEM_IDENT, start, self.pos, false);
    }

    /// An escaped identifier: `\` then any non-whitespace run, terminated by
    /// whitespace (the terminating whitespace is *not* part of the identifier).
    /// A lone `\` with nothing after it is still covered as an ident token.
    fn escaped_ident(&mut self, start: usize) {
        self.bump(); // backslash
        self.eat_while(|c| !c.is_whitespace());
        self.push(kind::IDENT, start, self.pos, false);
    }

    fn ident(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        self.push(kind::IDENT, start, self.pos, false);
    }

    /// A number starting with a decimal digit. Handles an optional fractional and
    /// exponent part (real literals) and an optional based suffix (`8'hFF`).
    fn number(&mut self, start: usize) {
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        // Fractional part only when a digit follows the dot (so `1.field` and a
        // bare `.` stay separate).
        if self.peek() == '.' && self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) {
            self.bump(); // .
            self.eat_while(|c| c.is_ascii_digit() || c == '_');
        }
        // Exponent.
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
                self.bump(); // e
                if sign_len == 1 {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit() || c == '_');
            }
        }
        // Sized/based suffix: `8'hFF`, `4'b1010`, `12'd34`.
        if self.peek() == '\'' && is_based_follow(self.peek_at(1)) {
            self.eat_based_suffix();
        }
        self.push(kind::NUMBER, start, self.pos, false);
    }

    /// An unsized based number starting at the apostrophe: `'1`, `'hFF`, `'x`.
    fn based_number(&mut self, start: usize) {
        self.eat_based_suffix();
        self.push(kind::NUMBER, start, self.pos, false);
    }

    /// Consume a based suffix positioned at the `'`: `' [sS]? [bodhBODH]? value`.
    /// The value run is permissive over the legal digit alphabets plus `x`, `z`,
    /// `?`, and `_`.
    fn eat_based_suffix(&mut self) {
        self.bump(); // '
        if matches!(self.peek(), 's' | 'S') {
            self.bump();
        }
        if matches!(self.peek(), 'b' | 'o' | 'd' | 'h' | 'B' | 'O' | 'D' | 'H') {
            self.bump();
        }
        self.eat_while(|c| c.is_ascii_hexdigit() || matches!(c, 'x' | 'X' | 'z' | 'Z' | '?' | '_'));
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

/// Verilog identifiers may contain `_` and `$` after the first character.
fn is_ident_continue(c: char) -> bool {
    c == '_' || c == '$' || c.is_alphanumeric()
}

fn starts_ident(c: Option<char>) -> bool {
    c.map(is_ident_start).unwrap_or(false)
}

/// True if the char after a `'` can begin a (un)sized based literal: a base
/// letter, a sign-spec `s`/`S`, or a value char (`0`, `1`, `x`, `z`, `?`, a hex
/// digit). A `'` followed by `{` is the SystemVerilog assignment-pattern opener,
/// not a number, so it is excluded.
fn is_based_follow(c: Option<char>) -> bool {
    match c {
        Some(ch) => {
            matches!(
                ch,
                'b' | 'o'
                    | 'd'
                    | 'h'
                    | 'B'
                    | 'O'
                    | 'D'
                    | 'H'
                    | 's'
                    | 'S'
                    | 'x'
                    | 'X'
                    | 'z'
                    | 'Z'
                    | '?'
            ) || ch.is_ascii_hexdigit()
        }
        None => false,
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
            "module m; endmodule",
            "wire [7:0] a = 8'hFF;",
            "logic b = 4'b1010, c = 'x, d = '1;",
            "// line\nassign x = y;",
            "/* block\ncomment */ initial begin end",
            "`define WIDTH 8\n`include \"defs.vh\"",
            "$display(\"hello %d\", count);",
            "always @(posedge clk) #5 q <= d;",
            "(* keep = \"true\" *) wire w;",
            "real r = 1.5e-3; int n = 1_000;",
            "\\escaped+ident logic;",
            "λ ☃ €", // non-ascii idents / unknowns still covered
            "",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("module top; endmodule");
        assert!(t.contains(&(kind::IDENT, "module".to_string())));
        assert!(t.contains(&(kind::IDENT, "top".to_string())));
        assert!(t.contains(&(kind::IDENT, "endmodule".to_string())));
        assert!(is_keyword("module"));
        assert!(is_keyword("endmodule"));
        assert!(!is_keyword("top"));
    }

    #[test]
    fn directives_and_system_tasks() {
        let t = texts("`include \"x.vh\" $display($time);");
        assert!(t.contains(&(kind::DIRECTIVE, "`include".to_string())));
        assert!(t.contains(&(kind::SYSTEM_IDENT, "$display".to_string())));
        assert!(t.contains(&(kind::SYSTEM_IDENT, "$time".to_string())));
    }

    #[test]
    fn numbers_all_forms() {
        let t = texts("8'hFF 4'b1010 12'd34 'x '1 42 1_000 1.5 1.5e-3 3.0E10");
        for n in [
            "8'hFF", "4'b1010", "12'd34", "'x", "'1", "42", "1_000", "1.5", "1.5e-3", "3.0E10",
        ] {
            assert!(
                t.contains(&(kind::NUMBER, n.to_string())),
                "missing number {n}"
            );
        }
    }

    #[test]
    fn assignment_pattern_is_not_a_number() {
        // `'{ … }` must not be eaten as a based literal.
        let t = texts("'{1, 2}");
        assert!(t.iter().any(|(k, s)| *k == kind::PUNCT && s == "'"));
        assert!(t.iter().any(|(k, s)| *k == kind::PUNCT && s == "{"));
    }

    #[test]
    fn operators() {
        let t = texts("a === b !== c <= d >= e << f >> g ::h ->i");
        for op in ["===", "!==", "<=", ">=", "<<", ">>", "::", "->"] {
            assert!(
                t.contains(&(kind::PUNCT, op.to_string())),
                "missing operator {op}"
            );
        }
    }

    #[test]
    fn unterminated_string_is_error_but_covered() {
        let t = texts("x = \"unterminated\n");
        assert!(t.iter().any(|(k, _)| *k == kind::ERROR));
        assert!(covers_all("x = \"unterminated\n"));
    }
}
