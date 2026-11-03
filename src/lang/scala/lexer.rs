//! Lossless Scala lexer, grounded in the Scala Language Specification token
//! grammar (Scala 2.13 + Scala 3).
//!
//! Guarantees (identical contract to the Rust and Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (whitespace, line/block comments) are emitted as `trivia` tokens,
//!   never discarded. Whitespace runs are kept whole; the parser inspects a
//!   whitespace token's text for a newline when it needs Scala's newline
//!   inference, so the lexer never has to fabricate zero-width tokens.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//!
//! Scala specifics handled here:
//! - Nestable block comments `/* /* */ */`.
//! - Plain `"..."`, triple-quoted (raw, multiline) `"""..."""`, and interpolated
//!   strings (`s"..."`, `f"..."`, `raw"..."`, and any `id"..."`/`id"""..."""`),
//!   including `$ident` and balanced `${ ... }` splices.
//! - Character literals `'c'` and (Scala 2) symbol literals `'sym`.
//! - Backtick-quoted identifiers `` `yield` ``.
//! - Symbolic operator identifiers (runs of operator characters lex as one `op`
//!   token, matching how Scala forms operator identifiers).
//! - Numeric literals: decimal/hex ints with `L` suffix, floats with `f`/`d`
//!   suffixes, exponents, and `_` digit separators.
//!
//! Coverage note (honest, mirrors the Rust/Python lexers): identifier start/
//! continue uses `char::is_alphabetic` / `is_alphanumeric` plus `_` and `$`
//! (which Scala treats as a letter) as a pragmatic stand-in for the full Unicode
//! identifier tables. Anything outside still lands in the tree as a covered
//! token, never dropped.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Scala's reserved keywords (2.13 + the Scala 3 additions). Like the Rust and
/// Python lexers, these lex as `ident` tokens; the parser distinguishes them via
/// [`is_keyword`]. Soft modifiers (`open`, `inline`, `opaque`, `using`, …) are
/// deliberately *not* here — they are contextual and handled by the parser.
pub const KEYWORDS: &[&str] = &[
    "abstract",
    "case",
    "catch",
    "class",
    "def",
    "do",
    "else",
    "enum",
    "export",
    "extends",
    "extension",
    "false",
    "final",
    "finally",
    "for",
    "forSome",
    "given",
    "if",
    "implicit",
    "import",
    "lazy",
    "match",
    "new",
    "null",
    "object",
    "override",
    "package",
    "private",
    "protected",
    "return",
    "sealed",
    "super",
    "then",
    "this",
    "throw",
    "trait",
    "try",
    "true",
    "type",
    "val",
    "var",
    "while",
    "with",
    "yield",
];

pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.contains(&text)
}

/// Token kind labels. Stored on the CST as `&'static str` so the tree stays
/// uniform and JSON-friendly.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const LINE_COMMENT: &str = "line_comment";
    pub const BLOCK_COMMENT: &str = "block_comment";
    pub const IDENT: &str = "ident";
    pub const BACKTICK_IDENT: &str = "backtick_ident";
    pub const OP: &str = "op";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const CHAR: &str = "char_literal";
    pub const STRING: &str = "string_literal";
    pub const SYMBOL: &str = "symbol_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Delimiter characters that always lex as their own single-byte `punct` token
/// (never merged into operator runs).
const DELIMITERS: &str = "()[]{},;.";

/// Scala operator characters. A maximal run of these forms a single operator
/// identifier (`=>`, `::`, `<:`, `+`, `<=>`, …), exactly as Scala forms them.
fn is_op_char(c: char) -> bool {
    matches!(
        c,
        '!' | '#'
            | '%'
            | '&'
            | '*'
            | '+'
            | '-'
            | '/'
            | ':'
            | '<'
            | '='
            | '>'
            | '?'
            | '@'
            | '\\'
            | '^'
            | '|'
            | '~'
    )
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
            let c = self.peek();
            match c {
                c if c.is_whitespace() => {
                    self.eat_while(|c| c.is_whitespace());
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                '/' if self.peek_at(1) == Some('/') => self.line_comment(start),
                '/' if self.peek_at(1) == Some('*') => self.block_comment(start),
                '"' => self.scan_string(start, false),
                '\'' => self.char_or_symbol(start),
                '`' => self.backtick_ident(start),
                c if is_ident_start(c) => self.ident_or_interp(start),
                c if c.is_ascii_digit() => self.number(start),
                '.' if self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) => {
                    self.number(start)
                }
                c if DELIMITERS.contains(c) => {
                    self.bump();
                    self.push(kind::PUNCT, start, self.pos, false);
                }
                c if is_op_char(c) => {
                    self.eat_while(is_op_char);
                    self.push(kind::OP, start, self.pos, false);
                }
                _ => {
                    // Unknown byte/char — preserve it as an explicit error token.
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }
        }
        self.tokens
    }

    // --- scanners -----------------------------------------------------------

    fn line_comment(&mut self, start: usize) {
        let end = self.find_line_end(start);
        self.pos = end;
        self.push(kind::LINE_COMMENT, start, end, true);
    }

    /// Scala block comments nest: `/* /* */ */`.
    fn block_comment(&mut self, start: usize) {
        self.pos += 2; // /*
        let mut depth = 1usize;
        while self.pos < self.bytes.len() && depth > 0 {
            if self.src[self.pos..].starts_with("/*") {
                depth += 1;
                self.pos += 2;
            } else if self.src[self.pos..].starts_with("*/") {
                depth -= 1;
                self.pos += 2;
            } else {
                self.bump();
            }
        }
        // Unterminated block comment is still trivia covering to EOF — lossless.
        self.push(kind::BLOCK_COMMENT, start, self.pos, true);
    }

    /// A plain identifier, or — when an identifier is immediately followed by a
    /// quote — a string interpolation prefix (`s"…"`, `raw"""…"""`, `id"…"`).
    fn ident_or_interp(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        if self.peek() == '"' {
            // The prefix is part of the string token; keep `start` at the prefix.
            self.scan_string(start, true);
        } else {
            self.push(kind::IDENT, start, self.pos, false);
        }
    }

    fn backtick_ident(&mut self, start: usize) {
        self.bump(); // opening backtick
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            self.bump();
            if c == '`' {
                terminated = true;
                break;
            }
            if c == '\n' {
                // Backtick identifiers do not span lines; stop, leaving the
                // newline out (we already consumed it — back up one).
                self.pos -= 1;
                break;
            }
        }
        let k = if terminated {
            kind::BACKTICK_IDENT
        } else {
            kind::ERROR
        };
        self.push(k, start, self.pos, false);
    }

    /// Scan a string literal beginning at the opening quote (the cursor is at the
    /// `"` when `interpolated` is false, or the interpolator prefix has already
    /// been consumed and the cursor is at the `"` when `interpolated` is true).
    /// Handles single `"…"`, triple `"""…"""` (raw, multiline), and `$…` splices
    /// in interpolated strings.
    fn scan_string(&mut self, start: usize, interpolated: bool) {
        let triple =
            self.peek() == '"' && self.peek_at(1) == Some('"') && self.peek_at(2) == Some('"');
        if triple {
            self.pos += 3;
        } else {
            self.bump(); // opening "
        }
        // Triple-quoted strings are raw: backslash is an ordinary character.
        let raw = triple;
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if interpolated && c == '$' {
                self.bump(); // $
                match self.peek() {
                    '$' => self.bump(),                     // escaped literal dollar
                    '{' => self.skip_brace_group(),         // ${ expr } splice
                    _ => self.eat_while(is_ident_continue), // $ident splice
                }
                continue;
            }
            if c == '\\' && !raw {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
                continue;
            }
            if c == '"' {
                if triple {
                    if self.peek_at(1) == Some('"') && self.peek_at(2) == Some('"') {
                        self.pos += 3;
                        terminated = true;
                        break;
                    }
                    self.bump();
                } else {
                    self.bump();
                    terminated = true;
                    break;
                }
            } else if c == '\n' && !triple {
                break; // unterminated single-line string ends at the newline
            } else {
                self.bump();
            }
        }
        let k = if terminated {
            kind::STRING
        } else {
            kind::ERROR
        };
        self.push(k, start, self.pos, false);
    }

    /// Skip a balanced `{ … }` interpolation splice (cursor at the opening `{`).
    /// Nested strings are skipped so braces inside them never unbalance the run;
    /// iterative so deeply nested splices cannot overflow the stack.
    fn skip_brace_group(&mut self) {
        self.bump(); // {
        let mut depth = 1usize;
        while self.pos < self.bytes.len() && depth > 0 {
            match self.peek() {
                '{' => {
                    depth += 1;
                    self.bump();
                }
                '}' => {
                    depth -= 1;
                    self.bump();
                }
                '"' => self.skip_simple_string(),
                _ => self.bump(),
            }
        }
    }

    /// Skip a simple `"…"` string (handling `\"`) without classifying it — used
    /// only inside `${ … }` splices to keep brace counting honest.
    fn skip_simple_string(&mut self) {
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
                break;
            } else if c == '\n' {
                break;
            } else {
                self.bump();
            }
        }
    }

    /// `'` begins either a character literal (`'c'`, `'\n'`) or a Scala 2 symbol
    /// literal (`'sym`). The discriminator mirrors the Rust lexer's char/lifetime
    /// split: a single identifier char immediately followed by a closing quote is
    /// a char literal; otherwise it is a symbol.
    fn char_or_symbol(&mut self, start: usize) {
        let after = self.peek_at(1);
        if starts_ident(after) {
            let id_len = after.map(|c| c.len_utf8()).unwrap_or(0);
            let next = self.src[start + 1 + id_len..].chars().next();
            if next != Some('\'') {
                // Symbol literal: `'` then an identifier (no closing quote).
                self.bump(); // '
                self.eat_while(is_ident_continue);
                self.push(kind::SYMBOL, start, self.pos, false);
                return;
            }
        }
        self.char_literal(start);
    }

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
            // Long suffix.
            if matches!(self.peek(), 'l' | 'L') {
                self.bump();
            }
            return self.push(kind::INT, start, self.pos, false);
        }
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        // Fractional part only when a digit follows the dot, so `1.toString` and
        // range `1.to(2)` keep `.` as a separate selector token.
        if self.peek() == '.' && self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) {
            is_float = true;
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
                is_float = true;
                self.bump(); // e
                if sign_len == 1 {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit() || c == '_');
            }
        }
        // Float/long suffix: f, F, d, D mark a float; l, L mark a long int.
        match self.peek() {
            'f' | 'F' | 'd' | 'D' => {
                is_float = true;
                self.bump();
            }
            'l' | 'L' => {
                self.bump();
            }
            _ => {}
        }
        let k = if is_float { kind::FLOAT } else { kind::INT };
        self.push(k, start, self.pos, false);
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
    c == '_' || c == '$' || c.is_alphabetic()
}

fn is_ident_continue(c: char) -> bool {
    c == '_' || c == '$' || c.is_alphanumeric()
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
            "object Main { def main(args: Array[String]): Unit = println(\"hi\") }",
            "val x = 1.5e3f + 0xFF_00L\n",
            "// line\n/* nested /* block */ */ class C\n",
            "val s = s\"hello $name and ${a + b}\"\n",
            "val t = \"\"\"multi\nline \"quoted\" $x\"\"\"\n",
            "val c = 'a'\nval sym = 'identifier\nval bt = `yield`\n",
            "def +(o: V): V = ???\nx <- xs; a => b; t <: U",
            "λ ☃ €  // unicode\n",
            "1.to(10) x.0 1.method",
            "",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("def add(a: Int): Int = a + b");
        assert!(t.contains(&(kind::IDENT, "def".to_string())));
        assert!(t.contains(&(kind::IDENT, "add".to_string())));
        assert!(t.contains(&(kind::PUNCT, "(".to_string())));
        assert!(t.contains(&(kind::OP, "+".to_string())));
        assert!(is_keyword("def"));
        assert!(is_keyword("trait"));
        assert!(!is_keyword("add"));
    }

    #[test]
    fn arrow_and_bounds_are_single_ops() {
        let t = texts("a => b <- c <: d >: e");
        assert!(t.contains(&(kind::OP, "=>".to_string())));
        assert!(t.contains(&(kind::OP, "<-".to_string())));
        assert!(t.contains(&(kind::OP, "<:".to_string())));
        assert!(t.contains(&(kind::OP, ">:".to_string())));
    }

    #[test]
    fn interpolated_string_is_one_token() {
        let t = texts("s\"a ${b + c} d $e\"");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "s\"a ${b + c} d $e\""));
    }

    #[test]
    fn triple_quoted_spans_newlines_and_quotes() {
        let t = texts("\"\"\"a\nb \"q\" c\"\"\"");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "\"\"\"a\nb \"q\" c\"\"\""));
    }

    #[test]
    fn char_vs_symbol_literal() {
        let t = texts("'a' 'sym");
        assert!(t.contains(&(kind::CHAR, "'a'".to_string())));
        assert!(t.contains(&(kind::SYMBOL, "'sym".to_string())));
    }

    #[test]
    fn backtick_identifier() {
        let t = texts("`type`");
        assert!(t.contains(&(kind::BACKTICK_IDENT, "`type`".to_string())));
    }

    #[test]
    fn numbers() {
        let t = texts("0xFF_00L 10_000 3.14 2e10 1.5f 42L");
        assert!(t.contains(&(kind::INT, "0xFF_00L".to_string())));
        assert!(t.contains(&(kind::INT, "10_000".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14".to_string())));
        assert!(t.contains(&(kind::FLOAT, "2e10".to_string())));
        assert!(t.contains(&(kind::FLOAT, "1.5f".to_string())));
        assert!(t.contains(&(kind::INT, "42L".to_string())));
    }

    #[test]
    fn selector_dot_is_not_eaten_by_number() {
        let t = texts("1.toString");
        assert_eq!(
            t,
            vec![
                (kind::INT, "1".to_string()),
                (kind::PUNCT, ".".to_string()),
                (kind::IDENT, "toString".to_string()),
            ]
        );
    }
}
