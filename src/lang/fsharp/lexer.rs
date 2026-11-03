//! Lossless F# lexer, grounded in the F# language specification's lexical syntax.
//!
//! Guarantees (identical contract to the Rust/Go/Haskell lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs, `//` line comments, `(* *)` nested block comments) are
//!   emitted as `trivia` tokens, never discarded. `newline` is emitted as a
//!   *non-trivia* token: the parser uses it (together with a token's byte-column)
//!   to find column-0 top-level declarations. This is a pragmatic stand-in for
//!   F#'s full offside / layout rule — we do **not** synthesize virtual scopes —
//!   but it is enough to carve top-level items losslessly.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//!
//! Progress guarantee: every scanner advances `pos` on every path, and the main
//! loop carries an explicit guard — if a turn fails to advance, one byte is
//! consumed as an `error` token. A non-advancing branch would mean an infinite
//! loop, so this is load-bearing.
//!
//! Coverage notes (honest, breadth gaps not correctness lies):
//! - Identifier start/continue uses `char::is_alphabetic` / `is_alphanumeric`
//!   plus `_` and `'` (the prime) as a pragmatic stand-in for the spec's full
//!   Unicode classes. Generic type parameters (`'a`) lex as identifiers whose
//!   text begins with the tick; double-backtick identifiers (`` ``ident`` ``) are
//!   lexed whole.
//! - Strings cover the F# zoo: regular `"..."` (with backslash escapes, and may
//!   span lines), triple-quoted `"""..."""`, verbatim `@"..."` (doubled `""` is a
//!   literal quote), and interpolated `$"..."` / `$@"..."` / `$"""..."""`. The
//!   interior of interpolated holes is *not* re-tokenized (a deliberate punt);
//!   every byte is still covered by the string token.
//! - `(*` always opens a block comment (the F# `(*)` operator gotcha — write
//!   `( * )`); block comments nest. `//` opens a line comment.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// F# reserved keywords. These lex as `ident` tokens; the parser distinguishes
/// them via [`is_keyword`]. Contextual words are deliberately not all listed.
pub const KEYWORDS: &[&str] = &[
    "abstract",
    "and",
    "as",
    "assert",
    "base",
    "begin",
    "class",
    "default",
    "delegate",
    "do",
    "done",
    "downcast",
    "downto",
    "elif",
    "else",
    "end",
    "exception",
    "extern",
    "false",
    "finally",
    "fixed",
    "for",
    "fun",
    "function",
    "global",
    "if",
    "in",
    "inherit",
    "inline",
    "interface",
    "internal",
    "lazy",
    "let",
    "match",
    "member",
    "module",
    "mutable",
    "namespace",
    "new",
    "not",
    "null",
    "of",
    "open",
    "or",
    "override",
    "private",
    "public",
    "rec",
    "return",
    "select",
    "static",
    "struct",
    "then",
    "to",
    "true",
    "try",
    "type",
    "upcast",
    "use",
    "val",
    "void",
    "when",
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
    pub const NEWLINE: &str = "newline";
    pub const LINE_COMMENT: &str = "line_comment";
    pub const BLOCK_COMMENT: &str = "block_comment";
    /// Identifier (also covers keywords, generic params `'a`, and
    /// double-backtick identifiers).
    pub const IDENT: &str = "ident";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const CHAR: &str = "char_literal";
    pub const STRING: &str = "string_literal";
    /// A maximal run of symbol characters (an operator, including `->`, `<-`,
    /// `|>`, `::`, `:`, `=`, `|`, `.`, `..`).
    pub const OPERATOR: &str = "operator";
    /// A single special character: `( ) [ ] { } , ;`.
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Characters that compose F# symbolic operators.
fn is_symbol(c: char) -> bool {
    matches!(
        c,
        '!' | '#'
            | '%'
            | '&'
            | '*'
            | '+'
            | '.'
            | '/'
            | '<'
            | '='
            | '>'
            | '?'
            | '@'
            | '^'
            | '|'
            | '-'
            | '~'
            | ':'
            | '$'
    )
}

/// Single-character punctuation tokens (braces included; `(*` is dispatched
/// before `(` so a block comment is never split).
fn is_special(c: char) -> bool {
    matches!(c, '(' | ')' | '[' | ']' | '{' | '}' | ',' | ';')
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
                '\n' => {
                    self.bump();
                    self.push(kind::NEWLINE, start, self.pos, false);
                }
                '\r' => {
                    self.bump();
                    if self.peek() == '\n' {
                        self.bump();
                    }
                    self.push(kind::NEWLINE, start, self.pos, false);
                }
                ' ' | '\t' | '\x0c' | '\x0b' => {
                    self.eat_while(|c| matches!(c, ' ' | '\t' | '\x0c' | '\x0b'));
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                c if c.is_whitespace() => {
                    self.eat_while(|c| c.is_whitespace() && c != '\n' && c != '\r');
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                // `(*` opens a (nesting) block comment — must precede `(` punct.
                '(' if self.peek_at(1) == Some('*') => self.block_comment(start),
                // `//` opens a line comment — must precede the `/` operator run.
                '/' if self.peek_at(1) == Some('/') => self.line_comment(start),
                // Verbatim / interpolated string prefixes.
                '@' if self.peek_at(1) == Some('"') => self.string_verbatim(start, 2),
                '@' if self.peek_at(1) == Some('$') && self.peek_at(2) == Some('"') => {
                    self.string_verbatim(start, 3)
                }
                '$' if self.peek_at(1) == Some('@') && self.peek_at(2) == Some('"') => {
                    self.string_verbatim(start, 3)
                }
                '$' if self.peek_at(1) == Some('"')
                    && self.peek_at(2) == Some('"')
                    && self.peek_at(3) == Some('"') =>
                {
                    self.string_triple(start, 4)
                }
                '$' if self.peek_at(1) == Some('"') => self.string_normal(start, 2),
                '"' if self.peek_at(1) == Some('"') && self.peek_at(2) == Some('"') => {
                    self.string_triple(start, 3)
                }
                '"' => self.string_normal(start, 1),
                '\'' => self.quote(start),
                '`' if self.peek_at(1) == Some('`') => self.backtick_ident(start),
                c if is_ident_start(c) => self.ident(start),
                c if c.is_ascii_digit() => self.number(start),
                c if is_symbol(c) => self.symbol_run(start),
                c if is_special(c) => {
                    self.bump();
                    self.push(kind::PUNCT, start, self.pos, false);
                }
                _ => {
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }

            // Progress guard: if a turn somehow consumed nothing, force one byte
            // as an error token so the loop can never spin forever.
            if self.pos == start {
                self.bump();
                self.push(kind::ERROR, start, self.pos, false);
            }
        }
        self.tokens
    }

    // --- scanners -----------------------------------------------------------

    /// Nested block comment `(* ... *)` (F# block comments nest).
    fn block_comment(&mut self, start: usize) {
        self.pos += 2; // (*
        let mut depth = 1usize;
        while self.pos < self.bytes.len() && depth > 0 {
            if self.src[self.pos..].starts_with("(*") {
                depth += 1;
                self.pos += 2;
            } else if self.src[self.pos..].starts_with("*)") {
                depth -= 1;
                self.pos += 2;
            } else {
                self.bump();
            }
        }
        // Unterminated comment still covers to EOF — lossless, still trivia.
        self.push(kind::BLOCK_COMMENT, start, self.pos, true);
    }

    fn line_comment(&mut self, start: usize) {
        let end = self.find_line_end(start);
        self.pos = end;
        self.push(kind::LINE_COMMENT, start, end, true);
    }

    fn ident(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        self.push(kind::IDENT, start, self.pos, false);
    }

    /// A generic type parameter `'a` (the tick is part of the identifier). Only
    /// reached when [`quote`] has decided this `'` is not a char literal.
    fn tick_ident(&mut self, start: usize) {
        self.bump(); // '
        self.eat_while(is_ident_continue);
        self.push(kind::IDENT, start, self.pos, false);
    }

    /// Double-backtick identifier `` ``name with spaces`` `` — lexes whole until
    /// the closing `` `` ``; an unterminated one runs to EOF as `error`.
    fn backtick_ident(&mut self, start: usize) {
        self.pos += 2; // ``
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            if self.src[self.pos..].starts_with("``") {
                self.pos += 2;
                terminated = true;
                break;
            }
            // A newline ends an (illegal) unterminated backtick identifier.
            if self.peek() == '\n' {
                break;
            }
            self.bump();
        }
        let k = if terminated { kind::IDENT } else { kind::ERROR };
        self.push(k, start, self.pos, false);
    }

    /// Decide whether a `'` begins a char literal or a generic type parameter.
    fn quote(&mut self, start: usize) {
        let p1 = self.peek_at(1);
        let p2 = self.peek_at(2);
        if p1 == Some('\\') {
            // Escape sequence: definitely a char literal.
            self.char_literal(start);
        } else if p2 == Some('\'') {
            // `'x'` — a single-character literal.
            self.char_literal(start);
        } else if p1.map(is_ident_start).unwrap_or(false) {
            // `'a` with no closing quote — a generic type parameter.
            self.tick_ident(start);
        } else {
            // Fall back to a char-literal scan (may end as an `error`).
            self.char_literal(start);
        }
    }

    /// Character literal `'x'` / `'\n'`. An unterminated literal becomes `error`.
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

    /// Regular `"..."` or interpolated `$"..."` string: a backslash escapes the
    /// following byte; F# regular strings may span newlines. Unterminated at EOF
    /// is recorded as `error`.
    fn string_normal(&mut self, start: usize, prefix: usize) {
        self.pos += prefix;
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

    /// Triple-quoted `"""..."""` (and `$"""..."""`) string: no escapes; ends at
    /// the next `"""`.
    fn string_triple(&mut self, start: usize, prefix: usize) {
        self.pos += prefix;
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            if self.src[self.pos..].starts_with("\"\"\"") {
                self.pos += 3;
                terminated = true;
                break;
            }
            self.bump();
        }
        let k = if terminated {
            kind::STRING
        } else {
            kind::ERROR
        };
        self.push(k, start, self.pos, false);
    }

    /// Verbatim `@"..."` (and `$@"..."` / `@$"..."`) string: no backslash
    /// escapes; a doubled `""` is a literal quote that does not close the string.
    fn string_verbatim(&mut self, start: usize, prefix: usize) {
        self.pos += prefix;
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            if self.peek() == '"' {
                if self.peek_at(1) == Some('"') {
                    self.pos += 2; // escaped quote
                } else {
                    self.bump();
                    terminated = true;
                    break;
                }
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

    /// A run of symbol characters is one operator token. (`//` and `(*` were
    /// already dispatched, so a `/`-run here is genuine division/operator.)
    fn symbol_run(&mut self, start: usize) {
        self.eat_while(is_symbol);
        self.push(kind::OPERATOR, start, self.pos, false);
    }

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        if self.peek() == '0' && matches!(self.peek_at(1), Some('x') | Some('X')) {
            self.pos += 2;
            self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
        } else if self.peek() == '0' && matches!(self.peek_at(1), Some('o') | Some('O')) {
            self.pos += 2;
            self.eat_while(|c| ('0'..='7').contains(&c) || c == '_');
        } else if self.peek() == '0' && matches!(self.peek_at(1), Some('b') | Some('B')) {
            self.pos += 2;
            self.eat_while(|c| c == '0' || c == '1' || c == '_');
        } else {
            self.eat_while(|c| c.is_ascii_digit() || c == '_');
            // Fractional part only when a digit follows the dot, so a `..` range
            // or a `.` member access after an integer is never swallowed.
            if self.peek() == '.' && self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) {
                is_float = true;
                self.bump(); // .
                self.eat_while(|c| c.is_ascii_digit() || c == '_');
            }
            if matches!(self.peek(), 'e' | 'E') {
                let sign = matches!(self.peek_at(1), Some('+') | Some('-'));
                let dig_idx = if sign { 2 } else { 1 };
                if self
                    .peek_at(dig_idx)
                    .map(|c| c.is_ascii_digit())
                    .unwrap_or(false)
                {
                    is_float = true;
                    self.bump(); // e / E
                    if sign {
                        self.bump();
                    }
                    self.eat_while(|c| c.is_ascii_digit() || c == '_');
                }
            }
        }
        // Numeric suffixes: y uy s us l u L UL ul n un I f m F M etc. Consume a
        // trailing run of suffix letters so they stay attached to the literal.
        // `f`/`m`/`M` force a float/decimal classification.
        let suffix_start = self.pos;
        self.eat_while(|c| c.is_ascii_alphabetic());
        let suffix = &self.src[suffix_start..self.pos];
        if suffix.chars().any(|c| matches!(c, 'f' | 'F' | 'm' | 'M')) {
            is_float = true;
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
    c == '_' || c.is_alphabetic()
}

fn is_ident_continue(c: char) -> bool {
    c == '_' || c == '\'' || c.is_alphanumeric()
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
            "module Main\n\nlet main () = printfn \"hi\"\n",
            "// a line comment\nlet x = 1 // trailing\n",
            "(* nested (* block *) comment *) let y = 2\n",
            "let f x = x + 1\n",
            "let s = \"str\\\"end\"\nlet v = @\"C:\\path\\\"\"more\"\n",
            "let t = \"\"\"triple \"quoted\" string\"\"\"\n",
            "let i = $\"value = {x}\"\n",
            "let c = 'a'\nlet c2 = '\\n'\n",
            "type Foo<'a> = Bar of 'a\n",
            "let ``odd name`` = 42\n",
            "let h = 0xFF + 0o17 + 0b1010 + 3.14 + 1.5e-3 + 1.0f + 2.0m\n",
            "x |> List.map (fun y -> y * 2) |> ignore\n",
            "λ = \"☃ €\" // unicode\n",
            "",
            "\n\n   \n// trailing\n",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("let add x y = x + y");
        assert!(t.contains(&(kind::IDENT, "let".to_string())));
        assert!(t.contains(&(kind::IDENT, "add".to_string())));
        assert!(t.contains(&(kind::OPERATOR, "=".to_string())));
        assert!(t.contains(&(kind::OPERATOR, "+".to_string())));
        assert!(is_keyword("let"));
        assert!(is_keyword("member"));
        assert!(is_keyword("namespace"));
        assert!(!is_keyword("printfn"));
    }

    #[test]
    fn reserved_operators_are_single_tokens() {
        let t = texts("a :: b -> c <- d |> e .. f : g");
        for op in ["::", "->", "<-", "|>", "..", ":"] {
            assert!(
                t.contains(&(kind::OPERATOR, op.to_string())),
                "missing operator {op}"
            );
        }
    }

    #[test]
    fn nested_block_comment_is_one_token() {
        let t = texts("(* a (* b *) c *)");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::BLOCK_COMMENT && s == "(* a (* b *) c *)"));
    }

    #[test]
    fn star_paren_does_not_leak_comment() {
        // `(*` opens a comment in F#; the whole rest is one (unterminated) comment.
        let t = texts("let z = (*)\n");
        assert!(t.iter().any(|(k, _)| *k == kind::BLOCK_COMMENT));
    }

    #[test]
    fn char_vs_type_param() {
        let t = texts("'a'");
        assert!(t.contains(&(kind::CHAR, "'a'".to_string())));
        let t2 = texts("'a ");
        assert!(t2.contains(&(kind::IDENT, "'a".to_string())));
    }

    #[test]
    fn verbatim_and_triple_strings() {
        let t = texts("@\"a\"\"b\"");
        assert!(t.contains(&(kind::STRING, "@\"a\"\"b\"".to_string())));
        let t2 = texts("\"\"\"x\"\"\"");
        assert!(t2.contains(&(kind::STRING, "\"\"\"x\"\"\"".to_string())));
    }
}
