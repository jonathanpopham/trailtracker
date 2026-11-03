//! Lossless Haskell lexer, grounded in the Haskell 2010 Report's lexical syntax.
//!
//! Guarantees (identical contract to the Rust/Go/Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs, line and nested block comments) are emitted as `trivia`
//!   tokens, never discarded. `newline` is emitted as a *non-trivia* token: the
//!   parser uses it (together with a token's byte-column) to find column-0
//!   top-level declarations. This is a pragmatic stand-in for Haskell's full
//!   layout algorithm — we do **not** synthesize virtual `{ ; }` — but it is
//!   enough to carve top-level items losslessly.
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
//!   plus `_` and `'` (the prime) as a pragmatic stand-in for the Report's full
//!   Unicode classes. Constructors (`conid`, uppercase-initial) and variables
//!   (`varid`) are distinguished by the first character's case.
//! - String literals stop at an unescaped newline (recorded as `error` when
//!   unterminated); multi-line string *gaps* (`"\   \"`) are handled only insofar
//!   as a backslash escapes the following byte. Either way the bytes are covered.
//! - `.lhs` literate Haskell is lexed with this same lexer: it stays lossless,
//!   but prose lines are tokenized as ordinary lexemes (no Bird-track / code-env
//!   extraction). That is a deliberate punt — correctness of losslessness over
//!   completeness of literate semantics.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Haskell 2010 reserved identifiers. These lex as `varid`/`conid` tokens; the
/// parser distinguishes them via [`is_keyword`]. Contextual words (`as`,
/// `qualified`, `hiding`, `family`, `role`) are deliberately *not* keywords.
pub const KEYWORDS: &[&str] = &[
    "case", "class", "data", "default", "deriving", "do", "else", "foreign", "if", "import", "in",
    "infix", "infixl", "infixr", "instance", "let", "module", "newtype", "of", "then", "type",
    "where",
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
    /// Variable identifier (lowercase- or underscore-initial).
    pub const VARID: &str = "varid";
    /// Constructor / module / type identifier (uppercase-initial).
    pub const CONID: &str = "conid";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const CHAR: &str = "char_literal";
    pub const STRING: &str = "string_literal";
    /// A maximal run of symbol characters (an operator, including reserved ops
    /// like `::`, `=`, `->`, `=>`, `|`, `..`, `:`, `\`, `@`, `~`, `<-`).
    pub const OPERATOR: &str = "operator";
    /// A single special character: `( ) [ ] { } , ; ` (backtick).
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// The Haskell `ascSymbol` set: characters that compose operators.
fn is_symbol(c: char) -> bool {
    matches!(
        c,
        '!' | '#'
            | '$'
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
            | '\\'
            | '^'
            | '|'
            | '-'
            | '~'
            | ':'
    )
}

/// The Haskell `special` set (minus `{`/`}` which are dispatched separately so
/// `{-` can open a block comment): single-character punctuation tokens.
fn is_special(c: char) -> bool {
    matches!(c, '(' | ')' | '[' | ']' | '{' | '}' | ',' | ';' | '`')
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
                    // Other Unicode whitespace (but not the newline chars handled
                    // above) — still trivia, still covered.
                    self.eat_while(|c| c.is_whitespace() && c != '\n' && c != '\r');
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                '{' if self.peek_at(1) == Some('-') => self.block_comment(start),
                '"' => self.string_literal(start),
                '\'' => self.char_literal(start),
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

    /// Nested block comment `{- ... -}` (Haskell block comments nest, like Rust).
    fn block_comment(&mut self, start: usize) {
        self.pos += 2; // {-
        let mut depth = 1usize;
        while self.pos < self.bytes.len() && depth > 0 {
            if self.src[self.pos..].starts_with("{-") {
                depth += 1;
                self.pos += 2;
            } else if self.src[self.pos..].starts_with("-}") {
                depth -= 1;
                self.pos += 2;
            } else {
                self.bump();
            }
        }
        // Unterminated comment still covers to EOF — lossless, still trivia.
        self.push(kind::BLOCK_COMMENT, start, self.pos, true);
    }

    fn ident(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        let text = &self.src[start..self.pos];
        let k = match text.chars().next() {
            Some(c) if c.is_uppercase() => kind::CONID,
            _ => kind::VARID,
        };
        self.push(k, start, self.pos, false);
    }

    /// A run of symbol characters. Two-or-more leading dashes that are not part of
    /// a larger operator begin a line comment (Report §2.3); otherwise the whole
    /// maximal symbol run is one operator token.
    fn symbol_run(&mut self, start: usize) {
        if self.peek() == '-' {
            let mut dashes = 0usize;
            while self.peek_at(dashes) == Some('-') {
                dashes += 1;
            }
            if dashes >= 2 {
                let after = self.peek_at(dashes);
                let is_comment = match after {
                    None => true,
                    Some(ch) => !is_symbol(ch),
                };
                if is_comment {
                    let end = self.find_line_end(start);
                    self.pos = end;
                    self.push(kind::LINE_COMMENT, start, end, true);
                    return;
                }
            }
        }
        self.eat_while(is_symbol);
        self.push(kind::OPERATOR, start, self.pos, false);
    }

    /// Interpreted string `"..."`: a backslash escapes the following byte (which
    /// also tolerates simple string gaps); an unescaped newline ends an
    /// unterminated literal, recorded as `error`.
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

    /// Character literal `'x'` / `'\n'`. The lexer only reaches here when `'` is
    /// not an identifier-continuation prime (those are consumed by [`ident`]); an
    /// unterminated literal becomes an `error`.
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
        } else if self.peek() == '0' && matches!(self.peek_at(1), Some('o') | Some('O')) {
            self.pos += 2;
            self.eat_while(|c| ('0'..='7').contains(&c) || c == '_');
        } else if self.peek() == '0' && matches!(self.peek_at(1), Some('b') | Some('B')) {
            self.pos += 2;
            self.eat_while(|c| c == '0' || c == '1' || c == '_');
        } else {
            self.eat_while(|c| c.is_ascii_digit() || c == '_');
            // Fractional part only when a digit follows the dot, so a `..` range
            // or a `.` operator after an integer is never swallowed.
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
            "module Main where\n\nmain = putStrLn \"hi\"\n",
            "-- a line comment\nx = 1 -- trailing\n",
            "{- nested {- block -} comment -} y = 2\n",
            "f x = x + 1 :: Int\n",
            "g a b = a `seq` b --> not a comment, an operator\n",
            "h = 0xFF + 0o17 + 0b1010 + 3.14 + 1.5e-3\n",
            "c = 'a'\nc2 = '\\n'\ns = \"str\\\"end\"\n",
            "prime' x'' = x''\n",
            "qualified = Data.Map.lookup\n",
            "λ = \"☃ €\" -- unicode\n",
            "",
            "\n\n   \n-- trailing\n",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("add x y = x + y");
        assert!(t.contains(&(kind::VARID, "add".to_string())));
        assert!(t.contains(&(kind::OPERATOR, "=".to_string())));
        assert!(t.contains(&(kind::OPERATOR, "+".to_string())));
        assert!(is_keyword("module"));
        assert!(is_keyword("instance"));
        assert!(!is_keyword("qualified"));
    }

    #[test]
    fn conid_vs_varid() {
        let t = texts("Just x");
        assert!(t.contains(&(kind::CONID, "Just".to_string())));
        assert!(t.contains(&(kind::VARID, "x".to_string())));
    }

    #[test]
    fn dashes_operator_vs_comment() {
        // `-->` is a legal operator, not a comment.
        let t = texts("a --> b");
        assert!(t.contains(&(kind::OPERATOR, "-->".to_string())));
        assert!(t.iter().all(|(k, _)| *k != kind::LINE_COMMENT));
        // `--` then non-symbol is a comment.
        let t2 = texts("a -- b");
        assert!(t2
            .iter()
            .any(|(k, s)| *k == kind::LINE_COMMENT && s == "-- b"));
    }

    #[test]
    fn reserved_operators_are_single_tokens() {
        let t = texts("a :: b -> c => d <- e | f .. g");
        for op in ["::", "->", "=>", "<-", "|", ".."] {
            assert!(
                t.contains(&(kind::OPERATOR, op.to_string())),
                "missing operator {op}"
            );
        }
    }

    #[test]
    fn nested_block_comment() {
        let t = texts("{- a {- b -} c -}");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::BLOCK_COMMENT && s == "{- a {- b -} c -}"));
    }
}
