//! Lossless Erlang lexer, grounded in the Erlang token grammar.
//!
//! Guarantees (identical contract to the Rust, Elixir, and Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs/newlines/form-feed, `%` line comments) are emitted as
//!   `trivia` tokens, never dropped. (Erlang is free-form — newlines carry no
//!   structure — so a newline is plain whitespace trivia, unlike Elixir/Python.)
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//!
//! Erlang surface handled honestly: `%` line comments; `"..."` strings and
//! `'...'` quoted atoms (with `\` escapes); bare atoms (`foo`, `node@host`);
//! variables (`Var`, `_Unused`); `$c` / `$\n` char literals; integers with `_`,
//! based integers (`16#FF`, `2#1010`), floats and exponents; `?MACRO` macro
//! references; the clause-terminating **dot** (`.` followed by whitespace / EOF /
//! a comment) is a distinct `dot` token so the parser can split top-level forms,
//! while a `.` used for record access (`R#rec.field`) or the `..`/`...` operators
//! stays ordinary punctuation.
//!
//! The main run loop carries a hard progress guard: if a dispatch iteration fails
//! to advance `pos`, one byte is consumed as an `error` token. A non-advancing
//! loop is an infinite loop (OOM), so every sub-scanner also bumps on every path.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic` /
//! `is_alphanumeric` plus `_`/`@` as a pragmatic stand-in for Erlang's ISO-Latin-1
//! identifier rules; string interpolation has no Erlang analogue. Every such byte
//! still lands in the tree, never dropped.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Erlang's reserved words. These lex as `atom` tokens; the parser/lowering
/// distinguish them via [`is_keyword`] so the call scanner never invents a call
/// out of `case(...)`-shaped guard/control syntax.
pub const KEYWORDS: &[&str] = &[
    "after", "and", "andalso", "band", "begin", "bnot", "bor", "bsl", "bsr", "bxor", "case",
    "catch", "cond", "div", "end", "fun", "if", "let", "maybe", "not", "of", "or", "orelse",
    "receive", "rem", "try", "when", "xor", "else",
];

pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.contains(&text)
}

/// Token kind labels. Stored on the CST as `&'static str`.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const COMMENT: &str = "comment";
    pub const ATOM: &str = "atom";
    pub const VAR: &str = "variable";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const STRING: &str = "string_literal";
    pub const CHAR: &str = "char_literal";
    pub const MACRO: &str = "macro";
    /// The clause-terminating `.` (period followed by whitespace / EOF / comment).
    pub const DOT: &str = "dot";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
const OPERATORS: &[&str] = &[
    "=:=", "=/=", "...", "->", "<-", "<=", ">=", "=<", "==", "/=", "++", "--", "||", "::", ":=",
    "=>", "..", "<<", ">>", "?=",
];

/// Single-character punctuation Erlang actually uses. Anything else unclassifiable
/// (e.g. `&`, `^`, `~`, a stray `@` or `\`) becomes an `error` token, per contract.
const SINGLE_PUNCT: &str = "+-*/<>=!.,;:|()[]{}#?";

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
                '%' => {
                    let end = self.find_line_end(start);
                    self.pos = end;
                    self.push(kind::COMMENT, start, end, true);
                }
                '"' => self.string(start),
                '\'' => self.quoted_atom(start),
                '$' => self.char_literal(start),
                '?' if self.peek_at(1).map(is_ident_start).unwrap_or(false) => {
                    self.macro_ref(start)
                }
                '.' => self.dot(start),
                c if is_var_start(c) => self.variable(start),
                c if is_atom_start(c) => self.atom(start),
                c if c.is_ascii_digit() => self.number(start),
                c if SINGLE_PUNCT.contains(c) => self.punct(start),
                _ => {
                    // Unknown byte/char — preserve it as an explicit error token.
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }
            // Hard progress guard: if a dispatch path consumed nothing, force one
            // byte forward as an error token. A non-advancing loop is an OOM bug.
            if self.pos == start {
                self.bump();
                self.push(kind::ERROR, start, self.pos, false);
            }
        }
        self.tokens
    }

    // --- identifiers / macros ----------------------------------------------

    fn variable(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        self.push(kind::VAR, start, self.pos, false);
    }

    fn atom(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        self.push(kind::ATOM, start, self.pos, false);
    }

    /// `?NAME`, `?MODULE` — a macro reference (cursor on `?`, ident-start follows).
    /// A leading `??` (stringifying macro) is tolerated.
    fn macro_ref(&mut self, start: usize) {
        self.bump(); // ?
        if self.peek() == '?' {
            self.bump();
        }
        self.eat_while(is_ident_continue);
        self.push(kind::MACRO, start, self.pos, false);
    }

    // --- strings / atoms / chars -------------------------------------------

    /// Scan a `"..."` string. A backslash escapes the next byte; consuming runs to
    /// the close quote or EOF (Erlang strings may span lines). Unterminated → error.
    fn string(&mut self, start: usize) {
        self.scan_quoted(start, '"', kind::STRING);
    }

    /// Scan a `'...'` quoted atom, same escape rules as a string.
    fn quoted_atom(&mut self, start: usize) {
        self.scan_quoted(start, '\'', kind::ATOM);
    }

    fn scan_quoted(&mut self, start: usize, quote: char, ok_kind: &'static str) {
        self.bump(); // opening quote
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '\\' {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
                continue;
            }
            if c == quote {
                self.bump();
                terminated = true;
                break;
            }
            self.bump();
        }
        let k = if terminated { ok_kind } else { kind::ERROR };
        self.push(k, start, self.pos, false);
    }

    /// `$a`, `$\n`, `$\\` — a single char-code literal.
    fn char_literal(&mut self, start: usize) {
        self.bump(); // $
        if self.peek() == '\\' {
            self.bump();
            if self.pos < self.bytes.len() {
                self.bump();
            }
        } else if self.pos < self.bytes.len() {
            self.bump();
        }
        self.push(kind::CHAR, start, self.pos, false);
    }

    // --- the dot ------------------------------------------------------------

    /// A `.` is the clause terminator iff what follows is whitespace, a comment, or
    /// EOF; `..`/`...` are operators; any other `.` is record-access punctuation.
    fn dot(&mut self, start: usize) {
        match self.peek_at(1) {
            Some('.') => self.punct(start), // `..` / `...`
            None => {
                self.bump();
                self.push(kind::DOT, start, self.pos, false);
            }
            Some(c) if c == '%' || c.is_whitespace() => {
                self.bump();
                self.push(kind::DOT, start, self.pos, false);
            }
            _ => self.punct(start), // record access `R#rec.field`
        }
    }

    // --- numbers ------------------------------------------------------------

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        // Based integer: `Base#Value` (`16#FF`, `2#1010`, `36#Z`). Only when a
        // value digit actually follows the `#`, so a trailing `#` (record/map) is
        // not swallowed.
        if self.peek() == '#'
            && self
                .peek_at(1)
                .map(|c| c.is_ascii_alphanumeric())
                .unwrap_or(false)
        {
            self.bump(); // #
            self.eat_while(|c| c.is_ascii_alphanumeric() || c == '_');
            return self.push(kind::INT, start, self.pos, false);
        }
        // Fractional part only when a digit follows the dot, so `1.` (then a
        // terminating dot) and tuple/record dots stay separate tokens.
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
        let k = if is_float { kind::FLOAT } else { kind::INT };
        self.push(k, start, self.pos, false);
    }

    // --- punctuation / operators -------------------------------------------

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
    c == '_' || c == '@' || c.is_alphanumeric()
}

/// A variable starts with `_` or an uppercase letter.
fn is_var_start(c: char) -> bool {
    c == '_' || c.is_uppercase()
}

/// A bare atom starts with a (lowercase / caseless) letter.
fn is_atom_start(c: char) -> bool {
    c.is_alphabetic() && !c.is_uppercase()
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

    fn round_trips(src: &str) -> bool {
        let rebuilt: String = lex(src)
            .iter()
            .map(|t| t.span.text(src))
            .collect::<Vec<_>>()
            .join("");
        rebuilt == src
    }

    #[test]
    fn contiguous_coverage_is_lossless() {
        for src in [
            "-module(foo).\n-export([fac/1]).\n",
            "fac(0) -> 1;\nfac(N) when N > 0 -> N * fac(N - 1).\n",
            "x = 16#FF + 2#1010 + 0 + 1_000 + 3.14 + 2.0e-3.\n",
            "S = \"a string\" ++ 'quoted atom' ++ atom@host.\n",
            "C = $a, NL = $\\n, BS = $\\\\.\n",
            "?MODULE:?FUNCTION_NAME(X).\n",
            "R = State#state.count, M = #{a => 1}.\n",
            "B = <<1, 2, 3>>, L = [X || X <- L, X =< 3].\n",
            "% just a comment\n",
            "λ = \"☃ €\".  % unicode\n",
            "",
            "f() -> ok.",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
            assert!(round_trips(src), "not lossless: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("fac(N) -> N * fac(N - 1).\n");
        assert!(t.contains(&(kind::ATOM, "fac".to_string())));
        assert!(t.contains(&(kind::VAR, "N".to_string())));
        assert!(t.contains(&(kind::PUNCT, "->".to_string())));
        assert!(t.iter().any(|(k, _)| *k == kind::DOT));
        assert!(is_keyword("case"));
        assert!(!is_keyword("fac"));
    }

    #[test]
    fn dot_terminator_vs_record_access() {
        let t = texts("X#rec.field.\n");
        // The mid `.` (before `field`) is punct; the trailing `.` is a clause dot.
        assert!(t.contains(&(kind::PUNCT, ".".to_string())));
        assert!(t.iter().any(|(k, _)| *k == kind::DOT));
    }

    #[test]
    fn atoms_variables_macros() {
        let t = texts("foo Bar _Baz node@host ?MACRO 'a b'\n");
        assert!(t.contains(&(kind::ATOM, "foo".to_string())));
        assert!(t.contains(&(kind::VAR, "Bar".to_string())));
        assert!(t.contains(&(kind::VAR, "_Baz".to_string())));
        assert!(t.contains(&(kind::ATOM, "node@host".to_string())));
        assert!(t.contains(&(kind::MACRO, "?MACRO".to_string())));
        assert!(t.contains(&(kind::ATOM, "'a b'".to_string())));
    }

    #[test]
    fn numbers() {
        let t = texts("16#FF 2#1010 1_000 3.14 2.0e-3 42\n");
        assert!(t.contains(&(kind::INT, "16#FF".to_string())));
        assert!(t.contains(&(kind::INT, "2#1010".to_string())));
        assert!(t.contains(&(kind::INT, "1_000".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14".to_string())));
        assert!(t.contains(&(kind::FLOAT, "2.0e-3".to_string())));
    }

    #[test]
    fn char_literals() {
        let t = texts("$a $\\n $  $\\\\\n");
        assert!(t.contains(&(kind::CHAR, "$a".to_string())));
        assert!(t.contains(&(kind::CHAR, "$\\n".to_string())));
        assert!(t.contains(&(kind::CHAR, "$ ".to_string())));
        assert!(t.contains(&(kind::CHAR, "$\\\\".to_string())));
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "S = \"oops\n",
            "A = 'oops\n",
            "λ = '☃'.  % unicode\n",
            "\n\n   \n% trailing\n",
            "& ^ ~", // unclassifiable bytes -> error tokens, still covered
            "$",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
            assert!(round_trips(src), "not lossless: {src:?}");
        }
    }
}
