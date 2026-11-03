//! Lossless Prolog lexer, grounded in the ISO Prolog token grammar.
//!
//! Guarantees (identical contract to the Rust, Elixir, Erlang, and Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs/newlines, `%` line comments, `/* … */` block comments)
//!   are emitted as `trivia` tokens, never dropped. Prolog is free-form — newlines
//!   carry no structure — so a newline is plain whitespace trivia.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//!
//! Prolog surface handled honestly: `%` line comments and `/* … */` block
//! comments; `"..."` strings, `'...'` quoted atoms, and `` `...` `` back-quoted
//! strings (with `\` escapes and ISO doubled-quote `''`/`""`/``` `` ``` escapes);
//! bare atoms (`foo`, `is_list`); variables (`Var`, `_Unused`, `_`); `0'c` /
//! `0'\n` character-code integers; `0x`/`0o`/`0b` based integers; decimal integers
//! with `_` digit-group separators; floats with exponents; symbolic / graphic
//! atoms (`:-`, `?-`, `-->`, `\+`, `=..`, `@>=`, `=:=`, `=\=`, …) scanned as a
//! maximal run of graphic chars — which makes every Prolog operator fall out for
//! free; and the solo atoms `!` and `;`.
//!
//! The clause terminator (the **end token**) is a *lone* `.` followed by layout, a
//! comment, or EOF — emitted as a distinct [`kind::END`] token so the parser can
//! split top-level clauses. A `.` that is part of a longer graphic run (`=..`), a
//! `.` glued to a non-layout char (the list/dict/functor `.` as in `Dict.key` or
//! `'[|]'`/`.(H,T)`), and the `.` inside a float (`3.14`) all stay ordinary
//! tokens. This mirrors ISO 6.4.8: only a graphic token consisting of exactly one
//! `.` followed by layout/EOF/`%` is the end token.
//!
//! The main run loop carries a hard progress guard: if a dispatch iteration fails
//! to advance `pos`, one byte is consumed as an `error` token. A non-advancing
//! loop is an infinite loop (OOM), so every sub-scanner also bumps on every path.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic` /
//! `is_alphanumeric` plus `_` as a pragmatic stand-in for ISO's identifier rules;
//! ISO's full escape-sequence grammar inside quoted tokens is not validated (we
//! only honor `\`-escapes and doubled quotes for *boundary* purposes — every byte
//! still lands in the tree). String interpolation has no Prolog analogue.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Token kind labels. Stored on the CST as `&'static str`.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const COMMENT: &str = "comment";
    /// A bare, quoted, symbolic, or solo atom (`foo`, `'a b'`, `:-`, `!`).
    pub const ATOM: &str = "atom";
    pub const VAR: &str = "variable";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const STRING: &str = "string_literal";
    pub const BACKQUOTE: &str = "backquote_literal";
    /// The clause-terminating lone `.` (followed by layout / a comment / EOF).
    pub const END: &str = "clause_end";
    /// Punctuation that is not an atom: `,` `|` `(` `)` `[` `]` `{` `}` `;`.
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
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
                '%' => {
                    let end = self.find_line_end(start);
                    self.pos = end;
                    self.push(kind::COMMENT, start, end, true);
                }
                '/' if self.peek_at(1) == Some('*') => self.block_comment(start),
                '"' => self.scan_quoted(start, '"', kind::STRING),
                '\'' => self.scan_quoted(start, '\'', kind::ATOM),
                '`' => self.scan_quoted(start, '`', kind::BACKQUOTE),
                c if is_var_start(c) => self.variable(start),
                c if c.is_ascii_digit() => self.number(start),
                c if is_atom_start(c) => self.atom(start),
                c if is_graphic(c) => self.graphic(start),
                '!' => {
                    // The cut: a solo atom.
                    self.bump();
                    self.push(kind::ATOM, start, self.pos, false);
                }
                ';' | ',' | '|' | '(' | ')' | '[' | ']' | '{' | '}' => {
                    self.bump();
                    self.push(kind::PUNCT, start, self.pos, false);
                }
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

    // --- identifiers --------------------------------------------------------

    fn variable(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        self.push(kind::VAR, start, self.pos, false);
    }

    fn atom(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        self.push(kind::ATOM, start, self.pos, false);
    }

    // --- comments -----------------------------------------------------------

    /// `/* … */` block comment. Non-nested (ISO Prolog block comments do not
    /// nest); an unterminated comment runs to EOF and stays lossless.
    fn block_comment(&mut self, start: usize) {
        self.bump(); // /
        self.bump(); // *
        while self.pos < self.bytes.len() {
            if self.peek() == '*' && self.peek_at(1) == Some('/') {
                self.bump(); // *
                self.bump(); // /
                break;
            }
            self.bump();
        }
        self.push(kind::COMMENT, start, self.pos, true);
    }

    // --- quoted forms -------------------------------------------------------

    /// Scan a `"..."` / `'...'` / `` `...` `` token. A backslash escapes the next
    /// byte; a doubled quote (`''`, `""`, ` `` `) is an in-token escaped quote, not
    /// a close. Runs to the close quote or EOF (these may span lines). An
    /// unterminated token becomes an `error` token over its bytes.
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
                // ISO doubled-quote escape: a second identical quote continues.
                if self.peek_at(1) == Some(quote) {
                    self.bump();
                    self.bump();
                    continue;
                }
                self.bump();
                terminated = true;
                break;
            }
            self.bump();
        }
        let k = if terminated { ok_kind } else { kind::ERROR };
        self.push(k, start, self.pos, false);
    }

    // --- numbers ------------------------------------------------------------

    fn number(&mut self, start: usize) {
        // Special leading-`0` forms: `0'c` char code, `0x`/`0o`/`0b` based ints.
        if self.peek() == '0' {
            match self.peek_at(1) {
                Some('\'') => return self.char_code(start),
                Some('x') | Some('X')
                    if self
                        .peek_at(2)
                        .map(|c| c.is_ascii_hexdigit())
                        .unwrap_or(false) =>
                {
                    self.bump(); // 0
                    self.bump(); // x
                    self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
                    return self.push(kind::INT, start, self.pos, false);
                }
                Some('o') | Some('O')
                    if self
                        .peek_at(2)
                        .map(|c| ('0'..='7').contains(&c))
                        .unwrap_or(false) =>
                {
                    self.bump(); // 0
                    self.bump(); // o
                    self.eat_while(|c| ('0'..='7').contains(&c) || c == '_');
                    return self.push(kind::INT, start, self.pos, false);
                }
                Some('b') | Some('B')
                    if self
                        .peek_at(2)
                        .map(|c| c == '0' || c == '1')
                        .unwrap_or(false) =>
                {
                    self.bump(); // 0
                    self.bump(); // b
                    self.eat_while(|c| c == '0' || c == '1' || c == '_');
                    return self.push(kind::INT, start, self.pos, false);
                }
                _ => {}
            }
        }

        let mut is_float = false;
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        // Fractional part only when a digit follows the dot, so a trailing `.`
        // (the clause terminator) and the functor/list `.` stay separate tokens.
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

    /// `0'c`, `0'\n`, `0'\\`, `0''` — a character-code integer (cursor at `0`).
    fn char_code(&mut self, start: usize) {
        self.bump(); // 0
        self.bump(); // '
        if self.peek() == '\\' {
            self.bump();
            if self.pos < self.bytes.len() {
                self.bump();
            }
        } else if self.peek() == '\'' && self.peek_at(1) == Some('\'') {
            // `0''` is the code of the quote char (doubled).
            self.bump();
            self.bump();
        } else if self.pos < self.bytes.len() {
            self.bump();
        }
        self.push(kind::INT, start, self.pos, false);
    }

    // --- graphic / symbolic atoms ------------------------------------------

    /// A maximal run of graphic chars. If the run is a lone `.` followed by
    /// layout / a comment / EOF it is the clause **end** token; otherwise it is a
    /// symbolic atom (which is how every Prolog operator — `:-`, `-->`, `=..`,
    /// `\+`, … — is represented).
    fn graphic(&mut self, start: usize) {
        self.eat_while(is_graphic);
        let text = &self.src[start..self.pos];
        if text == "." {
            let at_eof = self.pos >= self.bytes.len();
            let next_is_layout = self.peek().is_whitespace() || self.peek() == '%';
            if at_eof || next_is_layout {
                return self.push(kind::END, start, self.pos, false);
            }
        }
        self.push(kind::ATOM, start, self.pos, false);
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

/// ISO graphic-token characters (the symbol set operators are built from).
pub fn is_graphic(c: char) -> bool {
    matches!(
        c,
        '+' | '-'
            | '*'
            | '/'
            | '\\'
            | '^'
            | '<'
            | '>'
            | '='
            | '~'
            | ':'
            | '.'
            | '?'
            | '@'
            | '#'
            | '&'
            | '$'
    )
}

fn is_ident_continue(c: char) -> bool {
    c == '_' || c.is_alphanumeric()
}

/// A variable starts with `_` or an uppercase letter.
fn is_var_start(c: char) -> bool {
    c == '_' || c.is_uppercase()
}

/// A bare atom starts with a lowercase / caseless letter.
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
            ":- module(lists, [append/3, reverse/2]).\n",
            "append([], L, L).\nappend([H|T], L, [H|R]) :- append(T, L, R).\n",
            "X = 16'FF + 0x1F + 0o17 + 0b1010 + 1_000 + 3.14 + 2.0e-3.\n",
            "fac(0, 1) :- !.\nfac(N, F) :- N > 0, M is N - 1, fac(M, G), F is N * G.\n",
            "greet --> [hello], name.\n",
            "T =.. [F|Args], C = 0'a, S = \"a string\", A = 'quoted atom'.\n",
            "% a line comment\n/* a block\n   comment */\nf.\n",
            "λ('☃ €').  % unicode atom args\n",
            "",
            "p :- \\+ q ; r -> s ; t.\n",
            "main :- format(\"~w~n\", [X]).",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
            assert!(round_trips(src), "not lossless: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("foo(X) :- bar(X).\n");
        assert!(t.contains(&(kind::ATOM, "foo".to_string())));
        assert!(t.contains(&(kind::VAR, "X".to_string())));
        assert!(t.contains(&(kind::ATOM, ":-".to_string())));
        assert!(t.iter().any(|(k, _)| *k == kind::END));
    }

    #[test]
    fn end_token_vs_graphic_and_float_dots() {
        // `=..` is one graphic atom; only the trailing lone `.` is the end token.
        let t = texts("T =.. L.\n");
        assert!(t.contains(&(kind::ATOM, "=..".to_string())));
        assert_eq!(t.iter().filter(|(k, _)| *k == kind::END).count(), 1);
        // A float's interior dot is not an end token.
        let f = texts("X = 3.14.\n");
        assert!(f.contains(&(kind::FLOAT, "3.14".to_string())));
        assert_eq!(f.iter().filter(|(k, _)| *k == kind::END).count(), 1);
        // A `.` glued to a non-layout char is the cons/dict atom, not an end.
        let d = texts(".(a, b).\n");
        assert!(d.contains(&(kind::ATOM, ".".to_string())));
        assert_eq!(d.iter().filter(|(k, _)| *k == kind::END).count(), 1);
    }

    #[test]
    fn numbers() {
        let t = texts("0x1F 0o17 0b1010 1_000 3.14 2.0e-3 0'a 0'\\n 42\n");
        assert!(t.contains(&(kind::INT, "0x1F".to_string())));
        assert!(t.contains(&(kind::INT, "0o17".to_string())));
        assert!(t.contains(&(kind::INT, "0b1010".to_string())));
        assert!(t.contains(&(kind::INT, "1_000".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14".to_string())));
        assert!(t.contains(&(kind::FLOAT, "2.0e-3".to_string())));
        assert!(t.contains(&(kind::INT, "0'a".to_string())));
        assert!(t.contains(&(kind::INT, "0'\\n".to_string())));
    }

    #[test]
    fn variables_atoms_quoted() {
        let t = texts("foo Bar _Baz _ 'a b' \"str\" `bq`\n");
        assert!(t.contains(&(kind::ATOM, "foo".to_string())));
        assert!(t.contains(&(kind::VAR, "Bar".to_string())));
        assert!(t.contains(&(kind::VAR, "_Baz".to_string())));
        assert!(t.contains(&(kind::VAR, "_".to_string())));
        assert!(t.contains(&(kind::ATOM, "'a b'".to_string())));
        assert!(t.contains(&(kind::STRING, "\"str\"".to_string())));
        assert!(t.contains(&(kind::BACKQUOTE, "`bq`".to_string())));
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "S = \"oops\n",
            "A = 'oops\n",
            "/* unterminated block comment\n",
            "λ = '☃'.  % unicode\n",
            "\n\n   \n% trailing\n",
            "€ ¬",
            "0'",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
            assert!(round_trips(src), "not lossless: {src:?}");
        }
    }
}
