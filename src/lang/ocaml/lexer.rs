//! Lossless OCaml lexer, grounded in the OCaml manual's lexical conventions.
//!
//! Guarantees (identical contract to the Rust/Haskell/Go/Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs, `(* nested *)` block comments) are emitted as `trivia`
//!   tokens, never discarded. `newline` is emitted as a *non-trivia* token: the
//!   parser uses a token's byte-column (column 0 = start of a top-level item) as a
//!   pragmatic stand-in for OCaml's real grammar — we do **not** build a full
//!   parser, but it is enough to carve top-level items losslessly.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//!
//! Progress guarantee: every scanner advances `pos` on every path, and the main
//! loop carries an explicit guard — if a turn fails to advance, one byte is
//! consumed as an `error` token. A non-advancing branch would mean an infinite
//! loop, so this is load-bearing.
//!
//! OCaml-specific lexical points handled here (honest, breadth gaps not lies):
//! - `(* ... *)` comments **nest** (like Rust `/* */`), and OCaml additionally
//!   recognises string / quoted-string literals *inside* comments so that a `*)`
//!   buried in a string does not close the comment early — both are honored.
//! - `"..."` strings with `\` escapes, and `{id|...|id}` quoted (raw) strings with
//!   an arbitrary lowercase delimiter `id` (the common case is `{|...|}`).
//! - Character literals `'c'`, `'\n'`, `'\\'`, `'\123'`, `'\xFF'`, disambiguated
//!   from a type variable `'a` (a quote followed by an identifier with no closing
//!   `'`): the quote then lexes as `punct` and the identifier separately.
//! - Operator runs over the OCaml symbol set, so `->`, `|>`, `::`, `:=`, `>>=`
//!   stay single tokens. `;;` is lexed as one `punct` token (a structure item
//!   terminator); a single `;` is its own `punct`.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// OCaml reserved identifiers. These lex as `varid`/`conid` tokens; the parser
/// distinguishes them via [`is_keyword`]. (`lor`, `lxor`, `lsl`, … are infix
/// keyword-operators in OCaml but are not load-bearing for item carving, so they
/// are deliberately omitted here.)
pub const KEYWORDS: &[&str] = &[
    "and",
    "as",
    "assert",
    "begin",
    "class",
    "constraint",
    "do",
    "done",
    "downto",
    "else",
    "end",
    "exception",
    "external",
    "false",
    "for",
    "fun",
    "function",
    "functor",
    "if",
    "in",
    "include",
    "inherit",
    "initializer",
    "lazy",
    "let",
    "match",
    "method",
    "module",
    "mutable",
    "new",
    "nonrec",
    "object",
    "of",
    "open",
    "or",
    "private",
    "rec",
    "sig",
    "struct",
    "then",
    "to",
    "true",
    "try",
    "type",
    "val",
    "virtual",
    "when",
    "while",
    "with",
];

pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.contains(&text)
}

/// Token kind labels. Stored on the CST as `&'static str`.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const NEWLINE: &str = "newline";
    pub const BLOCK_COMMENT: &str = "block_comment";
    /// Variable / value identifier (lowercase- or underscore-initial); also the
    /// surface form of keywords.
    pub const VARID: &str = "varid";
    /// Constructor / module identifier (uppercase-initial).
    pub const CONID: &str = "conid";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const CHAR: &str = "char_literal";
    pub const STRING: &str = "string_literal";
    /// A `{id|...|id}` quoted (raw) string literal.
    pub const QUOTED_STRING: &str = "quoted_string";
    /// A maximal run of OCaml symbol characters (an operator, including reserved
    /// ops like `->`, `::`, `:=`, `|`, `|>`, `..`, `*`, `+`).
    pub const OPERATOR: &str = "operator";
    /// A single special character: `( ) [ ] { } , ` (backtick) or the `'`/`#`
    /// quote/sharp; or the `;` / `;;` item separators.
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// The OCaml operator-character set (manual §"Prefix and infix symbols").
fn is_symbol(c: char) -> bool {
    matches!(
        c,
        '!' | '$'
            | '%'
            | '&'
            | '*'
            | '+'
            | '-'
            | '.'
            | '/'
            | ':'
            | '<'
            | '='
            | '>'
            | '?'
            | '@'
            | '^'
            | '|'
            | '~'
            | '#'
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
                '(' if self.peek_at(1) == Some('*') => self.block_comment(start),
                '"' => self.string_literal(start),
                '{' if self.quoted_string_delim().is_some() => self.quoted_string(start),
                '\'' => self.quote_or_char(start),
                ';' => {
                    // `;;` is one token (structure item terminator); a lone `;`
                    // is its own punctuation.
                    self.bump();
                    if self.peek() == ';' {
                        self.bump();
                    }
                    self.push(kind::PUNCT, start, self.pos, false);
                }
                c if is_ident_start(c) => self.ident(start),
                c if c.is_ascii_digit() => self.number(start),
                c if is_symbol(c) => {
                    self.eat_while(is_symbol);
                    self.push(kind::OPERATOR, start, self.pos, false);
                }
                '(' | ')' | '[' | ']' | '{' | '}' | ',' | '`' => {
                    self.bump();
                    self.push(kind::PUNCT, start, self.pos, false);
                }
                _ => {
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }

            // Progress guard: a turn that consumed nothing would spin forever, so
            // force one byte as an error token.
            if self.pos == start {
                self.bump();
                self.push(kind::ERROR, start, self.pos, false);
            }
        }
        self.tokens
    }

    // --- scanners -----------------------------------------------------------

    /// Nested block comment `(* ... *)`. OCaml comments nest, and string /
    /// quoted-string literals inside a comment are skipped so that a `*)` buried
    /// in a string does not close the comment prematurely. Unterminated comments
    /// still cover to EOF (lossless, still trivia).
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
            } else if self.peek() == '"' {
                self.skip_string_in_comment();
            } else if self.peek() == '{' && self.quoted_string_delim().is_some() {
                self.skip_quoted_string_in_comment();
            } else {
                self.bump();
            }
        }
        self.push(kind::BLOCK_COMMENT, start, self.pos, true);
    }

    /// Skip a `"..."` literal while scanning inside a comment (no token emitted;
    /// the whole comment is one trivia token).
    fn skip_string_in_comment(&mut self) {
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
            } else {
                self.bump();
            }
        }
    }

    /// Skip a `{id|...|id}` literal while scanning inside a comment.
    fn skip_quoted_string_in_comment(&mut self) {
        if let Some(delim) = self.quoted_string_delim() {
            let closer = format!("|{delim}}}");
            self.pos += 2 + delim.len(); // {id|
            match self.src[self.pos..].find(&closer) {
                Some(off) => self.pos += off + closer.len(),
                None => self.pos = self.bytes.len(),
            }
        } else {
            self.bump();
        }
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

    /// Interpreted string `"..."`: a backslash escapes the following byte; an
    /// unterminated literal (EOF before the closing quote) is recorded as `error`.
    /// OCaml strings may span newlines, so a raw `\n` does not end them.
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

    /// If the cursor is at the start of a quoted string `{id|`, return the
    /// delimiter `id` (possibly empty for `{|`). Only `[a-z_]` are valid delimiter
    /// characters; otherwise this is an ordinary `{` brace.
    fn quoted_string_delim(&self) -> Option<String> {
        if self.peek() != '{' {
            return None;
        }
        let rest = &self.src[self.pos + 1..];
        let mut delim = String::new();
        for ch in rest.chars() {
            if ch == '|' {
                return Some(delim);
            }
            if ch.is_ascii_lowercase() || ch == '_' {
                delim.push(ch);
            } else {
                return None;
            }
        }
        None
    }

    /// Quoted (raw) string `{id|...|id}`. Content is verbatim until the matching
    /// `|id}`. Unterminated runs to EOF (still lossless).
    fn quoted_string(&mut self, start: usize) {
        let delim = self
            .quoted_string_delim()
            .expect("quoted_string called without a valid delimiter");
        let closer = format!("|{delim}}}");
        self.pos += 2 + delim.len(); // {id|
        let mut terminated = false;
        match self.src[self.pos..].find(&closer) {
            Some(off) => {
                self.pos += off + closer.len();
                terminated = true;
            }
            None => self.pos = self.bytes.len(),
        }
        let k = if terminated {
            kind::QUOTED_STRING
        } else {
            kind::ERROR
        };
        self.push(k, start, self.pos, false);
    }

    /// A `'` begins either a character literal (`'c'`, `'\n'`, `'\123'`) or — when
    /// it is followed by an identifier that is *not* closed by a second `'` — a
    /// type-variable tick (`'a`). In the latter case the `'` is emitted as a lone
    /// `punct` and the identifier lexes on the next turn.
    fn quote_or_char(&mut self, start: usize) {
        let c1 = self.peek_at(1);
        if c1 == Some('\\') {
            // Escape sequence: '\n', '\\', '\123', '\xFF', '\o377', '\u{...}'.
            self.bump(); // '
            self.bump(); // backslash
                         // Consume escape body up to and including the closing quote.
            let mut terminated = false;
            while self.pos < self.bytes.len() {
                let c = self.peek();
                if c == '\'' {
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
            return;
        }
        // A plain char literal is exactly `'<one char>'`.
        if c1.is_some() && self.peek_at(2) == Some('\'') {
            self.bump(); // '
            self.bump(); // the char
            self.bump(); // closing '
            self.push(kind::CHAR, start, self.pos, false);
            return;
        }
        // Otherwise treat the quote as punctuation (type variable / label tick).
        self.bump();
        self.push(kind::PUNCT, start, self.pos, false);
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
            // or a record-field `.` is never swallowed.
            if self.peek() == '.' && self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) {
                is_float = true;
                self.bump(); // .
                self.eat_while(|c| c.is_ascii_digit() || c == '_');
            } else if self.peek() == '.'
                && !self.peek_at(1).map(is_symbol).unwrap_or(false)
                && self.peek_at(1) != Some('.')
            {
                // Trailing-dot float like `1.` (but not `1..2` or `1.+`).
                is_float = true;
                self.bump();
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
        // Optional integer width suffix `l` / `L` / `n` (int32 / int64 / nativeint),
        // but only when it is not the first char of a longer identifier (so
        // `3 land 4` written `3land` is not misread — and `land`/`lsl` stay words).
        if !is_float
            && matches!(self.peek(), 'l' | 'L' | 'n')
            && !self.peek_at(1).map(is_ident_continue).unwrap_or(false)
        {
            self.bump();
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
            "let () = print_string \"hi\"\n",
            "(* a comment *) let x = 1\n",
            "(* nested (* block *) comment *) let y = 2\n",
            "let f x = x + 1\n",
            "let pipe x = x |> g |> h\n",
            "type 'a tree = Leaf | Node of 'a tree * 'a tree\n",
            "let c = 'a'\nlet c2 = '\\n'\nlet s = \"str\\\"end\"\n",
            "let raw = {|verbatim |} and r2 = {ml|a|ml}\n",
            "let prime' = x'' in prime'\n",
            "module M = struct let z = 0 end\n",
            "let r = obj#meth and a = arr.(0)\n",
            "λ = \"☃ €\" (* unicode *)\n",
            "",
            "\n\n   \n(* trailing *)\n",
            "x ;; y ;;\n",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("let add x y = x + y");
        assert!(t.contains(&(kind::VARID, "let".to_string())));
        assert!(t.contains(&(kind::VARID, "add".to_string())));
        assert!(t.contains(&(kind::OPERATOR, "=".to_string())));
        assert!(t.contains(&(kind::OPERATOR, "+".to_string())));
        assert!(is_keyword("let"));
        assert!(is_keyword("struct"));
        assert!(!is_keyword("add"));
    }

    #[test]
    fn conid_vs_varid() {
        let t = texts("Some x");
        assert!(t.contains(&(kind::CONID, "Some".to_string())));
        assert!(t.contains(&(kind::VARID, "x".to_string())));
    }

    #[test]
    fn reserved_operators_are_single_tokens() {
        let t = texts("a -> b :: c := d |> e .. f");
        for op in ["->", "::", ":=", "|>", ".."] {
            assert!(
                t.contains(&(kind::OPERATOR, op.to_string())),
                "missing operator {op}"
            );
        }
    }

    #[test]
    fn char_vs_type_variable() {
        // A char literal.
        let t = texts("'a'");
        assert!(t.contains(&(kind::CHAR, "'a'".to_string())));
        // A type variable: the quote is punct, the ident lexes separately.
        let t2 = texts("'a list");
        assert!(t2.contains(&(kind::PUNCT, "'".to_string())));
        assert!(t2.contains(&(kind::VARID, "a".to_string())));
        // An escaped char.
        let t3 = texts("'\\n'");
        assert!(t3.contains(&(kind::CHAR, "'\\n'".to_string())));
    }

    #[test]
    fn double_semicolon_is_one_token() {
        let t = texts("x ;; y");
        assert!(t.contains(&(kind::PUNCT, ";;".to_string())));
        let t2 = texts("a ; b");
        assert!(t2.contains(&(kind::PUNCT, ";".to_string())));
        assert!(t2.iter().all(|(_, s)| s != ";;"));
    }

    #[test]
    fn quoted_string_with_delimiter() {
        let t = texts("{ml|a |} b|ml}");
        assert!(t.contains(&(kind::QUOTED_STRING, "{ml|a |} b|ml}".to_string())));
    }

    #[test]
    fn nested_block_comment() {
        let t = texts("(* a (* b *) c *)");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::BLOCK_COMMENT && s == "(* a (* b *) c *)"));
    }

    #[test]
    fn comment_with_unbalanced_string() {
        // The `*)` inside the string must not close the comment early.
        let t = texts("(* \"*)\" still in comment *) let x = 1");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::BLOCK_COMMENT && s == "(* \"*)\" still in comment *)"));
        assert!(t.contains(&(kind::VARID, "let".to_string())));
    }
}
