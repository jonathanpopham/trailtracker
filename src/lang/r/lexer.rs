//! Lossless R lexer, grounded in the R language definition's token grammar.
//!
//! Guarantees (identical contract to the Rust, Python and Lua lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs, newlines, `#` line comments) are emitted as `trivia`
//!   tokens, not discarded. R is *not* whitespace-significant in the Python
//!   sense, so a newline is ordinary `newline` trivia; the parser uses it only as
//!   a soft statement-separator heuristic (R terminates a statement at a newline
//!   that is not an obvious expression continuation, exactly like the REPL does).
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped — an unterminated string or raw
//!   string is emitted as an `error` token spanning to end of input.
//!
//! R-specific surface the lexer covers in full:
//! - Both short string forms (`"…"`, `'…'`) with backslash escapes, and the
//!   raw-string forms `r"(…)"`, `R"[…]"`, `r"{…}"`, including dashed fences
//!   `r"---(…)---"` (R 4.0+).
//! - Backtick-quoted names (`` `weird name` ``) — non-syntactic identifiers.
//! - Numeric literals: decimal, hex (`0x1F`), decimal/hex floats with exponents
//!   (`1.5e-3`, `0x1.8p3`), the integer suffix `L` (`10L`) and the imaginary
//!   suffix `i` (`2i`).
//! - The assignment operators `<-`, `<<-`, `->`, `->>`, the namespace operators
//!   `::`/`:::`, the native pipe `|>`, the accessors `$`/`@`, and user infix
//!   operators `%…%` (`%>%`, `%in%`, `%*%`, `%%`, …).
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `.` and `_` as a pragmatic superset of R's identifier
//! rule (a name starts with a letter or `.`, and `.` may appear throughout) —
//! anything outside still lands in the tree as a covered token, never dropped.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// R's reserved words. Like the other lexers, these lex as `name` tokens; the
/// parser and lowering distinguish them via [`is_keyword`].
pub const KEYWORDS: &[&str] = &[
    "if",
    "else",
    "for",
    "while",
    "repeat",
    "function",
    "return",
    "break",
    "next",
    "in",
    "TRUE",
    "FALSE",
    "NULL",
    "NA",
    "Inf",
    "NaN",
    "NA_integer_",
    "NA_real_",
    "NA_character_",
    "NA_complex_",
];

pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.contains(&text)
}

/// Token kind labels. Stored on the CST as `&'static str` so the tree stays
/// uniform and JSON-friendly.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const NEWLINE: &str = "newline";
    pub const COMMENT: &str = "comment";
    pub const NAME: &str = "name";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const COMPLEX: &str = "complex_literal";
    pub const STRING: &str = "string_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
/// `%…%` infix operators are handled separately (variable length).
const OPERATORS: &[&str] = &[
    "<<-", "->>", "<-", "->", ":::", "::", "|>", "==", "!=", "<=", ">=", "&&", "||",
];

/// Single-character punctuation. `%` is handled by [`Lexer::percent_op`], `#` by
/// the comment scanner, and the backtick by [`Lexer::backtick`]; `.` is treated
/// as part of identifiers, never standalone punctuation.
const SINGLE_PUNCT: &str = "+-*/^=<>!&|~?:@$(){}[],;\\";

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
                '#' => self.comment(start),
                '"' | '\'' => self.short_string(start),
                '`' => self.backtick(start),
                'r' | 'R' if self.raw_string_open(self.pos).is_some() => self.raw_string(start),
                '%' => self.percent_op(start),
                c if c.is_ascii_digit() => self.number(start),
                '.' if self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) => {
                    self.number(start)
                }
                c if is_ident_start(c) => self.name(start),
                c if SINGLE_PUNCT.contains(c) => self.punct(start),
                _ => {
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }
            // Progress guard: the dispatch above advances on every path, but if a
            // future edit ever fails to, consume one byte as an error token rather
            // than spin forever (a non-advancing loop is an OOM hazard).
            if self.pos == start {
                self.bump();
                self.push(kind::ERROR, start, self.pos, false);
            }
        }
        self.tokens
    }

    // --- scanners -----------------------------------------------------------

    /// A `#` line comment running to (but not including) the next newline.
    fn comment(&mut self, start: usize) {
        let end = self.find_line_end(self.pos);
        self.pos = end;
        self.push(kind::COMMENT, start, end, true);
    }

    fn name(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        self.push(kind::NAME, start, self.pos, false);
    }

    /// A backtick-quoted name `` `…` `` (non-syntactic identifier). Backslash
    /// escapes are honored; an unterminated backtick name becomes an `error`
    /// token over its bytes.
    fn backtick(&mut self, start: usize) {
        self.bump(); // opening `
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
            if c == '`' {
                self.bump();
                terminated = true;
                break;
            }
            self.bump();
        }
        let token_kind = if terminated { kind::NAME } else { kind::ERROR };
        self.push(token_kind, start, self.pos, false);
    }

    /// A short string `"…"` / `'…'` with backslash escapes. An unterminated
    /// string (hitting end of input) becomes an `error` token over its bytes.
    fn short_string(&mut self, start: usize) {
        let quote = self.peek();
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
        let token_kind = if terminated {
            kind::STRING
        } else {
            kind::ERROR
        };
        self.push(token_kind, start, self.pos, false);
    }

    /// If a valid raw-string opener begins at `at` — `r`/`R`, a quote, zero or
    /// more `-`, then one of `(`/`[`/`{` — return `(quote_char, dash_count,
    /// close_delim_char)`. Otherwise `None` (the `r`/`R` is an ordinary name).
    fn raw_string_open(&self, at: usize) -> Option<(char, usize, char)> {
        let mut it = self.src.get(at..)?.chars();
        match it.next()? {
            'r' | 'R' => {}
            _ => return None,
        }
        let quote = match it.next()? {
            q @ ('"' | '\'') => q,
            _ => return None,
        };
        let mut dashes = 0;
        let open = loop {
            match it.next()? {
                '-' => dashes += 1,
                c @ ('(' | '[' | '{') => break c,
                _ => return None,
            }
        };
        let close = match open {
            '(' => ')',
            '[' => ']',
            _ => '}',
        };
        Some((quote, dashes, close))
    }

    /// Scan a raw string `r"(…)"` / `R"---[…]---"` …, opener confirmed by
    /// [`raw_string_open`]. Terminates at the matching `close` `-`{dashes}
    /// `quote`; if none is found the run reaches end of input and is reported as
    /// an `error` token (still fully covered).
    fn raw_string(&mut self, start: usize) {
        let (quote, dashes, close) = match self.raw_string_open(self.pos) {
            Some(info) => info,
            None => {
                // Defensive: should not happen (dispatch guards it). Stay lossless.
                self.bump();
                self.push(kind::ERROR, start, self.pos, false);
                return;
            }
        };
        // Consume `r`/`R`, the quote, the dashes, and the opening delimiter.
        self.bump(); // r / R
        self.bump(); // quote
        for _ in 0..dashes {
            self.bump(); // -
        }
        self.bump(); // open delimiter
        let mut closing = String::new();
        closing.push(close);
        for _ in 0..dashes {
            closing.push('-');
        }
        closing.push(quote);
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            if self.src[self.pos..].starts_with(&closing) {
                self.pos += closing.len();
                terminated = true;
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

    /// A user infix operator `%…%` (`%>%`, `%in%`, `%%`, …). Scans from the
    /// opening `%` to the next `%` provided no whitespace intervenes; a lone `%`
    /// with no contiguous closing `%` is emitted as a single-char punct.
    fn percent_op(&mut self, start: usize) {
        let mut idx = self.pos + 1;
        let mut end = None;
        if let Some(rest) = self.src.get(self.pos + 1..) {
            for ch in rest.chars() {
                if ch == '%' {
                    end = Some(idx + ch.len_utf8());
                    break;
                }
                if ch.is_whitespace() {
                    break;
                }
                idx += ch.len_utf8();
            }
        }
        match end {
            Some(e) => {
                self.pos = e;
                self.push(kind::PUNCT, start, self.pos, false);
            }
            None => {
                self.bump(); // lone %
                self.push(kind::PUNCT, start, self.pos, false);
            }
        }
    }

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        let mut is_complex = false;
        if self.peek() == '0' && matches!(self.peek_at(1), Some('x') | Some('X')) {
            self.pos += 2;
            self.eat_while(|c| c.is_ascii_hexdigit());
            if self.peek() == '.' {
                is_float = true;
                self.bump();
                self.eat_while(|c| c.is_ascii_hexdigit());
            }
            if matches!(self.peek(), 'p' | 'P') {
                is_float = true;
                self.bump();
                if matches!(self.peek(), '+' | '-') {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit());
            }
        } else {
            self.eat_while(|c| c.is_ascii_digit());
            if self.peek() == '.' {
                is_float = true;
                self.bump();
                self.eat_while(|c| c.is_ascii_digit());
            }
            if matches!(self.peek(), 'e' | 'E') {
                is_float = true;
                self.bump();
                if matches!(self.peek(), '+' | '-') {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit());
            }
        }
        // Suffix: `L` (integer) or `i` (imaginary/complex).
        match self.peek() {
            'L' => self.bump(),
            'i' => {
                self.bump();
                is_complex = true;
            }
            _ => {}
        }
        let k = if is_complex {
            kind::COMPLEX
        } else if is_float {
            kind::FLOAT
        } else {
            kind::INT
        };
        self.push(k, start, self.pos, false);
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
    c == '_' || c == '.' || c.is_alphabetic()
}

fn is_ident_continue(c: char) -> bool {
    c == '_' || c == '.' || c.is_alphanumeric()
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
            "f <- function(x) x + 1\n",
            "# a comment\nx <- 1L\n",
            "df$col[[1]] <- 2\n",
            "y <- data %>% filter(a > 1) %>% select(b)\n",
            "s <- r\"(raw \\ \"string\")\"\n",
            "z <- R\"---[a)b]---\"\n",
            "n <- 0xFF + 0x1.8p3 + 1.5e-3 + 3L + 2i\n",
            "`weird name` <- 1\n",
            "a %in% b; c %*% d\n",
            "x |> f() -> y\n",
            "v <<- 1\n",
            "λ <- '☃ €'  # unicode\n",
            "",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("add <- function(a, b) a + b\n");
        assert!(t.contains(&(kind::NAME, "add".to_string())));
        assert!(t.contains(&(kind::PUNCT, "<-".to_string())));
        assert!(t.contains(&(kind::NAME, "function".to_string())));
        assert!(is_keyword("function"));
        assert!(!is_keyword("add"));
    }

    #[test]
    fn assignment_and_namespace_operators() {
        let t = texts("a <- b <<- c -> d ->> e; pkg::fn; pkg:::priv; x |> y");
        for op in ["<-", "<<-", "->", "->>", "::", ":::", "|>"] {
            assert!(
                t.contains(&(kind::PUNCT, op.to_string())),
                "missing operator {op}"
            );
        }
    }

    #[test]
    fn percent_operators_and_lone_percent() {
        let t = texts("a %>% b %in% c %% d");
        for op in ["%>%", "%in%", "%%"] {
            assert!(
                t.contains(&(kind::PUNCT, op.to_string())),
                "missing infix {op}"
            );
        }
        // A `%` followed by whitespace with no contiguous closing `%` is a lone
        // punct, not a runaway token.
        let t2 = texts("50 % off");
        assert!(t2.contains(&(kind::PUNCT, "%".to_string())));
    }

    #[test]
    fn numbers() {
        let t = texts("0xFF 10L 3.14 1.5e-3 .5 2i 0x1.8p3");
        assert!(t.contains(&(kind::INT, "0xFF".to_string())));
        assert!(t.contains(&(kind::INT, "10L".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14".to_string())));
        assert!(t.contains(&(kind::FLOAT, "1.5e-3".to_string())));
        assert!(t.contains(&(kind::FLOAT, ".5".to_string())));
        assert!(t.contains(&(kind::COMPLEX, "2i".to_string())));
        assert!(t.contains(&(kind::FLOAT, "0x1.8p3".to_string())));
    }

    #[test]
    fn raw_strings_with_dashes_and_brackets() {
        let t = texts("r\"(a\"b)\" R\"---[x)y]---\" r\"{z}\"");
        assert!(t.contains(&(kind::STRING, "r\"(a\"b)\"".to_string())));
        assert!(t.contains(&(kind::STRING, "R\"---[x)y]---\"".to_string())));
        assert!(t.contains(&(kind::STRING, "r\"{z}\"".to_string())));
    }

    #[test]
    fn backtick_names() {
        let t = texts("`a b` <- 1");
        assert!(t.contains(&(kind::NAME, "`a b`".to_string())));
    }

    #[test]
    fn dotted_identifier_is_one_name() {
        let t = texts("as.numeric(x)");
        assert!(t.contains(&(kind::NAME, "as.numeric".to_string())));
    }

    #[test]
    fn unterminated_string_is_error_but_covered() {
        let t = texts("x <- 'open\n");
        assert!(t.iter().any(|(k, _)| *k == kind::ERROR));
        assert!(covers_all("x <- 'open\n"));
    }
}
