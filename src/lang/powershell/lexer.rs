//! Lossless PowerShell lexer, grounded in the PowerShell language token grammar.
//!
//! Guarantees (identical contract to the Rust, Python, and Bash lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs, `#` line comments, `<# #>` block comments, and
//!   backtick line-continuations) are emitted as `trivia` tokens, never dropped.
//!   `NEWLINE` is emitted as a *non-trivia* token because it is structurally
//!   significant in PowerShell (it terminates a statement, like `;`).
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes (an unterminated string runs to end-of-file as one `error` token).
//!   Input is never silently dropped.
//!
//! PowerShell is word/command-oriented and quote-rich. The lexer recognizes every
//! quoting and expansion form as a single covering token: single `'…'`, double
//! `"…"` (with backtick escapes and `""` doubling), and here-strings `@"…"@` /
//! `@'…'@` whose multi-line bodies are consumed up to the line-leading closer.
//! Variables are one token in all their forms: `$x`, `${complex name}`,
//! `$env:PATH`, `$script:foo`, `$_`, `$?`. Cmdlet/command names such as
//! `Get-ChildItem` lex as a single `ident` (an embedded `-` followed by a letter
//! joins), while a leading `-word` (e.g. `-eq`, `-replace`, `-Path`) lexes as an
//! `operator` — the parser/lowering decides operator vs. parameter semantically.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_` as a pragmatic stand-in for the full PowerShell
//! name table — anything outside it still lands in the tree as a covered token,
//! never dropped. PowerShell is case-insensitive, so [`is_keyword`] matches case-
//! insensitively.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// PowerShell reserved words / statement keywords. These lex as `ident` tokens;
/// the parser and lowering distinguish them via [`is_keyword`] (case-insensitive).
pub const KEYWORDS: &[&str] = &[
    "function",
    "filter",
    "workflow",
    "configuration",
    "class",
    "enum",
    "using",
    "if",
    "elseif",
    "else",
    "switch",
    "foreach",
    "for",
    "while",
    "do",
    "until",
    "try",
    "catch",
    "finally",
    "return",
    "throw",
    "break",
    "continue",
    "exit",
    "param",
    "begin",
    "process",
    "end",
    "data",
    "dynamicparam",
    "trap",
    "in",
    "hidden",
    "static",
];

/// Case-insensitive keyword test (PowerShell is case-insensitive).
pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.iter().any(|k| text.eq_ignore_ascii_case(k))
}

/// Token kind labels. Stored on the CST as `&'static str` so the tree stays
/// uniform and JSON-friendly.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const NEWLINE: &str = "newline";
    pub const LINE_COMMENT: &str = "line_comment";
    pub const BLOCK_COMMENT: &str = "block_comment";
    pub const LINE_CONTINUATION: &str = "line_continuation";
    pub const VARIABLE: &str = "variable";
    pub const IDENT: &str = "ident";
    pub const NUMBER: &str = "number";
    pub const STRING: &str = "string_literal";
    pub const OPERATOR: &str = "operator";
    pub const ERROR: &str = "error";
}

/// Multi-character symbolic operators, longest first so the scanner is
/// greedy-correct. Named `-word` operators (`-eq`, `-replace`, …) are handled
/// separately by the dash-word scanner.
const OPERATORS: &[&str] = &[
    "++", "--", "+=", "-=", "*=", "/=", "%=", "::", "..", "&&", "||", ">>", "<<",
];

/// Single-character punctuation/operator characters. `$`, backtick, the quote
/// characters, and the comment introducers are dispatched before this set.
const SINGLE_PUNCT: &str = "+-*/%=!<>|&;:,.()[]{}@?~^";

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
                '\n' | '\r' => self.newline(start),
                c if c.is_whitespace() => {
                    // Newlines were handled above; this run is spaces/tabs/other
                    // non-newline whitespace.
                    self.eat_while(|c| c.is_whitespace() && c != '\n' && c != '\r');
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                '<' if self.peek_at(1) == Some('#') => self.block_comment(start),
                '#' => self.line_comment(start),
                '`' if matches!(self.peek_at(1), Some('\n') | Some('\r')) => {
                    self.line_continuation(start)
                }
                '`' => {
                    // A lone backtick outside a string is an escape character; keep
                    // it (with the char it escapes) as a covered token, not an error.
                    self.bump();
                    if self.pos < self.bytes.len() {
                        self.bump();
                    }
                    self.push(kind::OPERATOR, start, self.pos, false);
                }
                '@' if matches!(self.peek_at(1), Some('"') | Some('\'')) => self.here_string(start),
                '"' => self.double_string(start),
                '\'' => self.single_string(start),
                '$' => self.variable(start),
                c if is_ident_start(c) => self.ident(start),
                c if c.is_ascii_digit() => self.number(start),
                '-' if self
                    .peek_at(1)
                    .map(|c| c.is_ascii_alphabetic())
                    .unwrap_or(false) =>
                {
                    self.dash_word(start)
                }
                c if SINGLE_PUNCT.contains(c) => self.operator(start),
                _ => {
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }
            // Progress guard: every branch above advances `pos`; if some hostile
            // input ever slips past them without moving, consume one byte as an
            // `error` token so the main loop can never spin (non-advancing loop =
            // infinite loop = OOM).
            if self.pos == start {
                self.bump();
                self.push(kind::ERROR, start, self.pos, false);
            }
        }
        self.tokens
    }

    // --- scanners -----------------------------------------------------------

    fn newline(&mut self, start: usize) {
        if self.peek() == '\r' {
            self.bump();
            if self.peek() == '\n' {
                self.bump();
            }
        } else {
            self.bump(); // \n
        }
        self.push(kind::NEWLINE, start, self.pos, false);
    }

    fn line_comment(&mut self, start: usize) {
        let end = self.find_line_end(start);
        self.pos = end;
        self.push(kind::LINE_COMMENT, start, end, true);
    }

    fn block_comment(&mut self, start: usize) {
        self.pos += 2; // <#
        while self.pos < self.bytes.len() {
            if self.src[self.pos..].starts_with("#>") {
                self.pos += 2;
                break;
            }
            self.bump();
        }
        // Unterminated block comment is still trivia covering to EOF — lossless.
        self.push(kind::BLOCK_COMMENT, start, self.pos, true);
    }

    fn line_continuation(&mut self, start: usize) {
        self.bump(); // `
        if self.peek() == '\r' {
            self.bump();
            if self.peek() == '\n' {
                self.bump();
            }
        } else if self.peek() == '\n' {
            self.bump();
        }
        self.push(kind::LINE_CONTINUATION, start, self.pos, true);
    }

    /// Double-quoted string `"…"`. Backtick escapes the next char; a doubled
    /// `""` is an escaped quote. Unterminated → an `error` token to EOF.
    fn double_string(&mut self, start: usize) {
        self.bump(); // opening "
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '`' {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
            } else if c == '"' {
                if self.peek_at(1) == Some('"') {
                    self.bump();
                    self.bump();
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

    /// Single-quoted string `'…'` (literal). A doubled `''` is an escaped quote;
    /// there is no backtick escaping. Unterminated → an `error` token to EOF.
    fn single_string(&mut self, start: usize) {
        self.bump(); // opening '
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            if self.peek() == '\'' {
                if self.peek_at(1) == Some('\'') {
                    self.bump();
                    self.bump();
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

    /// Here-string `@"…"@` or `@'…'@`. The closer is a line-leading `"@` / `'@`,
    /// so the terminator is `\n` + quote + `@`. Unterminated → an `error` token
    /// to EOF. Either way the whole multi-line body stays in one covering token.
    fn here_string(&mut self, start: usize) {
        self.bump(); // @
        let quote = self.peek(); // " or '
        self.bump(); // quote
        let needle = format!("\n{quote}@");
        match self.src[self.pos..].find(&needle) {
            Some(off) => {
                self.pos += off + needle.len();
                self.push(kind::STRING, start, self.pos, false);
            }
            None => {
                self.pos = self.bytes.len();
                self.push(kind::ERROR, start, self.pos, false);
            }
        }
    }

    /// Variable in every form: `$x`, `${complex name}`, `$env:PATH`,
    /// `$script:foo`, `$_`, `$?`, `$$`, `$^`. A bare `$` (e.g. before a `(`
    /// subexpression) is a single-char variable token; the `(` is scanned next.
    fn variable(&mut self, start: usize) {
        self.bump(); // $
        match self.peek() {
            '{' => {
                self.bump(); // {
                while self.pos < self.bytes.len() && self.peek() != '}' {
                    self.bump();
                }
                if self.peek() == '}' {
                    self.bump();
                }
            }
            '?' | '$' | '^' => self.bump(),
            c if is_ident_start(c) || c.is_ascii_digit() => {
                self.eat_while(is_name_char);
                // Scope / drive qualifier: `$env:PATH`, `$script:x`.
                if self.peek() == ':' {
                    self.bump();
                    self.eat_while(is_name_char);
                }
            }
            _ => {} // lone `$`
        }
        self.push(kind::VARIABLE, start, self.pos, false);
    }

    /// Bareword / command name. An embedded `-` followed by an identifier char
    /// joins (so `Get-ChildItem` is one token), matching the Verb-Noun shape of
    /// cmdlet and function names.
    fn ident(&mut self, start: usize) {
        loop {
            let c = self.peek();
            if is_ident_continue(c) {
                self.bump();
            } else if c == '-' && self.peek_at(1).map(is_ident_start).unwrap_or(false) {
                self.bump(); // join the hyphen
            } else {
                break;
            }
        }
        self.push(kind::IDENT, start, self.pos, false);
    }

    fn number(&mut self, start: usize) {
        if self.peek() == '0' && matches!(self.peek_at(1), Some('x') | Some('X')) {
            self.pos += 2;
            self.eat_while(|c| c.is_ascii_hexdigit());
        } else {
            self.eat_while(|c| c.is_ascii_digit());
            if self.peek() == '.' && self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) {
                self.bump(); // .
                self.eat_while(|c| c.is_ascii_digit());
            }
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
                    self.eat_while(|c| c.is_ascii_digit());
                }
            }
        }
        // Numeric multiplier / type suffix (`kb`, `mb`, `gb`, `l`, `d`, …).
        if self.peek().is_ascii_alphabetic() {
            self.eat_while(|c| c.is_ascii_alphanumeric());
        }
        self.push(kind::NUMBER, start, self.pos, false);
    }

    /// A leading `-word`: a named operator (`-eq`, `-replace`, `-match`) or a
    /// command parameter (`-Path`). Lexed uniformly; semantics are decided later.
    fn dash_word(&mut self, start: usize) {
        self.bump(); // -
        self.eat_while(|c| c.is_ascii_alphanumeric());
        self.push(kind::OPERATOR, start, self.pos, false);
    }

    fn operator(&mut self, start: usize) {
        for op in OPERATORS {
            if self.src[self.pos..].starts_with(op) {
                self.pos += op.len();
                return self.push(kind::OPERATOR, start, self.pos, false);
            }
        }
        self.bump();
        self.push(kind::OPERATOR, start, self.pos, false);
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
    c == '_' || c.is_alphanumeric()
}

/// A character allowed inside a `$name` variable body (no scope `:`, which is
/// handled separately).
fn is_name_char(c: char) -> bool {
    c == '_' || c.is_alphanumeric()
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
            "function Get-Thing { param($x) $x }",
            "$env:PATH -eq 'c:\\' -and $script:flag",
            "# comment\n$x = 1mb",
            "<# block\n comment #> Write-Host \"hi `$x ${y} $z\"",
            "@\"\nhere $x\n\"@\n@'\nliteral\n'@",
            "class C : Base { [int]$N; C() {} }",
            "$a.Method() | Where-Object { $_ -gt 0 }",
            "λ ☃ €", // non-ascii idents / unknowns still covered
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn keywords_are_case_insensitive() {
        assert!(is_keyword("function"));
        assert!(is_keyword("Function"));
        assert!(is_keyword("FUNCTION"));
        assert!(is_keyword("Class"));
        assert!(!is_keyword("Get-Thing"));
    }

    #[test]
    fn cmdlet_names_are_single_idents() {
        let t = texts("Get-ChildItem -Path .");
        assert!(t.contains(&(kind::IDENT, "Get-ChildItem".to_string())));
        assert!(t.contains(&(kind::OPERATOR, "-Path".to_string())));
    }

    #[test]
    fn variable_forms() {
        let t = texts("$x ${complex name} $env:PATH $_ $?");
        assert!(t.contains(&(kind::VARIABLE, "$x".to_string())));
        assert!(t.contains(&(kind::VARIABLE, "${complex name}".to_string())));
        assert!(t.contains(&(kind::VARIABLE, "$env:PATH".to_string())));
        assert!(t.contains(&(kind::VARIABLE, "$_".to_string())));
        assert!(t.contains(&(kind::VARIABLE, "$?".to_string())));
    }

    #[test]
    fn here_strings_are_single_tokens() {
        let t = texts("@\"\nline $x\n\"@");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s.starts_with("@\"") && s.ends_with("\"@")));
    }

    #[test]
    fn unterminated_string_is_error_to_eof() {
        let t = texts("\"oops");
        assert_eq!(t, vec![(kind::ERROR, "\"oops".to_string())]);
        assert!(covers_all("\"oops"));
    }
}
