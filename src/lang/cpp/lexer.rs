//! Lossless C++ lexer, grounded in the ISO C++ lexical grammar.
//!
//! Guarantees (identical contract to the Rust and Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (whitespace, comments) are emitted as `trivia` tokens, never dropped.
//!   Preprocessor directives are emitted as a single **non-trivia** `preprocessor`
//!   token (they carry `#include`/`#define` facts the lowering needs), spanning a
//!   full logical line including backslash-newline continuations.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_` as a pragmatic stand-in for the full Unicode
//! identifier tables (C++ also permits universal-character-name escapes in
//! identifiers, which we do not special-case). Anything outside still lands in
//! the tree as a covered token, never dropped.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// C++ keywords (through C++23, including common context-sensitive ones). Like the
/// other front ends these lex as `ident` tokens; the parser distinguishes them via
/// [`is_keyword`].
pub const KEYWORDS: &[&str] = &[
    "alignas",
    "alignof",
    "and",
    "and_eq",
    "asm",
    "auto",
    "bitand",
    "bitor",
    "bool",
    "break",
    "case",
    "catch",
    "char",
    "char8_t",
    "char16_t",
    "char32_t",
    "class",
    "compl",
    "concept",
    "const",
    "consteval",
    "constexpr",
    "constinit",
    "const_cast",
    "continue",
    "co_await",
    "co_return",
    "co_yield",
    "decltype",
    "default",
    "delete",
    "do",
    "double",
    "dynamic_cast",
    "else",
    "enum",
    "explicit",
    "export",
    "extern",
    "false",
    "float",
    "for",
    "friend",
    "goto",
    "if",
    "inline",
    "int",
    "long",
    "mutable",
    "namespace",
    "new",
    "noexcept",
    "not",
    "not_eq",
    "nullptr",
    "operator",
    "or",
    "or_eq",
    "override",
    "private",
    "protected",
    "public",
    "register",
    "reinterpret_cast",
    "requires",
    "return",
    "short",
    "signed",
    "sizeof",
    "static",
    "static_assert",
    "static_cast",
    "struct",
    "switch",
    "template",
    "this",
    "thread_local",
    "throw",
    "true",
    "try",
    "typedef",
    "typeid",
    "typename",
    "union",
    "unsigned",
    "using",
    "virtual",
    "void",
    "volatile",
    "wchar_t",
    "while",
    "xor",
    "xor_eq",
    "final",
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
    /// A whole preprocessor directive line (`#include`, `#define`, …), captured
    /// verbatim including any backslash-newline continuations. Non-trivia.
    pub const PREPROCESSOR: &str = "preprocessor";
    pub const IDENT: &str = "ident";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const CHAR: &str = "char_literal";
    pub const STRING: &str = "string_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
const OPERATORS: &[&str] = &[
    "<<=", ">>=", "->*", "...", "<=>", "::", "->", "++", "--", "<<", ">>", "<=", ">=", "==", "!=",
    "&&", "||", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", ".*", "##",
];

const SINGLE_PUNCT: &str = "+-*/%!&|^~<>=.,;:()[]{}?#";

/// The literal form a leading prefix introduces.
enum LitForm {
    /// `R"delim(...)delim"`, `LR"..."`, `u8R"..."`, …
    RawString,
    /// `L"..."`, `u8"..."`, `u"..."`, `U"..."`.
    String,
    /// `L'...'`, `u'...'`, `U'...'`, `u8'...'`.
    Char,
}

pub fn lex(source: &str) -> Vec<Token> {
    Lexer::new(source).run()
}

struct Lexer<'s> {
    src: &'s str,
    bytes: &'s [u8],
    pos: usize,
    tokens: Vec<Token>,
    /// True when the cursor is at the start of a line (only horizontal whitespace
    /// seen since the last newline). Gates preprocessor-directive recognition.
    at_line_start: bool,
}

impl<'s> Lexer<'s> {
    fn new(src: &'s str) -> Self {
        Lexer {
            src,
            bytes: src.as_bytes(),
            pos: 0,
            tokens: Vec::new(),
            at_line_start: true,
        }
    }

    fn run(mut self) -> Vec<Token> {
        while self.pos < self.bytes.len() {
            let start = self.pos;
            let c = self.peek();
            // Default: any emitted token leaves us mid-line. Only a whitespace run
            // containing a newline restores line-start state.
            let mut line_start_after = false;
            match c {
                c if c.is_whitespace() => {
                    self.eat_while(|c| c.is_whitespace());
                    let slice = &self.src[start..self.pos];
                    line_start_after = self.at_line_start || slice.contains('\n');
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                '#' if self.at_line_start => self.preprocessor(start),
                '/' if self.peek_at(1) == Some('/') => self.line_comment(start),
                '/' if self.peek_at(1) == Some('*') => self.block_comment(start),
                '"' => self.string_body(start, '"', kind::STRING),
                '\'' => self.string_body(start, '\'', kind::CHAR),
                c if is_ident_start(c) => {
                    if let Some((plen, form)) = self.literal_prefix(start) {
                        self.pos += plen;
                        match form {
                            LitForm::RawString => self.raw_string(start),
                            LitForm::String => self.string_body(start, '"', kind::STRING),
                            LitForm::Char => self.string_body(start, '\'', kind::CHAR),
                        }
                    } else {
                        self.ident(start);
                    }
                }
                c if c.is_ascii_digit() => self.number(start),
                '.' if self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) => {
                    self.number(start)
                }
                c if SINGLE_PUNCT.contains(c) => self.punct(start),
                _ => {
                    // Unknown byte/char — preserve it as an explicit error token.
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }
            self.at_line_start = line_start_after;
        }
        self.tokens
    }

    // --- scanners -----------------------------------------------------------

    /// A preprocessor directive line: from `#` to the end of the logical line,
    /// honoring backslash-newline continuations so a multi-line `#define` stays a
    /// single token. The terminating newline itself is left for the whitespace
    /// scanner (so line-start tracking resumes cleanly).
    fn preprocessor(&mut self, start: usize) {
        self.bump(); // #
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '\\' {
                // Backslash-newline (optionally CRLF) continues the directive.
                match self.peek_at(1) {
                    Some('\n') => {
                        self.bump(); // backslash
                        self.bump(); // \n
                    }
                    Some('\r') => {
                        self.bump(); // backslash
                        self.bump(); // \r
                        if self.peek() == '\n' {
                            self.bump();
                        }
                    }
                    _ => self.bump(),
                }
                continue;
            }
            if c == '\n' || c == '\r' {
                break;
            }
            self.bump();
        }
        self.push(kind::PREPROCESSOR, start, self.pos, false);
    }

    fn line_comment(&mut self, start: usize) {
        let end = self.find_line_end(start);
        self.pos = end;
        self.push(kind::LINE_COMMENT, start, end, true);
    }

    fn block_comment(&mut self, start: usize) {
        // C++ block comments do NOT nest: the first `*/` closes the comment.
        self.pos += 2; // /*
        while self.pos < self.bytes.len() {
            if self.src[self.pos..].starts_with("*/") {
                self.pos += 2;
                break;
            }
            self.bump();
        }
        // An unterminated block comment is still trivia covering to EOF — lossless.
        self.push(kind::BLOCK_COMMENT, start, self.pos, true);
    }

    fn ident(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        self.push(kind::IDENT, start, self.pos, false);
    }

    /// Detect a string/char literal prefix at `start` and classify it. Returns the
    /// prefix byte length and the literal form, or `None` for an ordinary
    /// identifier. Order matters: longer/raw prefixes are tested first.
    fn literal_prefix(&self, start: usize) -> Option<(usize, LitForm)> {
        let rest = &self.src[start..];
        // Raw-string prefixes (must be followed by an opening quote).
        for p in ["u8R", "LR", "uR", "UR", "R"] {
            if rest.starts_with(p) && rest[p.len()..].starts_with('"') {
                return Some((p.len(), LitForm::RawString));
            }
        }
        // Encoded (non-raw) string prefixes.
        for p in ["u8", "u", "U", "L"] {
            if rest.starts_with(p) && rest[p.len()..].starts_with('"') {
                return Some((p.len(), LitForm::String));
            }
        }
        // Character-literal prefixes.
        for p in ["u8", "u", "U", "L"] {
            if rest.starts_with(p) && rest[p.len()..].starts_with('\'') {
                return Some((p.len(), LitForm::Char));
            }
        }
        None
    }

    /// Scan a `"..."` or `'...'` literal body. The cursor is at the opening quote
    /// (any prefix already consumed). Handles backslash escapes; an unterminated
    /// literal (closed by EOF or a bare newline) becomes an `error` token.
    fn string_body(&mut self, start: usize, quote: char, lit_kind: &'static str) {
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
                break; // unterminated single-line literal
            } else {
                self.bump();
            }
        }
        if terminated {
            self.eat_suffix(); // user-defined-literal suffix (`"s"sv`, `'a'_x`)
        }
        let token_kind = if terminated { lit_kind } else { kind::ERROR };
        self.push(token_kind, start, self.pos, false);
    }

    /// Scan a raw string `R"delim(...)delim"`. The cursor is at the opening `"`
    /// (the `R`/`LR`/`u8R`/… prefix already consumed).
    fn raw_string(&mut self, start: usize) {
        self.bump(); // opening "
        let delim_start = self.pos;
        // The delimiter runs up to the first `(`; it may not contain `(`, `)`,
        // whitespace, or a backslash. A malformed opener becomes an error token.
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '(' {
                break;
            }
            if c == ')' || c == '\\' || c == '"' || c.is_whitespace() {
                self.push(kind::ERROR, start, self.pos, false);
                return;
            }
            self.bump();
        }
        if self.pos >= self.bytes.len() {
            self.push(kind::ERROR, start, self.pos, false);
            return;
        }
        let delim = self.src[delim_start..self.pos].to_string();
        self.bump(); // (
        let closing = format!("){delim}\"");
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            if self.src[self.pos..].starts_with(&closing) {
                self.pos += closing.len();
                terminated = true;
                break;
            }
            self.bump();
        }
        if terminated {
            self.eat_suffix();
        }
        let token_kind = if terminated {
            kind::STRING
        } else {
            kind::ERROR
        };
        self.push(token_kind, start, self.pos, false);
    }

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        if self.peek() == '0' {
            match self.peek_at(1) {
                Some('x') | Some('X') => {
                    self.pos += 2;
                    self.eat_digit_run(|c| c.is_ascii_hexdigit());
                    // Hex float: `0x1.8p3`.
                    if self.peek() == '.' {
                        is_float = true;
                        self.bump();
                        self.eat_digit_run(|c| c.is_ascii_hexdigit());
                    }
                    if matches!(self.peek(), 'p' | 'P') {
                        is_float = true;
                        self.eat_exponent();
                    }
                    self.eat_suffix();
                    let k = if is_float { kind::FLOAT } else { kind::INT };
                    return self.push(k, start, self.pos, false);
                }
                Some('b') | Some('B') => {
                    self.pos += 2;
                    self.eat_digit_run(|c| c == '0' || c == '1');
                    self.eat_suffix();
                    return self.push(kind::INT, start, self.pos, false);
                }
                _ => {}
            }
        }
        // Decimal / octal integer part.
        self.eat_digit_run(|c| c.is_ascii_digit());
        if self.peek() == '.' {
            is_float = true;
            self.bump(); // .
            self.eat_digit_run(|c| c.is_ascii_digit());
        }
        if matches!(self.peek(), 'e' | 'E') {
            // Only an exponent if a digit (optionally signed) follows.
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
                self.eat_exponent();
            }
        }
        self.eat_suffix();
        let k = if is_float { kind::FLOAT } else { kind::INT };
        self.push(k, start, self.pos, false);
    }

    /// Consume an exponent marker (`e`/`E`/`p`/`P`), an optional sign, and the
    /// exponent digits. The marker is assumed present at the cursor.
    fn eat_exponent(&mut self) {
        self.bump(); // e/E/p/P
        if matches!(self.peek(), '+' | '-') {
            self.bump();
        }
        self.eat_digit_run(|c| c.is_ascii_digit());
    }

    /// Numeric suffix: an identifier-continue run (`u`, `ll`, `f`, or a
    /// user-defined-literal suffix such as `_km`). A trailing `.` is never part of
    /// the suffix.
    fn eat_suffix(&mut self) {
        if is_ident_start(self.peek()) {
            self.eat_while(is_ident_continue);
        }
    }

    /// Eat a run of digits accepted by `pred`, allowing `'` digit separators that
    /// sit between two accepted digits (C++14 `1'000'000`).
    fn eat_digit_run(&mut self, pred: impl Fn(char) -> bool) {
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if pred(c) {
                self.bump();
            } else if c == '\'' && self.peek_at(1).map(&pred).unwrap_or(false) {
                self.bump(); // the separator; the next digit is eaten next iteration
            } else {
                break;
            }
        }
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

fn is_ident_continue(c: char) -> bool {
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
            "int main() { return 0; }\n",
            "#include <vector>\n#include \"foo.h\"\n",
            "// line\n/* block */ int x = 0xFF'00u;\n",
            "auto s = R\"(raw \"quoted\" text)\";\n",
            "auto t = LR\"delim(a)delim\" U\"u\" u8\"b\" L'x';\n",
            "double d = 1.5e-3 + 0x1.8p3 + 3'000.0f;\n",
            "a <=> b; x->*y; p.*q; ns::fn();\n",
            "auto λ = U'☃'; // unicode\n",
            "#define M(a, b) ((a) + \\\n  (b))\n",
            "template<class T> struct S { T v; };\n",
            "",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("int add(int a, int b) { return a + b; }");
        assert!(t.contains(&(kind::IDENT, "int".to_string())));
        assert!(t.contains(&(kind::IDENT, "add".to_string())));
        assert!(t.contains(&(kind::PUNCT, "(".to_string())));
        assert!(is_keyword("class"));
        assert!(is_keyword("namespace"));
        assert!(!is_keyword("add"));
    }

    #[test]
    fn preprocessor_is_one_token() {
        let t = texts("#include <vector>\n");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::PREPROCESSOR && s == "#include <vector>"));
    }

    #[test]
    fn preprocessor_continuation_joins_lines() {
        let toks = lex("#define X 1 \\\n  + 2\nint y;\n");
        let pp: Vec<&str> = toks
            .iter()
            .filter(|t| t.kind == kind::PREPROCESSOR)
            .map(|t| t.span.text("#define X 1 \\\n  + 2\nint y;\n"))
            .collect();
        assert_eq!(pp, vec!["#define X 1 \\\n  + 2"]);
    }

    #[test]
    fn hash_midline_is_punct_not_directive() {
        let t = texts("a # b");
        assert!(t.contains(&(kind::PUNCT, "#".to_string())));
        assert!(t.iter().all(|(k, _)| *k != kind::PREPROCESSOR));
    }

    #[test]
    fn raw_string_with_delimiter() {
        let t = texts("R\"x(a)b)x\"");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "R\"x(a)b)x\""));
    }

    #[test]
    fn spaceship_and_member_ptr_operators() {
        let t = texts("a <=> b .* c ->* d");
        assert!(t.contains(&(kind::PUNCT, "<=>".to_string())));
        assert!(t.contains(&(kind::PUNCT, ".*".to_string())));
        assert!(t.contains(&(kind::PUNCT, "->*".to_string())));
    }

    #[test]
    fn numbers_with_separators_and_suffixes() {
        let t = texts("1'000'000 0xDEAD'BEEFu 3.14f 0b1010 0x1.8p3");
        assert!(t.contains(&(kind::INT, "1'000'000".to_string())));
        assert!(t.contains(&(kind::INT, "0xDEAD'BEEFu".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14f".to_string())));
        assert!(t.contains(&(kind::INT, "0b1010".to_string())));
        assert!(t.contains(&(kind::FLOAT, "0x1.8p3".to_string())));
    }
}
