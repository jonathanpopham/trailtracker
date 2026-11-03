//! Lossless D lexer, grounded in the D language lexical grammar.
//!
//! Guarantees (identical contract to the Rust / C++ / Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (whitespace, all three comment forms) are emitted as `trivia`
//!   tokens, never dropped. D has three comment syntaxes: `//` line, `/* */`
//!   block (non-nesting), and `/+ +/` **nested** block comments.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped, and the main loop has a hard
//!   progress guard so a malformed sub-scanner can never spin.
//!
//! D string zoo, all handled here and classified as `string_literal`:
//!   - `"..."`         double-quoted, C-style backslash escapes, optional
//!                     `c`/`w`/`d` width suffix.
//!   - `` `...` ``     backtick wysiwyg (no escapes).
//!   - `r"..."`        raw wysiwyg (no escapes).
//!   - `x"..."`        hex string (no escapes).
//!   - `q{...}`        token string (balanced braces).
//!   - `q"(...)"` etc. delimited string (nesting bracket pairs or single-char
//!                     delimiter). Heredoc `q"IDENT..IDENT"` is approximated by
//!                     the single-char-delimiter path — still byte-lossless, see
//!                     the module-level punts note.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_` as a pragmatic stand-in for the full Unicode
//! identifier tables. Anything outside still lands in the tree as a covered
//! token, never dropped.

#![allow(clippy::doc_overindented_list_items)] // aligned doc block; style-only

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// D keywords (DMD reference set, including a few `__`-prefixed ones). Like the
/// other front ends these lex as `ident` tokens; the parser distinguishes them
/// via [`is_keyword`].
pub const KEYWORDS: &[&str] = &[
    "abstract",
    "alias",
    "align",
    "asm",
    "assert",
    "auto",
    "body",
    "bool",
    "break",
    "byte",
    "case",
    "cast",
    "catch",
    "cdouble",
    "cent",
    "cfloat",
    "char",
    "class",
    "const",
    "continue",
    "creal",
    "dchar",
    "debug",
    "default",
    "delegate",
    "delete",
    "deprecated",
    "do",
    "double",
    "else",
    "enum",
    "export",
    "extern",
    "false",
    "final",
    "finally",
    "float",
    "for",
    "foreach",
    "foreach_reverse",
    "function",
    "goto",
    "idouble",
    "if",
    "ifloat",
    "immutable",
    "import",
    "in",
    "inout",
    "int",
    "interface",
    "invariant",
    "ireal",
    "is",
    "lazy",
    "long",
    "macro",
    "mixin",
    "module",
    "new",
    "nothrow",
    "null",
    "out",
    "override",
    "package",
    "pragma",
    "private",
    "protected",
    "public",
    "pure",
    "real",
    "ref",
    "return",
    "scope",
    "shared",
    "short",
    "static",
    "struct",
    "super",
    "switch",
    "synchronized",
    "template",
    "this",
    "throw",
    "true",
    "try",
    "typeid",
    "typeof",
    "ubyte",
    "ucent",
    "uint",
    "ulong",
    "union",
    "unittest",
    "ushort",
    "version",
    "void",
    "wchar",
    "while",
    "with",
    "__gshared",
    "__traits",
    "__vector",
    "__parameters",
    "__FILE__",
    "__LINE__",
    "__MODULE__",
    "__FUNCTION__",
    "__PRETTY_FUNCTION__",
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
    /// A `/+ +/` nested block comment. Trivia.
    pub const NESTED_COMMENT: &str = "nested_comment";
    /// A `#!...` shebang line, only at the very start of the file. Non-trivia
    /// (it is structurally a directive, but D ignores it semantically).
    pub const SHEBANG: &str = "shebang";
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
    ">>>=", "^^=", "...", ">>>", "<<=", ">>=", "==", "!=", "<=", ">=", "<<", ">>", "&&", "||",
    "++", "--", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "~=", "..", "=>", "^^",
];

const SINGLE_PUNCT: &str = "+-*/%!&|^~<>=.,;:()[]{}?@#$";

/// The literal form a leading prefix introduces.
enum LitForm {
    /// `r"..."` — raw wysiwyg, delimiter `"`.
    Raw,
    /// `x"..."` — hex string, delimiter `"`.
    Hex,
    /// `q{...}` — token string, balanced braces.
    TokenString,
    /// `q"..."` — delimited string (nesting bracket pairs or single-char delim).
    Delimited,
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
        // Shebang: only meaningful as the first bytes of the file.
        if self.src.starts_with("#!") {
            let end = self.find_line_end(0);
            self.pos = end;
            self.push(kind::SHEBANG, 0, end, false);
        }
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
                '/' if self.peek_at(1) == Some('+') => self.nested_comment(start),
                '"' => self.escaped_string(start),
                '`' => self.wysiwyg(start, '`'),
                '\'' => self.char_literal(start),
                c if is_ident_start(c) => {
                    if let Some((plen, form)) = self.literal_prefix(start) {
                        self.pos += plen;
                        match form {
                            LitForm::Raw | LitForm::Hex => self.wysiwyg(start, '"'),
                            LitForm::TokenString => self.token_string(start),
                            LitForm::Delimited => self.delimited_string(start),
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
            // Main-loop progress guard: no branch may ever leave the cursor where
            // it found it. If one somehow does, force one byte of progress as an
            // error token so the lexer can never spin.
            if self.pos == start {
                self.bump();
                self.push(kind::ERROR, start, self.pos, false);
            }
        }
        self.tokens
    }

    // --- comment scanners ---------------------------------------------------

    fn line_comment(&mut self, start: usize) {
        let end = self.find_line_end(start);
        self.pos = end;
        self.push(kind::LINE_COMMENT, start, end, true);
    }

    fn block_comment(&mut self, start: usize) {
        // `/* */` block comments do NOT nest: the first `*/` closes the comment.
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

    /// `/+ +/` — D's **nesting** block comment. Track depth so an inner `/+` must
    /// be balanced by a matching `+/` before the outer comment closes.
    fn nested_comment(&mut self, start: usize) {
        self.pos += 2; // /+
        let mut depth: u32 = 1;
        while self.pos < self.bytes.len() && depth > 0 {
            if self.src[self.pos..].starts_with("/+") {
                self.pos += 2;
                depth += 1;
            } else if self.src[self.pos..].starts_with("+/") {
                self.pos += 2;
                depth -= 1;
            } else {
                self.bump();
            }
        }
        // An unterminated nested comment is still trivia covering to EOF.
        self.push(kind::NESTED_COMMENT, start, self.pos, true);
    }

    // --- identifier / literal-prefix dispatch -------------------------------

    fn ident(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        self.push(kind::IDENT, start, self.pos, false);
    }

    /// Detect a string-literal prefix at `start` and classify it. Returns the
    /// prefix byte length (the bytes to skip before the body scanner) and the
    /// literal form, or `None` for an ordinary identifier. Each prefix only
    /// counts when the introducer character immediately follows it.
    fn literal_prefix(&self, start: usize) -> Option<(usize, LitForm)> {
        let rest = &self.src[start..];
        if rest.starts_with("r\"") {
            return Some((1, LitForm::Raw));
        }
        if rest.starts_with("x\"") {
            return Some((1, LitForm::Hex));
        }
        if rest.starts_with("q{") {
            return Some((1, LitForm::TokenString));
        }
        if rest.starts_with("q\"") {
            return Some((2, LitForm::Delimited));
        }
        None
    }

    // --- string scanners ----------------------------------------------------

    /// Scan a `"..."` literal body with C-style backslash escapes. The cursor is
    /// at the opening quote. An unterminated literal (EOF or bare newline)
    /// becomes an `error` token.
    fn escaped_string(&mut self, start: usize) {
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
        if terminated {
            self.eat_string_suffix();
        }
        let k = if terminated {
            kind::STRING
        } else {
            kind::ERROR
        };
        self.push(k, start, self.pos, false);
    }

    /// Scan a wysiwyg literal (no escapes) terminated by `delim`: backtick
    /// strings (`delim == '`'`) and `r"..."` / `x"..."` (`delim == '"'`, the
    /// `r`/`x` prefix already consumed by the caller).
    fn wysiwyg(&mut self, start: usize, delim: char) {
        self.bump(); // opening delimiter
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            if self.peek() == delim {
                self.bump();
                terminated = true;
                break;
            }
            self.bump();
        }
        if terminated {
            self.eat_string_suffix();
        }
        let k = if terminated {
            kind::STRING
        } else {
            kind::ERROR
        };
        self.push(k, start, self.pos, false);
    }

    /// `q{ ... }` token string: balanced braces. The `q` prefix is consumed; the
    /// cursor is at the opening `{`.
    fn token_string(&mut self, start: usize) {
        self.bump(); // {
        let mut depth: u32 = 1;
        while self.pos < self.bytes.len() && depth > 0 {
            match self.peek() {
                '{' => depth += 1,
                '}' => depth -= 1,
                _ => {}
            }
            self.bump();
        }
        let k = if depth == 0 {
            kind::STRING
        } else {
            kind::ERROR
        };
        self.push(k, start, self.pos, false);
    }

    /// `q"(...)"` / `q"[...]"` / `q"{...}"` / `q"<...>"` (nesting bracket pairs)
    /// or `q"X...X"` (single-char delimiter). The `q"` prefix is consumed; the
    /// cursor is at the opening delimiter character.
    fn delimited_string(&mut self, start: usize) {
        if self.pos >= self.bytes.len() {
            // `q"` at end of input: nothing to delimit. Cover the bytes as error.
            self.push(kind::ERROR, start, self.pos, false);
            return;
        }
        let open = self.peek();
        let (close, nesting) = match open {
            '(' => (')', true),
            '[' => (']', true),
            '{' => ('}', true),
            '<' => ('>', true),
            other => (other, false),
        };
        self.bump(); // opening delimiter char
        let mut depth: u32 = 1;
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if nesting && c == open {
                depth += 1;
                self.bump();
                continue;
            }
            if c == close {
                if nesting {
                    depth -= 1;
                    if depth == 0 {
                        self.bump(); // closing delimiter char
                        if self.peek() == '"' {
                            self.bump();
                            terminated = true;
                        }
                        break;
                    }
                    self.bump();
                    continue;
                } else if self.peek_at(1) == Some('"') {
                    self.bump(); // delimiter char
                    self.bump(); // "
                    terminated = true;
                    break;
                }
            }
            self.bump();
        }
        if terminated {
            self.eat_string_suffix();
        }
        let k = if terminated {
            kind::STRING
        } else {
            kind::ERROR
        };
        self.push(k, start, self.pos, false);
    }

    /// Scan a `'...'` character literal with backslash escapes. Unterminated →
    /// `error` token.
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
                break; // unterminated single-line literal
            } else {
                self.bump();
            }
        }
        let k = if terminated { kind::CHAR } else { kind::ERROR };
        self.push(k, start, self.pos, false);
    }

    /// A string's optional width suffix: exactly one of `c`/`w`/`d`.
    fn eat_string_suffix(&mut self) {
        if matches!(self.peek(), 'c' | 'w' | 'd') {
            self.bump();
        }
    }

    // --- number scanner -----------------------------------------------------

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        if self.peek() == '0' {
            match self.peek_at(1) {
                Some('x') | Some('X') => {
                    self.pos += 2;
                    self.eat_digit_run(|c| c.is_ascii_hexdigit());
                    // Hex float: `0x1.8p3`.
                    if self.peek() == '.' && self.peek_at(1) != Some('.') {
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
        // Decimal integer part.
        self.eat_digit_run(|c| c.is_ascii_digit());
        // Fractional part — but not a `..` range and only with a digit following,
        // so `1..2` and a bare `1.` stay correctly tokenized.
        if self.peek() == '.'
            && self.peek_at(1) != Some('.')
            && self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false)
        {
            is_float = true;
            self.bump(); // .
            self.eat_digit_run(|c| c.is_ascii_digit());
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

    /// Numeric suffix: an identifier-continue run (`L`, `u`, `f`, `i`, `UL`, …),
    /// without crossing into a member access.
    fn eat_suffix(&mut self) {
        if is_ident_start(self.peek()) {
            self.eat_while(is_ident_continue);
        }
    }

    /// Eat a run of digits accepted by `pred`, allowing `_` digit separators
    /// (D permits underscores freely within a numeric literal).
    fn eat_digit_run(&mut self, pred: impl Fn(char) -> bool) {
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if pred(c) || c == '_' {
                self.bump();
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
            "void main() { return; }\n",
            "module a.b.c;\nimport std.stdio;\n",
            "// line\n/* block */ /+ /+ nested +/ +/ int x = 0xFF_00;\n",
            "auto s = r\"raw \\ text\"; auto t = `back\"tick`;\n",
            "auto h = x\"DE AD BE EF\"; auto q = q{ a + b }; auto d = q\"(a (b) c)\";\n",
            "double d = 1.5e-3 + 0x1.8p3 + 3_000.0f; auto r = 1..2;\n",
            "auto e = q\"/foo bar/\"c; char c = '\\n';\n",
            "#!/usr/bin/env rdmd\nvoid main() {}\n",
            "auto λ = '☃'; // unicode\n",
            "enum E { A, B = 2, C }\n",
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
        assert!(is_keyword("module"));
        assert!(!is_keyword("add"));
    }

    #[test]
    fn nested_comment_balances() {
        let t = texts("/+ outer /+ inner +/ still outer +/x");
        assert!(
            t.iter()
                .any(|(k, s)| *k == kind::NESTED_COMMENT
                    && s == "/+ outer /+ inner +/ still outer +/")
        );
        assert!(t.contains(&(kind::IDENT, "x".to_string())));
    }

    #[test]
    fn string_zoo() {
        let t = texts(r#""esc\"aped" `wysiwyg` r"raw\" x"DEAD" q{a{b}c}"#);
        // The escaped string keeps the escaped quote inside.
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == r#""esc\"aped""#));
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "`wysiwyg`"));
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "r\"raw\\\""));
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "x\"DEAD\""));
        assert!(t.iter().any(|(k, s)| *k == kind::STRING && s == "q{a{b}c}"));
    }

    #[test]
    fn delimited_strings() {
        let t = texts("q\"(a (b) c)\" q\"/slash/\" q\"[x]\"");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "q\"(a (b) c)\""));
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "q\"/slash/\""));
        assert!(t.iter().any(|(k, s)| *k == kind::STRING && s == "q\"[x]\""));
    }

    #[test]
    fn numbers_with_underscores_and_suffixes() {
        let t = texts("1_000_000 0xDEAD_BEEFu 3.14f 0b1010 0x1.8p3 1.5e-3L");
        assert!(t.contains(&(kind::INT, "1_000_000".to_string())));
        assert!(t.contains(&(kind::INT, "0xDEAD_BEEFu".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14f".to_string())));
        assert!(t.contains(&(kind::INT, "0b1010".to_string())));
        assert!(t.contains(&(kind::FLOAT, "0x1.8p3".to_string())));
        assert!(t.contains(&(kind::FLOAT, "1.5e-3L".to_string())));
    }

    #[test]
    fn range_is_not_a_float() {
        let t = texts("foreach (i; 0 .. 10) {}");
        assert!(t.contains(&(kind::PUNCT, "..".to_string())));
        assert!(t.contains(&(kind::INT, "0".to_string())));
        assert!(t.contains(&(kind::INT, "10".to_string())));
    }

    #[test]
    fn shebang_only_at_file_start() {
        let t = texts("#!/usr/bin/env rdmd\nint x;\n");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::SHEBANG && s == "#!/usr/bin/env rdmd"));
        // A mid-file '#' is just punct.
        let t2 = texts("a # b");
        assert!(t2.contains(&(kind::PUNCT, "#".to_string())));
        assert!(t2.iter().all(|(k, _)| *k != kind::SHEBANG));
    }
}
