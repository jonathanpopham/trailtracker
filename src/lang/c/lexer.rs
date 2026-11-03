//! Lossless C lexer, grounded in the ISO C token grammar (C11/C17, with the
//! common C23 spellings recognized as keywords).
//!
//! Guarantees (identical contract to the Rust and Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs/form-feed, comments, and backslash–newline line
//!   continuations) are emitted as `trivia` tokens, never discarded. `NEWLINE` is
//!   emitted as a *non-trivia* token because it is structurally significant in C:
//!   it terminates a preprocessing directive (`#include`, `#define`, …). In
//!   ordinary code the parser treats it as ignorable.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_`/`$` as a pragmatic stand-in for the full set of
//! C identifier characters (including universal-character-name escapes) — anything
//! outside still lands in the tree as a covered token, never dropped.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// C keywords (C11/C17 plus widely-used C23 spellings). Like the Rust/Python
/// lexers, these lex as `ident` tokens; the parser distinguishes them via
/// [`is_keyword`].
pub const KEYWORDS: &[&str] = &[
    "auto",
    "break",
    "case",
    "char",
    "const",
    "continue",
    "default",
    "do",
    "double",
    "else",
    "enum",
    "extern",
    "float",
    "for",
    "goto",
    "if",
    "inline",
    "int",
    "long",
    "register",
    "restrict",
    "return",
    "short",
    "signed",
    "sizeof",
    "static",
    "struct",
    "switch",
    "typedef",
    "union",
    "unsigned",
    "void",
    "volatile",
    "while",
    // C11
    "_Alignas",
    "_Alignof",
    "_Atomic",
    "_Bool",
    "_Complex",
    "_Generic",
    "_Imaginary",
    "_Noreturn",
    "_Static_assert",
    "_Thread_local",
    // C23 / common spellings
    "alignas",
    "alignof",
    "bool",
    "constexpr",
    "false",
    "nullptr",
    "static_assert",
    "thread_local",
    "true",
    "typeof",
    "typeof_unqual",
];

pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.contains(&text)
}

pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const NEWLINE: &str = "newline";
    pub const COMMENT: &str = "comment";
    pub const LINE_CONTINUATION: &str = "line_continuation";
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
    "<<=", ">>=", "...", "->", "++", "--", "<<", ">>", "<=", ">=", "==", "!=", "&&", "||", "+=",
    "-=", "*=", "/=", "%=", "&=", "|=", "^=", "##",
];

const SINGLE_PUNCT: &str = "+-*/%&|^~!<>=()[]{}:,.;?#";

/// Detect a string/char literal prefix at the start of `rest`. Returns the prefix
/// length (in bytes) when `rest` is one of the C literal prefixes (`u8`, `L`,
/// `u`, `U`) immediately followed by a `"` or `'` quote; `None` otherwise.
fn lit_prefix(rest: &str) -> Option<usize> {
    let is_quote = |c: Option<char>| matches!(c, Some('"') | Some('\''));
    if let Some(after) = rest.strip_prefix("u8") {
        if is_quote(after.chars().next()) {
            return Some(2);
        }
    }
    for p in ["L", "u", "U"] {
        if let Some(after) = rest.strip_prefix(p) {
            if is_quote(after.chars().next()) {
                return Some(1);
            }
        }
    }
    None
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
                '\\' if matches!(self.peek_at(1), Some('\n') | Some('\r')) => {
                    // Explicit line continuation: backslash–newline joins lines. It
                    // is trivia, so a physical newline absorbed here never becomes a
                    // structural NEWLINE — a multi-line `#define` stays one logical
                    // directive line.
                    self.bump(); // backslash
                    if self.peek() == '\r' {
                        self.bump();
                    }
                    if self.peek() == '\n' {
                        self.bump();
                    }
                    self.push(kind::LINE_CONTINUATION, start, self.pos, true);
                }
                ' ' | '\t' | '\x0b' | '\x0c' => {
                    self.eat_while(|c| matches!(c, ' ' | '\t' | '\x0b' | '\x0c'));
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                '/' if self.peek_at(1) == Some('/') => {
                    let end = self.find_line_end(start);
                    self.pos = end;
                    self.push(kind::COMMENT, start, end, true);
                }
                '/' if self.peek_at(1) == Some('*') => self.block_comment(start),
                '"' => self.quoted(start, '"', kind::STRING),
                '\'' => self.quoted(start, '\'', kind::CHAR),
                c if is_ident_start(c) => {
                    // A leading `L`/`u`/`U`/`u8` may be a string/char prefix rather
                    // than an identifier (`L"x"`, `u8"y"`, `U'z'`).
                    if let Some(plen) = lit_prefix(&self.src[start..]) {
                        self.pos += plen;
                        let quote = self.peek();
                        let k = if quote == '"' {
                            kind::STRING
                        } else {
                            kind::CHAR
                        };
                        self.quoted(start, quote, k);
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
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }
        }
        self.tokens
    }

    fn ident(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        self.push(kind::IDENT, start, self.pos, false);
    }

    /// Scan a `/* ... */` block comment. Spans newlines; an unterminated comment
    /// runs to end of input (still covered, still lossless).
    fn block_comment(&mut self, start: usize) {
        self.pos += 2; // consume "/*"
        while self.pos < self.bytes.len() {
            if self.peek() == '*' && self.peek_at(1) == Some('/') {
                self.pos += 2;
                break;
            }
            self.bump();
        }
        self.push(kind::COMMENT, start, self.pos, true);
    }

    /// Scan a string (`"`) or character (`'`) literal. The opening prefix, if any,
    /// has already been consumed; the cursor is at the opening quote. Backslash
    /// escapes are honored; an unterminated literal ends at the line break and is
    /// flagged as an `error` token (never dropped).
    fn quoted(&mut self, start: usize, quote: char, ok_kind: &'static str) {
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
            if c == '\n' || c == '\r' {
                break; // unterminated single-line literal
            }
            self.bump();
        }
        let k = if terminated { ok_kind } else { kind::ERROR };
        self.push(k, start, self.pos, false);
    }

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        if self.peek() == '0' && matches!(self.peek_at(1), Some('x') | Some('X')) {
            self.pos += 2;
            self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
            if self.peek() == '.' {
                is_float = true;
                self.bump();
                self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
            }
            if matches!(self.peek(), 'p' | 'P') {
                is_float = true;
                self.bump();
                if matches!(self.peek(), '+' | '-') {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit() || c == '_');
            }
            self.eat_suffix();
            let k = if is_float { kind::FLOAT } else { kind::INT };
            return self.push(k, start, self.pos, false);
        }
        if self.peek() == '0' && matches!(self.peek_at(1), Some('b') | Some('B')) {
            self.pos += 2;
            self.eat_while(|c| c == '0' || c == '1' || c == '_');
            self.eat_suffix();
            return self.push(kind::INT, start, self.pos, false);
        }
        // Decimal / octal integer, or a float.
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        if self.peek() == '.' {
            is_float = true;
            self.bump();
            self.eat_while(|c| c.is_ascii_digit() || c == '_');
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
                self.bump();
                if sign_len == 1 {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit() || c == '_');
            }
        }
        self.eat_suffix();
        let k = if is_float { kind::FLOAT } else { kind::INT };
        self.push(k, start, self.pos, false);
    }

    /// Consume a trailing numeric suffix run (`u`, `U`, `l`, `L`, `f`, `F`, and
    /// their combinations). Conservative on classification but always keeps the
    /// suffix bytes attached to the literal token.
    fn eat_suffix(&mut self) {
        self.eat_while(|c| matches!(c, 'u' | 'U' | 'l' | 'L' | 'f' | 'F'));
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
    c == '_' || c == '$' || c.is_alphabetic()
}

fn is_ident_continue(c: char) -> bool {
    c == '_' || c == '$' || c.is_alphanumeric()
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
            "int main(void) {\n    return 0;\n}\n",
            "#include <stdio.h>\n#include \"local.h\"\n",
            "#define MAX(a, b) ((a) > (b) ? (a) : (b))\n",
            "x = 0xFF_00 + 1.5e3 + 0b1010 + 0x1.8p3 + 42ull;\n",
            "char *s = L\"wide\" u8\"utf8\" \"plain\"; char c = '\\n';\n",
            "a /* block\ncomment */ b // line comment\nc\n",
            "p->next = &arr[i]; obj.method(); a <<= 2;\n",
            "λ = '☃';  /* unicode */\n",
            "#define LONG 1 + \\\n  2\n",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("static int add(int a, int b) { return a + b; }\n");
        assert!(t.contains(&(kind::IDENT, "static".to_string())));
        assert!(t.contains(&(kind::IDENT, "add".to_string())));
        assert!(t.contains(&(kind::PUNCT, "(".to_string())));
        assert!(t.contains(&(kind::PUNCT, "{".to_string())));
        assert!(is_keyword("static"));
        assert!(is_keyword("return"));
        assert!(!is_keyword("add"));
    }

    #[test]
    fn newline_is_structural_continuation_is_trivia() {
        let t = lex("a\nb \\\nc\n");
        assert!(t.iter().any(|tk| tk.kind == kind::NEWLINE && !tk.trivia));
        assert!(t
            .iter()
            .any(|tk| tk.kind == kind::LINE_CONTINUATION && tk.trivia));
    }

    #[test]
    fn block_comment_spans_newlines() {
        let t = texts("a /* x\ny */ b\n");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::COMMENT && s == "/* x\ny */"));
    }

    #[test]
    fn strings_chars_and_prefixes() {
        for (src, lit, k) in [
            ("\"hi\\n\"", "\"hi\\n\"", kind::STRING),
            ("L\"wide\"", "L\"wide\"", kind::STRING),
            ("u8\"u\"", "u8\"u\"", kind::STRING),
            ("'a'", "'a'", kind::CHAR),
            ("'\\''", "'\\''", kind::CHAR),
            ("U'z'", "U'z'", kind::CHAR),
        ] {
            let t = texts(src);
            assert!(
                t.iter().any(|(tk, s)| *tk == k && s == lit),
                "literal not recognized: {src}"
            );
        }
    }

    #[test]
    fn numbers() {
        let t = texts("0b1010 017 0xAF 10u 0x1.8p3 3.14f 2e10 5LL");
        assert!(t.contains(&(kind::INT, "0b1010".to_string())));
        assert!(t.contains(&(kind::INT, "0xAF".to_string())));
        assert!(t.contains(&(kind::INT, "10u".to_string())));
        assert!(t.contains(&(kind::FLOAT, "0x1.8p3".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14f".to_string())));
        assert!(t.contains(&(kind::INT, "5LL".to_string())));
    }

    #[test]
    fn arrow_and_compound_operators() {
        let t = texts("a->b <<= c >> d != e");
        assert!(t.contains(&(kind::PUNCT, "->".to_string())));
        assert!(t.contains(&(kind::PUNCT, "<<=".to_string())));
        assert!(t.contains(&(kind::PUNCT, ">>".to_string())));
        assert!(t.contains(&(kind::PUNCT, "!=".to_string())));
    }

    #[test]
    fn unterminated_literals_become_errors_not_drops() {
        let t = texts("char *s = \"oops\nint x;\n");
        assert!(t.iter().any(|(k, _)| *k == kind::ERROR));
        assert!(covers_all("char *s = \"oops\nint x;\n"));
    }
}
