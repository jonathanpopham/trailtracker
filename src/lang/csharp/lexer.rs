//! Lossless C# lexer, grounded in the C# language specification's lexical
//! grammar. Produces the same shared [`Token`] stream as the Rust lexer, with
//! the same guarantees: contiguous coverage, trivia retained, unknown input
//! preserved as `error` tokens.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_` as a pragmatic stand-in for the spec's full
//! Unicode identifier classes. Interpolated-string holes are scanned with brace
//! balancing rather than fully parsed; anything unhandled still lands in the
//! tree losslessly.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// C# reserved keywords plus the contextual keywords TrailTracker keys on for
/// structure (`record`, `var`, `where`, …). The parser handles further context.
pub const KEYWORDS: &[&str] = &[
    "abstract",
    "as",
    "base",
    "bool",
    "break",
    "byte",
    "case",
    "catch",
    "char",
    "checked",
    "class",
    "const",
    "continue",
    "decimal",
    "default",
    "delegate",
    "do",
    "double",
    "else",
    "enum",
    "event",
    "explicit",
    "extern",
    "false",
    "finally",
    "fixed",
    "float",
    "for",
    "foreach",
    "goto",
    "if",
    "implicit",
    "in",
    "int",
    "interface",
    "internal",
    "is",
    "lock",
    "long",
    "namespace",
    "new",
    "null",
    "object",
    "operator",
    "out",
    "override",
    "params",
    "private",
    "protected",
    "public",
    "readonly",
    "ref",
    "return",
    "sbyte",
    "sealed",
    "short",
    "sizeof",
    "stackalloc",
    "static",
    "string",
    "struct",
    "switch",
    "this",
    "throw",
    "true",
    "try",
    "typeof",
    "uint",
    "ulong",
    "unchecked",
    "unsafe",
    "ushort",
    "using",
    "virtual",
    "void",
    "volatile",
    "while",
    "record",
    "var",
    "where",
    "yield",
    "async",
    "await",
    "partial",
    "get",
    "set",
    "init",
    "global",
];

pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.contains(&text)
}

pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const LINE_COMMENT: &str = "line_comment";
    pub const BLOCK_COMMENT: &str = "block_comment";
    pub const DOC_COMMENT: &str = "doc_comment";
    pub const PREPROCESSOR: &str = "preprocessor";
    pub const IDENT: &str = "ident";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const CHAR: &str = "char_literal";
    pub const STRING: &str = "string_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first.
const OPERATORS: &[&str] = &[
    "<<=", ">>=", ">>>", "...", "??=", "=>", "==", "!=", "<=", ">=", "&&", "||", "??", "?.", "::",
    "->", "++", "--", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<", ">>",
];

const SINGLE_PUNCT: &str = "+-*/%!&|^<>=.,;:()[]{}@?~";

pub fn lex(source: &str) -> Vec<Token> {
    Lexer::new(source).run()
}

struct Lexer<'s> {
    src: &'s str,
    bytes: &'s [u8],
    pos: usize,
    tokens: Vec<Token>,
    /// True at start-of-line (ignoring whitespace), used to recognize `#`
    /// preprocessor directives which are only valid there.
    line_start: bool,
}

impl<'s> Lexer<'s> {
    fn new(src: &'s str) -> Self {
        Lexer {
            src,
            bytes: src.as_bytes(),
            pos: 0,
            tokens: Vec::new(),
            line_start: true,
        }
    }

    fn run(mut self) -> Vec<Token> {
        while self.pos < self.bytes.len() {
            let start = self.pos;
            let c = self.peek();
            match c {
                c if c.is_whitespace() => {
                    let mut saw_newline = false;
                    self.eat_while(|c| {
                        if c == '\n' {
                            saw_newline = true;
                        }
                        c.is_whitespace()
                    });
                    self.push(kind::WHITESPACE, start, self.pos, true);
                    if saw_newline {
                        self.line_start = true;
                    }
                    continue;
                }
                '#' if self.line_start => {
                    let end = self.find_line_end(start);
                    self.pos = end;
                    self.push(kind::PREPROCESSOR, start, end, true);
                }
                '/' if self.peek_at(1) == Some('/') => self.line_comment(start),
                '/' if self.peek_at(1) == Some('*') => self.block_comment(start),
                '@' if self.peek_at(1) == Some('"') => {
                    self.pos += 1; // @
                    self.string_body(start, true, false);
                }
                '@' if self.peek_at(1) == Some('$') && self.peek_at(2) == Some('"') => {
                    self.pos += 2; // @$
                    self.string_body(start, true, true);
                }
                '@' if matches!(self.peek_at(1), Some(c) if is_ident_start(c)) => {
                    self.pos += 1; // @ verbatim identifier prefix
                    self.eat_while(is_ident_continue);
                    self.push(kind::IDENT, start, self.pos, false);
                }
                '$' if self.peek_at(1) == Some('"') => {
                    if self.peek_at(2) == Some('"') && self.peek_at(3) == Some('"') {
                        self.pos += 1; // $
                        self.raw_string(start);
                    } else {
                        self.pos += 1; // $
                        self.string_body(start, false, true);
                    }
                }
                '$' if self.peek_at(1) == Some('@') && self.peek_at(2) == Some('"') => {
                    self.pos += 2; // $@
                    self.string_body(start, true, true);
                }
                '"' if self.peek_at(1) == Some('"') && self.peek_at(2) == Some('"') => {
                    self.raw_string(start)
                }
                '"' => self.string_body(start, false, false),
                '\'' => self.char_literal(start),
                c if is_ident_start(c) => {
                    self.eat_while(is_ident_continue);
                    self.push(kind::IDENT, start, self.pos, false);
                }
                c if c.is_ascii_digit() => self.number(start),
                '.' if matches!(self.peek_at(1), Some(d) if d.is_ascii_digit()) => {
                    self.number(start)
                }
                c if SINGLE_PUNCT.contains(c) => self.punct(start),
                _ => {
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }
            // Any non-newline-only token clears line-start.
            if self.tokens.last().map(|t| t.kind) != Some(kind::WHITESPACE) {
                self.line_start = false;
            }
        }
        self.tokens
    }

    fn line_comment(&mut self, start: usize) {
        // `///` is an XML doc comment; `//` an ordinary one. `////` is ordinary.
        let is_doc = self.peek_at(2) == Some('/') && self.peek_at(3) != Some('/');
        let end = self.find_line_end(start);
        self.pos = end;
        let k = if is_doc {
            kind::DOC_COMMENT
        } else {
            kind::LINE_COMMENT
        };
        self.push(k, start, end, true);
    }

    fn block_comment(&mut self, start: usize) {
        // C# block comments do not nest.
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

    /// Scan a `"..."` body. `verbatim` (`@"`) doubles `""` for a literal quote
    /// and may span lines; `interpolated` (`$"`) has `{...}` holes. The opening
    /// quote has not yet been consumed.
    fn string_body(&mut self, start: usize, verbatim: bool, interpolated: bool) {
        self.bump(); // opening "
        let mut hole_depth: i32 = 0;
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if interpolated && c == '{' {
                if self.peek_at(1) == Some('{') {
                    self.pos += 2;
                } else {
                    hole_depth += 1;
                    self.bump();
                }
                continue;
            }
            if interpolated && c == '}' {
                if hole_depth > 0 {
                    hole_depth -= 1;
                    self.bump();
                } else if self.peek_at(1) == Some('}') {
                    self.pos += 2;
                } else {
                    self.bump();
                }
                continue;
            }
            if c == '"' && hole_depth == 0 {
                if verbatim && self.peek_at(1) == Some('"') {
                    self.pos += 2; // doubled quote = literal
                    continue;
                }
                self.bump(); // closing quote
                terminated = true;
                break;
            }
            if c == '\\' && !verbatim {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
                continue;
            }
            if c == '\n' && !verbatim && hole_depth == 0 {
                break; // non-verbatim strings cannot span lines
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

    /// Raw string literal `"""..."""` (opening run of N>=3 quotes). Any `$`
    /// prefix has already been consumed; positioned at the first quote.
    fn raw_string(&mut self, start: usize) {
        let mut quote_count = 0;
        while self.peek() == '"' {
            quote_count += 1;
            self.bump();
        }
        let closing = "\"".repeat(quote_count);
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            if self.src[self.pos..].starts_with(&closing)
                && !self.src[self.pos + closing.len()..].starts_with('"')
            {
                self.pos += closing.len();
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

    fn char_literal(&mut self, start: usize) {
        self.bump(); // '
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
            self.eat_suffix();
            return self.push(kind::INT, start, self.pos, false);
        }
        if self.peek() == '0' && matches!(self.peek_at(1), Some('b') | Some('B')) {
            self.pos += 2;
            self.eat_while(|c| c == '0' || c == '1' || c == '_');
            self.eat_suffix();
            return self.push(kind::INT, start, self.pos, false);
        }
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        if self.peek() == '.' && matches!(self.peek_at(1), Some(d) if d.is_ascii_digit()) {
            is_float = true;
            self.bump();
            self.eat_while(|c| c.is_ascii_digit() || c == '_');
        }
        if matches!(self.peek(), 'e' | 'E') {
            let sign = matches!(self.peek_at(1), Some('+') | Some('-'));
            let digit_at = if sign { 2 } else { 1 };
            if matches!(self.peek_at(digit_at), Some(d) if d.is_ascii_digit()) {
                is_float = true;
                self.bump(); // e
                if sign {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit() || c == '_');
            }
        }
        // Float type suffixes f/d/m make it a float; integer suffixes u/l do not.
        if matches!(self.peek(), 'f' | 'F' | 'd' | 'D' | 'm' | 'M') {
            is_float = true;
        }
        self.eat_suffix();
        let k = if is_float { kind::FLOAT } else { kind::INT };
        self.push(k, start, self.pos, false);
    }

    fn eat_suffix(&mut self) {
        if matches!(self.peek(), c if is_ident_start(c)) {
            self.eat_while(is_ident_continue);
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
            "public class C { void M() { } }",
            "var s = @\"a\"\"b\";",
            "var s = $\"x{a + b}y\";",
            "var s = $@\"p{q}\"\"r\";",
            "var s = \"\"\"\nraw \"quote\"\n\"\"\";",
            "// line\n/// <doc/>\n/* block */ x",
            "#region foo\n#endif\nint x = 0xFF_u;",
            "decimal m = 1.5e3m; double d = .5;",
            "'a' '\\n' \"str\"",
            "λ ☃ €",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn verbatim_string_with_doubled_quote() {
        let t = texts("@\"a\"\"b\"");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "@\"a\"\"b\""));
    }

    #[test]
    fn interpolated_string_holes() {
        let t = texts("$\"x{a + b}y\"");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "$\"x{a + b}y\""));
    }

    #[test]
    fn raw_string_triple_quote() {
        let t = texts("\"\"\"a\"b\"\"\"");
        assert!(t.iter().any(|(k, _)| *k == kind::STRING));
    }

    #[test]
    fn preprocessor_and_doc_are_trivia() {
        let toks = lex("#nullable enable\n/// doc\nint x;");
        assert!(toks
            .iter()
            .any(|t| t.kind == kind::PREPROCESSOR && t.trivia));
        assert!(toks.iter().any(|t| t.kind == kind::DOC_COMMENT && t.trivia));
    }

    #[test]
    fn classifies_operators() {
        let t = texts("a ??= b => c?.d");
        assert!(t.contains(&(kind::PUNCT, "??=".to_string())));
        assert!(t.contains(&(kind::PUNCT, "=>".to_string())));
        assert!(t.contains(&(kind::PUNCT, "?.".to_string())));
    }
}
