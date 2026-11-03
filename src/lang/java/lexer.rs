//! Lossless Java lexer, grounded in the Java Language Specification (JLS) token
//! grammar.
//!
//! Guarantees (identical contract to the Rust and Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (whitespace, line/block/Javadoc comments) are emitted as `trivia`
//!   tokens, not discarded — the parser skips them for structure but the tree
//!   keeps them.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//!
//! Java surface covered: `//` line comments, `/* */` and `/** */` block comments
//! (Java block comments do **not** nest, unlike Rust), `"..."` strings, `"""..."""`
//! text blocks (JLS 15+, multi-line), `'...'` char literals, decimal/hex/binary/
//! octal integers and floating-point literals (with `_` separators and the
//! `lLfFdD` suffixes, including hex floats), identifiers/keywords, and the full
//! operator/punctuation set (`>>>`, `>>>=`, `::`, `->`, …).
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_` and `$` (both legal in Java identifiers) as a
//! pragmatic stand-in for the full Unicode identifier tables. Anything outside it
//! still lands in the tree as a covered token, never dropped.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Java's reserved keywords (JLS §3.9), plus the boolean/null literals. Like the
/// Rust and Python lexers, these lex as `ident` tokens; the parser and lowering
/// distinguish them via [`is_keyword`]. The *restricted/contextual* keywords
/// (`var`, `record`, `sealed`, `permits`, `yield`, `module`, …) are deliberately
/// excluded so they keep working as identifiers; the parser recognizes them by
/// position instead.
pub const KEYWORDS: &[&str] = &[
    "abstract",
    "assert",
    "boolean",
    "break",
    "byte",
    "case",
    "catch",
    "char",
    "class",
    "const",
    "continue",
    "default",
    "do",
    "double",
    "else",
    "enum",
    "extends",
    "final",
    "finally",
    "float",
    "for",
    "goto",
    "if",
    "implements",
    "import",
    "instanceof",
    "int",
    "interface",
    "long",
    "native",
    "new",
    "package",
    "private",
    "protected",
    "public",
    "return",
    "short",
    "static",
    "strictfp",
    "super",
    "switch",
    "synchronized",
    "this",
    "throw",
    "throws",
    "transient",
    "try",
    "void",
    "volatile",
    "while",
    // Literals — reserved, never identifiers.
    "true",
    "false",
    "null",
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
    pub const IDENT: &str = "ident";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const CHAR: &str = "char_literal";
    pub const STRING: &str = "string_literal";
    pub const TEXT_BLOCK: &str = "text_block";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
/// `>>>=` (4) precedes `>>>` (3) precedes `>>` (2), and so on.
const OPERATORS: &[&str] = &[
    ">>>=", "<<=", ">>=", ">>>", "...", "->", "::", "==", "!=", "<=", ">=", "&&", "||", "++", "--",
    "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<", ">>",
];

const SINGLE_PUNCT: &str = "+-*/%!&|^~<>=.,;:()[]{}@?";

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
                '/' if self.peek_at(1) == Some('/') => self.line_comment(start),
                '/' if self.peek_at(1) == Some('*') => self.block_comment(start),
                '"' => self.string(start),
                '\'' => self.char_literal(start),
                c if c.is_ascii_digit() => self.number(start),
                '.' if self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) => {
                    self.number(start)
                }
                c if is_ident_start(c) => self.ident(start),
                c if SINGLE_PUNCT.contains(c) => self.punct(start),
                _ => {
                    // Unknown byte/char — preserve it as an explicit error token.
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }
        }
        self.tokens
    }

    // --- scanners -----------------------------------------------------------

    fn line_comment(&mut self, start: usize) {
        let end = self.find_line_end(start);
        self.pos = end;
        self.push(kind::LINE_COMMENT, start, end, true);
    }

    /// `/* ... */` (and `/** ... */` Javadoc). Java block comments do not nest.
    fn block_comment(&mut self, start: usize) {
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

    /// Scan a `"..."` string or a `"""..."""` text block (JLS 15+). The text-block
    /// form spans newlines; the single-line form ends at an unescaped newline
    /// (unterminated → error token over what was consumed).
    fn string(&mut self, start: usize) {
        if self.peek_at(1) == Some('"') && self.peek_at(2) == Some('"') {
            return self.text_block(start);
        }
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
                break; // unterminated single-line string
            } else {
                self.bump();
            }
        }
        let token_kind = if terminated {
            kind::STRING
        } else {
            kind::ERROR
        };
        self.push(token_kind, start, self.pos, false);
    }

    /// Text block: `"""` … `"""`, spanning newlines, honoring backslash escapes.
    fn text_block(&mut self, start: usize) {
        self.pos += 3; // opening """
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '\\' {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
            } else if c == '"' && self.peek_at(1) == Some('"') && self.peek_at(2) == Some('"') {
                self.pos += 3;
                terminated = true;
                break;
            } else {
                self.bump();
            }
        }
        let token_kind = if terminated {
            kind::TEXT_BLOCK
        } else {
            kind::ERROR
        };
        self.push(token_kind, start, self.pos, false);
    }

    /// `'...'` char literal. Handles escapes; an unterminated literal becomes an
    /// error token over what was consumed.
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
        let token_kind = if terminated { kind::CHAR } else { kind::ERROR };
        self.push(token_kind, start, self.pos, false);
    }

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        if self.peek() == '0' && matches!(self.peek_at(1), Some('x') | Some('X')) {
            self.pos += 2;
            self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
            // Hex floating point: `0x1.8p3`.
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
            if self.eat_number_suffix() {
                is_float = true;
            }
            let k = if is_float { kind::FLOAT } else { kind::INT };
            return self.push(k, start, self.pos, false);
        }
        if self.peek() == '0' && matches!(self.peek_at(1), Some('b') | Some('B')) {
            self.pos += 2;
            self.eat_while(|c| c == '0' || c == '1' || c == '_');
            self.eat_number_suffix();
            return self.push(kind::INT, start, self.pos, false);
        }
        // Decimal (a leading `0` octal lexes as an integer too).
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        // Fractional part only if a digit follows the dot, so `1.method()` and
        // range-like constructs stay split.
        if self.peek() == '.' && self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) {
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
                self.bump(); // e
                if sign_len == 1 {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit() || c == '_');
            }
        }
        if self.eat_number_suffix() {
            is_float = true;
        }
        let k = if is_float { kind::FLOAT } else { kind::INT };
        self.push(k, start, self.pos, false);
    }

    /// Consume a single numeric suffix if present. Returns `true` when the suffix
    /// makes the literal floating-point (`f`/`F`/`d`/`D`); `l`/`L` is the `long`
    /// integer suffix and returns `false`.
    fn eat_number_suffix(&mut self) -> bool {
        match self.peek() {
            'l' | 'L' => {
                self.bump();
                false
            }
            'f' | 'F' | 'd' | 'D' => {
                self.bump();
                true
            }
            _ => false,
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
            "class A {}",
            "int x = 1_000;",
            "// comment\nlong y = 0xFF_00L;",
            "/* block *//** javadoc */ x",
            "String s = \"hi\\n\" + 'c';",
            "var t = \"\"\"\nmulti\nline\"\"\";",
            "a >>>= b; c >>> d; e <<= f;",
            "double d = 1.5e3; float g = 0x1.8p3f;",
            "λ ☃ €", // non-ascii idents / unknowns still covered
            "@Override public void m() {}",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("public int add(int a) { return a; }");
        assert!(t.contains(&(kind::IDENT, "public".to_string())));
        assert!(t.contains(&(kind::IDENT, "add".to_string())));
        assert!(t.contains(&(kind::PUNCT, "(".to_string())));
        assert!(is_keyword("public"));
        assert!(is_keyword("class"));
        assert!(!is_keyword("add"));
        // Restricted keywords stay identifiers.
        assert!(!is_keyword("record"));
        assert!(!is_keyword("var"));
    }

    #[test]
    fn text_block_spans_newlines() {
        let t = texts("var x = \"\"\"\na\nb\"\"\";");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::TEXT_BLOCK && s == "\"\"\"\na\nb\"\"\""));
    }

    #[test]
    fn numbers() {
        let t = texts("0b1010 0xAF 10_000 3.14 2e10 5L 1.5f 0x1.8p3");
        assert!(t.contains(&(kind::INT, "0b1010".to_string())));
        assert!(t.contains(&(kind::INT, "0xAF".to_string())));
        assert!(t.contains(&(kind::INT, "10_000".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14".to_string())));
        assert!(t.contains(&(kind::INT, "5L".to_string())));
        assert!(t.contains(&(kind::FLOAT, "1.5f".to_string())));
        assert!(t.contains(&(kind::FLOAT, "0x1.8p3".to_string())));
    }

    #[test]
    fn shift_operators_are_single_tokens() {
        let t = texts("a >>> b >>>= c");
        assert!(t.contains(&(kind::PUNCT, ">>>".to_string())));
        assert!(t.contains(&(kind::PUNCT, ">>>=".to_string())));
        assert!(t.iter().all(|(k, _)| *k != kind::ERROR));
    }

    #[test]
    fn dollar_is_identifier_char() {
        let t = texts("int $x = a$b;");
        assert!(t.contains(&(kind::IDENT, "$x".to_string())));
        assert!(t.contains(&(kind::IDENT, "a$b".to_string())));
    }

    #[test]
    fn block_comments_do_not_nest() {
        // Java block comments end at the first `*/`; the trailing `*/` is separate.
        let t = texts("/* a /* b */ c */");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::BLOCK_COMMENT && s == "/* a /* b */"));
    }
}
