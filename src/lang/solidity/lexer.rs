//! Lossless Solidity lexer, grounded in the Solidity language grammar.
//!
//! Guarantees (identical contract to the Rust, Python, and Java lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (whitespace, `//` line comments incl. `///` NatSpec, `/* */` and
//!   `/** */` block comments) are emitted as `trivia` tokens, not discarded — the
//!   parser skips them for structure but the tree keeps them.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//! - The main run loop has an explicit progress guard: every iteration advances
//!   `pos` by at least one byte, so the lexer can never spin (which would OOM).
//!
//! Solidity surface covered: `//`/`///` line comments, `/* */`/`/** */` block
//! comments (Solidity block comments do **not** nest), `"..."` and `'...'`
//! strings (both are string literals in Solidity, unlike C/Java where `'…'` is a
//! char), decimal and `0x` hex integer literals with `_` digit separators and
//! scientific notation (`2e10`), and the operator/punctuation set including the
//! mapping arrow `=>` and the power operator `**`. Denomination/time units
//! (`ether`, `wei`, `days`, …) lex as ordinary identifiers and are classified by
//! the parser/lowering via [`is_keyword`]; a `hex"…"` / `unicode"…"` prefix lexes
//! as an identifier followed by a normal string — both lossless.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_` and `$` (both legal in Solidity identifiers) as a
//! pragmatic stand-in for the full Unicode identifier tables. Anything outside it
//! still lands in the tree as a covered token, never dropped.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Solidity reserved/keyword set, plus the boolean literals and the
/// denomination/time units. Like the Java lexer these lex as `ident` tokens; the
/// parser and lowering distinguish them via [`is_keyword`]. Contextual words used
/// only inside `import` (`from`, `as`) are deliberately excluded so they keep
/// working as ordinary identifiers; the parser recognizes structure by position.
pub const KEYWORDS: &[&str] = &[
    // directives & declarations
    "pragma",
    "import",
    "using",
    "contract",
    "interface",
    "library",
    "abstract",
    "is",
    "function",
    "constructor",
    "modifier",
    "fallback",
    "receive",
    "event",
    "error",
    "struct",
    "enum",
    "mapping",
    "type",
    // signature / visibility / mutability
    "returns",
    "return",
    "public",
    "private",
    "internal",
    "external",
    "pure",
    "view",
    "payable",
    "nonpayable",
    "virtual",
    "override",
    "memory",
    "storage",
    "calldata",
    "constant",
    "immutable",
    "anonymous",
    "indexed",
    // statements / built-ins
    "new",
    "delete",
    "emit",
    "if",
    "else",
    "while",
    "do",
    "for",
    "break",
    "continue",
    "try",
    "catch",
    "throw",
    "revert",
    "require",
    "assert",
    "assembly",
    "unchecked",
    // common value types
    "address",
    "bool",
    "string",
    "bytes",
    "byte",
    "int",
    "uint",
    "fixed",
    "ufixed",
    // literals
    "true",
    "false",
    // denomination & time units
    "wei",
    "gwei",
    "ether",
    "seconds",
    "minutes",
    "hours",
    "days",
    "weeks",
    "years",
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
    pub const STRING: &str = "string_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
/// `>>=` (3) precedes `>>` (2); `**=` precedes `**`; `=>` is the mapping arrow.
const OPERATORS: &[&str] = &[
    ">>=", "<<=", "**=", "==", "!=", "<=", ">=", "&&", "||", "++", "--", "+=", "-=", "*=", "/=",
    "%=", "&=", "|=", "^=", "=>", "**", "<<", ">>",
];

const SINGLE_PUNCT: &str = "+-*/%!&|^~<>=.,;:()[]{}?";

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
                '"' | '\'' => self.string(start, c),
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
            // Progress guard: every iteration MUST advance `pos`. If a branch
            // somehow consumed nothing, force one byte forward as an error token
            // rather than spin forever (a non-advancing loop would OOM).
            if self.pos == start {
                self.bump();
                self.push(kind::ERROR, start, self.pos, false);
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

    /// `/* ... */` (and `/** ... */` NatSpec). Solidity block comments do not nest.
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

    /// Scan a `"..."` or `'...'` string literal (both are strings in Solidity).
    /// Honors backslash escapes; ends at the matching unescaped quote. An
    /// unterminated literal (newline or EOF) becomes an `error` token over what
    /// was consumed, never a silent drop.
    fn string(&mut self, start: usize, quote: char) {
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

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        // Hexadecimal: `0x...` with optional `_` separators.
        if self.peek() == '0' && matches!(self.peek_at(1), Some('x') | Some('X')) {
            self.pos += 2;
            self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
            return self.push(kind::INT, start, self.pos, false);
        }
        // Decimal integer part.
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        // Fractional part only if a digit follows the dot, so member access like
        // `1.foo` stays split into separate tokens.
        if self.peek() == '.' && self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) {
            is_float = true;
            self.bump();
            self.eat_while(|c| c.is_ascii_digit() || c == '_');
        }
        // Scientific notation `2e10`, `1.5e-3`.
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
            "contract A {}",
            "uint x = 1_000;",
            "// note\nuint y = 0xFF_00;",
            "/* block *//** natspec */ x",
            "string s = \"hi\\n\";",
            "string s = 'single';",
            "uint t = 2 ether; uint d = 3 days;",
            "mapping(address => uint) public balances;",
            "a >>= b; c ** d; e <<= f;",
            "uint d = 1.5e3; uint g = 2e10;",
            "λ ☃ €", // non-ascii idents / unknowns still covered
            "pragma solidity ^0.8.0;",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("function add(uint a) public returns (uint) {}");
        assert!(t.contains(&(kind::IDENT, "function".to_string())));
        assert!(t.contains(&(kind::IDENT, "add".to_string())));
        assert!(t.contains(&(kind::PUNCT, "(".to_string())));
        assert!(is_keyword("function"));
        assert!(is_keyword("contract"));
        assert!(!is_keyword("add"));
        // `from`/`as` stay ordinary identifiers.
        assert!(!is_keyword("from"));
        assert!(!is_keyword("as"));
    }

    #[test]
    fn single_quote_is_a_string() {
        let t = texts("string s = 'abc';");
        assert!(t.contains(&(kind::STRING, "'abc'".to_string())));
    }

    #[test]
    fn numbers() {
        let t = texts("0xAF 10_000 3.14 2e10 0xdead_beef");
        assert!(t.contains(&(kind::INT, "0xAF".to_string())));
        assert!(t.contains(&(kind::INT, "10_000".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14".to_string())));
        assert!(t.contains(&(kind::FLOAT, "2e10".to_string())));
        assert!(t.contains(&(kind::INT, "0xdead_beef".to_string())));
    }

    #[test]
    fn mapping_arrow_and_power_are_single_tokens() {
        let t = texts("mapping(uint => uint) m; uint p = a ** b;");
        assert!(t.contains(&(kind::PUNCT, "=>".to_string())));
        assert!(t.contains(&(kind::PUNCT, "**".to_string())));
        assert!(t.iter().all(|(k, _)| *k != kind::ERROR));
    }

    #[test]
    fn dollar_is_identifier_char() {
        let t = texts("uint $x = a$b;");
        assert!(t.contains(&(kind::IDENT, "$x".to_string())));
        assert!(t.contains(&(kind::IDENT, "a$b".to_string())));
    }

    #[test]
    fn block_comments_do_not_nest() {
        // Solidity block comments end at the first `*/`; the trailing `*/` is separate.
        let t = texts("/* a /* b */ c */");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::BLOCK_COMMENT && s == "/* a /* b */"));
    }

    #[test]
    fn unterminated_string_is_error_not_dropped() {
        let t = texts("string s = \"oops\n");
        assert!(t.iter().any(|(k, _)| *k == kind::ERROR));
        assert!(covers_all("string s = \"oops\n"));
    }
}
