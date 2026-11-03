//! Lossless Apex lexer, forked from the Java lexer ([`crate::lang::java::lexer`]).
//!
//! Apex is Java-derived, so the token grammar is almost identical. The Apex-
//! specific deviations handled here:
//! - **Case-insensitive keywords.** Apex keywords match regardless of case
//!   (`Public`, `WITH`, `Select`), so [`is_keyword`] compares case-insensitively
//!   and the parser/lowering do the same. Tokens still carry their exact bytes —
//!   losslessness is untouched.
//! - **Single-quoted strings.** Apex has no `char` type; `'...'` is a *string*
//!   literal (used heavily in inline SOQL/SOSL), not a char literal. It is lexed
//!   as a [`kind::STRING`] token.
//! - **Inline SOQL/SOSL** (`[SELECT Id FROM Contact]`) needs no special lexing:
//!   `[` / `]` are ordinary punctuation and the parser captures the query as a
//!   balanced `Bracket` token tree. The lowering's second pass reads the SObject
//!   out of that tree.
//!
//! Every other guarantee is inherited verbatim: contiguous spans (byte-for-byte
//! round-trip), trivia preserved, unknown bytes preserved as `error` tokens, and
//! a progress-guarded contiguous scan.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Apex's reserved keywords, plus the boolean/null literals. Stored lowercase;
/// [`is_keyword`] matches case-insensitively. Apex *system types* (`String`,
/// `List`, `Map`, `Integer`, `Id`, `SObject`, …) are intentionally **not**
/// keywords — they are ordinary identifiers, so they still resolve/participate
/// as type references. The SOQL/SOSL clause words that only ever appear inside a
/// bracketed query (`where`, `limit`, `order`, …) are likewise omitted: those
/// token trees are interpreted by the lowering's dedicated SOQL pass, not by the
/// keyword table.
pub const KEYWORDS: &[&str] = &[
    "abstract",
    "after",
    "and",
    "before",
    "break",
    "catch",
    "class",
    "continue",
    "delete",
    "do",
    "else",
    "enum",
    "extends",
    "final",
    "finally",
    "for",
    "from",
    "global",
    "if",
    "implements",
    "import",
    "inherited",
    "insert",
    "instanceof",
    "interface",
    "like",
    "merge",
    "new",
    "not",
    "on",
    "or",
    "override",
    "private",
    "protected",
    "public",
    "return",
    "returning",
    "select",
    "sharing",
    "static",
    "super",
    "switch",
    "testmethod",
    "this",
    "throw",
    "transient",
    "trigger",
    "try",
    "undelete",
    "update",
    "upsert",
    "virtual",
    "void",
    "webservice",
    "when",
    "while",
    "with",
    "without",
    // Literals — reserved, never identifiers.
    "true",
    "false",
    "null",
];

/// Case-insensitive keyword test (Apex keywords are case-insensitive).
pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.iter().any(|k| k.eq_ignore_ascii_case(text))
}

/// Token kind labels. Stored on the CST as `&'static str`.
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
                '\'' => self.string_single(start),
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

    /// `/* ... */` (and `/** ... */` ApexDoc). Block comments do not nest.
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

    /// `'...'` Apex string literal. Handles backslash escapes; ends at the
    /// closing quote. An unescaped newline or EOF terminates it as an `error`
    /// token over what was consumed (still lossless).
    fn string_single(&mut self, start: usize) {
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
        if self.peek() == '0' && matches!(self.peek_at(1), Some('x') | Some('X')) {
            self.pos += 2;
            self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
            self.eat_number_suffix();
            return self.push(kind::INT, start, self.pos, false);
        }
        // Decimal.
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        // Fractional part only if a digit follows the dot, so `1.method()` stays split.
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
    /// makes the literal floating-point (`d`/`D` for `Double`/`Decimal`); `l`/`L`
    /// is the `Long` suffix and returns `false`.
    fn eat_number_suffix(&mut self) -> bool {
        match self.peek() {
            'l' | 'L' => {
                self.bump();
                false
            }
            'd' | 'D' | 'f' | 'F' => {
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
            "public with sharing class A {}",
            "Integer x = 1_000;",
            "// comment\nList<Contact> cs = [SELECT Id FROM Contact];",
            "/* block *//** doc */ x",
            "String s = 'hi\\n' + 'c';",
            "trigger T on Contact (before insert, after update) {}",
            "@InvocableMethod(label='go') public static void m() {}",
            "λ ☃ €", // non-ascii idents / unknowns still covered
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn keywords_are_case_insensitive() {
        assert!(is_keyword("public"));
        assert!(is_keyword("PUBLIC"));
        assert!(is_keyword("Public"));
        assert!(is_keyword("with"));
        assert!(is_keyword("SHARING"));
        assert!(is_keyword("Trigger"));
        assert!(!is_keyword("Contact"));
        // System types are identifiers, not keywords.
        assert!(!is_keyword("String"));
        assert!(!is_keyword("List"));
    }

    #[test]
    fn single_quotes_are_strings() {
        let t = texts("String s = 'hello world';");
        assert!(t.contains(&(kind::STRING, "'hello world'".to_string())));
        assert!(t.iter().all(|(k, _)| *k != kind::ERROR));
    }

    #[test]
    fn inline_soql_lexes_as_ordinary_tokens() {
        // The bracket contents are plain idents/punct; the parser groups them.
        let t = texts("[SELECT Id FROM Contact]");
        assert!(t.contains(&(kind::PUNCT, "[".to_string())));
        assert!(t.contains(&(kind::IDENT, "SELECT".to_string())));
        assert!(t.contains(&(kind::IDENT, "Contact".to_string())));
        assert!(t.contains(&(kind::PUNCT, "]".to_string())));
    }

    #[test]
    fn numbers() {
        let t = texts("0xAF 10_000 3.14 2e10 5L 1.5");
        assert!(t.contains(&(kind::INT, "0xAF".to_string())));
        assert!(t.contains(&(kind::INT, "10_000".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14".to_string())));
        assert!(t.contains(&(kind::INT, "5L".to_string())));
    }
}
