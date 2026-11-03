//! Lossless Cypher (Neo4j query language) lexer.
//!
//! Cypher is a graph **query** language, so its surface is dominated by string
//! literals, pattern punctuators (`( ) [ ] { } - > < : | * .`), parameters
//! (`$x`), comments, and a case-insensitive keyword set — there is far less to
//! tokenize than a programming language, and that is expected.
//!
//! Guarantees (identical to the other front ends):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (whitespace, `//` line comments, `/* */` block comments) are emitted
//!   as `trivia` tokens, never discarded.
//! - Anything the lexer cannot classify becomes an `error` token covering the
//!   exact bytes. Input is never silently dropped.
//! - The main loop advances `pos` on every iteration (progress guard): a
//!   non-advancing branch would loop forever and exhaust memory.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_`, a pragmatic stand-in for the full Unicode
//! identifier tables. Anything outside it still lands in the tree as an `error`
//! token with its true span — a breadth gap, not a correctness lie.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// The Cypher keyword set. Cypher keywords are **case-insensitive**
/// (`MATCH`/`match`/`Match` are the same word), so [`is_keyword`] compares with
/// `eq_ignore_ascii_case`. The canonical spelling here is upper-case. Functions
/// and procedures (`count`, `toInteger`, `db.labels`) are deliberately *not*
/// keywords — they are detected as calls in the lowering instead.
pub const KEYWORDS: &[&str] = &[
    "MATCH",
    "OPTIONAL",
    "WHERE",
    "RETURN",
    "CREATE",
    "MERGE",
    "DELETE",
    "DETACH",
    "SET",
    "REMOVE",
    "WITH",
    "UNWIND",
    "CALL",
    "YIELD",
    "UNION",
    "ALL",
    "DISTINCT",
    "AS",
    "ORDER",
    "BY",
    "SKIP",
    "LIMIT",
    "ASC",
    "DESC",
    "ASCENDING",
    "DESCENDING",
    "AND",
    "OR",
    "XOR",
    "NOT",
    "IN",
    "STARTS",
    "ENDS",
    "CONTAINS",
    "IS",
    "NULL",
    "TRUE",
    "FALSE",
    "CASE",
    "WHEN",
    "THEN",
    "ELSE",
    "END",
    "ON",
    "FOREACH",
    "LOAD",
    "CSV",
    "FROM",
    "HEADERS",
    "FIELDTERMINATOR",
    "USING",
    "INDEX",
    "CONSTRAINT",
    "DROP",
    "EXISTS",
    "UNIQUE",
    "ASSERT",
    "REQUIRE",
    "FOR",
    "SCAN",
    "JOIN",
    "PERIODIC",
    "COMMIT",
    "PROFILE",
    "EXPLAIN",
    "MANDATORY",
    "OF",
    "ADD",
    "KEY",
    "DO",
];

/// Case-insensitive keyword test, as the Cypher grammar requires.
pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.iter().any(|kw| text.eq_ignore_ascii_case(kw))
}

/// Token kind labels. Stored on the CST as `&'static str`.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const LINE_COMMENT: &str = "line_comment";
    pub const BLOCK_COMMENT: &str = "block_comment";
    pub const IDENT: &str = "ident";
    /// A backtick-quoted name: `` `weird name` ``.
    pub const BACKTICK_IDENT: &str = "backtick_ident";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const STRING: &str = "string_literal";
    /// A query parameter: `$name` / `$0`.
    pub const PARAM: &str = "parameter";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
/// The pattern arrows (`-->`, `<--`, `-[…]->`) are intentionally *not* combined:
/// `<` and `>` are also comparison operators, so they stay single-character and
/// the parser/lowering reads pattern structure from the delimiter groups.
const OPERATORS: &[&str] = &["<=", ">=", "<>", "=~", "+=", "..", "||"];

const SINGLE_PUNCT: &str = "()[]{}-+*/%^=<>:|.,;!@&~?";

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
                c if c.is_whitespace() => {
                    self.eat_while(|c| c.is_whitespace());
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                '/' if self.peek_at(1) == Some('/') => self.line_comment(start),
                '/' if self.peek_at(1) == Some('*') => self.block_comment(start),
                '\'' => self.string_literal(start, '\''),
                '"' => self.string_literal(start, '"'),
                '`' => self.backtick_ident(start),
                '$' => self.parameter(start),
                c if is_ident_start(c) => self.ident(start),
                c if c.is_ascii_digit() => self.number(start),
                '.' if self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) => {
                    // A leading-dot float like `.5`.
                    self.number(start)
                }
                c if SINGLE_PUNCT.contains(c) => self.punct(start),
                _ => {
                    // Unknown byte/char — preserve it as an explicit error token.
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }
            // Progress guard: every branch above must have advanced `pos`. If a
            // future edit ever fails to, force one byte forward so the lexer can
            // never spin forever (OOM) on a fixed input.
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

    fn block_comment(&mut self, start: usize) {
        // Cypher block comments do not nest (C-style).
        self.pos += 2; // /*
        while self.pos < self.bytes.len() {
            if self.src[self.pos..].starts_with("*/") {
                self.pos += 2;
                break;
            }
            self.bump();
        }
        // Unterminated block comment is still trivia covering to EOF — lossless.
        self.push(kind::BLOCK_COMMENT, start, self.pos, true);
    }

    /// Scan a `'...'` or `"..."` string. Backslash escapes any next char. An
    /// unterminated literal becomes an error token over what was consumed.
    fn string_literal(&mut self, start: usize, quote: char) {
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

    /// Scan a backtick-quoted name `` `...` ``. A doubled backtick `` `` `` is an
    /// escaped literal backtick inside the name. Unterminated → error token.
    fn backtick_ident(&mut self, start: usize) {
        self.bump(); // opening `
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            if self.peek() == '`' {
                if self.peek_at(1) == Some('`') {
                    self.bump(); // escaped backtick (first)
                    self.bump(); // escaped backtick (second)
                    continue;
                }
                self.bump(); // closing `
                terminated = true;
                break;
            }
            self.bump();
        }
        let token_kind = if terminated {
            kind::BACKTICK_IDENT
        } else {
            kind::ERROR
        };
        self.push(token_kind, start, self.pos, false);
    }

    /// Scan a parameter `$name` / `$0`. A lone `$` (nothing nameable after) is
    /// still emitted as a parameter token so the byte is never dropped.
    fn parameter(&mut self, start: usize) {
        self.bump(); // $
        if starts_ident(Some(self.peek())) || self.peek().is_ascii_digit() {
            self.eat_while(is_ident_continue);
        }
        self.push(kind::PARAM, start, self.pos, false);
    }

    fn ident(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        self.push(kind::IDENT, start, self.pos, false);
    }

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        if self.peek() == '0' {
            match self.peek_at(1) {
                Some('x') | Some('X') => {
                    self.pos += 2;
                    self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
                    return self.push(kind::INT, start, self.pos, false);
                }
                Some('o') | Some('O') => {
                    self.pos += 2;
                    self.eat_while(|c| ('0'..='7').contains(&c) || c == '_');
                    return self.push(kind::INT, start, self.pos, false);
                }
                _ => {}
            }
        }
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        // Fractional part: a `.` followed by a digit (so `n.prop` and the range
        // `1..3` are not eaten as floats).
        if self.peek() == '.' && self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) {
            is_float = true;
            self.bump(); // .
            self.eat_while(|c| c.is_ascii_digit() || c == '_');
        }
        // Exponent.
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
    c == '_' || c.is_alphabetic()
}

fn is_ident_continue(c: char) -> bool {
    c == '_' || c.is_alphanumeric()
}

fn starts_ident(c: Option<char>) -> bool {
    c.map(is_ident_start).unwrap_or(false)
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
            "MATCH (n:Person) RETURN n",
            "// comment\nCREATE (a)-[:KNOWS]->(b)",
            "/* block */ MATCH (n {name: 'x'}) RETURN n.name",
            "WITH $param AS p RETURN p",
            "RETURN `weird ``name`` here`",
            "RETURN 1.5e3, 0xFF, .5, 1..3",
            "λ ☃ €", // non-ascii idents / unknowns still covered
            "",
            "$",
            "'unterminated",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn keywords_are_case_insensitive() {
        assert!(is_keyword("MATCH"));
        assert!(is_keyword("match"));
        assert!(is_keyword("Match"));
        assert!(!is_keyword("count"));
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("MATCH (n:Person) RETURN $id");
        assert!(t.contains(&(kind::IDENT, "MATCH".to_string())));
        assert!(t.contains(&(kind::IDENT, "Person".to_string())));
        assert!(t.contains(&(kind::PARAM, "$id".to_string())));
        assert!(t.contains(&(kind::PUNCT, ":".to_string())));
    }

    #[test]
    fn backtick_name_with_escaped_backtick() {
        let t = texts("RETURN `a``b`");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::BACKTICK_IDENT && s == "`a``b`"));
    }

    #[test]
    fn range_dots_are_not_a_float() {
        let t = texts("1..3");
        assert_eq!(
            t,
            vec![
                (kind::INT, "1".to_string()),
                (kind::PUNCT, "..".to_string()),
                (kind::INT, "3".to_string()),
            ]
        );
    }
}
