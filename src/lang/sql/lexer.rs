//! Lossless SQL lexer, grounded in the common ANSI/dialect token grammar.
//!
//! Guarantees:
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (whitespace, `--` line comments, `/* */` block comments) are emitted
//!   as `trivia` tokens, not discarded — the parser skips them for structure but
//!   the tree keeps them.
//! - Anything the lexer cannot classify becomes an `error` token covering the
//!   exact bytes. Input is never silently dropped.
//! - The main run loop advances `pos` on every iteration; a final progress guard
//!   consumes one char as `error` if (defensively) no scanner moved, so a
//!   pathological byte can never spin the loop forever.
//!
//! SQL is a multi-dialect family; this lexer stays deliberately coarse but
//! honest. It handles `'...'` strings (with doubled-quote `''` escape), the three
//! quoted-identifier forms (`"..."`, `` `...` ``, `[...]`, each with its doubled
//! escape), Postgres dollar-quoted strings (`$tag$...$tag$`, empty tag allowed),
//! numbers (incl. `0x` hex and exponents), and `--` / `/* */` comments (block
//! comments nest, as in Postgres). Keywords are case-insensitive and recognised
//! by the parser via [`is_keyword`], not baked into token kinds.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_`, a pragmatic stand-in for full dialect identifier
//! rules. Dialect-specific identifier sigils (`@var`, `#temp`, `:name`) are lexed
//! as a punct sigil followed by an `ident`, and MySQL backslash string escapes
//! are *not* treated as escapes (standard doubled-quote escaping only). None of
//! these is a losslessness lie: every byte still lands in the tree on its true
//! span.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// A representative set of SQL clause / statement keywords across common
/// dialects, matched case-insensitively (see [`is_keyword`]). Intentionally does
/// **not** list built-in function names (e.g. `count`, `now`, `coalesce`) so that
/// genuine function-call sites still resolve through the lowering pass.
pub const KEYWORDS: &[&str] = &[
    "add",
    "all",
    "alter",
    "and",
    "as",
    "asc",
    "authorization",
    "before",
    "begin",
    "between",
    "by",
    "cascade",
    "case",
    "cast",
    "check",
    "column",
    "constraint",
    "create",
    "cross",
    "database",
    "declare",
    "default",
    "delete",
    "desc",
    "distinct",
    "drop",
    "each",
    "else",
    "end",
    "exists",
    "for",
    "foreign",
    "from",
    "full",
    "function",
    "global",
    "grant",
    "group",
    "having",
    "if",
    "in",
    "index",
    "inner",
    "inout",
    "insert",
    "instead",
    "into",
    "is",
    "join",
    "key",
    "language",
    "left",
    "like",
    "limit",
    "local",
    "materialized",
    "not",
    "null",
    "of",
    "offset",
    "on",
    "or",
    "order",
    "out",
    "outer",
    "primary",
    "procedure",
    "recursive",
    "references",
    "replace",
    "return",
    "returns",
    "right",
    "row",
    "schema",
    "select",
    "sequence",
    "set",
    "table",
    "temp",
    "temporary",
    "then",
    "to",
    "trigger",
    "type",
    "union",
    "unique",
    "unlogged",
    "update",
    "using",
    "values",
    "view",
    "when",
    "where",
    "with",
];

/// Case-insensitive keyword test, per the SQL standard (`SELECT` == `select`).
pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.iter().any(|k| k.eq_ignore_ascii_case(text))
}

/// Token kind labels. Stored on the CST as `&'static str` so the tree stays
/// uniform and JSON-friendly.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const LINE_COMMENT: &str = "line_comment";
    pub const BLOCK_COMMENT: &str = "block_comment";
    pub const IDENT: &str = "ident";
    pub const QUOTED_IDENT: &str = "quoted_ident";
    pub const STRING: &str = "string_literal";
    pub const NUMBER: &str = "number_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
/// Covers ANSI plus common Postgres JSON/cast/concat operators.
const OPERATORS: &[&str] = &[
    "->>", "#>>", "->", "#>", "@>", "<@", "||", "::", ":=", "<=", ">=", "<>", "!=", "==", "<<",
    ">>", "=>", "&&",
];

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
                '-' if self.peek_at(1) == Some('-') => self.line_comment(start),
                '/' if self.peek_at(1) == Some('*') => self.block_comment(start),
                '\'' => self.quoted(start, '\'', kind::STRING),
                '"' => self.quoted(start, '"', kind::QUOTED_IDENT),
                '`' => self.quoted(start, '`', kind::QUOTED_IDENT),
                '[' => self.bracket_quoted(start),
                '$' if self.dollar_tag_len(start).is_some() => self.dollar_quote(start),
                c if is_ident_start(c) => self.ident(start),
                c if c.is_ascii_digit() => self.number(start),
                '.' if self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) => {
                    self.number(start)
                }
                c if is_punct(c) => self.punct(start),
                _ => {
                    // Unknown byte/char — preserve it as an explicit error token.
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }

            // Main-run-loop progress guard: every scanner above advances `pos`,
            // but if (defensively) none did, consume exactly one char as an error
            // token so the loop can never spin without making progress.
            if self.pos == start {
                self.bump();
                if self.pos == start {
                    // Zero-length char at EOF boundary; force a byte to stay safe.
                    self.pos = (start + 1).min(self.bytes.len());
                }
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
        // SQL block comments nest in Postgres; nest uniformly for safety.
        self.pos += 2; // /*
        let mut depth = 1usize;
        while self.pos < self.bytes.len() && depth > 0 {
            if self.src[self.pos..].starts_with("/*") {
                depth += 1;
                self.pos += 2;
            } else if self.src[self.pos..].starts_with("*/") {
                depth -= 1;
                self.pos += 2;
            } else {
                self.bump();
            }
        }
        // Unterminated block comment is still trivia covering to EOF — lossless.
        self.push(kind::BLOCK_COMMENT, start, self.pos, true);
    }

    fn ident(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        self.push(kind::IDENT, start, self.pos, false);
    }

    /// Scan a delimiter-quoted run where the closing delimiter equals the opening
    /// one and is escaped by doubling it: `'...''...'`, `"..."`, `` `...` ``.
    /// Unterminated → an error token covering what was consumed (still lossless).
    fn quoted(&mut self, start: usize, q: char, k: &'static str) {
        self.bump(); // opening delimiter
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == q {
                if self.peek_at(1) == Some(q) {
                    // Doubled delimiter is an escaped literal; stay inside.
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
        let tok = if terminated { k } else { kind::ERROR };
        self.push(tok, start, self.pos, false);
    }

    /// Scan a SQL-Server bracket-quoted identifier `[...]`; `]]` escapes a `]`.
    fn bracket_quoted(&mut self, start: usize) {
        self.bump(); // [
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == ']' {
                if self.peek_at(1) == Some(']') {
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
        let tok = if terminated {
            kind::QUOTED_IDENT
        } else {
            kind::ERROR
        };
        self.push(tok, start, self.pos, false);
    }

    /// Length in bytes of a Postgres dollar-quote opening delimiter `$tag$` at
    /// `start` (the `$`), or `None` if this `$` does not open one. The tag is an
    /// optional identifier (letter/underscore start; empty tag `$$` allowed) and
    /// may not contain `$`. This keeps positional params like `$1` as a plain
    /// punct `$` followed by a number.
    fn dollar_tag_len(&self, start: usize) -> Option<usize> {
        let mut i = start + 1;
        let mut first = true;
        loop {
            let ch = self.src.get(i..)?.chars().next()?;
            if ch == '$' {
                return Some(i + 1 - start);
            }
            let ok = if first {
                is_ident_start(ch)
            } else {
                is_ident_continue(ch)
            };
            if !ok {
                return None;
            }
            i += ch.len_utf8();
            first = false;
        }
    }

    fn dollar_quote(&mut self, start: usize) {
        let open_len = self.dollar_tag_len(start).expect("checked by caller");
        let delim = self.src[start..start + open_len].to_string(); // owned: "$tag$"
        self.pos = start + open_len;
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            if self.src[self.pos..].starts_with(&delim) {
                self.pos += delim.len();
                terminated = true;
                break;
            }
            self.bump();
        }
        let tok = if terminated {
            kind::STRING
        } else {
            kind::ERROR
        };
        self.push(tok, start, self.pos, false);
    }

    fn number(&mut self, start: usize) {
        // Hex literal `0x...` (SQL Server / MySQL).
        if self.peek() == '0' && matches!(self.peek_at(1), Some('x') | Some('X')) {
            self.pos += 2;
            self.eat_while(|c| c.is_ascii_hexdigit());
            self.push(kind::NUMBER, start, self.pos, false);
            return;
        }
        self.eat_while(|c| c.is_ascii_digit());
        if self.peek() == '.' {
            self.bump(); // .
            self.eat_while(|c| c.is_ascii_digit());
        }
        if matches!(self.peek(), 'e' | 'E') {
            let sign_len = match self.peek_at(1) {
                Some('+') | Some('-') => 1,
                _ => 0,
            };
            let digit_after = self
                .src
                .get(self.pos + 1 + sign_len..)
                .and_then(|s| s.chars().next())
                .map(|c| c.is_ascii_digit())
                .unwrap_or(false);
            if digit_after {
                self.bump(); // e
                if sign_len == 1 {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit());
            }
        }
        self.push(kind::NUMBER, start, self.pos, false);
    }

    fn punct(&mut self, start: usize) {
        for op in OPERATORS {
            if self.src[self.pos..].starts_with(op) {
                self.pos += op.len();
                self.push(kind::PUNCT, start, self.pos, false);
                return;
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

/// ASCII punctuation SQL uses. Quote/bracket/dollar openers are intercepted by
/// the run loop before reaching here; they appear in this set only as a defensive
/// fallback (e.g. a stray closing `]`).
fn is_punct(c: char) -> bool {
    matches!(
        c,
        '+' | '-'
            | '*'
            | '/'
            | '%'
            | '<'
            | '>'
            | '='
            | '~'
            | '!'
            | '&'
            | '|'
            | '^'
            | '?'
            | '$'
            | '@'
            | '#'
            | '('
            | ')'
            | ';'
            | ','
            | '.'
            | ':'
            | '{'
            | '}'
            | ']'
    )
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
            "SELECT * FROM t;",
            "-- a comment\nCREATE TABLE x (id int);",
            "/* nested /* block */ */ SELECT 1",
            "SELECT 'it''s ok', \"Quoted\", `back`, [bracket];",
            "CREATE FUNCTION f() RETURNS int AS $$ SELECT 1; $$ LANGUAGE sql;",
            "SELECT $1, 1.5e3, 0xFF, a->>'b', c::int;",
            "SELECT 'unterminated",
            "λ ☃ €", // non-ascii idents / unknowns still covered
            "",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("SELECT id FROM t");
        assert!(t.contains(&(kind::IDENT, "SELECT".to_string())));
        assert!(t.contains(&(kind::IDENT, "id".to_string())));
        assert!(is_keyword("select"));
        assert!(is_keyword("SELECT"));
        assert!(!is_keyword("count"));
    }

    #[test]
    fn string_doubled_quote_escape() {
        let t = texts("'it''s'");
        assert_eq!(t, vec![(kind::STRING, "'it''s'".to_string())]);
    }

    #[test]
    fn quoted_identifier_forms() {
        let t = texts("\"a\" `b` [c]");
        assert!(t.contains(&(kind::QUOTED_IDENT, "\"a\"".to_string())));
        assert!(t.contains(&(kind::QUOTED_IDENT, "`b`".to_string())));
        assert!(t.contains(&(kind::QUOTED_IDENT, "[c]".to_string())));
    }

    #[test]
    fn dollar_quote_vs_param() {
        let t = texts("$body$ x; $body$");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "$body$ x; $body$"));
        // A positional parameter is a punct `$` then a number, not a dollar quote.
        let p = texts("$1");
        assert_eq!(
            p,
            vec![
                (kind::PUNCT, "$".to_string()),
                (kind::NUMBER, "1".to_string()),
            ]
        );
    }

    #[test]
    fn empty_tag_dollar_quote() {
        let t = texts("$$abc$$");
        assert_eq!(t, vec![(kind::STRING, "$$abc$$".to_string())]);
    }

    #[test]
    fn number_forms() {
        let t = texts("1 1.5 1.5e-3 0xAF .25");
        assert!(t.contains(&(kind::NUMBER, "1".to_string())));
        assert!(t.contains(&(kind::NUMBER, "1.5".to_string())));
        assert!(t.contains(&(kind::NUMBER, "1.5e-3".to_string())));
        assert!(t.contains(&(kind::NUMBER, "0xAF".to_string())));
        assert!(t.contains(&(kind::NUMBER, ".25".to_string())));
    }
}
