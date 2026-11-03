//! Lossless Groovy lexer, grounded in the Groovy language grammar (and its
//! Gradle DSL dialect, which is plain Groovy).
//!
//! Guarantees (identical contract to the Rust, Java, and Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (whitespace, `//` line comments, `/* */` block comments) are emitted
//!   as `trivia` tokens, not discarded — the parser skips them for structure but
//!   the tree keeps them.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//! - The main run loop advances `pos` on **every** iteration: each scanner
//!   consumes at least one byte, and a final progress guard force-consumes one
//!   byte as an `error` token if (defensively) nothing else did. A non-advancing
//!   loop would spin forever and OOM, so this is load-bearing.
//!
//! Groovy surface covered: `//` line comments, `/* */` block comments (Groovy
//! block comments do **not** nest, like Java), single `'...'` and double `"..."`
//! strings, triple `'''...'''` and `"""..."""` strings (multi-line), slashy
//! `/.../` strings, dollar-slashy `$/.../$` strings, GString `${...}`
//! interpolation (brace-balanced so an embedded `}` or quote does not end the
//! string early), decimal/hex/binary integers and floats with `_` separators and
//! the `lLfFdDgGiI` suffixes, identifiers/keywords, and the Groovy operator set
//! (`?.`, `*.`, `<=>`, `==~`, `=~`, `..`, `..<`, `->`, `?:`, `*:`, `**`, `.&`,
//! `.@`, `::`, `>>>`, …).
//!
//! Slashy strings vs. division: a bare `/` is genuinely ambiguous (it can open a
//! slashy string or be the division operator). We resolve it with the standard
//! value/operator heuristic — a `/` that follows a value (identifier, literal, or
//! a closing `)`/`]`/`}`) is division; otherwise it opens a slashy string. A
//! wrong guess is only a *classification* difference, never a loss: the bytes are
//! covered identically either way.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_` and `$` (both legal in Groovy identifiers) as a
//! pragmatic stand-in for the full Unicode identifier tables. Anything outside it
//! still lands in the tree as a covered token, never dropped.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Groovy's reserved keywords plus the boolean/null literals and the Groovy
/// additions (`def`, `as`, `in`, `trait` is deliberately omitted — it is a
/// *contextual* keyword the parser recognizes by position so it keeps working as
/// an ordinary identifier). These lex as `ident` tokens; the parser and lowering
/// distinguish them via [`is_keyword`].
pub const KEYWORDS: &[&str] = &[
    "abstract",
    "as",
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
    "def",
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
    "in",
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
    pub const STRING: &str = "string_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
const OPERATORS: &[&str] = &[
    ">>>=", "==~", "<=>", "**=", "...", "..<", ">>>", "<<=", ">>=", "=~", "?.", "*.", ".&", ".@",
    "?:", "*:", "..", "**", "->", "::", "==", "!=", "<=", ">=", "&&", "||", "++", "--", "+=", "-=",
    "*=", "/=", "%=", "&=", "|=", "^=", "<<", ">>",
];

const SINGLE_PUNCT: &str = "+-*/%!&|^~<>=.,;:()[]{}@?$";

pub fn lex(source: &str) -> Vec<Token> {
    Lexer::new(source).run()
}

struct Lexer<'s> {
    src: &'s str,
    bytes: &'s [u8],
    pos: usize,
    tokens: Vec<Token>,
    /// True when the previous significant token could end an expression (an
    /// identifier that is not a keyword, a literal, or a closing `)`/`]`/`}`).
    /// Drives the slashy-string-vs-division decision.
    prev_value: bool,
}

impl<'s> Lexer<'s> {
    fn new(src: &'s str) -> Self {
        Lexer {
            src,
            bytes: src.as_bytes(),
            pos: 0,
            tokens: Vec::new(),
            prev_value: false,
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
                // Dollar-slashy string `$/ ... /$`.
                '$' if self.peek_at(1) == Some('/') => self.dollar_slashy(start),
                '\'' => {
                    if self.peek_at(1) == Some('\'') && self.peek_at(2) == Some('\'') {
                        self.triple_string(start, '\'', false);
                    } else {
                        self.quoted_string(start, '\'', false);
                    }
                }
                '"' => {
                    if self.peek_at(1) == Some('"') && self.peek_at(2) == Some('"') {
                        self.triple_string(start, '"', true);
                    } else {
                        self.quoted_string(start, '"', true);
                    }
                }
                // Slashy string `/ ... /` — only when a value is *not* expected
                // before it (otherwise `/` is division, handled by `punct`).
                '/' if !self.prev_value => self.slashy(start),
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

            // Progress guard: every iteration MUST advance. If some arm
            // defensively failed to consume a byte, force one as an error token
            // so the loop can never spin forever.
            if self.pos == start {
                self.bump();
                self.push(kind::ERROR, start, self.pos, false);
            }

            // Update the value/operator state from the just-pushed token.
            if let Some(t) = self.tokens.last() {
                if !t.trivia {
                    self.prev_value = token_is_value(t.kind, t.span.text(self.src));
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

    /// `/* ... */` (and `/** ... */` Groovydoc). Groovy block comments do not nest.
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

    /// A single-line `'...'` / `"..."` string. `interpolate` enables GString
    /// `${...}` brace-balanced consumption (double quotes only). An unterminated
    /// literal (newline / EOF before the close) becomes an error token.
    fn quoted_string(&mut self, start: usize, quote: char, interpolate: bool) {
        self.bump(); // opening quote
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '\\' {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
            } else if interpolate && c == '$' && self.peek_at(1) == Some('{') {
                self.consume_brace_interp();
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

    /// A triple-quoted string `'''...'''` / `"""..."""`, spanning newlines.
    fn triple_string(&mut self, start: usize, quote: char, interpolate: bool) {
        self.pos += 3; // opening triple quote
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '\\' {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
            } else if interpolate && c == '$' && self.peek_at(1) == Some('{') {
                self.consume_brace_interp();
            } else if c == quote && self.peek_at(1) == Some(quote) && self.peek_at(2) == Some(quote)
            {
                self.pos += 3;
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

    /// A slashy string `/ ... /` (single-line). Backslash escapes and `${...}`
    /// interpolation are honored; a newline before the close means this was not a
    /// slashy string after all, so the consumed bytes become an error token.
    fn slashy(&mut self, start: usize) {
        self.bump(); // opening /
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '\\' {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
            } else if c == '$' && self.peek_at(1) == Some('{') {
                self.consume_brace_interp();
            } else if c == '/' {
                self.bump();
                terminated = true;
                break;
            } else if c == '\n' {
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

    /// A dollar-slashy string `$/ ... /$` (multi-line). Ends at the `/$` sequence.
    fn dollar_slashy(&mut self, start: usize) {
        self.pos += 2; // opening $/
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            if self.src[self.pos..].starts_with("/$") {
                self.pos += 2;
                terminated = true;
                break;
            }
            let c = self.peek();
            if c == '$' && self.peek_at(1) == Some('{') {
                self.consume_brace_interp();
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

    /// Consume a GString interpolation `${ ... }`, balancing nested braces so an
    /// embedded `}` does not terminate the surrounding string early. Positioned at
    /// the `$`; consumes `${` then to the matching `}` (or EOF).
    fn consume_brace_interp(&mut self) {
        self.bump(); // $
        self.bump(); // {
        let mut depth = 1usize;
        while self.pos < self.bytes.len() && depth > 0 {
            let c = self.peek();
            if c == '\\' {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
            } else if c == '{' {
                depth += 1;
                self.bump();
            } else if c == '}' {
                depth -= 1;
                self.bump();
            } else {
                self.bump();
            }
        }
    }

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        if self.peek() == '0' && matches!(self.peek_at(1), Some('x') | Some('X')) {
            self.pos += 2;
            self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
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
        // range-like constructs (`1..2`) stay split.
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
    /// makes the literal floating-point (`f`/`F`/`d`/`D`/`g`/`G` — BigDecimal);
    /// `l`/`L` (long) and `i`/`I` (Integer) return `false`.
    fn eat_number_suffix(&mut self) -> bool {
        match self.peek() {
            'l' | 'L' | 'i' | 'I' => {
                self.bump();
                false
            }
            'f' | 'F' | 'd' | 'D' | 'g' | 'G' => {
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

/// Whether a significant token can end an expression (so a following `/` is
/// division, not a slashy string).
fn token_is_value(tok_kind: &str, text: &str) -> bool {
    match tok_kind {
        kind::INT | kind::FLOAT | kind::STRING => true,
        kind::IDENT => !is_keyword(text),
        kind::PUNCT => matches!(text, ")" | "]" | "}"),
        _ => false,
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
            "def x = 1_000",
            "// comment\nlong y = 0xFF_00L",
            "/* block *//** groovydoc */ x",
            "def s = \"hi ${name}\\n\" + 'c'",
            "def t = '''\nmulti\nline'''",
            "def u = \"\"\"a ${b} c\"\"\"",
            "def p = /foo\\/bar/",
            "def q = $/a $x /$",
            "a >>> b; c <=> d; e ==~ f; g =~ h",
            "list*.name; obj?.prop; obj.&method",
            "x in 1..10; y in 0..<5",
            "def cl = { a, b -> a + b }",
            "double d = 1.5e3; def g = 3.14G",
            "λ ☃ €", // non-ascii idents / unknowns still covered
            "task hello { doLast { println 'hi' } }",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("def add(int a) { return a }");
        assert!(t.contains(&(kind::IDENT, "def".to_string())));
        assert!(t.contains(&(kind::IDENT, "add".to_string())));
        assert!(t.contains(&(kind::PUNCT, "(".to_string())));
        assert!(is_keyword("def"));
        assert!(is_keyword("class"));
        assert!(!is_keyword("add"));
        // `trait` is contextual — stays an identifier at the lexer level.
        assert!(!is_keyword("trait"));
    }

    #[test]
    fn slashy_vs_division() {
        // After a value, `/` is division.
        let t = texts("a / b");
        assert!(t.contains(&(kind::PUNCT, "/".to_string())));
        // After `=` (no value), `/` opens a slashy string.
        let t2 = texts("def r = /ab+/");
        assert!(t2.iter().any(|(k, s)| *k == kind::STRING && s == "/ab+/"));
    }

    #[test]
    fn gstring_interpolation_balances_braces() {
        // The `}` inside the closure must not end the string early.
        let t = texts("\"${ [1,2].collect { it } }\"");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "\"${ [1,2].collect { it } }\""));
    }

    #[test]
    fn triple_and_dollar_slashy_span_newlines() {
        let t = texts("def x = \"\"\"\na\nb\"\"\"");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "\"\"\"\na\nb\"\"\""));
        let d = texts("def y = $/\na/b\n/$");
        assert!(d
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "$/\na/b\n/$"));
    }

    #[test]
    fn groovy_operators_are_single_tokens() {
        let t = texts("a <=> b; c ==~ d; e =~ f; g ?: h; i ?. j; k *. l");
        for op in ["<=>", "==~", "=~", "?:", "?.", "*."] {
            assert!(
                t.contains(&(kind::PUNCT, op.to_string())),
                "missing operator {op}"
            );
        }
    }

    #[test]
    fn ranges_do_not_eat_dots() {
        let t = texts("1..2");
        assert_eq!(
            t,
            vec![
                (kind::INT, "1".to_string()),
                (kind::PUNCT, "..".to_string()),
                (kind::INT, "2".to_string()),
            ]
        );
    }

    #[test]
    fn dollar_is_identifier_char() {
        let t = texts("def a$b = 1");
        assert!(t.contains(&(kind::IDENT, "a$b".to_string())));
    }
}
