//! Lossless Swift lexer, grounded in the Swift language reference token grammar.
//!
//! Guarantees (identical contract to the Rust and Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (whitespace, comments, the script shebang) are emitted as `trivia`
//!   tokens, not discarded. Swift is *not* whitespace-significant — newlines are
//!   ordinary trivia (unlike Python's structural `NEWLINE`).
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//!
//! Swift specifics handled here:
//! - `//` line comments and **nested** `/* */` block comments (Swift allows
//!   `/* /* */ */`); both `///`/`/** */` doc forms fall out naturally.
//! - All string forms: regular `"..."`, multiline `"""..."""`, and *raw* strings
//!   with an arbitrary number of pounds (`#"..."#`, `##"""..."""##`). The closing
//!   delimiter for a raw string is `"`/`"""` followed by the same pound count.
//!   Interpolation (`\(...)` / `\#(...)`) lives inside the one string token.
//! - Numbers: decimal/`0x`/`0o`/`0b` integers with `_` separators, decimal and
//!   hexadecimal (`0x1.8p3`) floats.
//! - Identifiers, including backtick-escaped identifiers (`` `class` ``) and the
//!   `$0` / `$name` forms.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_`/`$` as a pragmatic stand-in for the full Unicode
//! identifier tables. Anything outside still lands in the tree as a covered
//! token, never dropped. A bare `"` inside a `\(...)` interpolation can close the
//! string token early; the bytes are still covered (losslessness holds), only the
//! token boundary is approximate — the same breadth gap the Python f-string lexer
//! accepts.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Swift keywords (declarations, statements, expressions/types) plus the common
/// contextual modifiers. Like the Rust/Python lexers these all lex as `ident`
/// tokens; the parser and lowering distinguish them via [`is_keyword`].
pub const KEYWORDS: &[&str] = &[
    // Declarations.
    "associatedtype",
    "class",
    "deinit",
    "enum",
    "extension",
    "fileprivate",
    "func",
    "import",
    "init",
    "inout",
    "internal",
    "let",
    "open",
    "operator",
    "private",
    "precedencegroup",
    "protocol",
    "public",
    "rethrows",
    "static",
    "struct",
    "subscript",
    "typealias",
    "var",
    "actor",
    "macro",
    // Statements.
    "break",
    "case",
    "continue",
    "default",
    "defer",
    "do",
    "else",
    "fallthrough",
    "for",
    "guard",
    "if",
    "in",
    "repeat",
    "return",
    "switch",
    "where",
    "while",
    // Expressions and types.
    "Any",
    "as",
    "await",
    "async",
    "catch",
    "false",
    "is",
    "nil",
    "self",
    "Self",
    "some",
    "any",
    "super",
    "throw",
    "throws",
    "true",
    "try",
    // Common contextual modifiers (treated conservatively as keywords so they are
    // never mistaken for definition names or call targets).
    "convenience",
    "dynamic",
    "final",
    "indirect",
    "lazy",
    "mutating",
    "nonmutating",
    "optional",
    "override",
    "required",
    "unowned",
    "weak",
    "get",
    "set",
    "willSet",
    "didSet",
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
    pub const SHEBANG: &str = "shebang";
    pub const IDENT: &str = "ident";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const STRING: &str = "string_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
/// Longer prefixes (`===`, `!==`, `<<=`, `>>=`) precede their shorter cousins so
/// the table never splits `===` into `==` + `=`.
const OPERATORS: &[&str] = &[
    "<<=", ">>=", "===", "!==", "...", "..<", "->", "==", "!=", "<=", ">=", "&&", "||", "??", "+=",
    "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<", ">>", "&+", "&-", "&*", "~=", "..",
];

/// Single punctuation / operator characters. `#` is here only as a fallback —
/// raw-string and shebang openers are recognized before we reach this set.
const SINGLE_PUNCT: &str = "+-*/%=<>!&|^~?()[]{},;:.@#\\";

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
        // A leading `#!` line is a script shebang — trivia covering the line.
        if self.src.starts_with("#!") {
            let end = self.find_line_end(0);
            self.pos = end;
            self.push(kind::SHEBANG, 0, end, true);
        }
        while self.pos < self.bytes.len() {
            let start = self.pos;
            let c = self.peek();
            match c {
                ' ' | '\t' | '\n' | '\r' | '\x0b' | '\x0c' => {
                    self.eat_while(is_ws);
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                '/' if self.peek_at(1) == Some('/') => {
                    let end = self.find_line_end(start);
                    self.pos = end;
                    self.push(kind::LINE_COMMENT, start, end, true);
                }
                '/' if self.peek_at(1) == Some('*') => self.block_comment(start),
                '"' => self.string(start, 0),
                '#' => self.pound(start),
                '`' => self.backtick_ident(start),
                c if is_ident_start(c) => self.name(start),
                c if c.is_ascii_digit() => self.number(start),
                c if SINGLE_PUNCT.contains(c) => self.punct(start),
                _ => {
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }
            // Progress guarantee: if a sub-scanner returned without advancing the
            // cursor, consume one char as an `error` token so the loop can never
            // spin. Belt-and-suspenders against a future non-advancing branch.
            if self.pos == start {
                self.bump();
                self.push(kind::ERROR, start, self.pos, false);
            }
        }
        self.tokens
    }

    /// A `#`: either the opener of a raw string (`#"`, `##"""`, …) or a lone
    /// punctuation `#` (compiler directives like `#if`, macro expansions `#foo`,
    /// key paths, etc. — their bodies lex as ordinary following tokens).
    fn pound(&mut self, start: usize) {
        // Count the run of pounds; a raw string requires the run to be followed
        // immediately by a quote.
        let mut n = 0;
        while self.peek_at(n) == Some('#') {
            n += 1;
        }
        if self.peek_at(n) == Some('"') {
            self.pos += n; // consume the pounds; cursor now at the quote
            self.string(start, n);
        } else {
            // Emit a single `#`; any further pounds re-enter this arm.
            self.bump();
            self.push(kind::PUNCT, start, self.pos, false);
        }
    }

    fn name(&mut self, start: usize) {
        // Consume the known ident-start char first: `$` (the `$0`/`$name` forms)
        // is a valid start but *not* a continue char, so relying on `eat_while`
        // alone would emit a zero-width token and never advance.
        self.bump();
        self.eat_while(is_ident_continue);
        self.push(kind::IDENT, start, self.pos, false);
    }

    /// A backtick-escaped identifier `` `ident` `` — lets keywords be used as
    /// names. Unterminated (newline / EOF before the closing backtick) is an
    /// `error` token over the bytes seen.
    fn backtick_ident(&mut self, start: usize) {
        self.bump(); // opening backtick
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '`' {
                self.bump();
                terminated = true;
                break;
            }
            if c == '\n' || c == '\r' {
                break;
            }
            self.bump();
        }
        let k = if terminated { kind::IDENT } else { kind::ERROR };
        self.push(k, start, self.pos, false);
    }

    /// A possibly-nested block comment. Swift nests `/* */`, so we track depth and
    /// only close when it returns to zero. Unterminated runs to EOF (still trivia,
    /// still covered).
    fn block_comment(&mut self, start: usize) {
        self.pos += 2; // /*
        let mut depth: u32 = 1;
        while self.pos < self.bytes.len() && depth > 0 {
            if self.peek() == '/' && self.peek_at(1) == Some('*') {
                self.pos += 2;
                depth += 1;
            } else if self.peek() == '*' && self.peek_at(1) == Some('/') {
                self.pos += 2;
                depth -= 1;
            } else {
                self.bump();
            }
        }
        self.push(kind::BLOCK_COMMENT, start, self.pos, true);
    }

    /// Scan a string literal. `pounds` is the raw-string pound count (0 = an
    /// ordinary, escapable string). The cursor sits at the opening quote; any
    /// leading pounds have already been consumed by [`Lexer::pound`].
    ///
    /// Forms:
    /// - regular `"…"`, multiline `"""…"""`
    /// - raw `#"…"#`, raw multiline `#"""…"""#` (closing quote(s) + `pounds` `#`)
    ///
    /// In a non-raw string `\` escapes the next char (so `\"` and `\(` do not end
    /// the string). In a raw string `\` is literal; only the pounded closing
    /// delimiter terminates it.
    fn string(&mut self, start: usize, pounds: usize) {
        let raw = pounds > 0;
        let triple = self.peek_at(1) == Some('"') && self.peek_at(2) == Some('"');
        if triple {
            self.pos += 3;
        } else {
            self.bump();
        }
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '\\' && !raw {
                // Escape: consume the backslash and the next char (covers `\"`,
                // `\\`, and the `(` that opens an interpolation).
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
                continue;
            }
            if c == '"' {
                if triple {
                    if self.peek_at(1) == Some('"')
                        && self.peek_at(2) == Some('"')
                        && self.pounds_follow(3, pounds)
                    {
                        self.pos += 3 + pounds;
                        terminated = true;
                        break;
                    }
                    self.bump();
                } else if self.pounds_follow(1, pounds) {
                    self.pos += 1 + pounds;
                    terminated = true;
                    break;
                } else {
                    self.bump();
                }
            } else if (c == '\n' || c == '\r') && !triple {
                // Single-line strings (raw or not) cannot span a newline.
                break;
            } else {
                self.bump();
            }
        }
        let k = if terminated {
            kind::STRING
        } else {
            kind::ERROR
        };
        self.push(k, start, self.pos, false);
    }

    /// True if the `pounds` characters starting `offset` chars past the cursor are
    /// all `#` (the pound tail of a raw-string closing delimiter). `pounds == 0`
    /// is trivially true.
    fn pounds_follow(&self, offset: usize, pounds: usize) -> bool {
        for k in 0..pounds {
            if self.peek_at(offset + k) != Some('#') {
                return false;
            }
        }
        true
    }

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        if self.peek() == '0' {
            match self.peek_at(1) {
                Some('x') | Some('X') => {
                    self.pos += 2;
                    self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
                    // Hexadecimal float: fraction and mandatory `p` exponent.
                    if self.peek() == '.' && self.peek_at(1).map(is_hex_digit).unwrap_or(false) {
                        is_float = true;
                        self.bump();
                        self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
                    }
                    if matches!(self.peek(), 'p' | 'P') {
                        is_float = true;
                        self.eat_exponent();
                    }
                    let k = if is_float { kind::FLOAT } else { kind::INT };
                    return self.push(k, start, self.pos, false);
                }
                Some('o') | Some('O') => {
                    self.pos += 2;
                    self.eat_while(|c| ('0'..='7').contains(&c) || c == '_');
                    return self.push(kind::INT, start, self.pos, false);
                }
                Some('b') | Some('B') => {
                    self.pos += 2;
                    self.eat_while(|c| c == '0' || c == '1' || c == '_');
                    return self.push(kind::INT, start, self.pos, false);
                }
                _ => {}
            }
        }
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        // Decimal fraction only when a digit follows the dot (so `1.foo` stays
        // `1` `.` `foo`).
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
                self.eat_exponent();
            }
        }
        let k = if is_float { kind::FLOAT } else { kind::INT };
        self.push(k, start, self.pos, false);
    }

    /// Consume an exponent marker (`e`/`E`/`p`/`P`), an optional sign, and the
    /// digit run. The caller has already verified a digit follows.
    fn eat_exponent(&mut self) {
        self.bump(); // e / p
        if matches!(self.peek(), '+' | '-') {
            self.bump();
        }
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
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

fn is_ws(c: char) -> bool {
    matches!(c, ' ' | '\t' | '\n' | '\r' | '\x0b' | '\x0c')
}

fn is_hex_digit(c: char) -> bool {
    c.is_ascii_hexdigit()
}

fn is_ident_start(c: char) -> bool {
    c == '_' || c == '$' || c.is_alphabetic()
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
            "func f(x: Int) -> Int {\n    return x\n}\n",
            "class C {\n    var n = 0\n}\n",
            "let x = 0xFF_00 + 1.5e3 + 0x1.8p2\n",
            "let s = \"hi \\(name)!\" + \"\"\"\nmulti\nline\n\"\"\"\n",
            "let r = #\"raw \\#(x) \" still\"# + ##\"two #\"## \n",
            "// line\n/* block /* nested */ end */\nstruct S {}\n",
            "let λ = \"☃ €\" // unicode\n",
            "a ..< b ... c ?? d === e\n",
            "let `class` = 1; print($0)\n",
            "#!/usr/bin/swift\nprint(\"hi\")\n",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
            let toks = lex(src);
            let mut rebuilt = String::new();
            for t in &toks {
                rebuilt.push_str(t.span.text(src));
            }
            assert_eq!(rebuilt, src, "not lossless: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("func add(a: Int, b: Int) -> Int { a + b }");
        assert!(t.contains(&(kind::IDENT, "func".to_string())));
        assert!(t.contains(&(kind::IDENT, "add".to_string())));
        assert!(t.contains(&(kind::PUNCT, "(".to_string())));
        assert!(t.contains(&(kind::PUNCT, "->".to_string())));
        assert!(is_keyword("func"));
        assert!(is_keyword("class"));
        assert!(!is_keyword("add"));
    }

    #[test]
    fn nested_block_comment_is_one_token() {
        let t = texts("/* a /* b */ c */x");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::BLOCK_COMMENT && s == "/* a /* b */ c */"));
        assert!(t.contains(&(kind::IDENT, "x".to_string())));
    }

    #[test]
    fn multiline_and_interpolated_strings() {
        let t = texts("\"a\\(b)c\" + \"\"\"\nx\ny\n\"\"\"");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "\"a\\(b)c\""));
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "\"\"\"\nx\ny\n\"\"\""));
    }

    #[test]
    fn raw_strings_with_pounds() {
        // The closing delimiter must carry the same pound count; an inner `"#`
        // with too few pounds is literal content.
        let t = texts("##\"a \"# b\"##");
        assert!(
            t.iter()
                .any(|(k, s)| *k == kind::STRING && s == "##\"a \"# b\"##"),
            "raw string with 2 pounds not recognized: {t:?}"
        );
    }

    #[test]
    fn numbers() {
        let t = texts("0b1010 0o17 0xAF 10_000 3.14 2e10 0x1.8p3");
        assert!(t.contains(&(kind::INT, "0b1010".to_string())));
        assert!(t.contains(&(kind::INT, "0xAF".to_string())));
        assert!(t.contains(&(kind::INT, "10_000".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14".to_string())));
        assert!(t.contains(&(kind::FLOAT, "2e10".to_string())));
        assert!(t.contains(&(kind::FLOAT, "0x1.8p3".to_string())));
    }

    #[test]
    fn backtick_identifier() {
        let t = texts("let `default` = 1");
        assert!(t.contains(&(kind::IDENT, "`default`".to_string())));
    }

    #[test]
    fn operators_are_greedy() {
        let t = texts("a ..< b ... c");
        assert!(t.contains(&(kind::PUNCT, "..<".to_string())));
        assert!(t.contains(&(kind::PUNCT, "...".to_string())));
    }

    #[test]
    fn unterminated_string_is_error_not_dropped() {
        let toks = lex("let s = \"oops\n");
        let mut rebuilt = String::new();
        for t in &toks {
            rebuilt.push_str(t.span.text("let s = \"oops\n"));
        }
        assert_eq!(rebuilt, "let s = \"oops\n");
        assert!(toks.iter().any(|t| t.kind == kind::ERROR));
    }
}
