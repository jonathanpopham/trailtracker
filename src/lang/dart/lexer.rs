//! Lossless Dart lexer, grounded in the Dart language specification token
//! grammar.
//!
//! Guarantees (identical contract to the Rust, Java, and Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (whitespace, `//` line comments, `///` doc comments, `/* */` and
//!   `/** */` block comments) are emitted as `trivia` tokens, never discarded —
//!   the parser skips them for structure but the tree keeps them.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//!
//! Dart surface covered: `//`/`///` line comments, `/* */`/`/** */` block
//! comments (Dart block comments **do** nest, like Rust and unlike Java),
//! single- and double-quoted strings, triple-quoted multi-line strings, raw
//! strings (`r'...'`, `r"""..."""`), `$identifier` and `${expr}` interpolation
//! (the whole string — interpolations included — is a single `string_literal`
//! token), decimal/hex integers and floating-point literals, identifiers /
//! keywords, and the operator/punctuation set (`>>>`, `~/`, `??=`, `..`, `...`,
//! `=>`, …).
//!
//! Hazard handled head-on: a `${ … }` substitution can contain arbitrary code,
//! including the string's own quote character (`"a ${f("b")} c"`). The body
//! scanner skips a balanced `{ … }` run on `${`, and skips a nested quoted run
//! inside it, so a quote inside an interpolation does not prematurely terminate
//! the string. This is done iteratively (a brace counter, not recursion), so
//! deeply nested interpolation cannot overflow the stack. A wrong guess never
//! breaks losslessness — every byte is still covered.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_` and `$` (both legal in Dart identifiers) as a
//! pragmatic stand-in for the full Unicode identifier tables. Anything outside
//! still lands in the tree as a covered token, never dropped.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Dart reserved words plus the structural built-in identifiers the parser and
/// lowering rely on (`extends`, `with`, `implements`, `on`, `get`, `set`, …).
/// Like the Rust/Java lexers these all lex as `ident` tokens; [`is_keyword`]
/// distinguishes them. The *declaration-introducing* built-ins `mixin`,
/// `extension`, and `typedef` are also listed so they are filtered from
/// type-use scanning; the parser still recognizes them by position (matching
/// token text), not by token kind.
pub const KEYWORDS: &[&str] = &[
    // Reserved words.
    "assert",
    "break",
    "case",
    "catch",
    "class",
    "const",
    "continue",
    "default",
    "do",
    "else",
    "enum",
    "extends",
    "false",
    "final",
    "finally",
    "for",
    "if",
    "in",
    "is",
    "new",
    "null",
    "rethrow",
    "return",
    "super",
    "switch",
    "this",
    "throw",
    "true",
    "try",
    "var",
    "void",
    "while",
    "with",
    // Built-in identifiers / contextual keywords needed for parsing + filtering.
    "abstract",
    "as",
    "async",
    "await",
    "base",
    "covariant",
    "deferred",
    "dynamic",
    "export",
    "external",
    "factory",
    "get",
    "hide",
    "implements",
    "import",
    "interface",
    "late",
    "library",
    "mixin",
    "on",
    "part",
    "required",
    "sealed",
    "set",
    "show",
    "static",
    "sync",
    "typedef",
    "yield",
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

/// Multi-character operators, longest first so the scanner is greedy-correct
/// (`>>>=` before `>>>`, `...?` before `...`, `~/=` before `~/`, and so on).
const OPERATORS: &[&str] = &[
    ">>>=", "...?", ">>>", "...", "~/=", "<<=", ">>=", "??=", "?..", "=>", "??", "?.", "..", "~/",
    "==", "!=", "<=", ">=", "&&", "||", "++", "--", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=",
    "<<", ">>",
];

const SINGLE_PUNCT: &str = "+-*/%!&|^~<>=.,;:?()[]{}@#$";

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
        // A leading `#!` shebang line is consumed as trivia (Dart scripts permit
        // one). Anything else starting with `#` falls through to punctuation.
        if self.src.starts_with("#!") {
            let end = self.find_line_end(0);
            self.push(kind::LINE_COMMENT, 0, end, true);
            self.pos = end;
        }

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
                'r' if matches!(self.peek_at(1), Some('"') | Some('\'')) => {
                    self.bump(); // r
                    self.string(start, true);
                }
                '"' | '\'' => self.string(start, false),
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

            // Main-run-loop progress guard: every iteration MUST advance `pos`.
            // A scanner that failed to move would otherwise spin forever (OOM);
            // here we force one byte of progress as an `error` token. In practice
            // the arms above always advance, so this is a defensive net only.
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

    /// `/* ... */` (and `/** ... */` doc). Dart block comments nest.
    fn block_comment(&mut self, start: usize) {
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

    /// Scan a string literal as a single token. `raw` strings (prefix `r`, the
    /// `r` already consumed) have no escapes and no interpolation; ordinary
    /// strings honor `\` escapes and `$`/`${…}` interpolation. The triple-quoted
    /// form spans newlines; the single-quoted form ends at an unescaped newline.
    fn string(&mut self, start: usize, raw: bool) {
        let quote = self.peek(); // ' or "
        let triple = self.peek_at(1) == Some(quote) && self.peek_at(2) == Some(quote);
        let qlen = if triple { 3 } else { 1 };
        for _ in 0..qlen {
            self.bump();
        }
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if !raw && c == '\\' {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
                continue;
            }
            if !raw && c == '$' {
                // `${ expr }` — skip a balanced brace run so a quote inside the
                // interpolation cannot close the string. `$identifier` needs no
                // special handling (the `$` and ident chars are just consumed).
                if self.peek_at(1) == Some('{') {
                    self.bump(); // $
                    self.bump(); // {
                    self.skip_interpolation();
                    continue;
                }
                self.bump();
                continue;
            }
            if c == quote {
                if triple {
                    if self.peek_at(1) == Some(quote) && self.peek_at(2) == Some(quote) {
                        self.bump();
                        self.bump();
                        self.bump();
                        terminated = true;
                        break;
                    }
                    self.bump();
                    continue;
                }
                self.bump();
                terminated = true;
                break;
            }
            if !triple && c == '\n' {
                break; // unterminated single-line string
            }
            self.bump();
        }
        let token_kind = if terminated {
            kind::STRING
        } else {
            kind::ERROR
        };
        self.push(token_kind, start, self.pos, false);
    }

    /// Skip a `${ … }` interpolation body. The opening `{` is already consumed
    /// (depth starts at 1). Done iteratively with a brace counter so arbitrarily
    /// deep `${…}` nesting cannot overflow the stack. A nested quoted run is
    /// skipped wholesale so its braces/quotes do not confuse the counter.
    fn skip_interpolation(&mut self) {
        let mut depth = 1usize;
        while self.pos < self.bytes.len() && depth > 0 {
            let c = self.peek();
            match c {
                '{' => {
                    depth += 1;
                    self.bump();
                }
                '}' => {
                    depth -= 1;
                    self.bump();
                }
                '\'' | '"' => self.skip_nested_quote(c),
                _ => self.bump(),
            }
        }
    }

    /// Skip a nested quoted run inside an interpolation (best effort, single
    /// line): consume the opening quote, honor `\` escapes, stop at the matching
    /// quote. Always advances, so it can never stall the lexer.
    fn skip_nested_quote(&mut self, quote: char) {
        self.bump(); // opening quote
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '\\' {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
            } else if c == quote || c == '\n' {
                if c == quote {
                    self.bump();
                }
                break;
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
            return self.push(kind::INT, start, self.pos, false);
        }
        // A literal may begin with `.` (e.g. `.5`); the leading digits run is
        // then empty, which is fine.
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        // Fractional part only when a digit follows the dot, so `1..2` and member
        // access `x.0` stay split.
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
            "int x = 1000;",
            "// comment\nfinal y = 0xFF;",
            "/* a /* nested */ b */ x",
            "/// doc comment\nvoid m() {}",
            "var s = 'hi\\n' + \"world\";",
            "var t = '''\nmulti\nline''';",
            "var r = r'raw $no interp';",
            "var i = \"a ${f(\"b\")} c $name end\";",
            "a >>> b; c ~/ d; e ??= f; var g = [1, ...xs];",
            "double d = 1.5e3; var h = .5;",
            "p..foo()..bar();",
            "λ ☃ €", // non-ascii idents / unknowns still covered
            "",
            "#!/usr/bin/env dart\nvoid main() {}",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("int add(int a) => a;");
        assert!(t.contains(&(kind::IDENT, "int".to_string())));
        assert!(t.contains(&(kind::IDENT, "add".to_string())));
        assert!(t.contains(&(kind::PUNCT, "=>".to_string())));
        assert!(is_keyword("class"));
        assert!(is_keyword("extends"));
        assert!(!is_keyword("add"));
    }

    #[test]
    fn interpolation_with_inner_quotes_is_one_token() {
        let t = texts("var x = \"a ${f(\"b\")} c\";");
        assert!(
            t.iter()
                .any(|(k, s)| *k == kind::STRING && s == "\"a ${f(\"b\")} c\""),
            "got {t:?}"
        );
    }

    #[test]
    fn raw_string_has_no_escapes() {
        let t = texts(r"var x = r'a\nb';");
        assert!(t.iter().any(|(k, s)| *k == kind::STRING && s == r"r'a\nb'"));
    }

    #[test]
    fn triple_quoted_spans_newlines() {
        let t = texts("var x = '''\na\nb''';");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "'''\na\nb'''"));
    }

    #[test]
    fn numbers() {
        let t = texts("0xAF 10 3.14 2e10 .5");
        assert!(t.contains(&(kind::INT, "0xAF".to_string())));
        assert!(t.contains(&(kind::INT, "10".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14".to_string())));
        assert!(t.contains(&(kind::FLOAT, "2e10".to_string())));
        assert!(t.contains(&(kind::FLOAT, ".5".to_string())));
    }

    #[test]
    fn cascade_and_spread_operators() {
        let t = texts("a..b ...c");
        assert!(t.contains(&(kind::PUNCT, "..".to_string())));
        assert!(t.contains(&(kind::PUNCT, "...".to_string())));
    }

    #[test]
    fn nested_block_comments() {
        let t = texts("/* a /* b */ c */ x");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::BLOCK_COMMENT && s == "/* a /* b */ c */"));
    }

    #[test]
    fn unterminated_string_is_error_not_dropped() {
        let t = texts("var x = 'oops");
        assert!(t.iter().any(|(k, _)| *k == kind::ERROR));
        assert!(covers_all("var x = 'oops"));
    }
}
