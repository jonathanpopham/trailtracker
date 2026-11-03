//! Lossless JavaScript lexer, grounded in the ECMAScript token grammar.
//!
//! Guarantees (identical contract to the Rust and Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (whitespace, line terminators, comments, hashbang) are emitted as
//!   `trivia` tokens, never discarded. Line terminators are their own `newline`
//!   trivia kind so the parser can recover ASI (automatic semicolon insertion)
//!   boundaries without the lexer fabricating zero-width tokens.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//!
//! JavaScript-specific hazards handled here:
//! - **Template literals** (`` `a${expr}b` ``) — scanned with an explicit,
//!   heap-allocated context stack (never recursion) so deeply nested
//!   `${ `${ … }` }` cannot overflow the stack. The whole literal is one opaque
//!   token, matching how the Python lexer treats f-strings.
//! - **Regex vs. division** — the `/` character is contextually a regular
//!   expression or a division operator. We decide with the standard
//!   previous-significant-token heuristic. Misclassification cannot affect
//!   losslessness (the bytes are covered either way); it only changes a token
//!   label, and graph facts never depend on regex/division being told apart.
//! - **BigInt** (`10n`), numeric separators (`1_000`), all radix prefixes, and
//!   leading-dot floats (`.5`).
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_`/`$` as a pragmatic stand-in for the full Unicode
//! ID_Start/ID_Continue tables, and `\u{…}` identifier escapes are not stitched
//! into a single identifier. Anything outside still lands in the tree as a
//! covered token (`error` where unclassifiable), never dropped.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// JavaScript reserved words and common contextual keywords. Like the Rust and
/// Python lexers, these lex as plain `name` tokens; the parser and lowering
/// distinguish them via [`is_keyword`].
pub const KEYWORDS: &[&str] = &[
    "await",
    "break",
    "case",
    "catch",
    "class",
    "const",
    "continue",
    "debugger",
    "default",
    "delete",
    "do",
    "else",
    "enum",
    "export",
    "extends",
    "false",
    "finally",
    "for",
    "function",
    "if",
    "import",
    "in",
    "instanceof",
    "new",
    "null",
    "return",
    "super",
    "switch",
    "this",
    "throw",
    "true",
    "try",
    "typeof",
    "var",
    "void",
    "while",
    "with",
    "yield",
    "let",
    "static",
    "async",
    "of",
    "as",
    "from",
    "get",
    "set",
    "undefined",
];

pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.contains(&text)
}

/// Token kind labels. Stored on the CST as `&'static str`.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const NEWLINE: &str = "newline";
    pub const LINE_COMMENT: &str = "line_comment";
    pub const BLOCK_COMMENT: &str = "block_comment";
    pub const HASHBANG: &str = "hashbang";
    pub const NAME: &str = "name";
    pub const PRIVATE_NAME: &str = "private_name";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const STRING: &str = "string_literal";
    pub const TEMPLATE: &str = "template_literal";
    pub const REGEX: &str = "regex_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
/// The `/`-family operators (`/`, `/=`) are intentionally absent: `/` is handled
/// up front so it can be told apart from comments and regular expressions.
const OPERATORS: &[&str] = &[
    ">>>=", "...", "===", "!==", "**=", "<<=", ">>=", "&&=", "||=", "??=", ">>>", "=>", "?.", "??",
    "==", "!=", "<=", ">=", "&&", "||", "++", "--", "+=", "-=", "*=", "%=", "&=", "|=", "^=", "**",
    "<<", ">>",
];

/// Single-character punctuators. `/` and `#` are handled by dedicated scanners.
const SINGLE_PUNCT: &str = "+-*%=<>!~&|^?:.,;()[]{}@";

/// Keywords after which a `/` begins a regular expression rather than division
/// (they put the lexer in an expression-expected position).
const REGEX_PRECEDING_KEYWORDS: &[&str] = &[
    "return",
    "typeof",
    "instanceof",
    "in",
    "of",
    "new",
    "delete",
    "void",
    "do",
    "else",
    "case",
    "yield",
    "await",
    "throw",
];

pub fn lex(source: &str) -> Vec<Token> {
    Lexer::new(source).run()
}

struct Lexer<'s> {
    src: &'s str,
    bytes: &'s [u8],
    pos: usize,
    tokens: Vec<Token>,
    /// Last emitted non-trivia token (kind + span), used by the regex/division
    /// disambiguation heuristic.
    prev_sig: Option<(&'static str, ByteSpan)>,
}

/// Context frames for the iterative template-literal scanner. Heap-stacked so
/// arbitrarily deep `${ }` nesting never recurses (and so never overflows).
#[derive(Clone, Copy)]
enum TplCtx {
    /// Inside the literal text of a template (between backticks / interpolations).
    Template,
    /// Inside a `${ … }` interpolation; tracks nested braces.
    Interp,
}

impl<'s> Lexer<'s> {
    fn new(src: &'s str) -> Self {
        Lexer {
            src,
            bytes: src.as_bytes(),
            pos: 0,
            tokens: Vec::new(),
            prev_sig: None,
        }
    }

    fn run(mut self) -> Vec<Token> {
        // Hashbang: only a leading `#!` line (Node/CLI scripts).
        if self.src.starts_with("#!") {
            let end = self.find_line_end(0);
            self.push(kind::HASHBANG, 0, end, true);
            self.pos = end;
        }

        while self.pos < self.bytes.len() {
            let start = self.pos;
            let c = self.peek();
            match c {
                c if is_line_terminator(c) => self.newline(start),
                c if c.is_whitespace() => {
                    self.eat_while(|c| c.is_whitespace() && !is_line_terminator(c));
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                '/' => self.slash(start),
                '`' => self.template(start),
                '"' | '\'' => self.string(start, c),
                '#' => {
                    if is_ident_start(self.peek_at(1).unwrap_or('\0')) {
                        self.bump(); // #
                        self.eat_while(is_ident_continue);
                        self.push(kind::PRIVATE_NAME, start, self.pos, false);
                    } else {
                        self.bump();
                        self.push(kind::ERROR, start, self.pos, false);
                    }
                }
                c if is_ident_start(c) => {
                    self.eat_while(is_ident_continue);
                    self.push(kind::NAME, start, self.pos, false);
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

    // --- scanners -----------------------------------------------------------

    fn newline(&mut self, start: usize) {
        // `\r\n` is one line terminator; `\n`, `\r`, U+2028, U+2029 each one too.
        if self.peek() == '\r' {
            self.bump();
            if self.peek() == '\n' {
                self.bump();
            }
        } else {
            self.bump();
        }
        self.push(kind::NEWLINE, start, self.pos, true);
    }

    /// `/` — line comment, block comment, regex literal, or division operator.
    fn slash(&mut self, start: usize) {
        match self.peek_at(1) {
            Some('/') => {
                self.pos += 2;
                while self.pos < self.bytes.len() && !is_line_terminator(self.peek()) {
                    self.bump();
                }
                self.push(kind::LINE_COMMENT, start, self.pos, true);
            }
            Some('*') => {
                self.pos += 2;
                while self.pos < self.bytes.len() {
                    if self.src[self.pos..].starts_with("*/") {
                        self.pos += 2;
                        break;
                    }
                    self.bump();
                }
                // Unterminated block comment still covers to EOF — lossless.
                self.push(kind::BLOCK_COMMENT, start, self.pos, true);
            }
            _ => {
                // A `/` flush against a preceding `<` is the JSX closing-tag
                // delimiter `</`, never a regex start: reading it as a regex
                // runs unterminated to end-of-line and surfaces error bytes,
                // breaking the module's "JSX lexes as ordinary tokens, never
                // a coverage break" contract. (`x < /re/` with a space still
                // lexes as a regex.)
                let jsx_close = start > 0 && self.bytes[start - 1] == b'<';
                if self.regex_allowed() && !jsx_close {
                    self.regex(start);
                } else {
                    // Division operator: `/=` or `/`.
                    if self.src[self.pos..].starts_with("/=") {
                        self.pos += 2;
                    } else {
                        self.bump();
                    }
                    self.push(kind::PUNCT, start, self.pos, false);
                }
            }
        }
    }

    /// Scan a regular-expression literal `/body/flags`. A char class `[ … ]`
    /// shelters an inner `/`. A regex literal can never contain an unescaped
    /// line terminator, so a scan that hits one proves the `/` was never a
    /// regex — the value-context heuristic misjudged it (after `}` the
    /// self-closing JSX `/>` in `<X a={b} />` looks like a regex start). The
    /// scan rewinds and the `/` lexes as ordinary punct; the following bytes
    /// re-lex normally.
    fn regex(&mut self, start: usize) {
        self.bump(); // opening /
        let mut in_class = false;
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
            if is_line_terminator(c) {
                break;
            }
            match c {
                '[' => {
                    in_class = true;
                    self.bump();
                }
                ']' => {
                    in_class = false;
                    self.bump();
                }
                '/' if !in_class => {
                    self.bump();
                    terminated = true;
                    break;
                }
                _ => self.bump(),
            }
        }
        if terminated {
            self.eat_while(is_ident_continue); // flags
            self.push(kind::REGEX, start, self.pos, false);
        } else {
            // Unterminated ⇒ not a regex at all (see the doc comment): emit
            // the `/` as punct and re-lex from the next byte.
            self.pos = start + 1;
            self.push(kind::PUNCT, start, self.pos, false);
        }
    }

    /// Scan a regex literal at the cursor (`/`) inside a template interpolation,
    /// where the caller has already resolved regex/division ambiguity. Honors `\`
    /// escapes and `[...]` classes; a line terminator before the closing `/`
    /// proves it was division, so the cursor rewinds to just past the `/`. Never
    /// pushes a token — the enclosing `template` scan owns the span.
    fn scan_interp_regex(&mut self) {
        let slash = self.pos;
        self.bump(); // opening /
        let mut in_class = false;
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
            if is_line_terminator(c) {
                break;
            }
            match c {
                '[' => {
                    in_class = true;
                    self.bump();
                }
                ']' => {
                    in_class = false;
                    self.bump();
                }
                '/' if !in_class => {
                    self.bump();
                    terminated = true;
                    break;
                }
                _ => self.bump(),
            }
        }
        if terminated {
            self.eat_while(is_ident_continue); // trailing flags
        } else {
            self.pos = slash + 1; // not a regex: consume only the `/` (division)
        }
    }

    /// Scan a `'…'` or `"…"` string. Backslash escapes the next char (including a
    /// line-continuation `\`+newline). An unescaped line terminator ends an
    /// unterminated string as an `error` token.
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
                continue;
            }
            if c == quote {
                self.bump();
                terminated = true;
                break;
            }
            if is_line_terminator(c) {
                break;
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

    /// Scan a template literal as a single opaque token, tracking `${ … }`
    /// interpolations (which may themselves contain nested templates, objects,
    /// strings, and comments) with an explicit context stack. No recursion, so
    /// hostile nesting cannot overflow the stack. An unterminated literal becomes
    /// an `error` token covering everything consumed.
    fn template(&mut self, start: usize) {
        self.bump(); // opening backtick
        let mut stack: Vec<TplCtx> = vec![TplCtx::Template];
        // Previous significant byte inside the current interpolation, used to
        // tell a regex `/` from division — the same ambiguity `regex_allowed`
        // resolves at top level. Without it a regex inside `${ … }` (e.g.
        // `` `${s.replace(/"/g, '')}` ``) lets the `"` inside the regex start a
        // bogus string that desyncs the brace stack and spills the whole
        // template into an error token. Reset at each new expression context.
        let mut last_sig: Option<u8> = None;
        while self.pos < self.bytes.len() {
            let top = match stack.last().copied() {
                Some(t) => t,
                None => break, // the literal closed
            };
            match top {
                TplCtx::Template => {
                    let c = self.peek();
                    if c == '\\' {
                        self.bump();
                        if self.pos < self.bytes.len() {
                            self.bump();
                        }
                    } else if c == '`' {
                        self.bump();
                        stack.pop();
                    } else if c == '$' && self.peek_at(1) == Some('{') {
                        self.pos += 2;
                        stack.push(TplCtx::Interp);
                        last_sig = None; // fresh expression context
                    } else {
                        self.bump();
                    }
                }
                TplCtx::Interp => {
                    let interp_start = self.pos;
                    let c = self.peek();
                    match c {
                        '`' => {
                            self.bump();
                            stack.push(TplCtx::Template);
                        }
                        '{' => {
                            self.bump();
                            stack.push(TplCtx::Interp);
                            last_sig = None; // fresh expression context
                        }
                        '}' => {
                            self.bump();
                            stack.pop();
                        }
                        '\'' | '"' => self.skip_string_inline(c),
                        '/' if self.peek_at(1) == Some('/') => {
                            while self.pos < self.bytes.len() && !is_line_terminator(self.peek()) {
                                self.bump();
                            }
                        }
                        '/' if self.peek_at(1) == Some('*') => {
                            self.pos += 2;
                            while self.pos < self.bytes.len() {
                                if self.src[self.pos..].starts_with("*/") {
                                    self.pos += 2;
                                    break;
                                }
                                self.bump();
                            }
                        }
                        '/' if regex_allowed_after(last_sig) => {
                            // Regex candidate: scan it as a unit so its quotes and
                            // brackets can't start strings or close the interp. A
                            // line terminator before the closing `/` proves it was
                            // division; only the `/` is consumed then.
                            self.scan_interp_regex();
                        }
                        _ => self.bump(),
                    }
                    if self.pos > interp_start {
                        if let Some(&b) = self.bytes.get(self.pos - 1) {
                            if !b.is_ascii_whitespace() {
                                last_sig = Some(b);
                            }
                        }
                    }
                }
            }
        }
        let terminated = stack.is_empty();
        let token_kind = if terminated {
            kind::TEMPLATE
        } else {
            kind::ERROR
        };
        self.push(token_kind, start, self.pos, false);
    }

    /// Advance past a `'…'`/`"…"` string while inside a template interpolation.
    /// Does not emit a token (the enclosing template is one token); only keeps the
    /// brace counter honest by not letting a quoted `}` close the interpolation.
    fn skip_string_inline(&mut self, quote: char) {
        self.bump(); // opening quote
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '\\' {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
                continue;
            }
            if c == quote || is_line_terminator(c) {
                self.bump();
                break;
            }
            self.bump();
        }
    }

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        if self.peek() == '0' {
            let radix = match self.peek_at(1) {
                Some('x') | Some('X') => Some(16u32),
                Some('o') | Some('O') => Some(8),
                Some('b') | Some('B') => Some(2),
                _ => None,
            };
            if let Some(r) = radix {
                self.pos += 2;
                match r {
                    16 => self.eat_while(|c| c.is_ascii_hexdigit() || c == '_'),
                    8 => self.eat_while(|c| ('0'..='7').contains(&c) || c == '_'),
                    _ => self.eat_while(|c| c == '0' || c == '1' || c == '_'),
                }
                if self.peek() == 'n' {
                    self.bump(); // BigInt suffix
                }
                return self.push(kind::INT, start, self.pos, false);
            }
        }
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        // Fractional part only when a digit follows the dot, so `obj.prop` and
        // `1..2`-style sequences keep the `.` as its own punctuator.
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
        // BigInt suffix on a plain integer literal.
        if !is_float && self.peek() == 'n' {
            self.bump();
        }
        let k = if is_float { kind::FLOAT } else { kind::INT };
        self.push(k, start, self.pos, false);
    }

    fn punct(&mut self, start: usize) {
        // `?.` is optional chaining only when not followed by a digit, so the
        // ternary `a ? .5 : b` keeps `?` and `.5` separate.
        if self.src[self.pos..].starts_with("?.")
            && self.peek_at(2).map(|c| c.is_ascii_digit()).unwrap_or(false)
        {
            self.bump(); // just `?`
            return self.push(kind::PUNCT, start, self.pos, false);
        }
        for op in OPERATORS {
            if self.src[self.pos..].starts_with(op) {
                self.pos += op.len();
                return self.push(kind::PUNCT, start, self.pos, false);
            }
        }
        self.bump();
        self.push(kind::PUNCT, start, self.pos, false);
    }

    /// Heuristic: may a `/` at the cursor begin a regular expression? Decided from
    /// the previous significant token. Losslessness never depends on the answer.
    fn regex_allowed(&self) -> bool {
        let (k, span) = match self.prev_sig {
            None => return true, // start of input → expression position
            Some(p) => p,
        };
        if k == kind::NAME {
            // A regex follows expression-introducing keywords; after a plain
            // identifier or a value keyword (`this`, `true`, …) it is division.
            return REGEX_PRECEDING_KEYWORDS.contains(&span.text(self.src));
        }
        if k == kind::PUNCT {
            // After a value-closing punctuator, `/` is division.
            let t = span.text(self.src);
            return t != ")" && t != "]" && t != "}" && t != "++" && t != "--";
        }
        // A string/template/number/regex/private-name closes a value → division.
        !ends_value(k)
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
        let span = ByteSpan::new(start, end);
        if !trivia {
            self.prev_sig = Some((kind, span));
        }
        self.tokens.push(Token { kind, span, trivia });
    }
}

fn is_line_terminator(c: char) -> bool {
    matches!(c, '\n' | '\r' | '\u{2028}' | '\u{2029}')
}

/// True for token kinds that end a value expression, so a following `/` is a
/// division operator rather than the start of a regular expression.
fn ends_value(k: &str) -> bool {
    k == kind::STRING
        || k == kind::TEMPLATE
        || k == kind::INT
        || k == kind::FLOAT
        || k == kind::REGEX
        || k == kind::PRIVATE_NAME
}

/// Whether a `/` following byte `last` (the previous significant byte inside a
/// template interpolation) begins a regex literal rather than division. Division
/// follows a value byte — an identifier/number byte, a closing `)`/`]`, or a
/// closing string/template quote. Everything else expects an operand, so `/`
/// starts a regex. Byte-level analogue of `ends_value`; a rare mis-tag affects
/// precision only, never losslessness.
fn regex_allowed_after(last: Option<u8>) -> bool {
    match last {
        None => true,
        Some(b) => {
            !(b.is_ascii_alphanumeric()
                || b == b'_'
                || b == b'$'
                || b == b')'
                || b == b']'
                || b == b'\''
                || b == b'"'
                || b == b'`')
        }
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
            "function f(x) {\n  return x;\n}\n",
            "class C extends B { #x = 1; get y() { return this.#x; } }\n",
            "const x = 0xFF_00 + 1.5e3 + 3n + .5;\n",
            "let s = `a${ x + `b${y}` }c` + 'q\\n' + \"d\";\n",
            "const re = /ab[/]c/gi; let d = a / b / c;\n",
            "// line comment\n/* block /*not nested*/ x\n",
            "#!/usr/bin/env node\nconst z = 1;\n",
            "let λ = '☃ €'; // unicode\n",
            "a ??= b; c ||= d; e &&= f; g >>>= h;\n",
            "obj?.prop?.method?.(); a?.5:b;\n",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("function add(a, b) { return a + b; }");
        assert!(t.contains(&(kind::NAME, "function".to_string())));
        assert!(t.contains(&(kind::NAME, "add".to_string())));
        assert!(t.contains(&(kind::PUNCT, "(".to_string())));
        assert!(is_keyword("function"));
        assert!(is_keyword("return"));
        assert!(!is_keyword("add"));
    }

    #[test]
    fn template_with_nested_interpolation() {
        let t = texts("`a${ `b${c}d` }e`");
        assert_eq!(
            t.iter().filter(|(k, _)| *k == kind::TEMPLATE).count(),
            1,
            "the whole nested template is one token"
        );
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::TEMPLATE && s == "`a${ `b${c}d` }e`"));
    }

    #[test]
    fn regex_inside_template_interpolation_is_not_error() {
        // Regression (mirror of the TS fix): a regex inside `${ … }` used to let
        // a quote in the regex body (`/"/g`) start a bogus string, desync the
        // interpolation stack, and spill the whole template into an `error`
        // token. It must be consumed as a unit so the template stays lossless.
        for src in [
            r#"function q(n) { return `"${n.replace(/"/g, '""')}"`; }"#,
            "const t = `x ${s.replace(/[/}]/g, '_')} y`;",
            "const u = `${a.match(/\\d+/)[0]} of ${b}`;",
            "const v = `${width / 2}px ${height / 2}px`;",
        ] {
            let t = texts(src);
            assert!(
                t.iter().all(|(k, _)| *k != kind::ERROR),
                "error token in {src:?}: {t:?}"
            );
            assert!(covers_all(src), "not contiguous: {src:?}");
            assert_eq!(
                t.iter().filter(|(k, _)| *k == kind::TEMPLATE).count(),
                1,
                "template should be exactly one token: {src:?} -> {t:?}"
            );
        }
    }

    #[test]
    fn regex_vs_division() {
        // After `=` a `/` starts a regex; after an identifier it is division.
        let t = texts("x = /ab/g; y = a / b;");
        assert!(t.iter().any(|(k, s)| *k == kind::REGEX && s == "/ab/g"));
        assert!(t.iter().any(|(k, s)| *k == kind::PUNCT && s == "/"));
    }

    #[test]
    fn jsx_closing_tag_is_not_a_regex() {
        // `</` is the JSX closing-tag delimiter: the slash must lex as punct,
        // never as an unterminated regex spilling error bytes to end-of-line.
        for src in [
            "const x = <A>{p}</A>\n",
            "const x = (<W><M {...props} /></W>)\n",
            "const f = (\n  <F>\n    plain text child\n  </F>\n)\n",
        ] {
            let t = texts(src);
            assert!(
                t.iter().all(|(k, _)| *k != kind::ERROR),
                "error token in {src:?}: {t:?}"
            );
        }
        // A spaced `<` comparison still allows a regex on its right.
        let r = texts("const ok = a < /b/.test(s);");
        assert!(r.iter().any(|(k, s)| *k == kind::REGEX && s == "/b/"));
    }

    #[test]
    fn jsx_self_close_after_expression_attribute_is_not_a_regex() {
        // After `}` the value-context heuristic expects an expression, so the
        // `/` of a self-closing `/>` used to scan as a regex, die at the line
        // terminator, and surface error bytes. An unterminated scan proves it
        // was never a regex: the `/` must fall back to punct, error-free.
        for src in [
            "const n = <Navbar logo={x} />\n",
            "const s = <MDXContent {...props} params={params} />\n",
            "const p = (\n  <Page a={b} c={d} />\n)\n",
        ] {
            let t = texts(src);
            assert!(
                t.iter().all(|(k, _)| *k != kind::ERROR),
                "error token in {src:?}: {t:?}"
            );
            assert!(
                t.iter().any(|(k, s)| *k == kind::PUNCT && s == "/"),
                "self-close slash must lex as punct in {src:?}: {t:?}"
            );
        }
        // A genuine regex in expression position still lexes as one.
        let r = texts("const re = /re/.test(s);");
        assert!(r.iter().any(|(k, s)| *k == kind::REGEX && s == "/re/"));
    }

    #[test]
    fn numbers_including_bigint_and_separators() {
        let t = texts("0b1010 0o17 0xAFn 10_000 3.14 2e10 .5 99n");
        assert!(t.contains(&(kind::INT, "0b1010".to_string())));
        assert!(t.contains(&(kind::INT, "0xAFn".to_string())));
        assert!(t.contains(&(kind::INT, "10_000".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14".to_string())));
        assert!(t.contains(&(kind::FLOAT, ".5".to_string())));
        assert!(t.contains(&(kind::INT, "99n".to_string())));
    }

    #[test]
    fn private_names_and_optional_chaining() {
        let t = texts("this.#count?.toFixed(2)");
        assert!(t.contains(&(kind::PRIVATE_NAME, "#count".to_string())));
        assert!(t.contains(&(kind::PUNCT, "?.".to_string())));
    }

    #[test]
    fn unterminated_string_is_error_not_dropped() {
        let t = texts("x = 'oops\n");
        assert!(t.iter().any(|(k, _)| *k == kind::ERROR));
        assert!(covers_all("x = 'oops\n"));
    }
}
