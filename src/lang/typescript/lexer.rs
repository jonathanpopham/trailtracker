//! Lossless TypeScript / TSX lexer, grounded in the ECMAScript + TypeScript
//! token grammars.
//!
//! Guarantees (identical contract to the Rust and Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (whitespace, line/block comments, a leading shebang) are emitted as
//!   `trivia` tokens, never discarded. The parser skips them for structure but
//!   the tree keeps them.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//!
//! Two ECMAScript-specific hazards are handled head-on:
//!
//! * **Template literals** (`` `a ${expr} b` ``) nest arbitrarily: a substitution
//!   can contain code, strings, and further template literals. The whole template
//!   — interpolations included — is scanned as a *single* `template_literal`
//!   token using an explicit mode stack (never recursion), so deeply nested
//!   `${`…`}` cannot overflow the stack, and the bytes are preserved exactly. This
//!   mirrors how the Python lexer treats an f-string as one token.
//! * **`/` is ambiguous** between division and a regex literal. We disambiguate
//!   with the standard pragmatic heuristic — a regex may begin only where an
//!   expression is expected, decided from the previous significant token. A wrong
//!   guess never breaks losslessness: both readings cover the same bytes, so the
//!   tree still round-trips; only downstream precision is affected.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_` and `$` as a pragmatic stand-in for the full
//! ECMAScript `ID_Start`/`ID_Continue` tables (and Unicode escapes in
//! identifiers). Anything outside still lands in the tree as a covered token,
//! never dropped. JSX in `.tsx` is not lexed as a distinct construct: its angle
//! brackets, names, and text lex as ordinary punctuation/identifiers/strings and
//! reconstruct byte-for-byte; the semantic shape is simply not modelled.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// TypeScript reserved + contextual keywords. Like the Rust/Python lexers these
/// lex as `ident` tokens; the parser and lowering distinguish them via
/// [`is_keyword`].
pub const KEYWORDS: &[&str] = &[
    // ECMAScript reserved words.
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
    "await",
    "let",
    "static",
    "async",
    // TypeScript contextual keywords.
    "abstract",
    "accessor",
    "any",
    "as",
    "asserts",
    "bigint",
    "boolean",
    "constructor",
    "declare",
    "from",
    "get",
    "implements",
    "infer",
    "interface",
    "is",
    "keyof",
    "module",
    "namespace",
    "never",
    "number",
    "object",
    "of",
    "out",
    "override",
    "package",
    "private",
    "protected",
    "public",
    "readonly",
    "require",
    "satisfies",
    "set",
    "string",
    "symbol",
    "type",
    "undefined",
    "unique",
    "unknown",
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
    /// A private class field/method name (`#name`).
    pub const PRIVATE_IDENT: &str = "private_ident";
    pub const NUMBER: &str = "number_literal";
    pub const STRING: &str = "string_literal";
    pub const TEMPLATE: &str = "template_literal";
    pub const REGEX: &str = "regex_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
const OPERATORS: &[&str] = &[
    ">>>=", "**=", "<<=", ">>=", "&&=", "||=", "??=", "...", ">>>", "===", "!==", "=>", "?.", "??",
    "**", "==", "!=", "<=", ">=", "&&", "||", "++", "--", "+=", "-=", "*=", "/=", "%=", "&=", "|=",
    "^=", "<<", ">>",
];

const SINGLE_PUNCT: &str = "+-*/%!&|^~<>=.,;:?()[]{}@#";

pub fn lex(source: &str) -> Vec<Token> {
    Lexer::new(source).run()
}

struct Lexer<'s> {
    src: &'s str,
    bytes: &'s [u8],
    pos: usize,
    tokens: Vec<Token>,
    /// Whether the previously emitted significant token ends a value, so a
    /// following `/` is division rather than the start of a regex literal.
    prev_ends_value: bool,
}

impl<'s> Lexer<'s> {
    fn new(src: &'s str) -> Self {
        Lexer {
            src,
            bytes: src.as_bytes(),
            pos: 0,
            tokens: Vec::new(),
            prev_ends_value: false,
        }
    }

    fn run(mut self) -> Vec<Token> {
        // A leading `#!` line (script shebang) is trivia, like the Rust lexer.
        if self.src.starts_with("#!") {
            let end = self.find_line_end(0);
            self.push(kind::SHEBANG, 0, end, true);
            self.pos = end;
        }

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
                // A `/` flush against a preceding `<` is the JSX closing-tag
                // delimiter `</`, never a regex start: reading it as a regex
                // runs unterminated to end-of-line and surfaces error bytes,
                // breaking the header's "JSX lexes as ordinary tokens and
                // reconstructs byte-for-byte" contract. (`x < /re/` with a
                // space still lexes as a regex; the `</` slash falls through
                // to the punct arm.)
                '/' if !(self.prev_ends_value || start > 0 && self.bytes[start - 1] == b'<') => {
                    self.regex(start)
                }
                '"' | '\'' => self.string(start, c),
                '`' => self.template(start),
                '#' if starts_ident(self.peek_at(1)) => self.private_ident(start),
                c if is_ident_start(c) => self.ident(start),
                c if c.is_ascii_digit() => self.number(start),
                '.' if self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) => {
                    self.number(start)
                }
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

    fn block_comment(&mut self, start: usize) {
        // ECMAScript block comments do *not* nest.
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

    fn private_ident(&mut self, start: usize) {
        self.bump(); // #
        self.eat_while(is_ident_continue);
        self.push(kind::PRIVATE_IDENT, start, self.pos, false);
    }

    /// Scan a `'...'` / `"..."` string literal. Handles backslash escapes; an
    /// unterminated string (newline or EOF before the closing quote) becomes an
    /// `error` token over what was consumed, never a silent drop.
    fn string(&mut self, start: usize, quote: char) {
        self.bump(); // opening quote
        let terminated = self.consume_string_body(quote);
        let token_kind = if terminated {
            kind::STRING
        } else {
            kind::ERROR
        };
        self.push(token_kind, start, self.pos, false);
    }

    /// Consume a string body up to and including the closing `quote`. Returns
    /// whether the string was properly terminated. A line continuation
    /// (`\` then newline) is permitted; a bare newline ends an unterminated
    /// string. The cursor starts just past the opening quote.
    fn consume_string_body(&mut self, quote: char) -> bool {
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '\\' {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
            } else if c == quote {
                self.bump();
                return true;
            } else if c == '\n' || c == '\r' {
                return false;
            } else {
                self.bump();
            }
        }
        false
    }

    /// Scan a whole template literal `` `...${expr}...` ``, interpolations and any
    /// nested templates included, as a single token. Uses an explicit mode stack
    /// so arbitrarily deep `${`…`}` nesting cannot overflow the stack (a
    /// `catch_unwind` cannot catch a stack overflow). The cursor starts at the
    /// opening backtick.
    fn template(&mut self, start: usize) {
        self.bump(); // opening backtick
                     // Each stack frame is either template-text or a `${ }` substitution; the
                     // u32 in a substitution counts open braces so a `}` inside nested braces
                     // does not close the interpolation prematurely. The stack is mutated
                     // freely each step (no borrow held across the body), so it cannot recurse
                     // or overflow no matter how deeply `${`…`}` nests.
        #[derive(Clone, Copy)]
        enum Mode {
            Text,
            Subst(u32),
        }
        let mut stack: Vec<Mode> = vec![Mode::Text];
        // Previous significant byte *inside the current substitution*, used to
        // decide whether a `/` starts a regex literal or is division — the same
        // ambiguity the top-level lexer resolves with `prev_ends_value`. Without
        // this, a regex inside a substitution (e.g. `` `${s.replace(/"/g, '')}` ``)
        // lets the `"` inside the regex start a bogus string that runs on and
        // desyncs the brace tracking, spilling the whole template into an error
        // token. Reset to `None` (expression expected) at each new `${`.
        let mut last_sig: Option<u8> = None;
        while !stack.is_empty() {
            if self.pos >= self.bytes.len() {
                break; // unterminated
            }
            match *stack.last().unwrap() {
                Mode::Text => {
                    let c = self.peek();
                    if c == '\\' {
                        self.bump();
                        if self.pos < self.bytes.len() {
                            self.bump();
                        }
                    } else if c == '`' {
                        self.bump();
                        stack.pop(); // closes this template level
                    } else if c == '$' && self.peek_at(1) == Some('{') {
                        self.pos += 2; // ${
                        stack.push(Mode::Subst(0));
                        last_sig = None; // fresh expression context
                    } else {
                        self.bump();
                    }
                }
                Mode::Subst(_) => {
                    let sub_start = self.pos;
                    let c = self.peek();
                    match c {
                        '{' => {
                            if let Some(Mode::Subst(b)) = stack.last_mut() {
                                *b += 1;
                            }
                            self.bump();
                        }
                        '}' => {
                            let depth = match stack.last() {
                                Some(Mode::Subst(b)) => *b,
                                _ => 0,
                            };
                            if depth == 0 {
                                self.bump();
                                stack.pop(); // closes this `${ }`
                            } else {
                                if let Some(Mode::Subst(b)) = stack.last_mut() {
                                    *b -= 1;
                                }
                                self.bump();
                            }
                        }
                        '`' => {
                            self.bump();
                            stack.push(Mode::Text); // a nested template literal
                        }
                        '\'' | '"' => {
                            self.bump();
                            self.consume_string_body(c);
                        }
                        '/' if self.peek_at(1) == Some('/') => {
                            self.pos = self.find_line_end(self.pos);
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
                            // Regex candidate. Scanning it as a unit keeps its
                            // quotes/brackets/braces from being read as string
                            // starts or interpolation delimiters. If it runs to a
                            // line terminator it was never a regex (division);
                            // rewind to just past the `/` and let it re-lex.
                            self.scan_subst_regex();
                        }
                        _ => self.bump(),
                    }
                    // Remember the last non-whitespace byte we consumed so the
                    // next `/` can tell regex from division.
                    if self.pos > sub_start {
                        if let Some(&b) = self.bytes.get(self.pos - 1) {
                            if !b.is_ascii_whitespace() {
                                last_sig = Some(b);
                            }
                        }
                    }
                }
            }
        }
        // Terminated iff every level closed (the stack drained); an EOF break
        // leaves frames behind and the bytes become an `error` token.
        let token_kind = if stack.is_empty() {
            kind::TEMPLATE
        } else {
            kind::ERROR
        };
        self.push(token_kind, start, self.pos, false);
    }

    /// Scan a regex literal `/body/flags`. A `/` inside a character class `[...]`
    /// does not terminate the regex; escapes are honored. A regex literal can
    /// never contain an unescaped line terminator, so a scan that hits one
    /// proves the `/` was never a regex — the value-context heuristic
    /// misjudged it (after `}` the self-closing JSX `/>` in
    /// `<Navbar logo={x} />` looks like a regex start). The scan rewinds and
    /// the `/` lexes as ordinary punct; the following bytes re-lex normally.
    /// The cursor starts at the opening `/`.
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
            match c {
                '\n' | '\r' => break,
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
            // Trailing flags (`g`, `i`, `m`, `s`, `u`, `y`, `d`).
            self.eat_while(is_ident_continue);
            self.push(kind::REGEX, start, self.pos, false);
        } else {
            // Unterminated ⇒ not a regex at all (see the doc comment): emit
            // the `/` as punct and re-lex from the next byte.
            self.pos = start + 1;
            self.push(kind::PUNCT, start, self.pos, false);
        }
    }

    /// Scan a regex literal starting at the cursor (`/`), used inside a template
    /// substitution where regex/division ambiguity is resolved by the caller.
    /// Honors `\` escapes and `[...]` character classes; a line terminator before
    /// the closing `/` proves it was never a regex, so the cursor rewinds to just
    /// past the opening `/` (division) and the rest re-lexes normally. Never
    /// pushes a token — the enclosing `template` scan owns the byte span.
    fn scan_subst_regex(&mut self) {
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
            match c {
                '\n' | '\r' => break,
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

    fn number(&mut self, start: usize) {
        if self.peek() == '0' {
            match self.peek_at(1) {
                Some('x') | Some('X') => {
                    self.pos += 2;
                    self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
                    self.eat_bigint_suffix();
                    return self.push(kind::NUMBER, start, self.pos, false);
                }
                Some('o') | Some('O') => {
                    self.pos += 2;
                    self.eat_while(|c| ('0'..='7').contains(&c) || c == '_');
                    self.eat_bigint_suffix();
                    return self.push(kind::NUMBER, start, self.pos, false);
                }
                Some('b') | Some('B') => {
                    self.pos += 2;
                    self.eat_while(|c| c == '0' || c == '1' || c == '_');
                    self.eat_bigint_suffix();
                    return self.push(kind::NUMBER, start, self.pos, false);
                }
                _ => {}
            }
        }
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        // Fractional part only if a digit follows the dot — keeps member access
        // `x.foo` and the spread `...` lexing as expected.
        if self.peek() == '.' {
            self.bump(); // .
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
                self.bump(); // e
                if sign_len == 1 {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit() || c == '_');
            }
        }
        self.eat_bigint_suffix();
        self.push(kind::NUMBER, start, self.pos, false);
    }

    /// A trailing `n` makes the literal a BigInt; consumed as part of the number.
    fn eat_bigint_suffix(&mut self) {
        if self.peek() == 'n' {
            self.bump();
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
        if !trivia {
            self.prev_ends_value = ends_value(kind, &self.src[start..end]);
        }
        self.tokens.push(Token {
            kind,
            span: ByteSpan::new(start, end),
            trivia,
        });
    }
}

/// Decide whether a just-emitted significant token ends a value expression, so a
/// following `/` is division. The complement is "an expression is expected here",
/// where `/` begins a regex literal. This is the standard pragmatic ASI-free
/// heuristic; it can only mis-tag rare cases, never break losslessness.
fn ends_value(kind: &str, text: &str) -> bool {
    match kind {
        kind::NUMBER | kind::STRING | kind::TEMPLATE | kind::REGEX | kind::PRIVATE_IDENT => true,
        kind::IDENT => match text {
            // Keywords that expect an expression to follow → regex, not division.
            "return" | "typeof" | "instanceof" | "in" | "of" | "new" | "delete" | "void"
            | "throw" | "do" | "else" | "yield" | "await" | "case" | "extends" | "default" => false,
            // `this`/`super`/literals are values; any other identifier is a value.
            _ => true,
        },
        kind::PUNCT => match text {
            // A closing `)` or `]` ends a value (division follows). A `}` is
            // treated as a block end (expression expected → regex). Every other
            // operator/opener expects an operand → regex.
            ")" | "]" => true,
            _ => false,
        },
        _ => false,
    }
}

/// Whether a `/` following byte `last` (the previous significant byte within a
/// template substitution) begins a regex literal rather than division. Division
/// follows a value: an identifier/number byte, a closing `)`/`]`, or a closing
/// string/template quote. Everything else (operators, openers, `,`, `:`, `?`,
/// `{`, `}`, or the very start of the substitution) expects an operand, so `/`
/// starts a regex. Byte-level analogue of `ends_value`; a rare mis-tag can only
/// affect precision, never losslessness.
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
            "function f(x) { return x; }",
            "const x = 1.5e3 + 0xFF_u;\n",
            "// comment\nlet y = 0b1010n;",
            "/* block */ const s = `a ${b + `c ${d}`} e`;",
            "let r = /ab[/]c/gi; x / y;",
            "#!/usr/bin/env ts-node\nclass C {}",
            "const t = \"he\\\"llo\" + 'w';",
            "λ = '☃ €'; // unicode",
            "this.#priv = 1;",
            "type T = A<B, C>;",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("function add(a: number): number { return a; }");
        assert!(t.contains(&(kind::IDENT, "function".to_string())));
        assert!(t.contains(&(kind::IDENT, "add".to_string())));
        assert!(t.contains(&(kind::PUNCT, "(".to_string())));
        assert!(t.contains(&(kind::PUNCT, ":".to_string())));
        assert!(is_keyword("function"));
        assert!(is_keyword("interface"));
        assert!(!is_keyword("add"));
    }

    #[test]
    fn template_with_nested_interpolation_is_one_token() {
        let t = texts("`a ${ f(`x ${y}`) } b`");
        assert!(
            t.iter()
                .any(|(k, s)| *k == kind::TEMPLATE && s == "`a ${ f(`x ${y}`) } b`"),
            "nested template should be a single token: {t:?}"
        );
    }

    #[test]
    fn regex_inside_template_substitution_is_not_error() {
        // Regression: `${ ... /re/ ... }` used to let a quote inside the regex
        // (`/"/g`) start a bogus string that ran on, desynced the brace stack,
        // and spilled the whole template into an `error` token — 10,937 error
        // bytes across two bio-mcp-client files. The regex must be consumed as a
        // unit so the template still closes as a single lossless token.
        for src in [
            // The exact bio-mcp-client construct (`quoteIdent`/`escapeIdent`).
            r#"function q(n: string): string { return `"${n.replace(/"/g, '""')}"`; }"#,
            // Regex with a character class containing a brace and a slash.
            "const t = `x ${s.replace(/[/}]/g, '_')} y`;",
            // Regex after `(` then flags, followed by more interpolation text.
            "const u = `${a.match(/\\d+/)![0]} of ${b}`;",
            // Division inside a substitution must still be division (no regex).
            "const v = `${width / 2}px ${height / 2}px`;",
        ] {
            let t = texts(src);
            assert!(
                t.iter().all(|(k, _)| *k != kind::ERROR),
                "error token in {src:?}: {t:?}"
            );
            assert!(covers_all(src), "not contiguous: {src:?}");
            // The whole template is one lossless token.
            assert_eq!(
                t.iter().filter(|(k, _)| *k == kind::TEMPLATE).count(),
                1,
                "template should be exactly one token: {src:?} -> {t:?}"
            );
        }
    }

    #[test]
    fn regex_vs_division() {
        // After `=` an expression is expected → regex.
        let r = texts("const re = /a\\/b/g;");
        assert!(r.iter().any(|(k, s)| *k == kind::REGEX && s == "/a\\/b/g"));
        // After an identifier `/` is division.
        let d = texts("a / b / c");
        assert!(d.iter().all(|(k, _)| *k != kind::REGEX));
        assert_eq!(d.iter().filter(|(k, _)| *k == kind::PUNCT).count(), 2);
    }

    #[test]
    fn jsx_closing_tag_is_not_a_regex() {
        // `</` is the JSX closing-tag delimiter: the slash must lex as punct,
        // never as an unterminated regex spilling error bytes to end-of-line.
        for src in [
            "const x = <Wrapper toc={toc}>{children}</Wrapper>\n",
            "const f = (\n  <Footer>\n    plain text child\n  </Footer>\n)\n",
            "function f({ c }: { c: X }) { return <body>{c}</body> }\n",
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
            "const s = <Row {...props} />\n",
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
        // A genuine regex after `}` still lexes as one.
        let r = texts("if (x) {} /re/.test(s);");
        assert!(r.iter().any(|(k, s)| *k == kind::REGEX && s == "/re/"));
    }

    #[test]
    fn numbers_and_bigint() {
        let t = texts("0xFF 0o17 0b1010 1_000 3.14 2e10 42n");
        for lit in ["0xFF", "0o17", "0b1010", "1_000", "3.14", "2e10", "42n"] {
            assert!(
                t.iter().any(|(k, s)| *k == kind::NUMBER && s == lit),
                "number not recognized: {lit}"
            );
        }
    }

    #[test]
    fn private_field_is_one_token() {
        let t = texts("obj.#count");
        assert!(t.contains(&(kind::PRIVATE_IDENT, "#count".to_string())));
    }

    #[test]
    fn operators_are_greedy() {
        let t = texts("a >>>= b; c ??= d; e === f;");
        assert!(t.contains(&(kind::PUNCT, ">>>=".to_string())));
        assert!(t.contains(&(kind::PUNCT, "??=".to_string())));
        assert!(t.contains(&(kind::PUNCT, "===".to_string())));
    }

    #[test]
    fn unterminated_forms_round_trip() {
        for src in [
            "const s = \"oops\n",  // unterminated string
            "const t = `open ${x", // unterminated template
            "/* open block",       // unterminated comment
            "const r = /open",     // unterminated regex
        ] {
            assert!(covers_all(src), "must stay contiguous: {src:?}");
        }
    }
}
