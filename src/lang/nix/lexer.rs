//! Lossless Nix lexer, grounded in the Nix expression-language token grammar
//! (`src/libexpr/lexer.l` in the reference implementation).
//!
//! Guarantees (identical contract to the Rust and Lua lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim. The main run loop also
//!   carries an explicit progress guard: if a turn fails to advance `pos`, one
//!   char is consumed as an `error` token. A non-advancing loop would spin
//!   forever and exhaust memory, so this guard is load-bearing, not cosmetic.
//! - Trivia (whitespace, `#` line comments, `/* */` block comments) are emitted
//!   as `trivia` tokens, never discarded.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped — an unterminated string is emitted
//!   as an `error` token spanning to end of input.
//!
//! Nix-specific surface the lexer covers in full:
//! - Double-quoted strings `"…"` with `${ … }` antiquotation (interpolation) and
//!   backslash escapes, and indented strings `''…''` with their `'''`, `''$`,
//!   `''\` escapes and `${ … }` interpolation. Interpolations may themselves
//!   contain nested strings, comments and braces; the whole literal is one
//!   token. The scan is **iterative** (an explicit context stack), so hostile
//!   nesting cannot overflow the stack — only the heap stack grows.
//! - Paths: relative (`./foo`, `../bar`), absolute (`/etc/x`), home (`~/x`), and
//!   bare (`a/b/c`); plus angle-bracket search paths `<nixpkgs>` / `<nixpkgs/lib>`.
//!   Per the language, `a/b` (no surrounding spaces) is a *path*, while `a / b`
//!   is division — this lexer reproduces that.
//! - Decimal integers and floats (with `e`/`E` exponents).
//! - The Nix operator set, including `//` (update), `++` (concat), `->`
//!   (implication), `...` (formals ellipsis), and the comparison/boolean ops.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_ ' -` as a pragmatic superset of Nix's ASCII-only
//! identifier rule; path/search-path bodies use the ASCII path-char class.
//! Anything outside still lands in the tree as a covered token, never dropped.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Nix reserved words. Like the other lexers these lex as `ident` tokens; the
/// parser and lowering distinguish them via [`is_keyword`]. `import` and
/// `builtins` are deliberately **not** keywords — they are ordinary identifiers
/// (builtin functions), which is how the lowering recognizes `import`.
pub const KEYWORDS: &[&str] = &[
    "assert", "else", "if", "in", "inherit", "let", "or", "rec", "then", "with",
];

pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.contains(&text)
}

/// Token kind labels, stored on the CST as `&'static str`.
pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const LINE_COMMENT: &str = "line_comment";
    pub const BLOCK_COMMENT: &str = "block_comment";
    pub const IDENT: &str = "ident";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const STRING: &str = "string_literal";
    pub const INDENTED_STRING: &str = "indented_string_literal";
    pub const PATH: &str = "path";
    pub const SEARCH_PATH: &str = "search_path";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
const OPERATORS: &[&str] = &["...", "//", "++", "->", "==", "!=", "<=", ">=", "&&", "||"];

const SINGLE_PUNCT: &str = "+-*/<>=!?:;,.@()[]{}~$&|";

pub fn lex(source: &str) -> Vec<Token> {
    Lexer::new(source).run()
}

/// One frame of the iterative string scanner. `Interp` carries the brace nesting
/// depth *within* a single `${ … }` so a literal `{`/`}` does not falsely close
/// the antiquotation.
#[derive(Clone, Copy)]
enum SCtx {
    Short,
    Long,
    Interp(i32),
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
            if c == ' ' || c == '\t' || c == '\n' || c == '\r' || c.is_whitespace() {
                self.eat_while(|c| c.is_whitespace());
                self.push(kind::WHITESPACE, start, self.pos, true);
            } else if c == '#' {
                let end = self.find_line_end(self.pos);
                self.pos = end;
                self.push(kind::LINE_COMMENT, start, end, true);
            } else if c == '/' && self.peek_at(1) == Some('*') {
                self.block_comment(start);
            } else if c == '"' {
                let terminated = self.scan_string(false);
                let k = if terminated {
                    kind::STRING
                } else {
                    kind::ERROR
                };
                self.push(k, start, self.pos, false);
            } else if c == '\'' && self.peek_at(1) == Some('\'') {
                let terminated = self.scan_string(true);
                let k = if terminated {
                    kind::INDENTED_STRING
                } else {
                    kind::ERROR
                };
                self.push(k, start, self.pos, false);
            } else if c == '<' && self.spath_len(self.pos).is_some() {
                let end = self.spath_len(self.pos).unwrap();
                self.pos = end;
                self.push(kind::SEARCH_PATH, start, end, false);
            } else if let Some(end) = self.path_len(self.pos) {
                self.pos = end;
                self.push(kind::PATH, start, end, false);
            } else if is_ident_start(c) {
                self.eat_while(is_ident_continue);
                self.push(kind::IDENT, start, self.pos, false);
            } else if c.is_ascii_digit() {
                self.number(start);
            } else if SINGLE_PUNCT.contains(c) {
                self.punct(start);
            } else {
                self.bump();
                self.push(kind::ERROR, start, self.pos, false);
            }

            // Progress guard: every branch above advances `pos`, but if one ever
            // failed to, consume a single char as `error` so the loop can never
            // spin in place (infinite loop = OOM).
            if self.pos == start {
                self.bump();
                self.push(kind::ERROR, start, self.pos, false);
            }
        }
        self.tokens
    }

    // --- scanners -----------------------------------------------------------

    /// A `/* … */` block comment. Nix block comments do **not** nest. An
    /// unterminated comment runs to end of input and stays `trivia` — the bytes
    /// are still fully covered, so the file round-trips.
    fn block_comment(&mut self, start: usize) {
        self.pos += 2; // /*
        while self.pos < self.bytes.len() {
            if self.src[self.pos..].starts_with("*/") {
                self.pos += 2;
                break;
            }
            self.bump();
        }
        self.push(kind::BLOCK_COMMENT, start, self.pos, true);
    }

    /// Scan a string literal to its end, returning whether it terminated. Uses an
    /// explicit context stack (never recursion) so deeply nested interpolations
    /// (`"${"${"…"}"}"`) cannot overflow the call stack. `pos` advances on every
    /// loop turn, so the scan always terminates.
    fn scan_string(&mut self, indented: bool) -> bool {
        let mut stack: Vec<SCtx> = Vec::new();
        if indented {
            self.pos += 2; // ''
            stack.push(SCtx::Long);
        } else {
            self.pos += 1; // "
            stack.push(SCtx::Short);
        }
        while let Some(top) = stack.last().copied() {
            if self.pos >= self.bytes.len() {
                return false; // unterminated
            }
            match top {
                SCtx::Short => {
                    let c = self.peek();
                    if c == '\\' {
                        self.bump();
                        if self.pos < self.bytes.len() {
                            self.bump();
                        }
                    } else if c == '"' {
                        self.bump();
                        stack.pop();
                    } else if c == '$' && self.peek_at(1) == Some('{') {
                        self.pos += 2;
                        stack.push(SCtx::Interp(0));
                    } else {
                        self.bump();
                    }
                }
                SCtx::Long => {
                    let c = self.peek();
                    if c == '\'' && self.peek_at(1) == Some('\'') {
                        match self.peek_at(2) {
                            // ''' (escaped ''), ''$ (escaped $), ''\X (escape) —
                            // none of these close the string.
                            Some('\'') => self.pos += 3,
                            Some('$') => self.pos += 3,
                            Some('\\') => {
                                self.pos += 3;
                                if self.pos < self.bytes.len() {
                                    self.bump();
                                }
                            }
                            _ => {
                                self.pos += 2; // closing ''
                                stack.pop();
                            }
                        }
                    } else if c == '$' && self.peek_at(1) == Some('{') {
                        self.pos += 2;
                        stack.push(SCtx::Interp(0));
                    } else {
                        self.bump();
                    }
                }
                SCtx::Interp(_) => {
                    let c = self.peek();
                    if c == '"' {
                        self.pos += 1;
                        stack.push(SCtx::Short);
                    } else if c == '\'' && self.peek_at(1) == Some('\'') {
                        self.pos += 2;
                        stack.push(SCtx::Long);
                    } else if c == '#' {
                        // A comment inside an interpolation may contain braces.
                        let e = self.find_line_end(self.pos);
                        self.pos = e;
                    } else if c == '/' && self.peek_at(1) == Some('*') {
                        self.pos += 2;
                        while self.pos < self.bytes.len() && !self.src[self.pos..].starts_with("*/")
                        {
                            self.bump();
                        }
                        if self.pos < self.bytes.len() {
                            self.pos += 2;
                        }
                    } else if c == '$' && self.peek_at(1) == Some('{') {
                        self.pos += 2;
                        stack.push(SCtx::Interp(0));
                    } else if c == '{' {
                        if let Some(SCtx::Interp(d)) = stack.last_mut() {
                            *d += 1;
                        }
                        self.bump();
                    } else if c == '}' {
                        if let Some(SCtx::Interp(d)) = stack.last_mut() {
                            if *d == 0 {
                                self.pos += 1;
                                stack.pop();
                            } else {
                                *d -= 1;
                                self.bump();
                            }
                        } else {
                            self.bump();
                        }
                    } else {
                        self.bump();
                    }
                }
            }
        }
        true
    }

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        self.eat_while(|c| c.is_ascii_digit());
        if self.peek() == '.' && self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) {
            is_float = true;
            self.bump(); // .
            self.eat_while(|c| c.is_ascii_digit());
        }
        if matches!(self.peek(), 'e' | 'E') {
            let sign = match self.peek_at(1) {
                Some('+') | Some('-') => 1,
                _ => 0,
            };
            if self
                .src
                .get(self.pos + 1 + sign..)
                .and_then(|s| s.chars().next())
                .map(|c| c.is_ascii_digit())
                .unwrap_or(false)
            {
                is_float = true;
                self.bump(); // e
                if sign == 1 {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit());
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

    /// If a path token begins at `at`, return its end offset. A path is an
    /// optional leading `~` then path-chars, followed by **at least one** `/`
    /// group `'/' path-char+` (the slash group is what distinguishes a path from
    /// a bare identifier or number). Pure lookahead; consumes nothing.
    fn path_len(&self, at: usize) -> Option<usize> {
        let b = self.bytes;
        let mut i = at;
        if b.get(i) == Some(&b'~') {
            i += 1;
        }
        while i < b.len() && is_path_byte(b[i]) {
            i += 1;
        }
        let mut groups = 0usize;
        while i < b.len() && b[i] == b'/' && b.get(i + 1).map(|&x| is_path_byte(x)).unwrap_or(false)
        {
            i += 1; // '/'
            while i < b.len() && is_path_byte(b[i]) {
                i += 1;
            }
            groups += 1;
        }
        if groups == 0 {
            None
        } else {
            Some(i)
        }
    }

    /// If an angle-bracket search path `<…>` begins at `at` (pointing at `<`),
    /// return its end offset. Pure lookahead.
    fn spath_len(&self, at: usize) -> Option<usize> {
        let b = self.bytes;
        let mut i = at + 1;
        let mut any = false;
        while i < b.len() && (is_path_byte(b[i]) || b[i] == b'/') {
            i += 1;
            any = true;
        }
        if any && b.get(i) == Some(&b'>') {
            Some(i + 1)
        } else {
            None
        }
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
    c == '_' || c == '\'' || c == '-' || c.is_alphanumeric()
}

/// ASCII path-char class: letters, digits, and `. _ - +`.
fn is_path_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || matches!(b, b'.' | b'_' | b'-' | b'+')
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
            "{ a = 1; b = 2; }",
            "let x = 1; in x + 1",
            "# line comment\nx = 1",
            "/* block\ncomment */ y",
            "\"hello ${name} world\"",
            "''\n  indented ${x}\n  literal ''$ ok\n''",
            "import <nixpkgs> { }",
            "import ./pkgs/default.nix",
            "f = { pkgs, ... }: pkgs.hello",
            "x = a/b/c; y = a / b;",
            "n = 0xnope 1.5e3 42 ./rel + 3",
            "λ = \"☃ €\"  # unicode",
            "",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("let pkgs = import <nixpkgs>; in pkgs.hello");
        assert!(t.contains(&(kind::IDENT, "let".to_string())));
        assert!(t.contains(&(kind::IDENT, "import".to_string())));
        assert!(t.contains(&(kind::SEARCH_PATH, "<nixpkgs>".to_string())));
        assert!(is_keyword("let"));
        assert!(is_keyword("in"));
        assert!(!is_keyword("import"));
    }

    #[test]
    fn paths_vs_division() {
        // `a/b` (no spaces) is a path; `a / b` is division.
        let t = texts("a/b/c");
        assert!(t.iter().any(|(k, s)| *k == kind::PATH && s == "a/b/c"));
        let t = texts("a / b");
        assert!(t.iter().any(|(k, s)| *k == kind::PUNCT && s == "/"));
        let t = texts("./foo.nix ../bar /etc/x ~/cfg");
        assert!(t.iter().any(|(k, s)| *k == kind::PATH && s == "./foo.nix"));
        assert!(t.iter().any(|(k, s)| *k == kind::PATH && s == "../bar"));
        assert!(t.iter().any(|(k, s)| *k == kind::PATH && s == "/etc/x"));
        assert!(t.iter().any(|(k, s)| *k == kind::PATH && s == "~/cfg"));
    }

    #[test]
    fn strings_with_interpolation_are_one_token() {
        let t = texts("\"a ${ { x = \"b\"; }.x } c\"");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "\"a ${ { x = \"b\"; }.x } c\""));
        // Indented string with escapes and interpolation.
        let t = texts("''pre ${y} ''$ '''  end''");
        assert!(t.iter().any(|(k, _)| *k == kind::INDENTED_STRING));
    }

    #[test]
    fn unterminated_string_is_error_but_covered() {
        let t = texts("\"open ${ no close");
        assert!(t.iter().any(|(k, _)| *k == kind::ERROR));
        assert!(covers_all("\"open ${ no close"));
    }

    #[test]
    fn operators() {
        let t = texts("a // b ++ c -> d == e != f <= g >= h && i || j ...");
        for op in ["//", "++", "->", "==", "!=", "<=", ">=", "&&", "||", "..."] {
            assert!(
                t.contains(&(kind::PUNCT, op.to_string())),
                "missing operator {op}"
            );
        }
    }

    #[test]
    fn deeply_nested_interpolation_does_not_overflow() {
        // Iterative scanner: 5000 nested interpolations must not blow the stack.
        let depth = 5000;
        let mut src = String::new();
        for _ in 0..depth {
            src.push_str("\"${");
        }
        src.push('x');
        for _ in 0..depth {
            src.push_str("}\"");
        }
        assert!(covers_all(&src), "deep interpolation must stay covered");
    }
}
