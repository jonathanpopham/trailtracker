//! Lossless Objective-C lexer: ISO C token grammar plus the `@`-directive object
//! layer (and a pragmatic subset of Objective-C++ for `.mm`).
//!
//! Guarantees (identical contract to the C/C++ and Rust lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs/form-feed, `//` and `/* */` comments, and
//!   backslash–newline line continuations) are emitted as `trivia` tokens, never
//!   discarded. `NEWLINE` is a *non-trivia* token because it terminates a
//!   preprocessing directive (`#import`, `#define`, …); ordinary code ignores it.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//!
//! Objective-C specifics handled here:
//! - `@"..."` NSString literals lex as a single `string_literal` token (the `@`
//!   prefix is folded into the literal, exactly like the C `L"..."`/`u8"..."`
//!   prefixes), while a bare `@` (introducing `@interface`, `@selector`, `@[`, …)
//!   lexes as a `punct` token so the parser can dispatch on it like the C `#`.
//! - `::` is recognized as an operator so the Objective-C++ scope operator in
//!   `.mm` files round-trips as one token; the richer C++ grammar is otherwise
//!   only lexed losslessly, not deeply classified (an honest punt — see `mod.rs`).
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic`
//! / `is_alphanumeric` plus `_`/`$` as a pragmatic stand-in for the full set of
//! identifier characters — anything outside still lands in the tree as a covered
//! token, never dropped.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// C keywords plus the Objective-C / Objective-C++ words this front end treats as
/// reserved. Like the C lexer these lex as `ident` tokens; the parser and lowering
/// distinguish them via [`is_keyword`]. The Objective-C *directive* words
/// (`interface`, `implementation`, `protocol`, `property`, `end`, …) are
/// deliberately **not** listed here: they are only meaningful right after an `@`,
/// where the parser matches them by text, and listing them would wrongly exclude
/// an identically-spelled ordinary identifier.
pub const KEYWORDS: &[&str] = &[
    // --- C (C11/C17, common C23 spellings) ---
    "auto",
    "break",
    "case",
    "char",
    "const",
    "continue",
    "default",
    "do",
    "double",
    "else",
    "enum",
    "extern",
    "float",
    "for",
    "goto",
    "if",
    "inline",
    "int",
    "long",
    "register",
    "restrict",
    "return",
    "short",
    "signed",
    "sizeof",
    "static",
    "struct",
    "switch",
    "typedef",
    "union",
    "unsigned",
    "void",
    "volatile",
    "while",
    "_Bool",
    "_Complex",
    "_Atomic",
    "_Generic",
    "_Noreturn",
    "_Static_assert",
    "_Thread_local",
    "bool",
    "true",
    "false",
    "nullptr",
    "static_assert",
    "typeof",
    // --- Objective-C builtins / contextual keywords ---
    "id",
    "self",
    "super",
    "nil",
    "Nil",
    "YES",
    "NO",
    "BOOL",
    "SEL",
    "IMP",
    "Class",
    "Protocol",
    "instancetype",
    "oneway",
    "in",
    "out",
    "inout",
    "bycopy",
    "byref",
    // --- Objective-C++ (.mm) extras, lexed-but-shallow ---
    "class",
    "namespace",
    "template",
    "typename",
    "public",
    "private",
    "protected",
    "virtual",
    "operator",
    "new",
    "delete",
    "this",
    "using",
    "constexpr",
];

pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.contains(&text)
}

pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const NEWLINE: &str = "newline";
    pub const COMMENT: &str = "comment";
    pub const LINE_CONTINUATION: &str = "line_continuation";
    pub const IDENT: &str = "ident";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const CHAR: &str = "char_literal";
    pub const STRING: &str = "string_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
/// `::` is included for Objective-C++ scope resolution in `.mm`.
const OPERATORS: &[&str] = &[
    "<<=", ">>=", "...", "->", "++", "--", "<<", ">>", "<=", ">=", "==", "!=", "&&", "||", "+=",
    "-=", "*=", "/=", "%=", "&=", "|=", "^=", "##", "::",
];

const SINGLE_PUNCT: &str = "+-*/%&|^~!<>=()[]{}:,.;?#@";

/// Detect a string/char literal prefix at the start of `rest`. Returns the prefix
/// length (in bytes) when `rest` is one of the C literal prefixes (`u8`, `L`,
/// `u`, `U`) immediately followed by a `"` or `'` quote; `None` otherwise.
fn lit_prefix(rest: &str) -> Option<usize> {
    let is_quote = |c: Option<char>| matches!(c, Some('"') | Some('\''));
    if let Some(after) = rest.strip_prefix("u8") {
        if is_quote(after.chars().next()) {
            return Some(2);
        }
    }
    for p in ["L", "u", "U"] {
        if let Some(after) = rest.strip_prefix(p) {
            if is_quote(after.chars().next()) {
                return Some(1);
            }
        }
    }
    None
}

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
        // Main-run-loop progress guard: every branch advances `pos` (the final
        // `_` arm bumps at least one char), so the loop cannot spin in place.
        while self.pos < self.bytes.len() {
            let start = self.pos;
            let c = self.peek();
            match c {
                '\n' => {
                    self.bump();
                    self.push(kind::NEWLINE, start, self.pos, false);
                }
                '\r' => {
                    self.bump();
                    if self.peek() == '\n' {
                        self.bump();
                    }
                    self.push(kind::NEWLINE, start, self.pos, false);
                }
                '\\' if matches!(self.peek_at(1), Some('\n') | Some('\r')) => {
                    // Explicit line continuation: backslash–newline joins lines. It
                    // is trivia so a multi-line `#define` stays one logical line.
                    self.bump(); // backslash
                    if self.peek() == '\r' {
                        self.bump();
                    }
                    if self.peek() == '\n' {
                        self.bump();
                    }
                    self.push(kind::LINE_CONTINUATION, start, self.pos, true);
                }
                ' ' | '\t' | '\x0b' | '\x0c' => {
                    self.eat_while(|c| matches!(c, ' ' | '\t' | '\x0b' | '\x0c'));
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                '/' if self.peek_at(1) == Some('/') => {
                    let end = self.find_line_end(start);
                    self.pos = end;
                    self.push(kind::COMMENT, start, end, true);
                }
                '/' if self.peek_at(1) == Some('*') => self.block_comment(start),
                '"' => self.quoted(start, '"', kind::STRING),
                '\'' => self.quoted(start, '\'', kind::CHAR),
                // Objective-C `@"..."` NSString literal: fold the `@` into the
                // string token (mirrors the C `L"..."` prefix handling).
                '@' if self.peek_at(1) == Some('"') => {
                    self.bump(); // '@'
                    self.quoted(start, '"', kind::STRING);
                }
                c if is_ident_start(c) => {
                    // A leading `L`/`u`/`U`/`u8` may be a string/char prefix.
                    if let Some(plen) = lit_prefix(&self.src[start..]) {
                        self.pos += plen;
                        let quote = self.peek();
                        let k = if quote == '"' {
                            kind::STRING
                        } else {
                            kind::CHAR
                        };
                        self.quoted(start, quote, k);
                    } else {
                        self.ident(start);
                    }
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

    fn ident(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        self.push(kind::IDENT, start, self.pos, false);
    }

    /// Scan a `/* ... */` block comment. Spans newlines; an unterminated comment
    /// runs to end of input (still covered, still lossless).
    fn block_comment(&mut self, start: usize) {
        self.pos += 2; // consume "/*"
        while self.pos < self.bytes.len() {
            if self.peek() == '*' && self.peek_at(1) == Some('/') {
                self.pos += 2;
                break;
            }
            self.bump();
        }
        self.push(kind::COMMENT, start, self.pos, true);
    }

    /// Scan a string (`"`) or character (`'`) literal. Any opening prefix (`L`,
    /// `u8`, or the Objective-C `@`) has already been consumed; the cursor is at
    /// the opening quote. Backslash escapes are honored; an unterminated literal
    /// ends at the line break and is flagged as an `error` token (never dropped).
    fn quoted(&mut self, start: usize, quote: char, ok_kind: &'static str) {
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
            if c == '\n' || c == '\r' {
                break; // unterminated single-line literal
            }
            self.bump();
        }
        let k = if terminated { ok_kind } else { kind::ERROR };
        self.push(k, start, self.pos, false);
    }

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        if self.peek() == '0' && matches!(self.peek_at(1), Some('x') | Some('X')) {
            self.pos += 2;
            self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
            if self.peek() == '.' {
                is_float = true;
                self.bump();
                self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
            }
            if matches!(self.peek(), 'p' | 'P') {
                is_float = true;
                self.bump();
                if matches!(self.peek(), '+' | '-') {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit() || c == '_');
            }
            self.eat_suffix();
            let k = if is_float { kind::FLOAT } else { kind::INT };
            return self.push(k, start, self.pos, false);
        }
        if self.peek() == '0' && matches!(self.peek_at(1), Some('b') | Some('B')) {
            self.pos += 2;
            self.eat_while(|c| c == '0' || c == '1' || c == '_');
            self.eat_suffix();
            return self.push(kind::INT, start, self.pos, false);
        }
        // Decimal / octal integer, or a float.
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        if self.peek() == '.' {
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
                self.bump();
                if sign_len == 1 {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit() || c == '_');
            }
        }
        self.eat_suffix();
        let k = if is_float { kind::FLOAT } else { kind::INT };
        self.push(k, start, self.pos, false);
    }

    /// Consume a trailing numeric suffix run (`u`, `U`, `l`, `L`, `f`, `F`).
    fn eat_suffix(&mut self) {
        self.eat_while(|c| matches!(c, 'u' | 'U' | 'l' | 'L' | 'f' | 'F'));
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
            "@interface Foo : NSObject\n@end\n",
            "#import <Foundation/Foundation.h>\n#import \"Local.h\"\n",
            "NSString *s = @\"hello\\n\"; char c = '\\n';\n",
            "- (void)setX:(int)x andY:(int)y { _x = x; }\n",
            "@property (nonatomic, strong) NSArray *items;\n",
            "id r = [obj doThing:arg with:other];\n",
            "@import Foundation;\nNSArray *a = @[ @1, @2, @\"three\" ];\n",
            "a /* block\ncomment */ b // line\nc\n",
            "ns::Type x = obj::method();\n", // Objective-C++ ::
            "λ = @\"☃\";  /* unicode */\n",
            "#define LONG 1 + \\\n  2\n",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }

    #[test]
    fn objc_string_literal_folds_at_sign() {
        let t = texts("@\"hi\\n\"");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "@\"hi\\n\""));
    }

    #[test]
    fn bare_at_is_punct() {
        let t = texts("@interface");
        assert!(t.contains(&(kind::PUNCT, "@".to_string())));
        assert!(t.contains(&(kind::IDENT, "interface".to_string())));
    }

    #[test]
    fn newline_is_structural_continuation_is_trivia() {
        let t = lex("a\nb \\\nc\n");
        assert!(t.iter().any(|tk| tk.kind == kind::NEWLINE && !tk.trivia));
        assert!(t
            .iter()
            .any(|tk| tk.kind == kind::LINE_CONTINUATION && tk.trivia));
    }

    #[test]
    fn scope_operator_is_one_token() {
        let t = texts("a::b");
        assert!(t.contains(&(kind::PUNCT, "::".to_string())));
    }

    #[test]
    fn unterminated_literal_becomes_error_not_drop() {
        let t = texts("NSString *s = @\"oops\nint x;\n");
        assert!(t.iter().any(|(k, _)| *k == kind::ERROR));
        assert!(covers_all("NSString *s = @\"oops\nint x;\n"));
    }
}
