//! Lossless Crystal lexer.
//!
//! Crystal is a Ruby-family language (keyword…`end` blocks, `def`/`class`/`module`),
//! so this lexer is closely modelled on [`crate::lang::ruby::lexer`] and honours the
//! identical lossless contract:
//! - Every byte of input is covered by exactly one token (contiguous spans), so the
//!   token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs, `#` line comments, backslash line continuations) are
//!   emitted as `trivia` tokens, never dropped. `newline` is a *non-trivia* token
//!   because it separates statements.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//!
//! Crystal differs from Ruby in ways that matter to the lexer, and these are
//! handled honestly:
//! - **Single quotes are `Char` literals**, not strings (`'a'`, `'\n'`). Double
//!   quotes are strings (`"…"`), with `#{…}` interpolation kept inside the one
//!   string token rather than re-lexed.
//! - Crystal has **no `=begin`/`=end` block comments** — only `#` line comments.
//! - Heredocs use `<<-ID` (and quoted `<<-"ID"` / `<<-'ID'`); a bare `<<ID` is
//!   treated as a left-shift to avoid misreading `arr << Const`.
//! - There is **no `?a` character literal** (Crystal chars are single-quoted), so
//!   `?` is only ever a ternary operator or a method-name predicate suffix.
//! - Backticks are not command literals in Crystal; a stray `` ` `` becomes an
//!   `error` token (unclassifiable but still retained).
//! - Numeric type suffixes (`1_i64`, `2u8`, `3.0_f32`) are absorbed into the
//!   numeric token.
//!
//! The rich context-sensitive surface (`/` is regex *or* division, `%w[...]` is a
//! word array *or* modulo) is disambiguated with a single running bit — whether the
//! previous significant token *ends a value* — exactly as Ruby's lexer does.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic` /
//! `is_alphanumeric` plus `_` as a pragmatic stand-in for Crystal's full Unicode
//! identifier rules; `@[Annotation]` lexes its leading `@` as a (nameless) ivar
//! token followed by `[`, which is lossless but not semantically distinguished.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Crystal's reserved words. Like the other lexers, these lex as `ident` tokens;
/// the parser distinguishes them via [`is_keyword`].
pub const KEYWORDS: &[&str] = &[
    "__DIR__",
    "__END_LINE__",
    "__FILE__",
    "__LINE__",
    "abstract",
    "alias",
    "annotation",
    "as",
    "as?",
    "asm",
    "begin",
    "break",
    "case",
    "class",
    "def",
    "do",
    "else",
    "elsif",
    "end",
    "ensure",
    "enum",
    "extend",
    "false",
    "for",
    "fun",
    "if",
    "in",
    "include",
    "instance_sizeof",
    "is_a?",
    "lib",
    "macro",
    "module",
    "next",
    "nil",
    "nil?",
    "of",
    "offsetof",
    "out",
    "pointerof",
    "private",
    "protected",
    "require",
    "rescue",
    "responds_to?",
    "return",
    "select",
    "self",
    "sizeof",
    "struct",
    "super",
    "then",
    "true",
    "type",
    "typeof",
    "uninitialized",
    "union",
    "unless",
    "until",
    "verbatim",
    "when",
    "while",
    "with",
    "yield",
];

pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.contains(&text)
}

/// Keywords that *end a value* — after one of these a `/` is division, not regex.
fn keyword_ends_value(text: &str) -> bool {
    matches!(
        text,
        "end"
            | "self"
            | "nil"
            | "true"
            | "false"
            | "super"
            | "uninitialized"
            | "__FILE__"
            | "__LINE__"
            | "__DIR__"
    )
}

pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const NEWLINE: &str = "newline";
    pub const COMMENT: &str = "comment";
    pub const LINE_CONTINUATION: &str = "line_continuation";
    pub const IDENT: &str = "ident";
    pub const IVAR: &str = "ivar";
    pub const CVAR: &str = "cvar";
    pub const GVAR: &str = "gvar";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const STRING: &str = "string_literal";
    pub const CHAR: &str = "char_literal";
    pub const SYMBOL: &str = "symbol_literal";
    pub const REGEX: &str = "regex_literal";
    pub const HEREDOC_OPEN: &str = "heredoc_open";
    pub const HEREDOC_BODY: &str = "heredoc_body";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
const OPERATORS: &[&str] = &[
    "**=", "<=>", "===", "...", "<<=", ">>=", "&&=", "||=", "&+", "&-", "&*", "&.", "**", "==",
    "!=", ">=", "<=", "&&", "||", "<<", ">>", "=~", "!~", "=>", "->", "::", "..", "+=", "-=", "*=",
    "/=", "%=", "|=", "&=", "^=",
];

const SINGLE_PUNCT: &str = "+-*/%&|^~<>=()[]{}:,.;!?@";

/// Operator method names that may follow a `:` to form an operator symbol
/// (`:[]`, `:<=>`, `:+`), longest first.
const SYMBOL_OPS: &[&str] = &[
    "[]=", "<=>", "===", "[]", "==", "!=", "<=", ">=", "<<", ">>", "**", "+@", "-@", "=~", "!~",
    "+", "-", "*", "/", "%", "&", "|", "^", "~", "<", ">", "!",
];

/// A pending heredoc whose body is consumed at the next newline.
struct PendingHeredoc {
    id: String,
}

pub fn lex(source: &str) -> Vec<Token> {
    Lexer::new(source).run()
}

struct Lexer<'s> {
    src: &'s str,
    bytes: &'s [u8],
    pos: usize,
    tokens: Vec<Token>,
    /// Whether the previous significant token ends a value (drives the
    /// regex/heredoc/percent disambiguation).
    prev_value_end: bool,
    /// Heredocs opened on the current logical line, awaiting their bodies.
    pending: Vec<PendingHeredoc>,
}

impl<'s> Lexer<'s> {
    fn new(src: &'s str) -> Self {
        Lexer {
            src,
            bytes: src.as_bytes(),
            pos: 0,
            tokens: Vec::new(),
            prev_value_end: false,
            pending: Vec::new(),
        }
    }

    fn run(mut self) -> Vec<Token> {
        while self.pos < self.bytes.len() {
            let before = self.pos;
            let start = self.pos;
            let c = self.peek();
            match c {
                '\n' => {
                    self.bump();
                    self.push(kind::NEWLINE, start, self.pos, false);
                    self.drain_heredocs();
                }
                '\r' => {
                    self.bump();
                    if self.peek() == '\n' {
                        self.bump();
                    }
                    self.push(kind::NEWLINE, start, self.pos, false);
                    self.drain_heredocs();
                }
                '\\' if matches!(self.peek_at(1), Some('\n') | Some('\r')) => {
                    self.bump(); // backslash
                    if self.peek() == '\r' {
                        self.bump();
                    }
                    if self.peek() == '\n' {
                        self.bump();
                    }
                    self.push(kind::LINE_CONTINUATION, start, self.pos, true);
                }
                ' ' | '\t' | '\x0c' => {
                    self.eat_while(|c| c == ' ' || c == '\t' || c == '\x0c');
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                '#' => {
                    let end = self.find_line_end(start);
                    self.pos = end;
                    self.push(kind::COMMENT, start, end, true);
                }
                '"' => self.string(start, '"'),
                '\'' => self.char_literal(start),
                '<' => {
                    if let Some((end, id)) = self.try_heredoc(start) {
                        self.pos = end;
                        self.push(kind::HEREDOC_OPEN, start, end, false);
                        self.pending.push(PendingHeredoc { id });
                    } else {
                        self.punct(start);
                    }
                }
                '%' => {
                    if let Some(end) = self.try_percent_literal(start) {
                        self.pos = end;
                        self.push(kind::STRING, start, end, false);
                    } else {
                        self.punct(start);
                    }
                }
                '/' => {
                    if self.prev_value_end {
                        self.punct(start); // division (or `/=`)
                    } else {
                        self.regex(start);
                    }
                }
                ':' => self.colon(start),
                '@' => self.at_var(start),
                '$' => self.global_var(start),
                c if is_ident_start(c) => self.name(start),
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
            // Main-loop progress guard: every iteration must consume at least one
            // byte. If a branch ever failed to advance, force progress with an
            // `error` token rather than spin forever.
            if self.pos == before {
                self.bump();
                self.push(kind::ERROR, before, self.pos, false);
            }
        }
        self.tokens
    }

    // --- identifiers / variables -------------------------------------------

    fn name(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        // Method-name predicate/bang suffix: `foo?`, `foo!`. Do not absorb the `?`
        // of `?=` (not real) or the `!` of `!=` (would corrupt `foo != bar`).
        if matches!(self.peek(), '?' | '!') && self.peek_at(1) != Some('=') {
            self.bump();
        }
        self.push(kind::IDENT, start, self.pos, false);
    }

    /// `@ivar` and `@@cvar`. A leading `@[` (annotation attribute) leaves a bare
    /// `@` ivar token followed by `[`; lossless, see the module note.
    fn at_var(&mut self, start: usize) {
        self.bump(); // first @
        let cvar = self.peek() == '@';
        if cvar {
            self.bump(); // second @
        }
        self.eat_while(is_ident_continue);
        let k = if cvar { kind::CVAR } else { kind::IVAR };
        self.push(k, start, self.pos, false);
    }

    /// `$~`, `$1`, `$?` (Crystal's special regex/process globals).
    fn global_var(&mut self, start: usize) {
        self.bump(); // $
        let c = self.peek();
        if is_ident_start(c) {
            self.eat_while(is_ident_continue);
        } else if c.is_ascii_digit() {
            self.eat_while(|c| c.is_ascii_digit());
        } else if c != '\0' {
            self.bump(); // a single special-global char ($!, $~, $&, …)
        }
        self.push(kind::GVAR, start, self.pos, false);
    }

    // --- strings ------------------------------------------------------------

    /// Scan a double-quoted string. A backslash escapes the next byte for the
    /// purpose of finding the close. Newlines are allowed inside a string in
    /// Crystal, so it spans lines until its close. `#{…}` interpolation is kept
    /// inside the single token. An unterminated string becomes an `error` token.
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
            self.bump();
        }
        let k = if terminated {
            kind::STRING
        } else {
            kind::ERROR
        };
        self.push(k, start, self.pos, false);
    }

    /// `'a'`, `'\n'`, `'\u{1F600}'` — a single-quoted character literal. Scans to
    /// the closing quote (honouring backslash escapes) on the same line; an
    /// unterminated literal becomes an `error` token but its bytes are retained.
    fn char_literal(&mut self, start: usize) {
        self.bump(); // opening '
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
            if c == '\n' {
                break; // unterminated on this line
            }
            if c == '\'' {
                self.bump();
                terminated = true;
                break;
            }
            self.bump();
        }
        let k = if terminated { kind::CHAR } else { kind::ERROR };
        self.push(k, start, self.pos, false);
    }

    // --- symbols ------------------------------------------------------------

    fn colon(&mut self, start: usize) {
        // `::` scope operator.
        if self.peek_at(1) == Some(':') {
            return self.punct(start);
        }
        match self.peek_at(1) {
            Some('"') => {
                self.bump(); // :
                self.string(start, '"');
                // `string` pushed a STRING token over [start..]; relabel as a symbol.
                self.relabel_last(kind::SYMBOL);
            }
            Some(c) if is_ident_start(c) => {
                self.bump(); // :
                self.eat_while(is_ident_continue);
                if matches!(self.peek(), '?' | '!' | '=') {
                    self.bump();
                }
                self.push(kind::SYMBOL, start, self.pos, false);
            }
            Some(_) => {
                // Operator symbol: `:[]`, `:<=>`, `:+`.
                let rest = &self.src[self.pos + 1..];
                if let Some(op) = SYMBOL_OPS.iter().find(|op| rest.starts_with(**op)) {
                    self.pos += 1 + op.len();
                    self.push(kind::SYMBOL, start, self.pos, false);
                } else {
                    self.punct(start);
                }
            }
            None => self.punct(start),
        }
    }

    fn relabel_last(&mut self, k: &'static str) {
        if let Some(t) = self.tokens.last_mut() {
            t.kind = k;
            t.trivia = false;
        }
    }

    // --- regex --------------------------------------------------------------

    fn regex(&mut self, start: usize) {
        self.bump(); // opening /
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
            if c == '\n' {
                break; // unterminated regex on this line
            }
            if c == '/' {
                self.bump();
                terminated = true;
                break;
            }
            self.bump();
        }
        if terminated {
            // Trailing flags: i, m, x.
            self.eat_while(|c| matches!(c, 'i' | 'm' | 'x'));
            self.push(kind::REGEX, start, self.pos, false);
        } else {
            self.push(kind::ERROR, start, self.pos, false);
        }
    }

    // --- percent literals ---------------------------------------------------

    /// `%w[..]`, `%i(..)`, `%q{..}`, `%Q<..>`, `%r{..}x`, `%(..)`. Returns the end
    /// offset of the literal, or `None` if this `%` is the modulo operator.
    fn try_percent_literal(&mut self, start: usize) -> Option<usize> {
        let after = self.peek_at(1)?;
        // `%=` is modulo-assign, not a literal.
        if after == '=' {
            return None;
        }
        let (typed, delim_idx) = match after {
            'w' | 'W' | 'i' | 'I' | 'q' | 'Q' | 'r' | 's' | 'x' => (true, start + 2),
            _ => (false, start + 1),
        };
        let delim = self.src[delim_idx..].chars().next()?;
        // A valid percent-literal delimiter is a non-alphanumeric, non-space char.
        if delim.is_alphanumeric() || delim.is_whitespace() {
            return None;
        }
        // A bare `%(...)` is only a literal at a value-begin position; otherwise it
        // is modulo (`a % (b)`).
        if !typed && self.prev_value_end {
            return None;
        }
        let close = match delim {
            '(' => ')',
            '[' => ']',
            '{' => '}',
            '<' => '>',
            other => other,
        };
        let nests = delim != close;
        let mut p = delim_idx + delim.len_utf8();
        let mut depth = 1i32;
        while p < self.bytes.len() {
            let ch = self.src[p..].chars().next().unwrap_or('\0');
            if ch == '\\' {
                p += 1;
                if p < self.bytes.len() {
                    p += self.src[p..]
                        .chars()
                        .next()
                        .map(|c| c.len_utf8())
                        .unwrap_or(1);
                }
                continue;
            }
            if nests && ch == delim {
                depth += 1;
            } else if ch == close {
                depth -= 1;
                p += ch.len_utf8();
                if depth == 0 {
                    break;
                }
                continue;
            }
            p += ch.len_utf8();
        }
        // Trailing regex flags for `%r`.
        if after == 'r' {
            while p < self.bytes.len() {
                let ch = self.src[p..].chars().next().unwrap_or('\0');
                if matches!(ch, 'i' | 'm' | 'x') {
                    p += 1;
                } else {
                    break;
                }
            }
        }
        Some(p)
    }

    // --- heredocs -----------------------------------------------------------

    /// Detect a heredoc opener at `start` (cursor on the first `<`). Crystal uses
    /// `<<-ID` and the quoted forms `<<-"ID"` / `<<-'ID'`. Returns
    /// `(end_of_opener, identifier)` or `None` (then `<<` is an operator).
    fn try_heredoc(&self, start: usize) -> Option<(usize, String)> {
        if self.peek_at(1) != Some('<') {
            return None; // not `<<`
        }
        let mut p = start + 2;
        let dash = self.byte_at(p) == Some(b'-');
        if dash {
            p += 1;
        }
        // Optional quote.
        let quote = match self.byte_at(p) {
            Some(b'"') => Some(b'"'),
            Some(b'\'') => Some(b'\''),
            _ => None,
        };
        if quote.is_some() {
            p += 1;
        }
        // A bare `<<ID` (no `-`, no quote) is ambiguous with left-shift; only accept
        // it when dashed or quoted.
        if !dash && quote.is_none() {
            return None;
        }
        let id_start = p;
        while let Some(b) = self.byte_at(p) {
            if (b as char).is_ascii_alphanumeric() || b == b'_' {
                p += 1;
            } else {
                break;
            }
        }
        if p == id_start {
            return None; // no identifier
        }
        let id = self.src[id_start..p].to_string();
        if let Some(q) = quote {
            if self.byte_at(p) == Some(q) {
                p += 1;
            } else {
                return None; // unterminated quoted delimiter
            }
        }
        Some((p, id))
    }

    /// At a newline, consume every pending heredoc body in FIFO order. Each body
    /// runs from the cursor to (and including) its terminator line; if EOF arrives
    /// first the body extends to EOF. Either way the bytes stay in the tree.
    fn drain_heredocs(&mut self) {
        if self.pending.is_empty() {
            return;
        }
        let pending = std::mem::take(&mut self.pending);
        for h in pending {
            let body_start = self.pos;
            let mut line_start = self.pos;
            let mut body_end = self.bytes.len();
            while line_start < self.bytes.len() {
                let line_end = match self.src[line_start..].find('\n') {
                    Some(i) => line_start + i + 1,
                    None => self.bytes.len(),
                };
                let line = &self.src[line_start..line_end];
                let trimmed = line.trim_start_matches([' ', '\t']);
                let trimmed = trimmed.trim_end_matches(['\n', '\r']);
                if trimmed == h.id {
                    body_end = line_end;
                    break;
                }
                line_start = line_end;
            }
            self.pos = body_end;
            self.push(kind::HEREDOC_BODY, body_start, body_end, false);
        }
    }

    // --- numbers ------------------------------------------------------------

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        if self.peek() == '0' {
            match self.peek_at(1) {
                Some('x') | Some('X') => {
                    self.pos += 2;
                    self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
                    return self.finish_number(start, false);
                }
                Some('o') | Some('O') => {
                    self.pos += 2;
                    self.eat_while(|c| ('0'..='7').contains(&c) || c == '_');
                    return self.finish_number(start, false);
                }
                Some('b') | Some('B') => {
                    self.pos += 2;
                    self.eat_while(|c| c == '0' || c == '1' || c == '_');
                    return self.finish_number(start, false);
                }
                _ => {}
            }
        }
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
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
                self.bump();
                if sign_len == 1 {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit() || c == '_');
            }
        }
        self.finish_number(start, is_float);
    }

    /// Absorb a trailing Crystal numeric type suffix (`_i64`, `i32`, `u8`, `f32`,
    /// `_f64`) when one is genuinely present, then push.
    fn finish_number(&mut self, start: usize, is_float: bool) {
        let mark = self.pos;
        if self.peek() == '_' {
            self.bump();
        }
        let mut suffix = false;
        if matches!(self.peek(), 'i' | 'u' | 'f') {
            let after = self.peek_at(1);
            if matches!(after, Some(d) if d.is_ascii_digit()) {
                self.bump(); // i/u/f
                self.eat_while(|c| c.is_ascii_digit());
                suffix = true;
            }
        }
        if !suffix {
            self.pos = mark; // no valid suffix; restore
        }
        let k = if is_float { kind::FLOAT } else { kind::INT };
        self.push(k, start, self.pos, false);
    }

    // --- punctuation / operators -------------------------------------------

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

    fn byte_at(&self, idx: usize) -> Option<u8> {
        self.bytes.get(idx).copied()
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
            self.prev_value_end = self.compute_value_end(kind, start, end);
        }
        self.tokens.push(Token {
            kind,
            span: ByteSpan::new(start, end),
            trivia,
        });
    }

    /// Whether the token just produced ends a value (used by the next token's
    /// context-sensitive decisions). Trivia never changes the running bit.
    fn compute_value_end(&self, kind: &'static str, start: usize, end: usize) -> bool {
        match kind {
            kind::NEWLINE => false,
            kind::IDENT => {
                let text = self.src.get(start..end).unwrap_or("");
                if is_keyword(text) {
                    keyword_ends_value(text)
                } else {
                    true
                }
            }
            kind::IVAR
            | kind::CVAR
            | kind::GVAR
            | kind::INT
            | kind::FLOAT
            | kind::STRING
            | kind::CHAR
            | kind::SYMBOL
            | kind::REGEX
            | kind::HEREDOC_BODY
            | kind::HEREDOC_OPEN => true,
            kind::PUNCT => matches!(self.src.get(start..end), Some(")") | Some("]") | Some("}")),
            _ => false,
        }
    }
}

fn is_ident_start(c: char) -> bool {
    c == '_' || c.is_alphabetic()
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
            "def add(a : Int32, b : Int32) : Int32\n  a + b\nend\n",
            "class C < Base\n  def m; end\nend\n",
            "x = 0xFF_00 + 1.5e3 + 3_i64 + 2u8 + 1.0_f32\n",
            "s = \"a #{x} b\"\nc = 'q'\nn = '\\n'\n",
            "w = %w[a b c] + %i(x y) + %q{z}\n",
            "r = /ab+c/i\nq = a / b\n",
            "sym = :foo + :\"bar\" + :<=> + :[]\n",
            "doc = <<-SQL\n  select 1\nSQL\nputs doc\n",
            "a = b  # comment\nfoo \\\n  + bar\n",
            "λ = \"☃ €\"  # unicode\n",
            "@x = @@y + $1\nstruct S\nend\n",
            "@[Link(\"foo\")]\nlib LibC\nend\n",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
            let rebuilt: String = lex(src)
                .iter()
                .map(|t| t.span.text(src))
                .collect::<Vec<_>>()
                .join("");
            assert_eq!(rebuilt, src, "not lossless: {src:?}");
        }
    }

    #[test]
    fn single_quote_is_a_char_not_a_string() {
        let t = texts("c = 'a'\ns = \"a\"\n");
        assert!(t.contains(&(kind::CHAR, "'a'".to_string())));
        assert!(t.contains(&(kind::STRING, "\"a\"".to_string())));
    }

    #[test]
    fn numeric_type_suffixes() {
        let t = texts("a = 1_i64\nb = 2u8\nc = 3.0_f32\nd = 4i32\n");
        assert!(t.contains(&(kind::INT, "1_i64".to_string())));
        assert!(t.contains(&(kind::INT, "2u8".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.0_f32".to_string())));
        assert!(t.contains(&(kind::INT, "4i32".to_string())));
        // A trailing letter without digits is *not* a suffix: `1.times`.
        let t2 = texts("1.times { }\n");
        assert!(t2.contains(&(kind::INT, "1".to_string())));
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("def add(a, b)\n  a + b\nend\n");
        assert!(t.contains(&(kind::IDENT, "def".to_string())));
        assert!(t.contains(&(kind::IDENT, "add".to_string())));
        assert!(t.contains(&(kind::PUNCT, "(".to_string())));
        assert!(t.iter().any(|(k, _)| *k == kind::NEWLINE));
        assert!(is_keyword("def"));
        assert!(is_keyword("struct"));
        assert!(!is_keyword("add"));
    }

    #[test]
    fn heredoc_body_is_one_token() {
        let t = texts("doc = <<-SQL\n  select 1\nSQL\nx = 1\n");
        assert!(t.iter().any(|(k, _)| *k == kind::HEREDOC_OPEN));
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::HEREDOC_BODY && s.contains("select 1") && s.contains("SQL")));
    }

    #[test]
    fn regex_vs_division() {
        let t = texts("a / b\nx = /re/i\n");
        assert!(t.contains(&(kind::PUNCT, "/".to_string())));
        assert!(t.iter().any(|(k, s)| *k == kind::REGEX && s == "/re/i"));
    }

    #[test]
    fn symbols_and_operators() {
        let t = texts(":foo :\"bar\" :<=> :[] a <=> b\n");
        assert!(t.contains(&(kind::SYMBOL, ":foo".to_string())));
        assert!(t.contains(&(kind::SYMBOL, ":\"bar\"".to_string())));
        assert!(t.contains(&(kind::SYMBOL, ":<=>".to_string())));
        assert!(t.contains(&(kind::SYMBOL, ":[]".to_string())));
        assert!(t.contains(&(kind::PUNCT, "<=>".to_string())));
    }

    #[test]
    fn ivar_cvar_gvar() {
        let t = texts("@a = @@b + $1\n");
        assert!(t.contains(&(kind::IVAR, "@a".to_string())));
        assert!(t.contains(&(kind::CVAR, "@@b".to_string())));
        assert!(t.contains(&(kind::GVAR, "$1".to_string())));
    }

    #[test]
    fn predicate_and_bang_methods() {
        let t = texts("x.empty? && y.save!\na != b\n");
        assert!(t.contains(&(kind::IDENT, "empty?".to_string())));
        assert!(t.contains(&(kind::IDENT, "save!".to_string())));
        assert!(t.contains(&(kind::PUNCT, "!=".to_string())));
    }

    #[test]
    fn backtick_is_an_error_token_but_retained() {
        let t = texts("x = `oops`\n");
        assert!(t.iter().any(|(k, _)| *k == kind::ERROR));
        assert!(covers_all("x = `oops`\n"));
    }

    #[test]
    fn unterminated_string_and_char_round_trip() {
        for src in ["s = \"oops\n", "c = 'oops\n"] {
            let t = texts(src);
            assert!(t.iter().any(|(k, _)| *k == kind::ERROR));
            assert!(covers_all(src));
        }
    }
}
