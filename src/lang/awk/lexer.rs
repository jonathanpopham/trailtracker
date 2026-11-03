//! Lossless AWK lexer, grounded in the POSIX `awk` token grammar (with the common
//! `func`/`**`/`**=` gawk extensions).
//!
//! Guarantees (identical contract to the Rust, Python, Bash, and JavaScript
//! lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs/form-feeds, `#` line comments, backslash-newline line
//!   continuations) are emitted as `trivia` tokens, never discarded. `NEWLINE` is
//!   emitted as a *non-trivia* token because it is structurally significant in
//!   AWK: a newline terminates a rule / statement, like `;`.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes (an unterminated string runs to the line end / EOF as one `error`
//!   token; a lone backslash is one `error` token). Input is never silently
//!   dropped.
//!
//! Regex vs. division: the `/` character is contextually either a regular
//! expression literal (`/foo/`) or the division operator (`a / b`). We decide with
//! the standard previous-significant-token heuristic (mirrors the JavaScript
//! lexer). A misclassification cannot affect losslessness — the bytes are covered
//! either way, only the token *label* differs, and no graph fact depends on the
//! distinction.
//!
//! Coverage note (honest): identifier start/continue is ASCII
//! `[A-Za-z_][A-Za-z0-9_]*` (AWK identifiers are ASCII). Any other non-whitespace
//! byte the grammar does not name lands in the tree as a single covered `error`
//! token, never dropped.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// AWK control keywords (and the `function`/`func` definers). Like the other
/// lexers these lex as `ident` tokens; the parser and lowering distinguish them
/// via [`is_keyword`]. These are *not* called like user functions.
pub const KEYWORDS: &[&str] = &[
    "BEGIN", "END", "function", "func", "if", "else", "while", "for", "do", "break", "continue",
    "next", "nextfile", "exit", "return", "delete", "in", "getline", "print", "printf",
];

/// AWK built-in *functions* (callable, distinct from control keywords). A call to
/// one of these resolves to a `builtin` rather than a project function.
pub const BUILTINS: &[&str] = &[
    "length", "substr", "index", "split", "sub", "gsub", "match", "sprintf", "sin", "cos", "atan2",
    "exp", "log", "sqrt", "int", "rand", "srand", "tolower", "toupper", "system", "close",
    "fflush", "gensub", "systime", "strftime", "mktime", "and", "or", "xor", "compl", "lshift",
    "rshift", "typeof", "isarray", "patsplit",
];

/// Keywords after which a `/` begins a regular expression rather than division.
/// (After a plain identifier or built-in name, `/` is division — `length / 2`.)
const REGEX_PRECEDING_KEYWORDS: &[&str] = &[
    "print", "printf", "return", "case", "do", "else", "in", "delete", "while", "if", "for",
    "exit", "next", "nextfile", "getline",
];

pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.contains(&text)
}

pub fn is_builtin(text: &str) -> bool {
    BUILTINS.contains(&text)
}

pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const NEWLINE: &str = "newline";
    pub const COMMENT: &str = "comment";
    pub const LINE_CONTINUATION: &str = "line_continuation";
    pub const IDENT: &str = "ident";
    pub const NUMBER: &str = "number";
    pub const STRING: &str = "string_literal";
    pub const REGEX: &str = "regex_literal";
    pub const OPERATOR: &str = "operator";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest / prefix-safe first so the scanner is
/// greedy-correct (`**=` before `**`, `<=` etc.). `/` is handled separately in
/// [`Lexer::slash`] (regex vs. division), so `/=` is not in this table.
const OPERATORS: &[&str] = &[
    "**=", "+=", "-=", "*=", "%=", "^=", "==", "!=", "<=", ">=", "&&", "||", "++", "--", "!~",
    ">>", "**",
];

/// Characters that begin an operator (single or multi). `/` is deliberately
/// excluded — it is dispatched to [`Lexer::slash`] before operators.
fn is_op_start(c: char) -> bool {
    matches!(
        c,
        '+' | '-'
            | '*'
            | '%'
            | '^'
            | '='
            | '<'
            | '>'
            | '!'
            | '~'
            | '?'
            | ':'
            | ';'
            | ','
            | '('
            | ')'
            | '{'
            | '}'
            | '['
            | ']'
            | '$'
            | '|'
            | '&'
    )
}

fn is_ident_start(c: char) -> bool {
    c == '_' || c.is_ascii_alphabetic()
}

fn is_ident_continue(c: char) -> bool {
    c == '_' || c.is_ascii_alphanumeric()
}

pub fn lex(source: &str) -> Vec<Token> {
    Lexer::new(source).run()
}

struct Lexer<'s> {
    src: &'s str,
    bytes: &'s [u8],
    pos: usize,
    tokens: Vec<Token>,
    /// Last emitted non-trivia token (kind + span), used by the regex/division
    /// heuristic. `NEWLINE` counts (it puts us back in expression position).
    prev_sig: Option<(&'static str, ByteSpan)>,
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
        while self.pos < self.bytes.len() {
            // Progress guard: every branch below advances `pos`, and this assert
            // documents the invariant the whole lossless contract rests on.
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
                ' ' | '\t' | '\x0c' | '\x0b' => {
                    self.eat_while(|c| matches!(c, ' ' | '\t' | '\x0c' | '\x0b'));
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                '\\' => self.backslash(start),
                '#' => {
                    let end = self.find_line_end(start);
                    self.pos = end;
                    self.push(kind::COMMENT, start, end, true);
                }
                '"' => {
                    let ok = self.scan_string();
                    self.push(string_kind(ok), start, self.pos, false);
                }
                '/' => self.slash(start),
                c if c.is_ascii_digit() => self.number(start),
                '.' if self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) => {
                    self.number(start)
                }
                c if is_ident_start(c) => {
                    self.eat_while(is_ident_continue);
                    self.push(kind::IDENT, start, self.pos, false);
                }
                c if is_op_start(c) => {
                    if !self.operator(start) {
                        self.bump();
                        self.push(kind::OPERATOR, start, self.pos, false);
                    }
                }
                _ => {
                    // Unclassifiable byte (e.g. a stray `.` or a non-ASCII byte):
                    // a single covered `error` token, never dropped.
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }
            debug_assert!(self.pos > start, "lexer made no progress");
        }
        self.tokens
    }

    // --- numbers ------------------------------------------------------------

    fn number(&mut self, start: usize) {
        // Hexadecimal `0x…` (gawk).
        if self.peek() == '0' && matches!(self.peek_at(1), Some('x') | Some('X')) {
            self.bump();
            self.bump();
            self.eat_while(|c| c.is_ascii_hexdigit());
            self.push(kind::NUMBER, start, self.pos, false);
            return;
        }
        self.eat_while(|c| c.is_ascii_digit());
        if self.peek() == '.' {
            self.bump();
            self.eat_while(|c| c.is_ascii_digit());
        }
        // Optional exponent, only if it is actually well-formed (`1e10`, `1e+10`).
        if matches!(self.peek(), 'e' | 'E') {
            let save = self.pos;
            self.bump();
            if matches!(self.peek(), '+' | '-') {
                self.bump();
            }
            if self.peek().is_ascii_digit() {
                self.eat_while(|c| c.is_ascii_digit());
            } else {
                self.pos = save; // not an exponent after all — backtrack
            }
        }
        self.push(kind::NUMBER, start, self.pos, false);
    }

    // --- strings ------------------------------------------------------------

    /// Double-quoted string with backslash escapes (an escaped newline continues
    /// the string). An unescaped newline (or EOF) ends an unterminated string.
    /// Returns whether it terminated.
    fn scan_string(&mut self) -> bool {
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
            if c == '"' {
                self.bump();
                return true;
            }
            if c == '\n' {
                return false; // strings do not span raw newlines
            }
            self.bump();
        }
        false
    }

    // --- slash: comment? no — regex vs division -----------------------------

    fn slash(&mut self, start: usize) {
        if self.regex_allowed() {
            self.regex(start);
        } else {
            // Division operator: `/=` or `/`.
            if self.src[self.pos..].starts_with("/=") {
                self.pos += 2;
            } else {
                self.bump();
            }
            self.push(kind::OPERATOR, start, self.pos, false);
        }
    }

    /// Scan a `/body/` regex literal. A char class `[ … ]` shelters an inner `/`.
    /// A line terminator before the closing `/` makes it an `error` token over the
    /// bytes consumed (never dropped).
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
            if c == '\n' || c == '\r' {
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
        let token_kind = if terminated { kind::REGEX } else { kind::ERROR };
        self.push(token_kind, start, self.pos, false);
    }

    /// Heuristic: may a `/` at the cursor begin a regular expression? Decided from
    /// the previous significant token. Losslessness never depends on the answer.
    fn regex_allowed(&self) -> bool {
        let (k, span) = match self.prev_sig {
            None => return true, // start of input → expression position
            Some(p) => p,
        };
        if k == kind::IDENT {
            // After a control keyword (`print /re/`) a regex is allowed; after a
            // plain variable or built-in name (`x / 2`) it is division.
            return REGEX_PRECEDING_KEYWORDS.contains(&span.text(self.src));
        }
        if k == kind::OPERATOR {
            let t = span.text(self.src);
            // After a value-closing operator, `/` is division.
            return t != ")" && t != "]" && t != "++" && t != "--";
        }
        // A number / string / regex closes a value → division follows.
        !matches!(k, kind::NUMBER | kind::STRING | kind::REGEX)
    }

    // --- escapes / operators ------------------------------------------------

    fn backslash(&mut self, start: usize) {
        self.bump(); // the backslash
        match self.peek_opt() {
            Some('\n') => {
                self.bump();
                self.push(kind::LINE_CONTINUATION, start, self.pos, true);
            }
            Some('\r') => {
                self.bump();
                if self.peek() == '\n' {
                    self.bump();
                }
                self.push(kind::LINE_CONTINUATION, start, self.pos, true);
            }
            _ => {
                // A lone backslash outside a string is not valid AWK; keep it as a
                // single covered `error` token (the next char lexes normally).
                self.push(kind::ERROR, start, self.pos, false);
            }
        }
    }

    /// Try to consume a multi-character operator at `start`. Returns true on match.
    fn operator(&mut self, start: usize) -> bool {
        for op in OPERATORS {
            if self.src[self.pos..].starts_with(op) {
                self.pos += op.len();
                self.push(kind::OPERATOR, start, self.pos, false);
                return true;
            }
        }
        false
    }

    // --- primitives ---------------------------------------------------------

    fn peek(&self) -> char {
        self.src[self.pos..].chars().next().unwrap_or('\0')
    }

    fn peek_opt(&self) -> Option<char> {
        self.src[self.pos..].chars().next()
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

    fn push(&mut self, k: &'static str, start: usize, end: usize, trivia: bool) {
        let span = ByteSpan::new(start, end);
        if !trivia {
            self.prev_sig = Some((k, span));
        }
        self.tokens.push(Token {
            kind: k,
            span,
            trivia,
        });
    }
}

fn string_kind(terminated: bool) -> &'static str {
    if terminated {
        kind::STRING
    } else {
        kind::ERROR
    }
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
            "BEGIN { print \"hi\" }\n",
            "/foo/ { count++ }\n",
            "$1 ~ /^[0-9]+$/ { sum += $1 }\n",
            "function add(a, b) { return a + b }\n",
            "x = a / b   # division, not regex\n",
            "{ print length($0) / 2 }\n",
            "# just a comment\n",
            "printf(\"%d\\n\", n)\n",
            "y = 3.14e-2 + 0xff\n",
            "",
            "\n\n   \n# blanks\n",
            "λ\n", // non-ASCII byte → error token, still covered
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
            let rebuilt: String = lex(src).iter().map(|t| t.span.text(src)).collect();
            assert_eq!(rebuilt, src, "not lossless: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("print x\n");
        assert!(t.contains(&(kind::IDENT, "print".to_string())));
        assert!(t.contains(&(kind::IDENT, "x".to_string())));
        assert!(t.iter().any(|(k, _)| *k == kind::NEWLINE));
        assert!(is_keyword("function"));
        assert!(is_keyword("BEGIN"));
        assert!(is_builtin("length"));
        assert!(!is_keyword("length"));
        assert!(!is_builtin("foo"));
    }

    #[test]
    fn regex_vs_division() {
        // After `~` a `/` starts a regex; after an identifier it is division.
        let t = texts("$1 ~ /ab/\n");
        assert!(t.iter().any(|(k, s)| *k == kind::REGEX && s == "/ab/"));
        let d = texts("a / b\n");
        assert!(d.iter().any(|(k, s)| *k == kind::OPERATOR && s == "/"));
        assert!(!d.iter().any(|(k, _)| *k == kind::REGEX));
    }

    #[test]
    fn regex_char_class_shelters_slash() {
        let t = texts("x = /[/]/\n");
        // `/=` is *not* mis-lexed here because `=` puts us in regex position; and
        // the `[ … ]` class shelters the inner `/`.
        assert!(t.iter().any(|(k, s)| *k == kind::REGEX && s == "/[/]/"));
    }

    #[test]
    fn unterminated_string_is_error_not_dropped() {
        let src = "x = \"oops\n";
        let t = texts(src);
        assert!(t.iter().any(|(k, _)| *k == kind::ERROR));
        let rebuilt: String = lex(src).iter().map(|t| t.span.text(src)).collect();
        assert_eq!(rebuilt, src);
    }

    #[test]
    fn operators_are_greedy() {
        let t = texts("a += b !~ c >> d\n");
        assert!(t.contains(&(kind::OPERATOR, "+=".to_string())));
        assert!(t.contains(&(kind::OPERATOR, "!~".to_string())));
        assert!(t.contains(&(kind::OPERATOR, ">>".to_string())));
    }
}
