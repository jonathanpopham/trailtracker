//! Lossless Tcl/Tk lexer, grounded in the Tcl "dodekalogue" (the twelve rules of
//! `Tcl(n)`): everything is a command; a command is words separated by whitespace;
//! `{ }` brace words are literal and deferred; `[ ]` is command substitution;
//! `" "` is a quoted word with substitution; `$name`/`${name}` is variable
//! substitution; `\` escapes; `;` and newline separate commands; and `#` is a
//! comment **only at the start of a command**.
//!
//! Guarantees (identical contract to the Rust, Python, and Bash lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs, comments, backslash-newline continuations) are emitted
//!   as `trivia` tokens, never discarded. `newline` and `;` are emitted as
//!   *non-trivia* tokens because they are structurally significant in Tcl (they
//!   terminate a command).
//! - Anything the lexer cannot classify, or any unterminated quoting form, becomes
//!   an `error` token over the exact bytes (running to end-of-file if needed).
//!   Input is never silently dropped.
//! - The main loop advances `pos` on every iteration; a defensive progress guard
//!   forces a one-byte `error` token in the impossible case that a branch did not.
//!
//! Tcl is word-oriented and substitution-rich. The lexer recognizes every quoting
//! and substitution form as a single covering token: `{ … }` brace words (balanced,
//! honoring `\{` `\}` escapes), `[ … ]` command substitution (balanced), `" … "`
//! quoted strings, and `$`-substitutions (`$name`, `${name}`, `$arr(idx)`, `$1`).
//! The brace/bracket scanners balance nesting iteratively (no recursion), so even
//! pathologically deep `{{{…}}}` input cannot overflow the stack here.
//!
//! Honest coverage notes:
//! - The `#`-comment rule keys off whether the lexer is at a *command start*
//!   (beginning of input, or just after a `newline`/`;`); whitespace, line
//!   continuations, and comments preserve that state, while any real word clears
//!   it — exactly as Tcl treats a mid-command `#` as an ordinary character.
//! - `{` `}` `[` `]` `"` are treated as word breaks even mid-word; in Tcl they are
//!   only *special* at a word boundary, so a literal `a{b}` is mildly
//!   over-segmented into adjacent tokens. This never affects losslessness (every
//!   byte is still covered) — the parser re-groups adjacent tokens into words.
//! - `[ … ]` balancing counts bracket depth honoring backslashes but does not
//!   track braces/quotes *inside* the substitution, the same pragmatic
//!   simplification the Bash lexer makes for `$( … )`.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Tcl reserved/control words. Like the other lexers these lex as `word` tokens;
/// the parser and lowering distinguish them via [`is_keyword`]. Builtins that are
/// not control words (`puts`, `expr`, `incr`, …) are intentionally absent: an
/// invocation of one is an honest external `CALLS`, not a keyword.
pub const KEYWORDS: &[&str] = &[
    "if",
    "then",
    "else",
    "elseif",
    "while",
    "for",
    "foreach",
    "switch",
    "break",
    "continue",
    "return",
    "catch",
    "try",
    "finally",
    "error",
    "throw",
    "eval",
    "uplevel",
    "upvar",
    "default",
    "proc",
    "namespace",
    "package",
    "source",
    "set",
    "variable",
    "global",
];

pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.contains(&text)
}

pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const NEWLINE: &str = "newline";
    pub const COMMENT: &str = "comment";
    pub const LINE_CONTINUATION: &str = "line_continuation";
    pub const WORD: &str = "word";
    pub const NUMBER: &str = "number";
    pub const STRING: &str = "string_literal";
    pub const BRACE_WORD: &str = "brace_word";
    pub const BRACKET_WORD: &str = "bracket_word";
    pub const VARIABLE: &str = "variable";
    pub const SEMICOLON: &str = "semicolon";
    /// Synthesized by the *parser* when it expands a brace body into a nested
    /// script; never emitted by the lexer itself, but declared here so the parser
    /// and lowering share one vocabulary.
    pub const BRACE_OPEN: &str = "brace_open";
    pub const BRACE_CLOSE: &str = "brace_close";
    pub const ERROR: &str = "error";
}

/// A word character: anything that does not begin whitespace, a separator, a
/// quoting/substitution form, or an escape. `#` and `(` `)` are word characters
/// (a `#` only begins a comment at a command start — see [`Lexer::run`]).
fn is_word_char(c: char) -> bool {
    if c.is_whitespace() {
        return false;
    }
    !matches!(c, ';' | '{' | '}' | '[' | ']' | '"' | '$' | '\\')
}

fn is_ident_start(c: char) -> bool {
    c == '_' || c.is_alphabetic()
}

fn is_ident_continue(c: char) -> bool {
    c == '_' || c.is_alphanumeric()
}

pub fn lex(source: &str) -> Vec<Token> {
    Lexer::new(source).run()
}

struct Lexer<'s> {
    src: &'s str,
    bytes: &'s [u8],
    pos: usize,
    tokens: Vec<Token>,
    /// True when the cursor sits where a command word could begin (start of input,
    /// or just after a `newline`/`;`). Only then does a `#` begin a comment.
    at_cmd_start: bool,
}

impl<'s> Lexer<'s> {
    fn new(src: &'s str) -> Self {
        Lexer {
            src,
            bytes: src.as_bytes(),
            pos: 0,
            tokens: Vec::new(),
            at_cmd_start: true,
        }
    }

    fn run(mut self) -> Vec<Token> {
        while self.pos < self.bytes.len() {
            let start = self.pos;
            let c = self.peek();
            match c {
                '\n' => {
                    self.bump();
                    self.push(kind::NEWLINE, start, self.pos, false);
                    self.at_cmd_start = true;
                }
                '\r' => {
                    self.bump();
                    if self.peek() == '\n' {
                        self.bump();
                    }
                    self.push(kind::NEWLINE, start, self.pos, false);
                    self.at_cmd_start = true;
                }
                ' ' | '\t' | '\x0c' | '\x0b' => {
                    self.eat_while(|c| c == ' ' || c == '\t' || c == '\x0c' || c == '\x0b');
                    self.push(kind::WHITESPACE, start, self.pos, true);
                    // whitespace preserves command-start state
                }
                ';' => {
                    self.bump();
                    self.push(kind::SEMICOLON, start, self.pos, false);
                    self.at_cmd_start = true;
                }
                '\\' => self.backslash(start),
                '#' if self.at_cmd_start => {
                    let end = self.find_line_end(start);
                    self.pos = end;
                    self.push(kind::COMMENT, start, end, true);
                    // a comment runs to (but not including) the newline; the
                    // newline that follows keeps us at a command start
                }
                '"' => {
                    let ok = self.scan_double();
                    self.push(string_kind(ok), start, self.pos, false);
                    self.at_cmd_start = false;
                }
                '{' => {
                    let ok = self.scan_brace();
                    let k = if ok { kind::BRACE_WORD } else { kind::ERROR };
                    self.push(k, start, self.pos, false);
                    self.at_cmd_start = false;
                }
                '[' => {
                    let ok = self.scan_bracket();
                    let k = if ok { kind::BRACKET_WORD } else { kind::ERROR };
                    self.push(k, start, self.pos, false);
                    self.at_cmd_start = false;
                }
                '}' | ']' => {
                    // A stray closer outside any group: keep it as a covered word
                    // character so the stream stays lossless.
                    self.bump();
                    self.push(kind::WORD, start, self.pos, false);
                    self.at_cmd_start = false;
                }
                '$' => {
                    self.dollar(start);
                    self.at_cmd_start = false;
                }
                c if c.is_ascii_digit() => {
                    self.number(start);
                    self.at_cmd_start = false;
                }
                c if is_word_char(c) => {
                    self.word(start);
                    self.at_cmd_start = false;
                }
                _ => {
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                    self.at_cmd_start = false;
                }
            }
            // Defensive progress guard: every arm above advances `pos`, but if one
            // ever failed to, force a one-byte error token so the loop can never
            // spin and no byte is dropped.
            if self.pos == start {
                self.bump();
                self.push(kind::ERROR, start, self.pos, false);
                self.at_cmd_start = false;
            }
        }
        self.tokens
    }

    // --- words / numbers ----------------------------------------------------

    fn word(&mut self, start: usize) {
        self.eat_while(is_word_char);
        self.push(kind::WORD, start, self.pos, false);
    }

    fn number(&mut self, start: usize) {
        self.eat_while(|c| c.is_ascii_digit());
        // A digit run that runs straight into word characters (`2x`, `3.14`) is a
        // single Tcl word, not a number.
        if is_word_char(self.peek()) {
            self.eat_while(is_word_char);
            self.push(kind::WORD, start, self.pos, false);
        } else {
            self.push(kind::NUMBER, start, self.pos, false);
        }
    }

    // --- escapes ------------------------------------------------------------

    fn backslash(&mut self, start: usize) {
        self.bump(); // the backslash
        match self.peek_opt() {
            Some('\n') => {
                self.bump();
                self.push(kind::LINE_CONTINUATION, start, self.pos, true);
                // backslash-newline is whitespace in Tcl; command-start preserved
            }
            Some('\r') => {
                self.bump();
                if self.peek() == '\n' {
                    self.bump();
                }
                self.push(kind::LINE_CONTINUATION, start, self.pos, true);
            }
            Some(_) => {
                self.bump(); // the escaped character is part of a word
                self.push(kind::WORD, start, self.pos, false);
                self.at_cmd_start = false;
            }
            None => {
                // A lone trailing backslash: keep it as a covered word token.
                self.push(kind::WORD, start, self.pos, false);
                self.at_cmd_start = false;
            }
        }
    }

    // --- strings / brace / bracket words ------------------------------------

    /// Double-quoted `"…"` with backslash escapes; spans newlines. Returns whether
    /// it terminated. Embedded `$…`/`[…]` are left inside the string token —
    /// losslessly covered, resolved later if ever needed.
    fn scan_double(&mut self) -> bool {
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
            self.bump();
        }
        false
    }

    /// Brace word `{ … }`: balanced, deferred/literal, honoring `\{` `\}` `\\`
    /// escapes. The cursor sits on the opening `{`. Returns whether it balanced;
    /// an unbalanced run reaches end-of-file (caller marks it `error`).
    fn scan_brace(&mut self) -> bool {
        self.balanced('{', '}')
    }

    /// Command substitution `[ … ]`: balanced bracket run honoring backslashes.
    fn scan_bracket(&mut self) -> bool {
        self.balanced('[', ']')
    }

    /// Consume a balanced `open`/`close` run from the opening delimiter, honoring
    /// backslash escapes. Returns true if it balanced before end-of-file.
    fn balanced(&mut self, open: char, close: char) -> bool {
        let mut depth: i32 = 0;
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '\\' {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
                continue;
            }
            if c == open {
                depth += 1;
                self.bump();
                continue;
            }
            if c == close {
                depth -= 1;
                self.bump();
                if depth == 0 {
                    return true;
                }
                continue;
            }
            self.bump();
        }
        false
    }

    // --- variable substitution ----------------------------------------------

    fn dollar(&mut self, start: usize) {
        self.bump(); // the `$`
        match self.peek_opt() {
            Some('{') => {
                // `${name}` — runs to the first `}` (no nesting/escapes in Tcl).
                self.bump();
                while self.pos < self.bytes.len() && self.peek() != '}' {
                    self.bump();
                }
                if self.peek() == '}' {
                    self.bump();
                }
                self.push(kind::VARIABLE, start, self.pos, false);
            }
            Some(c) if is_ident_start(c) => {
                self.var_name();
                if self.peek() == '(' {
                    self.balanced('(', ')'); // `$arr(index)`
                }
                self.push(kind::VARIABLE, start, self.pos, false);
            }
            Some(c) if c.is_ascii_digit() => {
                self.bump(); // positional `$1`
                self.push(kind::VARIABLE, start, self.pos, false);
            }
            _ => {
                // A bare `$` (literal dollar, end of input, before whitespace).
                self.push(kind::VARIABLE, start, self.pos, false);
            }
        }
    }

    /// Consume a variable name body: ident characters plus `::` namespace
    /// separators (`$ns::var`).
    fn var_name(&mut self) {
        loop {
            let c = self.peek();
            if is_ident_continue(c) {
                self.bump();
            } else if self.src[self.pos..].starts_with("::") {
                self.pos += 2;
            } else {
                break;
            }
        }
    }

    // --- primitives ---------------------------------------------------------

    fn peek(&self) -> char {
        self.src[self.pos..].chars().next().unwrap_or('\0')
    }

    fn peek_opt(&self) -> Option<char> {
        self.src[self.pos..].chars().next()
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
        self.tokens.push(Token {
            kind: k,
            span: ByteSpan::new(start, end),
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
            "# a comment\nputs hello\n",
            "proc greet {name} {\n  puts \"hi $name\"\n}\n",
            "set x [expr {1 + 2}]\n",
            "namespace eval ::app {\n  variable v 1\n}\n",
            "puts \"interp $x and [cmd a]\"\n",
            "set L {a b c}\n",
            "if {$x > 0} then {puts yes} else {puts no}\n",
            "package require Tk 8.6\n",
            "foreach {k v} $d { puts $k }\n",
            "λ {set ☃ €}  # unicode\n",
            "puts foo#bar  ;# trailing comment after code\n",
            "",
            "\n\n   \n# only blanks\n",
            "set s \"unterminated\n",
            "proc broken {unbalanced\n",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
            let rebuilt: String = lex(src).iter().map(|t| t.span.text(src)).collect();
            assert_eq!(rebuilt, src, "not lossless: {src:?}");
        }
    }

    #[test]
    fn comment_only_at_command_start() {
        // `#` at the start of a command is a comment; mid-command it is ordinary.
        let t = texts("puts foo#bar\n# real\n");
        assert!(t.contains(&(kind::WORD, "foo#bar".to_string())));
        assert!(t.iter().any(|(k, s)| *k == kind::COMMENT && s == "# real"));
    }

    #[test]
    fn semicolon_resets_command_start() {
        // After `;` a `#` is again a comment.
        let t = texts("puts a ;# note\n");
        assert!(t.iter().any(|(k, s)| *k == kind::COMMENT && s == "# note"));
        assert!(t.iter().any(|(k, _)| *k == kind::SEMICOLON));
    }

    #[test]
    fn brace_and_bracket_words_are_single_tokens() {
        let t = texts("set x {a {b c} d}\n");
        assert!(t.contains(&(kind::BRACE_WORD, "{a {b c} d}".to_string())));
        let t2 = texts("set y [a [b] c]\n");
        assert!(t2.contains(&(kind::BRACKET_WORD, "[a [b] c]".to_string())));
    }

    #[test]
    fn variables_are_single_tokens() {
        let t = texts("$x ${y z} $arr(i) $1 $ns::v\n");
        for lit in ["$x", "${y z}", "$arr(i)", "$1", "$ns::v"] {
            assert!(
                t.iter().any(|(k, s)| *k == kind::VARIABLE && s == lit),
                "variable not recognized: {lit}"
            );
        }
    }

    #[test]
    fn keywords_recognized() {
        assert!(is_keyword("proc"));
        assert!(is_keyword("namespace"));
        assert!(!is_keyword("puts"));
    }

    #[test]
    fn unterminated_brace_is_error_not_dropped() {
        let src = "proc f {body\n";
        let t = texts(src);
        assert!(t.iter().any(|(k, _)| *k == kind::ERROR));
        let rebuilt: String = lex(src).iter().map(|t| t.span.text(src)).collect();
        assert_eq!(rebuilt, src);
    }
}
