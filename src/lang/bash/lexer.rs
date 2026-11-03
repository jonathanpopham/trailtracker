//! Lossless Bash/Shell lexer, grounded in the POSIX-shell + Bash token grammar.
//!
//! Guarantees (identical contract to the Rust and Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs, comments, backslash-newline line continuations) are
//!   emitted as `trivia` tokens, never discarded. `NEWLINE` is emitted as a
//!   *non-trivia* token because it is structurally significant in shell (it
//!   terminates a command, like `;`).
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes (an unterminated string runs to end-of-file as one `error` token).
//!   Input is never silently dropped.
//!
//! Shell is word-oriented and quote-rich. The lexer recognizes every quoting and
//! expansion form as a single covering token: single `'…'`, double `"…"`,
//! ANSI-C `$'…'`, locale `$"…"`, backquote `` `…` ``, and `$`-expansions
//! (`$name`, `${…}`, `$(…)`, `$((…))`, `$1`, `$?`, …). Here-documents are handled
//! specially: when a `<<`/`<<-` redirect names a delimiter, the body that begins
//! on the next physical line is consumed up to the terminator line as
//! `heredoc_body` + `heredoc_end` tokens, so multi-line here-doc payloads stay
//! losslessly in the stream without being mis-lexed as code.
//!
//! Coverage note (honest): identifier start/continue for `$name` uses
//! `char::is_alphabetic` / `is_alphanumeric` plus `_` as a pragmatic stand-in for
//! the full POSIX name table — anything outside still lands in the tree as a
//! covered token, never dropped. The `#`-comment rule keys off whether the
//! previous token was word-like (a `#` mid-word is an ordinary character, exactly
//! as Bash treats it).

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Bash reserved words. Like the other lexers these lex as `word` tokens; the
/// parser and lowering distinguish them via [`is_keyword`].
pub const KEYWORDS: &[&str] = &[
    "if", "then", "elif", "else", "fi", "time", "for", "in", "until", "while", "do", "done",
    "case", "esac", "coproc", "select", "function", "{", "}", "[[", "]]", "!",
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
    pub const EXPANSION: &str = "expansion";
    pub const OPERATOR: &str = "operator";
    pub const HEREDOC_DELIM: &str = "heredoc_delim";
    pub const HEREDOC_BODY: &str = "heredoc_body";
    pub const HEREDOC_END: &str = "heredoc_end";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest / prefix-safe first so the scanner is
/// greedy-correct (`<<<` before `<<-` before `<<`, `&>>` before `&>`, …).
const OPERATORS: &[&str] = &[
    ";;&", "&>>", "<<<", "<<-", ";;", ";&", "&&", "||", "|&", "&>", "<<", ">>", ">&", "<&", "<>",
    ">|", "==", "=~",
];

/// Characters that begin an operator (single or multi). Everything else that is
/// not whitespace / a quote / `$` / `\` is a word character.
fn is_op_start(c: char) -> bool {
    matches!(c, ';' | '&' | '|' | '<' | '>' | '=' | '(' | ')')
}

/// A word character: anything that does not start whitespace, a quote, an
/// expansion, an escape, or an operator. `#` is a word character (it only starts
/// a comment at a word boundary — see the dispatch in [`Lexer::run`]).
fn is_word_char(c: char) -> bool {
    if c.is_whitespace() {
        return false;
    }
    !matches!(
        c,
        '|' | '&' | ';' | '(' | ')' | '<' | '>' | '=' | '$' | '\'' | '"' | '`' | '\\'
    )
}

fn is_ident_start(c: char) -> bool {
    c == '_' || c.is_alphabetic()
}

fn is_ident_continue(c: char) -> bool {
    c == '_' || c.is_alphanumeric()
}

/// A character allowed inside a here-doc delimiter word (stops at whitespace and
/// shell metacharacters).
fn is_delim_char(c: char) -> bool {
    !c.is_whitespace() && !matches!(c, '|' | '&' | ';' | '(' | ')' | '<' | '>')
}

pub fn lex(source: &str) -> Vec<Token> {
    Lexer::new(source).run()
}

/// A here-document awaiting its body once the current physical line ends.
struct Pending {
    delim: String,
    strip_tabs: bool,
}

struct Lexer<'s> {
    src: &'s str,
    bytes: &'s [u8],
    pos: usize,
    tokens: Vec<Token>,
    /// Whether the previous emitted token was "word-like" (a word, number,
    /// string, or expansion). A `#` only begins a comment when it is *not*
    /// preceded by a word-like token — i.e. at a word boundary.
    prev_word_like: bool,
    /// Here-docs queued by `<<`/`<<-` on the current line, drained (in FIFO
    /// order) the moment a newline is emitted.
    pending: Vec<Pending>,
}

impl<'s> Lexer<'s> {
    fn new(src: &'s str) -> Self {
        Lexer {
            src,
            bytes: src.as_bytes(),
            pos: 0,
            tokens: Vec::new(),
            prev_word_like: false,
            pending: Vec::new(),
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
                ' ' | '\t' | '\x0c' => {
                    self.eat_while(|c| c == ' ' || c == '\t' || c == '\x0c');
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                '\\' => self.backslash(start),
                '#' if !self.prev_word_like => {
                    let end = self.find_line_end(start);
                    self.pos = end;
                    self.push(kind::COMMENT, start, end, true);
                }
                '\'' => {
                    let ok = self.scan_single(false);
                    self.push(string_kind(ok), start, self.pos, false);
                }
                '"' => {
                    let ok = self.scan_double();
                    self.push(string_kind(ok), start, self.pos, false);
                }
                '`' => {
                    let ok = self.scan_backtick();
                    let k = if ok { kind::EXPANSION } else { kind::ERROR };
                    self.push(k, start, self.pos, false);
                }
                '$' => self.dollar(start),
                c if c.is_ascii_digit() => self.number(start),
                c if is_op_start(c) => {
                    if !self.operator(start) {
                        self.bump();
                        self.push(kind::OPERATOR, start, self.pos, false);
                    }
                }
                c if is_word_char(c) => self.word(start),
                _ => {
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
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
        // single shell word, not a number.
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
            }
            None => {
                // A lone trailing backslash: keep it as a covered word token.
                self.push(kind::WORD, start, self.pos, false);
            }
        }
    }

    // --- strings ------------------------------------------------------------

    /// Single-quoted `'…'`. With `ansi_c`, backslash escapes are honored (`$'…'`);
    /// otherwise the body is fully literal. Returns whether it terminated.
    fn scan_single(&mut self, ansi_c: bool) -> bool {
        self.bump(); // opening quote
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if ansi_c && c == '\\' {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
                continue;
            }
            if c == '\'' {
                self.bump();
                return true;
            }
            self.bump();
        }
        false
    }

    /// Double-quoted `"…"` with backslash escapes; spans newlines. Returns
    /// whether it terminated. (Embedded `$…`/`` `…` `` are left inside the string
    /// token — losslessly covered, resolved later if ever needed.)
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

    /// Backquote command substitution `` `…` `` with backslash escapes.
    fn scan_backtick(&mut self) -> bool {
        self.bump(); // opening backquote
        while self.pos < self.bytes.len() {
            let c = self.peek();
            if c == '\\' {
                self.bump();
                if self.pos < self.bytes.len() {
                    self.bump();
                }
                continue;
            }
            if c == '`' {
                self.bump();
                return true;
            }
            self.bump();
        }
        false
    }

    // --- dollar expansions --------------------------------------------------

    fn dollar(&mut self, start: usize) {
        self.bump(); // the `$`
        match self.peek_opt() {
            Some('\'') => {
                let ok = self.scan_single(true); // ANSI-C quoting
                self.push(string_kind(ok), start, self.pos, false);
            }
            Some('"') => {
                let ok = self.scan_double(); // locale-translated string
                self.push(string_kind(ok), start, self.pos, false);
            }
            Some('(') => {
                // `$(…)` command substitution and `$((…))` arithmetic both balance
                // as nested parentheses.
                self.balanced('(', ')');
                self.push(kind::EXPANSION, start, self.pos, false);
            }
            Some('{') => {
                self.balanced('{', '}');
                self.push(kind::EXPANSION, start, self.pos, false);
            }
            Some(c) if is_ident_start(c) => {
                self.eat_while(is_ident_continue);
                self.push(kind::EXPANSION, start, self.pos, false);
            }
            Some(c) if c.is_ascii_digit() => {
                // Positional parameter: `$1` (`$12` is `$1` then `2`).
                self.bump();
                self.push(kind::EXPANSION, start, self.pos, false);
            }
            Some(c) if "#?$!@*-_".contains(c) => {
                // Special parameters: `$#`, `$?`, `$$`, `$!`, `$@`, `$*`, `$-`, `$_`.
                self.bump();
                self.push(kind::EXPANSION, start, self.pos, false);
            }
            _ => {
                // A bare `$` (e.g. end of input or before whitespace).
                self.push(kind::EXPANSION, start, self.pos, false);
            }
        }
    }

    /// Consume a balanced run delimited by `open`/`close`, honoring backslash
    /// escapes. The cursor must sit on the opening delimiter. Runs to end-of-file
    /// if never balanced (still losslessly covered).
    fn balanced(&mut self, open: char, close: char) {
        let mut depth = 0i32;
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
                if depth <= 0 {
                    break;
                }
                continue;
            }
            self.bump();
        }
    }

    // --- operators + here-doc introduction ----------------------------------

    /// Try to consume a multi-character operator at `start`. Returns true if one
    /// matched. `<<` / `<<-` additionally scan the here-doc delimiter and queue
    /// the body for consumption at the next newline.
    fn operator(&mut self, start: usize) -> bool {
        for op in OPERATORS {
            if self.src[self.pos..].starts_with(op) {
                self.pos += op.len();
                self.push(kind::OPERATOR, start, self.pos, false);
                if *op == "<<" || *op == "<<-" {
                    self.scan_heredoc_delim(*op == "<<-");
                }
                return true;
            }
        }
        false
    }

    /// After a `<<`/`<<-` operator, read the (optionally quoted) delimiter word and
    /// queue a [`Pending`] here-doc. Emits the inter-token whitespace as trivia and
    /// the delimiter as a `heredoc_delim` (or `string_literal`) token.
    fn scan_heredoc_delim(&mut self, strip_tabs: bool) {
        // Optional spaces/tabs before the delimiter.
        let ws_start = self.pos;
        self.eat_while(|c| c == ' ' || c == '\t');
        if self.pos > ws_start {
            self.push(kind::WHITESPACE, ws_start, self.pos, true);
        }
        let dstart = self.pos;
        let mut lit = String::new();
        let mut quoted = false;
        match self.peek_opt() {
            Some('\'') => {
                quoted = true;
                self.bump();
                while self.pos < self.bytes.len() && self.peek() != '\'' {
                    lit.push(self.peek());
                    self.bump();
                }
                if self.peek() == '\'' {
                    self.bump();
                }
            }
            Some('"') => {
                quoted = true;
                self.bump();
                while self.pos < self.bytes.len() && self.peek() != '"' {
                    lit.push(self.peek());
                    self.bump();
                }
                if self.peek() == '"' {
                    self.bump();
                }
            }
            Some(_) => {
                while self.pos < self.bytes.len() {
                    let c = self.peek();
                    if c == '\\' {
                        self.bump();
                        if self.pos < self.bytes.len() {
                            lit.push(self.peek());
                            self.bump();
                        }
                    } else if is_delim_char(c) {
                        lit.push(c);
                        self.bump();
                    } else {
                        break;
                    }
                }
            }
            None => {}
        }
        if self.pos == dstart {
            return; // no delimiter present (e.g. `<<` at end of line)
        }
        let token_kind = if quoted {
            kind::STRING
        } else {
            kind::HEREDOC_DELIM
        };
        self.push(token_kind, dstart, self.pos, false);
        if !lit.is_empty() {
            self.pending.push(Pending {
                delim: lit,
                strip_tabs,
            });
        }
    }

    /// At each newline, consume any queued here-doc bodies in order.
    fn drain_heredocs(&mut self) {
        if self.pending.is_empty() {
            return;
        }
        let pend = std::mem::take(&mut self.pending);
        for p in pend {
            self.consume_one_heredoc(&p.delim, p.strip_tabs);
        }
    }

    /// Consume one here-doc body: every line up to (but not including) the
    /// terminator line becomes a single `heredoc_body` token; the terminator line
    /// (with its newline) becomes a `heredoc_end` token. With `strip_tabs`
    /// (`<<-`), leading tabs are ignored when matching the terminator. If no
    /// terminator is found, the body covers the remainder of the file.
    fn consume_one_heredoc(&mut self, delim: &str, strip_tabs: bool) {
        let body_start = self.pos;
        let mut scan = self.pos;
        loop {
            if scan >= self.bytes.len() {
                if self.bytes.len() > body_start {
                    self.push(kind::HEREDOC_BODY, body_start, self.bytes.len(), false);
                }
                self.pos = self.bytes.len();
                return;
            }
            let line_start = scan;
            let nl = self.src[line_start..].find('\n').map(|i| line_start + i);
            let content_end = nl.unwrap_or(self.bytes.len());
            let after = nl.map(|i| i + 1).unwrap_or(self.bytes.len());
            let mut content = &self.src[line_start..content_end];
            content = content.strip_suffix('\r').unwrap_or(content);
            let candidate = if strip_tabs {
                content.trim_start_matches('\t')
            } else {
                content
            };
            if candidate == delim {
                if line_start > body_start {
                    self.push(kind::HEREDOC_BODY, body_start, line_start, false);
                }
                self.push(kind::HEREDOC_END, line_start, after, false);
                self.pos = after;
                return;
            }
            scan = after;
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
        self.prev_word_like = !trivia
            && (k == kind::WORD
                || k == kind::NUMBER
                || k == kind::STRING
                || k == kind::EXPANSION
                || k == kind::HEREDOC_DELIM
                || k == kind::HEREDOC_BODY
                || k == kind::HEREDOC_END);
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
            "#!/bin/bash\necho hello\n",
            "f() {\n  echo hi\n}\n",
            "x=1 ; y=$((x + 2))\n",
            "s='raw' + \"interp $x\" + $'ansi\\n' + `date`\n",
            "cat <<EOF\nbody $x\nmore\nEOF\n",
            "cat <<-'END'\n\tno-expand $x\n\tEND\n",
            "if [ -n \"$a\" ]; then echo y; fi  # trailing\n",
            "λ='☃ €'  # unicode\n",
            "a && b || c | d & e\n",
            "echo foo#bar  # real comment\n",
            "",
            "\n\n   \n# only blanks\n",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
            // And the token stream must reconstruct the source verbatim.
            let rebuilt: String = lex(src).iter().map(|t| t.span.text(src)).collect();
            assert_eq!(rebuilt, src, "not lossless: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("echo hello\n");
        assert!(t.contains(&(kind::WORD, "echo".to_string())));
        assert!(t.contains(&(kind::WORD, "hello".to_string())));
        assert!(t.iter().any(|(k, _)| *k == kind::NEWLINE));
        assert!(is_keyword("if"));
        assert!(is_keyword("function"));
        assert!(!is_keyword("echo"));
    }

    #[test]
    fn comment_only_at_word_boundary() {
        // `#` after whitespace is a comment; `#` mid-word is part of the word.
        let t = texts("echo foo#bar # c\n");
        assert!(t.contains(&(kind::WORD, "foo#bar".to_string())));
        assert!(t.iter().any(|(k, s)| *k == kind::COMMENT && s == "# c"));
    }

    #[test]
    fn expansions_are_single_tokens() {
        let t = texts("$x ${y} $(cmd a) $((1+2)) $? $1\n");
        for lit in ["$x", "${y}", "$(cmd a)", "$((1+2))", "$?", "$1"] {
            assert!(
                t.iter().any(|(k, s)| *k == kind::EXPANSION && s == lit),
                "expansion not recognized: {lit}"
            );
        }
    }

    #[test]
    fn string_forms() {
        for (src, lit) in [
            ("'literal'", "'literal'"),
            ("\"interp $x\"", "\"interp $x\""),
            ("$'ansi\\n'", "$'ansi\\n'"),
            ("$\"locale\"", "$\"locale\""),
        ] {
            let t = texts(src);
            assert!(
                t.iter().any(|(k, s)| *k == kind::STRING && s == lit),
                "string not recognized: {src}"
            );
        }
    }

    #[test]
    fn heredoc_body_is_captured() {
        let t = texts("cat <<EOF\nline one\nline $two\nEOF\n");
        assert!(t.iter().any(|(k, _)| *k == kind::HEREDOC_DELIM));
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::HEREDOC_BODY && s == "line one\nline $two\n"));
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::HEREDOC_END && s == "EOF\n"));
    }

    #[test]
    fn heredoc_strip_tabs_terminator() {
        let t = texts("cat <<-END\n\tbody\n\tEND\n");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::HEREDOC_END && s == "\tEND\n"));
    }

    #[test]
    fn operators_are_greedy() {
        let t = texts("a && b || c >> d 2>&1\n");
        assert!(t.contains(&(kind::OPERATOR, "&&".to_string())));
        assert!(t.contains(&(kind::OPERATOR, "||".to_string())));
        assert!(t.contains(&(kind::OPERATOR, ">>".to_string())));
        assert!(t.contains(&(kind::OPERATOR, ">&".to_string())));
    }

    #[test]
    fn assignment_splits_on_equals() {
        let t = texts("NAME=value\n");
        assert!(t.contains(&(kind::WORD, "NAME".to_string())));
        assert!(t.contains(&(kind::OPERATOR, "=".to_string())));
        assert!(t.contains(&(kind::WORD, "value".to_string())));
    }

    #[test]
    fn unterminated_string_is_error_not_dropped() {
        let src = "echo 'oops\n";
        let t = texts(src);
        assert!(t.iter().any(|(k, _)| *k == kind::ERROR));
        let rebuilt: String = lex(src).iter().map(|t| t.span.text(src)).collect();
        assert_eq!(rebuilt, src);
    }
}
