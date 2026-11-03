//! Lossless PHP lexer, grounded in the Zend token grammar.
//!
//! Guarantees (identical contract to the Rust and Python lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs/newlines, `//` / `#` / `/* */` comments) are emitted as
//!   `trivia` tokens, never discarded.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//!
//! PHP is a *templating* language: a file starts in **inline-HTML mode** and only
//! switches to **PHP mode** at an open tag (`<?php`, `<?=`, `<?`), returning to
//! HTML mode at a close tag (`?>`). The lexer tracks that mode so verbatim markup
//! outside `<?php … ?>` is preserved as `inline_html` tokens (non-trivia: it is
//! real content, not whitespace). The full string zoo — single/double quotes,
//! backtick shell-exec, heredoc and nowdoc — is handled, each as one
//! `string_literal` token (interpolation is not split; the lowering reads the
//! real tokens it needs and never invents).
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic` /
//! `is_alphanumeric` plus `_` as a pragmatic stand-in for PHP's
//! `[A-Za-z_\x80-\xff]` rule — anything outside still lands in the tree as a
//! covered token, never dropped.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// PHP keywords (8.x, including soft/contextual ones the parser may want to see).
/// Like the other front ends these lex as `name` tokens; the parser and lowering
/// distinguish them via [`is_keyword`].
pub const KEYWORDS: &[&str] = &[
    "abstract",
    "and",
    "array",
    "as",
    "break",
    "callable",
    "case",
    "catch",
    "class",
    "clone",
    "const",
    "continue",
    "declare",
    "default",
    "do",
    "echo",
    "else",
    "elseif",
    "empty",
    "enddeclare",
    "endfor",
    "endforeach",
    "endif",
    "endswitch",
    "endwhile",
    "enum",
    "extends",
    "final",
    "finally",
    "fn",
    "for",
    "foreach",
    "function",
    "global",
    "goto",
    "if",
    "implements",
    "include",
    "include_once",
    "instanceof",
    "insteadof",
    "interface",
    "isset",
    "list",
    "match",
    "namespace",
    "new",
    "or",
    "print",
    "private",
    "protected",
    "public",
    "readonly",
    "require",
    "require_once",
    "return",
    "static",
    "switch",
    "throw",
    "trait",
    "try",
    "unset",
    "use",
    "var",
    "while",
    "xor",
    "yield",
    "true",
    "false",
    "null",
    "self",
    "parent",
];

pub fn is_keyword(text: &str) -> bool {
    // PHP keywords are case-insensitive; compare a lowercased copy.
    let lower = text.to_ascii_lowercase();
    KEYWORDS.contains(&lower.as_str())
}

pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const COMMENT: &str = "comment";
    pub const INLINE_HTML: &str = "inline_html";
    pub const OPEN_TAG: &str = "open_tag";
    pub const CLOSE_TAG: &str = "close_tag";
    pub const NAME: &str = "name";
    pub const VARIABLE: &str = "variable";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const STRING: &str = "string_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
/// `<<<` (heredoc) and `#[` (attribute) are handled by dedicated branches before
/// this table is consulted, so they are intentionally absent here.
const OPERATORS: &[&str] = &[
    "<=>", "===", "!==", "**=", "<<=", ">>=", "??=", "...", "?->", "==", "!=", "<>", "<=", ">=",
    "&&", "||", "++", "--", "->", "=>", "::", "??", "**", "<<", ">>", "+=", "-=", "*=", "/=", ".=",
    "%=", "&=", "|=", "^=",
];

const SINGLE_PUNCT: &str = "+-*/%.!<>=&|^~?:;,()[]{}@\\";

pub fn lex(source: &str) -> Vec<Token> {
    Lexer::new(source).run()
}

struct Lexer<'s> {
    src: &'s str,
    bytes: &'s [u8],
    pos: usize,
    /// `true` while outside `<?php … ?>` — verbatim template markup.
    html_mode: bool,
    tokens: Vec<Token>,
}

impl<'s> Lexer<'s> {
    fn new(src: &'s str) -> Self {
        Lexer {
            src,
            bytes: src.as_bytes(),
            pos: 0,
            html_mode: true,
            tokens: Vec::new(),
        }
    }

    fn run(mut self) -> Vec<Token> {
        while self.pos < self.bytes.len() {
            if self.html_mode {
                self.lex_html();
            } else {
                self.lex_php_token();
            }
        }
        self.tokens
    }

    // --- HTML (template) mode -----------------------------------------------

    /// Emit verbatim markup up to the next `<?` open tag, then the open tag, and
    /// switch into PHP mode. If there is no further tag, the remainder is one
    /// `inline_html` token.
    fn lex_html(&mut self) {
        let start = self.pos;
        match self.src[self.pos..].find("<?") {
            Some(rel) => {
                let tag_at = start + rel;
                if tag_at > start {
                    self.push(kind::INLINE_HTML, start, tag_at, false);
                    self.pos = tag_at;
                }
                self.lex_open_tag();
                self.html_mode = false;
            }
            None => {
                self.pos = self.bytes.len();
                self.push(kind::INLINE_HTML, start, self.pos, false);
            }
        }
    }

    /// Consume an open tag (`<?php`, `<?=`, or short `<?`). Always advances at
    /// least two bytes, guaranteeing progress.
    fn lex_open_tag(&mut self) {
        let start = self.pos;
        let rest = &self.src[self.pos..];
        if rest.starts_with("<?php") && !self.is_ident_byte_at(start + 5) {
            self.pos += 5;
        } else if rest.starts_with("<?=") {
            self.pos += 3;
        } else {
            self.pos += 2; // short open tag `<?`
        }
        self.push(kind::OPEN_TAG, start, self.pos, false);
    }

    // --- PHP mode ------------------------------------------------------------

    fn lex_php_token(&mut self) {
        let start = self.pos;

        // Close tag returns control to template (HTML) mode.
        if self.src[self.pos..].starts_with("?>") {
            self.pos += 2;
            self.push(kind::CLOSE_TAG, start, self.pos, false);
            self.html_mode = true;
            return;
        }

        let c = self.peek();
        match c {
            ' ' | '\t' | '\n' | '\r' | '\x0c' => {
                self.eat_while(|c| matches!(c, ' ' | '\t' | '\n' | '\r' | '\x0c'));
                self.push(kind::WHITESPACE, start, self.pos, true);
            }
            '/' if self.peek_at(1) == Some('/') => {
                let end = self.line_or_tag_end(start);
                self.pos = end;
                self.push(kind::COMMENT, start, end, true);
            }
            '/' if self.peek_at(1) == Some('*') => {
                self.block_comment(start);
            }
            '#' if self.peek_at(1) == Some('[') => {
                // PHP 8 attribute opener `#[` — punctuation, not a comment.
                self.pos += 2;
                self.push(kind::PUNCT, start, self.pos, false);
            }
            '#' => {
                let end = self.line_or_tag_end(start);
                self.pos = end;
                self.push(kind::COMMENT, start, end, true);
            }
            '<' if self.peek_at(1) == Some('<') && self.peek_at(2) == Some('<') => {
                self.heredoc(start);
            }
            '\'' => self.single_quoted(start),
            '"' | '`' => self.double_quoted(start, c),
            '$' if self.peek_at(1).map(is_ident_start).unwrap_or(false) => {
                self.pos += 1; // `$`
                self.eat_while(is_ident_continue);
                self.push(kind::VARIABLE, start, self.pos, false);
            }
            c if is_ident_start(c) => {
                self.eat_while(is_ident_continue);
                self.push(kind::NAME, start, self.pos, false);
            }
            c if c.is_ascii_digit() => self.number(start),
            '.' if self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) => {
                self.number(start)
            }
            _ => self.punct(start),
        }
    }

    fn block_comment(&mut self, start: usize) {
        self.pos += 2; // `/*`
        match self.src[self.pos..].find("*/") {
            Some(rel) => self.pos += rel + 2,
            None => self.pos = self.bytes.len(),
        }
        self.push(kind::COMMENT, start, self.pos, true);
    }

    /// Single-quoted string: only `\\` and `\'` are escapes, but to find the
    /// terminator it suffices to skip the byte after any backslash.
    fn single_quoted(&mut self, start: usize) {
        self.bump(); // opening quote
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            match self.peek() {
                '\\' => {
                    self.bump();
                    if self.pos < self.bytes.len() {
                        self.bump();
                    }
                }
                '\'' => {
                    self.bump();
                    terminated = true;
                    break;
                }
                _ => self.bump(),
            }
        }
        self.push(self.str_kind(terminated), start, self.pos, false);
    }

    /// Double-quoted string or backtick shell-exec string. Backslash escapes the
    /// next byte; the matching `quote` terminates. Interpolation (`$x`, `{$x}`) is
    /// left inside the single token — the lowering reads what it needs later.
    fn double_quoted(&mut self, start: usize, quote: char) {
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
        self.push(self.str_kind(terminated), start, self.pos, false);
    }

    /// Heredoc (`<<<LABEL`) or nowdoc (`<<<'LABEL'`). The body runs until a line
    /// whose first non-whitespace content is `LABEL` followed by a non-identifier
    /// byte (PHP 7.3+ allows the closing marker to be indented). Captured as one
    /// `string_literal`; an unterminated doc becomes an `error` token to EOF.
    fn heredoc(&mut self, start: usize) {
        self.pos += 3; // `<<<`
        self.eat_while(|c| c == ' ' || c == '\t');
        // Optional quote around the label (`"LABEL"` heredoc, `'LABEL'` nowdoc).
        let quote = match self.peek() {
            '\'' => {
                self.bump();
                Some('\'')
            }
            '"' => {
                self.bump();
                Some('"')
            }
            _ => None,
        };
        let label_start = self.pos;
        if self.peek_satisfies(is_ident_start) {
            self.eat_while(is_ident_continue);
        }
        let label = self.src[label_start..self.pos].to_string();
        if let Some(q) = quote {
            if self.peek() == q {
                self.bump();
            }
        }
        if label.is_empty() {
            // No valid label: emit what we consumed as an error and bail (we have
            // advanced at least three bytes, so progress is guaranteed).
            self.push(kind::ERROR, start, self.pos, false);
            return;
        }
        // Consume the remainder of the opening line (through its newline).
        match self.src[self.pos..].find('\n') {
            Some(rel) => self.pos += rel + 1,
            None => {
                self.pos = self.bytes.len();
                self.push(kind::ERROR, start, self.pos, false);
                return;
            }
        }
        // Scan body lines for the closing label.
        let lbytes = label.as_bytes();
        let mut terminated = false;
        while self.pos < self.bytes.len() {
            let mut q = self.pos;
            while q < self.bytes.len() && matches!(self.bytes[q], b' ' | b'\t') {
                q += 1;
            }
            if self.src[q..].starts_with(&label) {
                let after = q + lbytes.len();
                if after >= self.bytes.len() || !is_ident_byte(self.bytes[after]) {
                    self.pos = after; // include the closing label in the token
                    terminated = true;
                    break;
                }
            }
            match self.src[self.pos..].find('\n') {
                Some(rel) => self.pos += rel + 1,
                None => {
                    self.pos = self.bytes.len();
                    break;
                }
            }
        }
        self.push(self.str_kind(terminated), start, self.pos, false);
    }

    fn number(&mut self, start: usize) {
        let mut is_float = false;
        if self.peek() == '0' {
            match self.peek_at(1) {
                Some('x') | Some('X') => {
                    self.pos += 2;
                    self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
                    return self.push(kind::INT, start, self.pos, false);
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
        if self.peek() == '.' && self.peek_at(1) != Some('.') {
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
        let c = self.peek();
        if SINGLE_PUNCT.contains(c) {
            self.bump();
            self.push(kind::PUNCT, start, self.pos, false);
        } else {
            self.bump();
            self.push(kind::ERROR, start, self.pos, false);
        }
    }

    // --- primitives ----------------------------------------------------------

    fn peek(&self) -> char {
        self.src[self.pos..].chars().next().unwrap_or('\0')
    }

    fn peek_at(&self, n: usize) -> Option<char> {
        self.src[self.pos..].chars().nth(n)
    }

    fn peek_satisfies(&self, pred: impl Fn(char) -> bool) -> bool {
        self.src[self.pos..]
            .chars()
            .next()
            .map(pred)
            .unwrap_or(false)
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

    /// End of a `//` / `#` line comment: the earlier of the next newline or the
    /// next `?>` close tag (a close tag terminates a line comment in PHP).
    fn line_or_tag_end(&self, from: usize) -> usize {
        let nl = self.src[from..]
            .find('\n')
            .map(|i| from + i)
            .unwrap_or(self.bytes.len());
        let tag = self.src[from..]
            .find("?>")
            .map(|i| from + i)
            .unwrap_or(self.bytes.len());
        nl.min(tag)
    }

    fn is_ident_byte_at(&self, idx: usize) -> bool {
        self.bytes
            .get(idx)
            .copied()
            .map(is_ident_byte)
            .unwrap_or(false)
    }

    fn str_kind(&self, terminated: bool) -> &'static str {
        if terminated {
            kind::STRING
        } else {
            kind::ERROR
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
    c == '_' || c.is_alphanumeric()
}

fn is_ident_byte(b: u8) -> bool {
    b == b'_' || b.is_ascii_alphanumeric() || b >= 0x80
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
            "<?php function f($x) { return $x; }\n",
            "<h1>Title</h1>\n<?php echo $name; ?>\n<p>after</p>\n",
            "<?php $h = <<<EOT\nhello $name\nEOT;\n",
            "<?php $n = <<<'RAW'\nno $interp here\nRAW;\n",
            "<?php $x = 0xFF_00 + 1.5e3 + 0b1010 + 017;\n",
            "<?php $s = 'a\\'b' . \"c{$d}e\" . `ls -la`;\n",
            "<?php // line comment\n# hash comment\n/* block */ $a = 1;\n",
            "<?= $short ?>",
            "<?php $o?->m() ?? $x <=> $y; #[Attr] class C {}\n",
            "λ + €", // bare HTML / unicode, never enters PHP mode
            "",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
            let tree_ok = {
                let toks = lex(src);
                let mut rebuilt = String::new();
                for t in &toks {
                    rebuilt.push_str(t.span.text(src));
                }
                rebuilt == src
            };
            assert!(tree_ok, "not lossless: {src:?}");
        }
    }

    #[test]
    fn classifies_core_tokens() {
        let t = texts("<?php function add($a, $b) { return $a + $b; }\n");
        assert!(t.contains(&(kind::OPEN_TAG, "<?php".to_string())));
        assert!(t.contains(&(kind::NAME, "function".to_string())));
        assert!(t.contains(&(kind::NAME, "add".to_string())));
        assert!(t.contains(&(kind::VARIABLE, "$a".to_string())));
        assert!(t.contains(&(kind::PUNCT, "(".to_string())));
        assert!(is_keyword("function"));
        assert!(is_keyword("FUNCTION")); // case-insensitive
        assert!(!is_keyword("add"));
    }

    #[test]
    fn inline_html_is_preserved_as_content() {
        let t = texts("<div><?php echo 1; ?></div>");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::INLINE_HTML && s == "<div>"));
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::INLINE_HTML && s == "</div>"));
        assert!(t.iter().any(|(k, _)| *k == kind::CLOSE_TAG));
    }

    #[test]
    fn heredoc_and_nowdoc_span_newlines() {
        let t = texts("<?php $a = <<<EOT\nline1 $x\nline2\nEOT;\n");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s.starts_with("<<<EOT") && s.ends_with("EOT")));
        let n = texts("<?php $a = <<<'RAW'\nraw $x\nRAW;\n");
        assert!(n
            .iter()
            .any(|(k, s)| *k == kind::STRING && s.contains("raw $x")));
    }

    #[test]
    fn numbers() {
        let t = texts("<?php $a = 0b1010 + 0o17 + 0xAF + 10_000 + 3.14 + 2e10;");
        assert!(t.contains(&(kind::INT, "0b1010".to_string())));
        assert!(t.contains(&(kind::INT, "0xAF".to_string())));
        assert!(t.contains(&(kind::INT, "10_000".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14".to_string())));
        assert!(t.contains(&(kind::FLOAT, "2e10".to_string())));
    }

    #[test]
    fn nullsafe_and_spaceship_operators() {
        let t = texts("<?php $a?->b <=> $c ??= $d;");
        assert!(t.contains(&(kind::PUNCT, "?->".to_string())));
        assert!(t.contains(&(kind::PUNCT, "<=>".to_string())));
        assert!(t.contains(&(kind::PUNCT, "??=".to_string())));
    }

    #[test]
    fn attribute_opener_is_not_a_comment() {
        let t = texts("<?php #[Route('/x')] function f() {}");
        assert!(t.contains(&(kind::PUNCT, "#[".to_string())));
        assert!(t.iter().all(|(k, _)| *k != kind::ERROR));
    }
}
