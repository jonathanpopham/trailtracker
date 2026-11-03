//! Lossless Elixir lexer, grounded in the Elixir token grammar.
//!
//! Guarantees (identical contract to the Rust, Python, and Ruby lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs/form-feed, `#` line comments) are emitted as `trivia`
//!   tokens, never dropped. `newline` is emitted as a *non-trivia* token because
//!   it separates statements (the parser uses it for structure).
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//!
//! Elixir surface handled honestly: `#` line comments; double-quoted strings and
//! single-quoted charlists, plus their `"""` / `'''` heredoc forms; `:atoms`
//! (bare, quoted, and operator atoms); sigils (`~w[]`, `~s""`, `~r//`, and the
//! `~s"""` / `~S'''` heredoc sigils); module attributes (`@doc`, `@spec`, `@x`);
//! `?a` char codes; numbers with `_`, `0x`/`0o`/`0b`, floats and exponents.
//!
//! The main run loop carries a hard progress guard: if a dispatch iteration fails
//! to advance `pos`, one byte is consumed as an `error` token. A non-advancing
//! loop is an infinite loop, so every sub-scanner also bumps on every path.
//!
//! Coverage note (honest): identifier start/continue uses `char::is_alphabetic` /
//! `is_alphanumeric` plus `_` as a pragmatic stand-in for Elixir's full Unicode
//! identifier rules; string/heredoc interpolation (`#{...}`) is kept inside the
//! single string token rather than re-lexed. Every such byte still lands in the
//! tree, never dropped.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Elixir's reserved words and the def-family macros. Like the other lexers,
/// these lex as `ident` tokens; the parser/lowering distinguish them via
/// [`is_keyword`]. (Several are technically macros, not keywords, but treating
/// them as keywords keeps the call scanner from inventing spurious calls.)
pub const KEYWORDS: &[&str] = &[
    "true",
    "false",
    "nil",
    "when",
    "and",
    "or",
    "not",
    "in",
    "fn",
    "do",
    "end",
    "catch",
    "rescue",
    "after",
    "else",
    "import",
    "require",
    "alias",
    "use",
    "def",
    "defp",
    "defmodule",
    "defmacro",
    "defmacrop",
    "defstruct",
    "defprotocol",
    "defimpl",
    "defdelegate",
    "defguard",
    "defguardp",
    "defexception",
    "defoverridable",
    "if",
    "unless",
    "case",
    "cond",
    "for",
    "with",
    "try",
    "receive",
    "quote",
    "unquote",
    "unquote_splicing",
    "super",
    "__MODULE__",
    "__DIR__",
    "__ENV__",
    "__CALLER__",
    "__aliases__",
    "__block__",
];

pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.contains(&text)
}

pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const NEWLINE: &str = "newline";
    pub const COMMENT: &str = "comment";
    pub const IDENT: &str = "ident";
    pub const ATTRIBUTE: &str = "attribute";
    pub const ATOM: &str = "atom_literal";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const STRING: &str = "string_literal";
    pub const CHARLIST: &str = "charlist_literal";
    pub const SIGIL: &str = "sigil_literal";
    pub const CHAR: &str = "char_literal";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
const OPERATORS: &[&str] = &[
    "^^^", "~~~", ">>>", "<<<", "&&&", "|||", "===", "!==", "...", "<~>", "<|>", "~>>", "<<~",
    "->", "<-", "|>", "<>", "++", "--", "**", "==", "!=", "<=", ">=", "&&", "||", "::", "..", "=~",
    "=>", "<~", "~>", "\\\\", "&.",
];

const SINGLE_PUNCT: &str = "+-*/%<>=&|^~!?.,;:()[]{}@\\";

/// Operator method names that may follow a `:` to form an operator atom
/// (`:++`, `:<>`, `:+`), longest first.
const SYMBOL_OPS: &[&str] = &[
    "<<<", ">>>", "&&&", "|||", "===", "!==", "...", "++", "--", "<>", "..", "==", "!=", "<=",
    ">=", "&&", "||", "::", "<-", "->", "|>", "=~", "+", "-", "*", "/", "<", ">", "!", "&", "|",
    "^", "~",
];

/// Valid sigil delimiters (the byte that follows the sigil letter run).
const SIGIL_DELIMS: &str = "/|\"'([{<";

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
                ' ' | '\t' | '\x0c' => {
                    self.eat_while(|c| c == ' ' || c == '\t' || c == '\x0c');
                    self.push(kind::WHITESPACE, start, self.pos, true);
                }
                '#' => {
                    let end = self.find_line_end(start);
                    self.pos = end;
                    self.push(kind::COMMENT, start, end, true);
                }
                '"' => {
                    if self.src[start..].starts_with("\"\"\"") {
                        self.heredoc(start, '"');
                    } else {
                        self.string(start, '"', kind::STRING);
                    }
                }
                '\'' => {
                    if self.src[start..].starts_with("'''") {
                        self.heredoc(start, '\'');
                    } else {
                        self.string(start, '\'', kind::CHARLIST);
                    }
                }
                '~' => {
                    if let Some(end) = self.try_sigil(start) {
                        self.pos = end;
                        self.push(kind::SIGIL, start, end, false);
                    } else {
                        self.punct(start);
                    }
                }
                ':' => self.colon(start),
                '?' if self.char_literal_follows() => self.char_literal(start),
                '@' if self.peek_at(1).map(is_ident_start).unwrap_or(false) => {
                    self.attribute(start)
                }
                c if is_ident_start(c) => self.name(start),
                c if c.is_ascii_digit() => self.number(start),
                c if SINGLE_PUNCT.contains(c) => self.punct(start),
                _ => {
                    self.bump();
                    self.push(kind::ERROR, start, self.pos, false);
                }
            }
            // Hard progress guard: if a dispatch path consumed nothing, force one
            // byte forward as an error token. A non-advancing loop is an OOM bug.
            if self.pos == start {
                self.bump();
                self.push(kind::ERROR, start, self.pos, false);
            }
        }
        self.tokens
    }

    // --- identifiers / attributes ------------------------------------------

    fn name(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        // Predicate/bang method suffix: `valid?`, `save!`. Do not absorb the `?`
        // of `?=` or the `!` of `!=`.
        if matches!(self.peek(), '?' | '!') && self.peek_at(1) != Some('=') {
            self.bump();
        }
        self.push(kind::IDENT, start, self.pos, false);
    }

    /// `@doc`, `@spec`, `@attr` — a module attribute (cursor on `@`, an
    /// ident-start follows).
    fn attribute(&mut self, start: usize) {
        self.bump(); // @
        self.eat_while(is_ident_continue);
        self.push(kind::ATTRIBUTE, start, self.pos, false);
    }

    // --- strings / charlists -----------------------------------------------

    /// Scan a quoted string/charlist for the given `quote` char. A backslash
    /// escapes the next byte; consuming runs to the close quote or EOF.
    fn string(&mut self, start: usize, quote: char, kind: &'static str) {
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
        let k = if terminated { kind } else { kind::ERROR };
        self.push(k, start, self.pos, false);
    }

    /// `"""` / `'''` heredoc (cursor on the opening triple). The body runs to the
    /// line whose first non-whitespace content is the closing triple. Unterminated
    /// heredocs extend to EOF — still lossless.
    fn heredoc(&mut self, start: usize, quote: char) {
        self.pos += 3; // opening triple
        let triple = if quote == '"' { "\"\"\"" } else { "'''" };
        let mut terminated = false;
        let mut line_start = self.pos;
        while line_start < self.bytes.len() {
            let line_end = match self.src[line_start..].find('\n') {
                Some(i) => line_start + i + 1,
                None => self.bytes.len(),
            };
            let line = &self.src[line_start..line_end];
            let trimmed = line.trim_start_matches([' ', '\t']);
            if trimmed.starts_with(triple) {
                let ws_len = line.len() - trimmed.len();
                self.pos = line_start + ws_len + 3;
                terminated = true;
                break;
            }
            line_start = line_end;
        }
        if !terminated {
            self.pos = self.bytes.len();
        }
        let k = if terminated {
            if quote == '"' {
                kind::STRING
            } else {
                kind::CHARLIST
            }
        } else {
            kind::ERROR
        };
        self.push(k, start, self.pos, false);
    }

    /// `?a`, `?\n` — a single char-code literal.
    fn char_literal(&mut self, start: usize) {
        self.bump(); // ?
        if self.peek() == '\\' {
            self.bump();
        }
        if self.pos < self.bytes.len() {
            self.bump();
        }
        self.push(kind::CHAR, start, self.pos, false);
    }

    fn char_literal_follows(&self) -> bool {
        match self.peek_at(1) {
            None => false,
            Some(c) => !c.is_whitespace(),
        }
    }

    // --- atoms --------------------------------------------------------------

    fn colon(&mut self, start: usize) {
        // `::` scope/typespec operator.
        if self.peek_at(1) == Some(':') {
            return self.punct(start);
        }
        match self.peek_at(1) {
            Some('"') => {
                self.bump(); // :
                self.string(start, '"', kind::STRING);
                self.relabel_last(kind::ATOM);
            }
            Some('\'') => {
                self.bump(); // :
                self.string(start, '\'', kind::CHARLIST);
                self.relabel_last(kind::ATOM);
            }
            Some(c) if is_ident_start(c) => {
                self.bump(); // :
                self.eat_while(is_ident_continue);
                if matches!(self.peek(), '?' | '!') {
                    self.bump();
                }
                self.push(kind::ATOM, start, self.pos, false);
            }
            Some(_) => {
                // Operator atom: `:++`, `:<>`, `:+`.
                let rest = &self.src[self.pos + 1..];
                if let Some(op) = SYMBOL_OPS.iter().find(|op| rest.starts_with(**op)) {
                    self.pos += 1 + op.len();
                    self.push(kind::ATOM, start, self.pos, false);
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

    // --- sigils -------------------------------------------------------------

    /// Detect a sigil at `start` (cursor on `~`): one or more letters then a
    /// delimiter. Returns the end offset, or `None` when `~` is an operator
    /// (`~>`, `~~~`). Heredoc sigils (`~s"""`) and paired/unpaired delimiters are
    /// handled. Trailing modifier letters are absorbed.
    fn try_sigil(&self, start: usize) -> Option<usize> {
        let mut p = start + 1; // after ~
        let letter_start = p;
        while let Some(b) = self.byte_at(p) {
            if (b as char).is_ascii_alphabetic() {
                p += 1;
            } else {
                break;
            }
        }
        if p == letter_start {
            return None; // `~` not followed by a letter -> operator
        }
        let delim = self.src[p..].chars().next()?;
        // Heredoc sigil: `~s"""` / `~S'''`.
        if (delim == '"' && self.src[p..].starts_with("\"\"\""))
            || (delim == '\'' && self.src[p..].starts_with("'''"))
        {
            let triple = if delim == '"' { "\"\"\"" } else { "'''" };
            let mut q = p + 3;
            let mut line_start = q;
            let mut terminated = false;
            while line_start < self.bytes.len() {
                let line_end = match self.src[line_start..].find('\n') {
                    Some(i) => line_start + i + 1,
                    None => self.bytes.len(),
                };
                let line = &self.src[line_start..line_end];
                let trimmed = line.trim_start_matches([' ', '\t']);
                if trimmed.starts_with(triple) {
                    let ws_len = line.len() - trimmed.len();
                    q = line_start + ws_len + 3;
                    terminated = true;
                    break;
                }
                line_start = line_end;
            }
            if !terminated {
                return Some(self.bytes.len());
            }
            return Some(self.eat_sigil_mods(q));
        }
        if !SIGIL_DELIMS.contains(delim) {
            return None;
        }
        let (open, close) = match delim {
            '(' => ('(', ')'),
            '[' => ('[', ']'),
            '{' => ('{', '}'),
            '<' => ('<', '>'),
            other => (other, other),
        };
        let nests = open != close;
        let mut q = p + delim.len_utf8();
        let mut depth = 1i32;
        while q < self.bytes.len() {
            let ch = self.src[q..].chars().next().unwrap_or('\0');
            if ch == '\\' {
                q += 1;
                if q < self.bytes.len() {
                    q += self.src[q..]
                        .chars()
                        .next()
                        .map(|c| c.len_utf8())
                        .unwrap_or(1);
                }
                continue;
            }
            if nests && ch == open {
                depth += 1;
            } else if ch == close {
                depth -= 1;
                q += ch.len_utf8();
                if depth == 0 {
                    break;
                }
                continue;
            }
            q += ch.len_utf8();
        }
        Some(self.eat_sigil_mods(q))
    }

    fn eat_sigil_mods(&self, mut p: usize) -> usize {
        while let Some(b) = self.byte_at(p) {
            if (b as char).is_ascii_alphabetic() {
                p += 1;
            } else {
                break;
            }
        }
        p
    }

    // --- numbers ------------------------------------------------------------

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
        if self.peek() == '.' && self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) {
            is_float = true;
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
            "defmodule M do\n  def add(a, b), do: a + b\nend\n",
            "x = 0xFF_00 + 1.5e3 + 0b1010 + 0o17\n",
            "s = \"a #{x} b\" <> 'charlist' <> \"\"\"\nheredoc\n\"\"\"\n",
            "w = ~w[a b c] ++ ~s\"hi\" ++ ~r/ab+c/i\n",
            "h = ~s\"\"\"\n  sigil heredoc\n  \"\"\"\n",
            "a = :ok\nb = :\"quoted atom\"\nc = :<>\nd = :++\n",
            "@moduledoc \"docs\"\n@spec f(integer) :: integer\n@x 1\n",
            "ch = ?a\nnl = ?\\n\nq = a ~> b\nbnot = ~~~x\n",
            "p = x |> foo() |> bar()\nf = fn y -> y * 2 end\n",
            "λ = \"☃ €\"  # unicode\n",
            "alias My.App.{User, Post}\nimport Enum, only: [map: 2]\n",
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
    fn classifies_core_tokens() {
        let t = texts("def add(a, b) do\n  a + b\nend\n");
        assert!(t.contains(&(kind::IDENT, "def".to_string())));
        assert!(t.contains(&(kind::IDENT, "add".to_string())));
        assert!(t.contains(&(kind::PUNCT, "(".to_string())));
        assert!(t.iter().any(|(k, _)| *k == kind::NEWLINE));
        assert!(is_keyword("def"));
        assert!(is_keyword("end"));
        assert!(!is_keyword("add"));
    }

    #[test]
    fn atoms_and_attributes() {
        let t = texts(":foo :\"bar\" :<> :++ @doc @spec\n");
        assert!(t.contains(&(kind::ATOM, ":foo".to_string())));
        assert!(t.contains(&(kind::ATOM, ":\"bar\"".to_string())));
        assert!(t.contains(&(kind::ATOM, ":<>".to_string())));
        assert!(t.contains(&(kind::ATOM, ":++".to_string())));
        assert!(t.contains(&(kind::ATTRIBUTE, "@doc".to_string())));
        assert!(t.contains(&(kind::ATTRIBUTE, "@spec".to_string())));
    }

    #[test]
    fn keyword_colon_is_not_an_atom() {
        // Trailing `key:` (keyword syntax) is ident + punct, not a leading atom.
        let t = texts("[do: 1, else: 2]\n");
        assert!(t.contains(&(kind::IDENT, "do".to_string())));
        assert!(t.contains(&(kind::PUNCT, ":".to_string())));
        assert!(!t.iter().any(|(k, _)| *k == kind::ATOM));
    }

    #[test]
    fn sigils_vs_operators() {
        let t = texts("~w[a b] ~r/x/i ~s\"y\" a ~> b ~~~c\n");
        let sigils: Vec<&String> = t
            .iter()
            .filter(|(k, _)| *k == kind::SIGIL)
            .map(|(_, s)| s)
            .collect();
        assert!(sigils.iter().any(|s| *s == "~w[a b]"));
        assert!(sigils.iter().any(|s| *s == "~r/x/i"));
        assert!(sigils.iter().any(|s| *s == "~s\"y\""));
        // `~>` and `~~~` stay operators.
        assert!(t.contains(&(kind::PUNCT, "~>".to_string())));
        assert!(t.contains(&(kind::PUNCT, "~~~".to_string())));
    }

    #[test]
    fn heredoc_is_one_token() {
        let t = texts("x = \"\"\"\n  line one\n  line two\n  \"\"\"\ny = 1\n");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s.contains("line one") && s.contains("line two")));
        assert!(covers_all("x = \"\"\"\n  line one\n  \"\"\"\n"));
    }

    #[test]
    fn numbers() {
        let t = texts("0xAF 0o17 0b1010 10_000 3.14 2.0e10\n");
        assert!(t.contains(&(kind::INT, "0xAF".to_string())));
        assert!(t.contains(&(kind::INT, "0o17".to_string())));
        assert!(t.contains(&(kind::INT, "10_000".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14".to_string())));
        assert!(t.contains(&(kind::FLOAT, "2.0e10".to_string())));
    }

    #[test]
    fn predicate_and_bang_names() {
        let t = texts("x.empty? && y.save!\na != b\n");
        assert!(t.contains(&(kind::IDENT, "empty?".to_string())));
        assert!(t.contains(&(kind::IDENT, "save!".to_string())));
        assert!(t.contains(&(kind::PUNCT, "!=".to_string())));
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "s = \"oops\n",
            "λ = '☃'  # unicode\n",
            "h = \"\"\"\nunterminated heredoc\n",
            "",
            "\n\n   \n# trailing\n",
            "~r{unterminated",
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
}
