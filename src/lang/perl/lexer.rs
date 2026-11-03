//! Lossless Perl lexer, grounded in the perlop/perldata token surface.
//!
//! Guarantees (identical contract to the Rust/Python/Ruby lexers):
//! - Every byte of input is covered by exactly one token (contiguous spans), so
//!   the token stream reconstructs the source verbatim.
//! - Trivia (spaces/tabs, `#` line comments, POD `=pod`…`=cut` blocks, backslash
//!   line continuations, and a trailing `__END__`/`__DATA__` section) are emitted
//!   as `trivia` tokens, never dropped. A newline is *also* trivia: unlike Ruby,
//!   Perl statements terminate with `;`, so a bare newline carries no structure.
//! - Anything the lexer cannot classify becomes an `error` token over the exact
//!   bytes. Input is never silently dropped.
//!
//! Perl is the textbook context-sensitive language: `/` is regex *or* division,
//! `%`/`&`/`*` are sigils *or* operators, `q()/qq()/qw()/qr()/m//` and friends are
//! quote-like terms, and `<<EOF` is a heredoc *or* a left-shift. The lexer
//! disambiguates with a single running bit — whether the previous significant
//! token *ends a value* — exactly as a real Perl lexer does. Heredocs are handled
//! with a pending queue: the opener token is emitted in place, the rest of the
//! line lexes normally, and at the next newline the bodies are consumed (FIFO) as
//! `heredoc_body` tokens. The result is always contiguous and lossless.
//!
//! Coverage note (honest, COARSE by design):
//! - Identifier start/continue uses `char::is_alphabetic`/`is_alphanumeric` plus
//!   `_` as a pragmatic stand-in for Perl's full identifier rules; `::` package
//!   separators are folded into one identifier token.
//! - Interpolation (`$x`, `@{...}`, `${...}`) inside `"`/`` ` ``/heredoc/quote-like
//!   bodies is kept *inside* the single string token rather than re-lexed.
//! - A quote-like operator is only recognized at a value-begin position and only
//!   when the delimiter is *immediately* adjacent (no `q (x)` with a space); the
//!   rare spaced form degrades to a bareword + group, still lossless.
//! - A bare `<<ID` heredoc is only taken at a value-begin position (so `$x << 2`
//!   stays a shift); `<<~ID`, `<<"ID"`, `<<'ID'` are always heredocs.
//!
//! Every such byte still lands in the tree, never dropped, and the main run-loop
//! has a progress guard: if a pass consumes nothing, one byte is taken as `error`
//! so the lexer can never spin.

use crate::core::cst::Token;
use crate::core::span::ByteSpan;

/// Perl's most common reserved words / named operators. Like the other lexers,
/// these lex as `ident` tokens; the parser/lowering distinguish them via
/// [`is_keyword`]. This is a pragmatic (not exhaustive) set — it is used only to
/// keep barewords like `if`/`return`/`print` out of the call graph.
pub const KEYWORDS: &[&str] = &[
    "and",
    "cmp",
    "continue",
    "do",
    "else",
    "elsif",
    "eq",
    "for",
    "foreach",
    "ge",
    "given",
    "gt",
    "if",
    "le",
    "local",
    "lt",
    "my",
    "ne",
    "no",
    "not",
    "or",
    "our",
    "package",
    "redo",
    "require",
    "return",
    "state",
    "sub",
    "unless",
    "until",
    "use",
    "wantarray",
    "when",
    "while",
    "x",
    "xor",
    "last",
    "next",
    "BEGIN",
    "END",
    "__PACKAGE__",
    "__FILE__",
    "__LINE__",
    "__SUB__",
    "__END__",
    "__DATA__",
];

pub fn is_keyword(text: &str) -> bool {
    KEYWORDS.contains(&text)
}

/// Words after which a `/` is a regex (not division) and a quote-like operator is
/// a term — i.e. words that do **not** end a value. Anything not listed (a normal
/// bareword / function returning a value) is treated as value-ending.
fn word_ends_value(text: &str) -> bool {
    if is_special_value_word(text) {
        return true;
    }
    !NON_VALUE_WORDS.contains(&text)
}

/// Builtins/keywords commonly *followed by a term* (a regex, list, or quote-like).
/// After one of these the lexer is in value-begin position.
const NON_VALUE_WORDS: &[&str] = &[
    "and",
    "or",
    "not",
    "xor",
    "eq",
    "ne",
    "lt",
    "gt",
    "le",
    "ge",
    "cmp",
    "x",
    "if",
    "unless",
    "while",
    "until",
    "for",
    "foreach",
    "when",
    "return",
    "print",
    "printf",
    "say",
    "push",
    "unshift",
    "pop",
    "shift",
    "split",
    "grep",
    "map",
    "join",
    "sort",
    "reverse",
    "keys",
    "values",
    "each",
    "defined",
    "ref",
    "scalar",
    "exists",
    "delete",
    "bless",
    "die",
    "warn",
    "do",
    "my",
    "our",
    "local",
    "state",
    "use",
    "no",
    "require",
    "sub",
    "wantarray",
    "else",
    "elsif",
];

/// A few keywords that *do* end a value (so a following `/` is division).
fn is_special_value_word(text: &str) -> bool {
    matches!(
        text,
        "__PACKAGE__" | "__FILE__" | "__LINE__" | "__SUB__" | "wantarray" | "time" | "undef"
    )
}

pub mod kind {
    pub const WHITESPACE: &str = "whitespace";
    pub const NEWLINE: &str = "newline";
    pub const COMMENT: &str = "comment";
    pub const POD: &str = "pod";
    pub const DATA_SECTION: &str = "data_section";
    pub const LINE_CONTINUATION: &str = "line_continuation";
    pub const IDENT: &str = "ident";
    pub const SCALAR_VAR: &str = "scalar_var";
    pub const ARRAY_VAR: &str = "array_var";
    pub const HASH_VAR: &str = "hash_var";
    pub const AMP_VAR: &str = "amp_var";
    pub const GLOB_VAR: &str = "glob_var";
    pub const INT: &str = "int_literal";
    pub const FLOAT: &str = "float_literal";
    pub const STRING: &str = "string_literal";
    pub const REGEX: &str = "regex_literal";
    pub const HEREDOC_OPEN: &str = "heredoc_open";
    pub const HEREDOC_BODY: &str = "heredoc_body";
    pub const PUNCT: &str = "punct";
    pub const ERROR: &str = "error";
}

/// Multi-character operators, longest first so the scanner is greedy-correct.
/// (`x=` is intentionally absent: `x` is a letter, so it is never reached from the
/// punctuation scanner.)
const OPERATORS: &[&str] = &[
    "<<=", ">>=", "**=", "||=", "&&=", "//=", "...", "<=>", "->", "=>", "::", "==", "!=", "<=",
    ">=", "=~", "!~", "**", "++", "--", "&&", "||", "//", "..", "<<", ">>", "+=", "-=", "*=", "/=",
    ".=", "%=", "|=", "&=", "^=",
];

const SINGLE_PUNCT: &str = "+-*/%&|^~<>=()[]{}:,.;!?\\@$";

/// Quote-like operators, longest first so `qq`/`qw`/`qr`/`qx`/`tr` win over `q`.
const QUOTE_OPS: &[&str] = &["tr", "qq", "qw", "qr", "qx", "q", "m", "s", "y"];

/// A pending heredoc whose body is consumed at the next newline.
struct PendingHeredoc {
    id: String,
    /// `<<~` indented form: the terminator may be indented and is matched trimmed.
    squiggly: bool,
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
    /// regex/heredoc/sigil/quote-like disambiguation).
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
            let start = self.pos;
            let c = self.peek();
            match c {
                '\n' => {
                    self.bump();
                    self.push(kind::NEWLINE, start, self.pos, true);
                    self.drain_heredocs();
                }
                '\r' => {
                    self.bump();
                    if self.peek() == '\n' {
                        self.bump();
                    }
                    self.push(kind::NEWLINE, start, self.pos, true);
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
                '=' if self.at_line_start(start) && self.starts_pod(start) => self.pod(start),
                '_' if self.at_line_start(start) && self.starts_data_section(start) => {
                    self.data_section(start)
                }
                '"' => self.string(start, '"'),
                '\'' => self.string(start, '\''),
                '`' => self.string(start, '`'),
                '<' => {
                    if let Some((end, id, squiggly)) = self.try_heredoc(start) {
                        self.pos = end;
                        self.push(kind::HEREDOC_OPEN, start, end, false);
                        self.pending.push(PendingHeredoc { id, squiggly });
                    } else {
                        self.punct(start);
                    }
                }
                '/' => {
                    if self.prev_value_end {
                        self.punct(start); // division / `/=` / defined-or `//`
                    } else {
                        self.regex(start);
                    }
                }
                '$' => self.variable(start, kind::SCALAR_VAR),
                '@' => {
                    if self.var_follows('@') {
                        self.variable(start, kind::ARRAY_VAR);
                    } else {
                        self.punct(start);
                    }
                }
                '%' => {
                    if !self.prev_value_end && self.var_follows('%') {
                        self.variable(start, kind::HASH_VAR);
                    } else {
                        self.punct(start);
                    }
                }
                '&' => {
                    if !self.prev_value_end && self.var_follows('&') {
                        self.variable(start, kind::AMP_VAR);
                    } else {
                        self.punct(start);
                    }
                }
                '*' => {
                    if !self.prev_value_end && self.var_follows('*') {
                        self.variable(start, kind::GLOB_VAR);
                    } else {
                        self.punct(start);
                    }
                }
                c if is_ident_start(c) => {
                    if !self.prev_value_end && self.quote_like(start) {
                        // handled as a quote-like literal token
                    } else {
                        self.name(start);
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

            // Progress guard: if a branch failed to advance, consume one byte as an
            // error token rather than spin. Non-advancing == infinite loop == OOM.
            if self.pos == start {
                self.bump();
                self.push(kind::ERROR, start, self.pos, false);
            }
        }
        self.tokens
    }

    // --- identifiers / variables -------------------------------------------

    fn name(&mut self, start: usize) {
        self.eat_while(is_ident_continue);
        self.eat_pkg_tail();
        self.push(kind::IDENT, start, self.pos, false);
    }

    /// Absorb a `::ident` (or `::ident::ident…`) package tail, so `Foo::Bar::baz`
    /// is one identifier token.
    fn eat_pkg_tail(&mut self) {
        loop {
            if self.src[self.pos..].starts_with("::") {
                let after = self.src[self.pos + 2..].chars().next();
                if matches!(after, Some(c) if is_ident_start(c)) {
                    self.pos += 2;
                    self.eat_while(is_ident_continue);
                    continue;
                }
            }
            break;
        }
    }

    /// Whether the char after a sigil makes it a variable (vs an operator). `$`/`@`
    /// special punctuation variables are recognized broadly; `%`/`&`/`*` only take
    /// a name-like or block continuation.
    fn var_follows(&self, sigil: char) -> bool {
        match self.peek_at(1) {
            None => false,
            Some(c) => {
                if is_ident_start(c) || c == '{' || c == '$' || c.is_ascii_digit() {
                    return true;
                }
                match sigil {
                    '$' => c.is_ascii_punctuation(),
                    '@' => matches!(c, '-' | '+'),
                    _ => false,
                }
            }
        }
    }

    /// Scan a sigil variable. Handles deref sigils (`$$ref`, `@$r`), `$#array`
    /// (last index), `${...}`/`@{...}` blocks, `::`-qualified names, numeric
    /// captures (`$1`), caret vars (`$^W`), and single-char special vars (`$!`,
    /// `$_`, `$"`, `` $` ``, `$/`, …). Always advances at least the sigil.
    fn variable(&mut self, start: usize, kind: &'static str) {
        self.bump(); // sigil
                     // Deref sigils: `$$ref`, `@$r`, also the PID `$$`.
        while self.peek() == '$' {
            self.bump();
        }
        // `$#array` / `$#{...}` / `$#$ref` last-index form.
        if kind == kind::SCALAR_VAR
            && self.peek() == '#'
            && matches!(self.peek_at(1), Some(c) if is_ident_start(c) || c == '{' || c == '$')
        {
            self.bump(); // '#'
        }
        match self.peek() {
            '{' => self.consume_braces(),
            c if is_ident_start(c) => {
                self.eat_while(is_ident_continue);
                self.eat_pkg_tail();
            }
            c if c.is_ascii_digit() => {
                self.eat_while(|c| c.is_ascii_digit());
            }
            '^' => {
                self.bump();
                if is_ident_start(self.peek()) {
                    self.bump();
                }
            }
            c if c != '\0' && !c.is_whitespace() && c.is_ascii_punctuation() => {
                // A single-char special variable: `$!`, `$@`, `$"`, `` $` ``, `$/`, …
                self.bump();
            }
            _ => {}
        }
        self.push(kind, start, self.pos, false);
    }

    /// Consume a balanced `{ … }` run (used for `${ … }` / `@{ … }` blocks).
    fn consume_braces(&mut self) {
        self.bump(); // {
        let mut depth = 1usize;
        while self.pos < self.bytes.len() && depth > 0 {
            match self.peek() {
                '{' => depth += 1,
                '}' => depth -= 1,
                _ => {}
            }
            self.bump();
        }
    }

    // --- strings ------------------------------------------------------------

    /// Scan a quoted string for `quote` (`"`, `'`, or `` ` ``). A backslash escapes
    /// the next byte; newlines are allowed inside (Perl strings may span lines).
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
            self.eat_while(|c| c.is_ascii_alphabetic()); // trailing flags
            self.push(kind::REGEX, start, self.pos, false);
        } else {
            self.push(kind::ERROR, start, self.pos, false);
        }
    }

    // --- quote-like operators ----------------------------------------------

    /// Try to lex a quote-like literal (`q()`, `qq{}`, `qw//`, `qr{}x`, `qx``,
    /// `m//`, `s///`, `tr///`, `y///`) at `start`. Returns `true` (and pushes one
    /// token) when recognized; `false` to fall back to a bareword. Only the
    /// *immediately adjacent* delimiter form is accepted (no `q (x)`).
    fn quote_like(&mut self, start: usize) -> bool {
        let rest = &self.src[start..];
        let op = match QUOTE_OPS.iter().copied().find(|op| {
            rest.starts_with(op)
                && match rest[op.len()..].chars().next() {
                    Some(c) => !is_ident_continue(c),
                    None => false,
                }
        }) {
            Some(o) => o,
            None => return false,
        };

        let two_part = matches!(op, "tr" | "s" | "y");
        let regexish = matches!(op, "m" | "qr" | "s" | "tr" | "y");
        let has_flags = regexish;

        let dpos = start + op.len();
        let delim = match self.src[dpos..].chars().next() {
            Some(c) => c,
            None => return false,
        };
        if !valid_open_delim(delim) {
            return false;
        }
        let close = matching_delim(delim);
        let nests = delim != close;

        let after = dpos + delim.len_utf8();
        let mut end = self.scan_quote_section(after, delim, close, nests);

        if two_part {
            if nests {
                // s{a}{b}: skip whitespace, then a fresh opening delimiter.
                let mut q = end;
                while q < self.bytes.len() {
                    let ch = self.src[q..].chars().next().unwrap_or('\0');
                    if ch.is_whitespace() {
                        q += ch.len_utf8();
                    } else {
                        break;
                    }
                }
                if let Some(open2) = self.src[q..].chars().next() {
                    if valid_open_delim(open2) {
                        let close2 = matching_delim(open2);
                        let nests2 = open2 != close2;
                        end = self.scan_quote_section(q + open2.len_utf8(), open2, close2, nests2);
                    }
                }
            } else {
                // s/a/b/: the closing delim of part one opens part two.
                end = self.scan_quote_section(end, delim, close, false);
            }
        }

        if has_flags {
            while end < self.bytes.len() {
                let ch = self.src[end..].chars().next().unwrap_or('\0');
                if ch.is_ascii_alphabetic() {
                    end += 1;
                } else {
                    break;
                }
            }
        }

        let k = if regexish { kind::REGEX } else { kind::STRING };
        self.pos = end;
        self.push(k, start, end, false);
        true
    }

    /// Scan one delimited section, the opener already consumed, returning the
    /// offset just past the matching close delimiter (or EOF if unterminated).
    fn scan_quote_section(&self, from: usize, open: char, close: char, nests: bool) -> usize {
        let mut q = from;
        let mut depth = 1i32;
        while q < self.bytes.len() {
            let ch = self.src[q..].chars().next().unwrap_or('\0');
            if ch == '\\' {
                q += 1;
                if q < self.bytes.len() {
                    q += self.char_len_at(q);
                }
                continue;
            }
            if nests && ch == open {
                depth += 1;
                q += ch.len_utf8();
                continue;
            }
            if ch == close {
                depth -= 1;
                q += ch.len_utf8();
                if depth == 0 {
                    break;
                }
                continue;
            }
            q += ch.len_utf8();
        }
        q
    }

    // --- heredocs -----------------------------------------------------------

    /// Detect a heredoc opener at `start` (cursor on the first `<`). Supports
    /// `<<~ID`, `<<"ID"`, `<<'ID'`, `` <<`ID` ``, and a bare `<<ID` (only at a
    /// value-begin position, so `$x << 2` stays a shift). Returns
    /// `(end_of_opener, identifier, squiggly)` or `None`.
    fn try_heredoc(&self, start: usize) -> Option<(usize, String, bool)> {
        if self.peek_at(1) != Some('<') {
            return None; // not `<<`
        }
        let mut p = start + 2;
        let squiggly = self.byte_at(p) == Some(b'~');
        if squiggly {
            p += 1;
        }
        let quote = match self.byte_at(p) {
            Some(b'"') => Some(b'"'),
            Some(b'\'') => Some(b'\''),
            Some(b'`') => Some(b'`'),
            _ => None,
        };
        if quote.is_some() {
            p += 1;
        }
        // A bare `<<ID` is ambiguous with left-shift; only accept it at a
        // value-begin position (or when squiggly / quoted).
        if !squiggly && quote.is_none() && self.prev_value_end {
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
        Some((p, id, squiggly))
    }

    /// At a newline, consume every pending heredoc body in FIFO order. Each body
    /// runs to (and including) its terminator line; EOF first ⇒ body extends to
    /// EOF. Either way the bytes stay in the tree.
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
                let candidate = if h.squiggly {
                    line.trim_start_matches([' ', '\t'])
                } else {
                    line
                };
                let candidate = candidate.trim_end_matches(['\n', '\r']);
                if candidate == h.id {
                    body_end = line_end;
                    break;
                }
                line_start = line_end;
            }
            self.pos = body_end;
            self.push(kind::HEREDOC_BODY, body_start, body_end, false);
        }
    }

    // --- POD / __END__ ------------------------------------------------------

    /// A line beginning with `=` followed by an ASCII letter starts POD.
    fn starts_pod(&self, start: usize) -> bool {
        matches!(self.byte_at(start + 1), Some(b) if (b as char).is_ascii_alphabetic())
    }

    /// Consume `=word` … `=cut` (inclusive) as one POD trivia token; runs to EOF if
    /// `=cut` never appears.
    fn pod(&mut self, start: usize) {
        let mut line_start = start;
        let end;
        loop {
            let line_end = match self.src[line_start..].find('\n') {
                Some(i) => line_start + i + 1,
                None => self.bytes.len(),
            };
            let line = &self.src[line_start..line_end];
            if let Some(tail) = line.strip_prefix("=cut") {
                let after = tail.chars().next();
                if matches!(
                    after,
                    None | Some(' ') | Some('\t') | Some('\n') | Some('\r')
                ) {
                    end = line_end;
                    break;
                }
            }
            if line_end >= self.bytes.len() {
                end = self.bytes.len();
                break;
            }
            line_start = line_end;
        }
        self.pos = end;
        self.push(kind::POD, start, end, true);
    }

    /// `__END__` / `__DATA__` as a whole line begins a trailing section that runs
    /// verbatim to EOF.
    fn starts_data_section(&self, start: usize) -> bool {
        let rest = &self.src[start..];
        for marker in ["__END__", "__DATA__"] {
            if let Some(tail) = rest.strip_prefix(marker) {
                let after = tail.chars().next();
                if matches!(
                    after,
                    None | Some(' ') | Some('\t') | Some('\n') | Some('\r')
                ) {
                    return true;
                }
            }
        }
        false
    }

    fn data_section(&mut self, start: usize) {
        self.pos = self.bytes.len();
        self.push(kind::DATA_SECTION, start, self.pos, true);
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
                Some('b') | Some('B') => {
                    self.pos += 2;
                    self.eat_while(|c| c == '0' || c == '1' || c == '_');
                    return self.push(kind::INT, start, self.pos, false);
                }
                Some('o') | Some('O') => {
                    self.pos += 2;
                    self.eat_while(|c| ('0'..='7').contains(&c) || c == '_');
                    return self.push(kind::INT, start, self.pos, false);
                }
                _ => {}
            }
        }
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        if self.peek() == '.' && self.peek_at(1).map(|c| c.is_ascii_digit()).unwrap_or(false) {
            is_float = true;
            self.bump();
            self.eat_while(|c| c.is_ascii_digit() || c == '_');
        } else if self.peek() == '.' && self.peek_at(1) != Some('.') {
            // A trailing dot (e.g. a leading `.5` was routed here): keep `..` ranges
            // intact, but a lone `1.` is still a float.
            is_float = true;
            self.bump();
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

    fn char_len_at(&self, idx: usize) -> usize {
        self.src[idx..]
            .chars()
            .next()
            .map(|c| c.len_utf8())
            .unwrap_or(1)
    }

    fn at_line_start(&self, pos: usize) -> bool {
        pos == 0 || self.bytes.get(pos - 1) == Some(&b'\n')
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

    /// Whether the token just produced ends a value. Trivia never changes the bit.
    fn compute_value_end(&self, kind: &'static str, start: usize, end: usize) -> bool {
        match kind {
            kind::IDENT => {
                let text = self.src.get(start..end).unwrap_or("");
                word_ends_value(text)
            }
            kind::SCALAR_VAR
            | kind::ARRAY_VAR
            | kind::HASH_VAR
            | kind::AMP_VAR
            | kind::GLOB_VAR
            | kind::INT
            | kind::FLOAT
            | kind::STRING
            | kind::REGEX
            | kind::HEREDOC_OPEN
            | kind::HEREDOC_BODY => true,
            // `)`/`]`/`}` end a value; `->` is marked value-ending so a method name
            // after it (e.g. `$obj->s`, `$obj->m`) is a plain identifier, never a
            // quote-like operator or regex.
            kind::PUNCT => matches!(
                self.src.get(start..end),
                Some(")") | Some("]") | Some("}") | Some("->")
            ),
            _ => false,
        }
    }
}

fn valid_open_delim(c: char) -> bool {
    !c.is_whitespace() && !c.is_alphanumeric() && c != '=' && !matches!(c, ')' | ']' | '}' | '>')
}

fn matching_delim(open: char) -> char {
    match open {
        '(' => ')',
        '[' => ']',
        '{' => '}',
        '<' => '>',
        other => other,
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
            "sub add { my ($a, $b) = @_; return $a + $b; }\n",
            "my @list = qw(a b c);\nmy %h = (x => 1);\n",
            "my $re = qr/ab+c/i;\n$str =~ s/foo/bar/g;\ntr/a-z/A-Z/;\n",
            "my $q = qq{hi $name}; my $w = q(raw); my $x = `ls -l`;\n",
            "my $doc = <<~SQL;\n  select 1\n  SQL\nprint $doc;\n",
            "=pod\nthis is documentation\n=cut\nmy $x = 1;\n",
            "my $c = $a / $b;\nmy $d = /regex/;\n",
            "package Geo::Point;\nour $VERSION = '1.0';\n",
            "my $pid = $$; my $self = $$ref; my @args = @_;\n",
            "print $/, $\\, $!, $\", $0, $1;\n",
            "λ = 'unicode ☃ €';  # comment\n",
            "my $h = { a => 1, b => sub { 2 } };\n",
            "1 while $x < 10;\nmy $v = $x // 5;\n",
            "__END__\nthis is the data section\nverbatim\n",
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
        let t = texts("sub add { return $a + $b; }\n");
        assert!(t.contains(&(kind::IDENT, "sub".to_string())));
        assert!(t.contains(&(kind::IDENT, "add".to_string())));
        assert!(t.contains(&(kind::SCALAR_VAR, "$a".to_string())));
        assert!(t.contains(&(kind::PUNCT, "{".to_string())));
        assert!(is_keyword("sub"));
        assert!(is_keyword("my"));
        assert!(!is_keyword("add"));
    }

    #[test]
    fn sigils_classify() {
        let t = texts("my $s = 1; my @a = (); my %h = (); my $r = \\&foo;\n");
        assert!(t.contains(&(kind::SCALAR_VAR, "$s".to_string())));
        assert!(t.contains(&(kind::ARRAY_VAR, "@a".to_string())));
        assert!(t.contains(&(kind::HASH_VAR, "%h".to_string())));
        assert!(t.contains(&(kind::AMP_VAR, "&foo".to_string())));
    }

    #[test]
    fn modulo_vs_hash_disambiguation() {
        // After a value, `%` is modulo; at a value-begin position it is a hash.
        let t = texts("my $r = $count % 2;\nmy %config = ();\n");
        assert!(t.contains(&(kind::PUNCT, "%".to_string())));
        assert!(t.contains(&(kind::HASH_VAR, "%config".to_string())));
    }

    #[test]
    fn regex_vs_division() {
        let t = texts("my $a = $x / $y;\n$s =~ /pat/;\n");
        assert!(t.contains(&(kind::PUNCT, "/".to_string())));
        assert!(t.iter().any(|(k, s)| *k == kind::REGEX && s == "/pat/"));
    }

    #[test]
    fn quote_like_operators() {
        let t = texts("my @w = qw(a b c);\nmy $q = q{raw};\n$x =~ s{a}{b}g;\ntr/a/b/;\n");
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::STRING && s == "qw(a b c)"));
        assert!(t.iter().any(|(k, s)| *k == kind::STRING && s == "q{raw}"));
        assert!(t.iter().any(|(k, s)| *k == kind::REGEX && s == "s{a}{b}g"));
        assert!(t.iter().any(|(k, s)| *k == kind::REGEX && s == "tr/a/b/"));
    }

    #[test]
    fn quote_like_not_misfired_on_barewords() {
        // `sort`, `system`, `map`, `s => 1` must not become quote-likes.
        let t = texts("my @x = sort @y;\nmy %h = (s => 1, y => 2);\nsystem('ls');\n");
        assert!(t.contains(&(kind::IDENT, "sort".to_string())));
        assert!(t.contains(&(kind::IDENT, "system".to_string())));
        assert!(t.contains(&(kind::IDENT, "s".to_string())));
        assert!(t.contains(&(kind::IDENT, "y".to_string())));
    }

    #[test]
    fn heredoc_body_is_one_token() {
        let t = texts("my $d = <<~SQL;\n  select 1\n  SQL\nmy $x = 1;\n");
        assert!(t.iter().any(|(k, _)| *k == kind::HEREDOC_OPEN));
        assert!(t
            .iter()
            .any(|(k, s)| *k == kind::HEREDOC_BODY && s.contains("select 1") && s.contains("SQL")));
    }

    #[test]
    fn two_heredocs_on_one_line() {
        let src = "func(<<A, <<B);\naaa\nA\nbbb\nB\n";
        let bodies: Vec<String> = lex(src)
            .into_iter()
            .filter(|t| t.kind == kind::HEREDOC_BODY)
            .map(|t| t.span.text(src).to_string())
            .collect();
        assert_eq!(bodies.len(), 2);
        assert!(bodies[0].contains("aaa") && bodies[0].contains("A"));
        assert!(bodies[1].contains("bbb") && bodies[1].contains("B"));
        assert!(covers_all(src));
    }

    #[test]
    fn shift_is_not_a_heredoc() {
        // `$x << 2` after a value must stay a shift operator.
        let t = texts("my $r = $x << 2;\n");
        assert!(t.contains(&(kind::PUNCT, "<<".to_string())));
        assert!(!t.iter().any(|(k, _)| *k == kind::HEREDOC_OPEN));
    }

    #[test]
    fn pod_and_data_are_trivia() {
        let src = "=head1 NAME\n\nFoo - a thing\n\n=cut\nmy $x = 1;\n__END__\nraw data\n";
        let toks = lex(src);
        assert!(toks.iter().any(|t| t.kind == kind::POD && t.trivia));
        assert!(toks
            .iter()
            .any(|t| t.kind == kind::DATA_SECTION && t.trivia));
        assert!(covers_all(src));
    }

    #[test]
    fn numbers() {
        let t = texts("my $a = 0xFF; my $b = 0b1010; my $c = 3.14; my $d = 1_000; my $e = 2e10;\n");
        assert!(t.contains(&(kind::INT, "0xFF".to_string())));
        assert!(t.contains(&(kind::INT, "0b1010".to_string())));
        assert!(t.contains(&(kind::FLOAT, "3.14".to_string())));
        assert!(t.contains(&(kind::INT, "1_000".to_string())));
        assert!(t.contains(&(kind::FLOAT, "2e10".to_string())));
    }

    #[test]
    fn unterminated_string_is_error_but_lossless() {
        let t = texts("my $s = \"oops\n");
        assert!(t.iter().any(|(k, _)| *k == kind::ERROR));
        assert!(covers_all("my $s = \"oops\n"));
    }

    #[test]
    fn never_spins_on_odd_input() {
        // Lone sigils, stray delimiters, raw bytes — must all terminate.
        for src in [
            "$", "@", "%", "&", "*", "\\", "::", "<<", "q", "s", "~~~", "\x07\x08",
        ] {
            assert!(covers_all(src), "not contiguous: {src:?}");
        }
    }
}
