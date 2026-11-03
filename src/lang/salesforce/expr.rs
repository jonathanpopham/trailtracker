//! A std-only expression parser for the Salesforce expression language (TT-85).
//!
//! Salesforce formulas (formula fields, validation-rule `errorConditionFormula`,
//! default values) and Flow condition/assignment expressions all share one small
//! surface language: literals, field/relationship references, `$`-system global
//! variables, function application (`ISBLANK`, `TEXT`, `IF`, `AND`, …), and a
//! handful of infix/prefix operators with C-like precedence. TT-64
//! ([`super::formula`]) only *scans* such a string for the names it references.
//! This module parses it into a real [`Expr`] AST — the reusable expression layer
//! the Workflow IR (decision 0002) and the deepened formula edges will consume.
//!
//! Design guarantees, mirroring the rest of TrailTracker:
//! - **std-only, no deps.** A hand-written lexer + precedence-climbing parser.
//! - **Never panics.** Anything unparseable becomes an [`Expr::Opaque`] carrying
//!   the exact source slice; malformed input yields whatever was recovered.
//! - **Always terminates.** The lexer only advances; the parser consumes at least
//!   one token per operator iteration and the token stream is finite.
//! - **Deterministic.** [`Expr::refs`] / [`Expr::system_refs`] return sorted
//!   `BTreeSet`s and [`Display`](std::fmt::Display) renders a canonical string.
//!
//! [`Expr::refs`] is a deliberate **superset** of TT-64's `refs`: it yields the
//! head of every field/dotted reference (excluding function names, literals, and
//! `$`-system refs), so this parser can eventually replace [`super::formula`].

use crate::core::json::Json;
use std::collections::BTreeSet;
use std::fmt;

/// A leaf literal value.
#[derive(Clone, Debug, PartialEq)]
pub enum Lit {
    /// A quoted string literal, stored **decoded** (escapes resolved).
    String(String),
    /// A numeric literal.
    Number(f64),
    /// `TRUE` / `FALSE` (case-insensitive).
    Bool(bool),
    /// `NULL` (case-insensitive).
    Null,
}

/// Prefix (unary) operators.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    /// Arithmetic negation: `-x`.
    Neg,
    /// Logical negation: `!x`, `NOT x`.
    Not,
}

/// Infix (binary) operators, in the language's precedence groups.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    /// `||` (also spelled `OR(...)` as a call).
    Or,
    /// `&&` (also spelled `AND(...)` as a call).
    And,
    /// `=` / `==`.
    Eq,
    /// `!=` / `<>`.
    Ne,
    /// `<`.
    Lt,
    /// `<=`.
    Le,
    /// `>`.
    Gt,
    /// `>=`.
    Ge,
    /// `+`.
    Add,
    /// `-`.
    Sub,
    /// `*`.
    Mul,
    /// `/`.
    Div,
}

/// A parsed Salesforce expression.
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    /// A literal value.
    Literal(Lit),
    /// A field / relationship reference as a dotted path, e.g.
    /// `Contact.Owner.Name` → `["Contact", "Owner", "Name"]`. A bare field is a
    /// one-element path.
    Ref(Vec<String>),
    /// A `$`-prefixed global reference, full path kept (`$Permission.Bypass`).
    SystemRef(String),
    /// A prefix operator applied to an operand.
    Unary(UnOp, Box<Expr>),
    /// An infix operator applied to two operands.
    Binary(BinOp, Box<Expr>, Box<Expr>),
    /// Function application: `NAME(arg, …)`. The name is kept verbatim.
    Call(String, Vec<Expr>),
    /// Unparseable input, preserving the exact source slice so nothing is lost.
    Opaque(String),
}

impl BinOp {
    /// The canonical source spelling used by [`Display`](std::fmt::Display).
    fn symbol(self) -> &'static str {
        match self {
            BinOp::Or => "||",
            BinOp::And => "&&",
            BinOp::Eq => "==",
            BinOp::Ne => "!=",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
        }
    }
}

impl UnOp {
    fn symbol(self) -> &'static str {
        match self {
            UnOp::Neg => "-",
            UnOp::Not => "!",
        }
    }
}

/// Parse a Salesforce formula / flow-condition expression into an [`Expr`].
///
/// Never panics and always terminates. Unrecognized constructs collapse to
/// [`Expr::Opaque`] carrying the offending source text; an empty or all-garbage
/// input yields an `Opaque` too.
pub fn parse_expression(input: &str) -> Expr {
    let tokens = lex(input);
    let mut parser = Parser {
        toks: tokens,
        pos: 0,
    };
    if parser.toks.is_empty() {
        return Expr::Opaque(input.trim().to_string());
    }
    parser.parse_or()
}

impl Expr {
    /// Every field / dotted-reference **head** in the expression, sorted and
    /// de-duplicated. Function names, literals, and `$`-system refs are excluded.
    /// A superset of TT-64's `refs`.
    pub fn refs(&self) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        self.collect_refs(&mut out);
        out
    }

    /// Every `$`-system reference (full path), sorted and de-duplicated.
    pub fn system_refs(&self) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        self.collect_system_refs(&mut out);
        out
    }

    fn collect_refs(&self, out: &mut BTreeSet<String>) {
        match self {
            Expr::Ref(path) => {
                if let Some(head) = path.first() {
                    out.insert(head.clone());
                }
            }
            Expr::Unary(_, inner) => inner.collect_refs(out),
            Expr::Binary(_, l, r) => {
                l.collect_refs(out);
                r.collect_refs(out);
            }
            Expr::Call(_, args) => {
                for a in args {
                    a.collect_refs(out);
                }
            }
            Expr::Literal(_) | Expr::SystemRef(_) | Expr::Opaque(_) => {}
        }
    }

    fn collect_system_refs(&self, out: &mut BTreeSet<String>) {
        match self {
            Expr::SystemRef(name) => {
                out.insert(name.clone());
            }
            Expr::Unary(_, inner) => inner.collect_system_refs(out),
            Expr::Binary(_, l, r) => {
                l.collect_system_refs(out);
                r.collect_system_refs(out);
            }
            Expr::Call(_, args) => {
                for a in args {
                    a.collect_system_refs(out);
                }
            }
            Expr::Literal(_) | Expr::Ref(_) | Expr::Opaque(_) => {}
        }
    }

    /// A structured JSON rendering of the AST, for the IR serializer. Deterministic.
    pub fn to_json(&self) -> Json {
        match self {
            Expr::Literal(lit) => {
                let value = match lit {
                    Lit::String(s) => Json::str(s.clone()),
                    Lit::Number(n) => Json::F64(*n),
                    Lit::Bool(b) => Json::Bool(*b),
                    Lit::Null => Json::Null,
                };
                Json::obj([("kind", Json::str("literal")), ("value", value)])
            }
            Expr::Ref(path) => Json::obj([
                ("kind", Json::str("ref")),
                (
                    "path",
                    Json::Array(path.iter().map(|s| Json::str(s.clone())).collect()),
                ),
            ]),
            Expr::SystemRef(name) => Json::obj([
                ("kind", Json::str("systemRef")),
                ("name", Json::str(name.clone())),
            ]),
            Expr::Unary(op, inner) => Json::obj([
                ("kind", Json::str("unary")),
                ("op", Json::str(op.symbol())),
                ("operand", inner.to_json()),
            ]),
            Expr::Binary(op, l, r) => Json::obj([
                ("kind", Json::str("binary")),
                ("op", Json::str(op.symbol())),
                ("left", l.to_json()),
                ("right", r.to_json()),
            ]),
            Expr::Call(name, args) => Json::obj([
                ("kind", Json::str("call")),
                ("name", Json::str(name.clone())),
                (
                    "args",
                    Json::Array(args.iter().map(|a| a.to_json()).collect()),
                ),
            ]),
            Expr::Opaque(text) => Json::obj([
                ("kind", Json::str("opaque")),
                ("text", Json::str(text.clone())),
            ]),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Literal(Lit::String(s)) => {
                f.write_str("'")?;
                for c in s.chars() {
                    match c {
                        '\\' => f.write_str("\\\\")?,
                        '\'' => f.write_str("\\'")?,
                        c => f.write_fmt(format_args!("{c}"))?,
                    }
                }
                f.write_str("'")
            }
            Expr::Literal(Lit::Number(n)) => write!(f, "{n}"),
            Expr::Literal(Lit::Bool(true)) => f.write_str("TRUE"),
            Expr::Literal(Lit::Bool(false)) => f.write_str("FALSE"),
            Expr::Literal(Lit::Null) => f.write_str("NULL"),
            Expr::Ref(path) => f.write_str(&path.join(".")),
            Expr::SystemRef(name) => f.write_str(name),
            Expr::Unary(op, inner) => write!(f, "({}{})", op.symbol(), inner),
            Expr::Binary(op, l, r) => write!(f, "({} {} {})", l, op.symbol(), r),
            Expr::Call(name, args) => {
                write!(f, "{name}(")?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{a}")?;
                }
                f.write_str(")")
            }
            Expr::Opaque(text) => write!(f, "«{text}»"),
        }
    }
}

// ---------------------------------------------------------------------------
// Lexer
// ---------------------------------------------------------------------------

/// Operator symbols recognized by the lexer, before precedence is applied.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Sym {
    OrOr,
    AndAnd,
    EqEq,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Plus,
    Minus,
    Star,
    Slash,
    Bang,
}

/// A lexical token. Each carries its exact source `text` so [`Expr::Opaque`] can
/// reproduce the original slice verbatim.
#[derive(Clone, Debug)]
enum TokKind {
    /// Dotted identifier path, e.g. `Contact.Owner.Name`.
    Word(Vec<String>),
    /// `$`-prefixed system reference, full path.
    System(String),
    /// String literal, already decoded.
    Str(String),
    /// Numeric literal.
    Num(f64),
    /// An operator symbol.
    Op(Sym),
    LParen,
    RParen,
    Comma,
    /// Any single character the lexer did not recognize.
    Unknown,
}

#[derive(Clone, Debug)]
struct Tok {
    kind: TokKind,
    text: String,
}

fn is_ident_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

fn is_ident_part(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

/// Tokenize an expression. Only ever advances, so it always terminates.
fn lex(input: &str) -> Vec<Tok> {
    let chars: Vec<char> = input.chars().collect();
    let n = chars.len();
    let mut i = 0usize;
    let mut out: Vec<Tok> = Vec::new();

    while i < n {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
        } else if c == '\'' || c == '"' {
            let (tok, next) = lex_string(&chars, i);
            out.push(tok);
            i = next;
        } else if c == '$' {
            let start = i;
            i += 1;
            while i < n && is_ident_part(chars[i]) {
                i += 1;
            }
            i = consume_dotted_tail(&chars, i);
            let text: String = chars[start..i].iter().collect();
            out.push(Tok {
                kind: TokKind::System(text.clone()),
                text,
            });
        } else if is_ident_start(c) {
            let start = i;
            i += 1;
            while i < n && is_ident_part(chars[i]) {
                i += 1;
            }
            let mut path = vec![chars[start..i].iter().collect::<String>()];
            // Consume `.segment` continuations, but only when the dot is truly
            // followed by an identifier (so a trailing dot stays punctuation).
            while i + 1 < n && chars[i] == '.' && is_ident_start(chars[i + 1]) {
                i += 1; // dot
                let seg_start = i;
                i += 1;
                while i < n && is_ident_part(chars[i]) {
                    i += 1;
                }
                path.push(chars[seg_start..i].iter().collect());
            }
            let text: String = chars[start..i].iter().collect();
            out.push(Tok {
                kind: TokKind::Word(path),
                text,
            });
        } else if c.is_ascii_digit() {
            let start = i;
            i += 1;
            while i < n && chars[i].is_ascii_digit() {
                i += 1;
            }
            if i + 1 < n && chars[i] == '.' && chars[i + 1].is_ascii_digit() {
                i += 1; // dot
                while i < n && chars[i].is_ascii_digit() {
                    i += 1;
                }
            }
            let text: String = chars[start..i].iter().collect();
            let value = text.parse::<f64>().unwrap_or(0.0);
            out.push(Tok {
                kind: TokKind::Num(value),
                text,
            });
        } else if let Some((sym, len)) = lex_operator(&chars, i) {
            let text: String = chars[i..i + len].iter().collect();
            out.push(Tok {
                kind: TokKind::Op(sym),
                text,
            });
            i += len;
        } else if c == '(' {
            out.push(Tok {
                kind: TokKind::LParen,
                text: "(".to_string(),
            });
            i += 1;
        } else if c == ')' {
            out.push(Tok {
                kind: TokKind::RParen,
                text: ")".to_string(),
            });
            i += 1;
        } else if c == ',' {
            out.push(Tok {
                kind: TokKind::Comma,
                text: ",".to_string(),
            });
            i += 1;
        } else {
            out.push(Tok {
                kind: TokKind::Unknown,
                text: c.to_string(),
            });
            i += 1;
        }
    }

    out
}

/// Lex a string literal beginning at the opening quote `chars[start]`. Honors
/// backslash escapes; an unterminated literal is consumed to end-of-input.
fn lex_string(chars: &[char], start: usize) -> (Tok, usize) {
    let n = chars.len();
    let quote = chars[start];
    let mut i = start + 1;
    let mut value = String::new();
    while i < n {
        let c = chars[i];
        if c == '\\' && i + 1 < n {
            value.push(chars[i + 1]);
            i += 2;
            continue;
        }
        if c == quote {
            i += 1;
            break;
        }
        value.push(c);
        i += 1;
    }
    let text: String = chars[start..i].iter().collect();
    (
        Tok {
            kind: TokKind::Str(value),
            text,
        },
        i,
    )
}

/// Match an operator at `chars[i]`, returning its symbol and length. Two-char
/// operators are tried before their one-char prefixes.
fn lex_operator(chars: &[char], i: usize) -> Option<(Sym, usize)> {
    let c = chars[i];
    let d = chars.get(i + 1).copied();
    match (c, d) {
        ('|', Some('|')) => Some((Sym::OrOr, 2)),
        ('&', Some('&')) => Some((Sym::AndAnd, 2)),
        ('=', Some('=')) => Some((Sym::EqEq, 2)),
        ('!', Some('=')) => Some((Sym::Ne, 2)),
        ('<', Some('>')) => Some((Sym::Ne, 2)),
        ('<', Some('=')) => Some((Sym::Le, 2)),
        ('>', Some('=')) => Some((Sym::Ge, 2)),
        ('=', _) => Some((Sym::Eq, 1)),
        ('<', _) => Some((Sym::Lt, 1)),
        ('>', _) => Some((Sym::Gt, 1)),
        ('+', _) => Some((Sym::Plus, 1)),
        ('-', _) => Some((Sym::Minus, 1)),
        ('*', _) => Some((Sym::Star, 1)),
        ('/', _) => Some((Sym::Slash, 1)),
        ('!', _) => Some((Sym::Bang, 1)),
        _ => None,
    }
}

/// Consume any `.<ident>` continuation starting at (or before) `i`, tolerating
/// whitespace. Bounded by input length, so it terminates.
fn consume_dotted_tail(chars: &[char], mut i: usize) -> usize {
    let n = chars.len();
    loop {
        let mut j = i;
        while j < n && chars[j].is_whitespace() {
            j += 1;
        }
        if j < n && chars[j] == '.' {
            j += 1;
            while j < n && chars[j].is_whitespace() {
                j += 1;
            }
            if j < n && is_ident_start(chars[j]) {
                j += 1;
                while j < n && is_ident_part(chars[j]) {
                    j += 1;
                }
                i = j;
                continue;
            }
        }
        break;
    }
    i
}

// ---------------------------------------------------------------------------
// Parser (precedence climbing)
// ---------------------------------------------------------------------------

struct Parser {
    toks: Vec<Tok>,
    pos: usize,
}

impl Parser {
    fn peek(&self) -> Option<&TokKind> {
        self.toks.get(self.pos).map(|t| &t.kind)
    }

    /// `expr := or`. `||` binds loosest.
    fn parse_or(&mut self) -> Expr {
        let mut left = self.parse_and();
        while matches!(self.peek(), Some(TokKind::Op(Sym::OrOr))) {
            self.pos += 1;
            let right = self.parse_and();
            left = Expr::Binary(BinOp::Or, Box::new(left), Box::new(right));
        }
        left
    }

    fn parse_and(&mut self) -> Expr {
        let mut left = self.parse_cmp();
        while matches!(self.peek(), Some(TokKind::Op(Sym::AndAnd))) {
            self.pos += 1;
            let right = self.parse_cmp();
            left = Expr::Binary(BinOp::And, Box::new(left), Box::new(right));
        }
        left
    }

    fn parse_cmp(&mut self) -> Expr {
        let mut left = self.parse_add();
        while let Some(op) = self.peek().and_then(cmp_op) {
            self.pos += 1;
            let right = self.parse_add();
            left = Expr::Binary(op, Box::new(left), Box::new(right));
        }
        left
    }

    fn parse_add(&mut self) -> Expr {
        let mut left = self.parse_mul();
        while let Some(op) = self.peek().and_then(add_op) {
            self.pos += 1;
            let right = self.parse_mul();
            left = Expr::Binary(op, Box::new(left), Box::new(right));
        }
        left
    }

    fn parse_mul(&mut self) -> Expr {
        let mut left = self.parse_unary();
        while let Some(op) = self.peek().and_then(mul_op) {
            self.pos += 1;
            let right = self.parse_unary();
            left = Expr::Binary(op, Box::new(left), Box::new(right));
        }
        left
    }

    fn parse_unary(&mut self) -> Expr {
        match self.peek() {
            Some(TokKind::Op(Sym::Minus)) => {
                self.pos += 1;
                Expr::Unary(UnOp::Neg, Box::new(self.parse_unary()))
            }
            Some(TokKind::Op(Sym::Bang)) => {
                self.pos += 1;
                Expr::Unary(UnOp::Not, Box::new(self.parse_unary()))
            }
            // Bare `NOT x` (not followed by `(`, which would be a `NOT(...)` call).
            Some(TokKind::Word(path))
                if path.len() == 1
                    && path[0].eq_ignore_ascii_case("NOT")
                    && !matches!(
                        self.toks.get(self.pos + 1).map(|t| &t.kind),
                        Some(TokKind::LParen)
                    ) =>
            {
                self.pos += 1;
                Expr::Unary(UnOp::Not, Box::new(self.parse_unary()))
            }
            _ => self.parse_primary(),
        }
    }

    fn parse_primary(&mut self) -> Expr {
        let kind = match self.peek() {
            Some(k) => k.clone(),
            // Nothing left to consume: an empty operand.
            None => return Expr::Opaque(String::new()),
        };
        match kind {
            TokKind::Str(s) => {
                self.pos += 1;
                Expr::Literal(Lit::String(s))
            }
            TokKind::Num(n) => {
                self.pos += 1;
                Expr::Literal(Lit::Number(n))
            }
            TokKind::System(name) => {
                self.pos += 1;
                Expr::SystemRef(name)
            }
            TokKind::LParen => {
                self.pos += 1;
                let inner = self.parse_or();
                // Tolerate a missing close paren rather than failing.
                if matches!(self.peek(), Some(TokKind::RParen)) {
                    self.pos += 1;
                }
                inner
            }
            TokKind::Word(path) => {
                self.pos += 1;
                if path.len() == 1 {
                    let word = &path[0];
                    if word.eq_ignore_ascii_case("TRUE") {
                        return Expr::Literal(Lit::Bool(true));
                    }
                    if word.eq_ignore_ascii_case("FALSE") {
                        return Expr::Literal(Lit::Bool(false));
                    }
                    if word.eq_ignore_ascii_case("NULL") {
                        return Expr::Literal(Lit::Null);
                    }
                    if matches!(self.peek(), Some(TokKind::LParen)) {
                        return self.parse_call(word.clone());
                    }
                }
                Expr::Ref(path)
            }
            // Operators, stray punctuation, and unknowns are not valid operands.
            // Consume the one offending token so callers make progress.
            TokKind::Op(_) | TokKind::RParen | TokKind::Comma | TokKind::Unknown => {
                let text = self.toks[self.pos].text.clone();
                self.pos += 1;
                Expr::Opaque(text)
            }
        }
    }

    /// Parse `(arg, arg, …)` for a call whose head `name` was already consumed.
    /// Assumes the current token is the opening `(`.
    fn parse_call(&mut self, name: String) -> Expr {
        self.pos += 1; // consume '('
        let mut args = Vec::new();
        loop {
            match self.peek() {
                None => break,
                Some(TokKind::RParen) => {
                    self.pos += 1;
                    break;
                }
                Some(TokKind::Comma) => {
                    // Skip stray/empty argument separators defensively.
                    self.pos += 1;
                }
                Some(_) => {
                    let before = self.pos;
                    args.push(self.parse_or());
                    // Guarantee progress even if an argument consumed nothing.
                    if self.pos == before {
                        self.pos += 1;
                    }
                }
            }
        }
        Expr::Call(name, args)
    }
}

fn cmp_op(kind: &TokKind) -> Option<BinOp> {
    match kind {
        TokKind::Op(Sym::EqEq) | TokKind::Op(Sym::Eq) => Some(BinOp::Eq),
        TokKind::Op(Sym::Ne) => Some(BinOp::Ne),
        TokKind::Op(Sym::Lt) => Some(BinOp::Lt),
        TokKind::Op(Sym::Le) => Some(BinOp::Le),
        TokKind::Op(Sym::Gt) => Some(BinOp::Gt),
        TokKind::Op(Sym::Ge) => Some(BinOp::Ge),
        _ => None,
    }
}

fn add_op(kind: &TokKind) -> Option<BinOp> {
    match kind {
        TokKind::Op(Sym::Plus) => Some(BinOp::Add),
        TokKind::Op(Sym::Minus) => Some(BinOp::Sub),
        _ => None,
    }
}

fn mul_op(kind: &TokKind) -> Option<BinOp> {
    match kind {
        TokKind::Op(Sym::Star) => Some(BinOp::Mul),
        TokKind::Op(Sym::Slash) => Some(BinOp::Div),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn refs(input: &str) -> Vec<String> {
        parse_expression(input).refs().into_iter().collect()
    }

    fn system_refs(input: &str) -> Vec<String> {
        parse_expression(input).system_refs().into_iter().collect()
    }

    #[test]
    fn parses_literals() {
        assert_eq!(parse_expression("42"), Expr::Literal(Lit::Number(42.0)));
        assert_eq!(parse_expression("2.5"), Expr::Literal(Lit::Number(2.5)));
        assert_eq!(
            parse_expression("'hello'"),
            Expr::Literal(Lit::String("hello".to_string()))
        );
        assert_eq!(parse_expression("TRUE"), Expr::Literal(Lit::Bool(true)));
        assert_eq!(parse_expression("false"), Expr::Literal(Lit::Bool(false)));
        assert_eq!(parse_expression("NULL"), Expr::Literal(Lit::Null));
    }

    #[test]
    fn string_escapes_are_decoded() {
        assert_eq!(
            parse_expression(r"'it\'s'"),
            Expr::Literal(Lit::String("it's".to_string()))
        );
    }

    #[test]
    fn parses_bare_and_dotted_refs() {
        assert_eq!(
            parse_expression("Amount__c"),
            Expr::Ref(vec!["Amount__c".to_string()])
        );
        assert_eq!(
            parse_expression("Contact.Owner.Name"),
            Expr::Ref(vec![
                "Contact".to_string(),
                "Owner".to_string(),
                "Name".to_string()
            ])
        );
        // The ref head is what surfaces in refs().
        assert_eq!(refs("Contact.Owner.Name"), vec!["Contact".to_string()]);
    }

    #[test]
    fn parses_system_refs() {
        assert_eq!(
            parse_expression("$Permission.Bypass"),
            Expr::SystemRef("$Permission.Bypass".to_string())
        );
        assert_eq!(
            system_refs("$Permission.Bypass"),
            vec!["$Permission.Bypass".to_string()]
        );
        // A system ref is never counted as a field ref.
        assert!(refs("$Permission.Bypass").is_empty());
    }

    #[test]
    fn parses_function_calls() {
        let e = parse_expression("ISBLANK(TEXT(Severity__c))");
        assert_eq!(
            e,
            Expr::Call(
                "ISBLANK".to_string(),
                vec![Expr::Call(
                    "TEXT".to_string(),
                    vec![Expr::Ref(vec!["Severity__c".to_string()])]
                )]
            )
        );
        // Function names are not refs; the argument field is.
        assert_eq!(
            refs("ISBLANK(TEXT(Severity__c))"),
            vec!["Severity__c".to_string()]
        );
    }

    #[test]
    fn multi_arg_call() {
        let e = parse_expression("IF(A__c > 1, B__c, C__c)");
        match e {
            Expr::Call(name, args) => {
                assert_eq!(name, "IF");
                assert_eq!(args.len(), 3);
            }
            other => panic!("expected call, got {other:?}"),
        }
        assert_eq!(
            refs("IF(A__c > 1, B__c, C__c)"),
            vec!["A__c".to_string(), "B__c".to_string(), "C__c".to_string()]
        );
    }

    #[test]
    fn precedence_and_binds_tighter_than_or() {
        // a && b || c  ==>  (a && b) || c
        let e = parse_expression("a && b || c");
        assert_eq!(e.to_string(), "((a && b) || c)");
        assert!(matches!(e, Expr::Binary(BinOp::Or, _, _)));
    }

    #[test]
    fn precedence_or_then_and() {
        // a || b && c  ==>  a || (b && c)
        let e = parse_expression("a || b && c");
        assert_eq!(e.to_string(), "(a || (b && c))");
    }

    #[test]
    fn precedence_arithmetic_over_comparison() {
        // a + b * c < d  ==>  (a + (b * c)) < d
        let e = parse_expression("a + b * c < d");
        assert_eq!(e.to_string(), "((a + (b * c)) < d)");
    }

    #[test]
    fn comparison_operator_spellings() {
        for (src, op) in [
            ("a = b", BinOp::Eq),
            ("a == b", BinOp::Eq),
            ("a != b", BinOp::Ne),
            ("a <> b", BinOp::Ne),
            ("a < b", BinOp::Lt),
            ("a <= b", BinOp::Le),
            ("a > b", BinOp::Gt),
            ("a >= b", BinOp::Ge),
        ] {
            match parse_expression(src) {
                Expr::Binary(got, _, _) => assert_eq!(got, op, "for {src}"),
                other => panic!("expected binary for {src}, got {other:?}"),
            }
        }
    }

    #[test]
    fn unary_neg_and_not() {
        assert_eq!(
            parse_expression("-Amount__c"),
            Expr::Unary(
                UnOp::Neg,
                Box::new(Expr::Ref(vec!["Amount__c".to_string()]))
            )
        );
        assert_eq!(
            parse_expression("NOT IsActive__c"),
            Expr::Unary(
                UnOp::Not,
                Box::new(Expr::Ref(vec!["IsActive__c".to_string()]))
            )
        );
        assert_eq!(
            parse_expression("!IsActive__c"),
            Expr::Unary(
                UnOp::Not,
                Box::new(Expr::Ref(vec!["IsActive__c".to_string()]))
            )
        );
    }

    #[test]
    fn not_with_parens_is_a_call() {
        assert!(matches!(
            parse_expression("NOT($Permission.Bypass)"),
            Expr::Call(ref name, _) if name == "NOT"
        ));
    }

    #[test]
    fn parentheses_override_precedence() {
        // (a || b) && c  ==>  the && is the root
        let e = parse_expression("(a || b) && c");
        assert!(matches!(e, Expr::Binary(BinOp::And, _, _)));
        assert_eq!(e.to_string(), "((a || b) && c)");
    }

    #[test]
    fn canonical_refs_and_system_refs_on_the_sforg_formula() {
        let e = parse_expression("ISBLANK(TEXT(Severity__c)) && NOT($Permission.Bypass)");
        assert_eq!(
            e.refs().into_iter().collect::<Vec<_>>(),
            vec!["Severity__c".to_string()]
        );
        assert_eq!(
            e.system_refs().into_iter().collect::<Vec<_>>(),
            vec!["$Permission.Bypass".to_string()]
        );
    }

    #[test]
    fn refs_superset_matches_formula_scanner_shape() {
        // Bare fields and dotted heads collected; literals/functions excluded.
        assert_eq!(
            refs("Amount__c > 2.5 && Name = 'ISBLANK(not a call)'"),
            vec!["Amount__c".to_string(), "Name".to_string()]
        );
        // TRUE / NULL never leak into refs.
        assert_eq!(
            refs("IsActive__c = TRUE || Other__c = NULL"),
            vec!["IsActive__c".to_string(), "Other__c".to_string()]
        );
    }

    #[test]
    fn multiple_system_refs_deduped_and_sorted() {
        assert_eq!(
            system_refs("$User.Id <> $User.Id && $Setup.MyCS__c.Flag__c"),
            vec!["$Setup.MyCS__c.Flag__c".to_string(), "$User.Id".to_string()]
        );
    }

    #[test]
    fn display_round_trips_structurally() {
        // Display renders a fully parenthesized, re-parseable string.
        let src = "AND(NOT(ISBLANK(Patient__c)), Status__c = 'Open')";
        let e = parse_expression(src);
        let rendered = e.to_string();
        let reparsed = parse_expression(&rendered);
        assert_eq!(reparsed.refs(), e.refs());
    }

    #[test]
    fn to_json_is_structured() {
        let j = parse_expression("A__c && B__c").to_json();
        let line = j.to_line();
        assert!(line.contains("\"kind\":\"binary\""));
        assert!(line.contains("\"op\":\"&&\""));
    }

    #[test]
    fn does_not_panic_on_garbage() {
        for src in [
            "",
            "   ",
            "$",
            "$$$.$.",
            "'unterminated string",
            "\"also unterminated",
            "Field__c.",
            ".",
            "...",
            "((((",
            "))))",
            "))(( &&",
            "&& || ++ -- == != <= >=",
            "1.2.3.4.5",
            "A.B.C.",
            "ISBLANK(",
            "IF(,,)",
            "日本語 && Field__c",
            "\\\\\\",
            "A(",
            "NOT",
            "- - -",
        ] {
            // Contract is only "no panic and terminates".
            let e = parse_expression(src);
            // refs()/system_refs() must also never panic.
            let _ = e.refs();
            let _ = e.system_refs();
            let _ = e.to_string();
            let _ = e.to_json().to_line();
        }
    }

    #[test]
    fn garbage_becomes_opaque_not_empty_panic() {
        // Leading garbage surfaces as an Opaque node carrying the raw slice.
        assert!(matches!(parse_expression(")"), Expr::Opaque(_)));
        assert!(matches!(parse_expression(""), Expr::Opaque(_)));
    }
}
