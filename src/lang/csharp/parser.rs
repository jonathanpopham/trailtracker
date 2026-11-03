//! C# parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust and Python parsers
//! ([`crate::lang::rust::parser`], [`crate::lang::python::parser`]): declaration
//! *headers* are parsed precisely — we always know a method's name and parameter
//! list, a type's name and base list, a `using` path — while bodies and
//! expression regions are captured as balanced **token-tree groups**
//! (`Paren`/`Bracket`/`Brace`), which are perfectly lossless. Graph facts (calls,
//! type refs, base lists) are extracted from these real tokens in the lowering
//! pass, never invented.
//!
//! C# is brace-delimited like Rust, so the shape follows the Rust parser closely.
//! The one wrinkle is that C# *members* (methods, fields, properties) carry no
//! leading keyword: they are `<modifiers> <type> <name> …`. The parser collects a
//! member header up to the first structural decider (`(`-led parameter list, `{`
//! property body, `=>` expression body, `=` initializer, `;`, or `:` base/ctor
//! initializer) and classifies the member by whether that header ends in a
//! parameter list. Namespaces (block and file-scoped), nested types, and type
//! bodies are recursively parsed as item lists so nested definitions stay
//! first-class.
//!
//! Anything unrecognized still lands in the tree as its exact tokens (a
//! `Statement`/`ErrorItem` node or a flat token run), so the result always
//! round-trips byte-for-byte. The recursion is depth-guarded at [`MAX_DEPTH`]
//! against hostile nesting, because a `catch_unwind` cannot catch a stack
//! overflow.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::csharp::lexer::{is_keyword, kind as tk, lex};

/// CST node-kind labels. The lowering interprets these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const USING: &str = "Using";
    pub const NAMESPACE: &str = "Namespace";
    pub const CLASS: &str = "Class";
    pub const STRUCT: &str = "Struct";
    pub const INTERFACE: &str = "Interface";
    pub const ENUM: &str = "Enum";
    pub const RECORD: &str = "Record";
    pub const DELEGATE: &str = "Delegate";
    pub const METHOD: &str = "Method";
    pub const FIELD: &str = "Field";
    pub const PROPERTY: &str = "Property";
    pub const STATEMENT: &str = "Statement";
    pub const ERROR_ITEM: &str = "ErrorItem";

    pub const NAME: &str = "Name";
    pub const HEADER: &str = "Header";
    pub const BASE_INIT: &str = "BaseInit";
    pub const INIT: &str = "Init";
    pub const ATTR_LIST: &str = "AttrList";
    pub const ITEM_BLOCK: &str = "ItemBlock";
    pub const ENUM_BODY: &str = "EnumBody";
    pub const BLOCK: &str = "Block";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Declaration modifiers consumed before the declaration keyword. Disjoint from
/// the type/declaration keywords so dispatch stays unambiguous. `event`,
/// `operator`, `implicit`, `explicit` are deliberately *not* here — they are left
/// for the member header so the member classifier sees them.
const MODIFIERS: &[&str] = &[
    "public",
    "private",
    "protected",
    "internal",
    "static",
    "abstract",
    "sealed",
    "virtual",
    "override",
    "readonly",
    "const",
    "new",
    "async",
    "partial",
    "extern",
    "unsafe",
    "volatile",
    "fixed",
    "required",
    "file",
    "ref",
];

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat run. Protects against stack overflow on pathological or
/// hostile inputs (deeply nested delimiters) — mirrors the Rust/Python guard
/// exactly, since a `catch_unwind` cannot catch a stack overflow.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = CSharpParser {
        src: source,
        toks,
        i: 0,
        diags: Vec::new(),
        depth: 0,
    };
    let root = p.parse_source_file();
    ParseTree {
        source_id: SourceId::from_path(path),
        path: path.to_string(),
        source: source.to_string(),
        root,
        diagnostics: p.diags,
    }
}

struct CSharpParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl CSharpParser<'_> {
    // --- cursor primitives --------------------------------------------------

    /// Append the current token (trivia or not) to `out` and advance.
    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading trivia tokens into `out`.
    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
        }
    }

    /// Kind of the n-th significant token from the cursor (no source borrow).
    fn peek_kind_n(&self, n: usize) -> Option<&'static str> {
        let mut j = self.i;
        let mut count = 0;
        while j < self.toks.len() {
            if self.toks[j].trivia {
                j += 1;
                continue;
            }
            if count == n {
                return Some(self.toks[j].kind);
            }
            count += 1;
            j += 1;
        }
        None
    }

    fn peek_kind(&self) -> Option<&'static str> {
        self.peek_kind_n(0)
    }

    /// Text of the n-th significant token from the cursor.
    fn peek_n_text(&self, n: usize) -> Option<&str> {
        let mut j = self.i;
        let mut count = 0;
        while j < self.toks.len() {
            if self.toks[j].trivia {
                j += 1;
                continue;
            }
            if count == n {
                return Some(self.toks[j].span.text(self.src));
            }
            count += 1;
            j += 1;
        }
        None
    }

    fn at(&self, s: &str) -> bool {
        self.peek_n_text(0) == Some(s)
    }

    fn at_n(&self, n: usize, s: &str) -> bool {
        self.peek_n_text(n) == Some(s)
    }

    fn at_ident(&self) -> bool {
        self.peek_kind() == Some(tk::IDENT)
    }

    fn at_open(&self) -> bool {
        self.at("(") || self.at("[") || self.at("{")
    }

    fn at_modifier(&self) -> bool {
        matches!(self.peek_n_text(0), Some(t) if MODIFIERS.contains(&t))
    }

    /// `record` introduces a type only when followed by an identifier (the record
    /// name) or by `class`/`struct` — otherwise it is an ordinary identifier.
    fn record_is_decl(&self) -> bool {
        matches!(self.peek_kind_n(1), Some(k) if k == tk::IDENT)
    }

    fn cur_offset(&self) -> usize {
        self.toks
            .get(self.i)
            .map(|t| t.span.start as usize)
            .unwrap_or(self.src.len())
    }

    fn make_node(&self, kind: &'static str, children: Vec<Child>) -> Node {
        let span =
            children_span(&children).unwrap_or_else(|| ByteSpan::empty_at(self.cur_offset()));
        Node::new(kind, span, children)
    }

    // --- top level ----------------------------------------------------------

    fn parse_source_file(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            let item = self.parse_item(false);
            c.push(Child::Node(item));
        }
        self.make_node(node::SOURCE_FILE, c)
    }

    /// Parse `{ items }` as a recursive item list. `in_type` selects member vs
    /// top-level dispatch for the contained items.
    fn parse_item_block(&mut self, label: &'static str, in_type: bool) -> Node {
        // Depth guard: beyond the cap, stop recursing and consume the body as a
        // flat balanced token run. Lossless, never a stack overflow.
        if self.depth >= MAX_DEPTH {
            let mut c = Vec::new();
            self.ws(&mut c);
            self.eat(&mut c); // {
            self.consume_balanced_flat(&mut c);
            self.note_depth_limit();
            return self.make_node(label, c);
        }
        self.depth += 1;
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // {
        loop {
            self.ws(&mut c);
            match self.peek_kind() {
                None => break,
                Some(_) if self.at("}") => {
                    self.eat(&mut c);
                    break;
                }
                Some(_) => {
                    let item = self.parse_item(in_type);
                    c.push(Child::Node(item));
                }
            }
        }
        let node = self.make_node(label, c);
        self.depth -= 1;
        node
    }

    // --- items --------------------------------------------------------------

    fn parse_item(&mut self, in_type: bool) -> Node {
        let mut c = Vec::new();

        // Attribute lists: `[Attr]` `[Attr(args)]`.
        loop {
            self.ws(&mut c);
            if self.at("[") {
                let a = self.parse_delimited(Some(node::ATTR_LIST));
                c.push(Child::Node(a));
            } else {
                break;
            }
        }

        // Declaration modifiers.
        loop {
            self.ws(&mut c);
            if self.at_modifier() {
                self.eat(&mut c);
            } else {
                break;
            }
        }

        // Dispatch on the declaration keyword.
        self.ws(&mut c);
        if !in_type && (self.at("using") || (self.at("global") && self.at_n(1, "using"))) {
            self.finish_using(c)
        } else if !in_type && self.at("namespace") {
            self.finish_namespace(c)
        } else if self.at("class") {
            self.finish_type_decl(c, node::CLASS)
        } else if self.at("struct") {
            self.finish_type_decl(c, node::STRUCT)
        } else if self.at("interface") {
            self.finish_type_decl(c, node::INTERFACE)
        } else if self.at("enum") {
            self.finish_enum(c)
        } else if self.at("record") && self.record_is_decl() {
            self.finish_record(c)
        } else if self.at("delegate") {
            self.finish_delegate(c)
        } else if in_type {
            self.finish_member(c)
        } else {
            self.finish_statement(c)
        }
    }

    fn finish_using(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        if self.at("global") {
            self.eat(&mut c); // global
            self.ws(&mut c);
        }
        self.eat(&mut c); // using
        self.ws(&mut c);
        if self.at("static") {
            self.eat(&mut c); // static
        }
        if let Some(body) = self.collect_region(node::HEADER, &[";"]) {
            c.push(Child::Node(body));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::USING, c)
    }

    fn finish_namespace(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // namespace
                          // Dotted name (`A.B.C`) up to the body or the file-scoped `;`.
        if let Some(name) = self.collect_dotted_name() {
            c.push(Child::Node(name));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_item_block(node::ITEM_BLOCK, false);
            c.push(Child::Node(b));
        } else if self.at(";") {
            // File-scoped namespace: every following item belongs to it.
            self.eat(&mut c); // ;
            let mut body = Vec::new();
            loop {
                self.ws(&mut body);
                if self.peek_kind().is_none() {
                    break;
                }
                let item = self.parse_item(false);
                body.push(Child::Node(item));
            }
            if !body.is_empty() {
                let block = self.make_node(node::ITEM_BLOCK, body);
                c.push(Child::Node(block));
            }
        }
        self.make_node(node::NAMESPACE, c)
    }

    fn finish_type_decl(&mut self, mut c: Vec<Child>, kind: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // class/struct/interface
        self.ws(&mut c);
        if self.at_ident() {
            c.push(Child::Node(self.name_node()));
        }
        if let Some(h) = self.collect_region(node::HEADER, &["{", ";"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_item_block(node::ITEM_BLOCK, true);
            c.push(Child::Node(b));
        } else if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(kind, c)
    }

    fn finish_enum(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // enum
        self.ws(&mut c);
        if self.at_ident() {
            c.push(Child::Node(self.name_node()));
        }
        // Optional underlying type: `: byte`.
        if let Some(h) = self.collect_region(node::HEADER, &["{", ";"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_delimited(Some(node::ENUM_BODY));
            c.push(Child::Node(b));
        } else if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::ENUM, c)
    }

    fn finish_record(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // record
        self.ws(&mut c);
        if self.at("class") || self.at("struct") {
            self.eat(&mut c); // record class / record struct
            self.ws(&mut c);
        }
        if self.at_ident() {
            c.push(Child::Node(self.name_node()));
        }
        // Header captures the primary-constructor parameter list and base list.
        if let Some(h) = self.collect_region(node::HEADER, &["{", ";"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_item_block(node::ITEM_BLOCK, true);
            c.push(Child::Node(b));
        } else if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::RECORD, c)
    }

    fn finish_delegate(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // delegate
        if let Some(h) = self.collect_region(node::HEADER, &[";"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::DELEGATE, c)
    }

    /// A type member with no leading keyword: method, constructor, field, or
    /// property. Classified by whether the header ends in a parameter list.
    fn finish_member(&mut self, mut c: Vec<Child>) -> Node {
        let header = self.collect_region(node::HEADER, &["{", "=>", "=", ";", ":"]);
        let is_method = header
            .as_ref()
            .map(|h| header_is_method(h, self.src))
            .unwrap_or(false);
        if let Some(h) = header {
            c.push(Child::Node(h));
        }

        // Constructor initializer / unexpected base: `: base(x)` / `: this(y)`.
        self.ws(&mut c);
        if self.at(":") {
            if let Some(b) = self.collect_region(node::BASE_INIT, &["{", ";"]) {
                c.push(Child::Node(b));
            }
        }

        self.ws(&mut c);
        let kind = if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
            // Auto-property / field-like initializer after the body: `= expr;`.
            self.ws(&mut c);
            if self.at("=") {
                if let Some(init) = self.collect_region(node::INIT, &[";"]) {
                    c.push(Child::Node(init));
                }
                self.ws(&mut c);
                if self.at(";") {
                    self.eat(&mut c);
                }
            }
            if is_method {
                node::METHOD
            } else {
                node::PROPERTY
            }
        } else if self.at("=>") {
            // Expression-bodied member; captured as a Block so calls are found.
            if let Some(b) = self.collect_region(node::BLOCK, &[";"]) {
                c.push(Child::Node(b));
            }
            self.ws(&mut c);
            if self.at(";") {
                self.eat(&mut c);
            }
            if is_method {
                node::METHOD
            } else {
                node::PROPERTY
            }
        } else if self.at("=") {
            if let Some(init) = self.collect_region(node::INIT, &[";"]) {
                c.push(Child::Node(init));
            }
            self.ws(&mut c);
            if self.at(";") {
                self.eat(&mut c);
            }
            if is_method {
                node::METHOD
            } else {
                node::FIELD
            }
        } else {
            if self.at(";") {
                self.eat(&mut c);
            }
            if is_method {
                node::METHOD
            } else {
                node::FIELD
            }
        };

        // Defensive: guarantee progress even on input we could not classify.
        if c.iter().all(is_trivia_child) {
            self.eat(&mut c);
            self.diags.push(Diagnostic {
                code: "csharp.unrecognized_member",
                message: "token(s) not recognized as a C# member".to_string(),
                span: children_span(&c).unwrap_or_else(|| ByteSpan::empty_at(self.cur_offset())),
            });
            return self.make_node(node::ERROR_ITEM, c);
        }
        self.make_node(kind, c)
    }

    /// A top-level statement (C# 9 top-level programs) or stray tokens outside a
    /// type. Consumed to the next logical end so nothing is dropped.
    fn finish_statement(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        if self.at_open() {
            let g = self.parse_delimited(None);
            c.push(Child::Node(g));
        } else if self.at("}") {
            // Stray closer: consume one token to guarantee progress.
            self.eat(&mut c);
        } else {
            // Collect up to and including the next depth-0 `;`, descending into
            // groups; stop (without eating) at a `}` that closes an outer scope.
            loop {
                self.ws(&mut c);
                match self.peek_kind() {
                    None => break,
                    Some(_) if self.at(";") => {
                        self.eat(&mut c);
                        break;
                    }
                    Some(_) if self.at("}") => break,
                    Some(_) if self.at_open() => {
                        let g = self.parse_delimited(None);
                        c.push(Child::Node(g));
                    }
                    Some(_) => self.eat(&mut c),
                }
            }
        }
        // Guarantee progress.
        if c.iter().all(is_trivia_child) {
            self.eat(&mut c);
        }
        self.make_node(node::STATEMENT, c)
    }

    // --- shared helpers -----------------------------------------------------

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.eat(&mut c); // the identifier (cursor is at it after caller ws)
        self.make_node(node::NAME, c)
    }

    /// Collect a dotted namespace name (`A . B . C`) up to the body `{` or the
    /// file-scoped `;`, as a `Name` node.
    fn collect_dotted_name(&mut self) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            match self.peek_kind() {
                None => break,
                _ if self.at("{") || self.at(";") || self.at("}") => break,
                _ => self.eat(&mut c),
            }
        }
        if c.iter().all(is_trivia_child) {
            // Push back trivia we consumed so it stays with the parent (it is
            // already in `c`); return it wrapped only if it has content.
            if c.is_empty() {
                return None;
            }
        }
        Some(self.make_node(node::NAME, c))
    }

    /// Collect tokens (descending into balanced groups) until a significant stop
    /// token at delimiter depth 0. Leading/trailing trivia around a stop stays
    /// with the parent. Returns `None` if nothing significant was collected.
    fn collect_region(&mut self, label: &'static str, stops: &[&str]) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            if self.peek_kind().is_none() {
                break;
            }
            // A `}` always closes an enclosing block (it should have been parsed
            // via `parse_delimited`), so never consume it as flat header content.
            if self.at("}") || stops.iter().any(|s| self.at(s)) {
                break;
            }
            if self.at_open() {
                self.ws(&mut c);
                let inner = self.parse_delimited(None);
                c.push(Child::Node(inner));
            } else {
                self.ws(&mut c);
                self.eat(&mut c);
            }
        }
        // `c` is empty exactly when the cursor began at a stop (the stop checks
        // skip trivia, so no trivia is consumed in that case); otherwise every
        // consumed trivia run is paired with the significant token it precedes, so
        // returning `None` here never drops bytes.
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(label, c))
        }
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`. Cursor is at
    /// (or before trivia preceding) the opener.
    fn parse_delimited(&mut self, label_override: Option<&'static str>) -> Node {
        let mut g = Vec::new();
        self.ws(&mut g);
        let (close, default_label) = if self.at("(") {
            (")", node::PAREN)
        } else if self.at("[") {
            ("]", node::BRACKET)
        } else if self.at("{") {
            ("}", node::BRACE)
        } else {
            // Defensive: not actually at an opener.
            return self.make_node(label_override.unwrap_or(node::ERROR_ITEM), g);
        };
        let label = label_override.unwrap_or(default_label);
        self.eat(&mut g); // opener
        loop {
            self.ws(&mut g);
            if self.peek_kind().is_none() {
                break; // unterminated; still lossless
            }
            if self.at(close) {
                self.eat(&mut g);
                break;
            }
            if self.at_open() {
                if self.depth < MAX_DEPTH {
                    self.depth += 1;
                    let inner = self.parse_delimited(None);
                    self.depth -= 1;
                    g.push(Child::Node(inner));
                } else {
                    // Depth cap: flatten the nested group rather than recursing.
                    self.eat(&mut g); // opener
                    self.consume_balanced_flat(&mut g);
                    self.note_depth_limit();
                }
            } else {
                self.eat(&mut g);
            }
        }
        self.make_node(label, g)
    }

    /// Iteratively consume a balanced delimiter run (the opener already eaten),
    /// appending every token as a flat leaf. Used at the depth cap so arbitrarily
    /// deep nesting is handled without further recursion.
    fn consume_balanced_flat(&mut self, out: &mut Vec<Child>) {
        let mut balance: i32 = 1;
        while balance > 0 {
            self.ws(out);
            match self.peek_n_text(0) {
                None => break,
                Some("(") | Some("[") | Some("{") => balance += 1,
                Some(")") | Some("]") | Some("}") => balance -= 1,
                _ => {}
            }
            self.eat(out);
        }
    }

    /// Record (once per truncation is enough) that the depth cap flattened
    /// structure — reported, never silent.
    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "csharp.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; group flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }
}

/// True if a member header denotes a method/constructor rather than a
/// field/property. The signal is the *parameter list*: the last direct `Paren`
/// group whose immediately preceding significant element (skipping a trailing
/// generic `<…>` clause) is a non-keyword identifier — the method name.
///
/// This holds for plain methods (`int Foo()`), generic methods even with trailing
/// `where` constraints (`T Foo<T>() where …`), tuple-return methods
/// (`(int,int) Swap()`), and explicit-interface methods (`int IFoo.Bar()`),
/// while a tuple-typed field (`(int,int) p;`) is correctly *not* a method because
/// its paren is the type and is followed (not preceded) by the name.
fn header_is_method(header: &Node, src: &str) -> bool {
    let children = &header.children;
    let mut paren_idx = None;
    for (i, ch) in children.iter().enumerate() {
        if let Child::Node(n) = ch {
            if n.kind == node::PAREN {
                paren_idx = Some(i);
            }
        }
    }
    let pi = match paren_idx {
        Some(i) => i,
        None => return false,
    };
    // Scan backwards from just before the parameter list, skipping any generic
    // argument clause (`<…>`) by angle-bracket balancing.
    let mut angle: i32 = 0;
    for ch in children[..pi].iter().rev() {
        match ch {
            Child::Token(t) if t.trivia => continue,
            Child::Token(t) => {
                let text = t.span.text(src);
                let opens = text.matches('>').count() as i32; // backward: `>` opens
                let closes = text.matches('<').count() as i32;
                if angle == 0 && opens == 0 && closes == 0 {
                    return t.kind == tk::IDENT && !is_keyword(text);
                }
                angle += opens - closes;
                if angle < 0 {
                    angle = 0;
                }
            }
            Child::Node(_) => {
                if angle == 0 {
                    return false; // a group (e.g. tuple type) directly before the paren
                }
            }
        }
    }
    false
}

fn is_trivia_child(c: &Child) -> bool {
    matches!(c, Child::Token(t) if t.trivia)
}

fn children_span(children: &[Child]) -> Option<ByteSpan> {
    let mut it = children.iter().map(child_span);
    let first = it.next()?;
    Some(it.fold(first, |a, b| a.merge(b)))
}

fn child_span(c: &Child) -> ByteSpan {
    match c {
        Child::Node(n) => n.span,
        Child::Token(t) => t.span,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kinds_of(root: &Node) -> Vec<&'static str> {
        root.child_nodes().map(|n| n.kind).collect()
    }

    #[test]
    fn parses_and_is_lossless() {
        let src = "\
// a file
using System;
using System.Collections.Generic;

namespace App.Core
{
    public interface IGreeter { string Greet(string name); }

    public class Greeter : IGreeter
    {
        private readonly string _prefix = \"Hello\";
        public int Count { get; set; }

        public Greeter(string prefix) : base()
        {
            _prefix = prefix;
        }

        public string Greet(string name) => $\"{_prefix}, {name}!\";

        public void Run()
        {
            var msg = Greet(\"world\");
            Console.WriteLine(msg);
        }
    }

    public enum Color { Red, Green = 2, Blue }

    public record Point(int X, int Y);
}
";
        let tree = parse("Greeter.cs", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "using System; namespace N { class C { void M() {} int f; } enum E { A } }";
        let tree = parse("t.cs", src);
        let top = kinds_of(&tree.root);
        assert!(top.contains(&node::USING), "using not found: {top:?}");
        assert!(
            top.contains(&node::NAMESPACE),
            "namespace not found: {top:?}"
        );

        let ns = tree.root.child(node::NAMESPACE).unwrap();
        let body = ns.child(node::ITEM_BLOCK).unwrap();
        let members = kinds_of(body);
        assert!(
            members.contains(&node::CLASS),
            "class not found: {members:?}"
        );
        assert!(members.contains(&node::ENUM), "enum not found: {members:?}");

        let class = body.child(node::CLASS).unwrap();
        let cbody = class.child(node::ITEM_BLOCK).unwrap();
        let cmembers = kinds_of(cbody);
        assert!(cmembers.contains(&node::METHOD), "method: {cmembers:?}");
        assert!(cmembers.contains(&node::FIELD), "field: {cmembers:?}");
    }

    #[test]
    fn classifies_method_field_property() {
        let src = "class C { int M(int x) { return x; } int F = 1; int P { get; set; } }";
        let tree = parse("t.cs", src);
        let class = tree.root.child(node::CLASS).unwrap();
        let body = class.child(node::ITEM_BLOCK).unwrap();
        let ks = kinds_of(body);
        assert_eq!(
            ks,
            vec![node::METHOD, node::FIELD, node::PROPERTY],
            "member classification"
        );
    }

    #[test]
    fn tuple_return_is_still_a_method() {
        let src = "class C { (int, int) Swap(int a, int b) { return (b, a); } }";
        let tree = parse("t.cs", src);
        let body = tree
            .root
            .child(node::CLASS)
            .unwrap()
            .child(node::ITEM_BLOCK)
            .unwrap();
        assert_eq!(kinds_of(body), vec![node::METHOD]);
        assert!(tree.is_lossless());
    }

    #[test]
    fn file_scoped_namespace_nests_items() {
        let src = "namespace A.B;\n\nclass C { }\nclass D { }\n";
        let tree = parse("t.cs", src);
        let ns = tree.root.child(node::NAMESPACE).expect("namespace");
        let body = ns.child(node::ITEM_BLOCK).expect("file-scoped body");
        let ks = kinds_of(body);
        assert_eq!(ks, vec![node::CLASS, node::CLASS]);
        assert!(tree.is_lossless());
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let depth = 10_000;
        let src = format!(
            "class C {{ void M() {{ {}{} }} }}",
            "(".repeat(depth),
            ")".repeat(depth)
        );
        let tree = parse("deep.cs", &src);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics
                .iter()
                .any(|d| d.code == "csharp.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }

    #[test]
    fn edge_inputs_round_trip() {
        for src in [
            "",                                           // empty
            "   \n\t  ",                                  // only trivia
            "class C { void M() { var s = $\"{a}\"; } }", // interpolation
            "class C { string s = @\"a\"\"b\"; }",        // verbatim string
            "#region X\nclass C {}\n#endregion",          // preprocessor trivia
            "class C { void M() { x = (1, 2;",            // unterminated paren
            "λ ☃ €",                                      // non-ascii error tokens
            "Console.WriteLine(\"hi\");",                 // top-level statement
        ] {
            let tree = parse("edge.cs", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }

    #[test]
    fn output_is_deterministic() {
        let src = "namespace N { class C : B { void M() { f(); } } }";
        let a = parse("t.cs", src);
        let b = parse("t.cs", src);
        assert_eq!(a.to_json().to_line(), b.to_json().to_line());
    }

    #[test]
    fn generic_method_with_constraints_is_a_method() {
        let src = "class C { T Wrap<T>(T x) where T : class { return x; } }";
        let tree = parse("t.cs", src);
        let body = tree
            .root
            .child(node::CLASS)
            .unwrap()
            .child(node::ITEM_BLOCK)
            .unwrap();
        assert_eq!(kinds_of(body), vec![node::METHOD]);
        assert!(tree.is_lossless());
    }
}
