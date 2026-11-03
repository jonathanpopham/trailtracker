//! TypeScript / TSX parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust and Python parsers: item *headers* are parsed
//! precisely — we always know a function's name, a class's `extends`/`implements`
//! clause, an `import` specifier, a decorator — while expression regions and
//! bodies are captured as balanced **token-tree groups** (`Paren`/`Bracket`/
//! `Brace`) plus flat tokens, which is perfectly lossless. Graph facts (calls,
//! type refs, base types) are extracted from these real tokens in the lowering
//! pass, never invented.
//!
//! TypeScript blocks are brace-delimited (unlike Python's indentation), so the
//! shape is closest to the Rust parser: `class`, `interface`, and `namespace`
//! bodies are parsed recursively as member/item lists so nested definitions stay
//! first-class, while everything else is captured as token trees.
//!
//! ASI (automatic semicolon insertion) means statements do not always end in
//! `;`. Rather than model ASI, a generic statement is bounded by the next
//! top-level `;`, the enclosing `}`, or the start of a new declaration keyword —
//! so a declaration is never swallowed into a preceding expression statement.
//!
//! Anything unrecognized still lands in the tree as its exact tokens, so the
//! result always round-trips byte-for-byte. The recursion is depth-guarded at
//! [`MAX_DEPTH`] against hostile nesting, because a `catch_unwind` cannot catch a
//! stack overflow.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::typescript::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const FUNCTION: &str = "Function";
    pub const CLASS: &str = "Class";
    pub const INTERFACE: &str = "Interface";
    pub const ENUM: &str = "Enum";
    pub const TYPE_ALIAS: &str = "TypeAlias";
    pub const NAMESPACE: &str = "Namespace";
    pub const VARIABLE: &str = "Variable";
    pub const IMPORT: &str = "Import";
    pub const METHOD: &str = "Method";
    pub const PROPERTY: &str = "Property";
    pub const DECORATOR: &str = "Decorator";
    pub const STMT: &str = "Stmt";
    pub const ERROR_ITEM: &str = "ErrorItem";

    pub const NAME: &str = "Name";
    pub const HEADER: &str = "Header";
    pub const SIGNATURE: &str = "Signature";
    pub const ITEM_BLOCK: &str = "ItemBlock";
    pub const MEMBER_BLOCK: &str = "MemberBlock";
    pub const BLOCK: &str = "Block";
    pub const ENUM_BODY: &str = "EnumBody";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remaining group iteratively. Protects against stack overflow on pathological
/// or hostile inputs (deeply nested delimiters or scopes) — a `catch_unwind`
/// cannot catch a stack overflow, so this guard is the real defense. Mirrors the
/// Rust parser's limit exactly.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = TsParser {
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

/// Leading declaration modifiers consumed before an item keyword.
struct Mods {
    export: bool,
}

struct TsParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> TsParser<'s> {
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

    /// Kind of the next significant (non-trivia) token.
    fn peek_kind(&self) -> Option<&'static str> {
        self.peek_kind_n(0)
    }

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

    fn next_is_ident(&self) -> bool {
        self.peek_kind_n(1) == Some(tk::IDENT)
    }

    /// A token that can serve as a member name: identifier, string, number, or a
    /// private `#name`.
    fn at_member_name(&self) -> bool {
        matches!(
            self.peek_kind(),
            Some(k) if k == tk::IDENT || k == tk::STRING || k == tk::NUMBER || k == tk::PRIVATE_IDENT
        )
    }

    fn at_open(&self) -> bool {
        self.at("(") || self.at("[") || self.at("{")
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
            let item = self.parse_item();
            c.push(Child::Node(item));
        }
        self.make_node(node::SOURCE_FILE, c)
    }

    /// Parse `{ items }` as a recursive item list (namespace / module bodies).
    fn parse_item_block(&mut self, label: &'static str) -> Node {
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
                    let item = self.parse_item();
                    c.push(Child::Node(item));
                }
            }
        }
        let node = self.make_node(label, c);
        self.depth -= 1;
        node
    }

    // --- items --------------------------------------------------------------

    fn parse_item(&mut self) -> Node {
        let mut c = Vec::new();
        self.parse_decorators(&mut c);
        let mods = self.parse_modifiers(&mut c);

        self.ws(&mut c);
        // Function (optionally `async`, optionally a `*` generator).
        if self.at("function") || (self.at("async") && self.at_n(1, "function")) {
            return self.finish_function(c);
        }
        if self.at("class") {
            return self.finish_class(c);
        }
        if self.at("interface") && self.next_is_ident() {
            return self.finish_interface(c);
        }
        if self.at("enum") || (self.at("const") && self.at_n(1, "enum")) {
            return self.finish_enum(c);
        }
        if (self.at("namespace") || self.at("module"))
            && matches!(self.peek_kind_n(1), Some(k) if k == tk::IDENT || k == tk::STRING)
        {
            return self.finish_namespace(c);
        }
        if self.at("type") && self.next_is_ident() && (self.at_n(2, "=") || self.at_n(2, "<")) {
            return self.finish_type_alias(c);
        }
        if self.at("const") || self.at("let") || self.at("var") {
            return self.finish_var(c);
        }
        if self.at("import") && !self.at_n(1, "(") && !self.at_n(1, ".") {
            return self.finish_import(c);
        }
        // `export { … } from …` / `export * from …`: a re-export clause, not a
        // definition. Collect to the statement terminator so nothing splits.
        if mods.export && (self.at("{") || self.at("*")) {
            return self.finish_clause(c);
        }
        self.finish_stmt(c)
    }

    /// Outer decorators: `@expr` / `@ns.Name(args)` lines attached to the item
    /// they precede, exactly as the Rust parser attaches `#[attr]`.
    fn parse_decorators(&mut self, c: &mut Vec<Child>) {
        loop {
            self.ws(c);
            if !self.at("@") {
                break;
            }
            let mut d = Vec::new();
            self.eat(&mut d); // @
            self.ws(&mut d);
            if self.at_member_name() {
                self.eat(&mut d); // base name
            }
            loop {
                self.ws(&mut d);
                if self.at(".") {
                    self.eat(&mut d);
                    self.ws(&mut d);
                    if self.at_member_name() {
                        self.eat(&mut d);
                    }
                } else {
                    break;
                }
            }
            self.ws(&mut d);
            if self.at("(") {
                let g = self.parse_delimited(None);
                d.push(Child::Node(g));
            }
            let node = self.make_node(node::DECORATOR, d);
            c.push(Child::Node(node));
        }
    }

    /// Leading declaration modifiers: `export`, `default`, `declare`, `abstract`.
    /// Access modifiers (`public`, `static`, …) appear only on class members and
    /// are handled in [`TsParser::parse_member`].
    fn parse_modifiers(&mut self, c: &mut Vec<Child>) -> Mods {
        let mut m = Mods { export: false };
        loop {
            self.ws(c);
            if self.at("export") {
                m.export = true;
                self.eat(c);
            } else if self.at("default") || self.at("declare") || self.at("abstract") {
                self.eat(c);
            } else {
                break;
            }
        }
        m
    }

    fn finish_function(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        if self.at("async") {
            self.eat(&mut c);
            self.ws(&mut c);
        }
        self.eat(&mut c); // function
        self.ws(&mut c);
        if self.at("*") {
            self.eat(&mut c); // generator
            self.ws(&mut c);
        }
        if self.at_member_name() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        // Angle/brace-aware like method signatures: a generic `<T = { … }>` or an
        // object-type return `function f(): { a: T } { … }` must not be read as
        // the body brace.
        if let Some(sig) = self.collect_region_inner(node::SIGNATURE, &["{", ";"], true, true) {
            c.push(Child::Node(sig));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
        } else if self.at(";") {
            self.eat(&mut c); // overload / ambient signature, no body
        }
        self.make_node(node::FUNCTION, c)
    }

    fn finish_class(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // class
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        // `<T> extends Base<…> implements A, B` up to the body brace. Angle-aware
        // so an object/mapped type inside a type argument (`extends Base<{ … }>`)
        // is balanced rather than mistaken for the body brace.
        if let Some(h) = self.collect_region_inner(node::HEADER, &["{"], true, false) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_member_block(node::MEMBER_BLOCK);
            c.push(Child::Node(b));
        }
        self.make_node(node::CLASS, c)
    }

    fn finish_interface(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // interface
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        // Angle-aware: `extends Base<…, { [K in T]: U }>` keeps an object/mapped
        // type inside type arguments from being read as the interface body.
        if let Some(h) = self.collect_region_inner(node::HEADER, &["{"], true, false) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_member_block(node::MEMBER_BLOCK);
            c.push(Child::Node(b));
        }
        self.make_node(node::INTERFACE, c)
    }

    fn finish_enum(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        if self.at("const") {
            self.eat(&mut c); // const enum
            self.ws(&mut c);
        }
        self.eat(&mut c); // enum
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        self.ws(&mut c);
        if self.at("{") {
            // The variant list is a balanced token tree; the Enum node is what
            // matters to the IR. Names can be read off these tokens later.
            let b = self.parse_delimited(Some(node::ENUM_BODY));
            c.push(Child::Node(b));
        }
        self.make_node(node::ENUM, c)
    }

    fn finish_type_alias(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // type
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(h) = self.collect_region(node::HEADER, &[";"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::TYPE_ALIAS, c)
    }

    fn finish_namespace(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // namespace / module
        self.ws(&mut c);
        // Name: an identifier (possibly dotted `A.B.C`) or an ambient module
        // string. Capture the leading name token, with any `.B.C` in the header.
        if self.at_member_name() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(h) = self.collect_region(node::HEADER, &["{"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_item_block(node::ITEM_BLOCK);
            c.push(Child::Node(b));
        } else if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::NAMESPACE, c)
    }

    fn finish_var(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // const / let / var
        if let Some(h) = self.collect_region(node::HEADER, &[";"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::VARIABLE, c)
    }

    fn finish_import(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // import
        if let Some(h) = self.collect_region(node::HEADER, &[";"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::IMPORT, c)
    }

    /// An `export { … } from '…'` / `export * from '…'` clause. Collected up to
    /// the statement terminator so it stays a single lossless statement.
    fn finish_clause(&mut self, mut c: Vec<Child>) -> Node {
        if let Some(h) = self.collect_region(node::HEADER, &[";"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::STMT, c)
    }

    /// A generic (non-declaration) statement. Bounded by the next top-level `;`
    /// (consumed), the enclosing `}` (left in place), or the start of a new
    /// declaration keyword (left in place, so a definition is never swallowed).
    fn finish_stmt(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        // A leading `{` is a block statement: capture it and stop.
        if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
            return self.make_node(node::STMT, c);
        }
        let mut took = false;
        loop {
            self.ws(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            if self.at(";") {
                self.eat(&mut c);
                took = true;
                break;
            }
            if self.at("}") {
                break;
            }
            if took && self.at_decl_start() {
                break;
            }
            if self.at_open() {
                let g = self.parse_delimited(None);
                c.push(Child::Node(g));
            } else {
                self.eat(&mut c);
            }
            took = true;
        }
        if !took {
            // Guarantee forward progress on a stray token (e.g. a lone `}`).
            self.ws(&mut c);
            if self.peek_kind().is_some() {
                self.eat(&mut c);
            }
        }
        self.make_node(node::STMT, c)
    }

    /// True at the start of a top-level declaration, used to end a generic
    /// statement before a new definition rather than absorbing it.
    fn at_decl_start(&self) -> bool {
        self.at("@")
            || self.at("function")
            || self.at("class")
            || self.at("interface")
            || self.at("enum")
            || self.at("namespace")
            || self.at("module")
            || self.at("import")
            || self.at("export")
            || self.at("const")
            || self.at("let")
            || self.at("var")
            || self.at("type")
            || self.at("declare")
            || self.at("abstract")
    }

    // --- class / interface members -----------------------------------------

    /// Parse `{ members }` as a recursive member list (class / interface bodies).
    fn parse_member_block(&mut self, label: &'static str) -> Node {
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
                    let m = self.parse_member();
                    c.push(Child::Node(m));
                }
            }
        }
        let node = self.make_node(label, c);
        self.depth -= 1;
        node
    }

    /// One class/interface member: a method (has a `(` / `<` signature) or a
    /// property/field/index/call signature (everything else, to its terminator).
    fn parse_member(&mut self) -> Node {
        let mut c = Vec::new();
        self.parse_decorators(&mut c);
        // Access / accessor modifiers, gated so a member literally named like a
        // modifier (e.g. `private: number` in an interface) is not misread.
        loop {
            self.ws(&mut c);
            if self.at_member_modifier() {
                self.eat(&mut c);
            } else {
                break;
            }
        }
        self.ws(&mut c);
        // A stray separator: an empty member.
        if self.at(";") || self.at(",") {
            self.eat(&mut c);
            return self.make_node(node::PROPERTY, c);
        }
        if self.at("*") {
            self.eat(&mut c); // generator method
            self.ws(&mut c);
        }
        // Member name: identifier/string/number/private, or a `[computed]` name
        // (left in the signature/header — no static name to capture).
        if self.at_member_name() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        self.ws(&mut c);
        if self.at("?") || self.at("!") {
            self.eat(&mut c); // optional / definite-assignment marker
        }
        self.ws(&mut c);
        if self.at("(") || self.at("<") || self.at("[") {
            // Method (or call/index signature): a `(`/`<`/`[` signature region.
            if let Some(sig) =
                self.collect_region_inner(node::SIGNATURE, &["{", ";", ","], true, true)
            {
                c.push(Child::Node(sig));
            }
            self.ws(&mut c);
            if self.at("{") {
                let b = self.parse_delimited(Some(node::BLOCK));
                c.push(Child::Node(b));
                self.make_node(node::METHOD, c)
            } else {
                if self.at(";") || self.at(",") {
                    self.eat(&mut c); // signature-only (interface / overload)
                }
                self.make_node(node::METHOD, c)
            }
        } else {
            // Property / field: `: T`, `= init`, etc. up to the terminator.
            if let Some(h) = self.collect_region_inner(node::HEADER, &[";", ",", "}"], true, false)
            {
                c.push(Child::Node(h));
            }
            self.ws(&mut c);
            if self.at(";") || self.at(",") {
                self.eat(&mut c);
            }
            self.make_node(node::PROPERTY, c)
        }
    }

    /// Whether the cursor is at an access/accessor modifier keyword acting as a
    /// modifier (followed by another modifier or the member name) rather than as
    /// the member name itself.
    fn at_member_modifier(&self) -> bool {
        let w = match self.peek_n_text(0) {
            Some(w) => w,
            None => return false,
        };
        let is_modifier_word = matches!(
            w,
            "public"
                | "private"
                | "protected"
                | "static"
                | "readonly"
                | "abstract"
                | "override"
                | "declare"
                | "async"
                | "get"
                | "set"
                | "accessor"
        );
        if !is_modifier_word {
            return false;
        }
        // If the next token makes `w` a member name or call, it is not a modifier.
        !matches!(
            self.peek_n_text(1),
            Some(":")
                | Some("?")
                | Some("(")
                | Some(")")
                | Some(",")
                | Some(";")
                | Some("=")
                | Some("}")
                | Some("<")
                | Some("!")
        )
    }

    // --- shared helpers -----------------------------------------------------

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.eat(&mut c); // the name token (cursor is at it after caller ws)
        self.make_node(node::NAME, c)
    }

    /// Collect tokens (descending into balanced groups) until a significant stop
    /// token at delimiter depth 0. Leading/trailing trivia around a stop stays
    /// with the parent.
    fn collect_region(&mut self, label: &'static str, stops: &[&str]) -> Option<Node> {
        self.collect_region_inner(label, stops, false, false)
    }

    /// Like [`Self::collect_region`] but with two type-syntax–aware refinements,
    /// each gated by a flag and enabled for method signatures / member headers:
    ///
    /// * `balance_angles`: track `<…>` type-parameter / type-argument nesting so a
    ///   `,` (or `;`) *inside* angle brackets does not end the region. Without it,
    ///   a generic method `m<X, Y>(…)` stops at the first type-parameter comma,
    ///   truncating the signature and mis-parsing the remainder as a sibling
    ///   member — dropping every following member of the class. `<` is
    ///   unambiguously a generic opener here, so the less-than operator is not a
    ///   concern. A `>`-leading token (`>`, `>>`, `>>>`) closes that many levels.
    /// * `balance_braces`: a `{` reached in *type position* — i.e. right after a
    ///   token that expects a type (`:`, `|`, `&`, `,`, `(`, `=>`, `extends`, …) —
    ///   is an object **type** literal (`m(): { a: T } { body }`), not the method
    ///   body, so it is balanced rather than treated as the body terminator.
    ///   Otherwise the bare `{` is the body and stops the region as usual.
    ///
    /// `()`/`[]`/`{}` are always balanced via `parse_delimited`.
    fn collect_region_inner(
        &mut self,
        label: &'static str,
        stops: &[&str],
        balance_angles: bool,
        balance_braces: bool,
    ) -> Option<Node> {
        let mut c = Vec::new();
        let mut angle: usize = 0;
        // Last significant (non-trivia) token text seen, to classify a `{` as a
        // type literal vs the method body. `(` seeds it so `(): {…}` — a return
        // type with no params text before `:` — still classifies correctly.
        let mut prev_sig: Option<String> = None;
        loop {
            if self.peek_kind().is_none() {
                break;
            }
            if angle == 0 && stops.iter().any(|s| self.at(s)) {
                // A `{` in type position is an object type, not the body: keep going.
                let type_brace = balance_braces
                    && self.at("{")
                    && matches!(
                        prev_sig.as_deref(),
                        Some(
                            ":" | "|"
                                | "&"
                                | ","
                                | "("
                                | "=>"
                                | "extends"
                                | "keyof"
                                | "typeof"
                                | "readonly"
                                | "in"
                                | "?"
                        )
                    );
                if !type_brace {
                    break;
                }
            }
            if balance_angles {
                if self.at("<") {
                    angle += 1;
                    prev_sig = Some("<".to_string());
                    self.ws(&mut c);
                    self.eat(&mut c);
                    continue;
                }
                if angle > 0 {
                    let leading_gt = self
                        .peek_n_text(0)
                        .map(|t| t.chars().take_while(|&ch| ch == '>').count())
                        .unwrap_or(0);
                    if leading_gt > 0 {
                        angle = angle.saturating_sub(leading_gt);
                        prev_sig = Some(">".to_string());
                        self.ws(&mut c);
                        self.eat(&mut c);
                        continue;
                    }
                }
            }
            if self.at_open() {
                // A balanced group's "previous token" for the next iteration is its
                // closing delimiter (a complete type/expression), so a `{` after it
                // reads as the body — not a type literal.
                prev_sig = match self.peek_n_text(0) {
                    Some("(") => Some(")".to_string()),
                    Some("[") => Some("]".to_string()),
                    _ => Some("}".to_string()),
                };
                self.ws(&mut c);
                let inner = self.parse_delimited(None);
                c.push(Child::Node(inner));
            } else {
                self.ws(&mut c);
                prev_sig = self.peek_n_text(0).map(str::to_string);
                self.eat(&mut c);
            }
        }
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(label, c))
        }
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`. The cursor
    /// is at (or before trivia preceding) the opener.
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

    /// Iteratively consume a balanced delimiter run (opener already eaten),
    /// appending every token as a flat leaf. Used at the depth cap so arbitrarily
    /// deep nesting is handled without further recursion.
    fn consume_balanced_flat(&mut self, out: &mut Vec<Child>) {
        let mut balance: i32 = 1;
        while balance > 0 {
            self.ws(out);
            if self.peek_kind().is_none() {
                break;
            }
            if self.at("(") || self.at("[") || self.at("{") {
                balance += 1;
            } else if self.at(")") || self.at("]") || self.at("}") {
                balance -= 1;
            }
            self.eat(out);
        }
    }

    /// Record (once is enough per chain) that the depth cap truncated structure.
    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "typescript.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; group flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }
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

    #[test]
    fn parses_and_is_lossless() {
        let src = "\
// a module
import { readFile } from 'fs';
import type { Opts } from './opts';

export const VERSION = '1.0';

@sealed
export class Point implements Shape {
    private x: number;
    constructor(x: number, public y: number) {
        this.x = x;
    }

    norm(): number {
        return Math.sqrt(this.x * this.x + this.y * this.y);
    }
}

export interface Shape {
    norm(): number;
}

export function add(a: number, b: number): number {
    return a + b;
}

const tag = `value=${add(1, 2)}`;
";
        let tree = parse("mod.ts", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "import x from 'm';\nclass C { m() {} }\ninterface I {}\nenum E { A }\nfunction f() {}\ntype T = number;\nnamespace N { function g() {} }\nconst k = 1;\n";
        let tree = parse("t.ts", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::IMPORT), "import: {kinds:?}");
        assert!(kinds.contains(&node::CLASS), "class: {kinds:?}");
        assert!(kinds.contains(&node::INTERFACE), "interface: {kinds:?}");
        assert!(kinds.contains(&node::ENUM), "enum: {kinds:?}");
        assert!(kinds.contains(&node::FUNCTION), "function: {kinds:?}");
        assert!(kinds.contains(&node::TYPE_ALIAS), "type: {kinds:?}");
        assert!(kinds.contains(&node::NAMESPACE), "namespace: {kinds:?}");
        assert!(kinds.contains(&node::VARIABLE), "const: {kinds:?}");
    }

    #[test]
    fn methods_nest_inside_class_bodies() {
        let src = "class C {\n  a() {}\n  private b(): void {}\n  get c() { return 1; }\n}\n";
        let tree = parse("t.ts", src);
        let class = tree
            .root
            .children_of(node::CLASS)
            .next()
            .expect("a class node");
        let body = class
            .child(node::MEMBER_BLOCK)
            .expect("class has a member block");
        let methods: Vec<&str> = body
            .children_of(node::METHOD)
            .filter_map(|m| m.child(node::NAME))
            .filter_map(|n| n.tokens().next())
            .map(|t| t.span.text(src))
            .collect();
        assert_eq!(methods, vec!["a", "b", "c"]);
    }

    #[test]
    fn declaration_after_unterminated_statement_is_not_swallowed() {
        // No semicolon after the call (ASI); the function must still be an item.
        let src = "doSetup()\nfunction helper() {}\n";
        let tree = parse("t.ts", src);
        let has_helper = tree.root.children_of(node::FUNCTION).any(|f| {
            f.child(node::NAME)
                .and_then(|n| n.tokens().next())
                .map(|t| t.span.text(src) == "helper")
                .unwrap_or(false)
        });
        assert!(has_helper, "helper() must be discovered as a Function item");
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let depth = 10_000;
        let src = format!(
            "function x() {{ {}{} }}",
            "(".repeat(depth),
            ")".repeat(depth)
        );
        let tree = parse("deep.ts", &src);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics
                .iter()
                .any(|d| d.code == "typescript.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }

    #[test]
    fn edge_inputs_round_trip() {
        for src in [
            "",                                  // empty
            "\n\n   \n// trailing\n",            // only trivia
            "const s = `open ${x",               // unterminated template
            "class C { m() { return /a/g; } }",  // regex in a method body
            "const o = { a: 1, b: [2, 3] };",    // object/array literals
            "}",                                 // stray close brace
            "const f = async <T>(x: T) => x;\n", // generic arrow
        ] {
            let tree = parse("edge.ts", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
