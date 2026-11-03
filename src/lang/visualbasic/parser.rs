//! Visual Basic .NET parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust, Python, and C# parsers
//! ([`crate::lang::rust::parser`], [`crate::lang::csharp::parser`]): declaration
//! *headers* are parsed precisely — a method's name and parameter list, a type's
//! name, an `Imports` path, an `Inherits`/`Implements` clause — while bodies and
//! expression regions are captured as balanced token regions, which are perfectly
//! lossless. Graph facts (calls, base lists, type refs) are extracted from these
//! real tokens in the lowering pass, never invented.
//!
//! VB .NET differs from the brace languages in two structural ways:
//!   * Blocks are delimited by `Keyword … End Keyword` (e.g. `Sub … End Sub`,
//!     `Class … End Class`) rather than `{ … }`. The parser recurses into
//!     container bodies (Namespace/Module/Class/Structure/Interface) as item
//!     lists, and captures method/property bodies as a flat balanced region that
//!     ends at the matching `End <kw>`.
//!   * Newlines are statement terminators (the lexer emits them as significant
//!     tokens), so single-line declarations are collected up to a newline or a
//!     `:` separator. The `_` line-continuation is trivia, so a folded statement
//!     parses as one logical line.
//!
//! VB is **case-insensitive**, so every keyword/structural comparison uses
//! [`str::eq_ignore_ascii_case`] (via [`Self::at`]).
//!
//! Anything unrecognized still lands in the tree as its exact tokens (a
//! `Statement`/`ErrorItem` node or a flat token run), so the result always
//! round-trips byte-for-byte. The recursion is depth-guarded at [`MAX_DEPTH`]
//! against hostile nesting, because a `catch_unwind` cannot catch a stack
//! overflow.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::visualbasic::lexer::{kind as tk, lex};

/// CST node-kind labels. The lowering interprets these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const IMPORTS: &str = "Imports";
    pub const NAMESPACE: &str = "Namespace";
    pub const MODULE: &str = "Module";
    pub const CLASS: &str = "Class";
    pub const STRUCTURE: &str = "Structure";
    pub const INTERFACE: &str = "Interface";
    pub const ENUM: &str = "Enum";
    pub const DELEGATE: &str = "Delegate";
    pub const METHOD: &str = "Method";
    pub const PROPERTY: &str = "Property";
    pub const FIELD: &str = "Field";
    pub const EVENT: &str = "Event";
    pub const INHERITS: &str = "Inherits";
    pub const IMPLEMENTS: &str = "Implements";
    pub const STATEMENT: &str = "Statement";
    pub const ERROR_ITEM: &str = "ErrorItem";

    pub const NAME: &str = "Name";
    pub const HEADER: &str = "Header";
    pub const ATTR_LIST: &str = "AttrList";
    pub const ITEM_BLOCK: &str = "ItemBlock";
    pub const ENUM_BODY: &str = "EnumBody";
    pub const BLOCK: &str = "Block";

    pub const PAREN: &str = "Paren";
    pub const BRACE: &str = "Brace";
}

/// Declaration modifiers consumed before the declaration keyword. `Dim`/`Const`
/// double as field introducers but are listed here so a field's name (the first
/// non-keyword identifier after them) is reached uniformly.
const MODIFIERS: &[&str] = &[
    "public",
    "private",
    "protected",
    "friend",
    "shared",
    "shadows",
    "overloads",
    "overrides",
    "overridable",
    "mustoverride",
    "notoverridable",
    "mustinherit",
    "notinheritable",
    "partial",
    "default",
    "readonly",
    "writeonly",
    "static",
    "const",
    "dim",
    "withevents",
    "async",
    "iterator",
    "narrowing",
    "widening",
];

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat run. Mirrors the Rust/C# guard exactly, since a
/// `catch_unwind` cannot catch a stack overflow.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = VbParser {
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

struct VbParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    depth: usize,
}

impl VbParser<'_> {
    // --- cursor primitives --------------------------------------------------

    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading trivia tokens (whitespace, comments,
    /// line-continuations) into `out`. Newlines are significant and are *not*
    /// trivia, so they stop this.
    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
        }
    }

    /// Move trivia, blank-line `newline` tokens, and `:` separators into `out`.
    /// Used between items so blank lines never break the item list.
    fn skip_separators(&mut self, out: &mut Vec<Child>) {
        loop {
            self.ws(out);
            if self.peek_kind() == Some(tk::NEWLINE) || self.at(":") {
                self.eat(out);
            } else {
                break;
            }
        }
    }

    /// Consume one statement separator (a `newline` or `:`), plus the trivia
    /// preceding it, if present.
    fn eat_stmt_sep(&mut self, out: &mut Vec<Child>) {
        self.ws(out);
        if self.peek_kind() == Some(tk::NEWLINE) || self.at(":") {
            self.eat(out);
        }
    }

    /// Kind of the n-th significant token (skips trivia; newlines count).
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

    /// Case-insensitive match of the current significant token against `s`.
    fn at(&self, s: &str) -> bool {
        matches!(self.peek_n_text(0), Some(t) if t.eq_ignore_ascii_case(s))
    }

    /// Case-insensitive match of the n-th significant token against `s`.
    fn at_n(&self, n: usize, s: &str) -> bool {
        matches!(self.peek_n_text(n), Some(t) if t.eq_ignore_ascii_case(s))
    }

    fn at_ident(&self) -> bool {
        self.peek_kind() == Some(tk::IDENT)
    }

    fn at_open(&self) -> bool {
        self.at("(") || self.at("{")
    }

    fn at_modifier(&self) -> bool {
        matches!(self.peek_n_text(0), Some(t) if MODIFIERS.iter().any(|m| t.eq_ignore_ascii_case(m)))
    }

    /// True at the start of an `End <kw>` block terminator.
    fn at_end(&self, end_kw: &str) -> bool {
        self.at("End") && self.at_n(1, end_kw)
    }

    /// Text of the next significant token that is not a separator (skips trivia,
    /// `newline`, and `:`). Used to peek at a following line's first keyword.
    fn next_decl_text(&self) -> Option<String> {
        let mut j = self.i;
        while j < self.toks.len() {
            let t = &self.toks[j];
            if t.trivia || t.kind == tk::NEWLINE {
                j += 1;
                continue;
            }
            let text = t.span.text(self.src);
            if text == ":" {
                j += 1;
                continue;
            }
            return Some(text.to_string());
        }
        None
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
            self.skip_separators(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            let before = self.i;
            let item = self.parse_item(false);
            c.push(Child::Node(item));
            self.force_progress(&mut c, before);
        }
        self.make_node(node::SOURCE_FILE, c)
    }

    /// Parse an item list up to (but not consuming) the `End <end_kw>` that closes
    /// the enclosing block. `in_interface` makes contained methods/properties
    /// bodiless.
    fn parse_item_block(&mut self, end_kw: &str, in_interface: bool) -> Node {
        if self.depth >= MAX_DEPTH {
            // Depth cap: consume the body as a flat run up to the terminator.
            let mut c = Vec::new();
            while self.peek_kind().is_some() && !self.at_end(end_kw) {
                self.eat(&mut c);
            }
            self.note_depth_limit();
            return self.make_node(node::ITEM_BLOCK, c);
        }
        self.depth += 1;
        let mut c = Vec::new();
        loop {
            self.skip_separators(&mut c);
            if self.peek_kind().is_none() || self.at_end(end_kw) {
                break;
            }
            let before = self.i;
            let item = self.parse_item(in_interface);
            c.push(Child::Node(item));
            self.force_progress(&mut c, before);
        }
        let n = self.make_node(node::ITEM_BLOCK, c);
        self.depth -= 1;
        n
    }

    /// Guarantee the cursor advanced; otherwise consume one token so the loop can
    /// never spin forever on unclassifiable input.
    fn force_progress(&mut self, out: &mut Vec<Child>, before: usize) {
        if self.i == before {
            self.eat(out);
        }
    }

    // --- items --------------------------------------------------------------

    fn parse_item(&mut self, in_interface: bool) -> Node {
        let mut c = Vec::new();

        // Leading attribute lists: `<Serializable>` `<Obsolete("x")>`.
        loop {
            self.ws(&mut c);
            if self.at("<") {
                let a = self.collect_angle(node::ATTR_LIST);
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

        self.ws(&mut c);
        if self.at("Imports") {
            self.finish_simple_line(c, node::IMPORTS)
        } else if self.at("Inherits") {
            self.finish_simple_line(c, node::INHERITS)
        } else if self.at("Implements") {
            self.finish_simple_line(c, node::IMPLEMENTS)
        } else if self.at("Namespace") {
            self.finish_container(c, node::NAMESPACE, "Namespace", false)
        } else if self.at("Module") {
            self.finish_container(c, node::MODULE, "Module", false)
        } else if self.at("Class") {
            self.finish_container(c, node::CLASS, "Class", false)
        } else if self.at("Structure") {
            self.finish_container(c, node::STRUCTURE, "Structure", false)
        } else if self.at("Interface") {
            self.finish_container(c, node::INTERFACE, "Interface", true)
        } else if self.at("Enum") {
            self.finish_enum(c)
        } else if self.at("Sub") {
            self.finish_method(c, "Sub", in_interface)
        } else if self.at("Function") {
            self.finish_method(c, "Function", in_interface)
        } else if self.at("Operator") {
            self.finish_method(c, "Operator", in_interface)
        } else if self.at("Declare") {
            self.finish_declare(c)
        } else if self.at("Property") {
            self.finish_property(c, in_interface)
        } else if self.at("Delegate") {
            self.finish_delegate(c)
        } else if self.at("Event") {
            self.finish_named_line(c, node::EVENT)
        } else if self.at_ident() && !self.peek_is_keyword() {
            // A field/variable declaration: `[modifiers] Name As Type [= init]`.
            self.finish_field(c)
        } else {
            self.finish_statement(c)
        }
    }

    fn peek_is_keyword(&self) -> bool {
        matches!(self.peek_n_text(0), Some(t) if crate::lang::visualbasic::lexer::is_keyword(t))
    }

    /// A keyword-led single-line declaration whose payload is captured as a
    /// `Header` (Imports / Inherits / Implements). Stops at the line terminator.
    fn finish_simple_line(&mut self, mut c: Vec<Child>, kind: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // the leading keyword
        if let Some(h) = self.collect_line(node::HEADER) {
            c.push(Child::Node(h));
        }
        self.eat_stmt_sep(&mut c);
        self.make_node(kind, c)
    }

    /// A keyword-led single-line declaration that has a name then a header
    /// (`Event Click As EventHandler`).
    fn finish_named_line(&mut self, mut c: Vec<Child>, kind: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // keyword
        self.ws(&mut c);
        if self.peek_kind().is_some() && self.peek_kind() != Some(tk::NEWLINE) {
            c.push(Child::Node(self.take_name()));
        }
        if let Some(h) = self.collect_line(node::HEADER) {
            c.push(Child::Node(h));
        }
        self.eat_stmt_sep(&mut c);
        self.make_node(kind, c)
    }

    /// A container block: `Namespace`/`Module`/`Class`/`Structure`/`Interface`.
    /// Parses the header line, then the body as a recursive item list up to the
    /// matching `End <kw>`.
    fn finish_container(
        &mut self,
        mut c: Vec<Child>,
        kind: &'static str,
        end_kw: &str,
        in_interface: bool,
    ) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // the keyword
        self.ws(&mut c);
        if self.peek_kind().is_some() && self.peek_kind() != Some(tk::NEWLINE) {
            // A namespace name may be dotted (`A.B.C`); type names are a single
            // identifier (generic `(Of T)` clauses fall to the header).
            let name = if kind == node::NAMESPACE {
                self.take_dotted_name()
            } else {
                self.take_name()
            };
            c.push(Child::Node(name));
        }
        if let Some(h) = self.collect_line(node::HEADER) {
            c.push(Child::Node(h));
        }
        self.eat_stmt_sep(&mut c);
        let block = self.parse_item_block(end_kw, in_interface);
        c.push(Child::Node(block));
        self.consume_end(&mut c, end_kw);
        self.make_node(kind, c)
    }

    fn finish_enum(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // Enum
        self.ws(&mut c);
        if self.peek_kind().is_some() && self.peek_kind() != Some(tk::NEWLINE) {
            c.push(Child::Node(self.take_name()));
        }
        if let Some(h) = self.collect_line(node::HEADER) {
            c.push(Child::Node(h));
        }
        self.eat_stmt_sep(&mut c);
        let body = self.collect_block_region(node::ENUM_BODY, "Enum");
        c.push(Child::Node(body));
        self.consume_end(&mut c, "Enum");
        self.make_node(node::ENUM, c)
    }

    /// A `Sub`/`Function`/`Operator`. Bodiless inside an interface, or when marked
    /// `MustOverride`; otherwise the body is captured up to the matching `End`.
    fn finish_method(&mut self, mut c: Vec<Child>, end_kw: &str, in_interface: bool) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // Sub / Function / Operator
        self.ws(&mut c);
        if self.peek_kind().is_some() && self.peek_kind() != Some(tk::NEWLINE) {
            c.push(Child::Node(self.take_name()));
        }
        if let Some(h) = self.collect_line(node::HEADER) {
            c.push(Child::Node(h));
        }
        let bodiless = in_interface || has_modifier_text(&c, self.src, "mustoverride");
        if bodiless {
            self.eat_stmt_sep(&mut c);
            return self.make_node(node::METHOD, c);
        }
        self.eat_stmt_sep(&mut c);
        let block = self.collect_block_region(node::BLOCK, end_kw);
        c.push(Child::Node(block));
        self.consume_end(&mut c, end_kw);
        self.make_node(node::METHOD, c)
    }

    /// A `Declare [Ansi|Unicode|Auto] Sub|Function Name Lib "..." (...)` P/Invoke:
    /// always a single line, no body. Lowered as a (bodiless) method.
    fn finish_declare(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // Declare
        self.ws(&mut c);
        if self.at("Ansi") || self.at("Unicode") || self.at("Auto") {
            self.eat(&mut c);
            self.ws(&mut c);
        }
        if self.at("Sub") || self.at("Function") {
            self.eat(&mut c);
            self.ws(&mut c);
        }
        if self.peek_kind().is_some() && self.peek_kind() != Some(tk::NEWLINE) {
            c.push(Child::Node(self.take_name()));
        }
        if let Some(h) = self.collect_line(node::HEADER) {
            c.push(Child::Node(h));
        }
        self.eat_stmt_sep(&mut c);
        self.make_node(node::METHOD, c)
    }

    /// A `Property`: auto-property (single line, no body) or a full property with
    /// `Get`/`Set` accessors up to `End Property`.
    fn finish_property(&mut self, mut c: Vec<Child>, in_interface: bool) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // Property
        self.ws(&mut c);
        if self.peek_kind().is_some() && self.peek_kind() != Some(tk::NEWLINE) {
            c.push(Child::Node(self.take_name()));
        }
        if let Some(h) = self.collect_line(node::HEADER) {
            c.push(Child::Node(h));
        }
        let bodiless = in_interface || has_modifier_text(&c, self.src, "mustoverride");
        self.eat_stmt_sep(&mut c);
        // A full property's body opens with a `Get`/`Set` accessor on a later line.
        let has_body = !bodiless
            && matches!(self.next_decl_text(), Some(t) if t.eq_ignore_ascii_case("get") || t.eq_ignore_ascii_case("set"));
        if has_body {
            let block = self.collect_block_region(node::BLOCK, "Property");
            c.push(Child::Node(block));
            self.consume_end(&mut c, "Property");
        }
        self.make_node(node::PROPERTY, c)
    }

    fn finish_delegate(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // Delegate
        self.ws(&mut c);
        if self.at("Sub") || self.at("Function") {
            self.eat(&mut c); // Delegate Sub / Delegate Function
            self.ws(&mut c);
        }
        if self.peek_kind().is_some() && self.peek_kind() != Some(tk::NEWLINE) {
            c.push(Child::Node(self.take_name()));
        }
        if let Some(h) = self.collect_line(node::HEADER) {
            c.push(Child::Node(h));
        }
        self.eat_stmt_sep(&mut c);
        self.make_node(node::DELEGATE, c)
    }

    /// A field / variable declaration with no leading keyword (modifiers, then the
    /// name and type). Captured as a `Header` for name/type extraction.
    fn finish_field(&mut self, mut c: Vec<Child>) -> Node {
        if let Some(h) = self.collect_line(node::HEADER) {
            c.push(Child::Node(h));
        }
        self.eat_stmt_sep(&mut c);
        // Guarantee progress on otherwise-empty input.
        if c.iter().all(is_trivia_child) {
            self.eat(&mut c);
        }
        self.make_node(node::FIELD, c)
    }

    /// Any other line (a statement outside a method body, an `Option`/`On Error`
    /// directive, a stray token). Consumed to the line terminator so nothing is
    /// dropped.
    fn finish_statement(&mut self, mut c: Vec<Child>) -> Node {
        if let Some(h) = self.collect_line(node::HEADER) {
            // Flatten the header's children directly into the statement so a
            // stray-token statement stays simple.
            for ch in h.children {
                c.push(ch);
            }
        }
        self.eat_stmt_sep(&mut c);
        if c.iter().all(is_trivia_child) {
            self.eat(&mut c);
            self.diags.push(Diagnostic {
                code: "vbnet.unrecognized",
                message: "token(s) not recognized as a VB.NET item".to_string(),
                span: children_span(&c).unwrap_or_else(|| ByteSpan::empty_at(self.cur_offset())),
            });
            return self.make_node(node::ERROR_ITEM, c);
        }
        self.make_node(node::STATEMENT, c)
    }

    // --- shared helpers -----------------------------------------------------

    /// Consume the next significant token as a `Name` node.
    fn take_name(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c);
        self.make_node(node::NAME, c)
    }

    /// Consume a dotted name (`A.B.C`) as a single `Name` node, for namespace
    /// declarations. Stops at the first token that is not `ident` `.` `ident`.
    fn take_dotted_name(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        if self.at_ident() {
            self.eat(&mut c);
        }
        while self.peek_n_text(0) == Some(".") {
            self.ws(&mut c);
            self.eat(&mut c); // .
            self.ws(&mut c);
            if self.at_ident() {
                self.eat(&mut c);
            }
        }
        self.make_node(node::NAME, c)
    }

    /// Consume the `End <kw>` terminator (plus its trailing separator). Tolerant:
    /// if the keyword does not match it consumes only `End` so the loop advances.
    fn consume_end(&mut self, out: &mut Vec<Child>, end_kw: &str) {
        self.skip_separators(out);
        if self.at("End") {
            self.eat(out); // End
            self.ws(out);
            if self.at(end_kw) {
                self.eat(out);
            }
            // `End Sub` / `End Class` … may be followed by trailing trivia + sep.
            self.eat_stmt_sep(out);
        }
    }

    /// Collect a single logical line up to (not including) a `newline` or a
    /// depth-0 `:` separator, descending into balanced `(…)`/`{…}` groups so a
    /// `:` inside a group does not end the line. Returns `None` if nothing
    /// significant was collected.
    fn collect_line(&mut self, label: &'static str) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            match self.peek_kind() {
                None => break,
                Some(tk::NEWLINE) => break,
                Some(_) if self.at(":") => break,
                Some(_) if self.at_open() => {
                    self.ws(&mut c);
                    let g = self.parse_delimited(None);
                    c.push(Child::Node(g));
                }
                Some(_) => {
                    self.ws(&mut c);
                    self.eat(&mut c);
                }
            }
        }
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(label, c))
        }
    }

    /// Collect a block body (statements / enum members) up to the matching
    /// `End <end_kw>`, which is left for the caller. Newlines are kept inside the
    /// region; balanced groups are parsed so call sites are recoverable.
    fn collect_block_region(&mut self, label: &'static str, end_kw: &str) -> Node {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            match self.peek_kind() {
                None => break,
                Some(_) if self.at_end(end_kw) => break,
                Some(_) if self.at_open() => {
                    let g = self.parse_delimited(None);
                    c.push(Child::Node(g));
                }
                Some(_) => self.eat(&mut c),
            }
        }
        self.make_node(label, c)
    }

    /// Collect a balanced `<…>` attribute list, descending into `(…)` groups.
    fn collect_angle(&mut self, label: &'static str) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // <
        let mut depth = 1i32;
        loop {
            self.ws(&mut c);
            match self.peek_kind() {
                None | Some(tk::NEWLINE) => break,
                Some(_) if self.at("<") => {
                    depth += 1;
                    self.eat(&mut c);
                }
                Some(_) if self.at(">") => {
                    depth -= 1;
                    self.eat(&mut c);
                    if depth == 0 {
                        break;
                    }
                }
                Some(_) if self.at("(") => {
                    let g = self.parse_delimited(None);
                    c.push(Child::Node(g));
                }
                Some(_) => self.eat(&mut c),
            }
        }
        self.make_node(label, c)
    }

    /// Parse a balanced delimiter group `(…)` or `{…}`. Cursor is at (or before
    /// trivia preceding) the opener.
    fn parse_delimited(&mut self, label_override: Option<&'static str>) -> Node {
        let mut g = Vec::new();
        self.ws(&mut g);
        let (close, default_label) = if self.at("(") {
            (")", node::PAREN)
        } else if self.at("{") {
            ("}", node::BRACE)
        } else {
            return self.make_node(label_override.unwrap_or(node::ERROR_ITEM), g);
        };
        let label = label_override.unwrap_or(default_label);
        self.eat(&mut g); // opener
        loop {
            self.ws(&mut g);
            match self.peek_kind() {
                None => break, // unterminated; still lossless
                Some(_) if self.at(close) => {
                    self.eat(&mut g);
                    break;
                }
                Some(_) if self.at_open() => {
                    if self.depth < MAX_DEPTH {
                        self.depth += 1;
                        let inner = self.parse_delimited(None);
                        self.depth -= 1;
                        g.push(Child::Node(inner));
                    } else {
                        self.eat(&mut g); // opener
                        self.consume_balanced_flat(&mut g);
                        self.note_depth_limit();
                    }
                }
                Some(_) => self.eat(&mut g),
            }
        }
        self.make_node(label, g)
    }

    /// Iteratively consume a balanced `(`/`{` run (the opener already eaten) at
    /// the depth cap, appending every token flat.
    fn consume_balanced_flat(&mut self, out: &mut Vec<Child>) {
        let mut balance: i32 = 1;
        while balance > 0 {
            self.ws(out);
            match self.peek_n_text(0) {
                None => break,
                Some("(") | Some("{") => balance += 1,
                Some(")") | Some("}") => balance -= 1,
                _ => {}
            }
            self.eat(out);
        }
    }

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "vbnet.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; group flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }
}

fn is_trivia_child(c: &Child) -> bool {
    matches!(c, Child::Token(t) if t.trivia)
}

/// True if any direct, top-level token in `children` (e.g. a consumed modifier)
/// matches `kw` case-insensitively.
fn has_modifier_text(children: &[Child], src: &str, kw: &str) -> bool {
    children.iter().any(|c| match c {
        Child::Token(t) if !t.trivia => t.span.text(src).eq_ignore_ascii_case(kw),
        _ => false,
    })
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
' a file
Imports System
Imports System.Collections.Generic

Namespace App.Core

    Public Interface IGreeter
        Function Greet(name As String) As String
    End Interface

    Public Class Greeter
        Implements IGreeter

        Private ReadOnly _prefix As String = \"Hello\"
        Public Property Count As Integer

        Public Sub New(prefix As String)
            _prefix = prefix
        End Sub

        Public Function Greet(name As String) As String Implements IGreeter.Greet
            Return $\"{_prefix}, {name}!\"
        End Function

        Public Sub Run()
            Dim msg = Greet(\"world\")
            Console.WriteLine(msg)
        End Sub
    End Class

    Public Enum Color
        Red
        Green = 2
        Blue
    End Enum

    Public Module Helpers
        Public Function Twice(n As Integer) As Integer
            Return n * 2
        End Function
    End Module
End Namespace
";
        let tree = parse("Greeter.vb", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "Imports System\nNamespace N\n Class C\n  Sub M()\n  End Sub\n  Dim f As Integer\n End Class\n Enum E\n  A\n End Enum\nEnd Namespace\n";
        let tree = parse("t.vb", src);
        let top = kinds_of(&tree.root);
        assert!(top.contains(&node::IMPORTS), "imports not found: {top:?}");
        assert!(top.contains(&node::NAMESPACE), "namespace: {top:?}");

        let ns = tree.root.child(node::NAMESPACE).unwrap();
        let body = ns.child(node::ITEM_BLOCK).unwrap();
        let members = kinds_of(body);
        assert!(members.contains(&node::CLASS), "class: {members:?}");
        assert!(members.contains(&node::ENUM), "enum: {members:?}");

        let class = body.child(node::CLASS).unwrap();
        let cbody = class.child(node::ITEM_BLOCK).unwrap();
        let cmembers = kinds_of(cbody);
        assert!(cmembers.contains(&node::METHOD), "method: {cmembers:?}");
        assert!(cmembers.contains(&node::FIELD), "field: {cmembers:?}");
        assert!(tree.is_lossless());
    }

    #[test]
    fn interface_methods_are_bodiless() {
        let src = "Interface I\n Function F() As Integer\n Sub G()\nEnd Interface\n";
        let tree = parse("t.vb", src);
        let body = tree
            .root
            .child(node::INTERFACE)
            .unwrap()
            .child(node::ITEM_BLOCK)
            .unwrap();
        let methods: Vec<&Node> = body.children_of(node::METHOD).collect();
        assert_eq!(methods.len(), 2, "two interface methods");
        for m in methods {
            assert!(
                m.child(node::BLOCK).is_none(),
                "interface method has no body"
            );
        }
        assert!(tree.is_lossless());
    }

    #[test]
    fn module_with_function() {
        let src = "Module M\n Sub Main()\n  Console.WriteLine(\"hi\")\n End Sub\nEnd Module\n";
        let tree = parse("t.vb", src);
        let m = tree.root.child(node::MODULE).expect("a Module");
        let body = m.child(node::ITEM_BLOCK).unwrap();
        assert!(kinds_of(body).contains(&node::METHOD));
        assert!(tree.is_lossless());
    }

    #[test]
    fn auto_vs_full_property() {
        let src = "Class C\n Public Property Auto As Integer\n Public Property Full As Integer\n  Get\n   Return 1\n  End Get\n End Property\nEnd Class\n";
        let tree = parse("t.vb", src);
        let body = tree
            .root
            .child(node::CLASS)
            .unwrap()
            .child(node::ITEM_BLOCK)
            .unwrap();
        let props: Vec<&Node> = body.children_of(node::PROPERTY).collect();
        assert_eq!(props.len(), 2, "two properties: {:?}", kinds_of(body));
        assert!(
            props[0].child(node::BLOCK).is_none(),
            "auto-property: no body"
        );
        assert!(props[1].child(node::BLOCK).is_some(), "full property: body");
        assert!(tree.is_lossless());
    }

    #[test]
    fn line_continuation_folds_statement() {
        let src = "Class C\n Dim x As Integer = 1 + _\n  2\nEnd Class\n";
        let tree = parse("t.vb", src);
        let body = tree
            .root
            .child(node::CLASS)
            .unwrap()
            .child(node::ITEM_BLOCK)
            .unwrap();
        assert_eq!(body.children_of(node::FIELD).count(), 1, "one folded field");
        assert!(tree.is_lossless());
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let depth = 10_000;
        let src = format!(
            "Module M\n Sub S()\n  Dim x = {}{}\n End Sub\nEnd Module\n",
            "(".repeat(depth),
            ")".repeat(depth)
        );
        let tree = parse("deep.vb", &src);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics
                .iter()
                .any(|d| d.code == "vbnet.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }

    #[test]
    fn edge_inputs_round_trip() {
        for src in [
            "",
            "   \n\t  \n",
            "' just a comment\n",
            "REM leading rem\n",
            "Option Strict On\n",
            "Class C\n Dim s = $\"{a}\"\nEnd Class\n",
            "Class C\n Dim s = \"a\"\"b\"\nEnd Class\n",
            "#Region \"X\"\nClass C\nEnd Class\n#End Region\n",
            "Class C\n Sub M()\n  x = (1, 2\nEnd Class\n", // unterminated group
            "λ ☃ €",
            "Class Unclosed\n Sub M()\n", // unterminated blocks
        ] {
            let tree = parse("edge.vb", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }

    #[test]
    fn colon_separated_statements_round_trip() {
        let src = "Module M\n Sub S()\n  Dim a = 1 : Dim b = 2\n End Sub\nEnd Module\n";
        let tree = parse("t.vb", src);
        assert!(tree.is_lossless());
    }

    #[test]
    fn output_is_deterministic() {
        let src = "Namespace N\n Class C\n  Inherits B\n  Sub M()\n   f()\n  End Sub\n End Class\nEnd Namespace\n";
        let a = parse("t.vb", src);
        let b = parse("t.vb", src);
        assert_eq!(a.to_json().to_line(), b.to_json().to_line());
    }
}
