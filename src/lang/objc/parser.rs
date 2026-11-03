//! Objective-C parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the C and C++ parsers ([`crate::lang::c::parser`],
//! [`crate::lang::cpp::parser`]): item *headers* are parsed precisely enough to
//! classify each top-level construct and find its name/selector, while bodies,
//! parameter lists, return types, and ivar blocks are captured as balanced
//! **token-tree groups** (`Paren`/`Bracket`/`Brace`) plus flat tokens, which is
//! perfectly lossless. Graph facts (message sends, calls, includes, base classes)
//! are read off these real tokens in the lowering pass, never invented.
//!
//! Objective-C is C plus an `@`-directive object layer. The parser dispatches on
//! the first significant token of each item:
//!   - `#…`        → a preprocessor directive line (`#import`/`#include`/`#define`
//!                   tagged precisely), exactly as in C.
//!   - `@interface`/`@implementation`/`@protocol` → an Objective-C container,
//!     parsed as a header (name, optional `(category)`, optional `: Super`,
//!     optional `<Proto, …>`, optional `{ ivars }`) followed by members up to the
//!     matching `@end`. Members are methods (`-`/`+`), `@property`, other
//!     `@`-directives, preprocessor lines, or ordinary C declarations.
//!   - `@class`/`@import`/other `@…` → a single directive item.
//!   - anything else → an ordinary C declaration unit (function definition,
//!     aggregate, typedef, prototype, or object declaration), classified after the
//!     fact exactly as the C parser does.
//!
//! Anything unrecognized still lands in the tree as its exact tokens, so the
//! result always round-trips byte-for-byte. Recursion into balanced groups is
//! depth-guarded at [`MAX_DEPTH`] against hostile nesting, because a
//! `catch_unwind` cannot catch a stack overflow.

#![allow(clippy::while_let_loop, clippy::doc_overindented_list_items)] // style-only; revisit in verification pass

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::objc::lexer::{is_keyword, kind as tk, lex};

/// CST node-kind labels. The lowering interprets these.
pub mod node {
    pub const UNIT: &str = "Unit";

    // Objective-C object layer.
    pub const INTERFACE: &str = "Interface";
    pub const IMPLEMENTATION: &str = "Implementation";
    pub const PROTOCOL: &str = "Protocol";
    pub const METHOD: &str = "Method";
    pub const PROPERTY: &str = "Property";
    pub const CLASS_DIRECTIVE: &str = "ClassDirective";
    pub const OBJC_IMPORT: &str = "ObjcImport";
    pub const OBJC_DIRECTIVE: &str = "ObjcDirective";

    // C layer.
    pub const FUNCTION: &str = "Function";
    pub const STRUCT: &str = "Struct";
    pub const UNION: &str = "Union";
    pub const ENUM: &str = "Enum";
    pub const TYPEDEF: &str = "Typedef";
    pub const DECL: &str = "Declaration";
    pub const INCLUDE: &str = "Include";
    pub const DEFINE: &str = "Define";
    pub const DIRECTIVE: &str = "Directive";
    pub const ERROR_ITEM: &str = "ErrorItem";

    pub const NAME: &str = "Name";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum group-nesting depth before the parser stops recursing and consumes the
/// remainder as a flat balanced run. Mirrors the Rust/C/C++ parsers' guard exactly
/// (a `catch_unwind` cannot catch a stack overflow).
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = ObjcParser {
        src: source,
        toks,
        i: 0,
        diags: Vec::new(),
        depth: 0,
    };
    let root = p.parse_unit();
    ParseTree {
        source_id: SourceId::from_path(path),
        path: path.to_string(),
        source: source.to_string(),
        root,
        diagnostics: p.diags,
    }
}

struct ObjcParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current group-nesting depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> ObjcParser<'s> {
    // --- cursor primitives --------------------------------------------------

    /// Append the current token (trivia or not) to `out` and advance.
    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading **trivia** tokens into `out`. A `newline` is *not*
    /// trivia, so it is left in place — directive structure depends on it.
    fn ws(&mut self, out: &mut Vec<Child>) {
        while matches!(self.toks.get(self.i), Some(t) if t.trivia) {
            self.eat(out);
        }
    }

    /// Move leading trivia **and** structural newlines into `out`. Used between
    /// top-level / member items, where blank lines are mere separators.
    fn trivia_and_newlines(&mut self, out: &mut Vec<Child>) {
        while let Some(t) = self.toks.get(self.i) {
            if t.trivia || t.kind == tk::NEWLINE {
                self.eat(out);
            } else {
                break;
            }
        }
    }

    /// Text of the n-th significant (non-trivia) token from the cursor; `newline`
    /// counts as significant.
    fn peek_text_n(&self, n: usize) -> Option<&str> {
        let mut count = 0;
        for t in &self.toks[self.i..] {
            if t.trivia {
                continue;
            }
            if count == n {
                return Some(t.span.text(self.src));
            }
            count += 1;
        }
        None
    }

    fn peek_text(&self) -> Option<&str> {
        self.peek_text_n(0)
    }

    fn at(&self, s: &str) -> bool {
        self.peek_text() == Some(s)
    }

    /// True when the next significant token (skipping trivia and structural
    /// newlines) has text equal to one of `set`. Used to stop a runaway header or
    /// declaration from swallowing the next line's directive / `@end`.
    fn next_significant_is_one_of(&self, set: &[&str]) -> bool {
        for t in &self.toks[self.i..] {
            if t.trivia || t.kind == tk::NEWLINE {
                continue;
            }
            return set.contains(&t.span.text(self.src));
        }
        false
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

    fn parse_unit(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.trivia_and_newlines(&mut c);
            if self.toks.get(self.i).is_none() {
                break;
            }
            let item = self.parse_item();
            c.push(Child::Node(item));
        }
        self.make_node(node::UNIT, c)
    }

    fn parse_item(&mut self) -> Node {
        if self.at("#") {
            self.parse_directive()
        } else if self.at("@") {
            self.parse_at_directive()
        } else {
            self.parse_decl()
        }
    }

    /// A preprocessor directive: `#` then the rest of the logical line (up to and
    /// including the terminating `newline`). `#import`/`#include`/`#define` are
    /// tagged precisely; everything else is a generic `Directive`.
    fn parse_directive(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // '#'
        self.ws(&mut c);
        let kw = self.peek_text().map(|s| s.to_string());
        loop {
            match self.toks.get(self.i) {
                None => break,
                Some(t) if t.kind == tk::NEWLINE => break,
                Some(_) => self.eat(&mut c),
            }
        }
        if matches!(self.toks.get(self.i), Some(t) if t.kind == tk::NEWLINE) {
            self.eat(&mut c);
        }
        let kind = match kw.as_deref() {
            // `#import` is the Objective-C include; treat it as an include.
            Some("include") | Some("include_next") | Some("import") => node::INCLUDE,
            Some("define") => node::DEFINE,
            _ => node::DIRECTIVE,
        };
        self.make_node(kind, c)
    }

    // --- the @-directive object layer ---------------------------------------

    fn parse_at_directive(&mut self) -> Node {
        match self.peek_text_n(1) {
            Some("interface") => self.parse_container(node::INTERFACE),
            Some("implementation") => self.parse_container(node::IMPLEMENTATION),
            Some("protocol") => self.parse_container(node::PROTOCOL),
            Some("class") => self.parse_at_line(node::CLASS_DIRECTIVE),
            Some("import") => self.parse_at_line(node::OBJC_IMPORT),
            Some("end") => {
                // A stray `@end` at the top level: keep it (lossless) and advance.
                let mut c = Vec::new();
                self.ws(&mut c);
                self.eat(&mut c); // '@'
                self.ws(&mut c);
                self.eat(&mut c); // 'end'
                self.make_node(node::OBJC_DIRECTIVE, c)
            }
            _ => self.parse_at_generic(),
        }
    }

    /// A simple `@word … ;` directive (`@class A, B;`, `@import Mod;`). Collects
    /// through the terminating `;`, capturing balanced groups, never crossing into
    /// a following line-leading directive.
    fn parse_at_line(&mut self, kind: &'static str) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // '@'
        loop {
            match self.toks.get(self.i) {
                None => break,
                Some(t) if t.trivia => self.eat(&mut c),
                Some(t) if t.kind == tk::NEWLINE => {
                    if self.next_significant_is_one_of(&["@", "#"]) {
                        break;
                    }
                    self.eat(&mut c);
                }
                Some(t) => {
                    let text = t.span.text(self.src);
                    match text {
                        ";" => {
                            self.eat(&mut c);
                            break;
                        }
                        "(" | "[" | "{" => {
                            let g = self.parse_group();
                            c.push(Child::Node(g));
                        }
                        "@" | "#" => break,
                        _ => self.eat(&mut c),
                    }
                }
            }
        }
        self.make_node(kind, c)
    }

    /// A block-shaped `@word …` directive (`@autoreleasepool { … }`, `@try { … }`,
    /// `@synchronized(x) { … }`). Ends at the first top-level `;` or balanced
    /// `{ … }` block, whichever comes first. Mostly seen inside bodies (where it is
    /// just tokens in a group), so this is a defensive top-level fallback.
    fn parse_at_generic(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // '@'
        let mut started = false;
        loop {
            match self.toks.get(self.i) {
                None => break,
                Some(t) if t.trivia => self.eat(&mut c),
                Some(t) if t.kind == tk::NEWLINE => {
                    if started && self.next_significant_is_one_of(&["@", "#"]) {
                        break;
                    }
                    self.eat(&mut c);
                }
                Some(t) => {
                    let text = t.span.text(self.src);
                    match text {
                        ";" => {
                            self.eat(&mut c);
                            break;
                        }
                        "{" => {
                            let g = self.parse_group();
                            c.push(Child::Node(g));
                            break;
                        }
                        "(" | "[" => {
                            let g = self.parse_group();
                            c.push(Child::Node(g));
                            started = true;
                        }
                        "@" | "#" if started => break,
                        _ => {
                            self.eat(&mut c);
                            started = true;
                        }
                    }
                }
            }
        }
        self.make_node(node::OBJC_DIRECTIVE, c)
    }

    /// Parse an `@interface` / `@implementation` / `@protocol` container: its
    /// header, an optional `{ ivars }` block, then members up to `@end`.
    fn parse_container(&mut self, kind: &'static str) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // '@'
        self.ws(&mut c);
        self.eat(&mut c); // 'interface' / 'implementation' / 'protocol'

        // Header: Name, optional (category), optional `: Super`, optional
        // `<Proto, …>`. The protocol list uses `<`/`>` punct tokens, so track
        // angle depth to keep `>` from being read as a member boundary.
        let mut angle: i32 = 0;
        let mut forward = false;
        loop {
            let t = match self.toks.get(self.i) {
                Some(t) => t,
                None => break,
            };
            if t.trivia {
                self.eat(&mut c);
                continue;
            }
            if t.kind == tk::NEWLINE {
                if angle == 0 && self.next_significant_is_one_of(&["{", "@", "#", "-", "+"]) {
                    break;
                }
                self.eat(&mut c);
                continue;
            }
            let text = t.span.text(self.src);
            if angle == 0 {
                match text {
                    ";" => {
                        self.eat(&mut c);
                        forward = true;
                        break;
                    }
                    "{" | "-" | "+" | "@" | "#" => break,
                    _ => {}
                }
            }
            match text {
                "<" => {
                    angle += 1;
                    self.eat(&mut c);
                }
                ">" => {
                    angle -= 1;
                    self.eat(&mut c);
                }
                "(" | "[" => {
                    let g = self.parse_group();
                    c.push(Child::Node(g));
                }
                _ => self.eat(&mut c),
            }
        }

        let name_idx = container_name_idx(&c, self.src);
        c = wrap_name(c, name_idx);

        if forward {
            return self.make_node(kind, c);
        }

        // Optional instance-variable block.
        if self.at("{") {
            let g = self.parse_group();
            c.push(Child::Node(g));
        }

        // Members up to the matching `@end`.
        loop {
            self.trivia_and_newlines(&mut c);
            let text = match self.peek_text() {
                Some(t) => t,
                None => break,
            };
            match text {
                "@" => {
                    match self.peek_text_n(1) {
                        Some("end") => {
                            self.ws(&mut c);
                            self.eat(&mut c); // '@'
                            self.ws(&mut c);
                            self.eat(&mut c); // 'end'
                            break;
                        }
                        Some("property") => {
                            let m = self.parse_property();
                            c.push(Child::Node(m));
                        }
                        _ => {
                            let m = self.parse_member_at_directive();
                            c.push(Child::Node(m));
                        }
                    }
                }
                "-" | "+" => {
                    let m = self.parse_method();
                    c.push(Child::Node(m));
                }
                "#" => {
                    let m = self.parse_directive();
                    c.push(Child::Node(m));
                }
                _ => {
                    let m = self.parse_decl();
                    c.push(Child::Node(m));
                }
            }
        }

        self.make_node(kind, c)
    }

    /// A method `- (ret)sel:(T)a part:(T)b { … }` or its declaration form ending
    /// in `;`. The leading `-`/`+`, the return-type `( … )`, each argument-type
    /// `( … )`, and the optional body `{ … }` are captured as real groups/tokens;
    /// the lowering derives the selector from them.
    fn parse_method(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // '-' or '+'
        loop {
            let t = match self.toks.get(self.i) {
                Some(t) => t,
                None => break,
            };
            if t.trivia {
                self.eat(&mut c);
                continue;
            }
            if t.kind == tk::NEWLINE {
                if self.next_significant_is_one_of(&["@", "#"]) {
                    break;
                }
                self.eat(&mut c);
                continue;
            }
            let text = t.span.text(self.src);
            match text {
                ";" => {
                    self.eat(&mut c);
                    break;
                }
                "{" => {
                    let g = self.parse_group();
                    c.push(Child::Node(g));
                    break;
                }
                "(" | "[" => {
                    let g = self.parse_group();
                    c.push(Child::Node(g));
                }
                "@" | "#" => break,
                ")" | "]" | "}" => self.eat(&mut c), // stray closer: keep, advance
                _ => self.eat(&mut c),
            }
        }
        self.make_node(node::METHOD, c)
    }

    /// `@property (attrs) Type *name;` → a `Property` item.
    fn parse_property(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // '@'
        self.ws(&mut c);
        self.eat(&mut c); // 'property'
        loop {
            let t = match self.toks.get(self.i) {
                Some(t) => t,
                None => break,
            };
            if t.trivia {
                self.eat(&mut c);
                continue;
            }
            if t.kind == tk::NEWLINE {
                if self.next_significant_is_one_of(&["@", "#"]) {
                    break;
                }
                self.eat(&mut c);
                continue;
            }
            let text = t.span.text(self.src);
            match text {
                ";" => {
                    self.eat(&mut c);
                    break;
                }
                "(" | "[" | "{" => {
                    let g = self.parse_group();
                    c.push(Child::Node(g));
                }
                "@" | "#" => break,
                _ => self.eat(&mut c),
            }
        }
        let name_idx = last_name_idx(&c, self.src, &["property"]);
        let c = wrap_name(c, name_idx);
        self.make_node(node::PROPERTY, c)
    }

    /// A member `@`-directive that is not `@property` or `@end`: `@optional` /
    /// `@required` (section markers, no `;`), `@synthesize x;`, `@dynamic y;`, etc.
    fn parse_member_at_directive(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // '@'
        self.ws(&mut c);
        let word = self.peek_text().map(|s| s.to_string());
        self.eat(&mut c); // the directive word
        if matches!(word.as_deref(), Some("optional") | Some("required")) {
            return self.make_node(node::OBJC_DIRECTIVE, c);
        }
        loop {
            let t = match self.toks.get(self.i) {
                Some(t) => t,
                None => break,
            };
            if t.trivia {
                self.eat(&mut c);
                continue;
            }
            if t.kind == tk::NEWLINE {
                if self.next_significant_is_one_of(&["@", "#"]) {
                    break;
                }
                self.eat(&mut c);
                continue;
            }
            let text = t.span.text(self.src);
            match text {
                ";" => {
                    self.eat(&mut c);
                    break;
                }
                "(" | "[" | "{" => {
                    let g = self.parse_group();
                    c.push(Child::Node(g));
                }
                "@" | "#" => break,
                _ => self.eat(&mut c),
            }
        }
        self.make_node(node::OBJC_DIRECTIVE, c)
    }

    // --- the C declaration layer --------------------------------------------

    /// Collect and classify one C declaration unit (the C parser's algorithm,
    /// extended to stop at a line-leading `@` so it never swallows `@end`,
    /// `@property`, or a following `@interface`).
    fn parse_decl(&mut self) -> Node {
        let mut c: Vec<Child> = Vec::new();
        let mut saw_paren = false;
        let mut saw_eq = false;
        let mut aggr: Option<&'static str> = None;
        let mut is_typedef = false;
        let mut is_func_def = false;
        let mut has_brace_body = false;
        let mut started = false;

        loop {
            self.ws(&mut c);
            let (kind, text) = match self.toks.get(self.i) {
                Some(t) => (t.kind, t.span.text(self.src)),
                None => break,
            };
            if kind == tk::NEWLINE {
                if started && self.next_significant_is_one_of(&["#", "@"]) {
                    break;
                }
                self.eat(&mut c);
                continue;
            }
            match text {
                ";" => {
                    self.eat(&mut c);
                    break;
                }
                "{" => {
                    let func_body = saw_paren && !saw_eq;
                    let g = self.parse_group();
                    c.push(Child::Node(g));
                    has_brace_body = true;
                    started = true;
                    if func_body {
                        is_func_def = true;
                        self.maybe_eat_trailing_semi(&mut c);
                        break;
                    }
                }
                "(" => {
                    saw_paren = true;
                    let g = self.parse_group();
                    c.push(Child::Node(g));
                    started = true;
                }
                "[" => {
                    let g = self.parse_group();
                    c.push(Child::Node(g));
                    started = true;
                }
                "=" => {
                    saw_eq = true;
                    self.eat(&mut c);
                    started = true;
                }
                ")" | "]" | "}" => {
                    self.eat(&mut c);
                    started = true;
                }
                "#" => {
                    if started {
                        break;
                    }
                    self.eat(&mut c);
                    started = true;
                }
                "@" => {
                    // A line-leading `@` was already handled by the NEWLINE guard;
                    // an inline `@` (`@[`, `@(`, `@selector`, …) is part of this
                    // declaration's initializer, so consume it and continue.
                    self.eat(&mut c);
                    started = true;
                }
                _ => {
                    if kind == tk::IDENT {
                        match text {
                            "typedef" => is_typedef = true,
                            "struct" => aggr = Some("struct"),
                            "union" => aggr = Some("union"),
                            "enum" => aggr = Some("enum"),
                            _ => {}
                        }
                    }
                    self.eat(&mut c);
                    started = true;
                }
            }
        }

        if c.is_empty() {
            return self.make_node(node::ERROR_ITEM, c);
        }

        let kind = if is_func_def {
            node::FUNCTION
        } else if is_typedef {
            node::TYPEDEF
        } else if let Some(kw) = aggr {
            if has_brace_body || is_forward_aggregate(&c, self.src) {
                match kw {
                    "struct" => node::STRUCT,
                    "union" => node::UNION,
                    _ => node::ENUM,
                }
            } else {
                node::DECL
            }
        } else {
            node::DECL
        };

        let name_idx = match kind {
            node::FUNCTION => function_name_idx(&c, self.src),
            node::TYPEDEF => last_name_idx(&c, self.src, &[]),
            node::STRUCT | node::UNION | node::ENUM => tag_name_idx(&c, self.src),
            node::DECL => decl_name_idx(&c, self.src),
            _ => None,
        };
        let c = wrap_name(c, name_idx);
        self.make_node(kind, c)
    }

    fn maybe_eat_trailing_semi(&mut self, out: &mut Vec<Child>) {
        if self.at(";") {
            self.ws(out);
            self.eat(out);
        }
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`. The cursor is
    /// at the opener. Depth-guarded: beyond [`MAX_DEPTH`] the nested group is
    /// flattened rather than recursed, so deep nesting cannot overflow.
    fn parse_group(&mut self) -> Node {
        let mut g = Vec::new();
        let (close, label) = match self.toks.get(self.i).map(|t| t.span.text(self.src)) {
            Some("(") => (")", node::PAREN),
            Some("[") => ("]", node::BRACKET),
            Some("{") => ("}", node::BRACE),
            _ => (")", node::PAREN),
        };
        self.eat(&mut g); // opener
        loop {
            self.ws(&mut g);
            let text = match self.toks.get(self.i) {
                Some(t) => t.span.text(self.src),
                None => break, // unterminated; still lossless
            };
            if text == close {
                self.eat(&mut g);
                break;
            }
            match text {
                "(" | "[" | "{" => {
                    if self.depth < MAX_DEPTH {
                        self.depth += 1;
                        let inner = self.parse_group();
                        self.depth -= 1;
                        g.push(Child::Node(inner));
                    } else {
                        self.eat(&mut g); // opener
                        self.consume_balanced_flat(&mut g);
                        self.note_depth_limit();
                    }
                }
                _ => self.eat(&mut g),
            }
        }
        self.make_node(label, g)
    }

    /// Iteratively consume a balanced delimiter run (opener already eaten),
    /// appending every token as a flat leaf. Used at the depth cap.
    fn consume_balanced_flat(&mut self, out: &mut Vec<Child>) {
        let mut balance: i32 = 1;
        while balance > 0 {
            self.ws(out);
            let text = match self.toks.get(self.i) {
                Some(t) => t.span.text(self.src),
                None => break,
            };
            match text {
                "(" | "[" | "{" => balance += 1,
                ")" | "]" | "}" => balance -= 1,
                _ => {}
            }
            self.eat(out);
        }
    }

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "objc.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; region flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }
}

// --- classification helpers (pure over the collected children) --------------

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

/// Text of a non-trivia identifier-token child, if that is what `c` is.
fn ident_tok_text<'a>(c: &'a Child, src: &'a str) -> Option<&'a str> {
    if let Child::Token(t) = c {
        if !t.trivia && t.kind == tk::IDENT {
            return Some(t.span.text(src));
        }
    }
    None
}

/// True for `struct S;` / `enum E;` style forward declarations.
fn is_forward_aggregate(c: &[Child], src: &str) -> bool {
    let mut idents = 0;
    for ch in c {
        match ch {
            Child::Node(_) => return false,
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => {
                let tx = t.span.text(src);
                if tx == "=" {
                    return false;
                }
                if t.kind == tk::IDENT && !is_keyword(tx) {
                    idents += 1;
                }
            }
        }
    }
    idents == 1
}

/// Index of the function-name identifier: the last non-keyword identifier before
/// the first top-level parameter `Paren` group.
fn function_name_idx(c: &[Child], src: &str) -> Option<usize> {
    let paren = c
        .iter()
        .position(|ch| matches!(ch, Child::Node(n) if n.kind == node::PAREN))?;
    (0..paren).rev().find(|&i| {
        ident_tok_text(&c[i], src)
            .map(|t| !is_keyword(t))
            .unwrap_or(false)
    })
}

/// Index of the last top-level non-keyword identifier, optionally excluding a set
/// of directive words. Used for typedef aliases and `@property` names.
fn last_name_idx(c: &[Child], src: &str, exclude: &[&str]) -> Option<usize> {
    (0..c.len()).rev().find(|&i| {
        ident_tok_text(&c[i], src)
            .map(|t| !is_keyword(t) && !exclude.contains(&t))
            .unwrap_or(false)
    })
}

/// Index of an aggregate tag: the first non-keyword identifier following the
/// `struct`/`union`/`enum` keyword, or `None` if anonymous.
fn tag_name_idx(c: &[Child], src: &str) -> Option<usize> {
    let kw = c.iter().position(|ch| {
        ident_tok_text(ch, src)
            .map(|t| matches!(t, "struct" | "union" | "enum"))
            .unwrap_or(false)
    })?;
    for (i, ch) in c.iter().enumerate().skip(kw + 1) {
        match ch {
            Child::Token(t) if t.trivia => continue,
            Child::Token(t) if t.kind == tk::IDENT && !is_keyword(t.span.text(src)) => {
                return Some(i);
            }
            _ => return None,
        }
    }
    None
}

/// Index of a plain declaration's name: the last non-keyword identifier before the
/// first top-level `=`, bracket, or parameter group.
fn decl_name_idx(c: &[Child], src: &str) -> Option<usize> {
    let mut boundary = c.len();
    for (i, ch) in c.iter().enumerate() {
        match ch {
            Child::Token(t) if !t.trivia && t.span.text(src) == "=" => {
                boundary = i;
                break;
            }
            Child::Node(n) if n.kind == node::BRACKET || n.kind == node::PAREN => {
                boundary = i;
                break;
            }
            _ => {}
        }
    }
    (0..boundary).rev().find(|&i| {
        ident_tok_text(&c[i], src)
            .map(|t| !is_keyword(t))
            .unwrap_or(false)
    })
}

/// Index of the container's class/protocol name: the first non-keyword identifier
/// following the `interface`/`implementation`/`protocol` directive word.
fn container_name_idx(c: &[Child], src: &str) -> Option<usize> {
    let kw = c.iter().position(|ch| {
        ident_tok_text(ch, src)
            .map(|t| matches!(t, "interface" | "implementation" | "protocol"))
            .unwrap_or(false)
    })?;
    (kw + 1..c.len()).find(|&i| {
        ident_tok_text(&c[i], src)
            .map(|t| !is_keyword(t))
            .unwrap_or(false)
    })
}

/// Wrap the child at `idx` (an identifier token) in a `Name` node so the lowering
/// can find the definition's name without re-deriving its position.
fn wrap_name(mut c: Vec<Child>, idx: Option<usize>) -> Vec<Child> {
    if let Some(i) = idx {
        if let Some(Child::Token(t)) = c.get(i) {
            let t = t.clone();
            c[i] = Child::Node(Node::new(node::NAME, t.span, vec![Child::Token(t)]));
        }
    }
    c
}

#[cfg(test)]
mod tests {
    use super::*;

    fn name_of(item: &Node, src: &str) -> Option<String> {
        item.child(node::NAME)
            .and_then(|n| n.tokens().next())
            .map(|t| t.span.text(src).to_string())
    }

    #[test]
    fn parses_and_is_lossless() {
        let src = "\
/* an Objective-C translation unit */
#import <Foundation/Foundation.h>
#import \"Greeter.h\"

#define TAG @\"app\"

@protocol Named <NSObject>
- (NSString *)name;
@end

@interface Greeter : NSObject <Named> {
    int _count;
}
@property (nonatomic, copy) NSString *name;
+ (instancetype)greeterWithName:(NSString *)name;
- (void)greet:(NSString *)who loudly:(BOOL)loud;
@end

@implementation Greeter
- (void)greet:(NSString *)who loudly:(BOOL)loud {
    NSString *msg = [NSString stringWithFormat:@\"hi %@\", who];
    NSLog(@\"%@\", msg);
}
@end

static int counter(void) {
    return 0;
}
";
        let tree = parse("Greeter.m", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "#import <Foundation/Foundation.h>\n@interface A : NSObject\n@end\n@implementation A\n@end\nint f(void) { return 0; }\n";
        let tree = parse("t.m", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::INCLUDE), "import: {kinds:?}");
        assert!(kinds.contains(&node::INTERFACE), "interface: {kinds:?}");
        assert!(kinds.contains(&node::IMPLEMENTATION), "impl: {kinds:?}");
        assert!(kinds.contains(&node::FUNCTION), "function: {kinds:?}");
    }

    #[test]
    fn interface_has_name_super_and_members() {
        let src = "@interface Dog : Animal <Pet>\n- (void)bark;\n@property int age;\n@end\n";
        let tree = parse("t.m", src);
        let iface = tree
            .root
            .children_of(node::INTERFACE)
            .next()
            .expect("an interface");
        assert_eq!(name_of(iface, src).as_deref(), Some("Dog"));
        assert!(iface.child(node::METHOD).is_some(), "has a method");
        assert!(iface.child(node::PROPERTY).is_some(), "has a property");
    }

    #[test]
    fn method_definition_has_body() {
        let src = "@implementation C\n- (int)add:(int)a to:(int)b {\n    return a + b;\n}\n@end\n";
        let tree = parse("t.m", src);
        let imp = tree
            .root
            .children_of(node::IMPLEMENTATION)
            .next()
            .expect("impl");
        let m = imp.child(node::METHOD).expect("a method");
        assert!(m.child(node::BRACE).is_some(), "method body is a Brace");
    }

    #[test]
    fn protocol_forward_declaration() {
        let src = "@protocol Fwd;\n@interface X : NSObject\n@end\n";
        let tree = parse("t.m", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(
            kinds.contains(&node::PROTOCOL),
            "forward protocol: {kinds:?}"
        );
        assert!(kinds.contains(&node::INTERFACE), "interface: {kinds:?}");
        assert!(tree.is_lossless());
    }

    #[test]
    fn class_and_import_directives() {
        let src = "@class Foo, Bar;\n@import Foundation;\n";
        let tree = parse("t.m", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::CLASS_DIRECTIVE), "@class: {kinds:?}");
        assert!(kinds.contains(&node::OBJC_IMPORT), "@import: {kinds:?}");
    }

    #[test]
    fn member_directive_does_not_escape_container() {
        let src = "@interface A : NSObject\n@required\n- (void)a;\n@optional\n- (void)b;\n@end\nint outside(void){return 0;}\n";
        let tree = parse("t.m", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        // The function after @end must be a *top-level* item, not swallowed.
        assert!(
            kinds.contains(&node::FUNCTION),
            "function escapes: {kinds:?}"
        );
        assert!(tree.is_lossless());
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let deep = format!(
            "int f(void) {{ return {}{}; }}\n",
            "(".repeat(10_000),
            ")".repeat(10_000)
        );
        let tree = parse("deep.m", &deep);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics
                .iter()
                .any(|d| d.code == "objc.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }

    #[test]
    fn edge_cases_round_trip() {
        for src in [
            "",                                  // empty file
            "\n\n   \n/* trailing */\n",         // only blanks and comments
            "NSArray *a = @[ @1, @2 ];\n",       // objc array literal
            "id s = @\"oops\nint y;\n",          // unterminated objc string
            "λ = @\"☃\";  // unicode\n",         // multi-byte
            "@interface Orphan : NSObject\n",    // missing @end (EOF)
            "[obj msg:[other thing] with:x];\n", // nested message sends
            "@end\n",                            // stray @end
            "- (void)loose;\n",                  // method at top level (no container)
        ] {
            let tree = parse("edge.m", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
