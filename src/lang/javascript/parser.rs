//! JavaScript parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust and Python parsers: definition *headers* are parsed
//! precisely — we always know a `function`'s name, a `class`'s `extends` clause,
//! an `import`'s specifier, a method's name — while bodies and expression regions
//! are captured as balanced **token-tree groups** (`Paren`/`Bracket`/`Brace`/
//! `Block`) plus flat tokens, which is perfectly lossless. Graph facts (calls,
//! base classes, imports) are extracted from these real tokens in the lowering
//! pass, never invented.
//!
//! JavaScript has no significant indentation and no mandatory semicolons. The one
//! structural wrinkle is **ASI** (automatic semicolon insertion): an
//! expression/declaration statement ends at the first `;`, the enclosing `}`, or
//! a line terminator at bracket depth 0. The lexer emits line terminators as
//! `newline` trivia, so the parser recovers these boundaries without the lexer
//! fabricating tokens. ASI guesses can only over- or under-split *statements*;
//! they never drop bytes (the tree always round-trips) and never lose a call
//! (the lowering scans every statement's tokens).
//!
//! Anything unrecognized still lands in the tree as its exact tokens (an
//! `ErrorItem` node or a flat `Statement` run), so the result always round-trips
//! byte-for-byte. The recursion is depth-guarded at [`MAX_DEPTH`] against hostile
//! nesting — both bracket nesting and class-body nesting — because a
//! `catch_unwind` cannot catch a stack overflow.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::javascript::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const IMPORT: &str = "Import";
    pub const FUNCTION: &str = "Function";
    pub const CLASS: &str = "Class";
    pub const CLASS_BODY: &str = "ClassBody";
    pub const METHOD: &str = "Method";
    pub const FIELD: &str = "Field";
    pub const VAR_DECL: &str = "VarDecl";
    pub const STATEMENT: &str = "Statement";
    pub const DECORATOR: &str = "Decorator";
    pub const ERROR_ITEM: &str = "ErrorItem";

    pub const NAME: &str = "Name";
    pub const HEADER: &str = "Header";
    pub const PARAMS: &str = "Params";
    pub const BLOCK: &str = "Block";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat balanced run. Mirrors the Rust/Python guard exactly, since
/// a `catch_unwind` cannot catch a stack overflow.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = JsParser {
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

struct JsParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> JsParser<'s> {
    // --- cursor primitives --------------------------------------------------

    /// Append the current token (trivia or not) to `out` and advance.
    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading trivia (whitespace, comments, **and newlines**)
    /// into `out`. Used everywhere newlines are insignificant (item boundaries,
    /// definition headers).
    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
        }
    }

    /// Move leading *same-line* trivia (whitespace, comments) into `out`, stopping
    /// at a `newline`. Used inside statement collectors so an ASI boundary is
    /// preserved for the caller.
    fn ws_inline(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len()
            && self.toks[self.i].trivia
            && self.toks[self.i].kind != tk::NEWLINE
        {
            self.eat(out);
        }
    }

    /// True if a `newline` trivia precedes the next significant token (an ASI
    /// boundary at the cursor).
    fn pending_newline(&self) -> bool {
        let mut j = self.i;
        while j < self.toks.len() && self.toks[j].trivia {
            if self.toks[j].kind == tk::NEWLINE {
                return true;
            }
            j += 1;
        }
        false
    }

    /// Kind of the n-th significant (non-trivia) token from the cursor.
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

    fn peek_text(&self) -> Option<&str> {
        self.peek_n_text(0)
    }

    fn at(&self, s: &str) -> bool {
        self.peek_text() == Some(s)
    }

    fn at_n(&self, n: usize, s: &str) -> bool {
        self.peek_n_text(n) == Some(s)
    }

    fn at_open(&self) -> bool {
        self.at("(") || self.at("[") || self.at("{")
    }

    fn at_name(&self) -> bool {
        self.peek_kind() == Some(tk::NAME)
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

    fn parse_item(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);

        // Leading decorators (`@expr` lines) attach to the class/declaration.
        while self.at("@") {
            let d = self.parse_decorator();
            c.push(Child::Node(d));
            self.ws(&mut c);
        }

        if self.at("export") {
            return self.finish_export(c);
        }
        self.dispatch(c)
    }

    /// Dispatch on the leading keyword after any `export`/decorator prefix.
    fn dispatch(&mut self, c: Vec<Child>) -> Node {
        if self.at_function() {
            self.finish_function(c)
        } else if self.at("class") {
            self.finish_class(c)
        } else if self.at("import") && self.import_is_declaration() {
            self.finish_import(c)
        } else if self.at("const") || self.at("let") || self.at("var") {
            self.finish_var(c)
        } else {
            self.finish_statement(c)
        }
    }

    /// `import` is a declaration unless it is the `import(...)` dynamic form or
    /// the `import.meta` member expression.
    fn import_is_declaration(&self) -> bool {
        !matches!(self.peek_n_text(1), Some("(") | Some("."))
    }

    fn at_function(&self) -> bool {
        self.at("function") || (self.at("async") && self.at_n(1, "function"))
    }

    // --- exports ------------------------------------------------------------

    fn finish_export(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // export
        self.ws(&mut c);

        if self.at("default") {
            self.eat(&mut c); // default
            self.ws(&mut c);
            if self.at_function() {
                return self.finish_function(c);
            }
            if self.at("class") {
                return self.finish_class(c);
            }
            return self.finish_statement(c); // export default <expr>
        }

        // `export { a, b as c } from "m"` / `export * from "m"` / `export { a }`.
        // Captured as an Import node so a `from` specifier becomes a dependency;
        // a bare `export { a }` simply carries no specifier and the lowering skips
        // emitting an import edge.
        if self.at("{") || self.at("*") {
            if let Some(h) = self.collect_stmt(node::HEADER) {
                c.push(Child::Node(h));
            }
            self.ws_inline(&mut c);
            if self.at(";") {
                self.eat(&mut c);
            }
            return self.make_node(node::IMPORT, c);
        }

        // `export function … / class … / const … / let … / var …`.
        self.dispatch(c)
    }

    // --- definitions --------------------------------------------------------

    /// `[async] function [*] NAME (params) { body }` (NAME optional for
    /// `export default function`).
    fn finish_function(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        if self.at("async") {
            self.eat(&mut c); // async
            self.ws(&mut c);
        }
        self.eat(&mut c); // function
        self.ws(&mut c);
        if self.at("*") {
            self.eat(&mut c); // generator
            self.ws(&mut c);
        }
        if self.at_name() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        self.ws(&mut c);
        if self.at("(") {
            let g = self.parse_delimited(Some(node::PARAMS));
            c.push(Child::Node(g));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
        } else if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::FUNCTION, c)
    }

    /// `class NAME extends Base { body }` (NAME optional for class expressions
    /// reached via `export default class`).
    fn finish_class(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // class
        self.ws(&mut c);
        if self.at_name() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(h) = self.collect_class_header() {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_class_body();
            c.push(Child::Node(b));
        }
        self.make_node(node::CLASS, c)
    }

    /// Collect a class header (`extends Base`, `implements …` in some dialects)
    /// up to the opening `{`. Newlines are insignificant here.
    fn collect_class_header(&mut self) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            match self.peek_kind() {
                None => break,
                _ if self.at("{") || self.at(";") => break,
                _ if self.at_open() => {
                    let g = self.parse_delimited(None);
                    c.push(Child::Node(g));
                }
                _ => self.eat(&mut c),
            }
        }
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(node::HEADER, c))
        }
    }

    /// Parse a class body `{ … }` as a list of members. Depth-guarded: beyond the
    /// cap the body is consumed as a flat balanced run rather than recursing.
    fn parse_class_body(&mut self) -> Node {
        if self.depth >= MAX_DEPTH {
            let mut c = Vec::new();
            self.ws(&mut c);
            self.eat(&mut c); // {
            self.consume_balanced_flat(&mut c);
            self.note_depth_limit();
            return self.make_node(node::CLASS_BODY, c);
        }
        self.depth += 1;
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // {
        loop {
            self.ws(&mut c);
            match self.peek_kind() {
                None => break,
                _ if self.at("}") => {
                    self.eat(&mut c);
                    break;
                }
                _ if self.at(";") => self.eat(&mut c), // empty member separator
                _ => {
                    let m = self.parse_member();
                    c.push(Child::Node(m));
                }
            }
        }
        let node = self.make_node(node::CLASS_BODY, c);
        self.depth -= 1;
        node
    }

    /// One class member: a method `name(params) { … }` or a field `name = expr;`.
    fn parse_member(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        while self.at("@") {
            let d = self.parse_decorator();
            c.push(Child::Node(d));
            self.ws(&mut c);
        }
        self.eat_member_modifiers(&mut c);
        self.ws(&mut c);
        if self.at("*") {
            self.eat(&mut c); // generator method
            self.ws(&mut c);
        }
        self.parse_member_name(&mut c);
        self.ws(&mut c);
        if self.at("(") {
            // Method.
            let g = self.parse_delimited(Some(node::PARAMS));
            c.push(Child::Node(g));
            self.ws(&mut c);
            if self.at("{") {
                let b = self.parse_delimited(Some(node::BLOCK));
                c.push(Child::Node(b));
            } else if self.at(";") {
                self.eat(&mut c);
            }
            self.make_node(node::METHOD, c)
        } else {
            // Field (`x`, `x = expr`, `#x = expr`).
            if let Some(h) = self.collect_stmt(node::HEADER) {
                c.push(Child::Node(h));
            }
            self.ws_inline(&mut c);
            if self.at(";") {
                self.eat(&mut c);
            }
            self.make_node(node::FIELD, c)
        }
    }

    /// Eat leading member modifiers (`static`, `get`, `set`, `async`). A modifier
    /// word is only a modifier when it is *not* itself the member name — e.g.
    /// `get()` is a method named `get`, `static = 1` a field named `static`.
    fn eat_member_modifiers(&mut self, c: &mut Vec<Child>) {
        loop {
            self.ws(c);
            let is_mod = matches!(
                self.peek_text(),
                Some("static") | Some("get") | Some("set") | Some("async")
            );
            if !is_mod {
                break;
            }
            if matches!(
                self.peek_n_text(1),
                Some("(") | Some("=") | Some(";") | Some("}")
            ) {
                break; // the word is the member name, not a modifier
            }
            self.eat(c);
        }
    }

    /// A member name: a computed `[expr]`, a private `#name`, or a plain
    /// identifier / string / numeric literal name.
    fn parse_member_name(&mut self, c: &mut Vec<Child>) {
        self.ws(c);
        if self.at("[") {
            let g = self.parse_delimited(Some(node::NAME));
            c.push(Child::Node(g));
            return;
        }
        if matches!(self.peek_kind(), Some(k) if is_member_name_kind(k)) {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
    }

    /// `import … from "module"` / `import "module"`. The whole clause + specifier
    /// is captured as a `Header`; the lowering reads the string specifier and the
    /// imported bindings off it.
    fn finish_import(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // import
        if let Some(h) = self.collect_stmt(node::HEADER) {
            c.push(Child::Node(h));
        }
        self.ws_inline(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::IMPORT, c)
    }

    /// `const|let|var NAME … ;` — a (possibly multi-line via groups) declaration.
    fn finish_var(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // const/let/var
        if let Some(h) = self.collect_stmt(node::HEADER) {
            c.push(Child::Node(h));
        }
        self.ws_inline(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::VAR_DECL, c)
    }

    /// A generic statement (expression statement, control flow, block, …): the
    /// real tokens up to the ASI boundary, with calls recoverable from them.
    fn finish_statement(&mut self, mut c: Vec<Child>) -> Node {
        match self.collect_stmt(node::STATEMENT) {
            Some(h) => c.push(Child::Node(h)),
            None => {
                // Guarantee progress on an otherwise-empty statement.
                self.ws_inline(&mut c);
                // Eat one token (the `;` or any other) to guarantee progress.
                if self.peek_kind().is_some() {
                    self.eat(&mut c);
                }
            }
        }
        self.ws_inline(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::STATEMENT, c)
    }

    /// A decorator expression `@name`, `@ns.name`, `@name(args)`, or `@(expr)`.
    /// Kept deliberately narrow so a same-line `@dec class X {}` does not swallow
    /// the class.
    fn parse_decorator(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // @
        self.ws(&mut c);
        if self.at("(") {
            let g = self.parse_delimited(None);
            c.push(Child::Node(g));
            return self.make_node(node::DECORATOR, c);
        }
        if self.at_name() {
            self.eat(&mut c); // leading identifier
        }
        loop {
            self.ws(&mut c);
            if self.at(".") {
                self.eat(&mut c);
                self.ws(&mut c);
                if self.at_name() {
                    self.eat(&mut c);
                }
            } else if self.at("(") {
                let g = self.parse_delimited(None);
                c.push(Child::Node(g));
            } else {
                break;
            }
        }
        self.make_node(node::DECORATOR, c)
    }

    // --- shared helpers -----------------------------------------------------

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.eat(&mut c); // the name token (cursor is at it after caller ws)
        self.make_node(node::NAME, c)
    }

    /// Collect a statement region: tokens (descending into balanced groups) up to
    /// a `;`, an enclosing `}`, or an ASI line-terminator boundary at bracket
    /// depth 0. The terminating `;` (if any) stays with the caller.
    fn collect_stmt(&mut self, label: &'static str) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            if self.pending_newline() {
                break; // ASI boundary
            }
            self.ws_inline(&mut c);
            match self.peek_kind() {
                None => break,
                _ if self.at(";") => break,
                _ if self.at("}") => break,
                _ if self.at_open() => {
                    let g = self.parse_delimited(None);
                    c.push(Child::Node(g));
                }
                _ => self.eat(&mut c),
            }
        }
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(label, c))
        }
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`. Cursor is at
    /// (or before trivia preceding) the opener. Newlines inside the group are
    /// ordinary content.
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
            match self.peek_text() {
                None => break,
                Some("(") | Some("[") | Some("{") => balance += 1,
                Some(")") | Some("]") | Some("}") => balance -= 1,
                _ => {}
            }
            self.eat(out);
        }
    }

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "javascript.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; region flattened"),
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

/// Token kinds that can name a class member (a plain identifier, a private name,
/// or a string/numeric literal member name).
fn is_member_name_kind(k: &str) -> bool {
    k == tk::NAME || k == tk::PRIVATE_NAME || k == tk::STRING || k == tk::INT || k == tk::FLOAT
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_and_is_lossless() {
        let src = "\
// a module
import { readFile } from 'fs';
import React from 'react';

export const VERSION = '1.0';

@sealed
export class Point extends Base {
  #scale = 1;
  static origin = new Point(0, 0);

  constructor(x, y) {
    this.x = x;
    this.y = y;
  }

  async norm() {
    return Math.sqrt(this.x * this.x + this.y * this.y);
  }

  get scaled() { return this.x * this.#scale; }
}

export default function add(a, b) {
  if (a > b) {
    return a;
  }
  return helper(b);
}

const tagged = `value=${ add(1, 2) }`;
";
        let tree = parse("mod.js", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "import x from 'm';\nclass C { m() {} }\nfunction f() {}\nconst k = 1;\n";
        let tree = parse("t.js", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::IMPORT), "import not found: {kinds:?}");
        assert!(kinds.contains(&node::CLASS), "class not found: {kinds:?}");
        assert!(
            kinds.contains(&node::FUNCTION),
            "function not found: {kinds:?}"
        );
        assert!(kinds.contains(&node::VAR_DECL), "var not found: {kinds:?}");
    }

    #[test]
    fn methods_nest_inside_class_body() {
        let src = "class C {\n  a() {}\n  b() {}\n}\n";
        let tree = parse("t.js", src);
        let class = tree
            .root
            .children_of(node::CLASS)
            .next()
            .expect("a class node");
        let body = class.child(node::CLASS_BODY).expect("class has a body");
        let methods: Vec<&str> = body
            .children_of(node::METHOD)
            .filter_map(|m| m.child(node::NAME))
            .filter_map(|n| n.tokens().next())
            .map(|t| t.span.text(src))
            .collect();
        assert_eq!(methods, vec!["a", "b"]);
    }

    #[test]
    fn asi_separates_unterminated_declarations() {
        // No semicolons, two separate top-level functions and a const.
        let src = "const a = 1\nfunction f() {}\nconst b = 2\n";
        let tree = parse("t.js", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(
            kinds.contains(&node::FUNCTION),
            "f must be its own item: {kinds:?}"
        );
        assert_eq!(
            kinds.iter().filter(|k| **k == node::VAR_DECL).count(),
            2,
            "two separate var decls: {kinds:?}"
        );
        assert!(tree.is_lossless());
    }

    #[test]
    fn export_default_function_is_a_function() {
        let src = "export default function () { return 1; }\n";
        let tree = parse("t.js", src);
        assert!(tree.root.children_of(node::FUNCTION).next().is_some());
        assert!(tree.is_lossless());
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let deep_parens = format!("const x = {}{};\n", "(".repeat(10_000), ")".repeat(10_000));
        let mut deep_classes = String::new();
        // Deeply nested braces via class bodies and blocks.
        deep_classes.push_str(&"class C { m() { ".repeat(2_000));
        deep_classes.push_str(&"} }".repeat(2_000));
        for src in [deep_parens, deep_classes] {
            let tree = parse("deep.js", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics
                    .iter()
                    .any(|d| d.code == "javascript.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "const x = (1, 2\n",         // unterminated paren
            "let λ = '☃'; // unicode\n", // multi-byte identifiers/strings
            "",                          // empty file
            "\n\n   \n// trailing\n",    // only blanks and comments
            "const t = `a${ b",          // unterminated template + interp
        ] {
            let tree = parse("edge.js", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
