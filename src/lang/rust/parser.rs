//! Rust parser producing the language-neutral lossless CST.
//!
//! Strategy (honest, breadth-growable): item *headers* are parsed precisely —
//! we always know a function's name, a struct's name, a `use` path, etc. Item
//! *bodies* and expression regions are captured as balanced **token trees**
//! (`Paren`/`Bracket`/`Brace`/`Block` groups), which are a real part of Rust's
//! grammar (macro token streams) and are perfectly lossless. `impl`, `trait`,
//! `mod`, and `extern {}` bodies are recursively parsed as item lists so nested
//! definitions stay first-class.
//!
//! Graph facts (calls, type refs) are extracted from these real token trees in
//! the lowering pass — never invented. Anything unrecognized becomes an
//! `ErrorItem` node that still contains its exact source tokens.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::rust::lexer::{self, kind as tk, lex};

/// CST node-kind labels. Typed views interpret these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const FUNCTION: &str = "Function";
    pub const STRUCT: &str = "Struct";
    pub const UNION: &str = "Union";
    pub const ENUM: &str = "Enum";
    pub const TRAIT: &str = "Trait";
    pub const IMPL: &str = "Impl";
    pub const MODULE: &str = "Module";
    pub const USE: &str = "Use";
    pub const CONST: &str = "Const";
    pub const STATIC: &str = "Static";
    pub const TYPE_ALIAS: &str = "TypeAlias";
    pub const EXTERN_CRATE: &str = "ExternCrate";
    pub const EXTERN_BLOCK: &str = "ExternBlock";
    pub const MACRO_DEF: &str = "MacroDef";
    pub const MACRO_CALL: &str = "MacroCall";
    pub const ERROR_ITEM: &str = "ErrorItem";

    pub const NAME: &str = "Name";
    pub const HEADER: &str = "Header";
    pub const SIGNATURE: &str = "Signature";
    pub const USE_TREE: &str = "UseTree";
    pub const ITEM_BLOCK: &str = "ItemBlock";

    pub const BLOCK: &str = "Block";
    pub const FIELD_LIST: &str = "FieldList";
    pub const TUPLE_FIELDS: &str = "TupleFields";
    pub const VARIANT_LIST: &str = "VariantList";
    pub const VISIBILITY: &str = "Visibility";
    pub const ATTR: &str = "Attr";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remaining group iteratively. Protects against stack overflow on pathological
/// or hostile inputs (deeply nested delimiters) — a `catch_unwind` cannot catch
/// a stack overflow, so this guard is the real defense. The limit is far beyond
/// any realistic source while staying well clear of the default stack.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = RustParser {
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

struct RustParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> RustParser<'s> {
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

    /// Kind of the next significant token (no borrow of source).
    fn peek_kind(&self) -> Option<&'static str> {
        let mut j = self.i;
        while j < self.toks.len() && self.toks[j].trivia {
            j += 1;
        }
        self.toks.get(j).map(|t| t.kind)
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
        matches!(self.peek_kind(), Some(k) if k == tk::IDENT || k == tk::RAW_IDENT)
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

    /// Parse `{ items }` as a recursive item list.
    fn parse_item_block(&mut self, label: &'static str) -> Node {
        // Depth guard: beyond the cap, stop recursing into items and consume the
        // body as a flat balanced token run. Lossless, never a stack overflow.
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

        // Outer attributes: `#[...]` / `#![...]`.
        loop {
            self.ws(&mut c);
            if self.at("#") {
                self.parse_attr(&mut c);
            } else {
                break;
            }
        }

        // Visibility: `pub` or `pub(...)`.
        self.ws(&mut c);
        if self.at("pub") {
            self.eat(&mut c);
            self.ws(&mut c);
            if self.at("(") {
                let g = self.parse_delimited(None);
                c.push(Child::Node(g));
            }
        }

        // Leading modifiers that precede the item keyword.
        loop {
            self.ws(&mut c);
            if self.at("async") || self.at("unsafe") || self.at("default") || self.at("move") {
                self.eat(&mut c);
            } else if self.at("const") && self.at_n(1, "fn") {
                self.eat(&mut c); // const (as fn modifier)
            } else if self.at("extern") && !self.at_n(1, "crate") {
                self.eat(&mut c); // extern
                self.ws(&mut c);
                if matches!(self.peek_kind(), Some(k) if k == tk::STRING) {
                    self.eat(&mut c); // abi string
                }
            } else {
                break;
            }
        }

        // Dispatch on the item keyword.
        self.ws(&mut c);
        if self.at("fn") {
            self.finish_fn(c)
        } else if self.at("struct") {
            self.finish_struct_like(c, node::STRUCT)
        } else if self.at("union") && self.next_is_ident() {
            self.finish_struct_like(c, node::UNION)
        } else if self.at("enum") {
            self.finish_enum(c)
        } else if self.at("trait") {
            self.finish_trait(c)
        } else if self.at("impl") {
            self.finish_impl(c)
        } else if self.at("mod") {
            self.finish_mod(c)
        } else if self.at("use") {
            self.finish_use(c)
        } else if self.at("type") {
            self.finish_type_alias(c)
        } else if self.at("static") {
            self.finish_named_until(c, node::STATIC, &[";"], true)
        } else if self.at("const") {
            self.finish_named_until(c, node::CONST, &[";"], true)
        } else if self.at("extern") {
            self.finish_extern_crate(c)
        } else if self.at("{") {
            // Reached after `extern "C"` modifiers — a foreign block.
            self.finish_extern_block(c)
        } else if self.at("macro_rules") && self.at_n(1, "!") {
            self.finish_macro_def(c)
        } else if self.at_ident() && self.at_n(1, "!") {
            self.finish_macro_call(c)
        } else {
            self.finish_error_item(c)
        }
    }

    fn parse_attr(&mut self, c: &mut Vec<Child>) {
        self.ws(c);
        self.eat(c); // #
        self.ws(c);
        if self.at("!") {
            self.eat(c);
            self.ws(c);
        }
        if self.at("[") {
            let g = self.parse_delimited(Some(node::ATTR));
            c.push(Child::Node(g));
        }
    }

    fn finish_fn(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // fn
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(sig) = self.collect_region(node::SIGNATURE, &["{", ";"]) {
            c.push(Child::Node(sig));
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

    fn finish_struct_like(&mut self, mut c: Vec<Child>, kind: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // struct/union
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(h) = self.collect_region(node::HEADER, &["{", "(", ";"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_delimited(Some(node::FIELD_LIST));
            c.push(Child::Node(b));
        } else if self.at("(") {
            let b = self.parse_delimited(Some(node::TUPLE_FIELDS));
            c.push(Child::Node(b));
            self.ws(&mut c);
            if self.at(";") {
                self.eat(&mut c);
            }
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
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(h) = self.collect_region(node::HEADER, &["{"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_delimited(Some(node::VARIANT_LIST));
            c.push(Child::Node(b));
        }
        self.make_node(node::ENUM, c)
    }

    fn finish_trait(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // trait
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(h) = self.collect_region(node::HEADER, &["{", ";"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_item_block(node::ITEM_BLOCK);
            c.push(Child::Node(b));
        } else if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::TRAIT, c)
    }

    fn finish_impl(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // impl
        if let Some(h) = self.collect_region(node::HEADER, &["{"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_item_block(node::ITEM_BLOCK);
            c.push(Child::Node(b));
        }
        self.make_node(node::IMPL, c)
    }

    fn finish_mod(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // mod
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_item_block(node::ITEM_BLOCK);
            c.push(Child::Node(b));
        } else if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::MODULE, c)
    }

    fn finish_use(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // use
        if let Some(t) = self.collect_region(node::USE_TREE, &[";"]) {
            c.push(Child::Node(t));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::USE, c)
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

    /// `const NAME: T = expr;` / `static [mut] NAME: T = expr;`.
    fn finish_named_until(
        &mut self,
        mut c: Vec<Child>,
        kind: &'static str,
        stops: &[&str],
        terminator_semicolon: bool,
    ) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // const/static
        self.ws(&mut c);
        if self.at("mut") {
            self.eat(&mut c);
            self.ws(&mut c);
        }
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(h) = self.collect_region(node::HEADER, stops) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if terminator_semicolon && self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(kind, c)
    }

    fn finish_extern_crate(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // extern
        self.ws(&mut c);
        self.eat(&mut c); // crate
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
        self.make_node(node::EXTERN_CRATE, c)
    }

    fn finish_extern_block(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_item_block(node::ITEM_BLOCK);
            c.push(Child::Node(b));
        }
        self.make_node(node::EXTERN_BLOCK, c)
    }

    fn finish_macro_def(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // macro_rules
        self.ws(&mut c);
        self.eat(&mut c); // !
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        self.ws(&mut c);
        if self.at_open() {
            let g = self.parse_delimited(None);
            c.push(Child::Node(g));
        }
        self.make_node(node::MACRO_DEF, c)
    }

    fn finish_macro_call(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        self.ws(&mut c);
        if self.at("!") {
            self.eat(&mut c);
        }
        self.ws(&mut c);
        if self.at_open() {
            let g = self.parse_delimited(None);
            c.push(Child::Node(g));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::MACRO_CALL, c)
    }

    fn finish_error_item(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        if self.at_open() {
            let g = self.parse_delimited(None);
            c.push(Child::Node(g));
        } else {
            // Consume exactly one significant token to guarantee progress.
            self.eat(&mut c);
        }
        self.diags.push(Diagnostic {
            code: "rust.unrecognized_item",
            message: "token(s) not recognized as a Rust item".to_string(),
            span: children_span(&c).unwrap_or_else(|| ByteSpan::empty_at(self.cur_offset())),
        });
        self.make_node(node::ERROR_ITEM, c)
    }

    // --- shared helpers -----------------------------------------------------

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.eat(&mut c); // the identifier (cursor is at it after caller ws)
        self.make_node(node::NAME, c)
    }

    /// Collect tokens (descending into balanced groups) until a significant
    /// stop token at delimiter depth 0. Leading/trailing trivia around a stop
    /// stays with the parent.
    fn collect_region(&mut self, label: &'static str, stops: &[&str]) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            if self.peek_kind().is_none() {
                break;
            }
            if stops.iter().any(|s| self.at(s)) {
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
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(label, c))
        }
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`. Cursor is
    /// at (or before trivia preceding) the opener.
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
                    // Depth cap: flatten the nested group into this one rather
                    // than recursing. Lossless; protects against stack overflow.
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
    /// deep nesting is handled without further recursion. Balance counts all
    /// delimiter kinds uniformly; on unbalanced input it stops at EOF.
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
            code: "rust.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; group flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }

    /// Is the token after the cursor's current keyword an identifier? Used to
    /// disambiguate the contextual `union` keyword from an ordinary `union` use.
    fn next_is_ident(&self) -> bool {
        matches!(self.peek_kind_n(1), Some(k) if k == tk::IDENT || k == tk::RAW_IDENT)
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

/// Re-export so callers can name keyword helpers via the parser module too.
pub use lexer::is_keyword;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_and_is_lossless() {
        let src = "\
// a file
use std::fmt;

pub struct Point { x: i32, y: i32 }

impl Point {
    pub fn new(x: i32, y: i32) -> Point {
        Point { x, y }
    }
    fn sum(&self) -> i32 { add(self.x, self.y) }
}

fn add(a: i32, b: i32) -> i32 { a + b }
";
        let tree = parse("test.rs", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "fn a() {} struct B; enum C { X } trait T {} mod m { fn inner() {} }";
        let tree = parse("t.rs", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::FUNCTION));
        assert!(kinds.contains(&node::STRUCT));
        assert!(kinds.contains(&node::ENUM));
        assert!(kinds.contains(&node::TRAIT));
        assert!(kinds.contains(&node::MODULE));
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        // Far deeper than MAX_DEPTH; must not stack-overflow and must stay lossless.
        let depth = 10_000;
        let src = format!("fn x() {{ {}{} }}", "(".repeat(depth), ")".repeat(depth));
        let tree = parse("deep.rs", &src);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics
                .iter()
                .any(|d| d.code == "rust.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }

    #[test]
    fn nested_module_functions_are_items() {
        let src = "mod m { fn inner() {} }";
        let tree = parse("t.rs", src);
        let has_inner = tree.root.walk().any(|n| n.kind == node::FUNCTION);
        assert!(has_inner, "nested fn should be a Function node");
    }
}
