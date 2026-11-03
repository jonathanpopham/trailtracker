//! Java parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust parser ([`crate::lang::rust::parser`]): declaration
//! *headers* are parsed precisely — we always know a type's name and supertypes,
//! a method's name and parameter list, a field's name, an `import` path — while
//! method bodies and expression regions are captured as balanced **token-tree
//! groups** (`Paren`/`Bracket`/`Brace`) plus flat tokens, which is perfectly
//! lossless. Graph facts (calls, type refs) are extracted from these real token
//! trees in the lowering pass, never invented.
//!
//! Java members carry no leading keyword the way Rust items do (`fn`/`struct`):
//! a method is distinguished from a field by whether a `(` follows the declared
//! name. The parser collects the declarator prefix (modifiers, annotations, type,
//! name) and then branches on the first significant delimiter (`(` → method,
//! `=`/`;` → field, a type keyword → nested type).
//!
//! Anything unrecognized still lands in the tree as its exact tokens, so the
//! result always round-trips byte-for-byte. The recursion is depth-guarded at
//! [`MAX_DEPTH`] against hostile nesting (both nested types and nested
//! delimiters), because a `catch_unwind` cannot catch a stack overflow.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::java::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const COMPILATION_UNIT: &str = "CompilationUnit";
    pub const PACKAGE: &str = "Package";
    pub const IMPORT: &str = "Import";
    pub const CLASS: &str = "Class";
    pub const INTERFACE: &str = "Interface";
    pub const ENUM: &str = "Enum";
    pub const RECORD: &str = "Record";
    pub const ANNOTATION_TYPE: &str = "AnnotationType";
    pub const METHOD: &str = "Method";
    pub const FIELD: &str = "Field";
    pub const INIT_BLOCK: &str = "InitBlock";
    pub const ANNOTATION: &str = "Annotation";
    pub const ERROR_ITEM: &str = "ErrorItem";

    pub const NAME: &str = "Name";
    pub const HEADER: &str = "Header";
    pub const SIGNATURE: &str = "Signature";
    pub const PARAMS: &str = "Params";
    pub const FIELD_INIT: &str = "FieldInit";
    pub const ITEM_BLOCK: &str = "ItemBlock";

    pub const BLOCK: &str = "Block";
    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// The leading declaration modifiers recognized before a declarator. The soft
/// modifiers (`sealed`, `default`) are included; `non-sealed` is handled as a
/// special three-token sequence in [`JavaParser::parse_modifiers`].
const MODIFIER_KEYWORDS: &[&str] = &[
    "public",
    "private",
    "protected",
    "static",
    "final",
    "abstract",
    "native",
    "synchronized",
    "transient",
    "volatile",
    "strictfp",
    "default",
    "sealed",
];

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat balanced run. Protects against stack overflow on
/// pathological or hostile inputs (deeply nested types *or* delimiters) — mirrors
/// the Rust/Python guards exactly, since a `catch_unwind` cannot catch a stack
/// overflow.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = JavaParser {
        src: source,
        toks,
        i: 0,
        diags: Vec::new(),
        depth: 0,
    };
    let root = p.parse_compilation_unit();
    ParseTree {
        source_id: SourceId::from_path(path),
        path: path.to_string(),
        source: source.to_string(),
        root,
        diagnostics: p.diags,
    }
}

struct JavaParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> JavaParser<'s> {
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

    /// Kind of the next significant token.
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

    fn at_open(&self) -> bool {
        self.at("(") || self.at("[") || self.at("{")
    }

    fn next_is_ident(&self) -> bool {
        self.peek_kind_n(1) == Some(tk::IDENT)
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

    fn parse_compilation_unit(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            let item = self.parse_top_item();
            c.push(Child::Node(item));
        }
        self.make_node(node::COMPILATION_UNIT, c)
    }

    fn parse_top_item(&mut self) -> Node {
        let mut c = Vec::new();
        self.parse_modifiers(&mut c);
        self.ws(&mut c);
        if self.at("package") {
            return self.finish_package(c);
        }
        if self.at("import") {
            return self.finish_import(c);
        }
        self.finish_member_or_type(c)
    }

    /// `package a.b.c;` — leading annotations (package-info) already collected.
    fn finish_package(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // package
        if let Some(h) = self.collect_region(node::HEADER, &[";"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::PACKAGE, c)
    }

    /// `import [static] a.b.C;` / `import a.b.*;`.
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

    // --- members and type declarations --------------------------------------

    /// Parse one class-body member: a nested type, an initializer block, or a
    /// method/constructor/field. Leading trivia, annotations, and modifiers are
    /// already collected into `c`.
    fn parse_member(&mut self) -> Node {
        let mut c = Vec::new();
        self.parse_modifiers(&mut c);
        self.ws(&mut c);
        self.finish_member_or_type(c)
    }

    fn finish_member_or_type(&mut self, mut c: Vec<Child>) -> Node {
        if self.at_type_keyword() {
            return self.finish_type_decl(c);
        }
        // A static or instance initializer block: `{ ... }`.
        if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
            return self.make_node(node::INIT_BLOCK, c);
        }
        // Otherwise a method, constructor, or field. Collect the declarator prefix
        // (type params, return/field type, declared name) up to the first
        // significant `(`, `=`, `;`, or `{`.
        if let Some(sig) = self.collect_region(node::SIGNATURE, &["(", "=", ";", "{", "}"]) {
            c.push(Child::Node(sig));
        }
        self.ws(&mut c);
        if self.at("(") {
            // Method or constructor.
            let params = self.parse_delimited(Some(node::PARAMS));
            c.push(Child::Node(params));
            // `throws ...` / annotation default value / etc., up to the body.
            if let Some(h) = self.collect_region(node::HEADER, &["{", ";"]) {
                c.push(Child::Node(h));
            }
            self.ws(&mut c);
            if self.at("{") {
                let b = self.parse_delimited(Some(node::BLOCK));
                c.push(Child::Node(b));
            } else if self.at(";") {
                self.eat(&mut c); // abstract / interface method
            }
            self.make_node(node::METHOD, c)
        } else {
            // Field declaration: capture initializer/remaining declarators up to `;`.
            if let Some(h) = self.collect_region(node::FIELD_INIT, &[";", "}"]) {
                c.push(Child::Node(h));
            }
            self.ws(&mut c);
            if self.at(";") {
                self.eat(&mut c);
            }
            self.make_node(node::FIELD, c)
        }
    }

    /// `[modifiers] class|interface|enum|record|@interface Name <header> { body }`.
    fn finish_type_decl(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        let kind = if self.at("class") {
            node::CLASS
        } else if self.at("interface") {
            node::INTERFACE
        } else if self.at("enum") {
            node::ENUM
        } else if self.at("record") {
            node::RECORD
        } else {
            node::ANNOTATION_TYPE // `@interface`
        };
        if self.at("@") {
            self.eat(&mut c); // @
            self.ws(&mut c);
            self.eat(&mut c); // interface
        } else {
            self.eat(&mut c); // class/interface/enum/record
        }
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        // Generics, record components `(...)`, `extends`/`implements`/`permits`.
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
        self.make_node(kind, c)
    }

    /// `{ members }` parsed as a recursive member list.
    fn parse_item_block(&mut self, label: &'static str) -> Node {
        // Depth guard: beyond the cap, stop recursing into members and consume the
        // body as a flat balanced run. Lossless, never a stack overflow.
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
                    let member = self.parse_member();
                    c.push(Child::Node(member));
                }
            }
        }
        let node = self.make_node(label, c);
        self.depth -= 1;
        node
    }

    /// Collect leading annotations and modifier keywords into `c`. Stops before
    /// `@interface` (an annotation-type declaration, not an annotation).
    fn parse_modifiers(&mut self, c: &mut Vec<Child>) {
        loop {
            self.ws(c);
            if self.at("@") && !self.at_n(1, "interface") {
                let ann = self.parse_annotation();
                c.push(Child::Node(ann));
            } else if self.at("non") && self.at_n(1, "-") && self.at_n(2, "sealed") {
                self.eat(c); // non
                self.eat(c); // -
                self.eat(c); // sealed
            } else if self.at_modifier() {
                self.eat(c);
            } else {
                break;
            }
        }
    }

    /// `@Name` / `@a.b.Name` / `@Name(args)`.
    fn parse_annotation(&mut self) -> Node {
        let mut a = Vec::new();
        self.ws(&mut a);
        self.eat(&mut a); // @
        loop {
            self.ws(&mut a);
            if self.at_ident() {
                self.eat(&mut a);
            } else {
                break;
            }
            self.ws(&mut a);
            if self.at(".") {
                self.eat(&mut a);
            } else {
                break;
            }
        }
        self.ws(&mut a);
        if self.at("(") {
            let g = self.parse_delimited(None);
            a.push(Child::Node(g));
        }
        self.make_node(node::ANNOTATION, a)
    }

    // --- type keyword dispatch ----------------------------------------------

    fn at_modifier(&self) -> bool {
        self.peek_n_text(0)
            .map(|t| MODIFIER_KEYWORDS.contains(&t))
            .unwrap_or(false)
    }

    fn at_type_keyword(&self) -> bool {
        self.at("class")
            || self.at("interface")
            || self.at("enum")
            || (self.at("@") && self.at_n(1, "interface"))
            || self.at_record_decl()
    }

    /// `record` is a *restricted* identifier: it only introduces a record when it
    /// is followed by `Name(`. Anything else (`record r;`, `record()`) is an
    /// ordinary use of the identifier.
    fn at_record_decl(&self) -> bool {
        self.at("record") && self.next_is_ident() && self.at_n(2, "(")
    }

    // --- shared helpers -----------------------------------------------------

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.eat(&mut c); // the identifier (cursor is at it after caller ws)
        self.make_node(node::NAME, c)
    }

    /// Collect tokens (descending into balanced groups) until a significant stop
    /// token at delimiter depth 0, or end of input. Leading/trailing trivia around
    /// a stop stays with the parent. Returns `None` if nothing was collected.
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

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`. The cursor is
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

    /// Record (once per truncation is enough) that the depth cap flattened
    /// structure — reported, never silent.
    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "java.depth_limit",
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_and_is_lossless() {
        let src = "\
// a file
package com.example;

import java.util.List;
import static java.lang.Math.max;

@Deprecated
public class Point implements Comparable<Point> {
    private final int x;
    private int y;

    public Point(int x, int y) {
        this.x = x;
        this.y = y;
    }

    @Override
    public int compareTo(Point other) {
        return max(this.x, other.x);
    }

    static int sum(int a, int b) { return a + b; }
}

interface Shape extends Cloneable {
    double area();
}

enum Color { RED, GREEN, BLUE }

record Pair(int a, int b) {}
";
        let tree = parse("Point.java", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_types() {
        let src = "class A {} interface B {} enum C { X } record D(int v) {}";
        let tree = parse("T.java", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::CLASS), "class: {kinds:?}");
        assert!(kinds.contains(&node::INTERFACE), "interface: {kinds:?}");
        assert!(kinds.contains(&node::ENUM), "enum: {kinds:?}");
        assert!(kinds.contains(&node::RECORD), "record: {kinds:?}");
    }

    #[test]
    fn methods_and_fields_nest_in_class() {
        let src = "class C {\n  int field = 1;\n  void m() {}\n  C() {}\n}";
        let tree = parse("C.java", src);
        let class = tree.root.children_of(node::CLASS).next().expect("a class");
        let block = class.child(node::ITEM_BLOCK).expect("class body");
        let methods: Vec<&str> = block.children_of(node::METHOD).map(|m| m.kind).collect();
        assert_eq!(methods.len(), 2, "m() and the constructor are Methods");
        assert_eq!(block.children_of(node::FIELD).count(), 1, "one field");
    }

    #[test]
    fn record_is_not_confused_with_identifier_use() {
        // `record` as a variable name must NOT parse as a record declaration.
        let src = "class C { int record = 1; void m() { int record = 2; } }";
        let tree = parse("C.java", src);
        let has_record_decl = tree.root.walk().any(|n| n.kind == node::RECORD);
        assert!(!has_record_decl, "`record` used as a name is not a Record");
        assert!(tree.is_lossless());
    }

    #[test]
    fn annotation_type_is_recognized() {
        let src = "public @interface Marker { String value(); }";
        let tree = parse("Marker.java", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::ANNOTATION_TYPE), "got {kinds:?}");
    }

    #[test]
    fn nested_types_are_first_class() {
        let src = "class Outer { class Inner { void m() {} } }";
        let tree = parse("Outer.java", src);
        let inner_method = tree.root.walk().any(|n| n.kind == node::METHOD);
        assert!(inner_method, "method inside a nested class is found");
        let nested_class = tree.root.walk().filter(|n| n.kind == node::CLASS).count();
        assert_eq!(nested_class, 2, "Outer and Inner");
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        // Far deeper than MAX_DEPTH on both axes; must not stack-overflow and must
        // stay lossless.
        let deep_braces = format!(
            "class C {{ void m() {{ {}{} }} }}",
            "{".repeat(10_000),
            "}".repeat(10_000)
        );
        let mut deep_types = String::new();
        for _ in 0..2_000 {
            deep_types.push_str("class C { ");
        }
        deep_types.push_str(&"}".repeat(2_000));
        for src in [deep_braces, deep_types] {
            let tree = parse("deep.java", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics
                    .iter()
                    .any(|d| d.code == "java.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "class C { void m() { foo(1, 2 }", // unterminated paren
            "class λ { String s = \"☃\"; }",   // multi-byte identifiers/strings
            "",                                // empty file
            "// only a comment\n",             // no code
            "class C { ; ; }",                 // stray semicolons
        ] {
            let tree = parse("edge.java", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
