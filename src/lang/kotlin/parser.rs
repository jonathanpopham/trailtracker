//! Kotlin parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust parser ([`crate::lang::rust::parser`]): declaration
//! *headers* are parsed precisely — we always know a `fun`'s signature, a
//! `class`/`interface`/`object`'s name and supertype list, an `import` path —
//! while bodies and expression regions are captured as balanced **token-tree
//! groups** (`Paren`/`Bracket`/`Brace`) plus flat tokens, which is perfectly
//! lossless. The bodies of `class`/`interface`/`object` are recursively parsed as
//! member lists so nested declarations stay first-class. Graph facts (calls,
//! type refs, supertypes) are extracted from these real tokens in the lowering
//! pass, never invented.
//!
//! Kotlin omits statement-ending semicolons, relying on newline inference, so —
//! like the Python parser — the lexer emits `newline` as a *significant*
//! (non-trivia) token and this parser uses it to terminate `import`/`package`
//! declarations, expression-bodied functions (`fun f() = expr`), property
//! initializers, and bodyless/abstract members (`fun f(): Int` in an interface).
//!
//! Anything unrecognized still lands in the tree as its exact tokens (an
//! `ErrorItem` node), so the result always round-trips byte-for-byte. The
//! recursion is depth-guarded at [`MAX_DEPTH`] against hostile nesting (both
//! delimiter and block nesting), because a `catch_unwind` cannot catch a stack
//! overflow.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::kotlin::lexer::{kind as tk, lex};

/// CST node-kind labels. The lowering interprets these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const PACKAGE: &str = "Package";
    pub const IMPORT: &str = "Import";
    pub const FUNCTION: &str = "Function";
    pub const CLASS: &str = "Class";
    pub const INTERFACE: &str = "Interface";
    pub const OBJECT: &str = "Object";
    pub const TYPE_ALIAS: &str = "TypeAlias";
    pub const PROPERTY: &str = "Property";
    pub const ANNOTATION: &str = "Annotation";
    pub const ERROR_ITEM: &str = "ErrorItem";

    pub const NAME: &str = "Name";
    pub const SIGNATURE: &str = "Signature";
    pub const HEADER: &str = "Header";
    pub const EXPR_BODY: &str = "ExprBody";
    pub const INITIALIZER: &str = "Initializer";
    pub const ITEM_BLOCK: &str = "ItemBlock";

    pub const BLOCK: &str = "Block";
    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Modifier keywords that may precede a declaration keyword. Consumed greedily
/// before dispatch; the lowering reads them back off the node's tokens (e.g.
/// `enum` → `type_kind: enum`, `data`/`sealed` → recorded properties).
const MODIFIERS: &[&str] = &[
    "public",
    "private",
    "protected",
    "internal",
    "abstract",
    "final",
    "open",
    "sealed",
    "const",
    "lateinit",
    "override",
    "data",
    "enum",
    "annotation",
    "inner",
    "companion",
    "inline",
    "noinline",
    "crossinline",
    "reified",
    "vararg",
    "suspend",
    "tailrec",
    "operator",
    "infix",
    "external",
    "expect",
    "actual",
    "value",
];

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat balanced run. Mirrors the Rust parser's guard exactly,
/// since a `catch_unwind` cannot catch a stack overflow.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = KotlinParser {
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

struct KotlinParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> KotlinParser<'s> {
    // --- cursor primitives --------------------------------------------------

    /// Append the current token (trivia or not) to `out` and advance.
    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading **trivia** tokens (whitespace, comments) into
    /// `out`. A `newline` is *not* trivia in Kotlin, so it is left in place —
    /// statement termination depends on it.
    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
        }
    }

    /// Move leading trivia, `newline`, and `;` separator tokens into `out`. Used
    /// between items where line breaks and semicolons are insignificant.
    fn seps(&mut self, out: &mut Vec<Child>) {
        loop {
            // Compute the decision without holding a token borrow across the
            // `&mut self` call to `eat`.
            let eat = match self.toks.get(self.i) {
                Some(t) => {
                    t.trivia
                        || t.kind == tk::NEWLINE
                        || (t.kind == tk::PUNCT && t.span.text(self.src) == ";")
                }
                None => false,
            };
            if eat {
                self.eat(out);
            } else {
                break;
            }
        }
    }

    /// Kind of the n-th significant (non-trivia) token from the cursor; `newline`
    /// counts as significant.
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

    fn at_ident(&self) -> bool {
        self.peek_kind() == Some(tk::IDENT)
    }

    fn at_open(&self) -> bool {
        self.at("(") || self.at("[") || self.at("{")
    }

    fn at_modifier(&self) -> bool {
        self.peek_n_text(0)
            .map(|t| MODIFIERS.contains(&t))
            .unwrap_or(false)
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
            self.seps(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            let item = self.parse_item();
            c.push(Child::Node(item));
        }
        self.make_node(node::SOURCE_FILE, c)
    }

    /// Parse `{ members }` as a recursive declaration list. Depth-guarded: beyond
    /// the cap, the body is consumed as a flat balanced run rather than recursing.
    fn parse_item_block(&mut self) -> Node {
        if self.depth >= MAX_DEPTH {
            let mut c = Vec::new();
            self.ws(&mut c);
            self.eat(&mut c); // {
            self.consume_balanced_flat(&mut c);
            self.note_depth_limit();
            return self.make_node(node::ITEM_BLOCK, c);
        }
        self.depth += 1;
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // {
        loop {
            self.seps(&mut c);
            match self.peek_kind() {
                None => break,
                Some(_) if self.at("}") => {
                    self.ws(&mut c);
                    self.eat(&mut c); // }
                    break;
                }
                Some(_) => {
                    let item = self.parse_item();
                    c.push(Child::Node(item));
                }
            }
        }
        let node = self.make_node(node::ITEM_BLOCK, c);
        self.depth -= 1;
        node
    }

    // --- items --------------------------------------------------------------

    fn parse_item(&mut self) -> Node {
        let mut c = Vec::new();

        // Annotations (`@Foo`, `@field:Foo(...)`) and modifier keywords precede
        // the declaration keyword, in any interleaving — commonly on their own
        // lines (`@Serializable\ndata class …`), so newlines between them are
        // skipped along with trivia.
        loop {
            self.seps(&mut c);
            if self.at("@") {
                let a = self.parse_annotation();
                c.push(Child::Node(a));
            } else if self.at_modifier() {
                self.eat(&mut c);
            } else {
                break;
            }
        }

        self.ws(&mut c);
        // `fun interface` is a functional interface, not a function.
        if self.at("fun") && self.peek_n_text(1) == Some("interface") {
            self.eat(&mut c); // the `fun` soft modifier
            return self.finish_type(c, node::INTERFACE);
        }
        if self.at("fun") {
            self.finish_fun(c)
        } else if self.at("class") {
            self.finish_type(c, node::CLASS)
        } else if self.at("interface") {
            self.finish_type(c, node::INTERFACE)
        } else if self.at("object") {
            self.finish_type(c, node::OBJECT)
        } else if self.at("typealias") {
            self.finish_typealias(c)
        } else if self.at("val") || self.at("var") {
            self.finish_property(c)
        } else if self.at("package") {
            self.finish_package(c)
        } else if self.at("import") {
            self.finish_import(c)
        } else {
            self.finish_error_item(c)
        }
    }

    /// `@Name`, `@pkg.Name(args)`, `@field:Name`, `@[A B]`. The name is a dotted
    /// path with an optional `target:` use-site prefix; it must not cross
    /// whitespace into a following modifier (`@Foo private val …`), so the path is
    /// parsed precisely rather than by eating every adjacent identifier.
    fn parse_annotation(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // @
                          // Optional use-site target: `ident :`.
        self.ws(&mut c);
        if self.at_ident() && self.peek_n_text(1) == Some(":") {
            self.eat(&mut c); // target
            self.ws(&mut c);
            self.eat(&mut c); // :
        }
        // Dotted type path: `ident (. ident)*`.
        self.ws(&mut c);
        if self.at_ident() {
            self.eat(&mut c);
            loop {
                self.ws(&mut c);
                if self.at(".") {
                    self.eat(&mut c); // .
                    self.ws(&mut c);
                    if self.at_ident() {
                        self.eat(&mut c);
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            }
        }
        // Optional value arguments `(...)` or array form `[...]`.
        self.ws(&mut c);
        if self.at_open() {
            let g = self.parse_delimited(None);
            c.push(Child::Node(g));
        }
        self.make_node(node::ANNOTATION, c)
    }

    /// `fun <T> Recv.name(params): Ret { body }` / `… = expr` / abstract `… : Ret`.
    /// The name is not split out here (Kotlin's optional receiver makes the name
    /// the identifier just before the value-parameter list); the lowering derives
    /// it from the `Signature`.
    fn finish_fun(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // fun
        if let Some(sig) = self.collect_region(node::SIGNATURE, &["{", "=", ";"]) {
            c.push(Child::Node(sig));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
        } else if self.at("=") {
            self.eat(&mut c); // =
            if let Some(body) = self.collect_region(node::EXPR_BODY, &[";"]) {
                c.push(Child::Node(body));
            }
        } else if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::FUNCTION, c)
    }

    /// `class`/`interface`/`object` `Name<T>(ctor) : Super(args), Iface { body }`.
    fn finish_type(&mut self, mut c: Vec<Child>, kind: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // class / interface / object
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
            let b = self.parse_item_block();
            c.push(Child::Node(b));
        }
        self.make_node(kind, c)
    }

    /// `typealias Name<T> = Type`.
    fn finish_typealias(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // typealias
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(h) = self.collect_region(node::HEADER, &[";"]) {
            c.push(Child::Node(h));
        }
        self.make_node(node::TYPE_ALIAS, c)
    }

    /// `val`/`var` `Name: T = expr` / `… by delegate` / `… { getter }`.
    fn finish_property(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // val / var
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(h) = self.collect_region(node::HEADER, &["=", "{"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("=") {
            self.eat(&mut c); // =
            if let Some(init) = self.collect_region(node::INITIALIZER, &[";"]) {
                c.push(Child::Node(init));
            }
        } else if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
        }
        self.make_node(node::PROPERTY, c)
    }

    fn finish_package(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // package
        self.collect_to_line_end(&mut c);
        self.make_node(node::PACKAGE, c)
    }

    fn finish_import(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // import
        self.collect_to_line_end(&mut c);
        self.make_node(node::IMPORT, c)
    }

    fn finish_error_item(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        if self.at_open() {
            let g = self.parse_delimited(None);
            c.push(Child::Node(g));
        } else if self.peek_kind().is_some() {
            // Consume exactly one significant token to guarantee progress; the
            // bytes stay in the tree.
            self.eat(&mut c);
        }
        self.diags.push(Diagnostic {
            code: "kotlin.unrecognized_item",
            message: "token(s) not recognized as a Kotlin declaration".to_string(),
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

    /// Collect tokens (descending into balanced groups) until a significant stop
    /// token at delimiter depth 0, a `newline` at depth 0, or end of input.
    /// Newlines inside groups are part of the group (implicit continuation).
    fn collect_region(&mut self, label: &'static str, stops: &[&str]) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            match self.peek_kind() {
                None => break,
                Some(k) if k == tk::NEWLINE => break,
                _ => {}
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

    /// Collect tokens (descending into balanced groups) up to a `newline` or `;`
    /// at depth 0 — a logical line. Used for `package`/`import` declarations.
    fn collect_to_line_end(&mut self, out: &mut Vec<Child>) {
        loop {
            match self.peek_kind() {
                None => break,
                Some(k) if k == tk::NEWLINE => break,
                _ if self.at(";") => break,
                _ => {
                    if self.at_open() {
                        self.ws(out);
                        let g = self.parse_delimited(None);
                        out.push(Child::Node(g));
                    } else {
                        self.ws(out);
                        self.eat(out);
                    }
                }
            }
        }
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`. The cursor is
    /// at (or before trivia preceding) the opener. Newlines inside the group are
    /// eaten as ordinary content.
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

    /// Record (once per truncation) that the depth cap flattened structure —
    /// reported, never silent.
    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "kotlin.depth_limit",
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
package com.example.app

import kotlin.math.sqrt
import com.example.util.Helper as H

const val VERSION = \"1.0\"

@Serializable
data class Point(val x: Int, val y: Int) : Comparable<Point>, Base() {
    fun norm(): Double = sqrt((x * x + y * y).toDouble())

    override fun compareTo(other: Point): Int {
        return norm().compareTo(other.norm())
    }
}

interface Shape {
    fun area(): Double
}

object Registry {
    val items = mutableListOf<Shape>()
}

fun add(a: Int, b: Int): Int = a + b
";
        let tree = parse("Main.kt", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "package p\nimport a.b\nfun f() {}\nclass C\ninterface I\nobject O\ntypealias T = Int\nval v = 1\n";
        let tree = parse("t.kt", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::PACKAGE), "package: {kinds:?}");
        assert!(kinds.contains(&node::IMPORT), "import: {kinds:?}");
        assert!(kinds.contains(&node::FUNCTION), "fun: {kinds:?}");
        assert!(kinds.contains(&node::CLASS), "class: {kinds:?}");
        assert!(kinds.contains(&node::INTERFACE), "interface: {kinds:?}");
        assert!(kinds.contains(&node::OBJECT), "object: {kinds:?}");
        assert!(kinds.contains(&node::TYPE_ALIAS), "typealias: {kinds:?}");
        assert!(kinds.contains(&node::PROPERTY), "property: {kinds:?}");
    }

    #[test]
    fn members_nest_inside_class_bodies() {
        let src = "class C {\n    fun a() {}\n    fun b() {}\n}\n";
        let tree = parse("t.kt", src);
        let class = tree
            .root
            .children_of(node::CLASS)
            .next()
            .expect("a class node");
        let block = class.child(node::ITEM_BLOCK).expect("class has a body");
        let methods = block.children_of(node::FUNCTION).count();
        assert_eq!(methods, 2, "two methods inside the class body");
    }

    #[test]
    fn expression_body_and_abstract_member() {
        // Expression body terminates at the newline; abstract member has no body.
        let src = "fun f() = 1\ninterface I {\n    fun g(): Int\n}\n";
        let tree = parse("t.kt", src);
        let f = tree
            .root
            .children_of(node::FUNCTION)
            .next()
            .expect("a function");
        assert!(
            f.child(node::EXPR_BODY).is_some(),
            "f has an expression body"
        );
        assert!(tree.is_lossless());
    }

    #[test]
    fn fun_interface_is_a_type() {
        let src = "fun interface Predicate {\n    fun test(x: Int): Boolean\n}\n";
        let tree = parse("t.kt", src);
        assert!(
            tree.root.children_of(node::INTERFACE).next().is_some(),
            "`fun interface` should parse as an interface, not a function"
        );
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        // Far deeper than MAX_DEPTH on both axes; must not stack-overflow and must
        // stay lossless.
        let deep_parens = format!("val x = {}{}\n", "(".repeat(10_000), ")".repeat(10_000));
        let mut deep_blocks = String::from("class A {\n");
        for _ in 0..2_000 {
            deep_blocks.push_str("class B {\n");
        }
        for _ in 0..2_000 {
            deep_blocks.push_str("}\n");
        }
        deep_blocks.push_str("}\n");
        for src in [deep_parens, deep_blocks] {
            let tree = parse("deep.kt", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics
                    .iter()
                    .any(|d| d.code == "kotlin.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "val x = (1, 2\n",                       // unterminated paren
            "val λ = \"☃\" // unicode\n",            // multi-byte identifiers/strings
            "",                                      // empty file
            "\n\n   \n// trailing\n",                // only blanks and comments
            "val s = \"\"\"raw ${f(\"x\")}\"\"\"\n", // interpolation with nested string
        ] {
            let tree = parse("edge.kt", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
