//! Dart parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Java parser ([`crate::lang::java::parser`]), which in
//! turn mirrors the Rust one: declaration *headers* are parsed precisely — we
//! always know a type's name and supertypes, a function's name and parameter
//! list, a directive's payload — while bodies and expression regions are
//! captured as balanced **token-tree groups** (`Paren`/`Bracket`/`Brace`) plus
//! flat tokens, which is perfectly lossless. Graph facts (calls, type refs) are
//! extracted from these real token trees in the lowering pass, never invented.
//!
//! Dart members carry no single leading keyword the way Rust items do
//! (`fn`/`struct`): a method is distinguished from a field by whether a `(`
//! follows the declared name, and a getter/arrow body by a `{`/`=>` following
//! the name. The parser collects the declarator prefix (annotations, modifiers,
//! type, name) and then branches on the first significant delimiter.
//!
//! Anything unrecognized still lands in the tree as its exact tokens, so the
//! result always round-trips byte-for-byte. The recursion is depth-guarded at
//! [`MAX_DEPTH`] against hostile nesting (both nested types and nested
//! delimiters), because a `catch_unwind` cannot catch a stack overflow.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::dart::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const COMPILATION_UNIT: &str = "CompilationUnit";
    /// `library` / `import` / `export` / `part` / `part of` directive.
    pub const DIRECTIVE: &str = "Directive";
    pub const CLASS: &str = "Class";
    pub const MIXIN: &str = "Mixin";
    pub const ENUM: &str = "Enum";
    pub const EXTENSION: &str = "Extension";
    pub const TYPEDEF: &str = "Typedef";
    /// A function, method, getter, setter, or constructor.
    pub const FUNCTION: &str = "Function";
    /// A field or top-level variable declaration.
    pub const FIELD: &str = "Field";
    pub const ANNOTATION: &str = "Annotation";
    pub const ERROR_ITEM: &str = "ErrorItem";

    pub const NAME: &str = "Name";
    pub const HEADER: &str = "Header";
    pub const SIGNATURE: &str = "Signature";
    pub const PARAMS: &str = "Params";
    pub const FIELD_INIT: &str = "FieldInit";
    /// The expression of an `=> expr` arrow body.
    pub const ARROW: &str = "Arrow";
    pub const ITEM_BLOCK: &str = "ItemBlock";

    pub const BLOCK: &str = "Block";
    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Leading declaration modifiers recognized before a declarator. `const`/`final`
/// double as variable-declaration keywords; consuming them here is fine because
/// the lowering reads them back off the member's tokens to classify a binding.
const MODIFIER_KEYWORDS: &[&str] = &[
    "abstract",
    "static",
    "final",
    "const",
    "external",
    "factory",
    "late",
    "covariant",
    "required",
    "sealed",
    "base",
    "interface",
];

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat balanced run. Mirrors the Rust/Java guards exactly, since
/// a `catch_unwind` cannot catch a stack overflow.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = DartParser {
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

struct DartParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> DartParser<'s> {
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

    fn at_ident(&self) -> bool {
        self.peek_kind() == Some(tk::IDENT)
    }

    /// A usable declaration name: an identifier that is not a keyword (so
    /// `extension on T` does not read `on` as the extension's name).
    fn at_name(&self) -> bool {
        self.peek_kind() == Some(tk::IDENT)
            && self
                .peek_n_text(0)
                .map(|t| !crate::lang::dart::lexer::is_keyword(t))
                .unwrap_or(false)
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

    fn parse_compilation_unit(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            let before = self.i;
            let item = self.parse_top_item();
            c.push(Child::Node(item));
            // Guard against a non-advancing item parse (e.g. a stray closing
            // delimiter at top level): consume one token as an error so the loop
            // always makes progress and stays lossless.
            if self.i == before {
                let mut e = Vec::new();
                self.eat(&mut e);
                if !e.is_empty() {
                    c.push(Child::Node(self.make_node(node::ERROR_ITEM, e)));
                }
            }
        }
        self.make_node(node::COMPILATION_UNIT, c)
    }

    fn parse_top_item(&mut self) -> Node {
        let mut c = Vec::new();
        self.parse_modifiers(&mut c);
        self.ws(&mut c);
        if self.at("library") || self.at("import") || self.at("export") || self.at("part") {
            return self.finish_directive(c);
        }
        self.finish_member_or_type(c)
    }

    /// `library a.b;` / `import 'uri' as x show y;` / `export 'uri';` /
    /// `part 'uri';` / `part of a.b;`.
    fn finish_directive(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        let kw = self.peek_n_text(0).unwrap_or("").to_string();
        self.eat(&mut c); // library/import/export/part
        if kw == "part" && self.at("of") {
            self.ws(&mut c);
            self.eat(&mut c); // of
        }
        if let Some(h) = self.collect_region(node::HEADER, &[";"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::DIRECTIVE, c)
    }

    // --- members and type declarations --------------------------------------

    /// Parse one class/mixin/enum/extension body member, or a top-level item.
    /// Leading trivia, annotations, and modifiers are already collected into `c`.
    fn finish_member_or_type(&mut self, mut c: Vec<Child>) -> Node {
        if self.at_type_keyword() {
            return self.finish_type_decl(c);
        }
        self.ws(&mut c);
        // Declarator prefix (type params, return/field type, declared name) up to
        // the first significant `(`, `=`, `;`, `{`, `=>`, or a closing `}`.
        if let Some(sig) = self.collect_region(node::SIGNATURE, &["(", "=", ";", "{", "=>", "}"]) {
            c.push(Child::Node(sig));
        }
        self.ws(&mut c);
        if self.at("(") {
            // Function / method / constructor.
            let params = self.parse_delimited(Some(node::PARAMS));
            c.push(Child::Node(params));
            // Constructor initializer list, `async`/`sync*`, redirects, etc.,
            // up to the body.
            if let Some(h) = self.collect_region(node::HEADER, &["{", ";", "=>", "}"]) {
                c.push(Child::Node(h));
            }
            self.parse_body(&mut c);
            self.make_node(node::FUNCTION, c)
        } else if self.at("{") || self.at("=>") {
            // A getter or a paramless function body (`Type get x => …`).
            self.parse_body(&mut c);
            self.make_node(node::FUNCTION, c)
        } else {
            // Field / top-level variable: capture initializer + extra declarators.
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

    /// Parse a function/getter body: a `{ … }` block, an `=> expr;` arrow, or a
    /// bare `;` (abstract / external / forward declaration).
    fn parse_body(&mut self, c: &mut Vec<Child>) {
        self.ws(c);
        if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
        } else if self.at("=>") {
            self.eat(c); // =>
            if let Some(r) = self.collect_region(node::ARROW, &[";", "}"]) {
                c.push(Child::Node(r));
            }
            self.ws(c);
            if self.at(";") {
                self.eat(c);
            }
        } else if self.at(";") {
            self.eat(c);
        }
    }

    /// `[modifiers] class|mixin|enum|extension|typedef Name <header> { body }`.
    fn finish_type_decl(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        let kw = self.peek_n_text(0).unwrap_or("");
        let kind = match kw {
            "class" => node::CLASS,
            "mixin" => node::MIXIN,
            "enum" => node::ENUM,
            "extension" => node::EXTENSION,
            "typedef" => node::TYPEDEF,
            _ => node::CLASS,
        };
        self.eat(&mut c); // the declaration keyword

        // `mixin class C` — a mixin-class declaration carries both keywords.
        if kind == node::MIXIN && self.at("class") {
            self.ws(&mut c);
            self.eat(&mut c);
        }
        // `extension type Name(...)` — an extension type carries the `type` word.
        if kind == node::EXTENSION && self.at("type") {
            self.ws(&mut c);
            self.eat(&mut c);
        }

        if kind == node::TYPEDEF {
            self.ws(&mut c);
            if self.at_name() {
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
            return self.make_node(node::TYPEDEF, c);
        }

        self.ws(&mut c);
        // The name is optional for an anonymous `extension on T { … }`.
        if self.at_name() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        // Generics, `extends`/`with`/`implements`/`on`, extension-type repr `(…)`.
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
                    let before = self.i;
                    let member = self.parse_member();
                    c.push(Child::Node(member));
                    if self.i == before {
                        // Defensive: a stray token that produced no progress (e.g.
                        // a lone `;`); consume one so the loop cannot spin.
                        self.eat(&mut c);
                    }
                }
            }
        }
        let n = self.make_node(label, c);
        self.depth -= 1;
        n
    }

    fn parse_member(&mut self) -> Node {
        let mut c = Vec::new();
        self.parse_modifiers(&mut c);
        self.ws(&mut c);
        self.finish_member_or_type(c)
    }

    /// Collect leading annotations and modifier keywords into `c`.
    fn parse_modifiers(&mut self, c: &mut Vec<Child>) {
        loop {
            self.ws(c);
            if self.at("@") {
                let ann = self.parse_annotation();
                c.push(Child::Node(ann));
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

    // --- dispatch helpers ---------------------------------------------------

    fn at_modifier(&self) -> bool {
        self.peek_n_text(0)
            .map(|t| MODIFIER_KEYWORDS.contains(&t))
            .unwrap_or(false)
    }

    fn at_type_keyword(&self) -> bool {
        self.at("class")
            || self.at("mixin")
            || self.at("enum")
            || self.at("extension")
            || self.at("typedef")
    }

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.eat(&mut c); // the identifier (cursor is at it after caller ws)
        self.make_node(node::NAME, c)
    }

    /// Collect tokens (descending into balanced groups) until a significant stop
    /// token at delimiter depth 0, or end of input. Returns `None` if nothing was
    /// collected.
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

    /// Record (once per truncation is enough) that the depth cap flattened
    /// structure — reported, never silent.
    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "dart.depth_limit",
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
library example;

import 'dart:math';
import 'package:meta/meta.dart';
import '../util.dart' as util;

/// A 2D point.
@immutable
abstract class Point implements Comparable<Point> {
  final int x;
  int y = 0;
  static const String note = 'a point';

  Point(this.x, this.y);
  Point.origin() : x = 0, y = 0;

  @override
  int compareTo(Point other) => x - other.x;

  int get magnitude {
    return x * x + y * y;
  }
}

mixin Bounded on Point {
  bool inside() => true;
}

enum Color { red, green, blue }

extension Doubling on int {
  int get doubled => this * 2;
}

typedef IntList = List<int>;

void main() {
  final p = Point(1, 2);
  print(p.compareTo(p));
}
";
        let tree = parse("point.dart", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_declarations() {
        let src = "class A {} mixin B {} enum C { x } extension D on int {} typedef E = int;";
        let tree = parse("t.dart", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::CLASS), "class: {kinds:?}");
        assert!(kinds.contains(&node::MIXIN), "mixin: {kinds:?}");
        assert!(kinds.contains(&node::ENUM), "enum: {kinds:?}");
        assert!(kinds.contains(&node::EXTENSION), "extension: {kinds:?}");
        assert!(kinds.contains(&node::TYPEDEF), "typedef: {kinds:?}");
    }

    #[test]
    fn methods_fields_getters_nest_in_class() {
        let src = "class C {\n  int field = 1;\n  void m() {}\n  C() {}\n  int get g => 1;\n}";
        let tree = parse("c.dart", src);
        let class = tree.root.children_of(node::CLASS).next().expect("a class");
        let block = class.child(node::ITEM_BLOCK).expect("class body");
        let fns = block.children_of(node::FUNCTION).count();
        assert_eq!(fns, 3, "m(), the constructor, and the getter");
        assert_eq!(block.children_of(node::FIELD).count(), 1, "one field");
    }

    #[test]
    fn arrow_body_is_lossless_and_captured() {
        let src = "int add(int a, int b) => a + b;";
        let tree = parse("a.dart", src);
        assert!(tree.is_lossless());
        let f = tree.root.children_of(node::FUNCTION).next().expect("a fn");
        assert!(f.child(node::ARROW).is_some(), "arrow body captured");
    }

    #[test]
    fn anonymous_extension_has_no_name_from_on() {
        let src = "extension on String { int len() => 0; }";
        let tree = parse("e.dart", src);
        let ext = tree
            .root
            .children_of(node::EXTENSION)
            .next()
            .expect("an extension");
        assert!(ext.child(node::NAME).is_none(), "`on` is not the name");
        assert!(tree.is_lossless());
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
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
            let tree = parse("deep.dart", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics
                    .iter()
                    .any(|d| d.code == "dart.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "class C { void m() { foo(1, 2 }", // unterminated paren
            "class λ { var s = '☃'; }",        // multi-byte idents/strings
            "",                                // empty file
            "// only a comment\n",             // no code
            "class C { ; ; }",                 // stray semicolons
            "var x = 'a ${b('c')} d';",        // interpolation w/ nested quotes
        ] {
            let tree = parse("edge.dart", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
