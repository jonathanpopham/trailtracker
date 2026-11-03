//! Groovy parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust and Java parsers ([`crate::lang::rust::parser`],
//! [`crate::lang::java::parser`]): declaration *headers* are parsed precisely —
//! we always know a type's name and supertypes, a method's name and parameter
//! list, a field's name, an `import` path — while method bodies, closures, and
//! expression regions are captured as balanced **token-tree groups**
//! (`Paren`/`Bracket`/`Brace`) plus flat tokens, which is perfectly lossless.
//! Graph facts (calls, type refs) are extracted from these real token trees in
//! the lowering pass, never invented.
//!
//! Groovy is harder than Java in two ways the parser must respect:
//!
//! 1. **Statement terminators are optional.** A newline ends a statement just as
//!    a `;` does. So beyond the explicit stop tokens, the header/field/statement
//!    collectors also stop at a depth-0 newline (delimiter groups are descended
//!    into, so newlines *inside* `(...)`/`[...]`/`{...}` never terminate early).
//!
//! 2. **Members carry no leading keyword.** Like Java, a method is told from a
//!    field by whether a `(` follows the name, and a top-level *script statement*
//!    (Gradle DSL: `repositories { … }`, `task foo { … }`) is told from a real
//!    method declaration by context — only a class-body member, a `def`-prefixed
//!    form, or a typed `Return name(...) { }` form is a declaration; a bare
//!    `name(...) { }` / `name { }` at script level is a call statement.
//!
//! Anything unrecognized still lands in the tree as its exact tokens, so the
//! result always round-trips byte-for-byte. The recursion is depth-guarded at
//! [`MAX_DEPTH`] against hostile nesting (both nested types and nested
//! delimiters), because a `catch_unwind` cannot catch a stack overflow.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::groovy::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const PACKAGE: &str = "Package";
    pub const IMPORT: &str = "Import";
    pub const CLASS: &str = "Class";
    pub const INTERFACE: &str = "Interface";
    pub const ENUM: &str = "Enum";
    pub const TRAIT: &str = "Trait";
    pub const ANNOTATION_TYPE: &str = "AnnotationType";
    pub const METHOD: &str = "Method";
    pub const FIELD: &str = "Field";
    /// A top-level / class-body statement (script body, Gradle DSL call, init
    /// block) that is not itself a declaration. Holds its exact tokens.
    pub const STATEMENT: &str = "Statement";
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

/// The leading declaration modifiers recognized before a declarator. `def` is
/// included (Groovy's dynamic-type marker), as are the standard Java modifiers.
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
    "def",
];

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat balanced run. Mirrors the Rust/Java guards exactly, since
/// a `catch_unwind` cannot catch a stack overflow.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = GroovyParser {
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

struct GroovyParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> GroovyParser<'s> {
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

    /// True if a depth-0 newline sits in the pending trivia before the next
    /// significant token — Groovy's implicit statement terminator.
    fn pending_has_newline(&self) -> bool {
        let mut j = self.i;
        while j < self.toks.len() && self.toks[j].trivia {
            if self.toks[j].span.text(self.src).contains('\n') {
                return true;
            }
            j += 1;
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

    fn parse_source_file(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            let before = self.i;
            let item = self.parse_top_item();
            c.push(Child::Node(item));
            // Ultimate progress guard: if an item somehow consumed nothing, force
            // one token so the loop can never spin (mirrors the lexer guard).
            if self.i == before {
                let mut e = Vec::new();
                self.eat(&mut e);
                c.push(Child::Node(self.make_node(node::ERROR_ITEM, e)));
            }
        }
        self.make_node(node::SOURCE_FILE, c)
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
        self.finish_member_or_statement(c, false)
    }

    /// `package a.b.c` (with or without a trailing `;`).
    fn finish_package(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // package
        if let Some(h) = self.collect_region(node::HEADER, &[";"], true) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::PACKAGE, c)
    }

    /// `import [static] a.b.C` / `import a.b.*` / `import a.b.C as D`.
    fn finish_import(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // import
        if let Some(h) = self.collect_region(node::HEADER, &[";"], true) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::IMPORT, c)
    }

    // --- members, types, and statements -------------------------------------

    /// Parse one class-body member, recursing into nested types. Leading trivia,
    /// annotations, and modifiers are collected first.
    fn parse_member(&mut self) -> Node {
        let mut c = Vec::new();
        self.parse_modifiers(&mut c);
        self.ws(&mut c);
        self.finish_member_or_statement(c, true)
    }

    /// The shared declarator dispatcher, used at both the top level
    /// (`in_class_body = false`, where a non-declaration is a script statement)
    /// and inside a class body (`in_class_body = true`, where members default to
    /// declarations). `c` already holds leading trivia/annotations/modifiers.
    fn finish_member_or_statement(&mut self, mut c: Vec<Child>, in_class_body: bool) -> Node {
        if self.at_type_keyword() {
            return self.finish_type_decl(c);
        }
        // A bare `{ ... }` — a static/instance initializer block or a standalone
        // closure statement.
        if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
            return self.make_node(node::STATEMENT, c);
        }

        // Collect the declarator prefix (type params, return/field type, the
        // declared name) up to the first significant `(`, `=`, `{`, `;`, `}`, or a
        // depth-0 newline.
        let sig = self.collect_region(node::SIGNATURE, &["(", "=", "{", ";", "}"], true);
        let sig_idents = sig
            .as_ref()
            .map(|s| self.top_level_ident_count(s))
            .unwrap_or(0);
        if let Some(s) = sig {
            c.push(Child::Node(s));
        }
        let has_def = self.has_token_text(&c, "def");
        let is_decl_context = in_class_body || has_def || sig_idents >= 2;

        self.ws(&mut c);
        if self.at("(") {
            // A `(...)` follows the name: a method/constructor declaration, or a
            // call statement (`foo(args)` / DSL `foo(args) { }`).
            let params = self.parse_delimited(Some(node::PARAMS));
            c.push(Child::Node(params));
            if let Some(h) = self.collect_region(node::HEADER, &["{", ";", "}"], true) {
                c.push(Child::Node(h));
            }
            self.ws(&mut c);
            if self.at("{") {
                let b = self.parse_delimited(Some(node::BLOCK));
                c.push(Child::Node(b));
                // A trailing brace block is a method body only in a declaration
                // context; otherwise it is a closure argument to a DSL call.
                if is_decl_context {
                    self.make_node(node::METHOD, c)
                } else {
                    self.make_node(node::STATEMENT, c)
                }
            } else if self.at(";") {
                self.eat(&mut c); // abstract / interface method, or a call statement
                if is_decl_context {
                    self.make_node(node::METHOD, c)
                } else {
                    self.make_node(node::STATEMENT, c)
                }
            } else if is_decl_context {
                // No body and no `;`: an abstract / interface / trait method
                // declaration (newline-terminated).
                self.make_node(node::METHOD, c)
            } else {
                // A script call statement on its own line.
                self.make_node(node::STATEMENT, c)
            }
        } else if self.at("=") {
            // `name = init` — a field/variable binding or a top-level assignment.
            if let Some(init) = self.collect_region(node::FIELD_INIT, &[";", "}"], true) {
                c.push(Child::Node(init));
            }
            self.ws(&mut c);
            if self.at(";") {
                self.eat(&mut c);
            }
            if is_decl_context {
                self.make_node(node::FIELD, c)
            } else {
                self.make_node(node::STATEMENT, c)
            }
        } else if self.at("{") {
            // `name { ... }` with no parens — a DSL call with a closure argument
            // (`repositories { … }`); no-paren method declarations are not valid.
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
            self.make_node(node::STATEMENT, c)
        } else if self.at(";") {
            self.eat(&mut c);
            if is_decl_context && top_level_has_ident(&c) {
                self.make_node(node::FIELD, c)
            } else {
                self.make_node(node::STATEMENT, c)
            }
        } else {
            // Newline-terminated, end of block, or EOF: a bare property/field
            // (`String name`) or a statement.
            if c.is_empty() {
                // Defensive: guarantee progress by consuming one token.
                self.eat(&mut c);
                return self.make_node(node::ERROR_ITEM, c);
            }
            if is_decl_context && top_level_has_ident(&c) {
                self.make_node(node::FIELD, c)
            } else {
                self.make_node(node::STATEMENT, c)
            }
        }
    }

    /// `[modifiers] class|interface|enum|trait|@interface Name <header> { body }`.
    fn finish_type_decl(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        let kind = if self.at("class") {
            node::CLASS
        } else if self.at("interface") {
            node::INTERFACE
        } else if self.at("enum") {
            node::ENUM
        } else if self.at("trait") {
            node::TRAIT
        } else {
            node::ANNOTATION_TYPE // `@interface`
        };
        if self.at("@") {
            self.eat(&mut c); // @
            self.ws(&mut c);
            self.eat(&mut c); // interface
        } else {
            self.eat(&mut c); // class/interface/enum/trait
        }
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        // Generics, `extends`/`implements`, up to the body brace.
        if let Some(h) = self.collect_region(node::HEADER, &["{", ";"], false) {
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
                        // Progress guard inside a body.
                        let mut e = Vec::new();
                        self.eat(&mut e);
                        c.push(Child::Node(self.make_node(node::ERROR_ITEM, e)));
                    }
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

    // --- keyword dispatch ----------------------------------------------------

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
            // `trait` is contextual: only a type declaration when followed by a name.
            || (self.at("trait") && self.next_is_ident())
    }

    // --- shared helpers -----------------------------------------------------

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.eat(&mut c); // the identifier (cursor is at it after caller ws)
        self.make_node(node::NAME, c)
    }

    /// Collect tokens (descending into balanced groups) until a significant stop
    /// token at delimiter depth 0, a depth-0 newline (when `newline_stop`), or end
    /// of input. Leading/trailing trivia around the stop stays with the parent.
    /// Returns `None` if nothing was collected.
    fn collect_region(
        &mut self,
        label: &'static str,
        stops: &[&str],
        newline_stop: bool,
    ) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            if self.peek_kind().is_none() {
                break;
            }
            if stops.iter().any(|s| self.at(s)) {
                break;
            }
            if newline_stop && !c.is_empty() && self.pending_has_newline() {
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
            code: "groovy.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; region flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }

    /// Count non-keyword identifier tokens directly under a node — used to tell a
    /// typed `Return name` declaration (>= 2 idents) from a bare call at script
    /// level.
    fn top_level_ident_count(&self, node: &Node) -> usize {
        node.children
            .iter()
            .filter(|c| match c {
                Child::Token(t) => {
                    !t.trivia
                        && t.kind == tk::IDENT
                        && !crate::lang::groovy::lexer::is_keyword(t.span.text(self.src))
                }
                _ => false,
            })
            .count()
    }

    /// Whether any direct modifier token in `children` has the given text (used to
    /// detect a leading `def`).
    fn has_token_text(&self, children: &[Child], text: &str) -> bool {
        children.iter().any(|c| match c {
            Child::Token(t) => !t.trivia && t.span.text(self.src) == text,
            _ => false,
        })
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

/// Whether the children hold a collected `Signature` (i.e. a declared name was
/// seen), used to classify a terminator-only member as a field vs. statement.
fn top_level_has_ident(children: &[Child]) -> bool {
    children.iter().any(|c| match c {
        Child::Node(n) => n.kind == node::SIGNATURE,
        _ => false,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_and_is_lossless() {
        let src = "\
// a file
package com.example

import groovy.transform.CompileStatic
import static java.lang.Math.max

@CompileStatic
class Point implements Comparable<Point> {
    int x
    private int y
    static final String NOTE = 'corner'

    Point(int x, int y) {
        this.x = x
        this.y = y
    }

    int compareTo(Point other) {
        return max(this.x, other.x)
    }

    def describe() { \"(${x}, ${y})\" }
}

trait Named {
    abstract String name()
}

enum Color { RED, GREEN, BLUE }

def add(a, b) { a + b }
";
        let tree = parse("Point.groovy", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn gradle_script_is_lossless() {
        let src = "\
plugins {
    id 'java'
    id 'groovy'
}

repositories {
    mavenCentral()
}

dependencies {
    implementation 'org.codehaus.groovy:groovy-all:3.0.9'
    testImplementation('junit:junit:4.13') {
        exclude group: 'org.hamcrest'
    }
}

task hello {
    doLast {
        println \"Hello from ${project.name}\"
    }
}
";
        let tree = parse("build.gradle", src);
        assert!(tree.is_lossless(), "gradle script must reconstruct source");
    }

    #[test]
    fn finds_top_level_types() {
        let src = "class A {}\ninterface B {}\nenum C { X }\ntrait D { void m() {} }";
        let tree = parse("T.groovy", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::CLASS), "class: {kinds:?}");
        assert!(kinds.contains(&node::INTERFACE), "interface: {kinds:?}");
        assert!(kinds.contains(&node::ENUM), "enum: {kinds:?}");
        assert!(kinds.contains(&node::TRAIT), "trait: {kinds:?}");
    }

    #[test]
    fn methods_and_fields_nest_in_class() {
        let src = "class C {\n  int field = 1\n  void m() {}\n  C() {}\n}";
        let tree = parse("C.groovy", src);
        let class = tree.root.children_of(node::CLASS).next().expect("a class");
        let block = class.child(node::ITEM_BLOCK).expect("class body");
        let methods = block.children_of(node::METHOD).count();
        assert_eq!(methods, 2, "m() and the constructor are Methods");
        assert_eq!(block.children_of(node::FIELD).count(), 1, "one field");
    }

    #[test]
    fn def_function_is_a_method() {
        let src = "def greet(name) { \"hi $name\" }";
        let tree = parse("s.groovy", src);
        assert!(
            tree.root.child_nodes().any(|n| n.kind == node::METHOD),
            "a top-level `def` function is a Method"
        );
    }

    #[test]
    fn dsl_call_is_a_statement_not_a_method() {
        // `repositories { … }` at script level is a call, not a declaration.
        let src = "repositories {\n  mavenCentral()\n}";
        let tree = parse("build.gradle", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::STATEMENT), "got {kinds:?}");
        assert!(
            !kinds.contains(&node::METHOD),
            "DSL closure is not a method"
        );
    }

    #[test]
    fn trait_used_as_identifier_is_not_a_type() {
        // `trait` as a variable must not parse as a trait declaration.
        let src = "def trait = 5\nprintln trait";
        let tree = parse("s.groovy", src);
        assert!(!tree.root.walk().any(|n| n.kind == node::TRAIT));
        assert!(tree.is_lossless());
    }

    #[test]
    fn nested_types_are_first_class() {
        let src = "class Outer { class Inner { void m() {} } }";
        let tree = parse("Outer.groovy", src);
        let methods = tree.root.walk().filter(|n| n.kind == node::METHOD).count();
        assert_eq!(methods, 1, "the inner method");
        let classes = tree.root.walk().filter(|n| n.kind == node::CLASS).count();
        assert_eq!(classes, 2, "Outer and Inner");
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
            let tree = parse("deep.groovy", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics
                    .iter()
                    .any(|d| d.code == "groovy.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn edge_cases_round_trip() {
        for src in [
            "class C { void m() { foo(1, 2 }", // unterminated paren
            "class λ { String s = '☃' }",      // multi-byte identifiers/strings
            "",                                // empty file
            "// only a comment\n",             // no code
            "class C { ; ; }",                 // stray semicolons
            "def r = /a+b/\nprintln r",        // slashy string
            "x = $/ dollar $slashy /$",        // dollar-slashy
            "}",                               // stray close brace at top level
        ] {
            let tree = parse("edge.groovy", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
