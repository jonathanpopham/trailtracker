//! D parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust and C++ parsers: item *headers* are parsed
//! precisely — a `module a.b.c;`, an `import`, an aggregate
//! (`class`/`struct`/`interface`/`union`), an `enum`, a `template`, an `alias`,
//! a function's name and parameter list — while bodies and
//! initializer/expression regions are captured as balanced **token-tree groups**
//! (`Paren`/`Bracket`/`Brace`) plus flat tokens, which is perfectly lossless.
//! Graph facts (calls, base classes, type uses) are extracted from these real
//! tokens in the lowering pass, never invented.
//!
//! D, like C/C++, has no `function` keyword for ordinary functions: a
//! *declarator* shaped `name ( params )` is the signal — followed by `{` it is a
//! definition, by `;` a declaration. We treat such a shape as a function only
//! when it is preceded by a specifier/return-type (or carries a body), which
//! keeps stray expression statements out, and document the residual ambiguity
//! honestly. Constructors (`this(...)`) and destructors (`~this(...)`) are
//! recognized specially since `this` is a keyword.
//!
//! Anything unrecognized still lands in the tree as its exact tokens (a `Decl`
//! or `ErrorItem` node), so the result always round-trips byte-for-byte.
//! Recursion is depth-guarded at [`MAX_DEPTH`] against hostile nesting — both
//! bracket nesting and item nesting — because a `catch_unwind` cannot catch a
//! stack overflow.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::d::lexer::{is_keyword, kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const MODULE_DECL: &str = "ModuleDecl";
    pub const IMPORT_DECL: &str = "ImportDecl";
    pub const CLASS: &str = "Class";
    pub const STRUCT: &str = "Struct";
    pub const INTERFACE: &str = "Interface";
    pub const UNION: &str = "Union";
    pub const ENUM: &str = "Enum";
    pub const TEMPLATE: &str = "Template";
    pub const FUNCTION: &str = "Function";
    pub const ALIAS: &str = "Alias";
    pub const DECL: &str = "Decl";
    pub const UNITTEST: &str = "Unittest";
    pub const ATTR_BLOCK: &str = "AttrBlock";
    pub const ACCESS_SPEC: &str = "AccessSpec";
    pub const ERROR_ITEM: &str = "ErrorItem";

    pub const NAME: &str = "Name";
    pub const HEADER: &str = "Header";

    pub const ITEM_BLOCK: &str = "ItemBlock";
    pub const BLOCK: &str = "Block";
    pub const ENUM_BODY: &str = "EnumBody";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat run. Protects against stack overflow on pathological or
/// hostile inputs — mirrors the Rust/C++ parsers exactly, since a
/// `catch_unwind` cannot catch a stack overflow.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = DParser {
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

struct DParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> DParser<'s> {
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

    /// Text of the n-th significant (non-trivia) token from the cursor.
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

    /// Parse `{ items }` as a recursive item list (aggregate / template /
    /// attribute-block body).
    fn parse_item_block(&mut self) -> Node {
        // Depth guard: beyond the cap, stop recursing into items and consume the
        // body as a flat balanced token run. Lossless, never a stack overflow.
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
        let n = self.make_node(node::ITEM_BLOCK, c);
        self.depth -= 1;
        n
    }

    // --- items --------------------------------------------------------------

    fn parse_item(&mut self) -> Node {
        let mut c = Vec::new();

        // Decoration prefixes that precede the entity proper: `@attr`,
        // `@attr(...)`, and the paren-carrying compile-time attributes
        // (`pragma(...)`, `extern(C)`, `align(8)`, `deprecated("..")`,
        // `version(X)`, `debug(Y)`). Storage classes (`const`, `static`,
        // `immutable`, …) are intentionally NOT stripped here so the declaration
        // parser can still see them.
        loop {
            self.ws(&mut c);
            if self.at("@") {
                self.eat(&mut c); // @
                self.ws(&mut c);
                if self.at_ident() {
                    self.eat(&mut c); // attribute name
                }
                self.ws(&mut c);
                if self.at("(") {
                    let g = self.parse_delimited(None);
                    c.push(Child::Node(g));
                }
                continue;
            }
            if self.at("pragma")
                || self.at("deprecated")
                || self.at("align")
                || self.at("extern")
                || self.at("version")
                || self.at("debug")
            {
                self.eat(&mut c); // keyword
                self.ws(&mut c);
                if self.at("(") {
                    let g = self.parse_delimited(None);
                    c.push(Child::Node(g));
                }
                continue;
            }
            break;
        }

        self.ws(&mut c);
        match self.peek_kind() {
            None => self.make_node(node::DECL, c),
            Some(_) if self.at("module") => self.finish_module(c),
            Some(_) if self.at("import") => self.finish_import(c),
            Some(_) if self.at("class") => self.finish_record(c, node::CLASS),
            Some(_) if self.at("struct") => self.finish_record(c, node::STRUCT),
            Some(_) if self.at("interface") => self.finish_record(c, node::INTERFACE),
            Some(_) if self.at("union") => self.finish_record(c, node::UNION),
            Some(_) if self.at("enum") => self.finish_enum(c),
            Some(_) if self.at("template") => self.finish_template(c),
            Some(_) if self.at("alias") => self.finish_alias(c),
            Some(_) if self.at("unittest") => self.finish_unittest(c),
            Some(_) if self.at("mixin") => self.finish_mixin(c),
            Some(_) if self.is_access_spec() => self.finish_access_spec(c),
            // A bare `{ ... }` after decorations is an attribute block
            // (`@safe { … }`, `static { … }`, `extern(C) { … }`).
            Some(_) if self.at("{") => self.finish_attr_block(c),
            // Stray closing delimiters: consume one so the caller always advances.
            Some(_) if self.at("}") || self.at(")") || self.at("]") => self.finish_error_item(c),
            Some(_) => self.parse_declaration(c),
        }
    }

    fn is_access_spec(&self) -> bool {
        (self.at("public")
            || self.at("private")
            || self.at("protected")
            || self.at("package")
            || self.at("export"))
            && self.at_n(1, ":")
    }

    fn finish_access_spec(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // visibility keyword
        self.ws(&mut c);
        if self.at(":") {
            self.eat(&mut c);
        }
        self.make_node(node::ACCESS_SPEC, c)
    }

    fn finish_attr_block(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_item_block();
            c.push(Child::Node(b));
        }
        self.make_node(node::ATTR_BLOCK, c)
    }

    fn finish_module(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // module
        self.collect_until_semi(&mut c);
        self.make_node(node::MODULE_DECL, c)
    }

    fn finish_import(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // import
        self.collect_until_semi(&mut c);
        self.make_node(node::IMPORT_DECL, c)
    }

    fn finish_alias(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // alias
        self.collect_until_semi(&mut c);
        self.make_node(node::ALIAS, c)
    }

    fn finish_unittest(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // unittest
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
        }
        self.make_node(node::UNITTEST, c)
    }

    /// `mixin template Name(...) { ... }` → a Template; any other `mixin ...;`
    /// (string mixin, mixin instantiation) is a generic declaration.
    fn finish_mixin(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // mixin
        self.ws(&mut c);
        if self.at("template") {
            return self.finish_template(c);
        }
        self.collect_until_semi(&mut c);
        self.make_node(node::DECL, c)
    }

    /// `template Name(args) { items }`.
    fn finish_template(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // template
        self.ws(&mut c);
        let name_idx = if self.at_ident() {
            let idx = c.len();
            self.eat(&mut c);
            Some(idx)
        } else {
            None
        };
        self.ws(&mut c);
        if self.at("(") {
            let g = self.parse_delimited(None); // template parameter list
            c.push(Child::Node(g));
        }
        self.ws(&mut c);
        if self.at("{") {
            wrap_name(&mut c, name_idx);
            let b = self.parse_item_block();
            c.push(Child::Node(b));
        } else if self.at(";") {
            wrap_name(&mut c, name_idx);
            self.eat(&mut c);
        } else {
            wrap_name(&mut c, name_idx);
        }
        self.make_node(node::TEMPLATE, c)
    }

    /// `class`/`struct`/`interface`/`union` — a definition (`{ ... }`), a forward
    /// declaration (`;`), or an elaborated specifier used in a declaration, which
    /// falls through to the general declaration parser.
    fn finish_record(&mut self, mut c: Vec<Child>, kind: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // class/struct/interface/union
        self.ws(&mut c);
        let name_idx = if self.at_ident() {
            let idx = c.len();
            self.eat(&mut c);
            Some(idx)
        } else {
            None
        };
        self.ws(&mut c);
        // Optional template parameter list: `class C(T) ...`.
        if self.at("(") {
            let g = self.parse_delimited(None);
            c.push(Child::Node(g));
            self.ws(&mut c);
        }
        if self.at(":") {
            // Base-class / interface list: collect up to the opening brace.
            if let Some(h) = self.collect_region(node::HEADER, &["{", ";"]) {
                c.push(Child::Node(h));
            }
        }
        self.ws(&mut c);
        if self.at("{") {
            wrap_name(&mut c, name_idx);
            let b = self.parse_item_block();
            c.push(Child::Node(b));
            self.make_node(kind, c)
        } else if self.at(";") {
            wrap_name(&mut c, name_idx);
            self.eat(&mut c);
            self.make_node(kind, c)
        } else {
            // Elaborated specifier used in a declaration; let the general parser
            // find any declarator.
            self.parse_declaration(c)
        }
    }

    fn finish_enum(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // enum
        self.ws(&mut c);
        let name_idx = if self.at_ident() {
            let idx = c.len();
            self.eat(&mut c);
            Some(idx)
        } else {
            None
        };
        self.ws(&mut c);
        if self.at(":") {
            // Underlying base type.
            if let Some(h) = self.collect_region(node::HEADER, &["{", ";", "="]) {
                c.push(Child::Node(h));
            }
        }
        self.ws(&mut c);
        if self.at("{") {
            wrap_name(&mut c, name_idx);
            let body = self.parse_delimited(Some(node::ENUM_BODY));
            c.push(Child::Node(body));
            self.make_node(node::ENUM, c)
        } else if self.at("=") {
            // Manifest constant: `enum NAME = value;`.
            wrap_name(&mut c, name_idx);
            self.collect_until_semi(&mut c);
            self.make_node(node::ENUM, c)
        } else if self.at(";") {
            wrap_name(&mut c, name_idx);
            self.eat(&mut c);
            self.make_node(node::ENUM, c)
        } else {
            self.parse_declaration(c)
        }
    }

    fn finish_error_item(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // exactly one significant token, guaranteeing progress
        self.diags.push(Diagnostic {
            code: "d.unrecognized_item",
            message: "token not recognized as a D item".to_string(),
            span: children_span(&c).unwrap_or_else(|| ByteSpan::empty_at(self.cur_offset())),
        });
        self.make_node(node::ERROR_ITEM, c)
    }

    /// The general declaration parser: collect specifiers and declarators until a
    /// top-level `;` (declaration) or `{` (definition/body), descending into
    /// balanced `()`/`[]` groups. A `name ( params )` shape marks a function;
    /// `this`/`~this` are recognized as constructor/destructor names.
    fn parse_declaration(&mut self, prefix: Vec<Child>) -> Node {
        let mut c = prefix;
        let mut name_idx: Option<usize> = None;
        let mut have_params = false;
        loop {
            self.ws(&mut c);
            match self.peek_kind() {
                None => break,
                _ if self.at(";") => {
                    self.eat(&mut c);
                    return self.finish_decl(c, name_idx, have_params, false);
                }
                _ if self.at("}") || self.at(")") || self.at("]") => {
                    // Belongs to an enclosing group; stop without consuming.
                    break;
                }
                _ if self.at("{") => {
                    let block = self.parse_delimited(Some(node::BLOCK));
                    c.push(Child::Node(block));
                    self.ws(&mut c);
                    if self.at(";") {
                        self.eat(&mut c);
                    }
                    return self.finish_decl(c, name_idx, have_params, true);
                }
                _ if self.at("(") || self.at("[") => {
                    let is_paren = self.at("(");
                    if is_paren && !have_params {
                        if let Some(ni) = self.declarator_name_idx(&c) {
                            name_idx = Some(ni);
                            have_params = true;
                        }
                    }
                    let g = self.parse_delimited(None);
                    c.push(Child::Node(g));
                }
                _ => self.eat(&mut c),
            }
        }
        self.finish_decl(c, name_idx, have_params, false)
    }

    /// Classify a collected declaration as a `Function` or a generic `Decl`.
    fn finish_decl(
        &self,
        mut c: Vec<Child>,
        name_idx: Option<usize>,
        have_params: bool,
        has_body: bool,
    ) -> Node {
        if have_params {
            if let Some(ni) = name_idx {
                // A bodiless `name(...)` with no preceding specifier is more
                // likely an expression than a real declaration; only the
                // specifier-prefixed or bodied forms become functions.
                let has_specifier = c[..ni].iter().any(is_significant);
                if has_body || has_specifier {
                    wrap_name(&mut c, Some(ni));
                    return self.make_node(node::FUNCTION, c);
                }
            }
        }
        self.make_node(node::DECL, c)
    }

    /// Index in `c` of the declarator name for a function: the last significant
    /// child before the cursor when it is a plain identifier (not a keyword used
    /// as a builtin type or a control construct), or the `this` keyword (a
    /// constructor/destructor name). `None` otherwise, so the construct stays a
    /// generic `Decl`.
    fn declarator_name_idx(&self, c: &[Child]) -> Option<usize> {
        if let Some(prev) = prev_significant(c) {
            if let Child::Token(t) = &c[prev] {
                let text = t.span.text(self.src);
                if t.kind == tk::IDENT && (text == "this" || !is_keyword(text)) {
                    return Some(prev);
                }
            }
        }
        None
    }

    // --- shared helpers -----------------------------------------------------

    /// Collect tokens (descending into balanced groups) up to and including the
    /// next top-level `;`, appending everything to `out`. Stops at EOF or an
    /// enclosing closer without consuming it.
    fn collect_until_semi(&mut self, out: &mut Vec<Child>) {
        loop {
            self.ws(out);
            match self.peek_kind() {
                None => break,
                _ if self.at(";") => {
                    self.eat(out);
                    break;
                }
                _ if self.at("}") || self.at(")") || self.at("]") => break,
                _ if self.at_open() => {
                    let g = self.parse_delimited(None);
                    out.push(Child::Node(g));
                }
                _ => self.eat(out),
            }
        }
    }

    /// Collect tokens (descending into balanced groups) until a significant stop
    /// token at delimiter depth 0, returning them as `label` (or `None` if empty).
    fn collect_region(&mut self, label: &'static str, stops: &[&str]) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            if stops.iter().any(|s| self.at(s)) {
                break;
            }
            if self.at_open() {
                let inner = self.parse_delimited(None);
                c.push(Child::Node(inner));
            } else {
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
    /// is at (or before trivia preceding) the opener. Depth-guarded.
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
            match self.peek_n_text(0) {
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
            code: "d.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; region flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }
}

fn prev_significant(c: &[Child]) -> Option<usize> {
    for (idx, ch) in c.iter().enumerate().rev() {
        match ch {
            Child::Token(t) if t.trivia => continue,
            _ => return Some(idx),
        }
    }
    None
}

fn is_significant(ch: &Child) -> bool {
    match ch {
        Child::Token(t) => !t.trivia,
        Child::Node(_) => true,
    }
}

/// Replace the token at `idx` (if any) with a `Name` node wrapping it, so the
/// lowering can read a definition's name uniformly via `child(NAME)`. Lossless:
/// the same token is preserved, only nested one level deeper.
fn wrap_name(c: &mut [Child], idx: Option<usize>) {
    if let Some(i) = idx {
        if let Child::Token(t) = &c[i] {
            let tok = t.clone();
            c[i] = Child::Node(Node::new(node::NAME, tok.span, vec![Child::Token(tok)]));
        }
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
// a D module
module geo.shapes;

import std.math;
import std.stdio : writeln;

interface Drawable {
    void draw();
}

class Shape : Drawable {
    private double scale;
    this(double s) { this.scale = s; }
    double area() const { return 0.0; }
    void draw() { writeln(\"shape\"); }
}

struct Vec2(T) {
    T x, y;
    T dot(Vec2!T o) { return x * o.x + y * o.y; }
}

enum Color : int { Red, Green = 2, Blue }

enum PI = 3.14159;

immutable int K = 42;

alias Real = double;

double hypot2(double a, double b) {
    return std.math.sqrt(a * a + b * b);
}

unittest {
    assert(hypot2(3, 4) == 5);
}
";
        let tree = parse("shapes.d", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src =
            "module m;\nimport a.b;\nclass C {}\nstruct S {}\nint f() { return 0; }\nenum E { A }\n";
        let tree = parse("t.d", src);
        let kinds: Vec<&str> = tree.root.walk().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::MODULE_DECL), "module: {kinds:?}");
        assert!(kinds.contains(&node::IMPORT_DECL), "import: {kinds:?}");
        assert!(kinds.contains(&node::CLASS), "class: {kinds:?}");
        assert!(kinds.contains(&node::STRUCT), "struct: {kinds:?}");
        assert!(kinds.contains(&node::FUNCTION), "function: {kinds:?}");
        assert!(kinds.contains(&node::ENUM), "enum: {kinds:?}");
    }

    #[test]
    fn methods_nest_inside_class_body() {
        let src = "class C {\n  void a() {}\n  void b() {}\n}\n";
        let tree = parse("t.d", src);
        let class = tree
            .root
            .children_of(node::CLASS)
            .next()
            .expect("a class node");
        let block = class.child(node::ITEM_BLOCK).expect("class body");
        let methods: Vec<&str> = block
            .children_of(node::FUNCTION)
            .filter_map(|f| f.child(node::NAME))
            .filter_map(|n| n.tokens().next())
            .map(|t| t.span.text(src))
            .collect();
        assert_eq!(methods, vec!["a", "b"]);
    }

    #[test]
    fn constructor_is_a_function() {
        let src = "class C {\n  this(int x) {}\n  ~this() {}\n}\n";
        let tree = parse("t.d", src);
        let class = tree.root.children_of(node::CLASS).next().expect("class");
        let block = class.child(node::ITEM_BLOCK).expect("body");
        let fns = block.children_of(node::FUNCTION).count();
        assert_eq!(fns, 2, "ctor + dtor are both Functions");
    }

    #[test]
    fn function_definition_has_body() {
        let src = "int f();\nint g() { return 1; }\n";
        let tree = parse("t.d", src);
        let fns: Vec<&Node> = tree.root.children_of(node::FUNCTION).collect();
        assert_eq!(fns.len(), 2, "prototype + definition are both Functions");
        let g = fns
            .iter()
            .find(|f| {
                f.child(node::NAME)
                    .and_then(|n| n.tokens().next())
                    .map(|t| t.span.text(src))
                    == Some("g")
            })
            .expect("g");
        assert!(g.child(node::BLOCK).is_some(), "g has a body block");
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        // Far deeper than MAX_DEPTH on both axes; must not stack-overflow and must
        // stay lossless.
        let deep_parens = format!("int x = {}{};\n", "(".repeat(10_000), ")".repeat(10_000));
        let mut deep_items = String::new();
        for _ in 0..2_000 {
            deep_items.push_str("class C {");
        }
        deep_items.push_str("int z;");
        for _ in 0..2_000 {
            deep_items.push('}');
        }
        for src in [deep_parens, deep_items] {
            let tree = parse("deep.d", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics.iter().any(|d| d.code == "d.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "int f(int a\n",          // unterminated paren
            "auto s = r\"unclosed",   // unterminated raw string
            "auto t = q{ unclosed",   // unterminated token string
            "char c = '☃'; // snow",  // multi-byte content
            "",                       // empty file
            "/+ unterminated nested", // unterminated nested comment
            "}}})",                   // stray closers
        ] {
            let tree = parse("edge.d", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
