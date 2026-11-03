//! Zig parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust/Go parsers: declaration *headers* are parsed
//! precisely — we always know a `fn`'s name, a `const`/`var`'s name, and whether
//! a declaration's initializer is a *type container* — while bodies and
//! expression regions are captured as balanced **token-tree groups**
//! (`Paren`/`Bracket`/`Brace`) plus flat tokens, which is perfectly lossless.
//! Graph facts (calls, type refs, imports) are extracted from these real tokens
//! in the lowering pass, never invented.
//!
//! The defining Zig idiom is that **types are values**: `const Foo = struct {…}`
//! / `enum {…}` / `union {…}` / `opaque {…}`. The parser recognizes this and
//! parses the container body as a recursive **item block** (`ItemBlock`) so nested
//! `fn` declarations (methods), nested types, and nested constants stay
//! first-class CST nodes — exactly how the Rust parser treats `impl`/`mod` bodies.
//! Function bodies (statement regions) and `error {…}` sets are captured as plain
//! balanced groups instead.
//!
//! Anything unrecognized still lands in the tree as its exact tokens (an
//! `ErrorItem` node), so the result always round-trips byte-for-byte. Recursion is
//! depth-guarded at [`MAX_DEPTH`] against hostile delimiter nesting — a
//! `catch_unwind` cannot catch a stack overflow, so the guard is the real defense.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::zig::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const FUNCTION: &str = "Function";
    pub const CONST_DECL: &str = "ConstDecl";
    pub const VAR_DECL: &str = "VarDecl";
    pub const TEST: &str = "Test";
    pub const COMPTIME: &str = "Comptime";
    pub const USINGNAMESPACE: &str = "UsingNamespace";
    pub const FIELD: &str = "Field";
    pub const ERROR_ITEM: &str = "ErrorItem";

    pub const NAME: &str = "Name";
    pub const SIGNATURE: &str = "Signature";
    /// A `const`/`var` type annotation region (`: T`), up to `=` or `;`.
    pub const HEADER: &str = "Header";
    /// A container's header after its keyword (`(u8)`, `(enum)`, …), up to `{`.
    pub const CONTAINER_HEADER: &str = "ContainerHeader";
    /// A plain initializer / value region (non-container), up to `;`.
    pub const VALUE: &str = "Value";
    /// A function body or comptime/test block: a balanced statement region.
    pub const BLOCK: &str = "Block";
    /// A container body parsed recursively as a list of members.
    pub const ITEM_BLOCK: &str = "ItemBlock";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remaining group iteratively. Mirrors the Rust/Go parsers exactly: a
/// `catch_unwind` cannot catch a stack overflow, so this guard is the real
/// defense against pathological or hostile delimiter nesting.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = ZigParser {
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

struct ZigParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> ZigParser<'s> {
    // --- cursor primitives --------------------------------------------------

    /// Append the current token (trivia or not) to `out` and advance.
    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading trivia tokens (whitespace, comments — including
    /// doc comments) into `out`. Zig has no structurally-significant whitespace.
    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
        }
    }

    /// Kind of the n-th significant token from the cursor.
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
            let before = self.i;
            let item = self.parse_member();
            c.push(Child::Node(item));
            if self.i == before {
                // Defensive: guarantee forward progress so a stubborn token can
                // never wedge the loop.
                self.eat(&mut c);
            }
        }
        self.make_node(node::SOURCE_FILE, c)
    }

    /// Parse one container member: a declaration (`const`/`var`/`fn`), a `test`
    /// or `comptime` block, a `usingnamespace`, a struct/enum/union *field*, or an
    /// unrecognized run (`ErrorItem`). Used at file scope and inside every
    /// `ItemBlock`.
    fn parse_member(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);

        // `test` and a bare `comptime { … }` block stand alone (never `pub`).
        if self.at("test") {
            return self.finish_test(c);
        }
        if self.at("comptime") && self.at_n(1, "{") {
            return self.finish_comptime(c);
        }

        // Visibility + leading modifiers.
        if self.at("pub") {
            self.eat(&mut c);
        }
        loop {
            self.ws(&mut c);
            if self.at("inline")
                || self.at("noinline")
                || self.at("threadlocal")
                || self.at("comptime")
                || self.at("export")
            {
                self.eat(&mut c);
            } else if self.at("extern") {
                self.eat(&mut c);
                self.ws(&mut c);
                if matches!(self.peek_kind(), Some(k) if k == tk::STRING) {
                    self.eat(&mut c); // extern abi / linkage string
                }
            } else {
                break;
            }
        }

        // Dispatch on the declaration keyword.
        self.ws(&mut c);
        if self.at("fn") {
            self.finish_fn(c)
        } else if self.at("const") {
            self.finish_decl(c, node::CONST_DECL)
        } else if self.at("var") {
            self.finish_decl(c, node::VAR_DECL)
        } else if self.at("usingnamespace") {
            self.finish_usingnamespace(c)
        } else if self.at_ident() {
            // A leading identifier at container scope is a field declaration.
            self.finish_field(c)
        } else {
            self.finish_error_item(c)
        }
    }

    /// Parse `{ members }` as a recursive member list (a type container body).
    fn parse_item_block(&mut self, label: &'static str) -> Node {
        // Depth guard: beyond the cap, stop recursing into members and consume the
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
                    let before = self.i;
                    let item = self.parse_member();
                    c.push(Child::Node(item));
                    if self.i == before {
                        self.eat(&mut c); // progress guard
                    }
                }
            }
        }
        let node = self.make_node(label, c);
        self.depth -= 1;
        node
    }

    // --- members ------------------------------------------------------------

    /// `fn name(params) ReturnType { body }` or a bodyless `;` (extern/forward).
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

    /// `const NAME [: T] [= value] ;` / `var NAME [: T] [= value] ;`. The value is
    /// parsed by [`Self::parse_value`], which recognizes a type container and
    /// descends its body as an `ItemBlock`.
    fn finish_decl(&mut self, mut c: Vec<Child>, kind: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // const / var
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        // Type annotation `: T`, captured up to `=` or `;`.
        if let Some(h) = self.collect_region(node::HEADER, &["=", ";"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("=") {
            self.eat(&mut c); // =
            self.parse_value(&mut c);
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(kind, c)
    }

    /// Parse a declaration initializer into `c`. Recognizes the type-container
    /// idiom (`[packed|extern] struct|enum|union|opaque { … }`) and parses the
    /// body as a recursive `ItemBlock`; an `error { … }` set body as a plain
    /// `Brace` group; everything else as a flat `Value` region up to `;`.
    fn parse_value(&mut self, c: &mut Vec<Child>) {
        self.ws(c);
        // Container layout modifiers immediately before the container keyword.
        loop {
            if (self.at("packed") || self.at("extern"))
                && (self.at_n(1, "struct")
                    || self.at_n(1, "union")
                    || self.at_n(1, "enum")
                    || self.at_n(1, "opaque"))
            {
                self.eat(c);
                self.ws(c);
            } else {
                break;
            }
        }

        if self.at("struct") || self.at("union") || self.at("enum") || self.at("opaque") {
            self.eat(c); // container keyword (a loose token; lowering reads it)
            if let Some(h) = self.collect_region(node::CONTAINER_HEADER, &["{"]) {
                c.push(Child::Node(h));
            }
            self.ws(c);
            if self.at("{") {
                let b = self.parse_item_block(node::ITEM_BLOCK);
                c.push(Child::Node(b));
            }
            if let Some(v) = self.collect_region(node::VALUE, &[";"]) {
                c.push(Child::Node(v));
            }
        } else if self.at("error") && self.at_n(1, "{") {
            self.eat(c); // error (loose token; lowering reads it)
            self.ws(c);
            if self.at("{") {
                let b = self.parse_delimited(Some(node::BRACE));
                c.push(Child::Node(b));
            }
            if let Some(v) = self.collect_region(node::VALUE, &[";"]) {
                c.push(Child::Node(v));
            }
        } else if let Some(v) = self.collect_region(node::VALUE, &[";"]) {
            c.push(Child::Node(v));
        }
    }

    /// `test "name" { … }` or `test ident { … }` or `test { … }`.
    fn finish_test(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // test
        self.ws(&mut c);
        if matches!(self.peek_kind(), Some(k) if k == tk::STRING) || self.at_ident() {
            self.eat(&mut c); // test name (string) or referenced decl ident
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
        }
        self.make_node(node::TEST, c)
    }

    /// `comptime { … }` block.
    fn finish_comptime(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // comptime
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
        }
        self.make_node(node::COMPTIME, c)
    }

    /// `usingnamespace expr;`.
    fn finish_usingnamespace(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // usingnamespace
        if let Some(v) = self.collect_region(node::VALUE, &[";"]) {
            c.push(Child::Node(v));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::USINGNAMESPACE, c)
    }

    /// A struct/enum/union field: `name [: T] [= default] ,`. Enum fields may be a
    /// bare `name,`. Captured up to the next top-level `,`, `;`, or `}`.
    fn finish_field(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(h) = self.collect_region(node::HEADER, &[",", ";", "}"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at(",") || self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::FIELD, c)
    }

    /// Anything not recognized: capture a balanced group or a single token so the
    /// tree stays lossless and the cursor always advances.
    fn finish_error_item(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        if self.at_open() {
            let g = self.parse_delimited(None);
            c.push(Child::Node(g));
        } else {
            self.eat(&mut c);
        }
        self.diags.push(Diagnostic {
            code: "zig.unrecognized_item",
            message: "token(s) not recognized as a Zig declaration".to_string(),
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
            match self.peek_n_text(0) {
                None => break,
                Some("(") | Some("[") | Some("{") => balance += 1,
                Some(")") | Some("]") | Some("}") => balance -= 1,
                _ => {}
            }
            self.eat(out);
        }
    }

    /// Record that the depth cap flattened structure — reported, never silent.
    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "zig.depth_limit",
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
//! A geometry module.
const std = @import(\"std\");

/// A point in 2D space.
const Point = struct {
    x: f64,
    y: f64,

    pub fn norm(self: Point) f64 {
        return @sqrt(self.x * self.x + self.y * self.y);
    }

    pub fn origin() Point {
        return Point{ .x = 0, .y = 0 };
    }
};

const Color = enum(u8) {
    red,
    green,
    blue,
};

const Shape = union(enum) {
    circle: f64,
    rect: Point,
};

const FileError = error{ NotFound, Permission };

pub const MAX: u32 = 100;
var counter: u32 = 0;

const banner =
    \\\\line one
    \\\\line two
;

pub fn add(a: i32, b: i32) i32 {
    return a + b;
}

test \"add works\" {
    _ = add(1, 2);
}
";
        let tree = parse("geom.zig", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_members() {
        let src =
            "const A = struct {};\nvar x = 1;\npub const Y = 2;\nfn f() void {}\ntest \"t\" {}\n";
        let tree = parse("t.zig", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::CONST_DECL), "{kinds:?}");
        assert!(kinds.contains(&node::VAR_DECL), "{kinds:?}");
        assert!(kinds.contains(&node::FUNCTION), "{kinds:?}");
        assert!(kinds.contains(&node::TEST), "{kinds:?}");
    }

    #[test]
    fn struct_container_body_is_item_block() {
        let src = "const S = struct {\n    a: i32,\n    pub fn m(self: S) void {}\n};\n";
        let tree = parse("t.zig", src);
        let decl = tree
            .root
            .children_of(node::CONST_DECL)
            .next()
            .expect("a const decl");
        let block = decl.child(node::ITEM_BLOCK).expect("an item block body");
        // The nested method is a first-class Function node in the tree.
        assert!(block.child_nodes().any(|n| n.kind == node::FUNCTION));
        assert!(block.child_nodes().any(|n| n.kind == node::FIELD));
    }

    #[test]
    fn import_is_a_const_value() {
        let src = "const std = @import(\"std\");\n";
        let tree = parse("t.zig", src);
        let decl = tree
            .root
            .children_of(node::CONST_DECL)
            .next()
            .expect("a const decl");
        assert!(decl.child(node::VALUE).is_some(), "import lives in a Value");
        assert!(tree.is_lossless());
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        // Far deeper than MAX_DEPTH; must not stack-overflow and must stay lossless.
        let depth = 10_000;
        let src = format!(
            "fn x() void {{ {}{} }}",
            "(".repeat(depth),
            ")".repeat(depth)
        );
        let tree = parse("deep.zig", &src);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics.iter().any(|d| d.code == "zig.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "const x = (1, 2\n",                         // unterminated paren
            "const λ = \"☃\";\n",                        // multi-byte ident/string
            "",                                          // empty file
            "\n\n   \n// trailing\n",                    // only blanks/comments
            "const s =\n    \\\\raw\n    \\\\more\n;\n", // multiline string
            "const E = error{A, B};\n",                  // error set
        ] {
            let tree = parse("edge.zig", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
