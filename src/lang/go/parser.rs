//! Go parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust parser ([`crate::lang::rust::parser`]): declaration
//! *headers* are parsed precisely — we always know a `func`'s receiver/name, a
//! `type` spec's name, an `import` path — while bodies and expression regions are
//! captured as balanced **token-tree groups** (`Paren`/`Bracket`/`Brace`) plus
//! flat tokens, which is perfectly lossless. Graph facts (calls, type refs) are
//! extracted from these real tokens in the lowering pass, never invented.
//!
//! Go is brace-delimited like Rust, so blocks, struct/interface bodies, and
//! parameter lists are delimiter groups. The one wrinkle is that top-level
//! declarations and the specs inside grouped `import`/`const`/`var`/`type`
//! parentheses are *newline-terminated*. The lexer emits `newline` as a
//! structurally-significant (non-trivia) token, and this parser stops single
//! specs at a `newline` (or the group's `)`) at delimiter depth 0. Newlines
//! inside any `()`/`[]`/`{}` group are ordinary content (Go's implicit line
//! continuation), so multi-line signatures and bodies just work.
//!
//! Anything unrecognized still lands in the tree as its exact tokens (an
//! `ErrorItem` node), so the result always round-trips byte-for-byte. The
//! recursion is depth-guarded at [`MAX_DEPTH`] against hostile delimiter nesting
//! — a `catch_unwind` cannot catch a stack overflow, so the guard is the real
//! defense.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::go::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const PACKAGE_CLAUSE: &str = "PackageClause";
    pub const IMPORT: &str = "Import";
    pub const FUNCTION: &str = "Function";
    pub const TYPE_DECL: &str = "TypeDecl";
    pub const TYPE_SPEC: &str = "TypeSpec";
    pub const VAR_DECL: &str = "VarDecl";
    pub const CONST_DECL: &str = "ConstDecl";
    pub const VALUE_SPEC: &str = "ValueSpec";
    pub const ERROR_ITEM: &str = "ErrorItem";

    pub const NAME: &str = "Name";
    pub const RECEIVER: &str = "Receiver";
    pub const SIGNATURE: &str = "Signature";
    pub const HEADER: &str = "Header";
    pub const BLOCK: &str = "Block";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remaining group iteratively. Mirrors the Rust/Python parsers exactly: a
/// `catch_unwind` cannot catch a stack overflow, so this guard is the real
/// defense against pathological or hostile delimiter nesting.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = GoParser {
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

struct GoParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> GoParser<'s> {
    // --- cursor primitives --------------------------------------------------

    /// Append the current token (trivia or not) to `out` and advance.
    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading **trivia** tokens (whitespace, comments) into
    /// `out`. A `newline` is *not* trivia in Go's grammar here, so it is left in
    /// place — declaration/spec boundaries depend on it.
    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
        }
    }

    /// Move leading trivia **and** newlines and stray `;` separators into `out`.
    /// Used between top-level items and between grouped specs.
    fn skip_separators(&mut self, out: &mut Vec<Child>) {
        loop {
            match self.toks.get(self.i) {
                Some(t) if t.trivia => self.eat(out),
                Some(t) if t.kind == tk::NEWLINE => self.eat(out),
                Some(t) if t.kind == tk::PUNCT && t.span.text(self.src) == ";" => self.eat(out),
                _ => break,
            }
        }
    }

    /// Kind of the n-th significant token from the cursor; `newline` counts as
    /// significant.
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
            let item = self.parse_item();
            c.push(Child::Node(item));
            if self.i == before {
                // Defensive: guarantee forward progress so a stubborn token can
                // never wedge the loop.
                self.eat(&mut c);
            }
        }
        self.make_node(node::SOURCE_FILE, c)
    }

    // --- items --------------------------------------------------------------

    fn parse_item(&mut self) -> Node {
        let c = Vec::new();
        if self.at("package") {
            self.finish_package(c)
        } else if self.at("import") {
            self.finish_import(c)
        } else if self.at("func") {
            self.finish_func(c)
        } else if self.at("type") {
            self.finish_type(c)
        } else if self.at("var") {
            self.finish_value_decl(c, node::VAR_DECL)
        } else if self.at("const") {
            self.finish_value_decl(c, node::CONST_DECL)
        } else {
            self.finish_error_item(c)
        }
    }

    fn finish_package(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // package
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        self.make_node(node::PACKAGE_CLAUSE, c)
    }

    /// `import "path"`, `import alias "path"`, or `import ( ... )`.
    fn finish_import(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // import
        self.ws(&mut c);
        if self.at("(") {
            let g = self.parse_delimited(None);
            c.push(Child::Node(g));
        } else if let Some(h) = self.collect_region(node::HEADER, &[]) {
            c.push(Child::Node(h));
        }
        self.make_node(node::IMPORT, c)
    }

    /// `func [receiver] name[typeparams](params) [results] { body }`. A method's
    /// receiver is the parenthesized group that precedes the name.
    fn finish_func(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // func
        self.ws(&mut c);
        if self.at("(") {
            // Receiver: `(r *T)` before the method name.
            let r = self.parse_delimited(Some(node::RECEIVER));
            c.push(Child::Node(r));
            self.ws(&mut c);
        }
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        // Signature: type params, params, results — up to the body `{` (or the
        // line end for a bodyless forward declaration).
        if let Some(sig) = self.collect_region(node::SIGNATURE, &["{"]) {
            c.push(Child::Node(sig));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
        }
        self.make_node(node::FUNCTION, c)
    }

    /// `type Name ...` or `type ( specs )`.
    fn finish_type(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // type
        self.ws(&mut c);
        if self.at("(") {
            self.parse_spec_group(&mut c, SpecKind::Type);
        } else {
            let spec = self.parse_type_spec();
            c.push(Child::Node(spec));
        }
        self.make_node(node::TYPE_DECL, c)
    }

    /// `var Name ...` / `const Name ...`, single or grouped.
    fn finish_value_decl(&mut self, mut c: Vec<Child>, kind: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // var / const
        self.ws(&mut c);
        if self.at("(") {
            self.parse_spec_group(&mut c, SpecKind::Value);
        } else {
            let spec = self.parse_value_spec();
            c.push(Child::Node(spec));
        }
        self.make_node(kind, c)
    }

    /// Anything not recognized as a declaration: capture a balanced group or a
    /// single token so the tree stays lossless and the cursor always advances.
    fn finish_error_item(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        if self.at_open() {
            let g = self.parse_delimited(None);
            c.push(Child::Node(g));
        } else {
            self.eat(&mut c);
        }
        self.diags.push(Diagnostic {
            code: "go.unrecognized_item",
            message: "token(s) not recognized as a Go declaration".to_string(),
            span: children_span(&c).unwrap_or_else(|| ByteSpan::empty_at(self.cur_offset())),
        });
        self.make_node(node::ERROR_ITEM, c)
    }

    // --- specs --------------------------------------------------------------

    /// Parse the `( ... )` of a grouped declaration, appending the opener, each
    /// newline-separated spec, and the closer to `c`.
    fn parse_spec_group(&mut self, c: &mut Vec<Child>, kind: SpecKind) {
        self.ws(c);
        self.eat(c); // (
        loop {
            self.skip_separators(c);
            match self.peek_kind() {
                None => break,
                _ if self.at(")") => {
                    self.eat(c);
                    break;
                }
                _ => {
                    let before = self.i;
                    let spec = match kind {
                        SpecKind::Type => self.parse_type_spec(),
                        SpecKind::Value => self.parse_value_spec(),
                    };
                    c.push(Child::Node(spec));
                    if self.i == before {
                        self.eat(c); // progress guard
                    }
                }
            }
        }
    }

    /// `Name [typeparams] [=] TypeExpr` — the name is parsed precisely; the type
    /// expression (including any `struct {}` / `interface {}` body, descended as a
    /// balanced group) is captured as a `Header` up to the line end or group `)`.
    fn parse_type_spec(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(h) = self.collect_region(node::HEADER, &[")"]) {
            c.push(Child::Node(h));
        }
        self.make_node(node::TYPE_SPEC, c)
    }

    /// `IdentList [Type] [= ExprList]` — captured whole; the lowering reads the
    /// leading identifier list off the real tokens.
    fn parse_value_spec(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        loop {
            match self.peek_kind() {
                None => break,
                Some(k) if k == tk::NEWLINE => break,
                _ if self.at(")") => break,
                _ => {
                    if self.at_open() {
                        self.ws(&mut c);
                        let g = self.parse_delimited(None);
                        c.push(Child::Node(g));
                    } else {
                        self.ws(&mut c);
                        self.eat(&mut c);
                    }
                }
            }
        }
        self.make_node(node::VALUE_SPEC, c)
    }

    // --- shared helpers -----------------------------------------------------

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.eat(&mut c); // the identifier (cursor is at it after caller ws)
        self.make_node(node::NAME, c)
    }

    /// Collect tokens (descending into balanced groups) until a `newline` or one
    /// of `stops` at delimiter depth 0, or end of input. Leading/trailing trivia
    /// around tokens is consumed; the terminating `newline`/stop stays for the
    /// caller. Returns `None` if nothing was collected.
    fn collect_region(&mut self, label: &'static str, stops: &[&str]) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            // Consume leading trivia so spans stay tight, but do not cross a
            // newline (it terminates the region).
            self.ws(&mut c);
            match self.peek_kind() {
                None => break,
                Some(k) if k == tk::NEWLINE => break,
                _ => {}
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
    /// is at (or before trivia preceding) the opener. Newlines inside the group
    /// are eaten as ordinary content — exactly Go's implicit line continuation
    /// within brackets/braces/parens.
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
    /// deep bracket nesting is handled without further recursion.
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
            code: "go.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; group flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }
}

/// Which spec a grouped declaration's parentheses contain.
enum SpecKind {
    Type,
    Value,
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
// Package geom does geometry.
package geom

import (
\t\"fmt\"
\tm \"math\"
)

const Pi = 3.14159

type Point struct {
\tX, Y float64
}

type Shape interface {
\tArea() float64
\tfmt.Stringer
}

func (p Point) Norm() float64 {
\treturn m.Sqrt(p.X*p.X + p.Y*p.Y)
}

func Add(a, b int) int {
\treturn a + b
}
";
        let tree = parse("geom.go", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src =
            "package p\nimport \"fmt\"\ntype T struct{}\nvar x = 1\nconst y = 2\nfunc f() {}\n";
        let tree = parse("t.go", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::PACKAGE_CLAUSE), "{kinds:?}");
        assert!(kinds.contains(&node::IMPORT), "{kinds:?}");
        assert!(kinds.contains(&node::TYPE_DECL), "{kinds:?}");
        assert!(kinds.contains(&node::VAR_DECL), "{kinds:?}");
        assert!(kinds.contains(&node::CONST_DECL), "{kinds:?}");
        assert!(kinds.contains(&node::FUNCTION), "{kinds:?}");
    }

    #[test]
    fn method_receiver_is_captured() {
        let src = "package p\nfunc (s *Server) Handle(w int) {}\n";
        let tree = parse("t.go", src);
        let f = tree
            .root
            .children_of(node::FUNCTION)
            .next()
            .expect("a function");
        assert!(f.child(node::RECEIVER).is_some(), "method has a receiver");
        let name = f
            .child(node::NAME)
            .and_then(|n| n.tokens().next())
            .map(|t| t.span.text(src));
        assert_eq!(name, Some("Handle"));
    }

    #[test]
    fn grouped_type_decl_has_multiple_specs() {
        let src = "package p\ntype (\n\tA int\n\tB struct{ x int }\n)\n";
        let tree = parse("t.go", src);
        let decl = tree
            .root
            .children_of(node::TYPE_DECL)
            .next()
            .expect("a type decl");
        let specs = decl.children_of(node::TYPE_SPEC).count();
        assert_eq!(specs, 2, "two grouped type specs");
        assert!(tree.is_lossless());
    }

    #[test]
    fn multiline_signature_round_trips() {
        let src = "package p\nfunc f(\n\ta int,\n\tb int,\n) (int, error) {\n\treturn a, nil\n}\n";
        let tree = parse("t.go", src);
        assert!(tree.is_lossless());
        let f = tree
            .root
            .children_of(node::FUNCTION)
            .next()
            .expect("a function");
        assert!(f.child(node::SIGNATURE).is_some());
        assert!(f.child(node::BLOCK).is_some());
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        // Far deeper than MAX_DEPTH; must not stack-overflow and must stay lossless.
        let depth = 10_000;
        let src = format!(
            "package p\nfunc x() {{ {}{} }}\n",
            "(".repeat(depth),
            ")".repeat(depth)
        );
        let tree = parse("deep.go", &src);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics.iter().any(|d| d.code == "go.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "package p\nx := (1, 2\n",                 // unterminated paren
            "package p\nλ := `☃`\n",                   // multi-byte identifiers/strings
            "",                                        // empty file
            "\n\n   \n// trailing\n",                  // only blanks and comments
            "package p\nvar s = `raw\nmultiline\n`\n", // raw string with newlines
        ] {
            let tree = parse("edge.go", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
