//! C parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust and Python parsers ([`crate::lang::rust::parser`],
//! [`crate::lang::python::parser`]): item *headers* are parsed precisely enough to
//! classify each top-level construct and find its name, while expression regions,
//! parameter lists, and bodies are captured as balanced **token-tree groups**
//! (`Paren`/`Bracket`/`Brace`) plus flat tokens, which is perfectly lossless.
//! Graph facts (calls, type uses, includes) are later read off these real tokens
//! in the lowering pass, never invented.
//!
//! C has no keyword that introduces an ordinary function or object declaration, so
//! the parser collects a **declaration unit** — every token and balanced group up
//! to the terminator that ends it — and classifies afterward:
//!   - a top-level `{ … }` reached after a parameter `( … )` (and no `=` and no
//!     `struct`/`union`/`enum`) is a **function body**: the unit is a definition;
//!   - a top-level `{ … }` belonging to an aggregate (`struct`/`union`/`enum`) or
//!     an initializer (`= { … }`) is part of the declaration, which still ends at
//!     its `;`;
//!   - otherwise the unit ends at a top-level `;`.
//!
//! Preprocessor directives (lines whose first significant token is `#`) are parsed
//! as their own line-terminated items, with `#include`/`#define` recognized
//! precisely; backslash–newline continuations are lexer trivia, so a multi-line
//! directive is one logical line here.
//!
//! Anything unrecognized still lands in the tree as its exact tokens (a flat run
//! or an `ErrorItem`), so the result always round-trips byte-for-byte. The
//! recursion into balanced groups is depth-guarded at [`MAX_DEPTH`] against hostile
//! nesting, because a `catch_unwind` cannot catch a stack overflow.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::c::lexer::{is_keyword, kind as tk, lex};

/// CST node-kind labels. The lowering interprets these.
pub mod node {
    pub const UNIT: &str = "Unit";
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
/// remainder as a flat balanced run. Protects against stack overflow on
/// pathological or hostile inputs — mirrors the Rust and Python parsers' guard
/// exactly, since a `catch_unwind` cannot catch a stack overflow.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = CParser {
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

struct CParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current group-nesting depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> CParser<'s> {
    // --- cursor primitives --------------------------------------------------

    /// Append the current token (trivia or not) to `out` and advance.
    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading **trivia** tokens (whitespace, comments, line
    /// continuations) into `out`. A `newline` is *not* trivia in C, so it is left
    /// in place — directive structure depends on it.
    fn ws(&mut self, out: &mut Vec<Child>) {
        while matches!(self.toks.get(self.i), Some(t) if t.trivia) {
            self.eat(out);
        }
    }

    /// Move leading trivia **and** structural newlines into `out`. Used between
    /// top-level items, where blank lines are mere separators.
    fn trivia_and_newlines(&mut self, out: &mut Vec<Child>) {
        while let Some(t) = self.toks.get(self.i) {
            if t.trivia || t.kind == tk::NEWLINE {
                self.eat(out);
            } else {
                break;
            }
        }
    }

    /// Kind of the n-th significant (non-trivia) token from the cursor; `newline`
    /// counts as significant.
    fn peek_kind_n(&self, n: usize) -> Option<&'static str> {
        let mut count = 0;
        for t in &self.toks[self.i..] {
            if t.trivia {
                continue;
            }
            if count == n {
                return Some(t.kind);
            }
            count += 1;
        }
        None
    }

    fn peek_kind(&self) -> Option<&'static str> {
        self.peek_kind_n(0)
    }

    /// Text of the first significant (non-trivia) token from the cursor.
    fn peek_text(&self) -> Option<&str> {
        for t in &self.toks[self.i..] {
            if t.trivia {
                continue;
            }
            return Some(t.span.text(self.src));
        }
        None
    }

    fn at(&self, s: &str) -> bool {
        self.peek_text() == Some(s)
    }

    fn at_newline(&self) -> bool {
        self.peek_kind() == Some(tk::NEWLINE)
    }

    /// True when the cursor sits on a `newline` whose next significant token is a
    /// `#` — i.e. a preprocessor directive begins on the following line. Used to
    /// stop a runaway declaration from swallowing a directive.
    fn next_significant_is_hash(&self) -> bool {
        for t in &self.toks[self.i..] {
            if t.trivia || t.kind == tk::NEWLINE {
                continue;
            }
            return t.span.text(self.src) == "#";
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
        } else {
            self.parse_decl()
        }
    }

    /// A preprocessor directive: `#` then the rest of the logical line (up to and
    /// including the terminating `newline`). `#include`/`#define` are tagged
    /// precisely; everything else is a generic `Directive`.
    fn parse_directive(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // '#'
        self.ws(&mut c);
        let kw = self.peek_text().map(|s| s.to_string());
        // Collect the rest of the logical line as flat leaves. Line continuations
        // were absorbed by the lexer as trivia, so a `newline` here is the true end.
        loop {
            match self.toks.get(self.i) {
                None => break,
                Some(t) if t.kind == tk::NEWLINE => break,
                Some(_) => self.eat(&mut c),
            }
        }
        if self.at_newline() {
            self.eat(&mut c);
        }
        let kind = match kw.as_deref() {
            Some("include") | Some("include_next") | Some("import") => node::INCLUDE,
            Some("define") => node::DEFINE,
            _ => node::DIRECTIVE,
        };
        self.make_node(kind, c)
    }

    /// Collect and classify one declaration unit (see the module comment).
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
                if started && self.next_significant_is_hash() {
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
                    // A `{` is a function body when a parameter list preceded it and
                    // it is not an initializer (`= { … }`). An aggregate body's `{`
                    // has *no* preceding top-level paren, so `saw_paren` distinguishes
                    // `struct S { … }` (false) from `struct T f(void) { … }` (true),
                    // i.e. a function whose return type is an aggregate.
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
                    // Stray closer at the top level: keep it (lossless) and make
                    // progress rather than recursing or looping.
                    self.eat(&mut c);
                    started = true;
                }
                "#" => {
                    if started {
                        break; // let the item loop re-dispatch the directive
                    }
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
            node::TYPEDEF => typedef_alias_idx(&c, self.src),
            node::STRUCT | node::UNION | node::ENUM => tag_name_idx(&c, self.src),
            node::DECL => decl_name_idx(&c, self.src),
            _ => None,
        };
        let c = wrap_name(c, name_idx);
        self.make_node(kind, c)
    }

    /// After a function body's `}`, swallow a stray same-line `;` (e.g. `};`) so it
    /// does not start a junk empty item. Only consumes a `;` on the same logical
    /// line (a `newline` before it leaves it for the next item).
    fn maybe_eat_trailing_semi(&mut self, out: &mut Vec<Child>) {
        if self.at(";") {
            self.ws(out);
            self.eat(out);
        }
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`. The cursor is
    /// at the opener. Newlines inside the group are eaten as ordinary content.
    /// Depth-guarded: beyond [`MAX_DEPTH`] the nested group is flattened rather
    /// than recursed, so deep nesting cannot overflow.
    fn parse_group(&mut self) -> Node {
        let mut g = Vec::new();
        let (close, label) = {
            match self.toks.get(self.i).map(|t| t.span.text(self.src)) {
                Some("(") => (")", node::PAREN),
                Some("[") => ("]", node::BRACKET),
                Some("{") => ("}", node::BRACE),
                _ => (")", node::PAREN),
            }
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
    /// appending every token as a flat leaf. Used at the depth cap so arbitrarily
    /// deep bracket nesting is handled without further recursion.
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

    /// Record (once per truncation) that the depth cap flattened structure —
    /// reported, never silent.
    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "c.depth_limit",
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

/// True for `struct S;` / `enum E;` style forward declarations: an aggregate
/// keyword with exactly one non-keyword identifier (the tag), no groups, no `=`.
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

/// Index of a typedef alias: the last top-level non-keyword identifier.
fn typedef_alias_idx(c: &[Child], src: &str) -> Option<usize> {
    (0..c.len()).rev().find(|&i| {
        ident_tok_text(&c[i], src)
            .map(|t| !is_keyword(t))
            .unwrap_or(false)
    })
}

/// Index of an aggregate tag: the first non-keyword identifier following the
/// `struct`/`union`/`enum` keyword, or `None` if the aggregate is anonymous.
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
            // Any other token (e.g. `{`) or a group means no tag name.
            _ => return None,
        }
    }
    None
}

/// Index of a plain declaration's name: the last non-keyword identifier before
/// the first top-level `=`, bracket, or parameter group.
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
/* a translation unit */
#include <stdio.h>
#include \"point.h\"

#define MAX(a, b) ((a) > (b) ? (a) : (b))
#define VERSION 2

typedef struct Point {
    int x;
    int y;
} Point;

enum Color { RED, GREEN, BLUE };

static int g_count = 0;

int add(int a, int b) {
    return a + b;
}

int main(void) {
    Point p = { .x = 1, .y = 2 };
    int m = MAX(add(p.x, p.y), g_count);
    printf(\"%d\\n\", m);
    return 0;
}
";
        let tree = parse("unit.c", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "#include <stdio.h>\nstruct S { int a; };\nint f(void) { return 0; }\n";
        let tree = parse("t.c", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::INCLUDE), "include: {kinds:?}");
        assert!(kinds.contains(&node::STRUCT), "struct: {kinds:?}");
        assert!(kinds.contains(&node::FUNCTION), "function: {kinds:?}");
    }

    #[test]
    fn function_definition_has_name_and_body() {
        let src = "static int add(int a, int b) {\n    return a + b;\n}\n";
        let tree = parse("t.c", src);
        let f = tree
            .root
            .children_of(node::FUNCTION)
            .next()
            .expect("a function");
        assert_eq!(name_of(f, src).as_deref(), Some("add"));
        assert!(f.child(node::BRACE).is_some(), "function body is a Brace");
        assert!(f.child(node::PAREN).is_some(), "params are a Paren");
    }

    #[test]
    fn prototype_is_declaration_not_function() {
        let src = "int add(int a, int b);\n";
        let tree = parse("t.c", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::DECL), "prototype is a Declaration");
        assert!(
            !kinds.contains(&node::FUNCTION),
            "prototype must not be a Function definition"
        );
    }

    #[test]
    fn typedef_and_aggregate_names() {
        let src = "typedef struct Node { int v; } Node;\nunion U { int i; float f; };\n";
        let tree = parse("t.c", src);
        let td = tree
            .root
            .children_of(node::TYPEDEF)
            .next()
            .expect("a typedef");
        assert_eq!(name_of(td, src).as_deref(), Some("Node"));
        let u = tree.root.children_of(node::UNION).next().expect("a union");
        assert_eq!(name_of(u, src).as_deref(), Some("U"));
    }

    #[test]
    fn global_variable_is_declaration_with_name() {
        let src = "static const int LIMIT = 100;\n";
        let tree = parse("t.c", src);
        let d = tree
            .root
            .children_of(node::DECL)
            .next()
            .expect("a declaration");
        assert_eq!(name_of(d, src).as_deref(), Some("LIMIT"));
    }

    #[test]
    fn directive_does_not_swallow_following_directive() {
        // An unterminated-looking line followed by a directive must not merge them.
        let src = "int x =\n#define Y 1\nY;\n";
        let tree = parse("t.c", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(
            kinds.contains(&node::DEFINE),
            "define recognized: {kinds:?}"
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
        let tree = parse("deep.c", &deep);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics.iter().any(|d| d.code == "c.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }

    #[test]
    fn edge_cases_round_trip() {
        for src in [
            "",                                 // empty file
            "\n\n   \n/* trailing */\n",        // only blanks and comments
            "int a = (1, 2;\n",                 // unterminated paren
            "char *s = \"oops\nint y;\n",       // unterminated string
            "λ = '☃';  // unicode\n",           // multi-byte
            "struct S;\nstruct S var;\n",       // forward decl vs variable
            "#\n#  pragma once\n# 1 \"x.c\"\n", // null + pragma + line marker
            "int (*fp)(int) = 0;\n",            // function pointer decl
        ] {
            let tree = parse("edge.c", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
