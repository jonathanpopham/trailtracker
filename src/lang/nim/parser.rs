//! Nim parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Python parser ([`crate::lang::python::parser`]):
//! declaration *headers* are parsed precisely — we always know a routine's name
//! and parameter region, a `type` definition's right-hand side, a `const`/`let`/
//! `var` binder, an `import` path — while bodies and expression regions are
//! captured as balanced **token-tree groups** (`Paren`/`Bracket`/`Brace`) plus
//! flat tokens, which is perfectly lossless. Graph facts (calls, type refs,
//! inheritance) are extracted from those real tokens in the lowering pass, never
//! invented.
//!
//! Nim is indentation-significant. The lexer emits structurally-significant
//! `newline` tokens and leading-indentation `whitespace` trivia; this parser
//! derives block structure from them — a declaration's body / section is the
//! maximal run of following logical lines whose indentation exceeds the header's.
//! Bodies are consumed as a *flat token region* (no full statement layout), which
//! is enough to round-trip and to harvest call/type facts; nested routines inside
//! a body are not separately scoped (an honest punt — see `mod.rs`).
//!
//! Anything unrecognized still lands in the tree as its exact tokens, so the
//! result always round-trips byte-for-byte. The recursion is depth-guarded at
//! [`MAX_DEPTH`] against hostile bracket nesting; indentation nesting is handled
//! iteratively (no per-level recursion), so it cannot overflow either.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::nim::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const MODULE: &str = "Module";
    /// A `proc`/`func`/`method`/`iterator`/`converter`/`template`/`macro`.
    pub const ROUTINE: &str = "Routine";
    /// A `type` section (one or many `TypeDef`s).
    pub const TYPE_SECTION: &str = "TypeSection";
    /// A single `Name = <rhs>` type definition.
    pub const TYPE_DEF: &str = "TypeDef";
    /// A `const`/`let`/`var` section (one or many `VarDef`s).
    pub const VAR_SECTION: &str = "VarSection";
    /// A single `Name … = <value>` binding.
    pub const VAR_DEF: &str = "VarDef";
    /// An `import`/`from`/`include`/`export` statement.
    pub const IMPORT: &str = "Import";
    /// Any other statement (control flow, expression, call, …).
    pub const STMT: &str = "Stmt";
    pub const ERROR_STMT: &str = "ErrorStmt";

    pub const NAME: &str = "Name";
    pub const HEADER: &str = "Header";
    pub const BLOCK: &str = "Block";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum bracket-nesting depth before the parser stops recursing and consumes
/// the remainder as a flat balanced run. Mirrors the Rust/Python parsers exactly,
/// since a `catch_unwind` cannot catch a stack overflow.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = NimParser {
        src: source,
        toks,
        i: 0,
        diags: Vec::new(),
        depth: 0,
        stmt_indent: 0,
    };
    let root = p.parse_module();
    ParseTree {
        source_id: SourceId::from_path(path),
        path: path.to_string(),
        source: source.to_string(),
        root,
        diagnostics: p.diags,
    }
}

/// Routine-introducing keywords. All lower to `Function` (distinguished by a
/// `routine_kind` property) — see the lowering.
const ROUTINE_KW: &[&str] = &[
    "proc",
    "func",
    "method",
    "iterator",
    "converter",
    "template",
    "macro",
];

const VAR_KW: &[&str] = &["const", "let", "var"];
const IMPORT_KW: &[&str] = &["import", "from", "include", "export"];

struct NimParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current bracket-nesting recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
    /// Leading-whitespace byte width of the statement currently being parsed;
    /// read when bounding its indented body/section.
    stmt_indent: i64,
}

impl<'s> NimParser<'s> {
    // --- cursor primitives --------------------------------------------------

    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading **trivia** tokens (whitespace, comments) into
    /// `out`. A `newline` is *not* trivia in Nim, so it is left in place — block
    /// structure depends on it.
    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
        }
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

    fn peek_kind(&self) -> Option<&'static str> {
        self.peek_kind_n(0)
    }

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

    fn at_newline(&self) -> bool {
        self.peek_kind() == Some(tk::NEWLINE)
    }

    fn at_open(&self) -> bool {
        self.at("(") || self.at("[") || self.at("{")
    }

    /// Leading indentation of the line at the cursor, in bytes. Assumes the cursor
    /// sits at the start of a code line (callers reach that via `skip_blank_lines`).
    fn line_indent(&self) -> i64 {
        match self.toks.get(self.i) {
            Some(t) if t.kind == tk::WHITESPACE => t.span.len() as i64,
            _ => 0,
        }
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

    fn parse_module(&mut self) -> Node {
        let mut c = Vec::new();
        self.parse_statements(-1, &mut c);
        self.make_node(node::MODULE, c)
    }

    /// Parse a run of statements more indented than `parent_indent`, appending
    /// each (and inter-statement blank/comment trivia) to `into`. Stops at the
    /// first code line dedenting to `parent_indent` or shallower, or at EOF.
    fn parse_statements(&mut self, parent_indent: i64, into: &mut Vec<Child>) {
        loop {
            self.skip_blank_lines(into);
            if self.peek_kind().is_none() {
                break;
            }
            if self.line_indent() <= parent_indent {
                break;
            }
            let before = self.i;
            let stmt = self.parse_statement();
            into.push(Child::Node(stmt));
            // Progress guard: a statement must consume at least one token.
            if self.i == before {
                self.eat(into);
            }
        }
    }

    /// Consume blank lines and comment-only lines into `out`, leaving the cursor at
    /// the leading whitespace of the next code line (so indentation can be
    /// measured) or at EOF. Trailing trivia with no terminating newline is kept too.
    fn skip_blank_lines(&mut self, out: &mut Vec<Child>) {
        loop {
            let mut j = self.i;
            while j < self.toks.len() && self.toks[j].trivia {
                j += 1;
            }
            match self.toks.get(j) {
                None => {
                    while self.i < self.toks.len() {
                        self.eat(out);
                    }
                    return;
                }
                Some(t) if t.kind == tk::NEWLINE => {
                    while self.i <= j {
                        self.eat(out);
                    }
                }
                Some(_) => return,
            }
        }
    }

    // --- statements ---------------------------------------------------------

    fn parse_statement(&mut self) -> Node {
        self.stmt_indent = self.line_indent();
        let mut c = Vec::new();
        self.ws(&mut c); // leading indentation

        match self.peek_text() {
            Some(t) if ROUTINE_KW.contains(&t) => self.finish_routine(c),
            Some("type") => self.finish_type_section(c),
            Some(t) if VAR_KW.contains(&t) => self.finish_var_section(c),
            Some(t) if IMPORT_KW.contains(&t) => self.finish_import(c),
            None => {
                // Only trivia remained; keep it (lossless) as an error stmt.
                self.eat(&mut c);
                self.make_node(node::ERROR_STMT, c)
            }
            _ if self.at_newline() => {
                self.eat(&mut c);
                self.make_node(node::ERROR_STMT, c)
            }
            _ => self.finish_generic(c),
        }
    }

    /// `proc NAME[gen](params): Ret {.pragmas.} = body`. The name, the header up to
    /// the body-introducing `=`, and the indented (or inline) body are captured.
    fn finish_routine(&mut self, mut c: Vec<Child>) -> Node {
        let header_indent = self.stmt_indent;
        self.eat(&mut c); // routine keyword
        self.ws(&mut c);
        // The name: an identifier or accent-quoted operator (`` `+` ``).
        if self.peek_kind() == Some(tk::NAME) {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(h) = self.collect_until_eq() {
            c.push(Child::Node(h));
        }
        self.parse_body(header_indent, &mut c);
        self.make_node(node::ROUTINE, c)
    }

    /// `type` section: either inline (`type Foo = object …`) or a block of defs
    /// under a bare `type` line.
    fn finish_type_section(&mut self, mut c: Vec<Child>) -> Node {
        let section_indent = self.stmt_indent;
        self.eat(&mut c); // type
        self.ws(&mut c);
        if self.at_newline() {
            self.eat(&mut c);
            let block = self.parse_def_block(section_indent, DefKind::Type);
            c.push(Child::Node(block));
        } else {
            let def = self.parse_type_def();
            c.push(Child::Node(def));
        }
        self.make_node(node::TYPE_SECTION, c)
    }

    /// `const`/`let`/`var` section: inline single binding or an indented block.
    fn finish_var_section(&mut self, mut c: Vec<Child>) -> Node {
        let section_indent = self.stmt_indent;
        self.eat(&mut c); // const/let/var
        self.ws(&mut c);
        if self.at_newline() {
            self.eat(&mut c);
            let block = self.parse_def_block(section_indent, DefKind::Var);
            c.push(Child::Node(block));
        } else {
            let def = self.parse_var_def();
            c.push(Child::Node(def));
        }
        self.make_node(node::VAR_SECTION, c)
    }

    /// A block of `TypeDef`/`VarDef` lines all indented deeper than `section_indent`.
    fn parse_def_block(&mut self, section_indent: i64, which: DefKind) -> Node {
        let mut c = Vec::new();
        loop {
            self.skip_blank_lines(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            if self.line_indent() <= section_indent {
                break;
            }
            let before = self.i;
            let def = match which {
                DefKind::Type => self.parse_type_def(),
                DefKind::Var => self.parse_var_def(),
            };
            c.push(Child::Node(def));
            if self.i == before {
                self.eat(&mut c); // progress guard
            }
        }
        self.make_node(node::BLOCK, c)
    }

    /// One `Name[gen] = <rhs>` definition, plus any deeper-indented field region
    /// (object/enum bodies). The rhs (`object`, `enum`, `object of Base`, an alias,
    /// …) is captured as a `Header`; the lowering reads it.
    fn parse_type_def(&mut self) -> Node {
        let def_indent = self.line_indent();
        let mut c = Vec::new();
        self.ws(&mut c);
        if self.peek_kind() == Some(tk::NAME) {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        // Everything up to end of the logical line is the rhs header (it may carry
        // `*` export markers, generic `[T]`, `= object of Base`, pragmas).
        if let Some(h) = self.collect_line_header() {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at_newline() {
            self.eat(&mut c);
        }
        // Object/enum fields: an indented region, captured flat (lossless).
        if self.line_indent() > def_indent && self.peek_kind().is_some() {
            let block = self.parse_region(def_indent);
            c.push(Child::Node(block));
        }
        self.make_node(node::TYPE_DEF, c)
    }

    /// One `Name … = value` binding. The remainder of the line (type annotation,
    /// value) is a `Header`; the lowering reads only the bound name.
    fn parse_var_def(&mut self) -> Node {
        let def_indent = self.line_indent();
        let mut c = Vec::new();
        self.ws(&mut c);
        if self.peek_kind() == Some(tk::NAME) {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(h) = self.collect_line_header() {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at_newline() {
            self.eat(&mut c);
        }
        // A value spanning indented continuation lines (rare) is kept lossless.
        if self.line_indent() > def_indent && self.peek_kind().is_some() {
            let block = self.parse_region(def_indent);
            c.push(Child::Node(block));
        }
        self.make_node(node::VAR_DEF, c)
    }

    fn finish_import(&mut self, mut c: Vec<Child>) -> Node {
        self.eat(&mut c); // import/from/include/export
        self.collect_line(&mut c);
        self.ws(&mut c);
        if self.at_newline() {
            self.eat(&mut c);
        }
        self.make_node(node::IMPORT, c)
    }

    /// Any other statement (control flow, an expression, a call). The line is
    /// captured, and if deeper-indented lines follow they are taken as a flat body
    /// region so call/type facts inside `if`/`for`/`while`/`block` bodies survive.
    fn finish_generic(&mut self, mut c: Vec<Child>) -> Node {
        let stmt_indent = self.stmt_indent;
        self.collect_line(&mut c);
        self.ws(&mut c);
        if self.at_newline() {
            self.eat(&mut c);
        }
        if self.line_indent() > stmt_indent && self.peek_kind().is_some() {
            let block = self.parse_region(stmt_indent);
            c.push(Child::Node(block));
        }
        self.make_node(node::STMT, c)
    }

    // --- bodies / regions ---------------------------------------------------

    /// After a routine header, attach the body: consume the `=` (if present) then
    /// either an inline body (statements after `=` on the same line) or an indented
    /// block. Forward declarations (no `=`) get no block — still lossless.
    fn parse_body(&mut self, header_indent: i64, c: &mut Vec<Child>) {
        self.ws(c);
        if self.at("=") {
            self.eat(c); // body-introducing '='
            self.ws(c);
            if self.at_newline() {
                self.eat(c);
                let block = self.parse_region(header_indent);
                c.push(Child::Node(block));
            } else if self.peek_kind().is_some() {
                // Inline body on the same line.
                let mut b = Vec::new();
                self.collect_line(&mut b);
                self.ws(&mut b);
                if self.at_newline() {
                    self.eat(&mut b);
                }
                let block = self.make_node(node::BLOCK, b);
                c.push(Child::Node(block));
            }
        } else {
            // No `=`: a forward declaration / proc type. Consume the rest of the
            // line so nothing is dropped.
            self.ws(c);
            if self.at_newline() {
                self.eat(c);
            }
        }
    }

    /// A flat body region: the maximal run of logical lines indented deeper than
    /// `parent_indent`, collected into a `Block` as tokens and balanced groups.
    /// Iterative over lines (no per-indent recursion), so indentation depth cannot
    /// overflow; bracket nesting inside lines is the depth-guarded recursion.
    fn parse_region(&mut self, parent_indent: i64) -> Node {
        let mut c = Vec::new();
        loop {
            self.skip_blank_lines(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            if self.line_indent() <= parent_indent {
                break;
            }
            let before = self.i;
            self.collect_line(&mut c);
            self.ws(&mut c);
            if self.at_newline() {
                self.eat(&mut c);
            }
            if self.i == before {
                self.eat(&mut c); // progress guard
            }
        }
        self.make_node(node::BLOCK, c)
    }

    // --- shared helpers -----------------------------------------------------

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.eat(&mut c); // the identifier (cursor is at it after caller ws)
        self.make_node(node::NAME, c)
    }

    /// Collect a routine header (descending into balanced groups) up to the
    /// body-introducing `=` at bracket depth 0, or the logical line end. The `=`
    /// itself stays with the parent for [`NimParser::parse_body`].
    fn collect_until_eq(&mut self) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            match self.peek_kind() {
                None => break,
                Some(k) if k == tk::NEWLINE => break,
                _ if self.at("=") => break,
                _ => {
                    if self.at_open() {
                        let g = self.parse_delimited();
                        c.push(Child::Node(g));
                    } else {
                        self.eat(&mut c);
                    }
                }
            }
        }
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(node::HEADER, c))
        }
    }

    /// Collect the rest of the logical line (descending into groups) as a `Header`.
    /// Used for type/var definition right-hand sides.
    fn collect_line_header(&mut self) -> Option<Node> {
        let mut c = Vec::new();
        self.collect_line(&mut c);
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(node::HEADER, c))
        }
    }

    /// Collect tokens (descending into balanced groups) up to the logical line end
    /// — a `newline` at bracket depth 0. Newlines inside groups are content
    /// (implicit continuation) and are not line ends here.
    fn collect_line(&mut self, out: &mut Vec<Child>) {
        loop {
            self.ws(out);
            match self.peek_kind() {
                None => break,
                Some(k) if k == tk::NEWLINE => break,
                _ => {
                    if self.at_open() {
                        let g = self.parse_delimited();
                        out.push(Child::Node(g));
                    } else {
                        self.eat(out);
                    }
                }
            }
        }
    }

    /// Parse a balanced delimiter group `(…)`, `[…]`, or `{…}`. Newlines inside are
    /// ordinary content (Nim's implicit line joining inside brackets).
    fn parse_delimited(&mut self) -> Node {
        let mut g = Vec::new();
        self.ws(&mut g);
        let (close, label) = if self.at("(") {
            (")", node::PAREN)
        } else if self.at("[") {
            ("]", node::BRACKET)
        } else if self.at("{") {
            ("}", node::BRACE)
        } else {
            return self.make_node(node::ERROR_STMT, g);
        };
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
                    let inner = self.parse_delimited();
                    self.depth -= 1;
                    g.push(Child::Node(inner));
                } else {
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

    /// Iteratively consume a balanced delimiter run (opener already eaten) as flat
    /// leaves. Used at the depth cap so deep bracket nesting needs no recursion.
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
            code: "nim.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; region flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }
}

enum DefKind {
    Type,
    Var,
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
## a module
import os, strutils
from sequtils import map

const Answer = 42

type
  Point = object
    x, y: float
  Color = enum
    red, green, blue
  Animal = ref object of RootObj
    name: string

proc dist(a, b: Point): float =
  result = sqrt((a.x - b.x) * (a.x - b.x))

func `+`(a, b: Point): Point =
  Point(x: a.x + b.x, y: a.y + b.y)

method speak(self: Animal): string {.base.} =
  \"...\"

for i in 0 ..< 10:
  echo i
";
        let tree = parse("mod.nim", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "import os\ntype T = object\nproc f() =\n  discard\nconst K = 1\n";
        let tree = parse("t.nim", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::IMPORT), "import: {kinds:?}");
        assert!(kinds.contains(&node::TYPE_SECTION), "type: {kinds:?}");
        assert!(kinds.contains(&node::ROUTINE), "proc: {kinds:?}");
        assert!(kinds.contains(&node::VAR_SECTION), "const: {kinds:?}");
    }

    #[test]
    fn type_block_holds_multiple_defs() {
        let src = "type\n  A = object\n  B = enum\n    x, y\n";
        let tree = parse("t.nim", src);
        let sect = tree
            .root
            .children_of(node::TYPE_SECTION)
            .next()
            .expect("a type section");
        let block = sect.child(node::BLOCK).expect("a def block");
        let defs: Vec<&str> = block
            .children_of(node::TYPE_DEF)
            .filter_map(|d| d.child(node::NAME))
            .filter_map(|n| n.tokens().next())
            .map(|t| t.span.text(src))
            .collect();
        assert_eq!(defs, vec!["A", "B"]);
    }

    #[test]
    fn routine_body_is_a_block() {
        let src = "proc run() =\n  helper()\n  other()\n";
        let tree = parse("t.nim", src);
        let r = tree
            .root
            .children_of(node::ROUTINE)
            .next()
            .expect("a routine");
        assert!(r.child(node::BLOCK).is_some(), "routine has a body block");
        assert!(tree.is_lossless());
    }

    #[test]
    fn inline_routine_body() {
        let src = "proc one(): int = 1\n";
        let tree = parse("t.nim", src);
        let r = tree
            .root
            .children_of(node::ROUTINE)
            .next()
            .expect("a routine");
        assert!(r.child(node::BLOCK).is_some(), "inline body is a Block");
        assert!(tree.is_lossless());
    }

    #[test]
    fn dedent_keeps_siblings_top_level() {
        let src = "proc f() =\n  x = 1\n\nproc g() =\n  y = 2\n";
        let tree = parse("t.nim", src);
        let top: Vec<&str> = tree
            .root
            .children_of(node::ROUTINE)
            .filter_map(|r| r.child(node::NAME))
            .filter_map(|n| n.tokens().next())
            .map(|t| t.span.text(src))
            .collect();
        assert_eq!(top, vec!["f", "g"]);
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let deep_brackets = format!("x = {}{}\n", "(".repeat(10_000), ")".repeat(10_000));
        let mut deep_indent = String::new();
        for d in 0..2_000 {
            deep_indent.push_str(&"  ".repeat(d));
            deep_indent.push_str("if true:\n");
        }
        for src in [deep_brackets, deep_indent] {
            let tree = parse("deep.nim", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
        }
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "x = (1, 2\n",            // unterminated paren
            "echo \"☃ €\"  ## doc\n", // multi-byte string/comment
            "",                       // empty file
            "\n\n   \n## trailing\n", // only blanks and comments
            "proc f(",                // truncated header
        ] {
            let tree = parse("edge.nim", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
