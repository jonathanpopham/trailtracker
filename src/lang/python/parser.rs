//! Python parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust parser ([`crate::lang::rust::parser`]): item
//! *headers* are parsed precisely — we always know a `def`'s name, a `class`'s
//! bases, an `import` path, a decorator — while expression regions and bodies are
//! captured as balanced **token-tree groups** (`Paren`/`Bracket`/`Brace`) plus
//! flat tokens, which is perfectly lossless. Graph facts (calls, type refs) are
//! later extracted from these real tokens in the lowering pass, never invented.
//!
//! The one structural difference from Rust is that Python's block boundaries are
//! **indentation**, not braces. The lexer already emits structurally-significant
//! `newline` tokens and leading-indentation `whitespace` trivia; this parser
//! derives INDENT/DEDENT from them: a compound statement's suite is the maximal
//! run of following logical lines whose indentation exceeds the header's. Blank
//! and comment-only lines are retained as trivia and never affect indentation.
//!
//! Anything unrecognized still lands in the tree as its exact tokens (an
//! `ErrorStmt` node or a flat token run), so the result always round-trips
//! byte-for-byte. The recursion is depth-guarded at [`MAX_DEPTH`] against hostile
//! nesting — both bracket nesting and indentation nesting — because a
//! `catch_unwind` cannot catch a stack overflow.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::python::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const MODULE: &str = "Module";
    pub const FUNCTION: &str = "Function";
    pub const CLASS: &str = "Class";
    pub const IMPORT: &str = "Import";
    pub const FROM_IMPORT: &str = "FromImport";
    pub const DECORATOR: &str = "Decorator";
    pub const COMPOUND: &str = "Compound";
    pub const SIMPLE_STMT: &str = "SimpleStmt";
    pub const ERROR_STMT: &str = "ErrorStmt";

    pub const NAME: &str = "Name";
    pub const HEADER: &str = "Header";
    pub const BLOCK: &str = "Block";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat run. Protects against stack overflow on pathological or
/// hostile inputs (deeply nested brackets *or* indentation) — mirrors the Rust
/// parser's guard exactly, since a `catch_unwind` cannot catch a stack overflow.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = PythonParser {
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

struct PythonParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
    /// Indentation (leading-whitespace byte width) of the statement currently
    /// being parsed; read by [`PythonParser::parse_suite`] to bound its block.
    stmt_indent: i64,
}

impl<'s> PythonParser<'s> {
    // --- cursor primitives --------------------------------------------------

    /// Append the current token (trivia or not) to `out` and advance.
    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading **trivia** tokens (whitespace, comments, line
    /// continuations) into `out`. A `newline` is *not* trivia in Python, so it is
    /// left in place — block structure depends on it.
    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
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

    /// Leading indentation of the line at the cursor, in bytes. Assumes the
    /// cursor sits at the start of a code line (callers reach that state via
    /// [`PythonParser::skip_blank_lines`]).
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
        // Parent indent of -1: every top-level line (indent >= 0) is a member.
        self.parse_statements(-1, &mut c);
        self.make_node(node::MODULE, c)
    }

    /// Parse a run of statements that are all more indented than `parent_indent`,
    /// appending each (and the inter-statement blank/comment trivia) to `into`.
    /// Stops at the first code line that dedents to `parent_indent` or shallower,
    /// or at end of input.
    fn parse_statements(&mut self, parent_indent: i64, into: &mut Vec<Child>) {
        loop {
            self.skip_blank_lines(into);
            if self.peek_kind().is_none() {
                break;
            }
            if self.line_indent() <= parent_indent {
                break;
            }
            let stmt = self.parse_statement();
            into.push(Child::Node(stmt));
        }
    }

    /// Consume (into `out`) every line from the cursor that carries no code — pure
    /// blank lines and comment-only lines — leaving the cursor at the leading
    /// whitespace of the next code line (so its indentation can be measured) or at
    /// end of input. Trailing trivia with no terminating newline is consumed too.
    fn skip_blank_lines(&mut self, out: &mut Vec<Child>) {
        loop {
            // Tentatively scan past leading trivia without committing the cursor.
            let mut j = self.i;
            while j < self.toks.len() && self.toks[j].trivia {
                j += 1;
            }
            match self.toks.get(j) {
                None => {
                    // Only trailing trivia remains (e.g. a final blank line with no
                    // newline); keep it so the tree stays lossless.
                    while self.i < self.toks.len() {
                        self.eat(out);
                    }
                    return;
                }
                Some(t) if t.kind == tk::NEWLINE => {
                    // Blank or comment-only line: commit through the newline.
                    while self.i <= j {
                        self.eat(out);
                    }
                }
                Some(_) => return, // a code line; leave its indentation in place
            }
        }
    }

    // --- statements ---------------------------------------------------------

    fn parse_statement(&mut self) -> Node {
        // The line's indentation is fixed before any trivia/decorators are eaten;
        // `parse_suite` reads it to bound the statement's own block.
        self.stmt_indent = self.line_indent();
        let mut c = Vec::new();
        self.ws(&mut c); // leading indentation

        // Decorators (`@expr` lines) attach to the def/class they precede, exactly
        // as the Rust parser attaches `#[attr]` to its item.
        while self.at("@") {
            let d = self.parse_decorator();
            c.push(Child::Node(d));
            self.ws(&mut c); // next line's indentation before the next @ / keyword
        }

        if self.at_function() {
            self.finish_function(c)
        } else if self.at("class") {
            self.finish_class(c)
        } else if self.at("import") {
            self.finish_import(c)
        } else if self.at("from") {
            self.finish_from_import(c)
        } else if self.at_compound() {
            self.finish_compound(c)
        } else if self.peek_kind().is_none() || self.at_newline() {
            // Defensive: nothing classifiable on the line. Consume one token to
            // guarantee progress; the bytes stay in the tree.
            self.eat(&mut c);
            self.make_node(node::ERROR_STMT, c)
        } else {
            self.finish_simple(c)
        }
    }

    /// `def NAME(params) -> ret:` (optionally `async`).
    fn finish_function(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        if self.at("async") {
            self.eat(&mut c); // async
            self.ws(&mut c);
        }
        self.eat(&mut c); // def
        self.ws(&mut c);
        if self.peek_kind() == Some(tk::NAME) {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(h) = self.collect_header() {
            c.push(Child::Node(h));
        }
        self.parse_suite(&mut c);
        self.make_node(node::FUNCTION, c)
    }

    /// `class NAME(bases):`.
    fn finish_class(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // class
        self.ws(&mut c);
        if self.peek_kind() == Some(tk::NAME) {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(h) = self.collect_header() {
            c.push(Child::Node(h));
        }
        self.parse_suite(&mut c);
        self.make_node(node::CLASS, c)
    }

    /// `if/elif/else/while/for/with/try/except/finally` (and `async for`/`async
    /// with`). The condition (if any) is captured as a `Header`; the suite follows.
    fn finish_compound(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        if self.at("async") {
            self.eat(&mut c); // async
            self.ws(&mut c);
        }
        self.eat(&mut c); // the compound keyword
        if let Some(h) = self.collect_header() {
            c.push(Child::Node(h));
        }
        self.parse_suite(&mut c);
        self.make_node(node::COMPOUND, c)
    }

    fn finish_import(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // import
        self.collect_line(&mut c);
        self.ws(&mut c);
        if self.at_newline() {
            self.eat(&mut c);
        }
        self.make_node(node::IMPORT, c)
    }

    fn finish_from_import(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // from
        self.collect_line(&mut c); // `<module> import <names>`
        self.ws(&mut c);
        if self.at_newline() {
            self.eat(&mut c);
        }
        self.make_node(node::FROM_IMPORT, c)
    }

    /// A simple (non-compound) statement: everything up to the logical line end.
    fn finish_simple(&mut self, mut c: Vec<Child>) -> Node {
        self.collect_line(&mut c);
        self.ws(&mut c);
        if self.at_newline() {
            self.eat(&mut c);
        }
        self.make_node(node::SIMPLE_STMT, c)
    }

    fn parse_decorator(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // @
        self.collect_line(&mut c);
        self.ws(&mut c);
        if self.at_newline() {
            self.eat(&mut c);
        }
        self.make_node(node::DECORATOR, c)
    }

    // --- suites (indentation-derived blocks) --------------------------------

    /// After a compound header, consume the `:` and the suite. Two forms: a block
    /// suite (a `newline` then an indented run of statements) or an inline suite
    /// (`if x: return` — statements on the same logical line).
    fn parse_suite(&mut self, c: &mut Vec<Child>) {
        let header_indent = self.stmt_indent;
        self.ws(c);
        if self.at(":") {
            self.eat(c); // :
        } else if self.peek_kind().is_some() && !self.at_newline() {
            // Malformed header (no colon). Record it, then recover by consuming the
            // rest of the line so nothing is dropped.
            self.diags.push(Diagnostic {
                code: "python.missing_colon",
                message: "compound statement header missing ':'".to_string(),
                span: ByteSpan::empty_at(self.cur_offset()),
            });
        }
        // Trailing trivia (and an end-of-line comment) on the header line.
        self.ws(c);
        if self.at_newline() {
            self.eat(c); // newline → block form
            let block = self.parse_block(header_indent);
            c.push(Child::Node(block));
        } else if self.peek_kind().is_some() {
            let block = self.parse_inline_suite();
            c.push(Child::Node(block));
        }
    }

    /// Block-form suite: the maximal run of lines indented deeper than
    /// `header_indent`. Depth-guarded — beyond [`MAX_DEPTH`] the body is consumed
    /// as a flat token run rather than recursing, so deep nesting cannot overflow.
    fn parse_block(&mut self, header_indent: i64) -> Node {
        if self.depth >= MAX_DEPTH {
            let mut c = Vec::new();
            self.consume_block_flat(header_indent, &mut c);
            self.note_depth_limit();
            return self.make_node(node::BLOCK, c);
        }
        self.depth += 1;
        let mut c = Vec::new();
        self.parse_statements(header_indent, &mut c);
        let block = self.make_node(node::BLOCK, c);
        self.depth -= 1;
        block
    }

    /// Inline suite: the simple statement(s) after `:` on the same line.
    fn parse_inline_suite(&mut self) -> Node {
        let mut c = Vec::new();
        let stmt = self.finish_simple(Vec::new());
        c.push(Child::Node(stmt));
        self.make_node(node::BLOCK, c)
    }

    /// At the depth cap, swallow an indented block as a flat token run (no further
    /// recursion). Lossless; the structure is reported as truncated via a
    /// `depth_limit` diagnostic.
    fn consume_block_flat(&mut self, parent_indent: i64, out: &mut Vec<Child>) {
        loop {
            self.skip_blank_lines(out);
            if self.peek_kind().is_none() {
                break;
            }
            if self.line_indent() <= parent_indent {
                break;
            }
            self.consume_logical_line_flat(out);
        }
    }

    /// Consume one logical line as flat leaves, honoring bracket nesting so an
    /// implicit line continuation inside `()`/`[]`/`{}` does not end the line.
    fn consume_logical_line_flat(&mut self, out: &mut Vec<Child>) {
        let mut depth: i32 = 0;
        while self.i < self.toks.len() {
            let t = &self.toks[self.i];
            let is_nl = t.kind == tk::NEWLINE;
            if !t.trivia {
                match t.span.text(self.src) {
                    "(" | "[" | "{" => depth += 1,
                    ")" | "]" | "}" => depth -= 1,
                    _ => {}
                }
            }
            self.eat(out);
            if is_nl && depth <= 0 {
                break;
            }
        }
    }

    // --- shared helpers -----------------------------------------------------

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.eat(&mut c); // the identifier (cursor is at it after caller ws)
        self.make_node(node::NAME, c)
    }

    /// Collect a compound-statement header: tokens (descending into balanced
    /// groups) up to the `:` that closes the header at bracket depth 0, or the
    /// logical line end. The `:` itself stays with the parent for `parse_suite`.
    fn collect_header(&mut self) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            match self.peek_kind() {
                None => break,
                Some(k) if k == tk::NEWLINE => break,
                _ if self.at(":") => break,
                _ => {
                    if self.at_open() {
                        let g = self.parse_delimited(None);
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

    /// Collect tokens (descending into balanced groups) up to the logical line
    /// end — a `newline` at bracket depth 0. Newlines inside groups are part of
    /// the group (implicit continuation) and are not line ends here.
    fn collect_line(&mut self, out: &mut Vec<Child>) {
        loop {
            self.ws(out);
            match self.peek_kind() {
                None => break,
                Some(k) if k == tk::NEWLINE => break,
                _ => {
                    if self.at_open() {
                        let g = self.parse_delimited(None);
                        out.push(Child::Node(g));
                    } else {
                        self.eat(out);
                    }
                }
            }
        }
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`. The cursor is
    /// at (or before trivia preceding) the opener. Newlines inside the group are
    /// eaten as ordinary content, which is exactly Python's implicit line joining.
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
            return self.make_node(label_override.unwrap_or(node::ERROR_STMT), g);
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
            match self.peek_text() {
                None => break,
                Some("(") | Some("[") | Some("{") => balance += 1,
                Some(")") | Some("]") | Some("}") => balance -= 1,
                _ => {}
            }
            self.eat(out);
        }
    }

    /// Record (once per truncation is enough) that the depth cap flattened
    /// structure — reported, never silent.
    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "python.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; region flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }

    // --- keyword dispatch ---------------------------------------------------

    fn at_function(&self) -> bool {
        self.at("def") || (self.at("async") && self.peek_n_text(1) == Some("def"))
    }

    /// Hard compound keywords only. `match`/`case` are deliberately excluded: they
    /// are *soft* keywords (legal identifiers), so treating `match = 1` as a block
    /// header would be wrong. A `match` block instead parses as flat statements —
    /// still lossless, and any nested `def`/`class` is still discovered.
    fn at_compound(&self) -> bool {
        match self.peek_text() {
            Some(
                "if" | "elif" | "else" | "while" | "for" | "with" | "try" | "except" | "finally",
            ) => true,
            Some("async") => matches!(self.peek_n_text(1), Some("for") | Some("with")),
            _ => false,
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
# a module
import os
from collections import OrderedDict, defaultdict as dd

X = 1


@decorator
class Point:
    \"\"\"A point.\"\"\"

    def __init__(self, x, y):
        self.x = x
        self.y = y

    def norm(self) -> float:
        return sqrt(self.x * self.x + self.y * self.y)


def add(a, b):
    if a > b:
        return a
    else:
        return b
";
        let tree = parse("mod.py", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "import os\nclass C:\n    def m(self):\n        pass\n\ndef f():\n    pass\n";
        let tree = parse("t.py", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::IMPORT), "import not found: {kinds:?}");
        assert!(kinds.contains(&node::CLASS), "class not found: {kinds:?}");
        assert!(kinds.contains(&node::FUNCTION), "def not found: {kinds:?}");
    }

    #[test]
    fn methods_nest_inside_class_blocks() {
        let src = "class C:\n    def a(self):\n        pass\n    def b(self):\n        pass\n";
        let tree = parse("t.py", src);
        let class = tree
            .root
            .children_of(node::CLASS)
            .next()
            .expect("a class node");
        let block = class.child(node::BLOCK).expect("class has a block");
        let methods: Vec<&str> = block
            .children_of(node::FUNCTION)
            .filter_map(|f| f.child(node::NAME))
            .filter_map(|n| n.tokens().next())
            .map(|t| t.span.text(src))
            .collect();
        assert_eq!(methods, vec!["a", "b"]);
    }

    #[test]
    fn inline_suite_is_captured() {
        let src = "def f(): return 1\n";
        let tree = parse("t.py", src);
        let f = tree
            .root
            .children_of(node::FUNCTION)
            .next()
            .expect("a function");
        assert!(f.child(node::BLOCK).is_some(), "inline body is a Block");
        assert!(tree.is_lossless());
    }

    #[test]
    fn dedent_closes_blocks() {
        // `g` must be a top-level sibling of `f`, not nested inside it.
        let src = "def f():\n    x = 1\n\ndef g():\n    y = 2\n";
        let tree = parse("t.py", src);
        let top: Vec<&str> = tree
            .root
            .children_of(node::FUNCTION)
            .filter_map(|f| f.child(node::NAME))
            .filter_map(|n| n.tokens().next())
            .map(|t| t.span.text(src))
            .collect();
        assert_eq!(top, vec!["f", "g"], "both defs are top-level");
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        // Far deeper than MAX_DEPTH on both axes; must not stack-overflow and must
        // stay lossless.
        let deep_brackets = format!("x = {}{}\n", "(".repeat(10_000), ")".repeat(10_000));
        let mut deep_indent = String::new();
        for d in 0..2_000 {
            deep_indent.push_str(&"    ".repeat(d));
            deep_indent.push_str("if True:\n");
        }
        for src in [deep_brackets, deep_indent] {
            let tree = parse("deep.py", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics
                    .iter()
                    .any(|d| d.code == "python.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "x = (1, 2\n",           // unterminated paren
            "λ = '☃'  # unicode\n",  // multi-byte identifiers/strings
            "",                      // empty file
            "\n\n   \n# trailing\n", // only blanks and comments
        ] {
            let tree = parse("edge.py", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
