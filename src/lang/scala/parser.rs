//! Scala parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust and Python parsers: definition *headers* are parsed
//! precisely — we always know a `def`'s name and signature, a `class`/`trait`/
//! `object`/`enum`'s name and `extends`/`with` clause, an `import` path — while
//! expression regions and bodies are captured as balanced **token-tree groups**
//! (`Paren`/`Bracket`/`Brace`) plus flat tokens, which is perfectly lossless.
//! Graph facts (calls, parents, type uses) are later extracted from these real
//! tokens in the lowering pass, never invented.
//!
//! Scala uses brace-delimited blocks for class/object/trait/enum/def bodies; this
//! parser parses those bodies as nested statement blocks so members (including
//! nested definitions) are discovered. Statement boundaries follow a pragmatic
//! reading of Scala's newline inference: a newline at bracket depth zero ends a
//! statement unless the previous token (or the next token) is an operator, an
//! open delimiter, a selector dot, or `=`/`,` — the common cases that continue a
//! logical line. Whatever the inference does, every token still lands in the
//! tree, so the result always round-trips byte-for-byte.
//!
//! Anything unrecognized lands in the tree as its exact tokens (an `ErrorStmt`
//! node or a flat token run). Recursion is depth-guarded at [`MAX_DEPTH`] against
//! hostile nesting — both bracket nesting and brace-block nesting — because a
//! `catch_unwind` cannot catch a stack overflow.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::scala::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const PACKAGE: &str = "Package";
    pub const IMPORT: &str = "Import";
    pub const CLASS: &str = "Class";
    pub const TRAIT: &str = "Trait";
    pub const OBJECT: &str = "Object";
    pub const ENUM: &str = "Enum";
    pub const DEF: &str = "Def";
    pub const VAL: &str = "Val";
    pub const TYPE_DEF: &str = "TypeDef";
    pub const GIVEN: &str = "Given";
    pub const EXTENSION: &str = "Extension";
    pub const EXPR_STMT: &str = "ExprStmt";
    pub const ERROR_STMT: &str = "ErrorStmt";
    pub const ANNOTATION: &str = "Annotation";

    pub const NAME: &str = "Name";
    pub const HEADER: &str = "Header";
    pub const BLOCK: &str = "Block";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Soft/contextual modifiers that may precede a definition keyword (in addition
/// to the hard keyword modifiers `private`/`protected`/`final`/`sealed`/
/// `abstract`/`implicit`/`lazy`/`override`). `case` is handled separately because
/// it only acts as a modifier before `class`/`object`.
const SOFT_MODIFIERS: &[&str] = &["open", "inline", "opaque", "transparent", "infix", "erased"];

const HARD_MODIFIERS: &[&str] = &[
    "private",
    "protected",
    "final",
    "sealed",
    "abstract",
    "implicit",
    "lazy",
    "override",
];

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat run. Protects against stack overflow on pathological or
/// hostile inputs (deeply nested brackets *or* brace blocks) — mirrors the Rust
/// parser's guard exactly, since a `catch_unwind` cannot catch a stack overflow.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = ScalaParser {
        src: source,
        toks,
        i: 0,
        diags: Vec::new(),
        depth: 0,
    };
    let root = p.parse_source();
    ParseTree {
        source_id: SourceId::from_path(path),
        path: path.to_string(),
        source: source.to_string(),
        root,
        diagnostics: p.diags,
    }
}

struct ScalaParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> ScalaParser<'s> {
    // --- cursor primitives --------------------------------------------------

    /// Append the current token (trivia or not) to `out` and advance.
    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading **trivia** tokens (whitespace, comments) into
    /// `out`. Newlines live inside whitespace trivia; statement boundaries are
    /// derived by inspecting that trivia via [`ScalaParser::newline_ahead`].
    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
        }
    }

    /// Kind of the n-th significant (non-trivia) token from the cursor.
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

    fn at_open(&self) -> bool {
        self.at("(") || self.at("[") || self.at("{")
    }

    /// True when only trivia separates the cursor from the previously consumed
    /// token *and* that trivia contains a line break — Scala's newline candidate.
    fn newline_ahead(&self) -> bool {
        let mut j = self.i;
        while j < self.toks.len() && self.toks[j].trivia {
            if self.toks[j].kind == tk::WHITESPACE
                && self.toks[j].span.text(self.src).contains('\n')
            {
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

    fn parse_source(&mut self) -> Node {
        let mut c = Vec::new();
        self.parse_stmts(&mut c, false);
        // Any trailing trivia after the last statement.
        self.ws(&mut c);
        self.make_node(node::SOURCE_FILE, c)
    }

    /// Parse a run of statements. When `in_braces`, stops (without consuming) at
    /// the closing `}` so the caller (`parse_brace_block`) can eat it.
    fn parse_stmts(&mut self, into: &mut Vec<Child>, in_braces: bool) {
        loop {
            self.skip_separators(into);
            match self.peek_kind() {
                None => break,
                _ if in_braces && self.at("}") => break,
                _ => {}
            }
            let before = self.i;
            let stmt = self.parse_statement();
            into.push(Child::Node(stmt));
            if self.i == before {
                // Safety net: guarantee forward progress so we can never loop.
                if self.i < self.toks.len() {
                    let mut c = Vec::new();
                    self.eat(&mut c);
                    into.push(Child::Node(self.make_node(node::ERROR_STMT, c)));
                } else {
                    break;
                }
            }
        }
    }

    /// Consume inter-statement trivia and any stray `;` separators into `out`,
    /// leaving the cursor at the next significant non-`;` token (or end).
    fn skip_separators(&mut self, out: &mut Vec<Child>) {
        loop {
            self.ws(out);
            if self.at(";") {
                self.eat(out);
            } else {
                break;
            }
        }
    }

    // --- statements ---------------------------------------------------------

    fn parse_statement(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);

        // Annotations: `@Ann` / `@Ann(args)`, possibly several, possibly across
        // lines, exactly as the Rust parser attaches `#[attr]` to its item.
        while self.at("@") {
            let a = self.parse_annotation();
            c.push(Child::Node(a));
            self.ws(&mut c);
        }

        // Modifiers (hard keyword + soft contextual). `case` is a modifier only
        // when it precedes `class`/`object`.
        self.collect_modifiers(&mut c);

        // Capture the dispatch keyword as an owned value so the arms can borrow
        // `self` mutably (the `self.peek_text()` borrow would otherwise live for
        // the whole `match`).
        let kw = self.peek_text().map(|s| s.to_string());
        match kw.as_deref() {
            Some("package") => self.finish_package(c),
            Some("import") | Some("export") => self.finish_import(c),
            Some("class") => self.finish_type_like(c, node::CLASS),
            Some("trait") => self.finish_type_like(c, node::TRAIT),
            Some("object") => self.finish_type_like(c, node::OBJECT),
            Some("enum") => self.finish_type_like(c, node::ENUM),
            Some("def") => self.finish_def(c),
            Some("val") | Some("var") => self.finish_val(c),
            Some("type") => self.finish_typedef(c),
            Some("given") => self.finish_given(c),
            Some("extension") => self.finish_extension(c),
            None => self.make_node(node::ERROR_STMT, c),
            _ => self.finish_expr_stmt(c),
        }
    }

    /// `@Ann` or `@Ann(args)` (the name path may be dotted; an optional argument
    /// list follows). Stops before the next modifier / definition keyword.
    fn parse_annotation(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // @
                          // The annotation type path: idents and dots.
        loop {
            self.ws(&mut c);
            match self.peek_kind() {
                Some(tk_kind) if tk_kind == tk::IDENT || tk_kind == tk::BACKTICK_IDENT => {
                    self.eat(&mut c);
                }
                _ if self.at(".") => self.eat(&mut c),
                _ => break,
            }
        }
        // Optional type args and argument list(s).
        self.ws(&mut c);
        while self.at("[") || self.at("(") {
            let g = self.parse_delimited();
            c.push(Child::Node(g));
            self.ws(&mut c);
        }
        self.make_node(node::ANNOTATION, c)
    }

    /// Collect leading modifier tokens into `c`.
    fn collect_modifiers(&mut self, c: &mut Vec<Child>) {
        loop {
            self.ws(c);
            let word = self.peek_text().map(|s| s.to_string());
            match word.as_deref() {
                Some(t) if HARD_MODIFIERS.contains(&t) || SOFT_MODIFIERS.contains(&t) => {
                    self.eat(c);
                    // `private`/`protected` may carry a `[scope]` qualifier.
                    self.ws(c);
                    if self.at("[") {
                        let g = self.parse_delimited();
                        c.push(Child::Node(g));
                    }
                }
                Some("case") if matches!(self.peek_n_text(1), Some("class") | Some("object")) => {
                    self.eat(c);
                }
                _ => break,
            }
        }
    }

    /// `package a.b.c` (no body), `package a.b { … }`, or `package object N { … }`.
    fn finish_package(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // package
        self.ws(&mut c);
        if self.at("object") {
            // `package object` is an object definition; reuse the object path.
            return self.finish_type_like(c, node::OBJECT);
        }
        if let Some(h) = self.collect_header() {
            c.push(Child::Node(h));
        }
        if self.at("{") {
            let block = self.parse_brace_block();
            c.push(Child::Node(block));
        }
        self.make_node(node::PACKAGE, c)
    }

    /// `import a.b.{x, y => z, _}` / `import a.b._` / `export …`.
    fn finish_import(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // import / export
        self.collect_value(&mut c);
        self.make_node(node::IMPORT, c)
    }

    /// `class`/`trait`/`object`/`enum` NAME[tparams](params) extends … with … { … }.
    fn finish_type_like(&mut self, mut c: Vec<Child>, kind: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // the keyword
        self.ws(&mut c);
        if self.at_name() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(h) = self.collect_header() {
            c.push(Child::Node(h));
        }
        if self.at("{") {
            let block = self.parse_brace_block();
            c.push(Child::Node(block));
        }
        self.make_node(kind, c)
    }

    /// `def NAME[tparams](params): RetType = body` (body may be a brace block, an
    /// `= expr`, or absent for an abstract method).
    fn finish_def(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // def
        self.ws(&mut c);
        if self.at_name() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(h) = self.collect_header() {
            c.push(Child::Node(h));
        }
        self.parse_value_body(&mut c);
        self.make_node(node::DEF, c)
    }

    /// `val`/`var` NAME: T = expr (pattern bindings are captured verbatim too).
    fn finish_val(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // val / var
        self.ws(&mut c);
        if self.at_name() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(h) = self.collect_header() {
            c.push(Child::Node(h));
        }
        self.parse_value_body(&mut c);
        self.make_node(node::VAL, c)
    }

    /// `type NAME[tparams] = RHS` / `type NAME >: Lo <: Hi` (no brace body).
    fn finish_typedef(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // type
        self.ws(&mut c);
        if self.at_name() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        self.collect_value(&mut c);
        self.make_node(node::TYPE_DEF, c)
    }

    /// `given name: Type = …` / `given Type = …` / `given [T] … : Type with { … }`.
    fn finish_given(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // given
        if let Some(h) = self.collect_header() {
            c.push(Child::Node(h));
        }
        self.parse_value_body(&mut c);
        self.make_node(node::GIVEN, c)
    }

    /// `extension (x: T) { def … }` / `extension (x: T) def …`.
    fn finish_extension(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // extension
        if let Some(h) = self.collect_header() {
            c.push(Child::Node(h));
        }
        if self.at("{") {
            let block = self.parse_brace_block();
            c.push(Child::Node(block));
        }
        self.make_node(node::EXTENSION, c)
    }

    /// A plain expression statement (anything not opening with a definition
    /// keyword). Captured as a value run so call sites inside still round-trip
    /// and are visible to the lowering's call scan.
    fn finish_expr_stmt(&mut self, mut c: Vec<Child>) -> Node {
        self.collect_value(&mut c);
        self.make_node(node::EXPR_STMT, c)
    }

    // --- bodies & headers ---------------------------------------------------

    /// After a `def`/`val`/`var`/`given` signature: an optional `= …` value or a
    /// brace block body, wrapped uniformly as a `Block` so the lowering can scan
    /// it for calls regardless of form. Abstract members (no `=`, no `{`) get no
    /// block.
    fn parse_value_body(&mut self, c: &mut Vec<Child>) {
        self.ws(c);
        if self.at("{") {
            let block = self.parse_brace_block();
            c.push(Child::Node(block));
            return;
        }
        if self.at("=") {
            let mut b = Vec::new();
            self.eat(&mut b); // =
            self.ws(&mut b);
            if self.at("{") {
                // `= { … }`: unwrap the brace block as the body.
                let block = self.parse_brace_block();
                let block = self.flatten_block(block, &mut b);
                c.push(Child::Node(block));
            } else {
                self.collect_value(&mut b);
                c.push(Child::Node(self.make_node(node::BLOCK, b)));
            }
        }
    }

    /// Re-home the leading `=` (and trivia) collected in `lead` onto the front of
    /// a brace block so the produced `Block` still spans the whole `= { … }`.
    fn flatten_block(&self, block: Node, lead: &mut Vec<Child>) -> Node {
        let mut children = std::mem::take(lead);
        children.extend(block.children);
        self.make_node(node::BLOCK, children)
    }

    /// Parse a brace-delimited statement block `{ … }` as nested statements.
    /// Depth-guarded — beyond [`MAX_DEPTH`] the body is consumed as a flat token
    /// run rather than recursing, so deep nesting cannot overflow.
    fn parse_brace_block(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        if !self.at("{") {
            return self.make_node(node::BLOCK, c);
        }
        if self.depth >= MAX_DEPTH {
            self.eat(&mut c); // {
            self.consume_balanced_flat(&mut c);
            self.note_depth_limit();
            return self.make_node(node::BLOCK, c);
        }
        self.depth += 1;
        self.eat(&mut c); // {
        self.parse_stmts(&mut c, true);
        self.ws(&mut c);
        if self.at("}") {
            self.eat(&mut c);
        }
        let block = self.make_node(node::BLOCK, c);
        self.depth -= 1;
        block
    }

    /// Collect a definition header: tokens (descending into balanced `(…)`/`[…]`
    /// groups) up to the body brace `{`, a statement terminator, or end of the
    /// logical line. Used for type/def/val signatures, `extends`/`with` clauses,
    /// and package paths. The body `{` and the value `=` stay with the parent.
    fn collect_header(&mut self) -> Option<Node> {
        let c = self.collect_run(true, true);
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(node::HEADER, c))
        }
    }

    /// Collect a value/expression run up to a statement terminator. Does not stop
    /// at `{` (a brace here is part of the expression, e.g. `foo { … }`).
    fn collect_value(&mut self, out: &mut Vec<Child>) {
        let run = self.collect_run(false, false);
        out.extend(run);
    }

    /// The shared run collector. `stop_at_brace` breaks before a depth-0 `{`
    /// (header form); `stop_at_eq` breaks before a depth-0 `=` (so a signature
    /// ends at the value). Both forms descend into `(…)`/`[…]` (and `{…}` when
    /// not stopping at it) and honor newline-based statement termination with a
    /// continuation rule.
    fn collect_run(&mut self, stop_at_brace: bool, stop_at_eq: bool) -> Vec<Child> {
        let mut out = Vec::new();
        let mut last: Option<(String, bool)> = None; // (text, is_op)
        loop {
            // Newline statement-termination check (before consuming the trivia
            // that carries the newline, so it is left for the separator pass).
            if self.newline_ahead() && !self.run_continues(&last) {
                break;
            }
            self.ws(&mut out);
            let kind = self.peek_kind();
            let text = self.peek_text().map(|s| s.to_string());
            match text.as_deref() {
                None => break,
                Some(";") | Some("}") => break,
                Some("{") if stop_at_brace => break,
                Some("=") if stop_at_eq && kind == Some(tk::OP) => break,
                Some("(") | Some("[") | Some("{") => {
                    let g = self.parse_delimited();
                    last = Some((")".to_string(), false));
                    out.push(Child::Node(g));
                }
                Some(t) => {
                    let is_op = kind == Some(tk::OP);
                    last = Some((t.to_string(), is_op));
                    self.eat(&mut out);
                }
            }
        }
        out
    }

    /// Whether a newline at the cursor should *not* terminate the current run:
    /// the previous token is an operator / open delimiter / comma, or the next
    /// token is an operator or a selector dot — Scala's main line-continuation
    /// cases.
    fn run_continues(&self, last: &Option<(String, bool)>) -> bool {
        if let Some(next) = self.peek_text() {
            if next.starts_with('.') {
                return true;
            }
            // A clause that extends the current definition header onto a new line.
            if matches!(next, "extends" | "with" | "derives") {
                return true;
            }
        }
        if self.peek_kind() == Some(tk::OP) {
            return true;
        }
        match last {
            Some((_, true)) => true, // previous token was an operator
            Some((t, false)) => matches!(t.as_str(), "," | "(" | "["),
            None => false,
        }
    }

    /// Parse a balanced delimiter group `(…)`, `[…]`, or `{…}` as flat content
    /// (tokens + nested groups). The cursor is at (or before trivia preceding)
    /// the opener. Depth-guarded against pathological nesting.
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
            let text = self.peek_text().map(|s| s.to_string());
            match text.as_deref() {
                None => break, // unterminated; still lossless
                Some(t) if t == close => {
                    self.eat(&mut g);
                    break;
                }
                _ if self.at_open() => {
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
                }
                _ => self.eat(&mut g),
            }
        }
        self.make_node(label, g)
    }

    /// Iteratively consume a balanced delimiter run (one opener already eaten),
    /// appending every token as a flat leaf. Used at the depth cap so arbitrarily
    /// deep nesting is handled without further recursion.
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
            code: "scala.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; region flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }

    // --- helpers ------------------------------------------------------------

    fn at_name(&self) -> bool {
        matches!(self.peek_kind(), Some(k) if k == tk::IDENT || k == tk::BACKTICK_IDENT)
            // operator-named defs: `def +(o: T)`
            || self.peek_kind() == Some(tk::OP)
    }

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.eat(&mut c); // the identifier / operator (cursor is at it)
        self.make_node(node::NAME, c)
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
package com.example

import scala.collection.mutable.{Map, Set}
import java.util._

/** A point. */
case class Point(x: Double, y: Double) extends Shape with Drawable {
  val origin = Point(0.0, 0.0)

  def norm: Double = math.sqrt(x * x + y * y)

  def scaled(k: Double): Point = {
    val nx = x * k
    Point(nx, y * k)
  }
}

object Main {
  def main(args: Array[String]): Unit = {
    val p = Point(3.0, 4.0)
    println(p.norm)
  }
}

trait Shape {
  def area: Double
}
";
        let tree = parse("Point.scala", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "import a.b\nclass C { def m: Int = 1 }\nobject O\ntrait T\n";
        let tree = parse("t.scala", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::IMPORT), "import: {kinds:?}");
        assert!(kinds.contains(&node::CLASS), "class: {kinds:?}");
        assert!(kinds.contains(&node::OBJECT), "object: {kinds:?}");
        assert!(kinds.contains(&node::TRAIT), "trait: {kinds:?}");
    }

    #[test]
    fn methods_nest_inside_class_blocks() {
        let src = "class C {\n  def a: Int = 1\n  def b: Int = 2\n}\n";
        let tree = parse("t.scala", src);
        let class = tree
            .root
            .children_of(node::CLASS)
            .next()
            .expect("a class node");
        let block = class.child(node::BLOCK).expect("class has a block");
        let methods: Vec<&str> = block
            .children_of(node::DEF)
            .filter_map(|f| f.child(node::NAME))
            .filter_map(|n| n.tokens().next())
            .map(|t| t.span.text(src))
            .collect();
        assert_eq!(methods, vec!["a", "b"]);
    }

    #[test]
    fn top_level_defs_are_siblings() {
        let src = "def f: Int = 1\ndef g: Int = 2\n";
        let tree = parse("t.scala", src);
        let names: Vec<&str> = tree
            .root
            .children_of(node::DEF)
            .filter_map(|f| f.child(node::NAME))
            .filter_map(|n| n.tokens().next())
            .map(|t| t.span.text(src))
            .collect();
        assert_eq!(names, vec!["f", "g"], "both defs are top-level");
    }

    #[test]
    fn operator_named_def() {
        let src = "class V { def +(o: V): V = o }\n";
        let tree = parse("v.scala", src);
        let class = tree.root.children_of(node::CLASS).next().unwrap();
        let block = class.child(node::BLOCK).unwrap();
        let def = block.children_of(node::DEF).next().expect("an op def");
        let name = def.child(node::NAME).unwrap().tokens().next().unwrap();
        assert_eq!(name.span.text(src), "+");
        assert!(tree.is_lossless());
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let deep_parens = format!("val x = {}{}\n", "(".repeat(10_000), ")".repeat(10_000));
        let mut deep_braces = String::from("object O ");
        deep_braces.push_str(&"{ def f = ".repeat(2_000));
        deep_braces.push('1');
        deep_braces.push_str(&" }".repeat(2_000));
        deep_braces.push('\n');
        for src in [deep_parens, deep_braces] {
            let tree = parse("deep.scala", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics
                    .iter()
                    .any(|d| d.code == "scala.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "val x = (1, 2\n",                // unterminated paren
            "val λ = \"☃\" // unicode\n",     // multi-byte ident/string
            "",                               // empty file
            "\n\n   \n// trailing\n",         // only blanks and comments
            "val s = s\"$x and ${y + 1}\"\n", // interpolation
        ] {
            let tree = parse("edge.scala", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
