//! Ruby parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust and Python parsers: item *headers* are parsed
//! precisely — we always know a `def`'s name and receiver, a `class`'s name and
//! superclass, a `module`'s name — while bodies and expressions are captured as a
//! mix of recognized sub-statements, balanced delimiter groups (`Paren`/`Bracket`/
//! `Brace`), and flat tokens, which is perfectly lossless. Graph facts (calls,
//! requires, includes, inheritance) are later read off these real tokens in the
//! lowering pass, never invented.
//!
//! Ruby's blocks are delimited by the `end` keyword (and `do…end` / `{…}` for
//! method blocks), not by braces or indentation. A compound statement opens with
//! a keyword (`def`/`class`/`module`/`if`/`unless`/`while`/`until`/`case`/`begin`/
//! `for`) and runs until its matching `end`, with intermediate clause keywords
//! (`elsif`/`else`/`when`/`in`/`rescue`/`ensure`) handled in between. Statement
//! boundaries are `newline`/`;` tokens (the lexer emits `newline` as a
//! *non-trivia* token). Trailing modifiers (`x if y`, `x while y`) are recognized
//! as plain expression tokens — only a *value-position* `if`/`case`/… recurses
//! into an `end`-block.
//!
//! Anything unrecognized still lands in the tree as its exact tokens (an
//! `ErrorStmt` node or a flat token run), so the result always round-trips
//! byte-for-byte. The recursion is depth-guarded at [`MAX_DEPTH`] against hostile
//! nesting (both bracket and `end`-block nesting), because a `catch_unwind` cannot
//! catch a stack overflow.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::ruby::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const PROGRAM: &str = "Program";
    pub const METHOD: &str = "Method";
    pub const CLASS: &str = "Class";
    pub const MODULE: &str = "Module";
    pub const SINGLETON_CLASS: &str = "SingletonClass";
    pub const COMPOUND: &str = "Compound";
    pub const EXPR_STMT: &str = "ExprStmt";
    pub const ERROR_STMT: &str = "ErrorStmt";

    pub const NAME: &str = "Name";
    pub const SUPERCLASS: &str = "Superclass";
    pub const HEADER: &str = "Header";
    pub const BLOCK: &str = "Block";
    pub const DO_BLOCK: &str = "DoBlock";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat run. Protects against stack overflow on pathological or
/// hostile inputs — mirrors the Rust/Python parsers' guard exactly, since a
/// `catch_unwind` cannot catch a stack overflow.
const MAX_DEPTH: usize = 256;

/// Keywords that open an `end`-terminated compound statement.
const COMPOUND_KEYWORDS: &[&str] = &["if", "unless", "while", "until", "case", "begin", "for"];

/// Keywords that close or continue a compound body (a body parse stops on these,
/// leaving them for the enclosing construct to consume).
const TERMINATORS: &[&str] = &["end", "else", "elsif", "when", "in", "rescue", "ensure"];

/// Intermediate clause keywords that introduce another sub-body and carry a
/// header of their own (`elsif cond`, `when x`, `rescue E => e`).
const HEADERED_CLAUSES: &[&str] = &["elsif", "when", "in", "rescue"];

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = RubyParser {
        src: source,
        toks,
        i: 0,
        diags: Vec::new(),
        depth: 0,
        brace_body_depth: 0,
    };
    let root = p.parse_program();
    ParseTree {
        source_id: SourceId::from_path(path),
        path: path.to_string(),
        source: source.to_string(),
        root,
        diagnostics: p.diags,
    }
}

struct RubyParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
    /// Nesting level of method-call **brace blocks** (`foo { … }`) whose bodies
    /// we are currently parsing as statements. While `> 0`, [`collect_expr_line`]
    /// stops at a top-level `}` so the brace-body parser can claim it. End-block
    /// bodies (`def`/`class`/… via [`parse_body`]) reset this to 0 so a `}` inside
    /// them keeps its ordinary hash/plain-token meaning.
    brace_body_depth: u32,
}

impl<'s> RubyParser<'s> {
    // --- cursor primitives --------------------------------------------------

    /// Append the current token (trivia or not) to `out` and advance.
    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading **trivia** tokens (whitespace, comments, line
    /// continuations) into `out`. A `newline` is *not* trivia in Ruby, so it is
    /// left in place — statement structure depends on it.
    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
        }
    }

    /// Eat statement separators — trivia, `newline`, and `;` — into `out`, leaving
    /// the cursor at the next real token (or end of input).
    fn skip_seps(&mut self, out: &mut Vec<Child>) {
        while let Some(t) = self.toks.get(self.i) {
            if t.trivia || t.kind == tk::NEWLINE || t.span.text(self.src) == ";" {
                self.eat(out);
            } else {
                break;
            }
        }
    }

    /// Kind of the n-th significant (non-trivia) token from the cursor; `newline`
    /// counts as significant.
    fn peek_kind_n(&self, n: usize) -> Option<&'static str> {
        self.nth_significant(n).map(|j| self.toks[j].kind)
    }

    fn peek_kind(&self) -> Option<&'static str> {
        self.peek_kind_n(0)
    }

    /// Index of the n-th significant token from the cursor.
    fn nth_significant(&self, n: usize) -> Option<usize> {
        let mut j = self.i;
        let mut count = 0;
        while j < self.toks.len() {
            if self.toks[j].trivia {
                j += 1;
                continue;
            }
            if count == n {
                return Some(j);
            }
            count += 1;
            j += 1;
        }
        None
    }

    fn peek_n_text(&self, n: usize) -> Option<&str> {
        self.nth_significant(n)
            .map(|j| self.toks[j].span.text(self.src))
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

    fn at_terminator(&self) -> bool {
        matches!(self.peek_text(), Some(t) if TERMINATORS.contains(&t))
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

    fn parse_program(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.parse_statements(&mut c);
            self.skip_seps(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            // A stray terminator keyword (e.g. an unmatched `end`) at top level:
            // wrap it as an `ErrorStmt` and consume one token to guarantee
            // progress; the bytes stay in the tree.
            let mut e = Vec::new();
            self.eat(&mut e);
            c.push(Child::Node(self.make_node(node::ERROR_STMT, e)));
        }
        self.make_node(node::PROGRAM, c)
    }

    /// Parse a run of statements, stopping at the first terminator keyword (left
    /// unconsumed for the enclosing construct) or at end of input.
    fn parse_statements(&mut self, into: &mut Vec<Child>) {
        loop {
            self.skip_seps(into);
            if self.peek_kind().is_none() || self.at_terminator() {
                break;
            }
            let stmt = self.parse_statement();
            into.push(Child::Node(stmt));
        }
    }

    // --- statements ---------------------------------------------------------

    fn parse_statement(&mut self) -> Node {
        let kw = self.peek_text().map(|s| s.to_string());
        match kw.as_deref() {
            Some("def") => self.finish_def(),
            Some("class") => self.finish_class(),
            Some("module") => self.finish_module(),
            Some(k) if COMPOUND_KEYWORDS.contains(&k) => self.finish_compound(),
            _ => self.finish_expr_stmt(),
        }
    }

    /// `def NAME(params) … end`, `def self.NAME … end`, `def NAME = expr`
    /// (endless), and operator/setter method names.
    fn finish_def(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // def
        let name = self.parse_method_name();
        c.push(Child::Node(name));
        self.ws(&mut c);
        if self.at("(") {
            let g = self.parse_delimited();
            c.push(Child::Node(g));
        } else if let Some(h) = self.collect_def_header() {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        // Endless method: `def square(x) = x * x`.
        if self.at("=") {
            self.eat(&mut c); // =
            self.collect_expr_line(&mut c);
            self.consume_line_end(&mut c);
            return self.make_node(node::METHOD, c);
        }
        self.consume_line_end(&mut c);
        let body = self.parse_body();
        c.push(Child::Node(body));
        self.ws(&mut c);
        if self.at("end") {
            self.eat(&mut c);
        }
        self.make_node(node::METHOD, c)
    }

    /// `class NAME [< Super] … end` or `class << self … end` (singleton class).
    fn finish_class(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // class
        self.ws(&mut c);
        let singleton = self.at("<<");
        if singleton {
            self.eat(&mut c); // <<
            let name = self.parse_name_path();
            c.push(Child::Node(name));
        } else {
            let name = self.parse_name_path();
            c.push(Child::Node(name));
            self.ws(&mut c);
            if self.at("<") {
                let sup = self.parse_superclass();
                c.push(Child::Node(sup));
            }
        }
        self.consume_line_end(&mut c);
        let body = self.parse_body();
        c.push(Child::Node(body));
        self.ws(&mut c);
        if self.at("end") {
            self.eat(&mut c);
        }
        let kind = if singleton {
            node::SINGLETON_CLASS
        } else {
            node::CLASS
        };
        self.make_node(kind, c)
    }

    /// `module NAME … end`.
    fn finish_module(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // module
        let name = self.parse_name_path();
        c.push(Child::Node(name));
        self.consume_line_end(&mut c);
        let body = self.parse_body();
        c.push(Child::Node(body));
        self.ws(&mut c);
        if self.at("end") {
            self.eat(&mut c);
        }
        self.make_node(node::MODULE, c)
    }

    /// `if/unless/while/until/case/begin/for … end`, including the intermediate
    /// `elsif`/`else`/`when`/`in`/`rescue`/`ensure` clauses.
    fn finish_compound(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // the opening keyword
        if let Some(h) = self.collect_header() {
            c.push(Child::Node(h));
        }
        self.consume_clause_connector(&mut c); // optional `then`/`do`
        loop {
            let body = self.parse_body();
            c.push(Child::Node(body));
            self.ws(&mut c);
            let nxt = self.peek_text().map(|s| s.to_string());
            match nxt.as_deref() {
                Some("end") => {
                    self.eat(&mut c);
                    break;
                }
                Some(k) if HEADERED_CLAUSES.contains(&k) => {
                    self.eat(&mut c); // elsif/when/in/rescue
                    if let Some(h) = self.collect_header() {
                        c.push(Child::Node(h));
                    }
                    self.consume_clause_connector(&mut c);
                }
                Some("else") | Some("ensure") => {
                    self.eat(&mut c);
                    self.consume_line_end(&mut c);
                }
                _ => break, // EOF / unterminated; still lossless
            }
        }
        self.make_node(node::COMPOUND, c)
    }

    /// An expression statement: collect a logical line, descending into balanced
    /// groups, `do…end` blocks, and value-position `if/case/…end` constructs.
    fn finish_expr_stmt(&mut self) -> Node {
        let mut c = Vec::new();
        self.collect_expr_line(&mut c);
        self.consume_line_end(&mut c);
        self.make_node(node::EXPR_STMT, c)
    }

    // --- name parsing -------------------------------------------------------

    /// Parse a method name: an operator (`+`, `<=>`, `[]`, `[]=`), a plain name
    /// (`foo`, `foo?`, `foo!`), a setter (`foo=`), or a receiver-qualified name
    /// (`self.foo`, `Klass.foo`). Adjacency (no whitespace gap) drives the
    /// receiver/setter chaining.
    fn parse_method_name(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        let first = match self.toks.get(self.i) {
            Some(t) if !t.trivia => t,
            _ => return self.make_node(node::NAME, c),
        };
        let first_text = first.span.text(self.src);
        if first_text == "(" {
            return self.make_node(node::NAME, c);
        }
        let is_op = first.kind == tk::PUNCT;
        self.eat(&mut c);
        if is_op {
            // Operator method: absorb the adjacent punctuation run (`[]`, `[]=`),
            // stopping at `(` or any whitespace.
            while let Some(t) = self.toks.get(self.i) {
                if t.trivia || t.kind != tk::PUNCT || t.span.text(self.src) == "(" {
                    break;
                }
                self.eat(&mut c);
            }
        } else {
            // Receiver chain: `self.foo`, `A::B.bar`.
            loop {
                let is_connector = matches!(
                    self.toks.get(self.i),
                    Some(t) if !t.trivia && matches!(t.span.text(self.src), "." | "::")
                );
                if !is_connector {
                    break;
                }
                self.eat(&mut c); // . or ::
                let has_name = matches!(self.toks.get(self.i), Some(t) if !t.trivia);
                if has_name {
                    self.eat(&mut c); // the name after the connector
                }
            }
            // Setter method: `def foo=(v)` — an adjacent `=` immediately before `(`.
            if matches!(self.toks.get(self.i), Some(t) if !t.trivia && t.span.text(self.src) == "=")
                && matches!(self.toks.get(self.i + 1), Some(n) if n.span.text(self.src) == "(")
            {
                self.eat(&mut c); // =
            }
        }
        self.make_node(node::NAME, c)
    }

    /// A constant/identifier path used as a class or module name: `Foo`,
    /// `Foo::Bar`. Captures the adjacent `ident`/`::`/`.` run.
    fn parse_name_path(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        if matches!(self.toks.get(self.i), Some(t) if t.trivia) {
            return self.make_node(node::NAME, c);
        }
        // First segment.
        if self.toks.get(self.i).is_some() {
            self.eat(&mut c);
        }
        loop {
            let is_connector = matches!(
                self.toks.get(self.i),
                Some(t) if !t.trivia && matches!(t.span.text(self.src), "::" | ".")
            );
            if !is_connector {
                break;
            }
            self.eat(&mut c);
            let has_name = matches!(self.toks.get(self.i), Some(t) if !t.trivia);
            if has_name {
                self.eat(&mut c);
            }
        }
        self.make_node(node::NAME, c)
    }

    /// `< Super` after a class name — captures the `<` and the superclass
    /// expression up to the logical line end.
    fn parse_superclass(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // <
        loop {
            self.ws(&mut c);
            match self.peek_kind() {
                None => break,
                Some(k) if k == tk::NEWLINE => break,
                _ if self.at(";") => break,
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
        self.make_node(node::SUPERCLASS, c)
    }

    // --- headers / lines ----------------------------------------------------

    /// Collect a compound-statement header (a condition / iterator expression) up
    /// to the logical line end or a `then`/`do` connector, descending into groups.
    fn collect_header(&mut self) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            match self.peek_kind() {
                None => break,
                Some(k) if k == tk::NEWLINE => break,
                _ if self.at(";") => break,
                _ if self.at("then") || self.at("do") => break,
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

    /// Collect bare `def` parameters (no parentheses) up to the logical line end or
    /// an endless-method `=`, descending into groups.
    fn collect_def_header(&mut self) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            match self.peek_kind() {
                None => break,
                Some(k) if k == tk::NEWLINE => break,
                _ if self.at(";") || self.at("=") => break,
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

    /// Consume an optional `then` / `do` clause connector plus the line end.
    fn consume_clause_connector(&mut self, c: &mut Vec<Child>) {
        self.ws(c);
        if self.at("then") || self.at("do") {
            self.eat(c);
        }
        self.consume_line_end(c);
    }

    /// Consume trailing trivia and a single `newline`/`;` statement terminator.
    fn consume_line_end(&mut self, c: &mut Vec<Child>) {
        self.ws(c);
        if self.at_newline() || self.at(";") {
            self.eat(c);
        }
    }

    /// Collect an expression up to the logical line end (a `newline`/`;` at bracket
    /// depth 0), descending into balanced groups and `do…end` blocks, and
    /// recursing into value-position `if/unless/while/until/case/begin … end`
    /// constructs (e.g. `x = if c then 1 else 2 end`). Trailing modifiers
    /// (`x if y`) are left as plain tokens.
    fn collect_expr_line(&mut self, c: &mut Vec<Child>) {
        let mut prev_is_operator = true; // start of line is a value-begin position
        loop {
            self.ws(c);
            match self.peek_kind() {
                None => break,
                Some(k) if k == tk::NEWLINE => break,
                _ if self.at(";") => break,
                _ if self.at_terminator() => break,
                // Inside a method-call brace block, the matching `}` ends the
                // current statement — leave it for the brace-body parser.
                _ if self.brace_body_depth > 0 && self.at("}") => break,
                _ => {
                    // A `{` in *value* position (`foo {`, `Foo.new {`, `xs.map {`)
                    // is a method block, not a hash. Parse its contents as
                    // statements so nested `class`/`def` are recognized (the
                    // brace-body analogue of the `do…end` path below). A `{` in
                    // value-*begin* position stays a hash literal via the
                    // `at_open` → `parse_delimited` path.
                    if !prev_is_operator && self.at("{") {
                        self.eat(c); // {
                        let body = self.parse_brace_body();
                        c.push(Child::Node(body));
                        self.ws(c);
                        if self.at("}") {
                            self.eat(c);
                        }
                        prev_is_operator = false;
                        continue;
                    }
                    if self.at_open() {
                        let g = self.parse_delimited();
                        c.push(Child::Node(g));
                        prev_is_operator = false;
                        continue;
                    }
                    if self.at("do") {
                        self.eat(c); // do
                        self.consume_line_end(c);
                        let body = self.parse_body();
                        c.push(Child::Node(body));
                        self.ws(c);
                        if self.at("end") {
                            self.eat(c);
                        }
                        prev_is_operator = false;
                        continue;
                    }
                    if prev_is_operator && self.at_value_compound() {
                        let comp = self.finish_compound();
                        c.push(Child::Node(comp));
                        prev_is_operator = false;
                        continue;
                    }
                    // Plain token. Track whether it is an operator (a value-begin
                    // follows) for the next iteration's value-compound decision.
                    let txt = self.peek_text().unwrap_or("");
                    let kind = self.peek_kind();
                    prev_is_operator = kind == Some(tk::PUNCT) && !matches!(txt, ")" | "]" | "}");
                    self.eat(c);
                }
            }
        }
    }

    /// True when the cursor is at a keyword that, in value position, opens an
    /// `end`-block (so it must be recursed, not treated as a trailing modifier).
    fn at_value_compound(&self) -> bool {
        matches!(
            self.peek_text(),
            Some("if" | "unless" | "while" | "until" | "case" | "begin")
        )
    }

    // --- bodies (end-delimited blocks) --------------------------------------

    /// Parse a statement body up to its terminator. Depth-guarded: beyond
    /// [`MAX_DEPTH`] the body is consumed as a flat token run rather than
    /// recursing, so deep nesting cannot overflow.
    fn parse_body(&mut self) -> Node {
        if self.depth >= MAX_DEPTH {
            let mut c = Vec::new();
            self.consume_body_flat(&mut c);
            self.note_depth_limit();
            return self.make_node(node::BLOCK, c);
        }
        self.depth += 1;
        // An `end`-delimited body is balanced by `end`, not `}`; a `}` inside it
        // is a hash/plain token, so suspend brace-body stopping while we descend.
        let saved_brace = self.brace_body_depth;
        self.brace_body_depth = 0;
        let mut c = Vec::new();
        self.parse_statements(&mut c);
        let block = self.make_node(node::BLOCK, c);
        self.brace_body_depth = saved_brace;
        self.depth -= 1;
        block
    }

    /// Parse the body of a method-call brace block `foo { … }` — the opening `{`
    /// already eaten — as statements up to the matching `}`. The mirror of
    /// [`parse_body`] for `do…end`: it yields a [`node::BLOCK`] so the lowering's
    /// `walk_stmts` recurses it and finds nested `class`/`def`. Brace balance is
    /// tracked implicitly: a value-begin `{` inside is consumed whole as a hash by
    /// `parse_delimited`, and a value-position `{` recurses here, so the first
    /// *top-level* `}` is genuinely this block's closer. Depth-guarded and
    /// lossless; a zero-width statement is force-advanced so progress is assured.
    fn parse_brace_body(&mut self) -> Node {
        if self.depth >= MAX_DEPTH {
            let mut c = Vec::new();
            self.consume_brace_body_flat(&mut c);
            self.note_depth_limit();
            return self.make_node(node::BLOCK, c);
        }
        self.depth += 1;
        self.brace_body_depth += 1;
        let mut c = Vec::new();
        loop {
            self.skip_seps(&mut c);
            if self.peek_kind().is_none() || self.at("}") {
                break;
            }
            let before = self.i;
            let stmt = self.parse_statement();
            c.push(Child::Node(stmt));
            if self.i == before {
                // A statement that consumed nothing (e.g. a stray terminator):
                // eat one token so the loop cannot spin forever. Stays lossless.
                self.eat(&mut c);
            }
        }
        self.brace_body_depth -= 1;
        self.depth -= 1;
        self.make_node(node::BLOCK, c)
    }

    /// At the depth cap, swallow a brace-block body as a flat token run, tracking
    /// `{}`/`(`/`[` balance so the matching `}` is left for the caller. Lossless;
    /// the truncation is reported via a `depth_limit` diagnostic by the caller.
    fn consume_brace_body_flat(&mut self, out: &mut Vec<Child>) {
        let mut balance: i32 = 0;
        loop {
            self.ws(out);
            match self.peek_text() {
                None => break,
                Some("}") if balance == 0 => break,
                Some("(") | Some("[") | Some("{") => balance += 1,
                Some(")") | Some("]") | Some("}") => balance -= 1,
                _ => {}
            }
            self.eat(out);
        }
    }

    /// At the depth cap, swallow a body as a flat token run, tracking `end`-block
    /// balance so the matching terminator is left for the caller. Lossless; the
    /// truncation is reported via a `depth_limit` diagnostic.
    fn consume_body_flat(&mut self, out: &mut Vec<Child>) {
        let mut balance: i32 = 0;
        loop {
            self.skip_seps(out);
            let t = self.peek_text().map(|s| s.to_string());
            match t.as_deref() {
                None => break,
                Some(t) if balance == 0 && TERMINATORS.contains(&t) => break,
                Some(t) => {
                    if is_block_opener(t) {
                        balance += 1;
                    } else if t == "end" {
                        balance -= 1;
                    }
                    self.eat(out);
                }
            }
        }
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}` as a flat run
    /// of tokens and nested groups. Depth-guarded.
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

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "ruby.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; region flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }
}

/// Keywords that open an `end`-block, used by the depth-cap flat scanner.
fn is_block_opener(text: &str) -> bool {
    matches!(
        text,
        "def"
            | "class"
            | "module"
            | "if"
            | "unless"
            | "while"
            | "until"
            | "case"
            | "begin"
            | "for"
            | "do"
    )
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
require 'set'
require_relative 'helper'

VERSION = '1.0'

module Geo
  class Point < Base
    include Comparable

    def initialize(x, y)
      @x = x
      @y = y
    end

    def self.origin
      new(0, 0)
    end

    def norm
      Math.sqrt(@x * @x + @y * @y)
    end

    def <=>(other)
      norm <=> other.norm
    end
  end
end

def add(a, b)
  if a > b
    a
  else
    b
  end
end

[1, 2, 3].each do |n|
  puts <<~MSG
    value: #{n}
  MSG
end
";
        let tree = parse("geo.rb", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "require 'x'\nclass C\n  def m\n  end\nend\n\ndef f\nend\n";
        let tree = parse("t.rb", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::CLASS), "class not found: {kinds:?}");
        assert!(kinds.contains(&node::METHOD), "def not found: {kinds:?}");
    }

    #[test]
    fn methods_nest_inside_class_bodies() {
        let src = "class C\n  def a\n  end\n  def b\n  end\nend\n";
        let tree = parse("t.rb", src);
        let class = tree
            .root
            .children_of(node::CLASS)
            .next()
            .expect("a class node");
        let block = class.child(node::BLOCK).expect("class has a block");
        let methods: Vec<&str> = block
            .children_of(node::METHOD)
            .filter_map(|f| f.child(node::NAME))
            .filter_map(|n| n.tokens().next())
            .map(|t| t.span.text(src))
            .collect();
        assert_eq!(methods, vec!["a", "b"]);
    }

    #[test]
    fn endless_method_has_no_end() {
        let src = "def square(x) = x * x\nx = 1\n";
        let tree = parse("t.rb", src);
        let m = tree
            .root
            .children_of(node::METHOD)
            .next()
            .expect("a method");
        // The endless method and the following statement are siblings.
        let methods = tree.root.children_of(node::METHOD).count();
        assert_eq!(methods, 1, "only one def");
        assert!(m.child(node::NAME).is_some());
        assert!(tree.is_lossless());
    }

    #[test]
    fn modifier_if_is_not_a_block() {
        // A trailing modifier `if` must not start an end-block.
        let src = "def f\n  return 1 if a > b\n  2\nend\n";
        let tree = parse("t.rb", src);
        // Exactly one top-level def, fully closed by its own `end`.
        assert_eq!(tree.root.children_of(node::METHOD).count(), 1);
        assert!(tree.is_lossless());
    }

    #[test]
    fn singleton_class_block() {
        let src = "class C\n  class << self\n    def helper\n    end\n  end\nend\n";
        let tree = parse("t.rb", src);
        let class = tree.root.children_of(node::CLASS).next().expect("class");
        let block = class.child(node::BLOCK).expect("block");
        assert!(
            block.children_of(node::SINGLETON_CLASS).next().is_some(),
            "class << self should parse as a SingletonClass"
        );
        assert!(tree.is_lossless());
    }

    #[test]
    fn case_when_and_begin_rescue() {
        let src = "\
def f(x)
  case x
  when 1
    :one
  else
    :many
  end
rescue => e
  nil
end
";
        let tree = parse("t.rb", src);
        assert_eq!(tree.root.children_of(node::METHOD).count(), 1);
        assert!(tree.is_lossless());
    }

    #[test]
    fn do_block_with_nested_def_round_trips() {
        let src = "describe 'x' do\n  it 'works' do\n    expect(1).to eq(1)\n  end\nend\n";
        let tree = parse("spec.rb", src);
        assert!(tree.is_lossless());
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        // Far deeper than MAX_DEPTH on both axes; must not stack-overflow and must
        // stay lossless.
        let deep_brackets = format!("x = {}{}\n", "(".repeat(10_000), ")".repeat(10_000));
        let mut deep_blocks = String::new();
        for _ in 0..2_000 {
            deep_blocks.push_str("begin\n");
        }
        for _ in 0..2_000 {
            deep_blocks.push_str("end\n");
        }
        for src in [deep_brackets, deep_blocks] {
            let tree = parse("deep.rb", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics
                    .iter()
                    .any(|d| d.code == "ruby.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "def f\n  x = (1, 2\n",     // unterminated paren + body
            "λ = '☃'  # unicode\n",     // multi-byte identifiers/strings
            "",                         // empty file
            "\n\n   \n# trailing\n",    // only blanks and comments
            "end\nclass C\nend\n",      // a stray leading `end`
            "x = <<~SQL\n  select 1\n", // unterminated heredoc
        ] {
            let tree = parse("edge.rb", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }

    /// Helper: collect the names of `Method` defs that appear inside any `Block`
    /// child of any top-level `ExprStmt` (the brace/do block bodies).
    fn block_def_names<'a>(tree: &'a ParseTree, src: &'a str) -> Vec<&'a str> {
        let mut out = Vec::new();
        for stmt in tree.root.children_of(node::EXPR_STMT) {
            for block in stmt.children_of(node::BLOCK) {
                for m in block.children_of(node::METHOD) {
                    if let Some(name) = m
                        .child(node::NAME)
                        .and_then(|n| n.tokens().next())
                        .map(|t| t.span.text(src))
                    {
                        out.push(name);
                    }
                }
            }
        }
        out
    }

    #[test]
    fn brace_block_def_is_found_and_lossless() {
        // A `def` placed inside a method-call BRACE block must surface as a
        // `Method` inside the `ExprStmt`'s `Block` (the do…end analogue), so the
        // lowering's `walk_stmts` BLOCK recursion finds it. Issue #3.
        for (src, want) in [
            ("Foo.class_eval { def bar; end }\n", "bar"),
            ("Module.new { def baz; end }\n", "baz"),
        ] {
            let tree = parse("t.rb", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
            let names = block_def_names(&tree, src);
            assert!(
                names.contains(&want),
                "expected a `{want}` def inside the brace block of {src:?}, got {names:?}"
            );
        }
    }

    #[test]
    fn brace_block_with_params_and_nested_call() {
        // Brace blocks must balance nested `{}` (here a hash arg inside) and end
        // at the right `}`, while still exposing the inner def.
        let src = "scope.configure { settings.merge({ a: 1 }); def setup; end }\n";
        let tree = parse("t.rb", src);
        assert!(tree.is_lossless());
        assert!(block_def_names(&tree, src).contains(&"setup"));
    }

    /// Recursively count `Block` nodes anywhere under `n`.
    fn count_blocks(n: &Node) -> usize {
        let mut total = if n.kind == node::BLOCK { 1 } else { 0 };
        for child in n.child_nodes() {
            total += count_blocks(child);
        }
        total
    }

    #[test]
    fn hash_literal_is_not_a_block() {
        // A `{` in value-begin position is a hash, not a block: it must parse via
        // the BRACE group path, never produce a statement `Block`, and round-trip.
        for src in [
            "h = { a: 1 }\n",
            "config = { a: 1, b: { c: 2 } }\n",
            "foo({ a: 1 })\n",
            "xs = [{ a: 1 }, { b: 2 }]\n",
        ] {
            let tree = parse("t.rb", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
            assert_eq!(
                count_blocks(&tree.root),
                0,
                "hash `{src}` must not be mis-parsed into any Block body"
            );
        }
        // Direct check that a top-level hash is a Brace group.
        let tree = parse("t.rb", "h = { a: 1 }\n");
        let stmt = tree
            .root
            .children_of(node::EXPR_STMT)
            .next()
            .expect("an expr stmt");
        assert!(
            stmt.children_of(node::BRACE).next().is_some(),
            "a value-begin `{{` should be a Brace group"
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src = "class C < B\n  def m\n    helper\n  end\nend\n\ndef helper\nend\n";
        let a = parse("m.rb", src);
        let b = parse("m.rb", src);
        assert_eq!(a.root, b.root, "parse output must be identical across runs");
    }
}
