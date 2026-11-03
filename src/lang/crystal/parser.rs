//! Crystal parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Ruby parser ([`crate::lang::ruby::parser`], itself modelled
//! on the Rust/Python parsers): item *headers* are parsed precisely — we always
//! know a `def`'s name and receiver, a `class`/`struct`/`enum`'s name, superclass,
//! and generic parameters, a `module`/`lib`'s name — while bodies and expressions
//! are captured as a mix of recognized sub-statements, balanced delimiter groups
//! (`Paren`/`Bracket`/`Brace`), and flat tokens, which is perfectly lossless. Graph
//! facts (calls, requires, includes, inheritance) are later read off these real
//! tokens in the lowering pass, never invented.
//!
//! Crystal's blocks are delimited by the `end` keyword (and `do…end` / `{…}` for
//! method blocks), not by braces or indentation. A compound statement opens with a
//! keyword (`def`/`class`/`struct`/`enum`/`module`/`lib`/`annotation`/`macro`/`if`/
//! `unless`/`while`/`until`/`case`/`begin`/`select`) and runs until its matching
//! `end`, with intermediate clause keywords (`elsif`/`else`/`when`/`in`/`rescue`/
//! `ensure`) handled in between. Leading visibility/`abstract` modifiers
//! (`private`/`protected`/`abstract`) are eaten as a prefix; an `abstract def` has
//! no body and no `end`. Crystal macro bodies wrap control flow in `{% … %}` /
//! `{{ … }}`, which the parser captures as balanced `Brace` groups, so a `{% end %}`
//! never closes the enclosing `macro`.
//!
//! Anything unrecognized still lands in the tree as its exact tokens (an
//! `ErrorStmt` node or a flat token run), so the result always round-trips
//! byte-for-byte. The recursion is depth-guarded at [`MAX_DEPTH`] against hostile
//! nesting (both bracket and `end`-block nesting), because a `catch_unwind` cannot
//! catch a stack overflow.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::crystal::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const PROGRAM: &str = "Program";
    pub const METHOD: &str = "Method";
    pub const MACRO_DEF: &str = "MacroDef";
    pub const CLASS: &str = "Class";
    pub const STRUCT: &str = "Struct";
    pub const ENUM: &str = "Enum";
    pub const ANNOTATION_DEF: &str = "AnnotationDef";
    pub const MODULE: &str = "Module";
    pub const LIB: &str = "Lib";
    pub const COMPOUND: &str = "Compound";
    pub const EXPR_STMT: &str = "ExprStmt";
    pub const ERROR_STMT: &str = "ErrorStmt";

    pub const NAME: &str = "Name";
    pub const SUPERCLASS: &str = "Superclass";
    pub const TYPE_ANNOT: &str = "TypeAnnot";
    pub const HEADER: &str = "Header";
    pub const BLOCK: &str = "Block";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat run. Protects against stack overflow on pathological or
/// hostile inputs — mirrors the Rust/Ruby parsers' guard exactly, since a
/// `catch_unwind` cannot catch a stack overflow.
const MAX_DEPTH: usize = 256;

/// Keywords that open an `end`-terminated compound statement.
const COMPOUND_KEYWORDS: &[&str] = &["if", "unless", "while", "until", "case", "begin", "select"];

/// Keywords that close or continue a compound body (a body parse stops on these,
/// leaving them for the enclosing construct to consume).
const TERMINATORS: &[&str] = &["end", "else", "elsif", "when", "in", "rescue", "ensure"];

/// Intermediate clause keywords that introduce another sub-body and carry a header
/// of their own (`elsif cond`, `when x`, `rescue E => e`).
const HEADERED_CLAUSES: &[&str] = &["elsif", "when", "in", "rescue"];

/// Leading modifiers that may precede a definition keyword.
const MODIFIERS: &[&str] = &["private", "protected", "abstract"];

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = CrystalParser {
        src: source,
        toks,
        i: 0,
        diags: Vec::new(),
        depth: 0,
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

struct CrystalParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> CrystalParser<'s> {
    // --- cursor primitives --------------------------------------------------

    /// Append the current token (trivia or not) to `out` and advance.
    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading **trivia** tokens (whitespace, comments, line
    /// continuations) into `out`. A `newline` is *not* trivia in Crystal, so it is
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
            // wrap it as an `ErrorStmt` and consume one token to guarantee progress;
            // the bytes stay in the tree.
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
        // Collect leading visibility / `abstract` modifiers as a prefix.
        let mut prefix = Vec::new();
        let mut is_abstract = false;
        loop {
            self.ws(&mut prefix);
            match self.peek_text() {
                Some("abstract") => {
                    is_abstract = true;
                    self.eat(&mut prefix);
                }
                Some(m) if MODIFIERS.contains(&m) => self.eat(&mut prefix),
                _ => break,
            }
        }
        let kw = self.peek_text().map(|s| s.to_string());
        match kw.as_deref() {
            Some("def") => self.finish_def(prefix, is_abstract),
            Some("macro") => self.finish_macro(prefix),
            Some("class") => self.finish_type(prefix, node::CLASS),
            Some("struct") => self.finish_type(prefix, node::STRUCT),
            Some("enum") => self.finish_type(prefix, node::ENUM),
            Some("annotation") => self.finish_type(prefix, node::ANNOTATION_DEF),
            Some("module") => self.finish_namespace(prefix, node::MODULE),
            Some("lib") => self.finish_namespace(prefix, node::LIB),
            Some(k) if COMPOUND_KEYWORDS.contains(&k) => self.finish_compound(prefix),
            _ => self.finish_expr_stmt(prefix),
        }
    }

    /// `def NAME(params) : Ret … end`, `def self.NAME …`, endless `def NAME = expr`,
    /// and bodiless `abstract def NAME`.
    fn finish_def(&mut self, mut c: Vec<Child>, is_abstract: bool) -> Node {
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
        if self.at(":") {
            let rt = self.collect_type_annot();
            c.push(Child::Node(rt));
        }
        self.ws(&mut c);
        // `abstract def` has no body and no `end`.
        if is_abstract {
            self.consume_line_end(&mut c);
            return self.make_node(node::METHOD, c);
        }
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

    /// `macro NAME(params) … end`. The body is captured generically; `{% … %}`
    /// macro control blocks land inside `Brace` groups, so they never close the
    /// macro early.
    fn finish_macro(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // macro
        let name = self.parse_method_name();
        c.push(Child::Node(name));
        self.ws(&mut c);
        if self.at("(") {
            let g = self.parse_delimited();
            c.push(Child::Node(g));
        } else if let Some(h) = self.collect_def_header() {
            c.push(Child::Node(h));
        }
        self.consume_line_end(&mut c);
        let body = self.parse_body();
        c.push(Child::Node(body));
        self.ws(&mut c);
        if self.at("end") {
            self.eat(&mut c);
        }
        self.make_node(node::MACRO_DEF, c)
    }

    /// `class/struct/enum/annotation NAME[(Generics)][< Super][ : BaseType] … end`.
    fn finish_type(&mut self, mut c: Vec<Child>, kind: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // the keyword
        let name = self.parse_name_path();
        c.push(Child::Node(name));
        self.ws(&mut c);
        // Generic parameters: `class Foo(T)`.
        if self.at("(") {
            let g = self.parse_delimited();
            c.push(Child::Node(g));
        }
        self.ws(&mut c);
        if self.at("<") {
            let sup = self.parse_superclass();
            c.push(Child::Node(sup));
        }
        self.ws(&mut c);
        // Enum base type: `enum Color : UInt8`.
        if self.at(":") {
            let bt = self.collect_type_annot();
            c.push(Child::Node(bt));
        }
        self.consume_line_end(&mut c);
        let body = self.parse_body();
        c.push(Child::Node(body));
        self.ws(&mut c);
        if self.at("end") {
            self.eat(&mut c);
        }
        self.make_node(kind, c)
    }

    /// `module NAME … end` / `lib NAME … end`.
    fn finish_namespace(&mut self, mut c: Vec<Child>, kind: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // module / lib
        let name = self.parse_name_path();
        c.push(Child::Node(name));
        self.ws(&mut c);
        if self.at("(") {
            let g = self.parse_delimited();
            c.push(Child::Node(g));
        }
        self.consume_line_end(&mut c);
        let body = self.parse_body();
        c.push(Child::Node(body));
        self.ws(&mut c);
        if self.at("end") {
            self.eat(&mut c);
        }
        self.make_node(kind, c)
    }

    /// `if/unless/while/until/case/begin/select … end`, including the intermediate
    /// `elsif`/`else`/`when`/`in`/`rescue`/`ensure` clauses.
    fn finish_compound(&mut self, mut c: Vec<Child>) -> Node {
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
    fn finish_expr_stmt(&mut self, mut c: Vec<Child>) -> Node {
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

    /// `< Super` after a type name — captures the `<` and the superclass expression
    /// up to the logical line end, descending into groups so generic args
    /// (`< Bar(T)`) become a child group rather than leaking flat tokens.
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

    /// Collect bare `def`/`macro` parameters (no parentheses) up to the logical line
    /// end, an endless-method `=`, or a `:` return-type marker, descending into
    /// groups.
    fn collect_def_header(&mut self) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            match self.peek_kind() {
                None => break,
                Some(k) if k == tk::NEWLINE => break,
                _ if self.at(";") || self.at("=") || self.at(":") => break,
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

    /// Collect a `: Type` annotation (a `def` return type or an `enum` base type)
    /// up to the logical line end, an `=`, or a `;`, descending into groups.
    fn collect_type_annot(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // :
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
        self.make_node(node::TYPE_ANNOT, c)
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
    /// depth 0), descending into balanced groups and `do…end` blocks, and recursing
    /// into value-position `if/unless/while/until/case/begin … end` constructs (e.g.
    /// `x = if c then 1 else 2 end`). Trailing modifiers (`x if y`) stay as plain
    /// tokens.
    fn collect_expr_line(&mut self, c: &mut Vec<Child>) {
        let mut prev_is_operator = true; // start of line is a value-begin position
        loop {
            self.ws(c);
            match self.peek_kind() {
                None => break,
                Some(k) if k == tk::NEWLINE => break,
                _ if self.at(";") => break,
                _ if self.at_terminator() => break,
                _ => {
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
                        let comp = self.finish_compound(Vec::new());
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
    /// [`MAX_DEPTH`] the body is consumed as a flat token run rather than recursing,
    /// so deep nesting cannot overflow.
    fn parse_body(&mut self) -> Node {
        if self.depth >= MAX_DEPTH {
            let mut c = Vec::new();
            self.consume_body_flat(&mut c);
            self.note_depth_limit();
            return self.make_node(node::BLOCK, c);
        }
        self.depth += 1;
        let mut c = Vec::new();
        self.parse_statements(&mut c);
        let block = self.make_node(node::BLOCK, c);
        self.depth -= 1;
        block
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
            code: "crystal.depth_limit",
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
            | "macro"
            | "class"
            | "struct"
            | "enum"
            | "annotation"
            | "module"
            | "lib"
            | "if"
            | "unless"
            | "while"
            | "until"
            | "case"
            | "begin"
            | "select"
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
require \"json\"
require \"./helper\"

VERSION = \"1.0\"

module Geo
  class Point < Base
    include Comparable

    def initialize(@x : Int32, @y : Int32)
    end

    def self.origin : Point
      new(0, 0)
    end

    def norm : Float64
      Math.sqrt(@x * @x + @y * @y)
    end

    def <=>(other)
      norm <=> other.norm
    end
  end

  struct Vec2(T)
    abstract def length : T
  end

  enum Color : UInt8
    Red
    Green
    Blue
  end
end

@[Link(\"c\")]
lib LibC
  fun printf(format : UInt8*, ...) : Int32
end

macro define(name)
  def {{name}}
    {% if true %}
      42
    {% end %}
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
  puts <<-MSG
    value: #{n}
  MSG
end
";
        let tree = parse("geo.cr", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "require \"x\"\nclass C\n  def m\n  end\nend\n\ndef f\nend\n\nstruct S\nend\n";
        let tree = parse("t.cr", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::CLASS), "class not found: {kinds:?}");
        assert!(kinds.contains(&node::METHOD), "def not found: {kinds:?}");
        assert!(kinds.contains(&node::STRUCT), "struct not found: {kinds:?}");
    }

    #[test]
    fn methods_nest_inside_class_bodies() {
        let src = "class C\n  def a\n  end\n  def b\n  end\nend\n";
        let tree = parse("t.cr", src);
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
        let tree = parse("t.cr", src);
        assert_eq!(
            tree.root.children_of(node::METHOD).count(),
            1,
            "only one def"
        );
        assert!(tree.is_lossless());
    }

    #[test]
    fn abstract_def_has_no_body() {
        let src = "abstract class Shape\n  abstract def area : Float64\nend\n";
        let tree = parse("t.cr", src);
        let class = tree.root.children_of(node::CLASS).next().expect("class");
        let block = class.child(node::BLOCK).expect("block");
        // The abstract def is a Method with a Name and no Block child.
        let m = block
            .children_of(node::METHOD)
            .next()
            .expect("abstract method");
        assert!(m.child(node::BLOCK).is_none(), "abstract def has no body");
        assert!(tree.is_lossless());
    }

    #[test]
    fn macro_with_inner_end_round_trips() {
        let src = "macro foo\n  {% if x %}\n    bar\n  {% end %}\nend\n\ndef after\nend\n";
        let tree = parse("m.cr", src);
        // The `{% end %}` must not close the macro: there is exactly one MacroDef
        // and one following def, both top-level siblings.
        assert_eq!(tree.root.children_of(node::MACRO_DEF).count(), 1);
        assert_eq!(tree.root.children_of(node::METHOD).count(), 1);
        assert!(tree.is_lossless());
    }

    #[test]
    fn modifier_if_is_not_a_block() {
        let src = "def f\n  return 1 if a > b\n  2\nend\n";
        let tree = parse("t.cr", src);
        assert_eq!(tree.root.children_of(node::METHOD).count(), 1);
        assert!(tree.is_lossless());
    }

    #[test]
    fn generic_superclass_keeps_args_in_a_group() {
        let src = "class Foo(T) < Bar(T)\nend\n";
        let tree = parse("t.cr", src);
        let class = tree.root.children_of(node::CLASS).next().expect("class");
        let sup = class.child(node::SUPERCLASS).expect("superclass");
        // Direct tokens of the Superclass: `<` and `Bar` (the `(T)` is a child group).
        let idents: Vec<&str> = sup
            .tokens()
            .filter(|t| t.kind == tk::IDENT)
            .map(|t| t.span.text(src))
            .collect();
        assert_eq!(idents, vec!["Bar"]);
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
rescue ex
  nil
end
";
        let tree = parse("t.cr", src);
        assert_eq!(tree.root.children_of(node::METHOD).count(), 1);
        assert!(tree.is_lossless());
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let deep_brackets = format!("x = {}{}\n", "(".repeat(10_000), ")".repeat(10_000));
        let mut deep_blocks = String::new();
        for _ in 0..2_000 {
            deep_blocks.push_str("begin\n");
        }
        for _ in 0..2_000 {
            deep_blocks.push_str("end\n");
        }
        for src in [deep_brackets, deep_blocks] {
            let tree = parse("deep.cr", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics
                    .iter()
                    .any(|d| d.code == "crystal.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "def f\n  x = (1, 2\n",     // unterminated paren + body
            "λ = \"☃\"  # unicode\n",   // multi-byte identifiers/strings
            "",                         // empty file
            "\n\n   \n# trailing\n",    // only blanks and comments
            "end\nclass C\nend\n",      // a stray leading `end`
            "x = <<-SQL\n  select 1\n", // unterminated heredoc
            "c = 'x'\nd = 'oops\n",     // a char + an unterminated char
        ] {
            let tree = parse("edge.cr", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }

    #[test]
    fn output_is_deterministic() {
        let src = "class C < B\n  def m\n    helper\n  end\nend\n\ndef helper\nend\n";
        let a = parse("m.cr", src);
        let b = parse("m.cr", src);
        assert_eq!(a.root, b.root, "parse output must be identical across runs");
    }
}
