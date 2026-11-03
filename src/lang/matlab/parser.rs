//! MATLAB parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Julia and Lua parsers (MATLAB is likewise
//! `keyword … end` delimited, not whitespace-significant): definition *headers*
//! are parsed precisely — we always recover a `function`'s signature, a
//! `classdef`'s name and superclasses, a member block's attributes — while
//! expression regions and bodies are captured as balanced token-tree groups
//! (`Paren`/`Bracket`/`Brace`) plus flat tokens, which is perfectly lossless.
//! Graph facts (calls, imports, members) are extracted from these real tokens in
//! the lowering pass, never invented.
//!
//! MATLAB blocks open with a keyword and close with `end`:
//! `function … [end]`, `classdef … end`, `properties`/`methods`/`events`/
//! `enumeration … end`, `if … [elseif/else] … end`, `switch … case/otherwise …
//! end`, `for`/`parfor … end`, `while … end`, `try … [catch] … end`, and
//! `spmd … end`. Statements are newline- or `;`-separated; a real newline ends a
//! statement (MATLAB has no trailing-operator line continuation — only the `...`
//! token, which the lexer folds into trivia, joins physical lines).
//!
//! ## The optional `function … end`
//!
//! In a *script* or a classic *function file*, a top-level `function` may have no
//! matching `end` (each function then runs to the next `function` or EOF); in
//! modern files and inside `classdef`, every `function` is `end`-terminated. We
//! handle both: a function body is parsed until its own `end` **or** the next
//! `function` keyword (whichever comes first); the `end` is consumed only when
//! actually present. The honest trade-off (documented): a genuinely *nested*
//! function inside an `end`-terminated parent is flattened to a sibling rather
//! than nested, because we cannot know the file's end-mode without unbounded
//! lookahead. This never loses bytes — the tree still round-trips — it only
//! affects nesting depth, which the lowering treats as a scope hint.
//!
//! Anything unrecognized still lands in the tree as its exact tokens, so the
//! result always round-trips. Recursion is depth-guarded at [`MAX_DEPTH`]
//! against hostile nesting (deep keyword blocks *or* deep brackets) — a
//! `catch_unwind` cannot catch a stack overflow, so the guard is the real
//! defense.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::matlab::lexer::{kind as tk, lex};

/// CST node-kind labels. The lowering interprets these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const FUNCTION: &str = "Function";
    pub const CLASSDEF: &str = "ClassDef";
    pub const PROPERTIES: &str = "Properties";
    pub const METHODS: &str = "Methods";
    pub const EVENTS: &str = "Events";
    pub const ENUMERATION: &str = "Enumeration";
    pub const IMPORT: &str = "Import";
    pub const CONTROL: &str = "Control";
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
/// remainder as a flat run. Mirrors the Rust/Julia/Lua/Python guard exactly.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = MatlabParser {
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

struct MatlabParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> MatlabParser<'s> {
    // --- cursor primitives --------------------------------------------------

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

    /// Eat every remaining token (flush trailing trivia at end of input).
    fn flush(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() {
            self.eat(out);
        }
    }

    fn peek_n_text(&self, n: usize) -> Option<&str> {
        let mut count = 0;
        for t in &self.toks[self.i..] {
            if t.trivia {
                continue;
            }
            if count == n {
                return Some(t.span.text(self.src));
            }
            count += 1;
        }
        None
    }

    fn peek_text(&self) -> Option<&str> {
        self.peek_n_text(0)
    }

    fn at(&self, s: &str) -> bool {
        self.peek_text() == Some(s)
    }

    /// True if a real newline appears in the trivia before the next significant
    /// token. A `...` continuation is trivia but **not** a newline, so it does
    /// not count — the statement continues across it.
    fn newline_before_next(&self) -> bool {
        for t in &self.toks[self.i..] {
            if !t.trivia {
                return false;
            }
            if t.kind == tk::NEWLINE {
                return true;
            }
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

    /// `ws` then consume `kw` if present; otherwise record a recoverable
    /// diagnostic and leave the cursor in place (bytes are never dropped — the
    /// surrounding context consumes them).
    fn eat_keyword(&mut self, out: &mut Vec<Child>, kw: &'static str) {
        self.ws(out);
        if self.at(kw) {
            self.eat(out);
        } else {
            self.diags.push(Diagnostic {
                code: "matlab.missing_keyword",
                message: format!("expected '{kw}'"),
                span: ByteSpan::empty_at(self.cur_offset()),
            });
        }
    }

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "matlab.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; region flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }

    // --- top level ----------------------------------------------------------

    fn parse_source_file(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            match self.peek_text() {
                None => {
                    self.flush(&mut c);
                    break;
                }
                Some(t) if is_block_terminator(t) => {
                    // A stray terminator at top level: consume it as an error
                    // statement so the loop makes progress and nothing is dropped.
                    let mut ec = Vec::new();
                    self.ws(&mut ec);
                    self.eat(&mut ec);
                    c.push(Child::Node(self.make_node(node::ERROR_STMT, ec)));
                }
                _ => {
                    let s = self.parse_statement();
                    c.push(Child::Node(s));
                }
            }
        }
        self.make_node(node::SOURCE_FILE, c)
    }

    /// Parse a block: statements until a block terminator or EOF (the terminator
    /// is **not** consumed — the caller owns it). When `stop_at_function` is set,
    /// a `function` keyword also ends the block (used for function bodies so a
    /// no-`end` function does not swallow its successors). Depth-guarded.
    fn parse_block(&mut self, stop_at_function: bool) -> Node {
        if self.depth >= MAX_DEPTH {
            let mut c = Vec::new();
            self.consume_block_flat(&mut c, stop_at_function);
            self.note_depth_limit();
            return self.make_node(node::BLOCK, c);
        }
        self.depth += 1;
        let mut c = Vec::new();
        loop {
            match self.peek_text() {
                None => {
                    self.flush(&mut c);
                    break;
                }
                Some(t) if is_block_terminator(t) => break,
                Some("function") if stop_at_function => break,
                _ => {
                    let s = self.parse_statement();
                    c.push(Child::Node(s));
                }
            }
        }
        let block = self.make_node(node::BLOCK, c);
        self.depth -= 1;
        block
    }

    /// At the depth cap, swallow a block as a flat token run (no recursion).
    fn consume_block_flat(&mut self, out: &mut Vec<Child>, stop_at_function: bool) {
        loop {
            match self.peek_text() {
                None => {
                    self.flush(out);
                    break;
                }
                Some(t) if is_block_terminator(t) => break,
                Some("function") if stop_at_function => break,
                _ => {
                    self.ws(out);
                    self.eat(out);
                }
            }
        }
    }

    // --- statements ---------------------------------------------------------

    fn parse_statement(&mut self) -> Node {
        match self.peek_text() {
            Some("function") => self.finish_function(),
            Some("classdef") => self.finish_classdef(),
            Some("if") => self.finish_if(),
            Some("switch") => self.finish_switch(),
            Some("for") | Some("parfor") => self.finish_for_while(),
            Some("while") => self.finish_for_while(),
            Some("try") => self.finish_try(),
            Some("spmd") => self.finish_spmd(),
            Some("import") => self.finish_import(),
            Some("return") | Some("break") | Some("continue") | Some("global")
            | Some("persistent") => self.finish_keyword_stmt(),
            Some(";") => self.finish_semi(),
            Some(_) => self.finish_simple(),
            None => {
                // Defensive: the loops guard against this, but guarantee progress.
                let mut c = Vec::new();
                self.eat(&mut c);
                self.make_node(node::ERROR_STMT, c)
            }
        }
    }

    /// `function [outs =] name(args) … [end]`. The header is the signature line;
    /// the body runs to the matching `end` or the next `function`.
    fn finish_function(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // function
        if let Some(h) = self.header() {
            c.push(Child::Node(h));
        }
        c.push(Child::Node(self.parse_block(true)));
        // The `end` is optional (script / classic function-file form).
        self.ws(&mut c);
        if self.at("end") {
            self.eat(&mut c);
        }
        self.make_node(node::FUNCTION, c)
    }

    /// `classdef [(attrs)] Name [< Super1 & Super2] … members … end`.
    fn finish_classdef(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // classdef
        if let Some(h) = self.header() {
            c.push(Child::Node(h));
        }
        c.push(Child::Node(self.parse_class_body()));
        self.eat_keyword(&mut c, "end");
        self.make_node(node::CLASSDEF, c)
    }

    /// The body of a `classdef`: a sequence of member blocks
    /// (`properties`/`methods`/`events`/`enumeration`) interleaved with anything
    /// else (kept as simple statements). `properties` and friends are only
    /// keywords in this context, so outside a `classdef` they stay ordinary
    /// identifiers (e.g. a `methods = …` assignment).
    fn parse_class_body(&mut self) -> Node {
        if self.depth >= MAX_DEPTH {
            let mut c = Vec::new();
            self.consume_block_flat(&mut c, false);
            self.note_depth_limit();
            return self.make_node(node::BLOCK, c);
        }
        self.depth += 1;
        let mut c = Vec::new();
        loop {
            match self.peek_text() {
                None => {
                    self.flush(&mut c);
                    break;
                }
                Some(t) if is_block_terminator(t) => break,
                Some("properties") => c.push(Child::Node(self.finish_member_block(node::PROPERTIES))),
                Some("methods") => c.push(Child::Node(self.finish_member_block(node::METHODS))),
                Some("events") => c.push(Child::Node(self.finish_member_block(node::EVENTS))),
                Some("enumeration") => {
                    c.push(Child::Node(self.finish_member_block(node::ENUMERATION)))
                }
                _ => c.push(Child::Node(self.parse_statement())),
            }
        }
        let block = self.make_node(node::BLOCK, c);
        self.depth -= 1;
        block
    }

    /// `properties`/`methods`/`events`/`enumeration [(attrs)] … end`.
    fn finish_member_block(&mut self, label: &'static str) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // the member keyword
                          // Optional `(attrs)` and rest of the declaration line.
        if let Some(h) = self.header() {
            c.push(Child::Node(h));
        }
        c.push(Child::Node(self.parse_block(false)));
        self.eat_keyword(&mut c, "end");
        self.make_node(label, c)
    }

    /// `if cond … [elseif cond …] [else …] end`.
    fn finish_if(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // if
        if let Some(h) = self.header() {
            c.push(Child::Node(h));
        }
        c.push(Child::Node(self.parse_block(false)));
        loop {
            self.ws(&mut c);
            match self.peek_text() {
                Some("elseif") => {
                    self.eat(&mut c);
                    if let Some(h) = self.header() {
                        c.push(Child::Node(h));
                    }
                    c.push(Child::Node(self.parse_block(false)));
                }
                Some("else") => {
                    self.eat(&mut c);
                    c.push(Child::Node(self.parse_block(false)));
                }
                _ => break,
            }
        }
        self.eat_keyword(&mut c, "end");
        self.make_node(node::CONTROL, c)
    }

    /// `switch expr [case c …] [otherwise …] end`.
    fn finish_switch(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // switch
        if let Some(h) = self.header() {
            c.push(Child::Node(h));
        }
        // Absorb any stray content before the first case (normally only trivia).
        c.push(Child::Node(self.parse_block(false)));
        loop {
            self.ws(&mut c);
            match self.peek_text() {
                Some("case") => {
                    self.eat(&mut c);
                    if let Some(h) = self.header() {
                        c.push(Child::Node(h));
                    }
                    c.push(Child::Node(self.parse_block(false)));
                }
                Some("otherwise") => {
                    self.eat(&mut c);
                    c.push(Child::Node(self.parse_block(false)));
                }
                _ => break,
            }
        }
        self.eat_keyword(&mut c, "end");
        self.make_node(node::CONTROL, c)
    }

    /// `for itr … end` / `parfor itr … end` / `while cond … end`.
    fn finish_for_while(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // for / parfor / while
        if let Some(h) = self.header() {
            c.push(Child::Node(h));
        }
        c.push(Child::Node(self.parse_block(false)));
        self.eat_keyword(&mut c, "end");
        self.make_node(node::CONTROL, c)
    }

    /// `try … [catch [e]] … end` (MATLAB has no `finally`).
    fn finish_try(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // try
        c.push(Child::Node(self.parse_block(false)));
        self.ws(&mut c);
        if self.at("catch") {
            self.eat(&mut c);
            // Optional exception variable on the same line.
            if let Some(h) = self.header() {
                c.push(Child::Node(h));
            }
            c.push(Child::Node(self.parse_block(false)));
        }
        self.eat_keyword(&mut c, "end");
        self.make_node(node::CONTROL, c)
    }

    /// `spmd [(n)] … end`.
    fn finish_spmd(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // spmd
        if let Some(h) = self.header() {
            c.push(Child::Node(h));
        }
        c.push(Child::Node(self.parse_block(false)));
        self.eat_keyword(&mut c, "end");
        self.make_node(node::CONTROL, c)
    }

    /// `import pkg.Fn` / `import pkg.*` (one or more clauses).
    fn finish_import(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // import
        self.collect_expr_run(&mut c, true);
        self.make_node(node::IMPORT, c)
    }

    /// `return` / `break` / `continue` / `global …` / `persistent …`.
    fn finish_keyword_stmt(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // the keyword
        self.collect_expr_run(&mut c, true);
        self.make_node(node::SIMPLE_STMT, c)
    }

    /// A lone `;` separator.
    fn finish_semi(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // ;
        self.make_node(node::SIMPLE_STMT, c)
    }

    /// An expression / assignment / command statement, delimited by the boundary
    /// heuristic. Always consumes at least one token so the parse loop advances.
    fn finish_simple(&mut self) -> Node {
        let mut c = Vec::new();
        self.collect_expr_run(&mut c, true);
        if c.is_empty() {
            // Guarantee progress (e.g. a stray opener at statement start).
            self.ws(&mut c);
            self.eat(&mut c);
        }
        self.make_node(node::SIMPLE_STMT, c)
    }

    // --- names & headers ----------------------------------------------------

    /// Collect a control/definition header: the run between an opening keyword and
    /// the block body (which begins at a real newline or `;`). Returns `None` when
    /// the region is empty.
    fn header(&mut self) -> Option<Node> {
        let mut c = Vec::new();
        self.collect_expr_run(&mut c, true);
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(node::HEADER, c))
        }
    }

    // --- expression regions -------------------------------------------------

    /// Collect an expression run into `out`. Stops (without consuming) at a block
    /// terminator or a statement-introducing keyword; consumes and stops at a
    /// `;`. When `soft_newline` is set, also stops at a real newline (MATLAB
    /// statements end at the newline; `...` continuations are trivia and do not
    /// trigger this). Balanced `()`/`[]`/`{}` groups are descended into as
    /// `Paren`/`Bracket`/`Brace`.
    fn collect_expr_run(&mut self, out: &mut Vec<Child>, soft_newline: bool) {
        let mut started = false;
        loop {
            let newline_ahead = self.newline_before_next();
            let txt = match self.peek_text() {
                None => {
                    self.flush(out);
                    break;
                }
                Some(t) => t,
            };
            if is_block_terminator(txt) || is_block_open_kw(txt) || is_hard_stmt_keyword(txt) {
                break;
            }
            if txt == ";" {
                self.ws(out);
                self.eat(out);
                break;
            }
            if soft_newline && newline_ahead && started {
                break;
            }
            if is_open_delim(txt) {
                self.ws(out);
                let g = self.parse_delimited();
                out.push(Child::Node(g));
            } else {
                self.ws(out);
                self.eat(out);
            }
            started = true;
        }
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`. Newlines
    /// inside are ordinary trivia (so multi-line matrices and continued argument
    /// lists stay one group). Keywords inside a delimiter (e.g. `end` as the last
    /// index in `a(1:end)`) are kept as ordinary flat tokens — they are never
    /// treated as block delimiters here, which keeps the group from swallowing
    /// past its closer. Only nested delimiter groups recurse.
    fn parse_delimited(&mut self) -> Node {
        let mut g = Vec::new();
        self.ws(&mut g);
        let (close, label) = match self.peek_text() {
            Some("(") => (")", node::PAREN),
            Some("[") => ("]", node::BRACKET),
            Some("{") => ("}", node::BRACE),
            _ => return self.make_node(node::ERROR_STMT, g),
        };
        self.eat(&mut g); // opener
        loop {
            self.ws(&mut g);
            match self.peek_text() {
                None => break, // unterminated; still lossless
                Some(t) if t == close => {
                    self.eat(&mut g);
                    break;
                }
                Some("(") | Some("[") | Some("{") => {
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

    /// Iteratively consume a balanced delimiter run (opener already eaten),
    /// appending every token as a flat leaf. Used at the depth cap.
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
}

// --- boundary heuristic helpers ---------------------------------------------

fn is_block_terminator(t: &str) -> bool {
    matches!(t, "end" | "else" | "elseif" | "case" | "otherwise" | "catch")
}

/// Keywords that open a `… end` block at statement level (and thus end an
/// expression run). `properties`/`methods`/`events`/`enumeration` are *not*
/// here: they are only keywords inside a `classdef`, handled by
/// [`MatlabParser::parse_class_body`].
fn is_block_open_kw(t: &str) -> bool {
    matches!(
        t,
        "function" | "classdef" | "if" | "switch" | "for" | "parfor" | "while" | "try" | "spmd"
    )
}

/// Keywords that can only begin a statement (never continue an expression).
fn is_hard_stmt_keyword(t: &str) -> bool {
    matches!(
        t,
        "import" | "return" | "break" | "continue" | "global" | "persistent"
    )
}

fn is_open_delim(t: &str) -> bool {
    matches!(t, "(" | "[" | "{")
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
% a class
classdef Circle < handle
    properties
        radius = 1.0
    end
    methods
        function obj = Circle(r)
            obj.radius = r;
        end
        function a = area(obj)
            a = pi * obj.radius .^ 2;
        end
    end
end
";
        let tree = parse("Circle.m", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "function y = f(x)\n  y = x + 1;\nend\n\nclassdef C\nend\n";
        let tree = parse("t.m", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::FUNCTION), "function: {kinds:?}");
        assert!(kinds.contains(&node::CLASSDEF), "classdef: {kinds:?}");
    }

    #[test]
    fn function_without_end_script_form() {
        // No `end` on either function: they must come out as two siblings.
        let src = "x = 3;\nfunction a = f(n)\n  a = n + 1;\nfunction b = g(n)\n  b = n - 1;\n";
        let tree = parse("script.m", src);
        let fns = tree.root.children_of(node::FUNCTION).count();
        assert_eq!(fns, 2, "two no-end functions should be siblings: {fns}");
        assert!(tree.is_lossless());
    }

    #[test]
    fn function_with_end_siblings() {
        let src = "function main()\n  g();\nend\nfunction g()\nend\n";
        let tree = parse("m.m", src);
        let fns = tree.root.children_of(node::FUNCTION).count();
        assert_eq!(fns, 2);
        assert!(tree.is_lossless());
    }

    #[test]
    fn switch_and_control_round_trip() {
        let src = "switch x\n  case 1\n    y = 1;\n  case 2\n    y = 2;\n  otherwise\n    y = 0;\nend\nfor i = 1:10\n  while i > 0\n    i = i - 1;\n  end\nend\n";
        let tree = parse("t.m", src);
        assert!(tree.is_lossless());
        assert!(tree.root.children_of(node::CONTROL).count() >= 2);
    }

    #[test]
    fn end_as_index_is_not_a_terminator() {
        let src = "function f(a)\n  b = a(1:end);\n  c = a(end);\nend\n";
        let tree = parse("t.m", src);
        assert!(tree.is_lossless());
        // The function's `end` is consumed; the `end` indices stay inside parens.
        let fns = tree.root.children_of(node::FUNCTION).count();
        assert_eq!(fns, 1);
    }

    #[test]
    fn methods_outside_classdef_is_identifier() {
        // `methods` as a variable must not start a member block at top level.
        let src = "methods = 5;\nx = methods + 1;\n";
        let tree = parse("t.m", src);
        assert!(tree.is_lossless());
        let simples = tree.root.children_of(node::SIMPLE_STMT).count();
        assert_eq!(simples, 2, "two assignments, no member block");
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let deep_brackets = format!("x = {}{};\n", "(".repeat(10_000), ")".repeat(10_000));
        let mut deep_blocks = String::new();
        for _ in 0..2_000 {
            deep_blocks.push_str("if x\n");
        }
        for _ in 0..2_000 {
            deep_blocks.push_str("end\n");
        }
        for src in [deep_brackets, deep_blocks] {
            let tree = parse("deep.m", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics
                    .iter()
                    .any(|d| d.code == "matlab.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "x = (1, 2\n",          // unterminated paren
            "s = 'unterminated\n",  // unterminated char array
            "s = \"open\n",         // unterminated string
            "α = 1;  % unicode\n",  // multi-byte identifier
            "",                     // empty file
            "\n\n   \n% trailing\n", // only blanks and comments
            "%{\nopen block\n",     // unterminated block comment
            "function f(\n",        // unterminated signature
        ] {
            let tree = parse("edge.m", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
