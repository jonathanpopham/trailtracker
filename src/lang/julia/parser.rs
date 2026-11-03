//! Julia parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Lua parser (Julia is likewise `keyword … end`
//! delimited, not whitespace-significant): definition *headers* are parsed
//! precisely — we always know a `function`'s signature, a `struct`'s name and
//! supertype, a `module`'s name — while expression regions and bodies are
//! captured as balanced token-tree groups (`Paren`/`Bracket`/`Brace`) plus flat
//! tokens, which is perfectly lossless. Graph facts (calls, type uses, imports)
//! are extracted from these real tokens in the lowering pass, never invented.
//!
//! Julia blocks open with a keyword and close with `end`:
//! `function … end`, `macro … end`, `struct`/`mutable struct … end`,
//! `abstract type … end`, `primitive type … end`, `module`/`baremodule … end`,
//! `begin … end`, `quote … end`, `let … end`, `if … [elseif/else] … end`,
//! `for … end`, `while … end`, `try … [catch/else/finally] … end`, and the
//! call-trailing `… do args … end`. Statements are normally newline-separated
//! (the `;` separator is optional), so — as in the Lua parser — a documented
//! soft-newline heuristic delimits expression/assignment statements.
//!
//! Anything unrecognized still lands in the tree as its exact tokens, so the
//! result always round-trips. Recursion is depth-guarded at [`MAX_DEPTH`]
//! against hostile nesting (deep keyword blocks *or* deep brackets) — a
//! `catch_unwind` cannot catch a stack overflow, so the guard is the real
//! defense.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::julia::lexer::{kind as tk, lex};

/// CST node-kind labels. The lowering interprets these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const FUNCTION: &str = "Function";
    pub const MACRO_DEF: &str = "MacroDef";
    pub const STRUCT: &str = "Struct";
    pub const ABSTRACT_TYPE: &str = "AbstractType";
    pub const PRIMITIVE_TYPE: &str = "PrimitiveType";
    pub const MODULE: &str = "Module";
    pub const IMPORT: &str = "Import";
    pub const EXPORT: &str = "Export";
    pub const CONST: &str = "Const";
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
/// remainder as a flat run. Mirrors the Rust/Lua/Python guard exactly.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = JuliaParser {
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

struct JuliaParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

/// The last significant element consumed in an expression run, used by the
/// statement-boundary and inline-block heuristics.
enum Last {
    None,
    Group,
    Tok(String),
}

impl<'s> JuliaParser<'s> {
    // --- cursor primitives --------------------------------------------------

    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading trivia tokens (whitespace, newlines, comments)
    /// into `out`.
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

    /// True if a newline appears in the trivia before the next significant token.
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
                code: "julia.missing_keyword",
                message: format!("expected '{kw}'"),
                span: ByteSpan::empty_at(self.cur_offset()),
            });
        }
    }

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "julia.depth_limit",
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

    /// Parse a block: statements until a block terminator (`end`/`else`/`elseif`/
    /// `catch`/`finally`) or EOF. The terminator is **not** consumed — the caller
    /// owns it. Depth-guarded.
    fn parse_block(&mut self) -> Node {
        if self.depth >= MAX_DEPTH {
            let mut c = Vec::new();
            self.consume_block_flat(&mut c);
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
    fn consume_block_flat(&mut self, out: &mut Vec<Child>) {
        loop {
            match self.peek_text() {
                None => {
                    self.flush(out);
                    break;
                }
                Some(t) if is_block_terminator(t) => break,
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
            Some("function") => self.finish_function(node::FUNCTION),
            Some("macro") => self.finish_function(node::MACRO_DEF),
            Some("mutable") if self.peek_n_text(1) == Some("struct") => self.finish_struct(),
            Some("struct") => self.finish_struct(),
            Some("abstract") if self.peek_n_text(1) == Some("type") => {
                self.finish_type_decl(node::ABSTRACT_TYPE)
            }
            Some("primitive") if self.peek_n_text(1) == Some("type") => {
                self.finish_type_decl(node::PRIMITIVE_TYPE)
            }
            Some("module") | Some("baremodule") => self.finish_module(),
            Some("const") => self.finish_const(),
            Some("using") | Some("import") => self.finish_import(),
            Some("export") => self.finish_export(),
            Some("if") => self.finish_if(),
            Some("for") => self.finish_for_while(),
            Some("while") => self.finish_for_while(),
            Some("begin") | Some("quote") => self.finish_begin(),
            Some("let") => self.finish_let(),
            Some("try") => self.finish_try(),
            Some("return") | Some("break") | Some("continue") | Some("global") | Some("local") => {
                self.finish_keyword_stmt()
            }
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

    /// `function sig … end` (long form) / `macro name(args) … end`. The header is
    /// the signature line; the body runs to the matching `end`.
    fn finish_function(&mut self, label: &'static str) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // function / macro
        if let Some(h) = self.header() {
            c.push(Child::Node(h));
        }
        c.push(Child::Node(self.parse_block()));
        self.eat_keyword(&mut c, "end");
        self.make_node(label, c)
    }

    /// `[mutable] struct Name[<: Super] … fields … end`.
    fn finish_struct(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        if self.at("mutable") {
            self.eat(&mut c);
        }
        self.eat_keyword(&mut c, "struct");
        if let Some(h) = self.header() {
            c.push(Child::Node(h));
        }
        c.push(Child::Node(self.parse_block()));
        self.eat_keyword(&mut c, "end");
        self.make_node(node::STRUCT, c)
    }

    /// `abstract type Name[<: Super] end` / `primitive type Name[<: Super] bits end`.
    /// There is no statement body — everything between the keywords and `end` is
    /// the header.
    fn finish_type_decl(&mut self, label: &'static str) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // abstract / primitive
        self.eat_keyword(&mut c, "type");
        // Collect the header up to `end` (it may include `<: Super` and, for
        // primitive types, a bit-width literal). Stop at the block terminator.
        let mut h = Vec::new();
        self.collect_expr_run(&mut h, false, &[]);
        if !h.is_empty() {
            c.push(Child::Node(self.make_node(node::HEADER, h)));
        }
        self.eat_keyword(&mut c, "end");
        self.make_node(label, c)
    }

    /// `[bare]module Name … items … end`.
    fn finish_module(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // module / baremodule
        self.ws(&mut c);
        if self.peek_kind() == Some(tk::IDENT) {
            c.push(Child::Node(self.name_node()));
        }
        c.push(Child::Node(self.parse_block()));
        self.eat_keyword(&mut c, "end");
        self.make_node(node::MODULE, c)
    }

    /// `const NAME = expr`.
    fn finish_const(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // const
                          // `global`/`local` can follow `const`.
        self.ws(&mut c);
        if self.at("global") || self.at("local") {
            self.eat(&mut c);
        }
        self.collect_expr_run(&mut c, true, &[]);
        self.make_node(node::CONST, c)
    }

    /// `using X[.Y][: a, b]` / `import X[.Y][: a, b]`.
    fn finish_import(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // using / import
        self.collect_expr_run(&mut c, true, &[]);
        self.make_node(node::IMPORT, c)
    }

    /// `export a, b, c`.
    fn finish_export(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // export
        self.collect_expr_run(&mut c, true, &[]);
        self.make_node(node::EXPORT, c)
    }

    /// `if cond … [elseif cond …] [else …] end`.
    fn finish_if(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // if
        if let Some(h) = self.header() {
            c.push(Child::Node(h));
        }
        c.push(Child::Node(self.parse_block()));
        loop {
            self.ws(&mut c);
            match self.peek_text() {
                Some("elseif") => {
                    self.eat(&mut c);
                    if let Some(h) = self.header() {
                        c.push(Child::Node(h));
                    }
                    c.push(Child::Node(self.parse_block()));
                }
                Some("else") => {
                    self.eat(&mut c);
                    c.push(Child::Node(self.parse_block()));
                }
                _ => break,
            }
        }
        self.eat_keyword(&mut c, "end");
        self.make_node(node::CONTROL, c)
    }

    /// `for itr … end` / `while cond … end`.
    fn finish_for_while(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // for / while
        if let Some(h) = self.header() {
            c.push(Child::Node(h));
        }
        c.push(Child::Node(self.parse_block()));
        self.eat_keyword(&mut c, "end");
        self.make_node(node::CONTROL, c)
    }

    /// `begin … end` / `quote … end`.
    fn finish_begin(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // begin / quote
        c.push(Child::Node(self.parse_block()));
        self.eat_keyword(&mut c, "end");
        self.make_node(node::CONTROL, c)
    }

    /// `let [bindings] … end`.
    fn finish_let(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // let
        if let Some(h) = self.header() {
            c.push(Child::Node(h));
        }
        c.push(Child::Node(self.parse_block()));
        self.eat_keyword(&mut c, "end");
        self.make_node(node::CONTROL, c)
    }

    /// `try … [catch [e]] … [else …] [finally …] end`.
    fn finish_try(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // try
        c.push(Child::Node(self.parse_block()));
        loop {
            self.ws(&mut c);
            match self.peek_text() {
                Some("catch") => {
                    self.eat(&mut c);
                    // Optional exception variable on the same line.
                    if let Some(h) = self.header() {
                        c.push(Child::Node(h));
                    }
                    c.push(Child::Node(self.parse_block()));
                }
                Some("else") | Some("finally") => {
                    self.eat(&mut c);
                    c.push(Child::Node(self.parse_block()));
                }
                _ => break,
            }
        }
        self.eat_keyword(&mut c, "end");
        self.make_node(node::CONTROL, c)
    }

    /// `return [expr]` / `break` / `continue` / `global …` / `local …`.
    fn finish_keyword_stmt(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // the keyword
        self.collect_expr_run(&mut c, true, &[]);
        self.make_node(node::SIMPLE_STMT, c)
    }

    /// A lone `;` separator.
    fn finish_semi(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // ;
        self.make_node(node::SIMPLE_STMT, c)
    }

    /// An expression / assignment statement (a call, an assignment, or a
    /// short-form function definition `f(x) = …`), delimited by the boundary
    /// heuristic. Always consumes at least one token so the parse loop advances.
    fn finish_simple(&mut self) -> Node {
        let mut c = Vec::new();
        self.collect_expr_run(&mut c, true, &[]);
        if c.is_empty() {
            // Guarantee progress (e.g. a stray block-opener at statement start).
            self.ws(&mut c);
            self.eat(&mut c);
        }
        self.make_node(node::SIMPLE_STMT, c)
    }

    // --- names & headers ----------------------------------------------------

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // identifier (cursor at it after caller ws)
        self.make_node(node::NAME, c)
    }

    /// Collect a control/definition header: the expression between an opening
    /// keyword and the block body (which begins at a newline or `;`). Returns
    /// `None` when the region is empty.
    fn header(&mut self) -> Option<Node> {
        let mut c = Vec::new();
        self.collect_expr_run(&mut c, true, &[]);
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(node::HEADER, c))
        }
    }

    // --- expression regions -------------------------------------------------

    /// Collect an expression run into `out`. Stops (without consuming) at a block
    /// terminator or a hard statement-introducing keyword; consumes and stops at
    /// a `;`. When `soft_newline` is set, also stops at a newline that is not an
    /// obvious expression continuation. A block-opening keyword (`if`, `for`,
    /// `do`, `begin`, …) is parsed inline as its construct when the surrounding
    /// expression demands an operand (or for `do`, which always trails a call),
    /// otherwise it ends the run as the start of a new statement. Balanced
    /// `()`/`[]`/`{}` groups are descended into as `Paren`/`Bracket`/`Brace`.
    fn collect_expr_run(
        &mut self,
        out: &mut Vec<Child>,
        soft_newline: bool,
        header_stops: &[&str],
    ) {
        let mut last = Last::None;
        loop {
            let newline_ahead = self.newline_before_next();
            let txt = match self.peek_text() {
                None => {
                    self.flush(out);
                    break;
                }
                Some(t) => t,
            };
            if header_stops.contains(&txt) || is_block_terminator(txt) {
                break;
            }
            if txt == ";" {
                self.ws(out);
                self.eat(out);
                break;
            }
            if is_block_open_kw(txt) {
                if txt == "do" || continues_after(&last) {
                    let construct = self.parse_block_construct();
                    out.push(Child::Node(construct));
                    last = Last::Group;
                    continue;
                } else {
                    break; // a new block statement
                }
            }
            if is_hard_stmt_keyword(txt) {
                break;
            }
            if soft_newline
                && newline_ahead
                && !matches!(last, Last::None)
                && !continues_after(&last)
                && !continues_before(txt)
            {
                break;
            }
            if is_open_delim(txt) {
                self.ws(out);
                let g = self.parse_delimited();
                out.push(Child::Node(g));
                last = Last::Group;
            } else {
                let owned = txt.to_string();
                self.ws(out);
                self.eat(out);
                last = Last::Tok(owned);
            }
        }
    }

    /// Parse the block construct at the cursor, reusing the statement finishers.
    /// Used both at statement level and inline in expression position.
    fn parse_block_construct(&mut self) -> Node {
        if self.depth >= MAX_DEPTH {
            // At the cap, swallow the construct as a flat run up to a matching
            // `end` rather than recursing further.
            let mut c = Vec::new();
            self.ws(&mut c);
            self.eat(&mut c); // opening keyword
            self.consume_block_flat(&mut c);
            self.ws(&mut c);
            if self.at("end") {
                self.eat(&mut c);
            }
            self.note_depth_limit();
            return self.make_node(node::CONTROL, c);
        }
        self.depth += 1;
        let node = match self.peek_text() {
            Some("function") => self.finish_function(node::FUNCTION),
            Some("macro") => self.finish_function(node::MACRO_DEF),
            Some("if") => self.finish_if(),
            Some("for") | Some("while") => self.finish_for_while(),
            Some("begin") | Some("quote") => self.finish_begin(),
            Some("let") => self.finish_let(),
            Some("try") => self.finish_try(),
            Some("do") => self.finish_do(),
            _ => {
                // Defensive: shouldn't happen (caller checked is_block_open_kw).
                let mut c = Vec::new();
                self.eat(&mut c);
                self.make_node(node::ERROR_STMT, c)
            }
        };
        self.depth -= 1;
        node
    }

    /// `… do [args] … end` — the call-trailing anonymous-function block. The
    /// optional argument list lives on the same physical line as `do`; it is kept
    /// as flat tokens (not a `HEADER`) so the lowering reads the do-block as an
    /// anonymous function rather than naming it after its first parameter.
    fn finish_do(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // do
        self.collect_do_args(&mut c);
        c.push(Child::Node(self.parse_block()));
        self.eat_keyword(&mut c, "end");
        self.make_node(node::FUNCTION, c)
    }

    /// Collect a do-block's same-line argument list, stopping at the first
    /// newline (or `;`) so a no-arg `do\n …` does not swallow its body.
    fn collect_do_args(&mut self, out: &mut Vec<Child>) {
        loop {
            if self.newline_before_next() {
                break;
            }
            match self.peek_text() {
                None => break,
                Some(t) if is_block_terminator(t) => break,
                Some(";") => {
                    self.ws(out);
                    self.eat(out);
                    break;
                }
                Some(t) if is_open_delim(t) => {
                    self.ws(out);
                    let g = self.parse_delimited();
                    out.push(Child::Node(g));
                }
                Some(_) => {
                    self.ws(out);
                    self.eat(out);
                }
            }
        }
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`. Newlines
    /// inside are ordinary trivia. Block keywords *inside* a delimiter are NOT
    /// parsed as `… end` blocks: in this position `for`/`if` are comprehension /
    /// generator syntax with no `end`, and a nested anonymous `function … end`
    /// (or `begin … end`) is balanced by its own `end` token regardless — so all
    /// keywords are kept as ordinary flat tokens and only nested delimiter groups
    /// recurse. This stays lossless and avoids swallowing past the closer. (The
    /// trade-off: an anonymous `function` argument does not become its own CST
    /// node — calls inside it are still scanned, since the tokens stay in-group.)
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
    matches!(t, "end" | "else" | "elseif" | "catch" | "finally")
}

/// Keywords that open a `… end` block and may appear inline in expression
/// position (Julia treats these as expressions).
fn is_block_open_kw(t: &str) -> bool {
    matches!(
        t,
        "if" | "for" | "while" | "begin" | "quote" | "let" | "try" | "function" | "macro" | "do"
    )
}

/// Keywords that can only begin a statement (never continue an expression), so
/// they end an expression run.
fn is_hard_stmt_keyword(t: &str) -> bool {
    matches!(
        t,
        "const"
            | "using"
            | "import"
            | "export"
            | "module"
            | "baremodule"
            | "struct"
            | "mutable"
            | "abstract"
            | "primitive"
            | "return"
            | "break"
            | "continue"
            | "global"
            | "local"
    )
}

fn is_open_delim(t: &str) -> bool {
    matches!(t, "(" | "[" | "{")
}

/// True when the most recently consumed element demands a right-hand operand, so
/// the expression must continue across a newline.
fn continues_after(last: &Last) -> bool {
    match last {
        Last::None | Last::Group => false,
        Last::Tok(text) => is_binary_operator(text) || matches!(text.as_str(), "where" | "in"),
    }
}

/// True when the next token continues the preceding expression (a binary
/// operator, a field/parameter access, or a call/index opener), so a newline
/// before it is not a statement boundary.
fn continues_before(text: &str) -> bool {
    is_binary_operator(text) || matches!(text, "where" | "(" | "[" | "{" | "." | "?" | ":")
}

/// A pragmatic set of Julia binary/assignment operators that expect a following
/// operand. Broadcast `.`-prefixed forms are included.
fn is_binary_operator(text: &str) -> bool {
    matches!(
        text,
        "+" | "-"
            | "*"
            | "/"
            | "\\"
            | "^"
            | "%"
            | "&"
            | "|"
            | "~"
            | "<<"
            | ">>"
            | ">>>"
            | "//"
            | ".."
            | "="
            | "=="
            | "==="
            | "!="
            | "!=="
            | "<"
            | ">"
            | "<="
            | ">="
            | "<:"
            | ">:"
            | "::"
            | "&&"
            | "||"
            | "->"
            | "=>"
            | ","
            | "+="
            | "-="
            | "*="
            | "/="
            | "^="
            | "%="
            | ".+"
            | ".-"
            | ".*"
            | "./"
            | ".^"
            | ".="
            | ".=="
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
module Geometry

using LinearAlgebra
import Base: show

abstract type Shape end

struct Circle <: Shape
    radius::Float64
end

const PI = 3.14159

function area(c::Circle)
    return PI * c.radius ^ 2
end

scale(c::Circle, k) = Circle(c.radius * k)

function describe(c::Circle)
    a = area(c)
    if a > 10
        println(\"big\")
    else
        println(\"small\")
    end
end

end
";
        let tree = parse("geometry.jl", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src =
            "function f()\nend\n\nstruct S\n  x::Int\nend\n\nabstract type T end\n\nconst K = 1\n";
        let tree = parse("t.jl", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::FUNCTION), "function: {kinds:?}");
        assert!(kinds.contains(&node::STRUCT), "struct: {kinds:?}");
        assert!(kinds.contains(&node::ABSTRACT_TYPE), "abstract: {kinds:?}");
        assert!(kinds.contains(&node::CONST), "const: {kinds:?}");
    }

    #[test]
    fn module_holds_nested_items() {
        let src = "module M\nfunction inner()\nend\nend\n";
        let tree = parse("m.jl", src);
        let has_inner = tree.root.walk().any(|n| n.kind == node::FUNCTION);
        assert!(has_inner, "nested fn should be a Function node");
    }

    #[test]
    fn statements_separated_by_newline() {
        let src = "println(1)\nprintln(2)\n";
        let tree = parse("t.jl", src);
        let stmts = tree.root.children_of(node::SIMPLE_STMT).count();
        assert_eq!(stmts, 2, "newline should separate the two call statements");
    }

    #[test]
    fn multiline_expression_stays_one_statement() {
        // A trailing binary operator continues the expression across the newline.
        let src = "x = a +\n    b\nprintln(x)\n";
        let tree = parse("t.jl", src);
        let simples = tree.root.children_of(node::SIMPLE_STMT).count();
        assert_eq!(simples, 2, "x = a + b, then println(x)");
    }

    #[test]
    fn control_blocks_round_trip() {
        let src = "for i in 1:10\n  while i > 0\n    i -= 1\n  end\nend\ntry\n  f()\ncatch e\n  g()\nfinally\n  h()\nend\n";
        let tree = parse("t.jl", src);
        assert!(tree.is_lossless());
        assert!(tree.root.children_of(node::CONTROL).count() >= 2);
    }

    #[test]
    fn do_block_round_trips() {
        let src = "map(xs) do x\n  x + 1\nend\n";
        let tree = parse("t.jl", src);
        assert!(tree.is_lossless());
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let deep_brackets = format!("x = {}{}\n", "(".repeat(10_000), ")".repeat(10_000));
        let mut deep_blocks = String::new();
        for _ in 0..2_000 {
            deep_blocks.push_str("begin ");
        }
        for _ in 0..2_000 {
            deep_blocks.push_str("end ");
        }
        deep_blocks.push('\n');
        for src in [deep_brackets, deep_blocks] {
            let tree = parse("deep.jl", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics
                    .iter()
                    .any(|d| d.code == "julia.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "x = (1, 2\n",             // unterminated paren
            "s = \"unterminated\n",    // unterminated string
            "α = '☃'  # unicode\n",    // multi-byte identifiers/chars
            "",                        // empty file
            "\n\n   \n# trailing\n",   // only blanks and comments
            "s = \"\"\"open triple\n", // unterminated triple string
            "function f(\n",           // unterminated signature
        ] {
            let tree = parse("edge.jl", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
