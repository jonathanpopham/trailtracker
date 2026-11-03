//! Ada parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Julia and Fortran parsers (Ada is likewise
//! `keyword … end`-delimited and case-insensitive, not whitespace-significant):
//! declaration *headers* are parsed precisely — we always know a subprogram's
//! name and signature, a package's name, a type's name — while executable
//! statement regions and expression bodies are captured as a flat `Block` of
//! balanced token groups (`Paren`/`Bracket`), which is perfectly lossless. Graph
//! facts (calls, type uses, imports) are extracted from these real tokens in the
//! lowering pass, never invented.
//!
//! Ada units open with a keyword and close with `end`:
//! `package [body] X is … end X;`, `procedure P (…) is … begin … end P;`,
//! `function F (…) return T is … begin … end F;`, `type X is …;`,
//! `task`/`protected`/`entry`/`generic`. Declarative parts are parsed as nested
//! item lists so nested definitions stay first-class; the *executable* region
//! after `begin` is captured as a flat balanced run whose end is found with a
//! block-keyword depth counter (`if`/`case`/`loop`/`select`/`begin`/`do` open,
//! `end` closes) — conditional/quantified expressions live inside parens, so the
//! counter never miscounts them.
//!
//! Anything unrecognized still lands in the tree as its exact tokens, so the
//! result always round-trips. Recursion is depth-guarded at [`MAX_DEPTH`] against
//! hostile nesting (deep keyword blocks *or* deep brackets) — a `catch_unwind`
//! cannot catch a stack overflow, so the guard is the real defense.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::ada::lexer::{kind as tk, lex};

/// CST node-kind labels. The lowering interprets these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const WITH_CLAUSE: &str = "WithClause";
    pub const USE_CLAUSE: &str = "UseClause";
    pub const PACKAGE: &str = "Package";
    pub const PROCEDURE: &str = "Procedure";
    pub const FUNCTION: &str = "Function";
    pub const GENERIC: &str = "Generic";
    pub const TASK: &str = "Task";
    pub const PROTECTED: &str = "Protected";
    pub const ENTRY: &str = "Entry";
    pub const TYPE_DECL: &str = "TypeDecl";
    pub const SUBTYPE_DECL: &str = "SubtypeDecl";
    pub const OBJECT_DECL: &str = "ObjectDecl";
    pub const DECL: &str = "Decl";
    pub const ERROR_ITEM: &str = "ErrorItem";

    pub const NAME: &str = "Name";
    pub const SIGNATURE: &str = "Signature";
    pub const HEADER: &str = "Header";
    pub const BLOCK: &str = "Block";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat run. Mirrors the Rust/Julia/Fortran guard exactly.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = AdaParser {
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

struct AdaParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

/// Case-insensitive text equality (Ada keywords are case-insensitive).
fn ci(a: &str, b: &str) -> bool {
    a.eq_ignore_ascii_case(b)
}

impl<'s> AdaParser<'s> {
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

    /// Exact-text match (for punctuation).
    fn at(&self, s: &str) -> bool {
        self.peek_text() == Some(s)
    }

    /// Case-insensitive keyword match.
    fn at_kw(&self, s: &str) -> bool {
        self.peek_text().map(|t| ci(t, s)).unwrap_or(false)
    }

    fn at_ident(&self) -> bool {
        self.peek_kind() == Some(tk::IDENT)
    }

    fn at_open(&self) -> bool {
        self.at("(") || self.at("[")
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

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "ada.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; region flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }

    // --- top level ----------------------------------------------------------

    fn parse_source_file(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            match self.peek_text() {
                None => break,
                Some(t) if ci(t, "begin") || ci(t, "end") || ci(t, "private") => {
                    // A stray separator/terminator at top level: consume one token
                    // as an error item so the loop makes progress, nothing dropped.
                    let mut ec = Vec::new();
                    self.ws(&mut ec);
                    self.eat(&mut ec);
                    c.push(Child::Node(self.make_node(node::ERROR_ITEM, ec)));
                }
                _ => {
                    let item = self.parse_item();
                    c.push(Child::Node(item));
                }
            }
        }
        self.make_node(node::SOURCE_FILE, c)
    }

    // --- items --------------------------------------------------------------

    fn parse_item(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);

        // Leading modifiers that precede the item keyword.
        loop {
            self.ws(&mut c);
            match self.peek_text() {
                Some(t)
                    if ci(t, "overriding")
                        || ci(t, "not")
                        || ci(t, "limited")
                        || ci(t, "synchronized")
                        || ci(t, "private")
                        || ci(t, "tagged") =>
                {
                    self.eat(&mut c);
                }
                Some(t) if ci(t, "separate") => {
                    self.eat(&mut c);
                    self.ws(&mut c);
                    if self.at("(") {
                        let g = self.parse_delimited();
                        c.push(Child::Node(g));
                    }
                }
                _ => break,
            }
        }

        self.ws(&mut c);
        match self.peek_text() {
            None => self.finish_error(c),
            Some(t) => {
                if ci(t, "with") {
                    self.finish_clause(c, node::WITH_CLAUSE)
                } else if ci(t, "use") {
                    self.finish_clause(c, node::USE_CLAUSE)
                } else if ci(t, "package") {
                    self.finish_package(c)
                } else if ci(t, "procedure") {
                    self.finish_subprogram(c, node::PROCEDURE)
                } else if ci(t, "function") {
                    self.finish_subprogram(c, node::FUNCTION)
                } else if ci(t, "generic") {
                    self.finish_generic(c)
                } else if ci(t, "task") {
                    self.finish_task_protected(c, node::TASK)
                } else if ci(t, "protected") {
                    self.finish_task_protected(c, node::PROTECTED)
                } else if ci(t, "entry") {
                    self.finish_entry(c)
                } else if ci(t, "type") {
                    self.finish_type(c)
                } else if ci(t, "subtype") {
                    self.finish_subtype(c)
                } else if ci(t, "pragma") || ci(t, "for") || ci(t, "exception") {
                    self.finish_decl(c)
                } else if self.peek_kind() == Some(tk::IDENT)
                    || self.peek_kind() == Some(tk::STRING)
                {
                    self.finish_object(c)
                } else {
                    self.finish_error(c)
                }
            }
        }
    }

    /// `with A.B.C;` / `use A.B;` — a context / use clause collected to `;`.
    fn finish_clause(&mut self, mut c: Vec<Child>, label: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // with / use
        self.collect_to_semicolon(&mut c);
        self.make_node(label, c)
    }

    /// `pragma …;`, `for X'… use …;`, `E : exception;` and the like.
    fn finish_decl(&mut self, mut c: Vec<Child>) -> Node {
        self.collect_to_semicolon(&mut c);
        self.make_node(node::DECL, c)
    }

    /// An object declaration `Name [, Name]* : [constant] T [:= expr];` (or any
    /// other identifier-introduced declaration), collected to `;`.
    fn finish_object(&mut self, mut c: Vec<Child>) -> Node {
        self.collect_to_semicolon(&mut c);
        self.make_node(node::OBJECT_DECL, c)
    }

    fn finish_error(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        if self.at_open() {
            let g = self.parse_delimited();
            c.push(Child::Node(g));
        } else {
            self.eat(&mut c); // exactly one token guarantees progress
        }
        self.diags.push(Diagnostic {
            code: "ada.unrecognized_item",
            message: "token(s) not recognized as an Ada declaration".to_string(),
            span: children_span(&c).unwrap_or_else(|| ByteSpan::empty_at(self.cur_offset())),
        });
        self.make_node(node::ERROR_ITEM, c)
    }

    /// `package [body] Name is … [private …] [begin …] end Name;`, or a package
    /// instantiation / renaming collected to `;`.
    fn finish_package(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // package
        self.ws(&mut c);
        if self.at_kw("body") {
            self.eat(&mut c);
        }
        c.push(Child::Node(self.name_node()));
        self.ws(&mut c);
        if self.at_kw("is") {
            self.eat(&mut c);
            self.ws(&mut c);
            if self.at_kw("new") {
                self.collect_to_semicolon(&mut c); // instantiation
            } else {
                self.parse_is_body(&mut c);
            }
        } else {
            // `renames` and the generic fallback are both collected to `;`.
            self.collect_to_semicolon(&mut c);
        }
        self.make_node(node::PACKAGE, c)
    }

    /// `procedure P (…) [is …] | renames … | ;` /
    /// `function F (…) return T [is …] | renames … | ;`.
    fn finish_subprogram(&mut self, mut c: Vec<Child>, label: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // procedure / function
        c.push(Child::Node(self.name_node()));
        let mut sig = Vec::new();
        self.collect_until(&mut sig, &["is", "renames"], &[";"]);
        if !sig.is_empty() {
            c.push(Child::Node(self.make_node(node::SIGNATURE, sig)));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c); // spec only
        } else if self.at_kw("renames") {
            self.collect_to_semicolon(&mut c);
        } else if self.at_kw("is") {
            self.eat(&mut c);
            self.ws(&mut c);
            // `is new` (instantiation), `is abstract`/`is null`, `is separate`
            // (stub), or `is (expr)` (expression function) — none open a body.
            if self.at_kw("new")
                || self.at_kw("abstract")
                || self.at_kw("null")
                || self.at_kw("separate")
                || self.at("(")
            {
                self.collect_to_semicolon(&mut c);
            } else {
                self.parse_is_body(&mut c);
            }
        } else {
            self.collect_to_semicolon(&mut c);
        }
        self.make_node(label, c)
    }

    /// The shared `is … [private …] [begin …] end Name;` body, entered with the
    /// cursor just past `is`.
    fn parse_is_body(&mut self, c: &mut Vec<Child>) {
        self.parse_decl_list(c);
        self.ws(c);
        if self.at_kw("private") {
            self.eat(c);
            self.parse_decl_list(c);
        }
        self.ws(c);
        if self.at_kw("begin") {
            self.eat(c);
            let b = self.parse_stmt_region();
            c.push(Child::Node(b));
        }
        self.eat_end_clause(c);
    }

    /// `type Name … ;` — the body (which may contain a `record … end record`
    /// region) is collected as a `Header`.
    fn finish_type(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // type
        c.push(Child::Node(self.name_node()));
        let mut h = Vec::new();
        self.collect_type_body(&mut h);
        if !h.is_empty() {
            c.push(Child::Node(self.make_node(node::HEADER, h)));
        }
        self.make_node(node::TYPE_DECL, c)
    }

    /// Collect a type declaration body up to the terminating `;`, treating a
    /// `record … end record` as a balanced region so the `;` inside the record
    /// component list does not end the declaration. `null record` (no `end`) is
    /// handled by not counting a `record` that immediately follows `null`.
    fn collect_type_body(&mut self, c: &mut Vec<Child>) {
        let mut rec: i32 = 0;
        let mut prev_null = false;
        loop {
            self.ws(c);
            match self.peek_text() {
                None => break,
                Some(";") if rec == 0 => {
                    self.eat(c);
                    break;
                }
                Some("(") | Some("[") => {
                    let g = self.parse_delimited();
                    c.push(Child::Node(g));
                    prev_null = false;
                }
                Some(t) if ci(t, "record") && !prev_null => {
                    rec += 1;
                    self.eat(c);
                    prev_null = false;
                }
                Some(t)
                    if ci(t, "end")
                        && self
                            .peek_n_text(1)
                            .map(|s| ci(s, "record"))
                            .unwrap_or(false) =>
                {
                    rec -= 1;
                    if rec < 0 {
                        rec = 0;
                    }
                    self.eat(c); // end
                    self.ws(c);
                    self.eat(c); // record
                    prev_null = false;
                }
                Some(t) => {
                    prev_null = ci(t, "null");
                    self.eat(c);
                }
            }
        }
    }

    fn finish_subtype(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // subtype
        c.push(Child::Node(self.name_node()));
        self.collect_to_semicolon(&mut c);
        self.make_node(node::SUBTYPE_DECL, c)
    }

    /// `generic <formals> <package|procedure|function spec/body>`.
    fn finish_generic(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // generic
                          // Formal part: declarations until the (bare) generic unit keyword.
        loop {
            self.ws(&mut c);
            match self.peek_text() {
                None => break,
                Some(t)
                    if ci(t, "package")
                        || ci(t, "procedure")
                        || ci(t, "function")
                        || ci(t, "end") =>
                {
                    break
                }
                _ => {
                    let item = self.parse_item();
                    c.push(Child::Node(item));
                }
            }
        }
        self.ws(&mut c);
        if self.at_kw("package") || self.at_kw("procedure") || self.at_kw("function") {
            let unit = self.parse_item();
            c.push(Child::Node(unit));
        }
        self.make_node(node::GENERIC, c)
    }

    /// `task [type] N [is … end N;]` / `task body N is … begin … end N;` and the
    /// matching `protected` forms.
    fn finish_task_protected(&mut self, mut c: Vec<Child>, label: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // task / protected
        self.ws(&mut c);
        if self.at_kw("body") {
            self.eat(&mut c);
        }
        self.ws(&mut c);
        if self.at_kw("type") {
            self.eat(&mut c);
        }
        self.ws(&mut c);
        if self.at_ident() {
            c.push(Child::Node(self.name_node()));
        }
        self.ws(&mut c);
        if self.at_kw("is") {
            self.eat(&mut c);
            self.ws(&mut c);
            if self.at_kw("new") {
                self.collect_to_semicolon(&mut c);
            } else {
                self.parse_is_body(&mut c);
            }
        } else if self.at(";") {
            self.eat(&mut c);
        } else {
            self.collect_to_semicolon(&mut c);
        }
        self.make_node(label, c)
    }

    /// `entry E [(…)] [when …] [is … begin … end E;] | ;`.
    fn finish_entry(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // entry
        c.push(Child::Node(self.name_node()));
        let mut sig = Vec::new();
        self.collect_until(&mut sig, &["is"], &[";"]);
        if !sig.is_empty() {
            c.push(Child::Node(self.make_node(node::SIGNATURE, sig)));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        } else if self.at_kw("is") {
            self.eat(&mut c);
            self.parse_is_body(&mut c);
        } else {
            self.collect_to_semicolon(&mut c);
        }
        self.make_node(node::ENTRY, c)
    }

    // --- names --------------------------------------------------------------

    /// A declared name: a dotted identifier (`Parent.Child`), or an operator
    /// string for `function "+" (…)`.
    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        if self.peek_kind() == Some(tk::STRING) {
            self.eat(&mut c);
        } else if self.at_ident() {
            self.eat(&mut c);
            loop {
                if self.at(".") && self.peek_kind_n(1) == Some(tk::IDENT) {
                    self.ws(&mut c);
                    self.eat(&mut c); // .
                    self.ws(&mut c);
                    self.eat(&mut c); // ident
                } else {
                    break;
                }
            }
        }
        self.make_node(node::NAME, c)
    }

    // --- declarative + statement regions ------------------------------------

    /// Parse a declarative item list, stopping (without consuming) at `begin`,
    /// `end`, or `private`. Depth-guarded.
    fn parse_decl_list(&mut self, out: &mut Vec<Child>) {
        if self.depth >= MAX_DEPTH {
            self.consume_flat_decls(out);
            self.note_depth_limit();
            return;
        }
        self.depth += 1;
        loop {
            self.ws(out);
            match self.peek_text() {
                None => break,
                Some(t) if ci(t, "begin") || ci(t, "end") || ci(t, "private") => break,
                _ => {
                    let item = self.parse_item();
                    out.push(Child::Node(item));
                }
            }
        }
        self.depth -= 1;
    }

    /// At the depth cap, swallow a declarative region as a flat token run.
    fn consume_flat_decls(&mut self, out: &mut Vec<Child>) {
        let mut bal: i32 = 0;
        loop {
            self.ws(out);
            match self.peek_text() {
                None => break,
                Some(t) if bal == 0 && (ci(t, "begin") || ci(t, "end") || ci(t, "private")) => {
                    break
                }
                Some(t) => {
                    if t == "(" || t == "[" {
                        bal += 1;
                    } else if t == ")" || t == "]" {
                        bal -= 1;
                        if bal < 0 {
                            bal = 0;
                        }
                    }
                    self.eat(out);
                }
            }
        }
    }

    /// Capture the executable statement region after `begin` as a flat `Block`,
    /// stopping (without consuming) at the `end` that closes this construct. A
    /// block-keyword depth counter distinguishes that `end` from the `end`s of
    /// nested `if`/`case`/`loop`/`select`/`begin`/`do` constructs. Parenthesised
    /// conditional/quantified expressions are descended into as `Paren` groups,
    /// so their inner keywords never reach the counter.
    fn parse_stmt_region(&mut self) -> Node {
        if self.depth >= MAX_DEPTH {
            let mut c = Vec::new();
            self.consume_flat_stmt(&mut c);
            self.note_depth_limit();
            return self.make_node(node::BLOCK, c);
        }
        self.depth += 1;
        let mut c = Vec::new();
        let mut bd: i32 = 0;
        let mut prev_end = false;
        loop {
            self.ws(&mut c);
            match self.peek_text() {
                None => break,
                Some(t) if bd == 0 && ci(t, "end") => break,
                Some(t) => {
                    if t == "(" || t == "[" {
                        let g = self.parse_delimited();
                        c.push(Child::Node(g));
                        prev_end = false;
                        continue;
                    }
                    let is_end = ci(t, "end");
                    if is_block_open_word(t) && !prev_end {
                        bd += 1;
                    } else if is_end {
                        bd -= 1;
                        if bd < 0 {
                            bd = 0;
                        }
                    }
                    self.eat(&mut c);
                    prev_end = is_end;
                }
            }
        }
        let block = self.make_node(node::BLOCK, c);
        self.depth -= 1;
        block
    }

    /// At the depth cap, swallow a statement region as a flat token run up to the
    /// first `end` at paren depth 0 (degraded but lossless).
    fn consume_flat_stmt(&mut self, out: &mut Vec<Child>) {
        let mut bal: i32 = 0;
        loop {
            self.ws(out);
            match self.peek_text() {
                None => break,
                Some(t) if bal == 0 && ci(t, "end") => break,
                Some(t) => {
                    if t == "(" || t == "[" {
                        bal += 1;
                    } else if t == ")" || t == "]" {
                        bal -= 1;
                        if bal < 0 {
                            bal = 0;
                        }
                    }
                    self.eat(out);
                }
            }
        }
    }

    /// `end [Name];` — eat `end` and the designator up to `;`.
    fn eat_end_clause(&mut self, c: &mut Vec<Child>) {
        self.ws(c);
        if self.at_kw("end") {
            self.eat(c);
            self.collect_to_semicolon(c);
        }
    }

    /// Collect tokens (descending into balanced groups) through the next `;` at
    /// delimiter depth 0, which is consumed.
    fn collect_to_semicolon(&mut self, c: &mut Vec<Child>) {
        loop {
            self.ws(c);
            match self.peek_text() {
                None => break,
                Some(";") => {
                    self.eat(c);
                    break;
                }
                Some("(") | Some("[") => {
                    let g = self.parse_delimited();
                    c.push(Child::Node(g));
                }
                Some(_) => self.eat(c),
            }
        }
    }

    /// Collect tokens (descending into balanced groups) until a stop keyword
    /// (case-insensitive) or stop punctuation appears at delimiter depth 0. The
    /// stop token is not consumed.
    fn collect_until(&mut self, c: &mut Vec<Child>, kws: &[&str], puncts: &[&str]) {
        loop {
            self.ws(c);
            match self.peek_text() {
                None => break,
                Some(t) => {
                    if puncts.contains(&t) || kws.iter().any(|k| ci(t, k)) {
                        break;
                    }
                    if t == "(" || t == "[" {
                        let g = self.parse_delimited();
                        c.push(Child::Node(g));
                    } else {
                        self.eat(c);
                    }
                }
            }
        }
    }

    /// Parse a balanced delimiter group `(...)` or `[...]`. Cursor is at (or
    /// before trivia preceding) the opener. Depth-guarded against deep nesting.
    fn parse_delimited(&mut self) -> Node {
        let mut g = Vec::new();
        self.ws(&mut g);
        let (close, label) = if self.at("(") {
            (")", node::PAREN)
        } else if self.at("[") {
            ("]", node::BRACKET)
        } else {
            return self.make_node(node::ERROR_ITEM, g); // defensive
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
                Some("(") | Some("[") => {
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

    /// Iteratively consume a balanced delimiter run (the opener already eaten),
    /// appending every token as a flat leaf. Used at the depth cap.
    fn consume_balanced_flat(&mut self, out: &mut Vec<Child>) {
        let mut balance: i32 = 1;
        while balance > 0 {
            self.ws(out);
            match self.peek_text() {
                None => break,
                Some("(") | Some("[") => balance += 1,
                Some(")") | Some("]") => balance -= 1,
                _ => {}
            }
            self.eat(out);
        }
    }
}

/// Keywords that open a `… end`-bearing construct *in a statement region* and so
/// raise the block-depth counter (`end` closes one). `declare` and `accept` are
/// deliberately absent: their `end` pairs with the block's `begin` and the
/// accept's `do`, both of which are counted instead.
fn is_block_open_word(t: &str) -> bool {
    ci(t, "if")
        || ci(t, "case")
        || ci(t, "loop")
        || ci(t, "select")
        || ci(t, "begin")
        || ci(t, "do")
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
-- a package
with Ada.Text_IO;
use Ada.Text_IO;

package body Geometry is

   type Shape is (Circle, Square);

   Tau : constant Float := 6.283185;

   function Area (R : Float) return Float is
   begin
      return Tau * R * R / 2.0;
   end Area;

   procedure Describe (R : Float) is
      A : Float := Area (R);
   begin
      if A > 10.0 then
         Put_Line (\"big\");
      else
         Put_Line (\"small\");
      end if;
   end Describe;

end Geometry;
";
        let tree = parse("geometry.adb", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "with X; package P is type T is range 1 .. 10; C : constant T := 1; \
                   procedure Q; end P;";
        let tree = parse("p.ads", src);
        let pkg = tree
            .root
            .child_nodes()
            .find(|n| n.kind == node::PACKAGE)
            .expect("package");
        let kinds: Vec<&str> = pkg.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::TYPE_DECL), "type: {kinds:?}");
        assert!(kinds.contains(&node::OBJECT_DECL), "object: {kinds:?}");
        assert!(kinds.contains(&node::PROCEDURE), "proc: {kinds:?}");
        assert!(tree.root.child_nodes().any(|n| n.kind == node::WITH_CLAUSE));
    }

    #[test]
    fn record_type_with_inner_semicolons() {
        let src = "type Point is record\n   X : Integer;\n   Y : Integer;\nend record;\n";
        let tree = parse("t.ads", src);
        assert!(tree.is_lossless());
        // The whole record is a single type declaration, not split at the ';'s.
        let decls: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert_eq!(decls, vec![node::TYPE_DECL], "got {decls:?}");
    }

    #[test]
    fn nested_subprogram_is_first_class() {
        let src = "procedure Outer is\n   procedure Inner is\n   begin\n      null;\n   \
                   end Inner;\nbegin\n   Inner;\nend Outer;\n";
        let tree = parse("o.adb", src);
        assert!(tree.is_lossless());
        let inner = tree
            .root
            .walk()
            .filter(|n| n.kind == node::PROCEDURE)
            .count();
        assert_eq!(inner, 2, "outer and inner procedures should both be nodes");
    }

    #[test]
    fn control_blocks_round_trip() {
        let src = "procedure P is\nbegin\n   for I in 1 .. 10 loop\n      while I > 0 loop\n         \
                   case I is\n            when 1 => null;\n            when others => null;\n         \
                   end case;\n      end loop;\n   end loop;\nend P;\n";
        let tree = parse("p.adb", src);
        assert!(tree.is_lossless());
        assert_eq!(
            tree.root
                .child_nodes()
                .filter(|n| n.kind == node::PROCEDURE)
                .count(),
            1,
            "the nested control ends must not leak past the procedure"
        );
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        // Deep bracket nesting (exercises the recursive `parse_delimited` guard).
        let deep_parens = format!(
            "X : Integer := {}{};\n",
            "(".repeat(10_000),
            ")".repeat(10_000)
        );
        // Deep nested packages (exercises the recursive `parse_decl_list` guard).
        // Note: nested `if`/`loop` blocks are handled *iteratively* by the
        // block-depth counter, so they never recurse and need no guard.
        let n = 3_000;
        let mut deep_pkgs = String::new();
        for i in 0..n {
            deep_pkgs.push_str(&format!("package P{i} is\n"));
        }
        for i in (0..n).rev() {
            deep_pkgs.push_str(&format!("end P{i};\n"));
        }
        for src in [deep_parens, deep_pkgs] {
            let tree = parse("deep.adb", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics.iter().any(|d| d.code == "ada.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn edge_inputs_round_trip() {
        for src in [
            "",
            "   \n\n  -- only trivia\n",
            "X := (1, 2\n",                          // unterminated paren
            "S : String := \"open\n",                // unterminated string
            "function \"+\" (L, R : T) return T;\n", // operator name
            "package P is end P;\n",
            "procedure P is begin\n", // unterminated body
        ] {
            let tree = parse("edge.adb", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
