//! VHDL parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Ada and Verilog parsers (VHDL is likewise
//! `keyword … end`-delimited and case-insensitive, not whitespace-significant):
//! declaration *headers* are parsed precisely — we always know an entity's name,
//! an architecture's name and the entity it implements, a subprogram's signature,
//! a type's name — while executable statement regions and expression bodies are
//! captured as a flat `Block` of balanced token groups (`Paren`/`Bracket`), which
//! is perfectly lossless. Graph facts (component/entity instantiations, subprogram
//! calls, library/use imports) are extracted from these real tokens in the
//! lowering pass, never invented.
//!
//! VHDL design units open with a keyword and close with `end`:
//! `entity E is … end [entity] [E];`,
//! `architecture A of E is <decls> begin <stmts> end [architecture] [A];`,
//! `package [body] P is <decls> end [package [body]] [P];`,
//! `function F (…) return T is <decls> begin <stmts> end [function] [F];`,
//! `procedure P (…) is … end [procedure] [P];`, `component C is … end component;`,
//! `type X is …;`, `subtype X is …;`, plus `library`/`use`/`context`/
//! `configuration`. Declarative parts are parsed as nested item lists so nested
//! definitions stay first-class; the *executable* region after `begin` is captured
//! as a flat balanced run whose end is found with a block-keyword depth counter
//! (`if`/`case`/`loop`/`generate`/`process`/`block`/`record`/`units`/`protected`/
//! `component`/`configuration` open, `end` closes) — conditional expressions live
//! inside parens, so the counter never miscounts them.
//!
//! Anything unrecognized still lands in the tree as its exact tokens, so the
//! result always round-trips. Recursion is depth-guarded at [`MAX_DEPTH`] against
//! hostile nesting (deep keyword blocks *or* deep brackets) — a `catch_unwind`
//! cannot catch a stack overflow, so the guard is the real defense.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::vhdl::lexer::{kind as tk, lex};

/// CST node-kind labels. The lowering interprets these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const LIBRARY_CLAUSE: &str = "LibraryClause";
    pub const USE_CLAUSE: &str = "UseClause";
    pub const CONTEXT: &str = "Context";
    pub const ENTITY: &str = "Entity";
    pub const ARCHITECTURE: &str = "Architecture";
    pub const PACKAGE: &str = "Package";
    pub const CONFIGURATION: &str = "Configuration";
    pub const FUNCTION: &str = "Function";
    pub const PROCEDURE: &str = "Procedure";
    pub const COMPONENT: &str = "Component";
    pub const TYPE_DECL: &str = "TypeDecl";
    pub const SUBTYPE_DECL: &str = "SubtypeDecl";
    pub const CONSTANT_DECL: &str = "ConstantDecl";
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
/// remainder as a flat run. Mirrors the Rust/Ada/Verilog guard exactly.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = VhdlParser {
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

struct VhdlParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

/// Case-insensitive text equality (VHDL keywords are case-insensitive).
fn ci(a: &str, b: &str) -> bool {
    a.eq_ignore_ascii_case(b)
}

impl<'s> VhdlParser<'s> {
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
            code: "vhdl.depth_limit",
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
                Some(t) if ci(t, "begin") || ci(t, "end") => {
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

        // Leading modifiers that precede the item keyword (`pure`/`impure` before
        // a function, `shared` before a variable, `postponed` before a process).
        loop {
            self.ws(&mut c);
            match self.peek_text() {
                Some(t)
                    if ci(t, "pure")
                        || ci(t, "impure")
                        || ci(t, "shared")
                        || ci(t, "postponed")
                        || ci(t, "guarded") =>
                {
                    self.eat(&mut c);
                }
                _ => break,
            }
        }

        self.ws(&mut c);
        match self.peek_text() {
            None => self.finish_error(c),
            Some(t) => {
                if ci(t, "library") {
                    self.finish_clause(c, node::LIBRARY_CLAUSE)
                } else if ci(t, "use") {
                    self.finish_clause(c, node::USE_CLAUSE)
                } else if ci(t, "context") {
                    self.finish_context(c)
                } else if ci(t, "entity") {
                    self.finish_entity(c)
                } else if ci(t, "architecture") {
                    self.finish_architecture(c)
                } else if ci(t, "package") {
                    self.finish_package(c)
                } else if ci(t, "configuration") {
                    self.finish_configuration(c)
                } else if ci(t, "function") {
                    self.finish_subprogram(c, node::FUNCTION)
                } else if ci(t, "procedure") {
                    self.finish_subprogram(c, node::PROCEDURE)
                } else if ci(t, "component") {
                    self.finish_component(c)
                } else if ci(t, "type") {
                    self.finish_type(c)
                } else if ci(t, "subtype") {
                    self.finish_subtype(c)
                } else if ci(t, "constant") {
                    self.finish_constant(c)
                } else if ci(t, "signal")
                    || ci(t, "variable")
                    || ci(t, "file")
                    || ci(t, "alias")
                    || ci(t, "attribute")
                    || ci(t, "disconnect")
                    || ci(t, "group")
                {
                    self.finish_object(c)
                } else if ci(t, "for")
                    || ci(t, "generic")
                    || ci(t, "port")
                    || ci(t, "assert")
                    || ci(t, "wait")
                    || ci(t, "report")
                    || ci(t, "null")
                    || ci(t, "return")
                    || ci(t, "next")
                    || ci(t, "exit")
                {
                    self.finish_decl(c)
                } else if self.peek_kind() == Some(tk::IDENT) {
                    self.finish_object(c)
                } else {
                    self.finish_error(c)
                }
            }
        }
    }

    /// `library A, B;` / `use A.B.all;` — a context / use clause collected to `;`.
    fn finish_clause(&mut self, mut c: Vec<Child>, label: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // library / use
        self.collect_to_semicolon(&mut c);
        self.make_node(label, c)
    }

    /// A generic single-`;` declaration (`for … use …;`, `assert …;`, …).
    fn finish_decl(&mut self, mut c: Vec<Child>) -> Node {
        self.collect_to_semicolon(&mut c);
        self.make_node(node::DECL, c)
    }

    /// `signal … ;` / `variable … ;` / `attribute … ;` etc. — collected to `;`.
    fn finish_object(&mut self, mut c: Vec<Child>) -> Node {
        self.collect_to_semicolon(&mut c);
        self.make_node(node::OBJECT_DECL, c)
    }

    /// `constant N [, N]* : T [:= expr];`, collected to `;`.
    fn finish_constant(&mut self, mut c: Vec<Child>) -> Node {
        self.collect_to_semicolon(&mut c);
        self.make_node(node::CONSTANT_DECL, c)
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
            code: "vhdl.unrecognized_item",
            message: "token(s) not recognized as a VHDL declaration".to_string(),
            span: children_span(&c).unwrap_or_else(|| ByteSpan::empty_at(self.cur_offset())),
        });
        self.make_node(node::ERROR_ITEM, c)
    }

    /// `context Name is <clauses> end [context] [Name];`, or a context reference
    /// `context Lib.Ctx;` collected to `;`.
    fn finish_context(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // context
        c.push(Child::Node(self.name_node()));
        self.ws(&mut c);
        if self.at_kw("is") {
            self.eat(&mut c);
            self.parse_decl_list(&mut c);
            self.eat_end_clause(&mut c);
        } else {
            self.collect_to_semicolon(&mut c); // context reference
        }
        self.make_node(node::CONTEXT, c)
    }

    /// `entity E is <generic/port + decls> [begin <passive stmts>] end [entity] [E];`.
    fn finish_entity(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // entity
        c.push(Child::Node(self.name_node()));
        self.ws(&mut c);
        if self.at_kw("is") {
            self.eat(&mut c);
            self.parse_is_body(&mut c);
        } else {
            self.collect_to_semicolon(&mut c);
        }
        self.make_node(node::ENTITY, c)
    }

    /// `architecture A of E is <decls> begin <concurrent stmts> end [architecture]
    /// [A];`. The architecture name is the first `Name` child; the implemented
    /// entity name is the second `Name` child.
    fn finish_architecture(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // architecture
        c.push(Child::Node(self.name_node())); // architecture name
        self.ws(&mut c);
        if self.at_kw("of") {
            self.eat(&mut c);
            c.push(Child::Node(self.name_node())); // implemented entity name
        }
        self.ws(&mut c);
        if self.at_kw("is") {
            self.eat(&mut c);
            self.parse_is_body(&mut c);
        } else {
            self.collect_to_semicolon(&mut c);
        }
        self.make_node(node::ARCHITECTURE, c)
    }

    /// `package [body] P is <decls> end [package [body]] [P];`, or a package
    /// instantiation `package P is new Gen (…);` collected to `;`.
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
            self.collect_to_semicolon(&mut c);
        }
        self.make_node(node::PACKAGE, c)
    }

    /// `configuration C of E is <decls/for-blocks> end [configuration] [C];`. The
    /// inner `for … end for;` structure is captured losslessly (degraded: nested
    /// `for` blocks are not given dedicated nodes).
    fn finish_configuration(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // configuration
        c.push(Child::Node(self.name_node()));
        self.ws(&mut c);
        if self.at_kw("of") {
            self.eat(&mut c);
            c.push(Child::Node(self.name_node()));
        }
        self.ws(&mut c);
        if self.at_kw("is") {
            self.eat(&mut c);
            self.parse_is_body(&mut c);
        } else {
            self.collect_to_semicolon(&mut c);
        }
        self.make_node(node::CONFIGURATION, c)
    }

    /// `function F (…) return T [is <decls> begin <stmts> end] | is new … | ;` /
    /// `procedure P (…) [is <decls> begin <stmts> end] | is new … | ;`.
    fn finish_subprogram(&mut self, mut c: Vec<Child>, label: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // function / procedure
        c.push(Child::Node(self.name_node()));
        let mut sig = Vec::new();
        self.collect_until(&mut sig, &["is"], &[";"]);
        if !sig.is_empty() {
            c.push(Child::Node(self.make_node(node::SIGNATURE, sig)));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c); // declaration only
        } else if self.at_kw("is") {
            self.eat(&mut c);
            self.ws(&mut c);
            if self.at_kw("new") {
                self.collect_to_semicolon(&mut c); // instantiation
            } else {
                self.parse_is_body(&mut c);
            }
        } else {
            self.collect_to_semicolon(&mut c);
        }
        self.make_node(label, c)
    }

    /// `component C [is] <generic/port decls> end component [C];`.
    fn finish_component(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // component
        c.push(Child::Node(self.name_node()));
        self.ws(&mut c);
        if self.at_kw("is") {
            self.eat(&mut c);
        }
        self.parse_decl_list(&mut c);
        self.eat_end_clause(&mut c);
        self.make_node(node::COMPONENT, c)
    }

    /// The shared `<decls> [begin <stmts>] end [name];` body, entered with the
    /// cursor just past `is`.
    fn parse_is_body(&mut self, c: &mut Vec<Child>) {
        self.parse_decl_list(c);
        self.ws(c);
        if self.at_kw("begin") {
            self.eat(c);
            let b = self.parse_stmt_region();
            c.push(Child::Node(b));
        }
        self.eat_end_clause(c);
    }

    /// `type Name is <type def>;` — the body (which may contain a
    /// `record … end record`, `protected … end protected`, or `units … end units`
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

    /// Collect a type declaration body up to the terminating `;` at delimiter
    /// depth 0, treating `record … end record`, `protected … end protected`, and
    /// `units … end units` as balanced regions so an inner `;` does not end the
    /// declaration.
    fn collect_type_body(&mut self, c: &mut Vec<Child>) {
        let mut bal: i32 = 0;
        loop {
            self.ws(c);
            match self.peek_text() {
                None => break,
                Some(";") if bal == 0 => {
                    self.eat(c);
                    break;
                }
                Some("(") | Some("[") => {
                    let g = self.parse_delimited();
                    c.push(Child::Node(g));
                }
                Some(t) if ci(t, "record") || ci(t, "protected") || ci(t, "units") => {
                    // `end record` / `end protected` / `end units` are handled by
                    // the `end` arm below; an opening keyword raises the balance.
                    let prev_is_end = matches!(
                        c.iter().rev().find_map(|ch| match ch {
                            Child::Token(t) if !t.trivia => Some(t.span.text(self.src)),
                            _ => None,
                        }),
                        Some(p) if ci(p, "end")
                    );
                    if !prev_is_end {
                        bal += 1;
                    }
                    self.eat(c);
                }
                Some(t) if ci(t, "end") => {
                    bal -= 1;
                    if bal < 0 {
                        bal = 0;
                    }
                    self.eat(c);
                }
                Some(_) => self.eat(c),
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

    // --- names --------------------------------------------------------------

    /// A declared name: an identifier, an operator string for `function "+" (…)`,
    /// or a dotted name `Lib.Unit` (used by `context`/`configuration` references).
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

    /// Parse a declarative item list, stopping (without consuming) at `begin` or
    /// `end`. Depth-guarded.
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
                Some(t) if ci(t, "begin") || ci(t, "end") => break,
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
                Some(t) if bal == 0 && (ci(t, "begin") || ci(t, "end")) => break,
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

    /// Capture the executable / concurrent statement region after `begin` as a
    /// flat `Block`, stopping (without consuming) at the `end` that closes this
    /// construct. A block-keyword depth counter distinguishes that `end` from the
    /// `end`s of nested `if`/`case`/`loop`/`generate`/`process`/`block`/`record`/
    /// `units`/`protected`/`component`/`configuration` constructs. Parenthesised
    /// expressions are descended into as `Paren` groups, so their inner keywords
    /// never reach the counter.
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

    /// `end [keywords] [Name];` — eat `end` and everything up to `;`.
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
/// raise the block-depth counter (`end` closes one). `begin` is deliberately
/// absent: in VHDL it does not pair with its own `end` (the single `end process`
/// / `end block` closes the construct whose `begin` it followed). `component` and
/// `configuration` are also absent: in a statement region they appear only as
/// instantiation keywords (`lbl : component foo`, `lbl : configuration bar`),
/// which have *no* matching `end`, so counting them would unbalance the counter.
/// `record`/`units`/`protected` are kept because a process's declarative part may
/// hold a `type … is record … end record;` (each with a matching `end`).
///
/// Known limitation: a VHDL-2008 conditional/case *generate*
/// (`if cond generate … end generate`, `case expr generate … end generate`) makes
/// the leading `if`/`case` raise the counter without a matching `end if`/`end
/// case`; the region is then over-consumed but the tree stays byte-for-byte
/// lossless (every token still lands in the `Block`), only the structural framing
/// degrades.
fn is_block_open_word(t: &str) -> bool {
    ci(t, "if")
        || ci(t, "case")
        || ci(t, "loop")
        || ci(t, "generate")
        || ci(t, "process")
        || ci(t, "block")
        || ci(t, "record")
        || ci(t, "units")
        || ci(t, "protected")
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
-- a design file
library ieee;
use ieee.std_logic_1164.all;

package types_pkg is
   subtype byte is std_logic_vector(7 downto 0);
   constant VERSION : integer := 2;
   function inc (x : integer) return integer;
end package types_pkg;

package body types_pkg is
   function inc (x : integer) return integer is
   begin
      return x + 1;
   end function inc;
end package body types_pkg;

entity counter is
   generic (W : integer := 8);
   port (clk : in std_logic;
         rst : in std_logic;
         q   : out std_logic_vector(7 downto 0));
end entity counter;

architecture rtl of counter is
   signal next_q : std_logic_vector(7 downto 0);
   component sub is
      port (a : in std_logic; y : out std_logic);
   end component;
begin
   u_sub : sub port map (a => clk, y => next_q(0));

   process (clk, rst)
   begin
      if rst = '1' then
         q <= (others => '0');
      elsif clk'event and clk = '1' then
         q <= next_q;
      end if;
   end process;
end architecture rtl;
";
        let tree = parse("counter.vhd", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_units() {
        let src = "entity E is end entity;\narchitecture A of E is begin end A;\n\
                   package P is end package;\n";
        let tree = parse("u.vhd", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::ENTITY), "{kinds:?}");
        assert!(kinds.contains(&node::ARCHITECTURE), "{kinds:?}");
        assert!(kinds.contains(&node::PACKAGE), "{kinds:?}");
    }

    #[test]
    fn architecture_records_entity_name() {
        let src = "architecture rtl of counter is begin end rtl;";
        let tree = parse("a.vhd", src);
        let arch = tree
            .root
            .children_of(node::ARCHITECTURE)
            .next()
            .expect("architecture");
        let names: Vec<&str> = arch
            .children_of(node::NAME)
            .filter_map(|n| n.tokens().next().map(|t| t.span.text(src)))
            .collect();
        assert_eq!(names, vec!["rtl", "counter"]);
    }

    #[test]
    fn record_type_with_inner_semicolons() {
        let src = "type point is record\n   x : integer;\n   y : integer;\nend record;\n";
        let tree = parse("t.vhd", src);
        assert!(tree.is_lossless());
        let decls: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert_eq!(decls, vec![node::TYPE_DECL], "got {decls:?}");
    }

    #[test]
    fn nested_subprogram_is_first_class() {
        let src = "package body P is\n   function outer (x : integer) return integer is\n      \
                   function inner (y : integer) return integer is\n      begin\n         \
                   return y;\n      end inner;\n   begin\n      return inner(x);\n   \
                   end outer;\nend P;\n";
        let tree = parse("p.vhd", src);
        assert!(tree.is_lossless());
        let fns = tree
            .root
            .walk()
            .filter(|n| n.kind == node::FUNCTION)
            .count();
        assert_eq!(fns, 2, "outer and inner functions should both be nodes");
    }

    #[test]
    fn control_blocks_round_trip() {
        let src = "architecture a of e is begin\n   process begin\n      for i in 0 to 9 loop\n         \
                   case i is\n            when 0 => null;\n            when others => null;\n         \
                   end case;\n      end loop;\n   end process;\nend a;\n";
        let tree = parse("p.vhd", src);
        assert!(tree.is_lossless());
        assert_eq!(
            tree.root
                .child_nodes()
                .filter(|n| n.kind == node::ARCHITECTURE)
                .count(),
            1,
            "the nested control ends must not leak past the architecture"
        );
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let deep_parens = format!(
            "constant X : integer := {}{};\n",
            "(".repeat(10_000),
            ")".repeat(10_000)
        );
        let mut deep_blocks = String::from("architecture a of e is begin\n   process begin\n");
        for _ in 0..3_000 {
            deep_blocks.push_str("if true then\n");
        }
        for _ in 0..3_000 {
            deep_blocks.push_str("end if;\n");
        }
        deep_blocks.push_str("end process;\nend a;\n");
        // Deep parens are recursion-guarded: must round-trip AND report the limit.
        let paren_tree = parse("deep.vhd", &deep_parens);
        assert!(paren_tree.is_lossless(), "deep parens must round-trip");
        assert!(
            paren_tree
                .diagnostics
                .iter()
                .any(|d| d.code == "vhdl.depth_limit"),
            "recursion depth limit should be reported for deep parens"
        );
        // Deep `if/end if` nesting is handled by an iterative block-depth counter
        // (no recursion to overflow), so it round-trips with no depth diagnostic.
        let block_tree = parse("deep.vhd", &deep_blocks);
        assert!(block_tree.is_lossless(), "deep blocks must round-trip");
    }

    #[test]
    fn edge_inputs_round_trip() {
        for src in [
            "",
            "   \n\n  -- only trivia\n",
            "x <= (1, 2\n",                          // unterminated paren
            "s : string := \"open\n",                // unterminated string
            "function \"+\" (l, r : t) return t;\n", // operator name
            "entity E is end E;\n",
            "architecture a of e is begin\n", // unterminated body
            "end architecture;",              // stray terminator
        ] {
            let tree = parse("edge.vhd", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
