//! Verilog / SystemVerilog parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust and Lua parsers: definition *headers* are parsed
//! precisely — we always know a `module`'s name, a `class`'s name, a `function`'s
//! signature — while bodies and expression regions are captured as recursive item
//! lists or balanced token-tree groups (`Paren`/`Bracket`/`Brace`), which is
//! perfectly lossless. Graph facts (instantiations, calls, imports) are extracted
//! from these real tokens in the lowering pass, never invented.
//!
//! Verilog's block structure is keyword … end-keyword (not braces):
//! `module`…`endmodule`, `function`…`endfunction`, `task`…`endtask`,
//! `class`…`endclass`, `package`…`endpackage`, `interface`…`endinterface`,
//! `begin`…`end`, `case`…`endcase`, and so on. A definition header runs up to the
//! terminating `;`, then the body is a recursive item list up to the matching
//! end-keyword. Compiler directives (`` `define ``, `` `include ``) are line-based
//! and captured as `Directive` nodes spanning to end of line.
//!
//! Anything unrecognized still lands in the tree as its exact tokens (a
//! `GenericStmt` or `ErrorItem`), so the result always round-trips. The recursion
//! is depth-guarded at [`MAX_DEPTH`] against hostile nesting (deep keyword blocks
//! *or* deep brackets) — a `catch_unwind` cannot catch a stack overflow, so the
//! guard is the real defense.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::verilog::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const MODULE: &str = "Module";
    pub const INTERFACE: &str = "Interface";
    pub const PROGRAM: &str = "Program";
    pub const PACKAGE: &str = "Package";
    pub const CLASS: &str = "Class";
    pub const FUNCTION: &str = "Function";
    pub const TASK: &str = "Task";
    pub const GENERATE: &str = "Generate";
    pub const BEGIN_BLOCK: &str = "BeginBlock";
    pub const CASE: &str = "Case";
    pub const BLOCK_CONSTRUCT: &str = "BlockConstruct";
    pub const DIRECTIVE: &str = "Directive";
    pub const IMPORT_DECL: &str = "ImportDecl";
    pub const PARAM_DECL: &str = "ParamDecl";
    pub const GENERIC_STMT: &str = "GenericStmt";
    pub const ERROR_ITEM: &str = "ErrorItem";

    pub const NAME: &str = "Name";
    pub const HEADER: &str = "Header";
    pub const ITEM_BLOCK: &str = "ItemBlock";
    pub const ATTR: &str = "Attr";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat run. Protects against stack overflow on pathological or
/// hostile inputs — mirrors the Rust/Lua parsers' guard exactly.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = VerilogParser {
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

struct VerilogParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> VerilogParser<'s> {
    // --- cursor primitives --------------------------------------------------

    /// Append the current token (trivia or not) to `out` and advance.
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

    /// Eat every remaining token (used to flush trailing trivia at end of input).
    fn flush(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() {
            self.eat(out);
        }
    }

    /// Kind of the n-th significant (non-trivia) token from the cursor.
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

    /// Text of the n-th significant token from the cursor.
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

    fn at_ident(&self) -> bool {
        self.peek_kind() == Some(tk::IDENT)
    }

    fn at_open(&self) -> bool {
        self.at("(") || self.at("[") || self.at("{")
    }

    /// True if a newline appears in the trivia between the cursor and the next
    /// significant token — the basis for the directive line-boundary detection.
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

    /// `ws` then consume a block end-keyword. Consumes only when it exactly
    /// matches `expected`, so a missing/mismatched terminator is never *stolen*
    /// from an enclosing scope; the bytes are recorded via a diagnostic and left
    /// for the rightful owner (or the top-level stray-terminator handler).
    fn eat_block_end(&mut self, out: &mut Vec<Child>, expected: &'static str) {
        self.ws(out);
        if self.at(expected) {
            self.eat(out);
            // Optional `: label` after an end-keyword (e.g. `endmodule : m`).
            self.maybe_end_label(out);
        } else {
            self.diags.push(Diagnostic {
                code: "verilog.missing_end",
                message: format!("expected '{expected}'"),
                span: ByteSpan::empty_at(self.cur_offset()),
            });
        }
    }

    /// Consume an optional `: name` block label following an end-keyword.
    fn maybe_end_label(&mut self, out: &mut Vec<Child>) {
        let save = self.i;
        let mut tmp = Vec::new();
        self.ws(&mut tmp);
        if self.at(":") {
            self.eat(&mut tmp);
            self.ws(&mut tmp);
            if self.at_ident() {
                self.eat(&mut tmp);
            }
            out.extend(tmp);
        } else {
            // No label — rewind so the trivia stays with the outer scope.
            self.i = save;
        }
    }

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "verilog.depth_limit",
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
                Some(t) if is_end_keyword(t) => {
                    // A stray terminator at top level: consume it as an error item
                    // so the loop makes progress and nothing is dropped.
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

    /// Parse a body as a recursive item list until a block end-keyword or EOF.
    /// Depth-guarded: beyond [`MAX_DEPTH`] the body is consumed as a flat token
    /// run rather than recursing.
    fn parse_item_block(&mut self) -> Node {
        if self.depth >= MAX_DEPTH {
            let mut c = Vec::new();
            self.consume_block_flat(&mut c);
            self.note_depth_limit();
            return self.make_node(node::ITEM_BLOCK, c);
        }
        self.depth += 1;
        let mut c = Vec::new();
        loop {
            match self.peek_text() {
                None => {
                    self.flush(&mut c);
                    break;
                }
                Some(t) if is_end_keyword(t) => break,
                _ => {
                    let item = self.parse_item();
                    c.push(Child::Node(item));
                }
            }
        }
        let block = self.make_node(node::ITEM_BLOCK, c);
        self.depth -= 1;
        block
    }

    /// At the depth cap, swallow a body as a flat token run (no recursion).
    fn consume_block_flat(&mut self, out: &mut Vec<Child>) {
        loop {
            match self.peek_text() {
                None => {
                    self.flush(out);
                    break;
                }
                Some(t) if is_end_keyword(t) => break,
                _ => {
                    self.ws(out);
                    self.eat(out);
                }
            }
        }
    }

    // --- items --------------------------------------------------------------

    fn parse_item(&mut self) -> Node {
        let mut prefix = Vec::new();
        self.ws(&mut prefix);

        // Attributes `(* ... *)`.
        while self.at("(") && self.peek_n_text(1) == Some("*") {
            self.parse_attr(&mut prefix);
            self.ws(&mut prefix);
        }

        // Compiler directive / macro use line.
        if self.peek_kind() == Some(tk::DIRECTIVE) {
            return self.finish_directive(prefix);
        }

        // Leading declaration qualifiers that precede a definition keyword
        // (`virtual class`, `pure virtual function`, `static function`, …). Only
        // consume the qualifier run when a definition keyword actually follows it,
        // so an identifier that merely looks like a qualifier is left alone.
        let mut k = 0;
        while is_qualifier(self.peek_n_text(k)) {
            k += 1;
        }
        if self.peek_n_text(k).map(is_def_keyword).unwrap_or(false) {
            for _ in 0..k {
                self.ws(&mut prefix);
                self.eat(&mut prefix);
            }
        }

        self.ws(&mut prefix);
        match self.peek_text() {
            Some("module") | Some("macromodule") => {
                self.finish_def(prefix, node::MODULE, "endmodule")
            }
            Some("interface") => self.finish_def(prefix, node::INTERFACE, "endinterface"),
            Some("program") => self.finish_def(prefix, node::PROGRAM, "endprogram"),
            Some("package") => self.finish_def(prefix, node::PACKAGE, "endpackage"),
            Some("class") => self.finish_def(prefix, node::CLASS, "endclass"),
            Some("function") => self.finish_def(prefix, node::FUNCTION, "endfunction"),
            Some("task") => self.finish_def(prefix, node::TASK, "endtask"),
            Some("generate") => self.finish_block(prefix, node::GENERATE, "endgenerate", false),
            Some("begin") => self.finish_begin(prefix),
            Some("case") | Some("casex") | Some("casez") => {
                self.finish_block(prefix, node::CASE, "endcase", true)
            }
            Some("specify") => {
                self.finish_block(prefix, node::BLOCK_CONSTRUCT, "endspecify", false)
            }
            Some("primitive") => self.finish_def(prefix, node::BLOCK_CONSTRUCT, "endprimitive"),
            Some("config") => self.finish_def(prefix, node::BLOCK_CONSTRUCT, "endconfig"),
            Some("clocking") => self.finish_def(prefix, node::BLOCK_CONSTRUCT, "endclocking"),
            Some("property") => self.finish_def(prefix, node::BLOCK_CONSTRUCT, "endproperty"),
            Some("sequence") => self.finish_def(prefix, node::BLOCK_CONSTRUCT, "endsequence"),
            Some("covergroup") => self.finish_def(prefix, node::BLOCK_CONSTRUCT, "endgroup"),
            Some("parameter") | Some("localparam") => self.finish_stmt(prefix, node::PARAM_DECL),
            Some("import") | Some("export") => self.finish_stmt(prefix, node::IMPORT_DECL),
            Some(_) => self.finish_stmt(prefix, node::GENERIC_STMT),
            None => {
                // Defensive: guarantee progress.
                let mut c = prefix;
                self.eat(&mut c);
                self.make_node(node::ERROR_ITEM, c)
            }
        }
    }

    /// `(* ... *)` attribute instance. Consumes through the closing `*)`.
    fn parse_attr(&mut self, out: &mut Vec<Child>) {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // (
        loop {
            self.ws(&mut c);
            match self.peek_text() {
                None => break, // unterminated; still lossless
                Some("*") if self.peek_n_text(1) == Some(")") => {
                    self.eat(&mut c); // *
                    self.ws(&mut c);
                    self.eat(&mut c); // )
                    break;
                }
                Some(_) => self.eat(&mut c),
            }
        }
        out.push(Child::Node(self.make_node(node::ATTR, c)));
    }

    /// A directive line: the directive token plus the rest of its source line.
    fn finish_directive(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // the directive token
        loop {
            if self.peek_kind().is_none() || self.newline_before_next() {
                break;
            }
            self.ws(&mut c); // non-newline trivia only (no newline ahead)
            if self.peek_kind().is_none() {
                break;
            }
            if self.at_open() {
                let g = self.parse_delimited();
                c.push(Child::Node(g));
            } else {
                self.eat(&mut c);
            }
        }
        self.make_node(node::DIRECTIVE, c)
    }

    /// A definition with a `;`-terminated header and an end-keyword-delimited
    /// body: `kw [name] header ; items end_kw [: label]`. Module-family
    /// definitions (`simple_name`) take the first identifier as the `Name`;
    /// `function`/`task` keep the name inline in the `Header` (the lowering finds
    /// it), since a return type may precede it.
    fn finish_def(&mut self, mut c: Vec<Child>, kind: &'static str, end_kw: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // the def keyword
        let simple_name = !matches!(kind, node::FUNCTION | node::TASK);
        if simple_name {
            // Skip an optional lifetime/qualifier between keyword and name that a
            // few constructs allow (`covergroup`, `class` parameters come after).
            self.ws(&mut c);
            if self.at_ident() && !is_keyword_word(self.peek_text()) {
                let n = self.name_node();
                c.push(Child::Node(n));
            }
        }
        // `extern` / `pure` function & task *prototypes* end at `;` with no body
        // and no end-keyword. Detect them from the already-collected prefix so we
        // do not wrongly swallow the following members as a body.
        let prototype = matches!(kind, node::FUNCTION | node::TASK)
            && c.iter().any(|child| match child {
                Child::Token(t) => matches!(t.span.text(self.src), "extern" | "pure"),
                Child::Node(_) => false,
            });
        if let Some(h) = self.collect_region(node::HEADER, &[";"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        if !prototype {
            let body = self.parse_item_block();
            c.push(Child::Node(body));
            self.eat_block_end(&mut c, end_kw);
        }
        self.make_node(kind, c)
    }

    /// A block construct with no `;` header: `kw [header_paren] items end_kw`.
    /// `grab_paren` captures a leading `(...)` (the `case` selector expression).
    fn finish_block(
        &mut self,
        mut c: Vec<Child>,
        kind: &'static str,
        end_kw: &'static str,
        grab_paren: bool,
    ) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // the block keyword
        if grab_paren {
            self.ws(&mut c);
            if self.at("(") {
                let g = self.parse_delimited();
                c.push(Child::Node(g));
            }
        }
        let body = self.parse_item_block();
        c.push(Child::Node(body));
        self.eat_block_end(&mut c, end_kw);
        self.make_node(kind, c)
    }

    /// `begin [: label] items end [: label]`.
    fn finish_begin(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // begin
        self.ws(&mut c);
        if self.at(":") {
            self.eat(&mut c);
            self.ws(&mut c);
            if self.at_ident() {
                let n = self.name_node();
                c.push(Child::Node(n));
            }
        }
        let body = self.parse_item_block();
        c.push(Child::Node(body));
        self.eat_block_end(&mut c, "end");
        self.make_node(node::BEGIN_BLOCK, c)
    }

    /// A statement / declaration captured up to its terminating `;`. Descends into
    /// balanced groups. Stops (without consuming) at a block keyword or
    /// end-keyword so a following construct parses fresh. Always consumes at least
    /// one token to guarantee progress.
    fn finish_stmt(&mut self, mut c: Vec<Child>, kind: &'static str) -> Node {
        let start_i = self.i;
        loop {
            self.ws(&mut c);
            match self.peek_text() {
                None => {
                    self.flush(&mut c);
                    break;
                }
                Some(";") => {
                    self.eat(&mut c);
                    break;
                }
                Some(t) if is_end_keyword(t) || is_block_opener(t) => break,
                Some(_) => {
                    if self.at_open() {
                        let g = self.parse_delimited();
                        c.push(Child::Node(g));
                    } else {
                        self.eat(&mut c);
                    }
                }
            }
        }
        // Progress guard: if nothing significant was consumed (e.g. we stopped
        // immediately at a block keyword that is not a recognized opener path),
        // consume exactly one token so the caller always advances.
        if self.i == start_i {
            self.eat(&mut c);
        }
        self.make_node(kind, c)
    }

    // --- shared helpers -----------------------------------------------------

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.eat(&mut c); // the identifier (cursor is at it after caller ws)
        self.make_node(node::NAME, c)
    }

    /// Collect tokens (descending into balanced groups) until a significant stop
    /// token at delimiter depth 0, or a block/end keyword. Leading/trailing trivia
    /// around a stop stays with the parent.
    fn collect_region(&mut self, label: &'static str, stops: &[&str]) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            match self.peek_text() {
                None => break,
                Some(t) if stops.contains(&t) => break,
                Some(t) if is_end_keyword(t) || is_block_opener(t) => break,
                Some(_) => {
                    if self.at_open() {
                        self.ws(&mut c);
                        let inner = self.parse_delimited();
                        c.push(Child::Node(inner));
                    } else {
                        self.ws(&mut c);
                        self.eat(&mut c);
                    }
                }
            }
        }
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(label, c))
        }
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`. Cursor is at
    /// (or before trivia preceding) the opener.
    fn parse_delimited(&mut self) -> Node {
        let mut g = Vec::new();
        self.ws(&mut g);
        let (close, label) = match self.peek_text() {
            Some("(") => (")", node::PAREN),
            Some("[") => ("]", node::BRACKET),
            Some("{") => ("}", node::BRACE),
            _ => return self.make_node(node::ERROR_ITEM, g),
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
                Some(_) => self.eat(&mut g),
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

// --- keyword classification -------------------------------------------------

/// Block end-keywords. Encountering one ends an item list.
fn is_end_keyword(t: &str) -> bool {
    matches!(
        t,
        "end"
            | "endmodule"
            | "endfunction"
            | "endtask"
            | "endclass"
            | "endpackage"
            | "endinterface"
            | "endprogram"
            | "endgenerate"
            | "endcase"
            | "endspecify"
            | "endprimitive"
            | "endconfig"
            | "endclocking"
            | "endproperty"
            | "endsequence"
            | "endgroup"
    )
}

/// Keywords that open a structural block (so a `GenericStmt` stops before them and
/// a fresh item is parsed).
fn is_block_opener(t: &str) -> bool {
    matches!(
        t,
        "module"
            | "macromodule"
            | "interface"
            | "program"
            | "package"
            | "class"
            | "function"
            | "task"
            | "generate"
            | "begin"
            | "case"
            | "casex"
            | "casez"
            | "specify"
            | "primitive"
            | "config"
            | "clocking"
            | "property"
            | "sequence"
            | "covergroup"
    )
}

/// Declaration qualifiers that may precede a definition keyword.
fn is_qualifier(t: Option<&str>) -> bool {
    matches!(
        t,
        Some("virtual")
            | Some("pure")
            | Some("static")
            | Some("automatic")
            | Some("extern")
            | Some("local")
            | Some("protected")
            | Some("const")
            | Some("rand")
            | Some("randc")
    )
}

/// Keywords that begin a `;`-headed definition (used to decide whether a leading
/// qualifier like `virtual`/`static` is part of a definition).
fn is_def_keyword(t: &str) -> bool {
    matches!(
        t,
        "module"
            | "macromodule"
            | "interface"
            | "program"
            | "package"
            | "class"
            | "function"
            | "task"
            | "covergroup"
            | "property"
            | "sequence"
            | "clocking"
    )
}

/// Whether a word is any recognized Verilog keyword (openers, enders, qualifiers).
fn is_keyword_word(t: Option<&str>) -> bool {
    match t {
        Some(s) => {
            is_block_opener(s) || is_end_keyword(s) || crate::lang::verilog::lexer::is_keyword(s)
        }
        None => false,
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
// a design file
`include \"defs.vh\"
`define WIDTH 8

package pkg;
    localparam int VERSION = 1;
endpackage

module top #(parameter W = 8) (input clk, output [W-1:0] q);
    wire [7:0] data;
    sub u_sub (.clk(clk), .out(data));

    always @(posedge clk) begin
        q <= data;
        $display(\"q = %d\", q);
    end

    function automatic int add(int a, int b);
        return a + b;
    endfunction
endmodule

class Packet extends BasePacket;
    function new();
        super.new();
    endfunction
endclass
";
        let tree = parse("design.sv", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "module m; endmodule\nfunction f; endfunction\nclass C; endclass\npackage p; endpackage\n";
        let tree = parse("t.sv", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::MODULE));
        assert!(kinds.contains(&node::FUNCTION));
        assert!(kinds.contains(&node::CLASS));
        assert!(kinds.contains(&node::PACKAGE));
    }

    #[test]
    fn module_name_is_captured() {
        let src = "module counter (input clk); endmodule";
        let tree = parse("t.v", src);
        let m = tree
            .root
            .children_of(node::MODULE)
            .next()
            .expect("a module");
        let name = m.child(node::NAME).expect("a name node");
        assert_eq!(
            name.tokens().next().map(|t| t.span.text(src)),
            Some("counter")
        );
    }

    #[test]
    fn nested_begin_blocks_round_trip() {
        let src = "module m; initial begin begin x = 1; end y = 2; end endmodule";
        let tree = parse("t.v", src);
        assert!(tree.is_lossless());
    }

    #[test]
    fn case_block_round_trips() {
        let src =
            "module m; always @(*) case (sel) 2'b00: a = 1; default: a = 0; endcase endmodule";
        let tree = parse("t.v", src);
        assert!(tree.is_lossless());
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        // Deep brackets and deep keyword blocks; must not stack-overflow.
        let deep_brackets = format!("wire x = {}{};\n", "(".repeat(10_000), ")".repeat(10_000));
        let mut deep_blocks = String::from("module m; initial ");
        for _ in 0..2_000 {
            deep_blocks.push_str("begin ");
        }
        for _ in 0..2_000 {
            deep_blocks.push_str("end ");
        }
        deep_blocks.push_str("endmodule\n");
        for src in [deep_brackets, deep_blocks] {
            let tree = parse("deep.v", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics
                    .iter()
                    .any(|d| d.code == "verilog.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "module m (input a\n",    // unterminated header / no endmodule
            "x = \"unterminated\n",   // unterminated string
            "/* open block comment",  // unterminated comment
            "λ = '☃';  // unicode\n", // multi-byte
            "",                       // empty file
            "\n\n   \n// trailing\n", // only blanks and comments
            "endmodule",              // stray terminator
        ] {
            let tree = parse("edge.v", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
