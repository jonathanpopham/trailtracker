//! Lua parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust and Python parsers: definition *headers* are parsed
//! precisely — we always know a `function`'s name path, its parameters, a
//! `local` binder — while expression regions and bodies are captured as balanced
//! token-tree groups (`Paren`/`Bracket`/`Brace`) plus flat tokens, which is
//! perfectly lossless. Graph facts (calls, requires, methods) are extracted from
//! these real tokens in the lowering pass, never invented.
//!
//! Unlike Python, Lua is **not** whitespace-significant: blocks are delimited by
//! keywords (`do`/`end`, `then`/`end`, `repeat`/`until`, function bodies), and a
//! newline is ordinary trivia. Statements are normally separated only by a
//! newline (the optional `;` is rare), and there is a genuine grammar ambiguity
//! when statements abut without a separator. Rather than build a full Lua
//! expression parser, this parser uses a documented heuristic to delimit
//! expression/assignment statements: at bracket depth 0 it ends such a statement
//! at a `;`, at a statement-introducing keyword, or at a newline that is not an
//! obvious expression continuation (the previous token does not demand a
//! right-hand side and the next does not continue one). This keeps definitions,
//! calls, requires and methods precise — the analytically important facts — while
//! staying byte-for-byte lossless on every input.
//!
//! Anything unrecognized still lands in the tree as its exact tokens, so the
//! result always round-trips. The recursion is depth-guarded at [`MAX_DEPTH`]
//! against hostile nesting (deep keyword blocks *or* deep brackets) — a
//! `catch_unwind` cannot catch a stack overflow, so the guard is the real defense.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::lua::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const CHUNK: &str = "Chunk";
    pub const FUNCTION: &str = "Function";
    pub const FUNC_NAME: &str = "FuncName";
    pub const LOCAL_STMT: &str = "LocalStmt";
    pub const SIMPLE_STMT: &str = "SimpleStmt";
    pub const RETURN: &str = "Return";
    pub const CONTROL: &str = "Control";
    pub const LABEL: &str = "Label";
    pub const ERROR_STMT: &str = "ErrorStmt";

    pub const HEADER: &str = "Header";
    pub const BLOCK: &str = "Block";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat run. Protects against stack overflow on pathological or
/// hostile inputs — mirrors the Rust/Python parsers' guard exactly.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = LuaParser {
        src: source,
        toks,
        i: 0,
        diags: Vec::new(),
        depth: 0,
    };
    let root = p.parse_chunk();
    ParseTree {
        source_id: SourceId::from_path(path),
        path: path.to_string(),
        source: source.to_string(),
        root,
        diagnostics: p.diags,
    }
}

struct LuaParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

/// The last significant element consumed in an expression run, used by the
/// statement-boundary heuristic.
enum Last {
    None,
    Group,
    Tok(String, bool),
}

impl<'s> LuaParser<'s> {
    // --- cursor primitives --------------------------------------------------

    /// Append the current token (trivia or not) to `out` and advance.
    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading **trivia** tokens (whitespace, newlines,
    /// comments) into `out`. In Lua every one of these is trivia.
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

    /// True if a newline appears in the trivia between the cursor and the next
    /// significant token (the basis for the soft statement-separator heuristic).
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
    /// diagnostic and leave the cursor in place (the bytes are never dropped —
    /// the surrounding context will consume them).
    fn eat_keyword(&mut self, out: &mut Vec<Child>, kw: &'static str) {
        self.ws(out);
        if self.at(kw) {
            self.eat(out);
        } else {
            self.diags.push(Diagnostic {
                code: "lua.missing_keyword",
                message: format!("expected '{kw}'"),
                span: ByteSpan::empty_at(self.cur_offset()),
            });
        }
    }

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "lua.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; region flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }

    // --- top level ----------------------------------------------------------

    fn parse_chunk(&mut self) -> Node {
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
        self.make_node(node::CHUNK, c)
    }

    /// Parse a block: statements until a block terminator (`end`/`else`/`elseif`/
    /// `until`) or end of input. The terminator is **not** consumed — the caller
    /// owns it. Depth-guarded: beyond [`MAX_DEPTH`] the body is consumed as a flat
    /// token run rather than recursing.
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
    /// Lossless; the truncation is reported via a `depth_limit` diagnostic.
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
            Some("function") => self.finish_function(),
            Some("local") => {
                if self.peek_n_text(1) == Some("function") {
                    self.finish_local_function()
                } else {
                    self.finish_local_assign()
                }
            }
            Some("if") => self.finish_if(),
            Some("while") => self.finish_while_for("while"),
            Some("for") => self.finish_while_for("for"),
            Some("do") => self.finish_do(),
            Some("repeat") => self.finish_repeat(),
            Some("return") => self.finish_return(),
            Some("break") | Some("goto") => self.finish_keyword_simple(),
            Some("::") => self.finish_label(),
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

    /// `function funcname ( params ) block end`, or an anonymous
    /// `function ( params ) block end` in expression position.
    fn finish_function(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // function
        self.ws(&mut c);
        if !self.at("(") {
            let name = self.parse_func_name();
            c.push(Child::Node(name));
        }
        self.ws(&mut c);
        if self.at("(") {
            let params = self.parse_delimited();
            c.push(Child::Node(params));
        }
        c.push(Child::Node(self.parse_block()));
        self.eat_keyword(&mut c, "end");
        self.make_node(node::FUNCTION, c)
    }

    /// `local function Name ( params ) block end`.
    fn finish_local_function(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // local
        self.eat_keyword(&mut c, "function");
        self.ws(&mut c);
        let name = self.parse_simple_name();
        c.push(Child::Node(name));
        self.ws(&mut c);
        if self.at("(") {
            let params = self.parse_delimited();
            c.push(Child::Node(params));
        }
        c.push(Child::Node(self.parse_block()));
        self.eat_keyword(&mut c, "end");
        self.make_node(node::FUNCTION, c)
    }

    /// `local namelist [= explist]`.
    fn finish_local_assign(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // local
        self.collect_expr_run(&mut c, true, &[]);
        self.make_node(node::LOCAL_STMT, c)
    }

    /// `if exp then block {elseif exp then block} [else block] end`.
    fn finish_if(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // if
        if let Some(h) = self.header(&["then"]) {
            c.push(Child::Node(h));
        }
        self.eat_keyword(&mut c, "then");
        c.push(Child::Node(self.parse_block()));
        loop {
            self.ws(&mut c);
            match self.peek_text() {
                Some("elseif") => {
                    self.eat(&mut c);
                    if let Some(h) = self.header(&["then"]) {
                        c.push(Child::Node(h));
                    }
                    self.eat_keyword(&mut c, "then");
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

    /// `while exp do block end` / `for ... do block end` (numeric and generic
    /// `for` share the same header-then-`do` shape).
    fn finish_while_for(&mut self, _kw: &str) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // while / for
        if let Some(h) = self.header(&["do"]) {
            c.push(Child::Node(h));
        }
        self.eat_keyword(&mut c, "do");
        c.push(Child::Node(self.parse_block()));
        self.eat_keyword(&mut c, "end");
        self.make_node(node::CONTROL, c)
    }

    /// `do block end`.
    fn finish_do(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // do
        c.push(Child::Node(self.parse_block()));
        self.eat_keyword(&mut c, "end");
        self.make_node(node::CONTROL, c)
    }

    /// `repeat block until exp`.
    fn finish_repeat(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // repeat
        c.push(Child::Node(self.parse_block()));
        self.eat_keyword(&mut c, "until");
        if let Some(h) = self.header(&[]) {
            c.push(Child::Node(h));
        }
        self.make_node(node::CONTROL, c)
    }

    /// `return [explist] [;]`.
    fn finish_return(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // return
        self.collect_expr_run(&mut c, true, &[]);
        self.make_node(node::RETURN, c)
    }

    /// `break` / `goto Name` — a single keyword (plus an optional label).
    fn finish_keyword_simple(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        let is_goto = self.at("goto");
        self.eat(&mut c); // break / goto
        if is_goto {
            self.ws(&mut c);
            if self.peek_kind() == Some(tk::NAME) {
                self.eat(&mut c);
            }
        }
        self.make_node(node::SIMPLE_STMT, c)
    }

    /// `::Name::` label.
    fn finish_label(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // ::
        self.ws(&mut c);
        if self.peek_kind() == Some(tk::NAME) {
            self.eat(&mut c);
        }
        self.ws(&mut c);
        if self.at("::") {
            self.eat(&mut c);
        }
        self.make_node(node::LABEL, c)
    }

    /// A lone `;` (empty statement).
    fn finish_semi(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // ;
        self.make_node(node::SIMPLE_STMT, c)
    }

    /// An expression / assignment statement (a function call or `varlist =
    /// explist`), delimited by the boundary heuristic.
    fn finish_simple(&mut self) -> Node {
        let mut c = Vec::new();
        self.collect_expr_run(&mut c, true, &[]);
        self.make_node(node::SIMPLE_STMT, c)
    }

    // --- names --------------------------------------------------------------

    /// `Name {'.' Name} [':' Name]` — a function-definition target path.
    fn parse_func_name(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        if self.peek_kind() == Some(tk::NAME) {
            self.eat(&mut c);
        }
        loop {
            self.ws(&mut c);
            if self.at(".") {
                self.eat(&mut c);
                self.ws(&mut c);
                if self.peek_kind() == Some(tk::NAME) {
                    self.eat(&mut c);
                }
            } else if self.at(":") {
                self.eat(&mut c);
                self.ws(&mut c);
                if self.peek_kind() == Some(tk::NAME) {
                    self.eat(&mut c);
                }
                break; // a method name is terminal
            } else {
                break;
            }
        }
        self.make_node(node::FUNC_NAME, c)
    }

    /// A single `Name` wrapped as a `FuncName` (for `local function`).
    fn parse_simple_name(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        if self.peek_kind() == Some(tk::NAME) {
            self.eat(&mut c);
        }
        self.make_node(node::FUNC_NAME, c)
    }

    // --- expression regions -------------------------------------------------

    /// Collect a control-statement header (the expression between a keyword and
    /// `then`/`do`, or a `repeat`'s `until` condition). Returns `None` when the
    /// region is empty.
    fn header(&mut self, stops: &[&'static str]) -> Option<Node> {
        let mut c = Vec::new();
        self.collect_expr_run(&mut c, false, stops);
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(node::HEADER, c))
        }
    }

    /// Collect an expression run into `out`. Stops (without consuming) at a block
    /// terminator, at any `header_stops` keyword, or at a statement-introducing
    /// keyword; consumes and stops at a `;`. When `soft_newline` is set, also
    /// stops at a newline that is not an obvious expression continuation. A
    /// `function` keyword is parsed inline as an anonymous function when the
    /// surrounding expression demands an operand, otherwise it begins a new
    /// statement and ends the run. Balanced `()`/`[]`/`{}` groups are descended
    /// into as `Paren`/`Bracket`/`Brace` nodes.
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
            if is_hard_stmt_keyword(txt) {
                break;
            }
            if txt == "function" {
                if continues_after(&last) {
                    let f = self.finish_function();
                    out.push(Child::Node(f));
                    last = Last::Group;
                    continue;
                } else {
                    break; // a new function statement
                }
            }
            if soft_newline && newline_ahead && !matches!(last, Last::None) {
                let next_kind = self.peek_kind().unwrap_or(tk::ERROR);
                if !continues_after(&last) && !continues_before(next_kind, txt) {
                    break;
                }
            }
            if is_open_delim(txt) {
                self.ws(out);
                let g = self.parse_delimited();
                out.push(Child::Node(g));
                last = Last::Group;
            } else {
                let owned = txt.to_string();
                let is_name = self.peek_kind() == Some(tk::NAME);
                self.ws(out);
                self.eat(out);
                last = Last::Tok(owned, is_name);
            }
        }
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`. Newlines
    /// inside are ordinary trivia. An anonymous `function ... end` appearing in
    /// the group (e.g. a table field or call argument) is parsed as a real
    /// `Function` node so nested definitions and calls are captured.
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
                Some("function") => {
                    if self.depth < MAX_DEPTH {
                        self.depth += 1;
                        let f = self.finish_function();
                        self.depth -= 1;
                        g.push(Child::Node(f));
                    } else {
                        self.eat(&mut g);
                        self.note_depth_limit();
                    }
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
    matches!(t, "end" | "else" | "elseif" | "until")
}

/// Keywords that can only begin a statement (never continue an expression), so
/// they end an expression run.
fn is_hard_stmt_keyword(t: &str) -> bool {
    matches!(
        t,
        "local" | "if" | "while" | "for" | "do" | "repeat" | "return" | "break" | "goto"
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
        Last::Tok(text, is_name) => {
            if *is_name {
                matches!(text.as_str(), "and" | "or" | "not")
            } else {
                matches!(
                    text.as_str(),
                    "+" | "-"
                        | "*"
                        | "/"
                        | "//"
                        | "%"
                        | "^"
                        | "#"
                        | "&"
                        | "~"
                        | "|"
                        | "<<"
                        | ">>"
                        | ".."
                        | "="
                        | ","
                        | "<"
                        | ">"
                        | "<="
                        | ">="
                        | "=="
                        | "~="
                        | "."
                        | ":"
                )
            }
        }
    }
}

/// True when the next token continues the preceding expression (a binary
/// operator, a field/method access, or a call/index/table-argument opener), so a
/// newline before it is not a statement boundary.
fn continues_before(kind: &str, text: &str) -> bool {
    if kind == tk::NAME {
        return matches!(text, "and" | "or");
    }
    matches!(
        text,
        "+" | "-"
            | "*"
            | "/"
            | "//"
            | "%"
            | "^"
            | "&"
            | "~"
            | "|"
            | "<<"
            | ">>"
            | ".."
            | "<"
            | ">"
            | "<="
            | ">="
            | "=="
            | "~="
            | "."
            | ":"
            | "("
            | "["
            | "{"
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
-- a module
local M = {}

local function helper(x)
    return x * 2
end

function M.new(name)
    local self = { name = name }
    return self
end

function M:greet()
    if self.name ~= nil then
        print('hi ' .. self.name)
    else
        print('hi')
    end
end

M.handlers = {
    onclick = function(e)
        helper(e)
    end,
}

return M
";
        let tree = parse("mod.lua", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "local function f()\nend\n\nfunction g()\nend\n\nlocal x = 1\n";
        let tree = parse("t.lua", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(
            kinds.iter().filter(|k| **k == node::FUNCTION).count() >= 2,
            "two function defs: {kinds:?}"
        );
        assert!(
            kinds.contains(&node::LOCAL_STMT),
            "local assignment: {kinds:?}"
        );
    }

    #[test]
    fn method_function_name_has_colon() {
        let src = "function Account:deposit(n)\n    self.balance = self.balance + n\nend\n";
        let tree = parse("t.lua", src);
        let f = tree
            .root
            .children_of(node::FUNCTION)
            .next()
            .expect("a function");
        let fname = f.child(node::FUNC_NAME).expect("a func name");
        let names: Vec<&str> = fname.tokens().map(|t| t.span.text(src)).collect();
        assert!(names.contains(&"Account"));
        assert!(names.contains(&"deposit"));
        assert!(fname.tokens().any(|t| t.span.text(src) == ":"));
    }

    #[test]
    fn control_blocks_round_trip() {
        let src = "for i = 1, 10 do\n    while i > 0 do\n        i = i - 1\n    end\nend\nrepeat\n    x = x + 1\nuntil x > 5\n";
        let tree = parse("t.lua", src);
        assert!(tree.is_lossless());
        assert!(tree.root.children_of(node::CONTROL).count() >= 2);
    }

    #[test]
    fn long_strings_and_comments_round_trip() {
        let src = "local s = [==[\nraw [[nested]] text\n]==]\n--[[ block\ncomment ]]\nreturn s\n";
        let tree = parse("t.lua", src);
        assert!(tree.is_lossless());
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let deep_brackets = format!("x = {}{}\n", "(".repeat(10_000), ")".repeat(10_000));
        let mut deep_blocks = String::new();
        for _ in 0..2_000 {
            deep_blocks.push_str("do ");
        }
        for _ in 0..2_000 {
            deep_blocks.push_str("end ");
        }
        deep_blocks.push('\n');
        for src in [deep_brackets, deep_blocks] {
            let tree = parse("deep.lua", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics.iter().any(|d| d.code == "lua.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "x = (1, 2\n",            // unterminated paren
            "s = 'unterminated\n",    // unterminated string
            "λ = '☃'  -- unicode\n",  // multi-byte identifiers/strings
            "",                       // empty file
            "\n\n   \n-- trailing\n", // only blanks and comments
            "local x = [[ open",      // unterminated long string
        ] {
            let tree = parse("edge.lua", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }

    #[test]
    fn statements_separated_by_newline() {
        // No semicolons: two calls on consecutive lines must be two statements.
        let src = "print(1)\nprint(2)\n";
        let tree = parse("t.lua", src);
        let stmts = tree.root.children_of(node::SIMPLE_STMT).count();
        assert_eq!(stmts, 2, "newline should separate the two call statements");
    }

    #[test]
    fn multiline_assignment_stays_one_statement() {
        // A trailing binary operator means the expression continues across lines.
        let src = "local x = a +\n    b\nprint(x)\n";
        let tree = parse("t.lua", src);
        let locals = tree.root.children_of(node::LOCAL_STMT).count();
        let simples = tree.root.children_of(node::SIMPLE_STMT).count();
        assert_eq!(locals, 1);
        assert_eq!(simples, 1, "the print is its own statement");
    }
}
