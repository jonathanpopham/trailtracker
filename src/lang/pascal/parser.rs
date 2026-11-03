//! Object Pascal / Delphi parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Julia and Lua parsers (Pascal is likewise keyword-block
//! delimited, not whitespace-significant): definition *headers* are parsed
//! precisely — we always know a routine's signature, a type's name and ancestor,
//! a unit's name — while bodies and member regions are captured as balanced
//! `begin … end` / `record … end` blocks (plus `(…)` / `[…]` groups), which is
//! perfectly lossless. Graph facts (calls, type uses, imports, methods) are
//! extracted from these real tokens in the lowering pass, never invented.
//!
//! Pascal blocks open with a keyword and close with `end`:
//! `begin … end`, `case … end`, `try … [except|finally] … end`, `asm … end`
//! (statement bodies), and `record`/`class`/`object`/`interface`/`dispinterface`
//! … `end` (type definitions). `repeat … until` and `if … then … else` have no
//! `end` and are kept as flat tokens inside whatever block contains them. A
//! variant-record `case … of` has no `end` of its own (it is closed by the
//! record's `end`), so `case` is an opener only in statement bodies, never in a
//! type definition — the two block contexts use different opener sets.
//!
//! Pascal is case-insensitive, so every keyword test here is case-insensitive
//! ([`crate::lang::pascal::lexer::is_keyword`] and the `*_lc` cursor helpers).
//!
//! Anything unrecognized still lands in the tree as its exact tokens, so the
//! result always round-trips. Recursion is depth-guarded at [`MAX_DEPTH`] against
//! hostile nesting (deep `begin` blocks *or* deep brackets) — a `catch_unwind`
//! cannot catch a stack overflow, so the guard is the real defense.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::pascal::lexer::{is_keyword, kind as tk, lex};

/// CST node-kind labels. The lowering interprets these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    /// `program`/`library`/`unit`/`package` header.
    pub const MODULE_DECL: &str = "ModuleDecl";
    /// `interface`/`implementation`/`initialization`/`finalization` marker.
    pub const SECTION: &str = "Section";
    pub const USES: &str = "Uses";
    pub const TYPE_SECTION: &str = "TypeSection";
    pub const TYPE_DECL: &str = "TypeDecl";
    pub const CONST_SECTION: &str = "ConstSection";
    pub const CONST_DECL: &str = "ConstDecl";
    pub const VAR_SECTION: &str = "VarSection";
    pub const VAR_DECL: &str = "VarDecl";
    pub const LABEL_DECL: &str = "LabelDecl";
    /// `procedure`/`function`/`constructor`/`destructor`/`operator`.
    pub const ROUTINE: &str = "Routine";
    pub const BEGIN_BLOCK: &str = "BeginBlock";
    pub const ASM_BLOCK: &str = "AsmBlock";
    /// A standalone `end` / `end.` / `end;` terminator.
    pub const TERMINATOR: &str = "Terminator";
    pub const SIMPLE_STMT: &str = "SimpleStmt";
    pub const ERROR_STMT: &str = "ErrorStmt";
    pub const DIRECTIVE: &str = "Directive";

    pub const HEADER: &str = "Header";
    pub const BLOCK: &str = "Block";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat balanced run. Mirrors the Rust/Julia/Lua guard exactly.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = PascalParser {
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

/// Which keywords open an `… end` block. Statement bodies and type definitions
/// have different opener sets (see the module note on variant-record `case`).
#[derive(Clone, Copy, PartialEq)]
enum BlockCtx {
    Body,
    Type,
}

impl BlockCtx {
    fn is_opener(self, kw: &str) -> bool {
        match self {
            BlockCtx::Body => matches!(kw, "begin" | "case" | "try" | "asm"),
            BlockCtx::Type => {
                matches!(
                    kw,
                    "record" | "class" | "object" | "interface" | "dispinterface"
                )
            }
        }
    }
}

struct PascalParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    depth: usize,
}

impl<'s> PascalParser<'s> {
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

    fn peek_text_n(&self, n: usize) -> Option<&str> {
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
        self.peek_text_n(0)
    }

    fn peek_kind(&self) -> Option<&'static str> {
        let mut count = 0;
        for t in &self.toks[self.i..] {
            if t.trivia {
                continue;
            }
            if count == 0 {
                return Some(t.kind);
            }
            count += 1;
        }
        None
    }

    fn peek_lc_n(&self, n: usize) -> Option<String> {
        self.peek_text_n(n).map(|s| s.to_ascii_lowercase())
    }

    fn peek_lc(&self) -> Option<String> {
        self.peek_lc_n(0)
    }

    /// Exact (case-sensitive) match — used for punctuation.
    fn at(&self, s: &str) -> bool {
        self.peek_text() == Some(s)
    }

    /// Case-insensitive keyword match.
    fn at_kw(&self, kw: &str) -> bool {
        self.peek_text()
            .map(|t| t.eq_ignore_ascii_case(kw))
            .unwrap_or(false)
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

    /// `ws` then consume `kw` (case-insensitive) if present; otherwise record a
    /// recoverable diagnostic and leave the cursor in place (bytes are never
    /// dropped — the surrounding context consumes them).
    fn eat_keyword(&mut self, out: &mut Vec<Child>, kw: &'static str) {
        self.ws(out);
        if self.at_kw(kw) {
            self.eat(out);
        } else {
            self.diags.push(Diagnostic {
                code: "pascal.missing_keyword",
                message: format!("expected '{kw}'"),
                span: ByteSpan::empty_at(self.cur_offset()),
            });
        }
    }

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "pascal.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; region flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }

    /// Is `class`/`object` actually a block opener here, or a modifier/reference
    /// such as `class procedure`, `class var`, or `class of T`?
    fn opener_confirmed(&self, kw: &str) -> bool {
        match kw {
            "class" | "object" => !matches!(
                self.peek_lc_n(1).as_deref(),
                Some("of")
                    | Some("procedure")
                    | Some("function")
                    | Some("constructor")
                    | Some("destructor")
                    | Some("operator")
                    | Some("property")
                    | Some("var")
                    | Some("const")
                    | Some("threadvar")
                    | Some(";")
            ),
            _ => true,
        }
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
                Some(_) => {
                    let before = self.i;
                    let s = self.parse_statement();
                    c.push(Child::Node(s));
                    if self.i == before {
                        // Defensive: guarantee forward progress.
                        let mut ec = Vec::new();
                        self.eat(&mut ec);
                        if !ec.is_empty() {
                            c.push(Child::Node(self.make_node(node::ERROR_STMT, ec)));
                        } else {
                            break;
                        }
                    }
                }
            }
        }
        self.make_node(node::SOURCE_FILE, c)
    }

    fn parse_statement(&mut self) -> Node {
        match self.peek_lc().as_deref() {
            Some("program") | Some("library") | Some("unit") | Some("package") => {
                self.finish_module_decl()
            }
            Some("interface")
            | Some("implementation")
            | Some("initialization")
            | Some("finalization") => self.finish_section(),
            Some("uses") => self.finish_uses(),
            Some("type") => self.finish_type_section(),
            Some("const") | Some("resourcestring") => self.finish_const_section(),
            Some("var") | Some("threadvar") => self.finish_var_section(),
            Some("label") => self.finish_label(),
            Some("procedure") | Some("function") | Some("constructor") | Some("destructor")
            | Some("operator") => self.finish_routine(),
            Some("begin") => self.finish_begin_block(),
            Some("asm") => self.finish_asm_block(),
            Some("end") => self.finish_terminator(),
            Some(";") => self.finish_semi(),
            _ => self.finish_simple(),
        }
    }

    // --- block parsing ------------------------------------------------------

    /// Parse a block: tokens until the matching `end` (not consumed — the caller
    /// owns it) or EOF. Nested openers (`begin`/`case`/`try`/`asm` in a body;
    /// `record`/`class`/… in a type) are recursed so their own `end` does not
    /// close the outer block. Depth-guarded.
    fn parse_block(&mut self, ctx: BlockCtx) -> Node {
        if self.depth >= MAX_DEPTH {
            let mut c = Vec::new();
            self.consume_block_flat(&mut c, ctx);
            self.note_depth_limit();
            return self.make_node(node::BLOCK, c);
        }
        self.depth += 1;
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            match self.peek_lc().as_deref() {
                None => {
                    self.flush(&mut c);
                    break;
                }
                Some("end") => break,
                Some(k) if ctx.is_opener(k) && self.opener_confirmed(k) => {
                    self.eat(&mut c); // opener keyword
                    c.push(Child::Node(self.parse_block(ctx)));
                    self.eat_keyword(&mut c, "end");
                }
                _ if self.at("(") || self.at("[") => {
                    let g = self.parse_delimited();
                    c.push(Child::Node(g));
                }
                _ => self.eat(&mut c),
            }
        }
        let block = self.make_node(node::BLOCK, c);
        self.depth -= 1;
        block
    }

    /// At the depth cap, swallow a block's contents as a flat token run with an
    /// iterative balance counter (no recursion). Stops before the matching `end`.
    fn consume_block_flat(&mut self, out: &mut Vec<Child>, ctx: BlockCtx) {
        let mut balance: i32 = 0;
        loop {
            self.ws(out);
            match self.peek_lc().as_deref() {
                None => break,
                Some("end") if balance == 0 => break,
                Some("end") => {
                    balance -= 1;
                    self.eat(out);
                }
                Some(k) if ctx.is_opener(k) && self.opener_confirmed(k) => {
                    balance += 1;
                    self.eat(out);
                }
                _ => self.eat(out),
            }
        }
    }

    /// Parse a balanced delimiter group `(...)` or `[...]`. Keywords inside are
    /// ordinary flat tokens. Depth-guarded against deep bracket nesting.
    fn parse_delimited(&mut self) -> Node {
        let mut g = Vec::new();
        self.ws(&mut g);
        let (close, label) = match self.peek_text() {
            Some("(") => (")", node::PAREN),
            Some("[") => ("]", node::BRACKET),
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

    /// Iteratively consume a balanced delimiter run (opener already eaten),
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

    /// Collect tokens (descending into `()`/`[]` groups) until a top-level `;`
    /// (consumed), a top-level `end` (left in place), or EOF.
    fn collect_to_semi(&mut self, out: &mut Vec<Child>) {
        loop {
            self.ws(out);
            match self.peek_lc().as_deref() {
                None => {
                    self.flush(out);
                    break;
                }
                Some(";") => {
                    self.eat(out);
                    break;
                }
                Some("end") => break,
                _ if self.at("(") || self.at("[") => {
                    let g = self.parse_delimited();
                    out.push(Child::Node(g));
                }
                _ => self.eat(out),
            }
        }
    }

    /// Collect a type-decl name part (descending into groups) until a top-level
    /// `=` (consumed), or a `;`/`end`/EOF boundary.
    fn collect_until_eq(&mut self, out: &mut Vec<Child>) {
        loop {
            self.ws(out);
            match self.peek_lc().as_deref() {
                None => {
                    self.flush(out);
                    break;
                }
                Some("=") => {
                    self.eat(out);
                    break;
                }
                Some(";") => break,
                Some("end") => break,
                _ if self.at("(") || self.at("[") => {
                    let g = self.parse_delimited();
                    out.push(Child::Node(g));
                }
                _ => self.eat(out),
            }
        }
    }

    // --- statement finishers ------------------------------------------------

    /// `program`/`unit`/`library`/`package Name[(...)] ;`.
    fn finish_module_decl(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // keyword
        self.collect_to_semi(&mut c);
        self.make_node(node::MODULE_DECL, c)
    }

    /// A lone `interface`/`implementation`/`initialization`/`finalization`.
    fn finish_section(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c);
        self.make_node(node::SECTION, c)
    }

    /// `uses A, B, C in 'C.pas';`.
    fn finish_uses(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // uses
        self.collect_to_semi(&mut c);
        self.make_node(node::USES, c)
    }

    /// `type Name = def; Name2 = def; …` — one or more declarations until the
    /// next section/routine boundary (i.e. until the next significant token is no
    /// longer a plain identifier starting a `Name = …`).
    fn finish_type_section(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // type
        loop {
            self.ws(&mut c);
            if self.at_decl_name() {
                c.push(Child::Node(self.type_decl()));
            } else {
                break;
            }
        }
        self.make_node(node::TYPE_SECTION, c)
    }

    fn type_decl(&mut self) -> Node {
        let mut c = Vec::new();
        let mut h = Vec::new();
        self.collect_until_eq(&mut h); // name part incl `=`
        c.push(Child::Node(self.make_node(node::HEADER, h)));
        self.ws(&mut c);
        if self.at_kw("packed") {
            self.eat(&mut c);
            self.ws(&mut c);
        }
        match self.peek_lc().as_deref() {
            Some(k @ ("class" | "object" | "record" | "interface" | "dispinterface")) => {
                let is_class_like = matches!(k, "class" | "object");
                self.eat(&mut c); // kind keyword
                self.ws(&mut c);
                if is_class_like && self.at_kw("of") {
                    // `class of T` metaclass reference — no member block.
                    self.collect_to_semi(&mut c);
                    return self.make_node(node::TYPE_DECL, c);
                }
                if self.at("(") {
                    let g = self.parse_delimited(); // ancestor / interface list
                    c.push(Child::Node(g));
                } else if self.at("[") {
                    let g = self.parse_delimited(); // interface GUID
                    c.push(Child::Node(g));
                }
                self.ws(&mut c);
                if self.at(";") {
                    self.eat(&mut c); // forward / empty declaration
                } else {
                    c.push(Child::Node(self.parse_block(BlockCtx::Type)));
                    self.eat_keyword(&mut c, "end");
                    self.collect_to_semi(&mut c); // trailing `;` and any directives
                }
            }
            _ => {
                // Alias / enum / pointer / array / set / procedural type.
                self.collect_to_semi(&mut c);
            }
        }
        self.make_node(node::TYPE_DECL, c)
    }

    /// `const`/`resourcestring` section: `Name = value;` / `Name: Type = value;`.
    fn finish_const_section(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // const / resourcestring
        loop {
            self.ws(&mut c);
            if self.at_decl_name() {
                let mut d = Vec::new();
                self.collect_to_semi(&mut d);
                c.push(Child::Node(self.make_node(node::CONST_DECL, d)));
            } else {
                break;
            }
        }
        self.make_node(node::CONST_SECTION, c)
    }

    /// `var`/`threadvar` section: `a, b: Type;` / `a: Type = value;`.
    fn finish_var_section(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // var / threadvar
        loop {
            self.ws(&mut c);
            if self.at_decl_name() {
                let mut d = Vec::new();
                self.collect_to_semi(&mut d);
                c.push(Child::Node(self.make_node(node::VAR_DECL, d)));
            } else {
                break;
            }
        }
        self.make_node(node::VAR_SECTION, c)
    }

    fn finish_label(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // label
        self.collect_to_semi(&mut c);
        self.make_node(node::LABEL_DECL, c)
    }

    /// `procedure`/`function`/`constructor`/`destructor`/`operator` — signature
    /// header, then directives / local sections / a `begin`|`asm` body. A routine
    /// with no body (interface signature or `forward`) stops at the next item.
    fn finish_routine(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // routine keyword
        let mut h = Vec::new();
        self.collect_to_semi(&mut h);
        c.push(Child::Node(self.make_node(node::HEADER, h)));
        loop {
            self.ws(&mut c);
            match self.peek_lc().as_deref() {
                None => break,
                Some("begin") | Some("asm") => {
                    self.eat(&mut c); // begin / asm
                    c.push(Child::Node(self.parse_block(BlockCtx::Body)));
                    self.eat_keyword(&mut c, "end");
                    self.ws(&mut c);
                    if self.at(".") || self.at(";") {
                        self.eat(&mut c);
                    }
                    break;
                }
                Some("var")
                | Some("const")
                | Some("type")
                | Some("label")
                | Some("threadvar")
                | Some("resourcestring") => {
                    c.push(Child::Node(self.parse_statement()));
                }
                Some("procedure") | Some("function") | Some("constructor") | Some("destructor")
                | Some("operator") => break,
                Some("end")
                | Some("implementation")
                | Some("interface")
                | Some("initialization")
                | Some("finalization")
                | Some("uses")
                | Some("exports") => break,
                Some(";") => self.eat(&mut c),
                _ => {
                    // A directive (`virtual; override; external '…';`).
                    let mut d = Vec::new();
                    self.collect_to_semi(&mut d);
                    if d.is_empty() {
                        self.eat(&mut c);
                    } else {
                        c.push(Child::Node(self.make_node(node::DIRECTIVE, d)));
                    }
                }
            }
        }
        self.make_node(node::ROUTINE, c)
    }

    /// A top-level `begin … end.` (a program/library main body).
    fn finish_begin_block(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // begin
        c.push(Child::Node(self.parse_block(BlockCtx::Body)));
        self.eat_keyword(&mut c, "end");
        self.ws(&mut c);
        if self.at(".") || self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::BEGIN_BLOCK, c)
    }

    fn finish_asm_block(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // asm
        c.push(Child::Node(self.parse_block(BlockCtx::Body)));
        self.eat_keyword(&mut c, "end");
        self.ws(&mut c);
        if self.at(".") || self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::ASM_BLOCK, c)
    }

    fn finish_terminator(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // end
        self.ws(&mut c);
        if self.at(".") || self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::TERMINATOR, c)
    }

    fn finish_semi(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // ;
        self.make_node(node::SIMPLE_STMT, c)
    }

    /// A fallback statement region (an initialization-section statement, an
    /// `exports` clause, or a stray run), delimited at the next top-level `;`.
    /// Always consumes at least one token so the parse loop advances.
    fn finish_simple(&mut self) -> Node {
        let mut c = Vec::new();
        self.collect_to_semi(&mut c);
        if c.is_empty() {
            self.ws(&mut c);
            self.eat(&mut c);
        }
        self.make_node(node::SIMPLE_STMT, c)
    }

    /// True when the next significant token is a plain (non-keyword) identifier —
    /// the start of a `Name = …` / `Name: …` declaration inside a type/const/var
    /// section.
    fn at_decl_name(&self) -> bool {
        self.peek_kind() == Some(tk::IDENT)
            && self.peek_text().map(|t| !is_keyword(t)).unwrap_or(false)
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
unit Geometry;

interface

uses
  SysUtils, Math;

type
  TShape = class
  public
    function Area: Double; virtual; abstract;
  end;

  TCircle = class(TShape)
  private
    FRadius: Double;
  public
    constructor Create(ARadius: Double);
    function Area: Double; override;
  end;

const
  TAU = 6.283185;

implementation

constructor TCircle.Create(ARadius: Double);
begin
  FRadius := ARadius;
end;

function TCircle.Area: Double;
begin
  Result := TAU * FRadius * FRadius / 2;
end;

procedure Describe(C: TCircle);
var
  A: Double;
begin
  A := C.Area;
  if A > 10.0 then
    WriteLn('big')
  else
    WriteLn('small');
end;

end.
";
        let tree = parse("Geometry.pas", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "unit U;\ninterface\ntype\n  TFoo = class end;\nconst K = 1;\nimplementation\nprocedure P;\nbegin\nend;\nend.\n";
        let tree = parse("u.pas", src);
        let mut kinds = std::collections::BTreeSet::new();
        for n in tree.root.walk() {
            kinds.insert(n.kind);
        }
        assert!(kinds.contains(node::MODULE_DECL), "module: {kinds:?}");
        assert!(kinds.contains(node::TYPE_DECL), "type: {kinds:?}");
        assert!(kinds.contains(node::CONST_DECL), "const: {kinds:?}");
        assert!(kinds.contains(node::ROUTINE), "routine: {kinds:?}");
    }

    #[test]
    fn class_with_members_round_trips() {
        let src =
            "type\n  TC = class(TBase)\n    procedure Foo;\n    function Bar: Integer;\n  end;\n";
        let tree = parse("c.pas", src);
        assert!(tree.is_lossless());
        let td = tree
            .root
            .walk()
            .find(|n| n.kind == node::TYPE_DECL)
            .expect("a type decl");
        assert!(td.child(node::BLOCK).is_some(), "class has a member block");
    }

    #[test]
    fn program_main_block() {
        let src = "program Hello;\nbegin\n  WriteLn('hi');\nend.\n";
        let tree = parse("hello.dpr", src);
        assert!(tree.is_lossless());
        assert!(tree.root.walk().any(|n| n.kind == node::BEGIN_BLOCK));
    }

    #[test]
    fn nested_control_blocks_round_trip() {
        let src = "procedure P;\nbegin\n  for i := 1 to 10 do\n  begin\n    case i of\n      1: WriteLn('one');\n    else\n      WriteLn('other');\n    end;\n  end;\n  try\n    Risky;\n  finally\n    Cleanup;\n  end;\nend;\n";
        let tree = parse("p.pas", src);
        assert!(tree.is_lossless());
    }

    #[test]
    fn variant_record_round_trips() {
        // The variant `case` has no `end` of its own; it is closed by the
        // record's `end`. The parser must not over-consume.
        let src = "type\n  TVar = record\n    Tag: Integer;\n    case Boolean of\n      True: (I: Integer);\n      False: (R: Real);\n  end;\n";
        let tree = parse("v.pas", src);
        assert!(tree.is_lossless());
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let deep_brackets = format!("x := {}{};\n", "(".repeat(10_000), ")".repeat(10_000));
        let mut deep_blocks = String::from("procedure P;\n");
        for _ in 0..2_000 {
            deep_blocks.push_str("begin ");
        }
        for _ in 0..2_000 {
            deep_blocks.push_str("end; ");
        }
        deep_blocks.push('\n');
        for src in [deep_brackets, deep_blocks] {
            let tree = parse("deep.pas", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics
                    .iter()
                    .any(|d| d.code == "pascal.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "x := (1, 2\n",           // unterminated paren
            "s := 'unterminated\n",   // unterminated string
            "{ unterminated comment", // unterminated block comment
            "α := 1; // unicode\n",   // multi-byte identifiers
            "",                       // empty file
            "\n\n   \n// trailing\n", // only blanks and comments
            "procedure P(\n",         // unterminated signature
            "type T = class\n",       // unterminated class
        ] {
            let tree = parse("edge.pas", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
