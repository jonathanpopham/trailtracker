//! Elixir parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust/Python/Ruby parsers: item *headers* are parsed
//! precisely — we always know a `def`'s name and signature, a `defmodule`'s
//! alias path, a `defimpl`'s protocol/`for:` header — while bodies and
//! expressions are captured as a mix of recognized sub-statements, balanced
//! delimiter groups (`Paren`/`Bracket`/`Brace`), and flat tokens, which is
//! perfectly lossless. Graph facts (calls, aliases, attributes) are read off
//! these real tokens in the lowering pass, never invented.
//!
//! Elixir blocks are delimited by `do … end` (and `fn … end` for anonymous
//! functions); statement boundaries are `newline`/`;` tokens (the lexer emits
//! `newline` as a *non-trivia* token). A `do` block may carry intermediate clause
//! keywords (`else`/`rescue`/`catch`/`after`). The keyword form `def f(x), do:
//! expr` is recognized too — its body is captured after the comma. The `do:`
//! keyword-list head is distinguished from a block-opening `do` by the colon that
//! immediately follows it.
//!
//! Anything unrecognized still lands in the tree as its exact tokens (an
//! `ErrorStmt` node or a flat run), so the result always round-trips
//! byte-for-byte. Recursion is depth-guarded at [`MAX_DEPTH`] against hostile
//! nesting (bracket and `do`/`fn` nesting) — a `catch_unwind` cannot catch a
//! stack overflow, so the guard is the real defense.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::elixir::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const PROGRAM: &str = "Program";
    pub const FUNCTION: &str = "Function";
    pub const DEFMODULE: &str = "DefModule";
    pub const DEFPROTOCOL: &str = "DefProtocol";
    pub const DEFIMPL: &str = "DefImpl";
    pub const EXPR_STMT: &str = "ExprStmt";
    pub const ERROR_STMT: &str = "ErrorStmt";

    pub const NAME: &str = "Name";
    pub const HEADER: &str = "Header";
    pub const BLOCK: &str = "Block";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat run. Mirrors the Rust/Python/Ruby parsers' guard exactly.
const MAX_DEPTH: usize = 256;

/// The `def`-family macros that introduce a function definition.
const DEF_KEYWORDS: &[&str] = &["def", "defp", "defmacro", "defmacrop"];

/// Keywords that close or continue a `do` body (a body parse stops on these,
/// leaving them for the enclosing construct to consume).
const TERMINATORS: &[&str] = &["end", "else", "rescue", "catch", "after"];

/// Intermediate clause keywords inside a `do … end` block.
const CLAUSES: &[&str] = &["else", "rescue", "catch", "after"];

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = ElixirParser {
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

struct ElixirParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> ElixirParser<'s> {
    // --- cursor primitives --------------------------------------------------

    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading **trivia** tokens into `out`. A `newline` is not
    /// trivia in Elixir, so it is left in place — statement structure needs it.
    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
        }
    }

    /// Eat statement separators — trivia, `newline`, and `;` — into `out`.
    fn skip_seps(&mut self, out: &mut Vec<Child>) {
        while let Some(t) = self.toks.get(self.i) {
            if t.trivia || t.kind == tk::NEWLINE || t.span.text(self.src) == ";" {
                self.eat(out);
            } else {
                break;
            }
        }
    }

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

    fn peek_kind_n(&self, n: usize) -> Option<&'static str> {
        self.nth_significant(n).map(|j| self.toks[j].kind)
    }

    fn peek_kind(&self) -> Option<&'static str> {
        self.peek_kind_n(0)
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

    fn at_open(&self) -> bool {
        self.at("(") || self.at("[") || self.at("{")
    }

    fn at_terminator(&self) -> bool {
        matches!(self.peek_text(), Some(t) if TERMINATORS.contains(&t))
    }

    /// True when the cursor is at a `do` that begins a block — distinguished from
    /// the `do:` keyword-list head (a `do` immediately followed by `:`).
    fn at_block_do(&self) -> bool {
        self.at("do") && self.peek_n_text(1) != Some(":")
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
            // A stray terminator (e.g. an unmatched `end`) at top level: wrap it
            // as an `ErrorStmt` and consume one token to guarantee progress.
            let mut e = Vec::new();
            self.eat(&mut e);
            c.push(Child::Node(self.make_node(node::ERROR_STMT, e)));
        }
        self.make_node(node::PROGRAM, c)
    }

    fn parse_statements(&mut self, into: &mut Vec<Child>) {
        loop {
            self.skip_seps(into);
            if self.peek_kind().is_none() || self.at_terminator() {
                break;
            }
            let before = self.i;
            let stmt = self.parse_statement();
            into.push(Child::Node(stmt));
            // Progress guard: a statement must always consume at least one token.
            if self.i == before {
                self.eat(into);
            }
        }
    }

    // --- statements ---------------------------------------------------------

    fn parse_statement(&mut self) -> Node {
        match self.peek_text() {
            Some("defmodule") => self.finish_module(node::DEFMODULE),
            Some("defprotocol") => self.finish_module(node::DEFPROTOCOL),
            Some("defimpl") => self.finish_module(node::DEFIMPL),
            Some(k) if DEF_KEYWORDS.contains(&k) => self.finish_def(),
            _ => self.finish_expr_stmt(),
        }
    }

    /// `def NAME(args) [when guard] do … end`, `def NAME(args), do: expr`.
    fn finish_def(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // def/defp/defmacro/defmacrop
        let name = self.parse_def_name();
        c.push(Child::Node(name));
        if let Some(h) = self.collect_header(true) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at_block_do() {
            self.eat(&mut c); // do
            self.parse_block_body(&mut c);
        } else if self.at(",") {
            // Keyword form: `, do: expr` (and any trailing `, else: …`).
            let blk = self.collect_kw_block();
            c.push(Child::Node(blk));
            self.consume_line_end(&mut c);
        } else {
            self.consume_line_end(&mut c);
        }
        self.make_node(node::FUNCTION, c)
    }

    /// `defmodule NAME do … end`, `defprotocol NAME do … end`,
    /// `defimpl PROTO, for: TYPE do … end`.
    fn finish_module(&mut self, kind: &'static str) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // defmodule/defprotocol/defimpl
        let name = self.parse_name_path();
        c.push(Child::Node(name));
        // Header captures the `defimpl … , for: TYPE` clause (no comma stop).
        if let Some(h) = self.collect_header(false) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at_block_do() {
            self.eat(&mut c); // do
            self.parse_block_body(&mut c);
        } else if self.at(",") {
            let blk = self.collect_kw_block();
            c.push(Child::Node(blk));
            self.consume_line_end(&mut c);
        } else {
            self.consume_line_end(&mut c);
        }
        self.make_node(kind, c)
    }

    fn finish_expr_stmt(&mut self) -> Node {
        let mut c = Vec::new();
        self.collect_expr_line(&mut c);
        self.consume_line_end(&mut c);
        self.make_node(node::EXPR_STMT, c)
    }

    // --- name parsing -------------------------------------------------------

    /// The defined function name — the first significant token after `def`
    /// (`foo`, `foo?`, an operator like `+`). The argument list is left for the
    /// header.
    fn parse_def_name(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        if let Some(t) = self.toks.get(self.i) {
            if !t.trivia && t.span.text(self.src) != "(" {
                self.eat(&mut c);
            }
        }
        self.make_node(node::NAME, c)
    }

    /// An alias path used as a module/protocol/impl name: `Foo`, `Foo.Bar.Baz`.
    fn parse_name_path(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        if matches!(self.toks.get(self.i), Some(t) if t.trivia) {
            return self.make_node(node::NAME, c);
        }
        if self.toks.get(self.i).is_some() {
            self.eat(&mut c);
        }
        loop {
            let is_connector = matches!(
                self.toks.get(self.i),
                Some(t) if !t.trivia && matches!(t.span.text(self.src), "." | "::")
            );
            if !is_connector {
                break;
            }
            self.eat(&mut c); // . or ::
            if matches!(self.toks.get(self.i), Some(t) if !t.trivia) {
                self.eat(&mut c);
            }
        }
        self.make_node(node::NAME, c)
    }

    // --- headers / lines ----------------------------------------------------

    /// Collect a header (signature / `for:` clause) up to a block-opening `do`,
    /// the logical line end, or `;`. When `comma_stop` is set, a top-level `,`
    /// (the start of a `, do:` keyword form) also stops collection. Descends into
    /// balanced groups so commas inside `(...)` stay in the header.
    fn collect_header(&mut self, comma_stop: bool) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            match self.peek_kind() {
                None => break,
                Some(k) if k == tk::NEWLINE => break,
                _ if self.at(";") => break,
                _ if comma_stop && self.at(",") => break,
                _ if self.at_block_do() => break,
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

    /// Collect a `, do: expr[, else: …]` keyword body up to the logical line end
    /// into a `Block` node (descending into groups), so the lowering can scan it
    /// for calls just like a `do … end` body.
    fn collect_kw_block(&mut self) -> Node {
        let mut c = Vec::new();
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
                    } else if self.at("fn") {
                        self.eat(&mut c); // fn
                        self.parse_fn_block(&mut c);
                    } else {
                        self.eat(&mut c);
                    }
                }
            }
        }
        self.make_node(node::BLOCK, c)
    }

    /// Consume trailing trivia and a single `newline`/`;` statement terminator.
    fn consume_line_end(&mut self, c: &mut Vec<Child>) {
        self.ws(c);
        if self.peek_kind() == Some(tk::NEWLINE) || self.at(";") {
            self.eat(c);
        }
    }

    /// Collect an expression up to the logical line end (a `newline`/`;` at
    /// bracket depth 0), descending into balanced groups, `fn … end` anonymous
    /// functions, and value-position `do … end` blocks (`if c do … end`).
    fn collect_expr_line(&mut self, c: &mut Vec<Child>) {
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
                        continue;
                    }
                    if self.at("fn") {
                        self.eat(c); // fn
                        self.parse_fn_block(c);
                        continue;
                    }
                    if self.at_block_do() {
                        self.eat(c); // do
                        self.parse_block_body(c);
                        continue;
                    }
                    self.eat(c);
                }
            }
        }
    }

    // --- blocks (do/fn … end) -----------------------------------------------

    /// Parse a `do` body (the `do` already eaten): one or more sub-bodies split by
    /// `else`/`rescue`/`catch`/`after` clauses, closed by `end`. Children are
    /// appended directly into `c`.
    fn parse_block_body(&mut self, c: &mut Vec<Child>) {
        self.consume_line_end(c);
        loop {
            let body = self.parse_body();
            c.push(Child::Node(body));
            self.ws(c);
            let nxt = self.peek_text().map(|s| s.to_string());
            match nxt.as_deref() {
                Some("end") => {
                    self.eat(c);
                    break;
                }
                Some(k) if CLAUSES.contains(&k) => {
                    self.eat(c); // else/rescue/catch/after
                    self.consume_line_end(c);
                }
                _ => break, // EOF / unterminated; still lossless
            }
        }
    }

    /// Parse an `fn … end` anonymous function body (the `fn` already eaten). The
    /// clause heads (`args ->`) parse as ordinary statements; closed by `end`.
    fn parse_fn_block(&mut self, c: &mut Vec<Child>) {
        let body = self.parse_body();
        c.push(Child::Node(body));
        self.ws(c);
        if self.at("end") {
            self.eat(c);
        }
    }

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
        let mut c = Vec::new();
        self.parse_statements(&mut c);
        let block = self.make_node(node::BLOCK, c);
        self.depth -= 1;
        block
    }

    /// At the depth cap, swallow a body as a flat token run, tracking `do`/`fn` …
    /// `end` balance so the matching terminator is left for the caller.
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

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`. Depth-guarded.
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

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "elixir.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; region flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }
}

/// Keywords that open an `end`-block, used by the depth-cap flat scanner.
fn is_block_opener(text: &str) -> bool {
    matches!(text, "do" | "fn")
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
defmodule Geo.Point do
  @moduledoc \"\"\"
  A 2-D point.
  \"\"\"
  @enforce_keys [:x, :y]
  defstruct [:x, :y]

  alias Geo.Vector
  import Enum, only: [map: 2]
  require Logger

  @spec norm(t) :: float
  def norm(%{x: x, y: y}) do
    :math.sqrt(x * x + y * y)
  end

  def origin, do: %Geo.Point{x: 0, y: 0}

  def scale(p, k) do
    %{p | x: p.x * k, y: p.y * k}
  rescue
    e -> Logger.error(e)
  end
end

defprotocol Drawable do
  def draw(shape)
end

defimpl Drawable, for: Geo.Point do
  def draw(p), do: render(p)
end

result =
  [1, 2, 3]
  |> Enum.map(fn n -> n * 2 end)
  |> Enum.sum()
";
        let tree = parse("geo.ex", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "defmodule M do\n  def f do\n  end\nend\n\ndef g, do: 1\n";
        let tree = parse("t.ex", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::DEFMODULE), "defmodule: {kinds:?}");
        assert!(kinds.contains(&node::FUNCTION), "def: {kinds:?}");
    }

    #[test]
    fn defs_nest_inside_module_bodies() {
        let src = "defmodule C do\n  def a do\n  end\n  def b do\n  end\nend\n";
        let tree = parse("t.ex", src);
        let module = tree
            .root
            .children_of(node::DEFMODULE)
            .next()
            .expect("a defmodule node");
        let block = module.child(node::BLOCK).expect("module has a block");
        let defs: Vec<&str> = block
            .children_of(node::FUNCTION)
            .filter_map(|f| f.child(node::NAME))
            .filter_map(|n| n.tokens().next())
            .map(|t| t.span.text(src))
            .collect();
        assert_eq!(defs, vec!["a", "b"]);
    }

    #[test]
    fn keyword_form_def_has_no_end() {
        let src = "def square(x), do: x * x\nz = 1\n";
        let tree = parse("t.ex", src);
        assert_eq!(tree.root.children_of(node::FUNCTION).count(), 1);
        assert!(tree.is_lossless());
    }

    #[test]
    fn fn_block_and_do_block_round_trip() {
        let src = "x = if a do\n  fn y -> y end\nelse\n  0\nend\n";
        let tree = parse("t.ex", src);
        assert!(tree.is_lossless());
    }

    #[test]
    fn defimpl_with_for_clause() {
        let src = "defimpl String.Chars, for: MyType do\n  def to_string(v), do: v.name\nend\n";
        let tree = parse("t.ex", src);
        let imp = tree
            .root
            .children_of(node::DEFIMPL)
            .next()
            .expect("a defimpl node");
        assert!(imp.child(node::HEADER).is_some(), "for: clause is a header");
        assert!(tree.is_lossless());
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let deep_brackets = format!("x = {}{}\n", "(".repeat(10_000), ")".repeat(10_000));
        let mut deep_blocks = String::new();
        for _ in 0..2_000 {
            deep_blocks.push_str("if x do\n");
        }
        for _ in 0..2_000 {
            deep_blocks.push_str("end\n");
        }
        for src in [deep_brackets, deep_blocks] {
            let tree = parse("deep.ex", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics
                    .iter()
                    .any(|d| d.code == "elixir.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn edge_inputs_round_trip() {
        for src in [
            "x = (1, 2\n",                          // unterminated paren
            "λ = \"☃\"  # unicode\n",               // multi-byte
            "",                                     // empty
            "\n\n   \n# trailing\n",                // blanks + comment
            "end\ndefmodule C do\nend\n",           // stray leading end
            "h = \"\"\"\n  unterminated heredoc\n", // unterminated heredoc
            "@doc \"x\"\ndef f, do: ~w[a b c]\n",
        ] {
            let tree = parse("edge.ex", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }

    #[test]
    fn output_is_deterministic() {
        let src = "defmodule C do\n  def m do\n    helper()\n  end\nend\n\ndef helper do\nend\n";
        let a = parse("m.ex", src);
        let b = parse("m.ex", src);
        assert_eq!(a.root, b.root, "parse output must be identical across runs");
    }
}
