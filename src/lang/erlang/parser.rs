//! Erlang parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust/Elixir parsers: form *headers* are parsed precisely
//! — we always know a function clause's name and parameter list, an attribute's
//! name (`-module`, `-export`, `-record`, `-define`, …), and a record/type name —
//! while clause bodies and expressions are captured as a mix of balanced
//! delimiter groups (`Paren`/`Bracket`/`Brace`) and flat tokens, which is
//! perfectly lossless. Graph facts (calls, record uses, attribute targets) are
//! read off these real tokens in the lowering pass, never invented.
//!
//! Erlang structure: a source file is a sequence of **forms**, each terminated by
//! a `dot` token (the lexer flags clause-terminating `.` distinctly from record
//! access). A form is either an **attribute** (`-name(...).`) or a **function**
//! (one or more clauses `name(Params) [when Guard] -> Body` separated by `;`).
//! Function clauses are split on `;` / `->` only at *block depth 0*: the
//! `case`/`if`/`receive`/`try`/`begin`/`maybe`/anonymous-`fun` … `end` blocks
//! (which also use `;` and `->` internally) are tracked with a depth counter so a
//! `;` inside a `case` is never mistaken for a clause separator.
//!
//! Anything unrecognized still lands in the tree as its exact tokens (an
//! `ErrorForm` node), so the result always round-trips byte-for-byte. Recursion is
//! depth-guarded at [`MAX_DEPTH`] against hostile nesting — a `catch_unwind`
//! cannot catch a stack overflow, so the guard is the real defense.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::erlang::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const FUNCTION: &str = "Function";
    pub const ATTRIBUTE: &str = "Attribute";
    pub const ERROR_FORM: &str = "ErrorForm";

    pub const CLAUSE: &str = "Clause";
    pub const NAME: &str = "Name";
    pub const PARAMS: &str = "Params";
    pub const GUARD: &str = "Guard";
    pub const BODY: &str = "Body";
    pub const ARGS: &str = "Args";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat run. Mirrors the Rust/Elixir parsers' guard exactly.
const MAX_DEPTH: usize = 256;

/// Keywords that open an `end`-terminated block (and so own any `;` / `->`
/// appearing inside them). `fun` is handled separately (it may be a reference
/// `fun f/1` with no `end`).
const BLOCK_OPENERS: &[&str] = &["case", "if", "receive", "try", "begin", "maybe"];

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = ErlangParser {
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

struct ErlangParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> ErlangParser<'s> {
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

    fn peek_kind(&self) -> Option<&'static str> {
        self.peek_kind_n(0)
    }

    fn peek_kind_n(&self, n: usize) -> Option<&'static str> {
        self.nth_significant(n).map(|j| self.toks[j].kind)
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

    fn at_dot(&self) -> bool {
        self.peek_kind() == Some(tk::DOT)
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

    fn parse_source_file(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c); // inter-form trivia lives directly under the file
            if self.peek_kind().is_none() {
                break;
            }
            let before = self.i;
            let form = self.parse_form();
            c.push(Child::Node(form));
            // Progress guard: a form must always consume at least one token.
            if self.i == before {
                self.eat(&mut c);
            }
        }
        self.make_node(node::SOURCE_FILE, c)
    }

    fn parse_form(&mut self) -> Node {
        if self.at("-") {
            self.parse_attribute()
        } else if self.peek_kind() == Some(tk::ATOM) {
            self.parse_function()
        } else {
            self.parse_error_form()
        }
    }

    // --- attributes ---------------------------------------------------------

    /// `-name(...).`, `-name.`, `-type t() :: ...`, `-spec f(...) -> ...`.
    fn parse_attribute(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // -
        self.ws(&mut c);
        if self.peek_kind() == Some(tk::ATOM) {
            let name = self.name_node();
            c.push(Child::Node(name));
        }
        // Everything up to the clause `dot` is the attribute argument region.
        if let Some(args) = self.collect_segment(node::ARGS, &[], false) {
            c.push(Child::Node(args));
        }
        self.ws(&mut c);
        if self.at_dot() {
            self.eat(&mut c);
        }
        self.make_node(node::ATTRIBUTE, c)
    }

    // --- functions ----------------------------------------------------------

    /// One function form: clause (`;` clause)* `dot`. All clauses share the same
    /// name/arity, so the whole form lowers to a single `Function`.
    fn parse_function(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            let before = self.i;
            let clause = self.parse_clause();
            c.push(Child::Node(clause));
            if self.i == before {
                // Defensive progress guard.
                self.eat(&mut c);
            }
            self.ws(&mut c);
            if self.at(";") {
                self.eat(&mut c); // clause separator
                continue;
            }
            break;
        }
        self.ws(&mut c);
        if self.at_dot() {
            self.eat(&mut c);
        }
        self.make_node(node::FUNCTION, c)
    }

    /// `name(Params) [when Guard] -> Body`. The clause head name is the function
    /// name; `Params` gives the arity; `Body` is where the lowering scans calls.
    fn parse_clause(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        if self.peek_kind() == Some(tk::ATOM) {
            let name = self.name_node();
            c.push(Child::Node(name));
        }
        self.ws(&mut c);
        if self.at("(") {
            let params = self.parse_delimited_as(node::PARAMS);
            c.push(Child::Node(params));
        }
        // Guard region: everything up to the clause `->` (or a `;`/`dot` if the
        // clause is malformed / has no arrow).
        if let Some(g) = self.collect_segment(node::GUARD, &[";"], true) {
            c.push(Child::Node(g));
        }
        self.ws(&mut c);
        if self.at("->") {
            self.eat(&mut c); // ->
            if let Some(b) = self.collect_segment(node::BODY, &[";"], false) {
                c.push(Child::Node(b));
            }
        }
        self.make_node(node::CLAUSE, c)
    }

    fn parse_error_form(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            if self.peek_kind().is_none() || self.at_dot() {
                break;
            }
            if self.at_open() {
                let g = self.parse_delimited();
                c.push(Child::Node(g));
            } else {
                self.eat(&mut c);
            }
        }
        self.ws(&mut c);
        if self.at_dot() {
            self.eat(&mut c);
        }
        self.diags.push(Diagnostic {
            code: "erlang.unrecognized_form",
            message: "token(s) not recognized as an Erlang form".to_string(),
            span: children_span(&c).unwrap_or_else(|| ByteSpan::empty_at(self.cur_offset())),
        });
        self.make_node(node::ERROR_FORM, c)
    }

    // --- shared collectors --------------------------------------------------

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.eat(&mut c); // the leading atom (cursor is at it after caller ws)
        self.make_node(node::NAME, c)
    }

    /// Collect a token region, descending into balanced `()`/`[]`/`{}` groups and
    /// tracking `end`-block depth, until — *at block depth 0* — a `dot`, a stop
    /// text, or (when `stop_arrow`) a top-level `->` is reached. Returns `None`
    /// when nothing was collected (e.g. a guardless clause whose `->` is immediate).
    fn collect_segment(
        &mut self,
        label: &'static str,
        stops: &[&str],
        stop_arrow: bool,
    ) -> Option<Node> {
        let mut c = Vec::new();
        let mut block_depth: i32 = 0;
        loop {
            self.ws(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            if block_depth == 0 {
                if self.at_dot() {
                    break;
                }
                if let Some(t) = self.peek_text() {
                    if stops.contains(&t) || (stop_arrow && t == "->") {
                        break;
                    }
                }
            }
            if self.at_open() {
                let g = self.parse_delimited();
                c.push(Child::Node(g));
                continue;
            }
            // Track `end`-block nesting so inner `;` / `->` are not stop tokens.
            if let Some(t) = self.peek_text() {
                if t == "end" {
                    if block_depth > 0 {
                        block_depth -= 1;
                    }
                } else if self.is_block_opener_here(t) {
                    block_depth += 1;
                }
            }
            self.eat(&mut c);
        }
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(label, c))
        }
    }

    /// Whether the keyword at the cursor opens an `end`-block. `fun` opens one only
    /// when it is an anonymous/named `fun … end`, not a `fun f/1` reference.
    fn is_block_opener_here(&self, text: &str) -> bool {
        if BLOCK_OPENERS.contains(&text) {
            return true;
        }
        if text == "fun" {
            return !self.fun_is_reference();
        }
        false
    }

    /// Heuristic: a `fun` at the cursor is a *reference* (`fun f/1`, `fun M:f/2`,
    /// no `end`) if a `/` followed by an integer appears before any `(`, `->`,
    /// `end`, `;`, or `dot`. Otherwise it is an anonymous/named `fun … end`.
    fn fun_is_reference(&self) -> bool {
        let mut k = 1;
        let mut saw_slash = false;
        while k <= 8 {
            let kind = self.peek_kind_n(k);
            match self.peek_n_text(k) {
                None => return false,
                Some("(") | Some("->") | Some("end") | Some(";") => return false,
                Some("/") => saw_slash = true,
                _ => {
                    if saw_slash {
                        return kind == Some(tk::INT);
                    }
                }
            }
            if kind == Some(tk::DOT) {
                return false;
            }
            k += 1;
        }
        false
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`. Depth-guarded.
    fn parse_delimited(&mut self) -> Node {
        let label = match self.peek_text() {
            Some("(") => node::PAREN,
            Some("[") => node::BRACKET,
            Some("{") => node::BRACE,
            _ => node::ERROR_FORM,
        };
        self.parse_delimited_as(label)
    }

    /// As [`parse_delimited`] but with a caller-chosen label (e.g. `Params`).
    fn parse_delimited_as(&mut self, label: &'static str) -> Node {
        let mut g = Vec::new();
        self.ws(&mut g);
        let close = if self.at("(") {
            ")"
        } else if self.at("[") {
            "]"
        } else if self.at("{") {
            "}"
        } else {
            return self.make_node(label, g);
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
    /// deep nesting is handled without further recursion.
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
            code: "erlang.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; group flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
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
%% a module
-module(geo).
-export([norm/1, scale/2]).
-import(math, [sqrt/1]).
-record(point, {x = 0, y = 0}).
-define(PI, 3.14159).

norm(#point{x = X, y = Y}) ->
    sqrt(X * X + Y * Y).

scale(P, K) when K > 0 ->
    case P of
        #point{x = X, y = Y} -> #point{x = X * K, y = Y * K};
        _ -> P
    end;
scale(P, _) ->
    P.

run() ->
    F = fun(N) -> N * 2 end,
    lists:map(F, [1, 2, 3]).
";
        let tree = parse("geo.erl", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_forms() {
        let src = "-module(m).\nf() -> ok.\ng(X) -> X.\n";
        let tree = parse("m.erl", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::ATTRIBUTE), "attribute: {kinds:?}");
        assert_eq!(
            tree.root.children_of(node::FUNCTION).count(),
            2,
            "two functions: {kinds:?}"
        );
    }

    #[test]
    fn multi_clause_function_is_one_node() {
        let src = "fac(0) -> 1;\nfac(N) -> N * fac(N - 1).\n";
        let tree = parse("f.erl", src);
        assert_eq!(tree.root.children_of(node::FUNCTION).count(), 1);
        let f = tree.root.children_of(node::FUNCTION).next().unwrap();
        assert_eq!(f.children_of(node::CLAUSE).count(), 2, "two clauses");
        assert!(tree.is_lossless());
    }

    #[test]
    fn case_semicolons_do_not_split_clauses() {
        // The `;` inside the `case` belongs to the case, not the function.
        let src = "f(X) ->\n    case X of\n        1 -> a;\n        2 -> b\n    end.\n";
        let tree = parse("c.erl", src);
        let f = tree.root.children_of(node::FUNCTION).next().unwrap();
        assert_eq!(f.children_of(node::CLAUSE).count(), 1, "single clause");
        assert!(tree.is_lossless());
    }

    #[test]
    fn fun_reference_is_not_a_block() {
        let src = "f() -> Fn = fun lists:map/2, Fn.\n";
        let tree = parse("r.erl", src);
        assert!(tree.is_lossless());
        let f = tree.root.children_of(node::FUNCTION).next().unwrap();
        assert_eq!(f.children_of(node::CLAUSE).count(), 1);
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let depth = 10_000;
        let src = format!("f() -> {}{}.\n", "(".repeat(depth), ")".repeat(depth));
        let tree = parse("deep.erl", &src);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics
                .iter()
                .any(|d| d.code == "erlang.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }

    #[test]
    fn edge_inputs_round_trip() {
        for src in [
            "",
            "\n\n  % only a comment\n",
            "f() -> (1, 2.\n",         // unterminated paren
            "λ = \"☃\".  % unicode\n", // multi-byte
            "garbage tokens here\n",   // no dot, error form
            "-endif.\n-else.\n",       // paren-less attributes
            "f() -> X#rec.field.\n",   // record access dot vs terminator
        ] {
            let tree = parse("edge.erl", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }

    #[test]
    fn output_is_deterministic() {
        let src = "-module(m).\nf() -> g().\ng() -> ok.\n";
        let a = parse("m.erl", src);
        let b = parse("m.erl", src);
        assert_eq!(a.root, b.root, "parse output must be identical across runs");
    }
}
