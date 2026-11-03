//! Nix parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust and Lua parsers: the analytically important
//! *structure* is parsed precisely — attribute-set scopes, `let … in` binding
//! groups, and each `name = value;` binding with its attribute path — while
//! expression *values* are captured as a flat `Value` region containing balanced
//! token-tree groups (`Paren`/`List`/`AttrSet`). Graph facts (bindings, lambdas,
//! imports, calls) are extracted from these real tokens in the lowering pass,
//! never invented.
//!
//! Nix is a single-expression functional language: a file is one expression,
//! usually an attribute set, a `let … in` form, or a function
//! (`{ pkgs, ... }: …`). Bindings only occur inside attribute sets and `let`
//! forms, so those are the only two places this parser looks for them.
//!
//! Two genuine grammar hazards are handled explicitly:
//! - A leading `{` is ambiguous: it opens either an attribute set or a lambda's
//!   formal-argument set (`{ a, b ? x }: body`). We disambiguate by scanning to
//!   the matching `}` and checking whether the next significant token is `:` or
//!   `@` (the lambda markers).
//! - A binding's value runs to a `;`, but `with e;` and `assert e;` introduce a
//!   `;` that is *not* a terminator. The value collector tracks those pending
//!   separators and only stops at the genuine terminating `;`; nested `let … in`
//!   forms consume their own internal `;`.
//!
//! Anything unrecognized still lands in the tree as its exact tokens, so the
//! result always round-trips. Recursion is depth-guarded at [`MAX_DEPTH`] — a
//! `catch_unwind` cannot catch a stack overflow, so the guard is the real defense
//! against hostile nesting.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::nix::lexer::{kind as tk, lex};

/// CST node-kind labels. The lowering interprets these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    /// `let bindings in` (the body follows as sibling tokens, not nested here).
    pub const LET: &str = "Let";
    /// `{ … }` or `rec { … }` attribute set holding bindings.
    pub const ATTR_SET: &str = "AttrSet";
    /// `[ … ]` list.
    pub const LIST: &str = "List";
    /// `( … )` parenthesized expression.
    pub const PAREN: &str = "Paren";
    /// A lambda header: a formals set `{ … }` plus optional `@ name` and the `:`.
    pub const LAMBDA: &str = "Lambda";
    /// The `{ … }` formal-argument set of a lambda.
    pub const FORMALS: &str = "Formals";
    /// `attrpath = value ;`.
    pub const BINDING: &str = "Binding";
    /// `inherit [ ( expr ) ] names ;`.
    pub const INHERIT: &str = "Inherit";
    /// The dotted attribute path on the left of a binding's `=`.
    pub const ATTR_PATH: &str = "AttrPath";
    /// The right-hand-side expression region of a binding.
    pub const VALUE: &str = "Value";
    pub const ERROR_ITEM: &str = "ErrorItem";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat run. Mirrors the Rust/Lua parsers' guard exactly.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = NixParser {
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

struct NixParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> NixParser<'s> {
    // --- cursor primitives --------------------------------------------------

    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
        }
    }

    fn flush(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() {
            self.eat(out);
        }
    }

    fn peek_kind(&self) -> Option<&'static str> {
        let mut j = self.i;
        while j < self.toks.len() && self.toks[j].trivia {
            j += 1;
        }
        self.toks.get(j).map(|t| t.kind)
    }

    fn peek_text(&self) -> Option<&str> {
        let mut j = self.i;
        while j < self.toks.len() && self.toks[j].trivia {
            j += 1;
        }
        self.toks.get(j).map(|t| t.span.text(self.src))
    }

    fn at(&self, s: &str) -> bool {
        self.peek_text() == Some(s)
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
            code: "nix.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; region flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }

    // --- top level ----------------------------------------------------------

    /// A Nix file is one expression. We parse it as an expression region with no
    /// terminating `;`, recognizing the structural forms and keeping everything
    /// else as flat tokens.
    fn parse_source_file(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            match self.peek_text() {
                None => break,
                Some("let") => c.push(Child::Node(self.parse_let())),
                Some("rec") => c.push(Child::Node(self.parse_attrset())),
                Some("{") => c.push(Child::Node(self.parse_brace())),
                Some("[") => c.push(Child::Node(self.parse_group("]", node::LIST))),
                Some("(") => c.push(Child::Node(self.parse_group(")", node::PAREN))),
                Some(_) => self.eat(&mut c),
            }
        }
        self.flush(&mut c);
        self.make_node(node::SOURCE_FILE, c)
    }

    // --- bindings -----------------------------------------------------------

    /// `let bindings in`. The body after `in` is left to the caller's region (it
    /// is not nested inside the `Let` node), which keeps the parser simple and
    /// lossless without a full expression grammar.
    fn parse_let(&mut self) -> Node {
        if self.depth >= MAX_DEPTH {
            let mut c = Vec::new();
            self.ws(&mut c);
            self.eat(&mut c); // let
            loop {
                self.ws(&mut c);
                match self.peek_text() {
                    None => break,
                    Some("in") => {
                        self.eat(&mut c);
                        break;
                    }
                    Some(_) => self.eat(&mut c),
                }
            }
            self.note_depth_limit();
            return self.make_node(node::LET, c);
        }
        self.depth += 1;
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // let
        loop {
            self.ws(&mut c);
            match self.peek_text() {
                None => break,
                Some("in") => {
                    self.eat(&mut c);
                    break;
                }
                Some("}") => break, // defensive: stray close
                Some(_) => {
                    let before = self.i;
                    let b = self.parse_binding();
                    c.push(Child::Node(b));
                    if self.i == before {
                        self.eat(&mut c); // progress guard
                    }
                }
            }
        }
        let node = self.make_node(node::LET, c);
        self.depth -= 1;
        node
    }

    /// `{ … }` or `rec { … }` attribute set of bindings.
    fn parse_attrset(&mut self) -> Node {
        if self.depth >= MAX_DEPTH {
            let mut c = Vec::new();
            self.ws(&mut c);
            if self.at("rec") {
                self.eat(&mut c);
                self.ws(&mut c);
            }
            if self.at("{") {
                self.eat(&mut c);
                self.consume_balanced_flat(&mut c);
            }
            self.note_depth_limit();
            return self.make_node(node::ATTR_SET, c);
        }
        self.depth += 1;
        let mut c = Vec::new();
        self.ws(&mut c);
        if self.at("rec") {
            self.eat(&mut c);
            self.ws(&mut c);
        }
        if self.at("{") {
            self.eat(&mut c);
        } else {
            // Defensive: a `rec` not followed by `{`. Return what we have rather
            // than risk over-consuming the rest of the file.
            self.depth -= 1;
            return self.make_node(node::ATTR_SET, c);
        }
        loop {
            self.ws(&mut c);
            match self.peek_text() {
                None => break,
                Some("}") => {
                    self.eat(&mut c);
                    break;
                }
                Some(_) => {
                    let before = self.i;
                    let b = self.parse_binding();
                    c.push(Child::Node(b));
                    if self.i == before {
                        self.eat(&mut c); // progress guard
                    }
                }
            }
        }
        let node = self.make_node(node::ATTR_SET, c);
        self.depth -= 1;
        node
    }

    /// Decide whether a `{` opens lambda formals or an attribute set, then parse
    /// the right one.
    fn parse_brace(&mut self) -> Node {
        if self.brace_is_formals() {
            self.parse_lambda()
        } else {
            self.parse_attrset()
        }
    }

    /// Lookahead: from the current `{`, scan to the matching `}` and report
    /// whether the next significant token is a lambda marker (`:` or `@`).
    fn brace_is_formals(&self) -> bool {
        let mut j = self.i;
        while j < self.toks.len() && self.toks[j].trivia {
            j += 1;
        }
        if self.toks.get(j).map(|t| t.span.text(self.src)) != Some("{") {
            return false;
        }
        let mut depth = 0i32;
        let mut k = j;
        while k < self.toks.len() {
            let t = &self.toks[k];
            if t.trivia {
                k += 1;
                continue;
            }
            match t.span.text(self.src) {
                "{" => depth += 1,
                "}" => {
                    depth -= 1;
                    if depth == 0 {
                        let mut m = k + 1;
                        while m < self.toks.len() && self.toks[m].trivia {
                            m += 1;
                        }
                        return matches!(
                            self.toks.get(m).map(|t| t.span.text(self.src)),
                            Some(":") | Some("@")
                        );
                    }
                }
                _ => {}
            }
            k += 1;
        }
        false
    }

    /// A lambda header: the `{ … }` formals, an optional `@ name`, and the `:`.
    /// The body follows as sibling tokens in the enclosing region.
    fn parse_lambda(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        c.push(Child::Node(self.parse_group("}", node::FORMALS)));
        self.ws(&mut c);
        if self.at("@") {
            self.eat(&mut c);
            self.ws(&mut c);
            if self.peek_kind() == Some(tk::IDENT) {
                self.eat(&mut c);
            }
            self.ws(&mut c);
        }
        if self.at(":") {
            self.eat(&mut c);
        }
        self.make_node(node::LAMBDA, c)
    }

    /// One binding inside an attribute set or `let`: either `inherit …;` or
    /// `attrpath = value ;`.
    fn parse_binding(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        if self.at("inherit") {
            return self.parse_inherit();
        }
        c.push(Child::Node(self.parse_attrpath()));
        self.ws(&mut c);
        if self.at("=") {
            self.eat(&mut c);
            c.push(Child::Node(self.parse_value()));
            self.ws(&mut c);
            if self.at(";") {
                self.eat(&mut c);
            }
        } else if self.at(";") {
            self.eat(&mut c); // stray / empty
        } else if self.peek_text().is_some() {
            // Malformed binding: consume one token so the enclosing loop advances.
            self.eat(&mut c);
        }
        self.make_node(node::BINDING, c)
    }

    /// `inherit [ ( expr ) ] name* ;`.
    fn parse_inherit(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // inherit
        self.ws(&mut c);
        if self.at("(") {
            c.push(Child::Node(self.parse_group(")", node::PAREN)));
        }
        loop {
            self.ws(&mut c);
            match self.peek_text() {
                None => break,
                Some(";") => {
                    self.eat(&mut c);
                    break;
                }
                Some("}") | Some("in") => break,
                Some(_) => self.eat(&mut c),
            }
        }
        self.make_node(node::INHERIT, c)
    }

    /// The dotted attribute path before `=`: identifiers, string keys, and `.`
    /// separators. Stops (without consuming) at `=`/`;`/`}`/`in` or any token
    /// that cannot be part of a path (e.g. a dynamic `${…}` attr, which we punt).
    fn parse_attrpath(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            match self.peek_text() {
                None => break,
                Some("=") | Some(";") | Some("}") | Some("in") => break,
                Some(".") => self.eat(&mut c),
                Some(_) => {
                    if matches!(
                        self.peek_kind(),
                        Some(tk::IDENT) | Some(tk::STRING) | Some(tk::INDENTED_STRING)
                    ) {
                        self.eat(&mut c);
                    } else {
                        break;
                    }
                }
            }
        }
        self.make_node(node::ATTR_PATH, c)
    }

    /// A binding's right-hand-side expression region, collected up to the
    /// terminating `;` (left unconsumed for the caller). `with`/`assert`
    /// separators and nested `let … in` `;`s are handled so they do not end the
    /// value early.
    fn parse_value(&mut self) -> Node {
        let mut c = Vec::new();
        let mut pending = 0usize; // unmatched with/assert separators
        loop {
            self.ws(&mut c);
            match self.peek_text() {
                None => break,
                Some(";") => {
                    if pending > 0 {
                        pending -= 1;
                        self.eat(&mut c);
                    } else {
                        break; // the terminator — caller consumes it
                    }
                }
                // Defensive: an unbalanced close means the enclosing scope ended.
                Some("}") | Some(")") | Some("]") | Some("in") => break,
                Some("with") | Some("assert") => {
                    pending += 1;
                    self.eat(&mut c);
                }
                Some("let") => c.push(Child::Node(self.parse_let())),
                Some("rec") => c.push(Child::Node(self.parse_attrset())),
                Some("{") => c.push(Child::Node(self.parse_brace())),
                Some("[") => c.push(Child::Node(self.parse_group("]", node::LIST))),
                Some("(") => c.push(Child::Node(self.parse_group(")", node::PAREN))),
                Some(_) => self.eat(&mut c),
            }
        }
        self.make_node(node::VALUE, c)
    }

    // --- delimited groups ---------------------------------------------------

    /// Parse a balanced group `( … )`, `[ … ]`, or formals `{ … }`. The cursor is
    /// at (or before trivia preceding) the opener.
    fn parse_group(&mut self, close: &str, label: &'static str) -> Node {
        if self.depth >= MAX_DEPTH {
            let mut c = Vec::new();
            self.ws(&mut c);
            self.eat(&mut c); // opener
            self.consume_balanced_flat(&mut c);
            self.note_depth_limit();
            return self.make_node(label, c);
        }
        self.depth += 1;
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // opener
        loop {
            self.ws(&mut c);
            match self.peek_text() {
                None => break, // unterminated; still lossless
                Some(t) if t == close => {
                    self.eat(&mut c);
                    break;
                }
                Some("let") => c.push(Child::Node(self.parse_let())),
                Some("rec") => c.push(Child::Node(self.parse_attrset())),
                Some("{") => c.push(Child::Node(self.parse_brace())),
                Some("[") => c.push(Child::Node(self.parse_group("]", node::LIST))),
                Some("(") => c.push(Child::Node(self.parse_group(")", node::PAREN))),
                Some(_) => self.eat(&mut c),
            }
        }
        let node = self.make_node(label, c);
        self.depth -= 1;
        node
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
                Some(_) => {}
            }
            self.eat(out);
        }
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
# a flake-ish module
{ pkgs, lib, ... }:

let
  version = \"1.2.3\";
  greet = name: \"hello ${name}\";
  helper = x: x + 1;
in
{
  name = \"demo\";
  inherit version;
  deps = [ pkgs.hello pkgs.cowsay ];
  build = pkgs.stdenv.mkDerivation {
    pname = \"demo\";
    nested = rec {
      a = 1;
      b = a + 1;
    };
  };
}
";
        let tree = parse("default.nix", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_bindings() {
        let src = "{ a = 1; b = x: x; }";
        let tree = parse("t.nix", src);
        let set = tree
            .root
            .child_nodes()
            .find(|n| n.kind == node::ATTR_SET)
            .expect("an attr set");
        let bindings = set.children_of(node::BINDING).count();
        assert_eq!(bindings, 2);
    }

    #[test]
    fn formals_vs_attrset_disambiguation() {
        // `{ pkgs }: body` is a lambda; `{ a = 1; }` is an attr set.
        let lam = parse("a.nix", "{ pkgs }: pkgs");
        assert!(lam.root.walk().any(|n| n.kind == node::LAMBDA));
        let set = parse("b.nix", "{ a = 1; }");
        assert!(set.root.walk().any(|n| n.kind == node::ATTR_SET));
        assert!(!set.root.walk().any(|n| n.kind == node::LAMBDA));
    }

    #[test]
    fn with_and_assert_semicolons_do_not_end_value() {
        let src = "{ x = with pkgs; assert cond; [ a b ]; y = 2; }";
        let tree = parse("t.nix", src);
        let set = tree
            .root
            .child_nodes()
            .find(|n| n.kind == node::ATTR_SET)
            .expect("attr set");
        // Both bindings must survive: the `;` after `with`/`assert` are not the
        // binding terminator.
        assert_eq!(set.children_of(node::BINDING).count(), 2);
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        // Deep braces and deep parens, far beyond MAX_DEPTH.
        let depth = 10_000;
        let mut braces = String::new();
        for _ in 0..depth {
            braces.push_str("{ a = ");
        }
        braces.push_str("1;");
        for _ in 0..depth {
            braces.push('}');
        }
        let mut parens = String::from("x = ");
        for _ in 0..depth {
            parens.push('(');
        }
        for _ in 0..depth {
            parens.push(')');
        }
        for src in [braces, parens] {
            let tree = parse("deep.nix", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics.iter().any(|d| d.code == "nix.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "{ a = (1 + 2",          // unterminated paren
            "\"open ${ x",           // unterminated interpolation
            "λ = \"☃\"; # unicode",  // multi-byte
            "",                      // empty
            "\n\n  # only trivia\n", // trivia only
            "rec",                   // bare keyword
        ] {
            let tree = parse("edge.nix", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
