//! Prolog parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust/Elixir/Erlang parsers: form *headers* are parsed
//! precisely — we always know a clause's head functor and argument list, and a
//! directive's neck (`:-` / `?-`) — while clause/directive bodies are captured as
//! a mix of balanced delimiter groups (`Paren`/`Bracket`/`Brace`) and flat tokens,
//! which is perfectly lossless. Graph facts (calls, imports, exports) are read off
//! these real tokens in the lowering pass, never invented.
//!
//! Prolog structure: a source file is a sequence of **forms**, each terminated by
//! an end token (the lexer flags the clause-terminating lone `.` distinctly from
//! the list/dict/functor `.` and from a `.` inside a float). A form is either a
//! **directive** (`:- Goal.` or `?- Goal.`) or a **clause** — a fact `head.` or a
//! rule `head :- body.` / a DCG rule `head --> body.`. Unlike Erlang there is no
//! `;`-separated multi-clause form: each clause is its own form, and the lowering
//! groups clauses sharing a predicate name/arity into one `Function`.
//!
//! Anything unrecognized still lands in the tree as its exact tokens (an
//! `ErrorForm` node), so the result always round-trips byte-for-byte. Recursion is
//! depth-guarded at [`MAX_DEPTH`] against hostile nesting — a `catch_unwind`
//! cannot catch a stack overflow, so the guard is the real defense.
//!
//! Known shape limitation (honest): a clause head written in operator notation
//! (e.g. `X =:= Y :- …`, a leading-variable or symbolic-operator head) is not
//! recognized as a clause head and lands in an `ErrorForm` (still lossless). The
//! canonical `pred(Args)` / `pred` head form is what the lowering reads.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::prolog::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    /// A clause: a fact (`head.`) or a rule (`head :- body.` / `head --> body.`).
    pub const CLAUSE: &str = "Clause";
    /// A directive (`:- Goal.` / `?- Goal.`).
    pub const DIRECTIVE: &str = "Directive";
    pub const ERROR_FORM: &str = "ErrorForm";

    pub const NAME: &str = "Name";
    pub const PARAMS: &str = "Params";
    pub const BODY: &str = "Body";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat run. Mirrors the Rust/Elixir/Erlang parsers' guard exactly.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = PrologParser {
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

struct PrologParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> PrologParser<'s> {
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
        self.nth_significant(0).map(|j| self.toks[j].kind)
    }

    fn peek_text(&self) -> Option<&str> {
        self.nth_significant(0)
            .map(|j| self.toks[j].span.text(self.src))
    }

    fn at(&self, s: &str) -> bool {
        self.peek_text() == Some(s)
    }

    fn at_open(&self) -> bool {
        self.at("(") || self.at("[") || self.at("{")
    }

    fn at_end(&self) -> bool {
        self.peek_kind() == Some(tk::END)
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
        if self.at(":-") || self.at("?-") {
            self.parse_directive()
        } else if self.peek_kind() == Some(tk::ATOM) {
            self.parse_clause()
        } else {
            self.parse_error_form()
        }
    }

    // --- directives ---------------------------------------------------------

    /// `:- Goal.` / `?- Goal.` — the neck token is kept as a leaf; the goal region
    /// becomes the `Body`.
    fn parse_directive(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // :- / ?-
        if let Some(body) = self.collect_body() {
            c.push(Child::Node(body));
        }
        self.ws(&mut c);
        if self.at_end() {
            self.eat(&mut c);
        }
        self.make_node(node::DIRECTIVE, c)
    }

    // --- clauses ------------------------------------------------------------

    /// `head [(:- | -->) body] .` — the head functor is `Name`; `Params` gives the
    /// arity; `Body` (present only for a rule / DCG) is where the lowering scans
    /// calls. The neck operator (`:-` / `-->`) is kept as a leaf so the lowering
    /// can tell a fact from a rule and a rule from a DCG.
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
        self.ws(&mut c);
        if self.at(":-") || self.at("-->") {
            self.eat(&mut c); // neck
            if let Some(body) = self.collect_body() {
                c.push(Child::Node(body));
            }
        }
        self.ws(&mut c);
        if self.at_end() {
            self.eat(&mut c);
        }
        self.make_node(node::CLAUSE, c)
    }

    fn parse_error_form(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            if self.peek_kind().is_none() || self.at_end() {
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
        if self.at_end() {
            self.eat(&mut c);
        }
        self.diags.push(Diagnostic {
            code: "prolog.unrecognized_form",
            message: "token(s) not recognized as a Prolog clause or directive".to_string(),
            span: children_span(&c).unwrap_or_else(|| ByteSpan::empty_at(self.cur_offset())),
        });
        self.make_node(node::ERROR_FORM, c)
    }

    // --- shared collectors --------------------------------------------------

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.eat(&mut c); // the head atom (cursor is at it after caller ws)
        self.make_node(node::NAME, c)
    }

    /// Collect a clause/directive body: every token up to the end token (or EOF)
    /// at depth 0, descending into balanced `()`/`[]`/`{}` groups. Returns `None`
    /// when nothing was collected (e.g. a directive whose end token is immediate).
    fn collect_body(&mut self) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            if self.peek_kind().is_none() || self.at_end() {
                break;
            }
            if self.at_open() {
                let g = self.parse_delimited();
                c.push(Child::Node(g));
            } else {
                self.eat(&mut c);
            }
        }
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(node::BODY, c))
        }
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
            code: "prolog.depth_limit",
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
:- module(lists_demo, [append/3, last/2]).
:- use_module(library(lists)).

append([], L, L).
append([H|T], L, [H|R]) :-
    append(T, L, R).

last([X], X) :- !.
last([_|T], X) :- last(T, X).

greeting --> [hello], name, [!].

?- append([1], [2], X).
";
        let tree = parse("lists_demo.pl", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_forms() {
        let src = ":- module(m, []).\nfoo(a).\nbar(X) :- foo(X).\n";
        let tree = parse("m.pl", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::DIRECTIVE), "directive: {kinds:?}");
        assert_eq!(
            tree.root.children_of(node::CLAUSE).count(),
            2,
            "two clauses: {kinds:?}"
        );
    }

    #[test]
    fn fact_rule_and_dcg_are_clauses() {
        let src = "f(a).\nr(X) :- g(X).\nd --> [t].\n";
        let tree = parse("c.pl", src);
        assert_eq!(tree.root.children_of(node::CLAUSE).count(), 3);
        // The rule and DCG carry a Body; the fact does not.
        let bodies = tree
            .root
            .children_of(node::CLAUSE)
            .filter(|c| c.child(node::BODY).is_some())
            .count();
        assert_eq!(bodies, 2, "rule and DCG have bodies, fact does not");
        assert!(tree.is_lossless());
    }

    #[test]
    fn end_token_inside_args_does_not_split() {
        // The interior `.` is a float, not an end token; one clause results.
        let src = "area(R, A) :- A is 3.14159 * R * R.\n";
        let tree = parse("a.pl", src);
        assert_eq!(tree.root.children_of(node::CLAUSE).count(), 1);
        assert!(tree.is_lossless());
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let depth = 10_000;
        let src = format!("f :- {}{}.\n", "(".repeat(depth), ")".repeat(depth));
        let tree = parse("deep.pl", &src);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics
                .iter()
                .any(|d| d.code == "prolog.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }

    #[test]
    fn edge_inputs_round_trip() {
        for src in [
            "",
            "\n\n  % only a comment\n",
            "f :- (1, 2.\n",           // unterminated paren
            "λ('☃').  % unicode\n",    // multi-byte
            "garbage @ tokens here\n", // no end token, error form
            ":- dynamic foo/1.\n",     // directive without parens around goal
            "X =.. [f, a, b].\n",      // univ operator vs end token
            ".(a, b).\n",              // cons functor dot vs terminator
        ] {
            let tree = parse("edge.pl", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }

    #[test]
    fn output_is_deterministic() {
        let src = ":- module(m, []).\nf(X) :- g(X).\ng(ok).\n";
        let a = parse("m.pl", src);
        let b = parse("m.pl", src);
        assert_eq!(a.root, b.root, "parse output must be identical across runs");
    }
}
