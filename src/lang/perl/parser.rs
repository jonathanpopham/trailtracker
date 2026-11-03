//! Perl parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust/Python/Ruby parsers: item *headers* are parsed
//! precisely — we always know a `sub`'s name, a `package`'s name, and the shape of
//! a `use`/`require` — while bodies and expressions are captured as a mix of
//! recognized sub-statements, balanced delimiter groups (`Paren`/`Bracket`), brace
//! `Block`s (parsed as nested statements so a nested `sub` is still found), and
//! flat tokens. Graph facts (calls, imports, inheritance, constants) are later
//! read off these real tokens in the lowering pass, never invented.
//!
//! Unlike Ruby, Perl blocks are brace-delimited (`{ … }`) and statements end with
//! `;`, so the parser is a straightforward brace/`;` statement splitter. Control
//! constructs (`if`/`while`/`for`/…), anonymous subs, and hash/code blocks all
//! flow through the generic expression-statement collector, which descends into
//! `()`/`[]` groups and `{}` blocks uniformly — so a named `sub` nested inside any
//! of them is discovered, and the result always round-trips byte-for-byte.
//!
//! Anything unrecognized still lands in the tree as its exact tokens (an
//! `ErrorStmt` node or a flat token run). The recursion is depth-guarded at
//! [`MAX_DEPTH`] against hostile nesting (both bracket and brace), because a
//! `catch_unwind` cannot catch a stack overflow.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::perl::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const PROGRAM: &str = "Program";
    pub const PACKAGE: &str = "Package";
    pub const SUB: &str = "Sub";
    pub const USE: &str = "Use";
    pub const BLOCK: &str = "Block";
    pub const EXPR_STMT: &str = "ExprStmt";
    pub const ERROR_STMT: &str = "ErrorStmt";

    pub const NAME: &str = "Name";
    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat run. Mirrors the Rust/Ruby/Python parsers' guard exactly,
/// since a `catch_unwind` cannot catch a stack overflow.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = PerlParser {
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

struct PerlParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    depth: usize,
}

impl<'s> PerlParser<'s> {
    // --- cursor primitives --------------------------------------------------

    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move leading **trivia** tokens (whitespace, newlines, comments, POD, data
    /// section, line continuations) into `out`.
    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
        }
    }

    /// Eat statement separators — trivia and `;` — leaving the cursor at the next
    /// real token (or end of input).
    fn skip_seps(&mut self, out: &mut Vec<Child>) {
        while let Some(t) = self.toks.get(self.i) {
            if t.trivia || t.span.text(self.src) == ";" {
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

    fn at_open_group(&self) -> bool {
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

    // --- top level ----------------------------------------------------------

    fn parse_program(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.parse_statements(&mut c);
            self.skip_seps(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            // A stray `}` (or other unexpected token) at top level: wrap as an
            // ErrorStmt and consume one token to guarantee progress.
            let mut e = Vec::new();
            self.eat(&mut e);
            c.push(Child::Node(self.make_node(node::ERROR_STMT, e)));
        }
        self.make_node(node::PROGRAM, c)
    }

    /// Parse a run of statements, stopping at a closing `}` (left for the enclosing
    /// block) or end of input.
    fn parse_statements(&mut self, into: &mut Vec<Child>) {
        loop {
            self.skip_seps(into);
            if self.peek_kind().is_none() || self.at("}") {
                break;
            }
            let before = self.i;
            let stmt = self.parse_statement();
            into.push(Child::Node(stmt));
            if self.i == before {
                // Safety: force progress so the parser can never spin.
                let mut e = Vec::new();
                self.eat(&mut e);
                into.push(Child::Node(self.make_node(node::ERROR_STMT, e)));
            }
        }
    }

    // --- statements ---------------------------------------------------------

    fn parse_statement(&mut self) -> Node {
        match self.peek_text() {
            Some("package") => self.finish_package(),
            Some("sub") if self.peek_kind_n(1) == Some(tk::IDENT) => self.finish_sub(),
            Some("use") | Some("no") | Some("require") => self.finish_use(),
            Some("{") => self.parse_block(),
            _ => self.finish_expr_stmt(),
        }
    }

    /// `package NAME;`, `package NAME VERSION;`, or `package NAME { … }`.
    fn finish_package(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // package
        let name = self.parse_name();
        c.push(Child::Node(name));
        // Optional version / trailing tokens up to `{` or `;`.
        self.collect_until_block_or_semi(&mut c);
        if self.at("{") {
            let block = self.parse_block();
            c.push(Child::Node(block));
        } else if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::PACKAGE, c)
    }

    /// `sub NAME (proto) :attrs { … }` or a forward declaration `sub NAME;`.
    fn finish_sub(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // sub
        let name = self.parse_name();
        c.push(Child::Node(name));
        // Prototype / signature / attributes — anything up to the block or `;`.
        self.collect_until_block_or_semi(&mut c);
        if self.at("{") {
            let block = self.parse_block();
            c.push(Child::Node(block));
        } else if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::SUB, c)
    }

    /// `use MODULE …;`, `no MODULE …;`, `require MODULE;`.
    fn finish_use(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // use / no / require
        self.collect_stmt_body(&mut c);
        self.make_node(node::USE, c)
    }

    /// A generic expression statement: collect a logical line up to `;`, descending
    /// into groups and brace blocks (so nested named subs are still discovered).
    fn finish_expr_stmt(&mut self) -> Node {
        let mut c = Vec::new();
        self.collect_stmt_body(&mut c);
        self.make_node(node::EXPR_STMT, c)
    }

    // --- name parsing -------------------------------------------------------

    /// A package/sub name: a single (possibly `::`-qualified) identifier token.
    fn parse_name(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        if matches!(self.toks.get(self.i), Some(t) if !t.trivia && t.kind == tk::IDENT) {
            self.eat(&mut c);
        }
        self.make_node(node::NAME, c)
    }

    // --- collectors ---------------------------------------------------------

    /// Collect tokens (and `()`/`[]` groups) up to a `{` block opener or a `;`,
    /// without consuming either. Used for `sub`/`package` headers.
    fn collect_until_block_or_semi(&mut self, c: &mut Vec<Child>) {
        loop {
            self.ws(c);
            match self.peek_kind() {
                None => break,
                _ if self.at("{") || self.at(";") || self.at("}") => break,
                _ => {
                    if self.at_open_group() {
                        let g = self.parse_delimited();
                        c.push(Child::Node(g));
                    } else {
                        self.eat(c);
                    }
                }
            }
        }
    }

    /// Collect a statement body up to (and consuming) a `;` at brace/bracket depth
    /// zero, or up to a closing `}` / EOF (left for the caller). Descends into
    /// `()`/`[]` groups and `{}` blocks.
    fn collect_stmt_body(&mut self, c: &mut Vec<Child>) {
        loop {
            self.ws(c);
            match self.peek_kind() {
                None => break,
                _ if self.at(";") => {
                    self.eat(c);
                    break;
                }
                _ if self.at("}") => break,
                _ => {
                    if self.at_open_group() {
                        let g = self.parse_delimited();
                        c.push(Child::Node(g));
                    } else if self.at("{") {
                        // A brace block at statement level (a control body, bare
                        // block, anon sub body, or hash ref) ends the statement:
                        // `if (c) { ... }` and `do { ... } while` have no trailing
                        // `;`, while `my $h = { ... };` leaves its `;` for skip_seps.
                        // Coarse but lossless; nested named subs are still found via
                        // the block's own statement parse.
                        let block = self.parse_block();
                        c.push(Child::Node(block));
                        break;
                    } else {
                        self.eat(c);
                    }
                }
            }
        }
    }

    // --- blocks / groups ----------------------------------------------------

    /// Parse a `{ … }` block as nested statements. Depth-guarded: beyond
    /// [`MAX_DEPTH`] the body is consumed as a flat balanced run rather than
    /// recursing, so deep nesting cannot overflow.
    fn parse_block(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        if !self.at("{") {
            return self.make_node(node::ERROR_STMT, c);
        }
        if self.depth >= MAX_DEPTH {
            self.eat(&mut c); // {
            self.consume_balanced_flat(&mut c, '{', '}');
            self.note_depth_limit();
            return self.make_node(node::BLOCK, c);
        }
        self.eat(&mut c); // {
        self.depth += 1;
        self.parse_statements(&mut c);
        self.depth -= 1;
        self.ws(&mut c);
        if self.at("}") {
            self.eat(&mut c);
        }
        self.make_node(node::BLOCK, c)
    }

    /// Parse a balanced `(…)` or `[…]` group as a flat run of tokens and nested
    /// groups/blocks. Depth-guarded.
    fn parse_delimited(&mut self) -> Node {
        let mut g = Vec::new();
        self.ws(&mut g);
        let (close, label, openc, closec) = if self.at("(") {
            (")", node::PAREN, '(', ')')
        } else if self.at("[") {
            ("]", node::BRACKET, '[', ']')
        } else {
            return self.make_node(node::ERROR_STMT, g);
        };
        if self.depth >= MAX_DEPTH {
            self.eat(&mut g); // opener
            self.consume_balanced_flat(&mut g, openc, closec);
            self.note_depth_limit();
            return self.make_node(label, g);
        }
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
            if self.at_open_group() {
                self.depth += 1;
                let inner = self.parse_delimited();
                self.depth -= 1;
                g.push(Child::Node(inner));
            } else if self.at("{") {
                let block = self.parse_block();
                g.push(Child::Node(block));
            } else {
                self.eat(&mut g);
            }
        }
        self.make_node(label, g)
    }

    /// Iteratively consume a balanced run (opener already eaten) at the depth cap,
    /// appending every token as a flat leaf so arbitrarily deep nesting needs no
    /// further recursion. Tracks all three bracket families.
    fn consume_balanced_flat(&mut self, out: &mut Vec<Child>, _open: char, _close: char) {
        let mut balance: i32 = 1;
        while balance > 0 {
            self.ws(out);
            match self.peek_text() {
                None => break,
                Some("(") | Some("[") | Some("{") => balance += 1,
                Some(")") | Some("]") | Some("}") => balance -= 1,
                _ => {}
            }
            if self.peek_kind().is_none() {
                break;
            }
            self.eat(out);
        }
    }

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "perl.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; region flattened"),
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
#!/usr/bin/perl
use strict;
use warnings;
use parent 'Base';

=pod
Module documentation.
=cut

package Geo::Point;

our $VERSION = '1.0';
use constant PI => 3.14159;

sub new {
    my ($class, %args) = @_;
    my $self = { x => $args{x}, y => $args{y} };
    return bless $self, $class;
}

sub norm {
    my $self = shift;
    return sqrt($self->{x} ** 2 + $self->{y} ** 2);
}

package main;

my $p = Geo::Point->new(x => 3, y => 4);
print $p->norm(), \"\\n\";

my $doc = <<~END;
    inline heredoc
    END
print $doc;

__END__
trailing data, not code
";
        let tree = parse("point.pl", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "use strict;\npackage Foo;\nsub bar { 1 }\nsub baz;\n";
        let tree = parse("t.pm", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::USE), "use not found: {kinds:?}");
        assert!(
            kinds.contains(&node::PACKAGE),
            "package not found: {kinds:?}"
        );
        assert!(kinds.contains(&node::SUB), "sub not found: {kinds:?}");
    }

    #[test]
    fn subs_nest_inside_package_blocks() {
        let src = "package P {\n  sub a { 1 }\n  sub b { 2 }\n}\n";
        let tree = parse("t.pm", src);
        let pkg = tree
            .root
            .children_of(node::PACKAGE)
            .next()
            .expect("a package node");
        let block = pkg.child(node::BLOCK).expect("package has a block");
        let subs: Vec<&str> = block
            .children_of(node::SUB)
            .filter_map(|s| s.child(node::NAME))
            .filter_map(|n| n.tokens().next())
            .map(|t| t.span.text(src))
            .collect();
        assert_eq!(subs, vec!["a", "b"]);
    }

    #[test]
    fn anonymous_sub_is_not_a_named_sub() {
        // `my $cb = sub { ... };` must not produce a top-level Sub node.
        let src = "my $cb = sub { return 1; };\nsub real { 2 }\n";
        let tree = parse("t.pl", src);
        let names: Vec<String> = tree
            .root
            .children_of(node::SUB)
            .filter_map(|s| s.child(node::NAME))
            .filter_map(|n| n.tokens().next())
            .map(|t| t.span.text(src).to_string())
            .collect();
        assert_eq!(names, vec!["real".to_string()]);
        assert!(tree.is_lossless());
    }

    #[test]
    fn nested_sub_inside_control_block_found() {
        let src = "if ($x) {\n  sub helper { 1 }\n}\n";
        let tree = parse("t.pl", src);
        let found = tree.root.walk().any(|n| {
            n.kind == node::SUB
                && n.child(node::NAME)
                    .and_then(|nm| nm.tokens().next())
                    .map(|t| t.span.text(src) == "helper")
                    .unwrap_or(false)
        });
        assert!(found, "nested sub should be discovered");
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let deep_parens = format!("my $x = {}{};\n", "(".repeat(10_000), ")".repeat(10_000));
        let deep_braces = format!("{}{}\n", "sub f { ".repeat(2_000), "}".repeat(2_000));
        for src in [deep_parens, deep_braces] {
            let tree = parse("deep.pl", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics
                    .iter()
                    .any(|d| d.code == "perl.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "sub f {\n  my $x = (1, 2\n",    // unterminated paren + block
            "my $λ = 'unicode ☃';\n",        // multi-byte identifiers/strings
            "",                              // empty file
            "\n\n   \n# trailing\n",         // only blanks and comments
            "}\npackage P;\n",               // a stray leading `}`
            "my $x = <<~SQL;\n  select 1\n", // unterminated heredoc
            "=pod\nunterminated pod\n",      // POD with no =cut
        ] {
            let tree = parse("edge.pl", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }

    #[test]
    fn output_is_deterministic() {
        let src = "package P;\nsub m { helper() }\nsub helper { 1 }\n";
        let a = parse("m.pl", src);
        let b = parse("m.pl", src);
        assert_eq!(a.root, b.root, "parse output must be identical across runs");
    }
}
