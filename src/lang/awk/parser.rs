//! AWK parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Bash parser: definition *headers* are parsed precisely —
//! we always recognize a `function name(args) { … }` definition and a
//! `pattern { action }` rule — while pattern expressions and action bodies are
//! captured as flat runs of the real, lossless tokens (with brace blocks parsed
//! recursively so the structure is depth-guarded). Graph facts (the function's
//! name, the calls inside its body) are read off those real tokens in the
//! lowering pass, never invented.
//!
//! An AWK program is a sequence of items separated by newlines / `;`:
//!   - function definitions: `function name(p1, p2) { … }` (also gawk `func`);
//!   - rules: an optional pattern (`BEGIN`, `END`, `/regex/`, an expression, or a
//!     `e1, e2` range) followed by an optional `{ action }` block. A bare pattern
//!     (no action) and a bare action (no pattern) are both legal.
//!
//! Anything unrecognized still lands in the tree as its exact tokens, so the
//! result always round-trips byte-for-byte. Brace recursion is depth-guarded at
//! [`MAX_DEPTH`]: beyond the cap a block is consumed as a flat balanced run with a
//! `depth_limit` diagnostic, because a `catch_unwind` cannot catch a stack
//! overflow — the guard is the real defense.

#![allow(clippy::while_let_loop)] // loop borrow shape; style-only

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::awk::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const PROGRAM: &str = "Program";
    pub const FUNCTION: &str = "Function";
    pub const NAME: &str = "Name";
    pub const PARAMS: &str = "Params";
    pub const RULE: &str = "Rule";
    pub const PATTERN: &str = "Pattern";
    /// A `{ … }` brace block (a rule's action or a function body, and any nested
    /// block). All of a body's calls are read off the leaf tokens here.
    pub const BLOCK: &str = "Block";
    pub const ERROR_ITEM: &str = "ErrorItem";
}

/// Maximum brace-nesting depth before the parser stops recursing and consumes the
/// remainder of a block as a flat balanced run. Mirrors the Rust/Bash guard.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = AwkParser {
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

struct AwkParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current brace-recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> AwkParser<'s> {
    // --- cursor primitives --------------------------------------------------

    /// Append the current token (trivia or not) to `out` and advance.
    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading **trivia** tokens (whitespace, comments, line
    /// continuations) into `out`. A `newline` is *not* trivia, so it is left in
    /// place — it separates items / statements.
    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
        }
    }

    /// Eat trivia plus item separators (newlines and `;`) into `out`. Leaves the
    /// cursor on the next real item token or end of input.
    fn eat_separators(&mut self, out: &mut Vec<Child>) {
        loop {
            self.ws(out);
            match self.cur() {
                Some(t) if t.kind == tk::NEWLINE => self.eat(out),
                Some(t) if t.span.text(self.src) == ";" => self.eat(out),
                _ => break,
            }
        }
    }

    /// The current raw token (including trivia), if any.
    fn cur(&self) -> Option<&Token> {
        self.toks.get(self.i)
    }

    /// Text of the next significant (non-trivia) token from the cursor.
    fn peek_text(&self) -> Option<&str> {
        let mut j = self.i;
        while let Some(t) = self.toks.get(j) {
            if t.trivia {
                j += 1;
                continue;
            }
            return Some(t.span.text(self.src));
        }
        None
    }

    /// Kind of the next significant (non-trivia) token from the cursor.
    fn peek_kind(&self) -> Option<&'static str> {
        let mut j = self.i;
        while let Some(t) = self.toks.get(j) {
            if t.trivia {
                j += 1;
                continue;
            }
            return Some(t.kind);
        }
        None
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

    // --- top level ----------------------------------------------------------

    fn parse_program(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.eat_separators(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            let before = self.i;
            let item = self.parse_item();
            c.push(Child::Node(item));
            // Main-loop progress guard: parse_item always consumes a token, but if
            // it ever did not we would force progress here rather than spin.
            if self.i == before {
                let mut e = Vec::new();
                self.eat(&mut e);
                c.push(Child::Node(self.make_node(node::ERROR_ITEM, e)));
            }
        }
        self.make_node(node::PROGRAM, c)
    }

    /// Parse one program item: a function definition or a rule.
    fn parse_item(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        match self.peek_text() {
            Some("function") | Some("func") => self.finish_function(c),
            _ => self.finish_rule(c),
        }
    }

    // --- function definitions ----------------------------------------------

    /// `function name(params) { body }` (also gawk `func`).
    fn finish_function(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // `function` / `func`
        self.ws(&mut c);
        if self.peek_kind() == Some(tk::IDENT) {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        self.ws(&mut c);
        if self.at("(") {
            let p = self.params_node();
            c.push(Child::Node(p));
        }
        // The body may be preceded by newlines.
        self.eat_fillers(&mut c);
        if self.at("{") {
            let body = self.parse_block();
            c.push(Child::Node(body));
        }
        self.make_node(node::FUNCTION, c)
    }

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // the name ident
        self.make_node(node::NAME, c)
    }

    /// Capture a `( … )` parameter list as a flat token run (params are simple
    /// `ident` / `,` sequences; no nesting). Always consumes the matching `)` if
    /// present.
    fn params_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // `(`
        loop {
            match self.cur() {
                None => break,
                Some(t) => {
                    let is_close = !t.trivia && t.span.text(self.src) == ")";
                    self.eat(&mut c);
                    if is_close {
                        break;
                    }
                }
            }
        }
        self.make_node(node::PARAMS, c)
    }

    /// Eat trivia plus newlines (but not `;`) into `out`, for the gap between a
    /// function header and its `{` body.
    fn eat_fillers(&mut self, out: &mut Vec<Child>) {
        loop {
            self.ws(out);
            match self.cur() {
                Some(t) if t.kind == tk::NEWLINE => self.eat(out),
                _ => break,
            }
        }
    }

    // --- rules --------------------------------------------------------------

    /// A `pattern { action }` rule. Either part may be absent (a bare pattern, or
    /// a bare action). Guaranteed to consume at least one token.
    fn finish_rule(&mut self, mut c: Vec<Child>) -> Node {
        // Pattern: everything up to (but not including) a top-level `{`, `;`, or a
        // newline. Parentheses / brackets are balanced so a `;`-free expression is
        // captured whole.
        if !self.at("{") {
            let pat = self.collect_pattern();
            if pat.iter().any(is_significant) {
                let n = self.make_node(node::PATTERN, pat);
                c.push(Child::Node(n));
            } else {
                // Only trivia (shouldn't happen after eat_separators) — keep it.
                c.extend(pat);
            }
        }
        if self.at("{") {
            let action = self.parse_block();
            c.push(Child::Node(action));
        }
        self.make_node(node::RULE, c)
    }

    /// Collect the raw tokens of a pattern expression up to a top-level `{`, `;`,
    /// or newline, tracking `()`/`[]` nesting. Includes interleaved trivia.
    fn collect_pattern(&mut self) -> Vec<Child> {
        let mut out = Vec::new();
        let mut paren: i32 = 0;
        while let Some(t) = self.toks.get(self.i) {
            if !t.trivia {
                let txt = t.span.text(self.src);
                if t.kind == tk::NEWLINE {
                    break;
                }
                if paren == 0 && (txt == "{" || txt == ";") {
                    break;
                }
                match txt {
                    "(" | "[" => paren += 1,
                    ")" | "]" => {
                        if paren > 0 {
                            paren -= 1;
                        }
                    }
                    _ => {}
                }
            }
            self.eat(&mut out);
        }
        out
    }

    // --- brace blocks -------------------------------------------------------

    /// Parse a `{ … }` block (rule action / function body / nested block),
    /// recursing into inner blocks. Depth-guarded: beyond [`MAX_DEPTH`] the block
    /// is consumed as a flat balanced run with a `depth_limit` diagnostic.
    fn parse_block(&mut self) -> Node {
        if self.depth >= MAX_DEPTH {
            let mut c = Vec::new();
            self.consume_block_flat(&mut c);
            self.note_depth_limit();
            return self.make_node(node::BLOCK, c);
        }
        self.depth += 1;
        let mut c = Vec::new();
        self.ws(&mut c);
        if self.at("{") {
            self.eat(&mut c); // `{`
        }
        loop {
            let t = match self.toks.get(self.i) {
                Some(t) => t,
                None => break,
            };
            if t.trivia {
                self.eat(&mut c);
                continue;
            }
            let txt = t.span.text(self.src);
            if txt == "}" {
                self.eat(&mut c);
                break;
            }
            if txt == "{" {
                let inner = self.parse_block();
                c.push(Child::Node(inner));
                continue;
            }
            self.eat(&mut c);
        }
        self.depth -= 1;
        self.make_node(node::BLOCK, c)
    }

    /// At the depth cap, swallow a `{ … }` block as a flat token run, balancing
    /// the braces without recursing.
    fn consume_block_flat(&mut self, out: &mut Vec<Child>) {
        self.ws(out);
        if self.at("{") {
            self.eat(out); // `{`
        }
        let mut bal: i32 = 1;
        while let Some(t) = self.toks.get(self.i) {
            if !t.trivia {
                match t.span.text(self.src) {
                    "{" => bal += 1,
                    "}" => {
                        bal -= 1;
                        self.eat(out);
                        if bal == 0 {
                            break;
                        }
                        continue;
                    }
                    _ => {}
                }
            }
            self.eat(out);
        }
    }

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "awk.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; region flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }
}

fn is_significant(c: &Child) -> bool {
    match c {
        Child::Node(_) => true,
        Child::Token(t) => !t.trivia,
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
#!/usr/bin/awk -f
# word-count
BEGIN { FS = \",\"; total = 0 }

/^#/ { next }        # skip comments

$1 ~ /^[0-9]+$/ {
    total += $1
    count[$2]++
}

function report(n,    i) {
    for (i in count)
        printf(\"%s: %d\\n\", i, count[i])
    return n
}

END {
    print \"total =\", total
    report(total)
}
";
        let tree = parse("wc.awk", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_function_definitions() {
        let src = "function add(a, b) { return a + b }\nfunc mul(a, b) { return a * b }\n";
        let tree = parse("t.awk", src);
        let fns: Vec<&str> = tree
            .root
            .children_of(node::FUNCTION)
            .filter_map(|f| f.child(node::NAME))
            .filter_map(|n| n.tokens().next())
            .map(|t| t.span.text(src))
            .collect();
        assert_eq!(fns, vec!["add", "mul"]);
    }

    #[test]
    fn rules_carry_patterns_and_actions() {
        let src = "BEGIN { x = 1 }\n/foo/ { print }\nEND { print x }\n";
        let tree = parse("t.awk", src);
        let rules = tree.root.children_of(node::RULE).count();
        assert_eq!(rules, 3, "BEGIN, /foo/, END");
        // Every rule has an action block.
        for r in tree.root.children_of(node::RULE) {
            assert!(r.child(node::BLOCK).is_some(), "rule has an action block");
        }
    }

    #[test]
    fn bare_pattern_and_bare_action() {
        let src = "/only-pattern/\n{ print }\n";
        let tree = parse("t.awk", src);
        let rules: Vec<&Node> = tree.root.children_of(node::RULE).collect();
        assert_eq!(rules.len(), 2);
        assert!(rules[0].child(node::PATTERN).is_some());
        assert!(rules[0].child(node::BLOCK).is_none());
        assert!(rules[1].child(node::PATTERN).is_none());
        assert!(rules[1].child(node::BLOCK).is_some());
        assert!(tree.is_lossless());
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let mut deep = String::from("BEGIN ");
        deep.push_str(&"{ ".repeat(5_000));
        deep.push_str("print 1");
        deep.push_str(&" }".repeat(5_000));
        deep.push('\n');
        let tree = parse("deep.awk", &deep);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics.iter().any(|d| d.code == "awk.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }

    #[test]
    fn edge_cases_round_trip() {
        for src in [
            "x = \"oops\n",        // unterminated string
            "λ = 1\n",             // non-ASCII identifier byte → error token
            "",                    // empty file
            "\n\n   \n# c\n",      // only blanks + comment
            "{ a / b }\n",         // division inside an action
            "x ~ /re/ { y }\n",    // regex pattern
            "function f(){f()}\n", // self-reference, no spaces
        ] {
            let tree = parse("edge.awk", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
