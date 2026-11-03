//! Bash parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust and Python parsers: definition *headers* are parsed
//! precisely — we always know a `function` keyword, a `name ()` definition, a
//! `{ … }` / `( … )` group, or a compound keyword block (`if … fi`, `for … done`,
//! `case … esac`) — while command lines and expression regions are captured as
//! flat runs of the real, lossless tokens. Graph facts (calls, includes,
//! assignments) are later read off those real tokens in the lowering pass, never
//! invented.
//!
//! Shell has no indentation structure; blocks are delimited by reserved words and
//! brackets. The parser recognizes:
//!   - function definitions: `name () compound` and `function name [()] compound`;
//!   - groups: `{ …; }` (command group) and `( … )` (subshell);
//!   - compound statements: `if/for/while/until/select/case …` up to their
//!     matching `fi`/`done`/`esac`;
//!   - everything else as a `Command` (one pipeline / logical line).
//!
//! Anything unrecognized still lands in the tree as its exact tokens, so the
//! result always round-trips byte-for-byte. The recursion is depth-guarded at
//! [`MAX_DEPTH`] against hostile bracket / keyword nesting, because a
//! `catch_unwind` cannot catch a stack overflow.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::bash::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const SCRIPT: &str = "Script";
    pub const FUNCTION: &str = "Function";
    pub const NAME: &str = "Name";
    pub const GROUP: &str = "Group";
    pub const COMPOUND: &str = "Compound";
    pub const COMMAND: &str = "Command";
    pub const ERROR_STMT: &str = "ErrorStmt";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat run. Mirrors the Rust/Python guard exactly — a
/// `catch_unwind` cannot catch a stack overflow, so the guard is the real
/// defense against hostile nesting.
const MAX_DEPTH: usize = 256;

/// Statement separators that act as inter-statement "filler".
const FILLER_TEXT: &[&str] = &[
    ";", "&", ";;", ";&", ";;&", "then", "do", "else", "elif", "in",
];

/// Tokens that terminate a `Command` (logical line) without being part of it.
const CMD_TERM: &[&str] = &[";", "&", ";;", ";&", ";;&"];

/// Block-closing tokens (a brace group `}`, a subshell `)`).
const CLOSERS: &[&str] = &["}", ")"];

/// Compound-statement terminator keywords.
const COMPOUND_TERM: &[&str] = &["fi", "done", "esac"];

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = BashParser {
        src: source,
        toks,
        i: 0,
        diags: Vec::new(),
        depth: 0,
    };
    let root = p.parse_script();
    ParseTree {
        source_id: SourceId::from_path(path),
        path: path.to_string(),
        source: source.to_string(),
        root,
        diagnostics: p.diags,
    }
}

/// What kind of statement begins at the cursor (an owned classification, so the
/// dispatcher never holds a borrow into the parser across its `&mut self` calls).
#[derive(Clone, Copy)]
enum Stmt {
    FunctionKw,
    FuncParen,
    Compound,
    BraceGroup,
    Subshell,
    Command,
    Empty,
}

struct BashParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> BashParser<'s> {
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
    /// place — it is a statement separator.
    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
        }
    }

    /// Eat trivia plus statement-separator "filler" (newlines, `;`, `&`, `;;`,
    /// and the structural sub-keywords `then`/`do`/`else`/`elif`/`in`) into `out`.
    /// Leaves the cursor on the next real statement token, a closer/terminator, or
    /// end of input.
    fn eat_fillers(&mut self, out: &mut Vec<Child>) {
        loop {
            self.ws(out);
            if self.peek_kind() == Some(tk::NEWLINE) {
                self.eat(out);
                continue;
            }
            let is_filler = match self.peek_text() {
                Some(t) => FILLER_TEXT.contains(&t),
                None => false,
            };
            if is_filler {
                self.eat(out);
            } else {
                break;
            }
        }
    }

    /// Kind of the n-th significant (non-trivia) token from the cursor; `newline`
    /// counts as significant.
    fn peek_kind_n(&self, n: usize) -> Option<&'static str> {
        let mut j = self.i;
        let mut count = 0;
        while j < self.toks.len() {
            if self.toks[j].trivia {
                j += 1;
                continue;
            }
            if count == n {
                return Some(self.toks[j].kind);
            }
            count += 1;
            j += 1;
        }
        None
    }

    fn peek_kind(&self) -> Option<&'static str> {
        self.peek_kind_n(0)
    }

    fn peek_n_text(&self, n: usize) -> Option<&str> {
        let mut j = self.i;
        let mut count = 0;
        while j < self.toks.len() {
            if self.toks[j].trivia {
                j += 1;
                continue;
            }
            if count == n {
                return Some(self.toks[j].span.text(self.src));
            }
            count += 1;
            j += 1;
        }
        None
    }

    fn peek_text(&self) -> Option<&str> {
        self.peek_n_text(0)
    }

    fn at(&self, s: &str) -> bool {
        self.peek_text() == Some(s)
    }

    fn at_newline(&self) -> bool {
        self.peek_kind() == Some(tk::NEWLINE)
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

    fn parse_script(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.eat_fillers(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            let stmt = self.parse_statement();
            c.push(Child::Node(stmt));
        }
        self.make_node(node::SCRIPT, c)
    }

    // --- statements ---------------------------------------------------------

    /// Parse one statement. The cursor is on a real (non-filler) token. Always
    /// makes progress (consumes at least one token).
    fn parse_statement(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        // Classify first into an owned tag so the immutable borrow from
        // `peek_text` is released before the `&mut self` parse calls below.
        match self.classify() {
            Stmt::FunctionKw => self.finish_function_kw(c),
            Stmt::FuncParen => self.finish_func_paren(c),
            Stmt::Compound => self.finish_compound(c),
            Stmt::BraceGroup => self.finish_group(c, "}"),
            Stmt::Subshell => self.finish_group(c, ")"),
            Stmt::Empty => {
                // Defensive: nothing classifiable. Consume one token to guarantee
                // progress; the bytes stay in the tree.
                self.eat(&mut c);
                self.make_node(node::ERROR_STMT, c)
            }
            Stmt::Command => self.finish_command(c),
        }
    }

    /// Decide what kind of statement begins at the cursor without holding any
    /// borrow into `self` (returns an owned, `Copy` tag).
    fn classify(&self) -> Stmt {
        if self.peek_kind().is_none() {
            return Stmt::Empty;
        }
        match self.peek_text() {
            Some("function") => Stmt::FunctionKw,
            _ if self.looks_like_func_def() => Stmt::FuncParen,
            Some("if" | "for" | "while" | "until" | "select" | "case") => Stmt::Compound,
            Some("{") => Stmt::BraceGroup,
            Some("(") => Stmt::Subshell,
            _ => Stmt::Command,
        }
    }

    /// True if the cursor is at a `name ( )` function definition.
    fn looks_like_func_def(&self) -> bool {
        if self.peek_kind() != Some(tk::WORD) {
            return false;
        }
        match self.peek_text() {
            Some(name) if name == "{" || name == "}" || is_reserved(name) => return false,
            None => return false,
            _ => {}
        }
        self.peek_n_text(1) == Some("(") && self.peek_n_text(2) == Some(")")
    }

    /// `function name [()] compound`.
    fn finish_function_kw(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // `function`
        self.ws(&mut c);
        if self.peek_kind() == Some(tk::WORD) {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        self.ws(&mut c);
        if self.at("(") {
            self.eat(&mut c);
            self.ws(&mut c);
            if self.at(")") {
                self.eat(&mut c);
            }
        }
        self.parse_body(&mut c);
        self.make_node(node::FUNCTION, c)
    }

    /// `name () compound`.
    fn finish_func_paren(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        let n = self.name_node();
        c.push(Child::Node(n));
        self.ws(&mut c);
        if self.at("(") {
            self.eat(&mut c);
        }
        self.ws(&mut c);
        if self.at(")") {
            self.eat(&mut c);
        }
        self.parse_body(&mut c);
        self.make_node(node::FUNCTION, c)
    }

    /// Parse a function body: optional newlines, then one compound command.
    fn parse_body(&mut self, c: &mut Vec<Child>) {
        self.eat_fillers(c);
        if self.peek_kind().is_some() {
            let body = self.parse_statement();
            c.push(Child::Node(body));
        }
    }

    /// `{ …; }` command group or `( … )` subshell. `close` is the matching closer.
    fn finish_group(&mut self, mut c: Vec<Child>, close: &'static str) -> Node {
        if self.depth >= MAX_DEPTH {
            self.consume_group_flat(&mut c, close);
            self.note_depth_limit();
            return self.make_node(node::GROUP, c);
        }
        self.depth += 1;
        self.ws(&mut c);
        self.eat(&mut c); // opener
        loop {
            self.eat_fillers(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            if self.at(close) {
                self.eat(&mut c);
                break;
            }
            let stmt = self.parse_statement();
            c.push(Child::Node(stmt));
        }
        self.depth -= 1;
        self.make_node(node::GROUP, c)
    }

    /// `if/for/while/until/select/case …` up to its matching terminator keyword.
    fn finish_compound(&mut self, mut c: Vec<Child>) -> Node {
        let term = match self.peek_text() {
            Some("if") => "fi",
            Some("case") => "esac",
            _ => "done", // for / while / until / select
        };
        if self.depth >= MAX_DEPTH {
            self.consume_compound_flat(&mut c, term);
            self.note_depth_limit();
            return self.make_node(node::COMPOUND, c);
        }
        self.depth += 1;
        self.ws(&mut c);
        self.eat(&mut c); // the compound keyword
        loop {
            self.eat_fillers(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            if self.at(term) {
                self.eat(&mut c);
                break;
            }
            // Don't run past a closer that belongs to an enclosing group.
            if CLOSERS.iter().any(|cl| self.at(cl)) {
                break;
            }
            let stmt = self.parse_statement();
            c.push(Child::Node(stmt));
        }
        self.depth -= 1;
        self.make_node(node::COMPOUND, c)
    }

    /// One command / pipeline line: significant tokens up to a statement
    /// terminator, closer, compound terminator, or filler keyword. Connectors
    /// (`|`, `||`, `&&`, `|&`) are kept inside, so a whole pipeline is one node;
    /// the lowering splits segments to find each command word.
    fn finish_command(&mut self, mut c: Vec<Child>) -> Node {
        let mut consumed_any = false;
        loop {
            self.ws(&mut c);
            if self.peek_kind().is_none() || self.at_newline() {
                break;
            }
            let stop = match self.peek_text() {
                Some(t) => {
                    CMD_TERM.contains(&t)
                        || CLOSERS.contains(&t)
                        || COMPOUND_TERM.contains(&t)
                        || FILLER_TEXT.contains(&t)
                }
                None => true,
            };
            if stop {
                if consumed_any {
                    break;
                }
                // Degenerate: a terminator with no command before it. Force
                // progress so the byte is never dropped and we never spin.
                self.eat(&mut c);
                break;
            }
            self.eat(&mut c);
            consumed_any = true;
        }
        self.make_node(node::COMMAND, c)
    }

    // --- depth-cap flat consumers ------------------------------------------

    /// At the depth cap, swallow a `{ … }` / `( … )` group as a flat token run,
    /// balancing the opener/closer pair without recursing.
    fn consume_group_flat(&mut self, out: &mut Vec<Child>, close: &'static str) {
        let open = if close == "}" { "{" } else { "(" };
        self.ws(out);
        self.eat(out); // opener
        let mut bal: i32 = 1;
        while self.i < self.toks.len() {
            if let Some(t) = self.peek_text() {
                if t == open {
                    bal += 1;
                } else if t == close {
                    bal -= 1;
                    self.eat(out);
                    if bal == 0 {
                        break;
                    }
                    continue;
                }
            }
            self.eat(out);
        }
    }

    /// At the depth cap, swallow a compound statement as a flat token run up to its
    /// first matching terminator keyword (or end of input).
    fn consume_compound_flat(&mut self, out: &mut Vec<Child>, term: &str) {
        self.ws(out);
        self.eat(out); // the keyword
        while self.i < self.toks.len() {
            if self.at(term) {
                self.eat(out);
                break;
            }
            self.eat(out);
        }
    }

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "bash.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; region flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }

    // --- shared helpers -----------------------------------------------------

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // the name word
        self.make_node(node::NAME, c)
    }
}

fn is_reserved(text: &str) -> bool {
    crate::lang::bash::lexer::is_keyword(text)
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
#!/bin/bash
# a script
NAME=\"world\"

greet() {
    local who=\"$1\"
    echo \"hello, $who\"
    cat <<EOF
multi
line $who
EOF
}

function bye {
    echo bye
}

if [ -n \"$NAME\" ]; then
    greet \"$NAME\"
else
    bye
fi

for f in a b c; do
    echo $f
done

source ./lib.sh
";
        let tree = parse("script.sh", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_function_definitions() {
        let src = "f() {\n  echo hi\n}\nfunction g {\n  echo bye\n}\n";
        let tree = parse("t.sh", src);
        let fns: Vec<&str> = tree
            .root
            .children_of(node::FUNCTION)
            .filter_map(|f| f.child(node::NAME))
            .filter_map(|n| n.tokens().next())
            .map(|t| t.span.text(src))
            .collect();
        assert_eq!(fns, vec!["f", "g"]);
    }

    #[test]
    fn group_body_holds_nested_commands() {
        let src = "f() {\n  echo a\n  echo b\n}\n";
        let tree = parse("t.sh", src);
        let f = tree
            .root
            .children_of(node::FUNCTION)
            .next()
            .expect("a function");
        let group = f.child(node::GROUP).expect("function has a group body");
        let cmds = group.children_of(node::COMMAND).count();
        assert_eq!(cmds, 2, "two echo commands inside the group");
    }

    #[test]
    fn compound_if_is_recognized() {
        let src = "if true; then\n  echo yes\nfi\n";
        let tree = parse("t.sh", src);
        assert!(
            tree.root.children_of(node::COMPOUND).next().is_some(),
            "if/fi should parse as a Compound"
        );
        assert!(tree.is_lossless());
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        // Far deeper than MAX_DEPTH on both axes; must not stack-overflow and must
        // stay lossless.
        let mut deep_groups = String::from("f() ");
        deep_groups.push_str(&"{ ".repeat(5_000));
        deep_groups.push_str("echo hi");
        deep_groups.push_str(&" }".repeat(5_000));
        deep_groups.push('\n');

        let mut deep_if = String::new();
        for _ in 0..5_000 {
            deep_if.push_str("if true; then ");
        }
        deep_if.push_str("echo hi");
        for _ in 0..5_000 {
            deep_if.push_str(" fi");
        }
        deep_if.push('\n');

        for src in [deep_groups, deep_if] {
            let tree = parse("deep.sh", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics
                    .iter()
                    .any(|d| d.code == "bash.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "echo 'oops\n",          // unterminated string
            "λ='☃'  # unicode\n",    // multi-byte identifiers/strings
            "",                      // empty file
            "\n\n   \n# trailing\n", // only blanks and comments
            "cat <<EOF\nno terminator here\n",
        ] {
            let tree = parse("edge.sh", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
