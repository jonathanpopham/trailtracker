//! R parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Lua parser: R has no statement keywords that introduce
//! definitions (a function is an ordinary value, written `function(args) body`
//! or, since R 4.1, `\(args) body`), so the parser segments the source into
//! statements and captures balanced delimiter groups precisely while keeping the
//! analytically important shapes first-class. Specifically:
//!
//! - `function`/`\` followed by a parameter `(...)` list and a body becomes a
//!   real [`node::FUNCTION`] node, so the lowering can attribute its calls and
//!   nested definitions. The body is a brace block (`{ … }`) when present, else a
//!   bare-expression [`node::BODY`] run.
//! - Brace groups `{ … }` are always parsed as **statement blocks** (R braces are
//!   only ever code blocks, never data literals), so nested definitions inside
//!   `if`/`for`/`while` bodies and function bodies stay first-class.
//! - Parenthesis `(...)` and bracket `[...]`/`[[...]]` groups are captured as
//!   balanced token-tree nodes — losslessly — and graph facts are extracted from
//!   them in the lowering, never invented.
//!
//! R is **not** whitespace-significant: a newline is ordinary trivia, but it
//! softly terminates a statement when the preceding token does not demand a
//! right-hand side and the next token does not continue an expression — the same
//! rule the R parser/REPL uses. Statements may also be separated by `;`.
//!
//! Anything unrecognized still lands in the tree as its exact tokens, so the
//! result always round-trips. The recursion is depth-guarded at [`MAX_DEPTH`]
//! against hostile nesting (deep braces *or* deep brackets) — a `catch_unwind`
//! cannot catch a stack overflow, so the guard is the real defense.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::r::lexer::{kind as tk, lex};

/// CST node-kind labels. The lowering interprets these.
pub mod node {
    pub const PROGRAM: &str = "Program";
    pub const SIMPLE_STMT: &str = "SimpleStmt";
    pub const FUNCTION: &str = "Function";
    pub const BODY: &str = "Body";
    pub const ERROR_STMT: &str = "ErrorStmt";

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
    let mut p = RParser {
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

struct RParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

/// The last significant element consumed in an expression run, used by the
/// statement-boundary heuristic.
#[allow(dead_code)]
enum Last {
    None,
    Group,
    Tok(String),
}

impl<'s> RParser<'s> {
    // --- cursor primitives --------------------------------------------------

    /// Append the current token (trivia or not) to `out` and advance.
    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading trivia tokens (whitespace, newlines, comments)
    /// into `out`. In R every one of these is trivia.
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

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "r.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; region flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }

    // --- top level ----------------------------------------------------------

    fn parse_program(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            match self.peek_text() {
                None => {
                    self.flush(&mut c);
                    break;
                }
                Some(t) if is_close_delim(t) => {
                    // A stray closer at top level: consume it as an error
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
        self.make_node(node::PROGRAM, c)
    }

    fn parse_statement(&mut self) -> Node {
        let mut c = Vec::new();
        self.collect_expr_run(&mut c, true);
        if c.is_empty() {
            // Defensive: guarantee progress (e.g. a leading bare `,`).
            self.ws(&mut c);
            self.eat(&mut c);
            return self.make_node(node::ERROR_STMT, c);
        }
        self.make_node(node::SIMPLE_STMT, c)
    }

    /// `function (params) body` / `\(params) body`. The body is a brace block
    /// when present, else a bare-expression run.
    fn finish_function(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // `function` or `\`
        self.ws(&mut c);
        if self.at("(") {
            let params = self.parse_group();
            c.push(Child::Node(params));
        }
        self.ws(&mut c);
        if self.at("{") {
            let body = self.parse_group(); // brace block of statements
            c.push(Child::Node(body));
        } else {
            let mut bc = Vec::new();
            self.collect_expr_run(&mut bc, true);
            if !bc.is_empty() {
                c.push(Child::Node(self.make_node(node::BODY, bc)));
            }
        }
        self.make_node(node::FUNCTION, c)
    }

    /// Collect an expression run into `out`. Stops (without consuming) at a close
    /// delimiter or a `,` (both belong to an enclosing group/caller); consumes
    /// and stops at a `;`. When `soft_newline` is set, also stops at a newline
    /// that is not an obvious expression continuation. A `function`/`\(` is parsed
    /// inline as a real function node. Balanced `()`/`[]`/`{}` groups are
    /// descended into as `Paren`/`Bracket`/`Brace` nodes.
    fn collect_expr_run(&mut self, out: &mut Vec<Child>, soft_newline: bool) {
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
            if is_close_delim(txt) || txt == "," {
                break;
            }
            if txt == ";" {
                self.ws(out);
                self.eat(out);
                break;
            }
            if txt == "function" || (txt == "\\" && self.peek_n_text(1) == Some("(")) {
                if self.depth < MAX_DEPTH {
                    self.depth += 1;
                    let f = self.finish_function();
                    self.depth -= 1;
                    out.push(Child::Node(f));
                } else {
                    self.ws(out);
                    self.eat(out);
                    self.note_depth_limit();
                }
                last = Last::Group;
                continue;
            }
            if soft_newline && newline_ahead && !matches!(last, Last::None) {
                let next_kind = self.peek_kind().unwrap_or(tk::ERROR);
                if !continues_after(&last) && !continues_before(next_kind, txt) {
                    break;
                }
            }
            if is_open_delim(txt) {
                self.ws(out);
                if self.depth < MAX_DEPTH {
                    self.depth += 1;
                    let g = self.parse_group();
                    self.depth -= 1;
                    out.push(Child::Node(g));
                } else {
                    self.eat(out); // opener
                    self.consume_balanced_flat(out);
                    self.note_depth_limit();
                }
                last = Last::Group;
            } else {
                let owned = txt.to_string();
                self.ws(out);
                self.eat(out);
                last = Last::Tok(owned);
            }
        }
    }

    /// Dispatch a group opener: `{` → a statement block, `(`/`[` → a balanced
    /// token group. Cursor is at (or before trivia preceding) the opener.
    fn parse_group(&mut self) -> Node {
        if self.at("{") {
            self.parse_brace_block()
        } else {
            self.parse_delimited()
        }
    }

    /// Parse `{ statements }` as a recursive statement block. R braces are only
    /// ever code blocks, so nested definitions inside stay first-class.
    fn parse_brace_block(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // {
        loop {
            match self.peek_text() {
                None => {
                    self.flush(&mut c);
                    break;
                }
                Some("}") => {
                    self.ws(&mut c);
                    self.eat(&mut c);
                    break;
                }
                Some(t) if is_close_delim(t) => {
                    // Stray `)`/`]` inside a brace: consume as an error statement.
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
        self.make_node(node::BRACE, c)
    }

    /// Parse a balanced delimiter group `(...)` or `[...]`. Nested groups,
    /// brace blocks, and inline functions are parsed as real nodes.
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
                Some(t) if t == "function" || (t == "\\" && self.peek_n_text(1) == Some("(")) => {
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
                        let inner = self.parse_group();
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
}

// --- boundary heuristic helpers ---------------------------------------------

fn is_open_delim(t: &str) -> bool {
    matches!(t, "(" | "[" | "{")
}

fn is_close_delim(t: &str) -> bool {
    matches!(t, ")" | "]" | "}")
}

/// True when the most recently consumed element demands a right-hand operand, so
/// the expression must continue across a newline.
fn continues_after(last: &Last) -> bool {
    match last {
        Last::None | Last::Group => false,
        Last::Tok(text) => {
            matches!(
                text.as_str(),
                "+" | "-"
                    | "*"
                    | "/"
                    | "^"
                    | "%%"
                    | "%/%"
                    | "%in%"
                    | "%*%"
                    | "%o%"
                    | "<-"
                    | "<<-"
                    | "->"
                    | "->>"
                    | "="
                    | "=="
                    | "!="
                    | "<"
                    | ">"
                    | "<="
                    | ">="
                    | "&"
                    | "&&"
                    | "|"
                    | "||"
                    | "!"
                    | "~"
                    | ":"
                    | "::"
                    | ":::"
                    | "$"
                    | "@"
                    | "|>"
            ) || text.starts_with('%')
        }
    }
}

/// True when the next token continues the preceding expression (a binary
/// operator, an access/namespace operator, or a call/index opener), so a newline
/// before it is not a statement boundary.
fn continues_before(kind: &str, text: &str) -> bool {
    if kind == tk::NAME {
        // The `else` of an `if` continues the statement; a bare name starts a new
        // one.
        return text == "else";
    }
    matches!(
        text,
        "+" | "-"
            | "*"
            | "/"
            | "^"
            | "<-"
            | "<<-"
            | "->"
            | "->>"
            | "=="
            | "!="
            | "<"
            | ">"
            | "<="
            | ">="
            | "&"
            | "&&"
            | "|"
            | "||"
            | "~"
            | ":"
            | "::"
            | ":::"
            | "$"
            | "@"
            | "|>"
            | "("
            | "["
            | "{"
    ) || text.starts_with('%')
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
# inventory module
library(dplyr)

make_item <- function(name, qty = 0) {
    self <- list(name = name, qty = qty)
    if (self$qty < 0) {
        self$qty <- 0
    }
    self
}

Item.add <- function(item, n) item$qty + n

total <- sum(sapply(items, function(it) it$qty))
result <- data %>% filter(qty > 0) -> kept
";
        let tree = parse("inventory.R", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_function_and_statements() {
        let src = "f <- function(x) x + 1\ng <- function(y) {\n  y * 2\n}\nz <- 3\n";
        let tree = parse("t.R", src);
        let stmts: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(
            stmts.iter().filter(|k| **k == node::SIMPLE_STMT).count() >= 3,
            "three statements: {stmts:?}"
        );
        // Each assigned function is a Function node nested in its statement.
        let funcs = tree
            .root
            .walk()
            .filter(|n| n.kind == node::FUNCTION)
            .count();
        assert_eq!(funcs, 2, "two function definitions");
    }

    #[test]
    fn lambda_shorthand_is_a_function() {
        let src = "sq <- \\(x) x^2\n";
        let tree = parse("t.R", src);
        assert!(tree.root.walk().any(|n| n.kind == node::FUNCTION));
        assert!(tree.is_lossless());
    }

    #[test]
    fn brace_blocks_are_statement_blocks() {
        let src = "f <- function() {\n  a()\n  b()\n}\n";
        let tree = parse("t.R", src);
        let brace = tree
            .root
            .walk()
            .find(|n| n.kind == node::BRACE)
            .expect("a brace block");
        assert!(
            brace.children_of(node::SIMPLE_STMT).count() >= 2,
            "two statements in the body"
        );
    }

    #[test]
    fn statements_separated_by_newline() {
        let src = "print(1)\nprint(2)\n";
        let tree = parse("t.R", src);
        let stmts = tree.root.children_of(node::SIMPLE_STMT).count();
        assert_eq!(stmts, 2, "newline should separate the two call statements");
    }

    #[test]
    fn multiline_expression_stays_one_statement() {
        let src = "x <- a +\n    b\nprint(x)\n";
        let tree = parse("t.R", src);
        let stmts = tree.root.children_of(node::SIMPLE_STMT).count();
        assert_eq!(stmts, 2, "the continued expr is one stmt, print is another");
    }

    #[test]
    fn brackets_and_double_brackets_round_trip() {
        let src = "x[[1]] <- y[2]\nm[i, j] <- 0\n";
        let tree = parse("t.R", src);
        assert!(tree.is_lossless());
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let deep_parens = format!("x <- {}{}\n", "(".repeat(10_000), ")".repeat(10_000));
        let deep_braces = format!(
            "f <- function() {}{}\n",
            "{".repeat(2_000),
            "}".repeat(2_000)
        );
        for src in [deep_parens, deep_braces] {
            let tree = parse("deep.R", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics.iter().any(|d| d.code == "r.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "x <- (1, 2\n",          // unterminated paren
            "s <- 'unterminated\n",  // unterminated string
            "λ <- '☃'  # unicode\n", // multi-byte identifiers/strings
            "",                      // empty file
            "\n\n   \n# trailing\n", // only blanks and comments
            "y <- r\"( open",        // unterminated raw string
        ] {
            let tree = parse("edge.R", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
