//! OCaml parser producing the language-neutral lossless CST.
//!
//! Strategy (honest, breadth-growable): OCaml has a large grammar, and we do
//! **not** reimplement it. We carve the file into top-level *structure items*
//! using two robust, lossless signals:
//!
//! 1. **Item-head keywords.** A structure item begins with one of `let`, `and`,
//!    `module`, `type`, `open`, `include`, `class`, `exception`, `external`, or
//!    `val`. An item runs from one such head to the next head **at block depth 0**.
//! 2. **Balanced blocks consumed whole.** `struct … end`, `sig … end`,
//!    `begin … end`, and `object … end`, plus the bracket families `(…)`, `[…]`,
//!    `{…}`, are consumed as balanced groups, so an inner head (e.g. a `let`
//!    inside a `struct`) never falsely ends the outer item, and a `;;` inside a
//!    group never falsely terminates it.
//!
//! To avoid splitting a multi-line binding whose body happens to dedent, a head
//! keyword only starts a *new* item when it sits in **byte-column 0** (start of
//! file, or directly after a newline). Nested `let … in` is indented, so it stays
//! inside its parent item — an honest punt: nested bindings are not lifted to
//! definitions (the lowering documents this). A `;;` token at depth 0 also ends
//! the current item.
//!
//! Each item is classified by its leading lexeme; names and graph facts are
//! extracted from the real tokens in the lowering pass, never invented. Anything
//! unrecognized becomes an `ErrorItem` node that still holds its exact tokens, so
//! the tree always round-trips.
//!
//! The block / delimiter recursion is depth-guarded at [`MAX_DEPTH`] (mirroring
//! the Rust parser): beyond the cap the remaining group is consumed as a flat
//! balanced run with a `depth_limit` diagnostic, because a `catch_unwind` cannot
//! catch a stack overflow.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::ocaml::lexer::{kind as tk, lex};

/// CST node-kind labels. The lowering interprets these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    /// `let … = …` or an `and …` continuation (a value/function binding).
    pub const BINDING: &str = "Binding";
    /// `module X = …` (a structure binding).
    pub const MODULE: &str = "Module";
    /// `module type X = …` (a module-type / signature binding).
    pub const MODULE_TYPE: &str = "ModuleType";
    /// `type x = …` (a type declaration).
    pub const TYPE_DECL: &str = "TypeDecl";
    /// `open X`.
    pub const OPEN: &str = "Open";
    /// `include X`.
    pub const INCLUDE: &str = "Include";
    /// `class … = …`.
    pub const CLASS: &str = "Class";
    /// `exception E …`.
    pub const EXCEPTION: &str = "Exception";
    /// `external name : type = "prim"`.
    pub const EXTERNAL: &str = "External";
    /// `val name : type` (signature item; declares a type, defines no value).
    pub const VAL: &str = "Val";
    /// A recognized top-level expression statement (defines nothing).
    pub const EXPR_ITEM: &str = "ExprItem";
    pub const ERROR_ITEM: &str = "ErrorItem";

    /// A `struct/sig/begin/object … end` block.
    pub const BLOCK: &str = "Block";
    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Item-head keywords that open a top-level structure item.
fn is_item_head_kw(text: &str) -> bool {
    matches!(
        text,
        "let"
            | "and"
            | "module"
            | "type"
            | "open"
            | "include"
            | "class"
            | "exception"
            | "external"
            | "val"
    )
}

/// Keywords that open an `end`-terminated block.
fn is_block_open_kw(text: &str) -> bool {
    matches!(text, "struct" | "sig" | "begin" | "object")
}

/// Maximum block/delimiter-nesting depth before the parser stops recursing and
/// consumes the remainder iteratively. Mirrors the Rust parser; protects against a
/// stack overflow on hostile inputs, which `catch_unwind` cannot catch.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = OcamlParser {
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

struct OcamlParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    depth: usize,
}

impl<'s> OcamlParser<'s> {
    // --- cursor primitives --------------------------------------------------

    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading trivia tokens (whitespace/comments — *not*
    /// newlines, which are structural) into `out`.
    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
        }
    }

    /// Text of the n-th significant token from the cursor (skips trivia; newlines
    /// count as significant). `None` only at true end-of-input.
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

    fn at(&self, s: &str) -> bool {
        self.peek_n_text(0) == Some(s)
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

    /// Is token `idx` a top-level item head: a non-trivia item-head keyword sitting
    /// in byte-column 0 (file start, or directly after a `\n`)?
    fn is_head(&self, idx: usize) -> bool {
        let t = match self.toks.get(idx) {
            Some(t) => t,
            None => return false,
        };
        if t.trivia || t.kind == tk::NEWLINE {
            return false;
        }
        if !is_item_head_kw(t.span.text(self.src)) {
            return false;
        }
        let s = t.span.start as usize;
        s == 0 || self.src.as_bytes().get(s - 1) == Some(&b'\n')
    }

    // --- top level ----------------------------------------------------------

    fn parse_source_file(&mut self) -> Node {
        let mut c = Vec::new();
        while self.i < self.toks.len() {
            // Leading trivia / newlines before the first significant token of an
            // item attach to the file directly (lossless either way).
            if self.toks[self.i].trivia || self.toks[self.i].kind == tk::NEWLINE {
                self.eat(&mut c);
                continue;
            }
            let item = self.parse_item();
            c.push(Child::Node(item));
        }
        self.make_node(node::SOURCE_FILE, c)
    }

    /// Collect one item: its head plus everything up to the next column-0 item head
    /// (at block depth 0), or through a depth-0 `;;`. Balanced groups and blocks
    /// are consumed whole.
    fn parse_item(&mut self) -> Node {
        let mut c = Vec::new();
        let mut consumed_significant = false;
        loop {
            if self.i >= self.toks.len() {
                break;
            }
            let is_trivia = self.toks[self.i].trivia;
            let is_newline = self.toks[self.i].kind == tk::NEWLINE;
            if is_trivia || is_newline {
                self.eat(&mut c);
                continue;
            }
            // Significant token.
            if consumed_significant && self.is_head(self.i) {
                break;
            }
            let text = self.toks[self.i].span.text(self.src);
            if text == "(" || text == "[" || text == "{" {
                let g = self.parse_delimited();
                c.push(Child::Node(g));
            } else if is_block_open_kw(text) {
                let g = self.parse_block();
                c.push(Child::Node(g));
            } else if text == ";;" {
                self.eat(&mut c);
                break;
            } else {
                self.eat(&mut c);
            }
            consumed_significant = true;
        }
        let kind = classify(&c, self.src);
        if kind == node::ERROR_ITEM {
            self.diags.push(Diagnostic {
                code: "ocaml.unrecognized_item",
                message: "token(s) not recognized as an OCaml top-level item".to_string(),
                span: children_span(&c).unwrap_or_else(|| ByteSpan::empty_at(self.cur_offset())),
            });
        }
        self.make_node(kind, c)
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`. The cursor is
    /// at (or before trivia preceding) the opener.
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
            return self.make_node(node::ERROR_ITEM, g);
        };
        self.eat(&mut g); // opener
        loop {
            self.ws(&mut g);
            if self.peek_n_text(0).is_none() {
                break; // unterminated; still lossless
            }
            if self.at(close) {
                self.eat(&mut g);
                break;
            }
            self.parse_nested(&mut g, false);
        }
        self.make_node(label, g)
    }

    /// Parse a `struct/sig/begin/object … end` block. The cursor is at the opener
    /// keyword.
    fn parse_block(&mut self) -> Node {
        let mut g = Vec::new();
        self.eat(&mut g); // opener keyword
        loop {
            self.ws(&mut g);
            if self.peek_n_text(0).is_none() {
                break; // unterminated; still lossless
            }
            if self.at("end") {
                self.eat(&mut g);
                break;
            }
            self.parse_nested(&mut g, true);
        }
        self.make_node(node::BLOCK, g)
    }

    /// Consume the next construct inside a group/block: a nested block, a nested
    /// delimiter group, or a single token. `allow_blocks` is false inside bracket
    /// families (where a bare `struct`/`end` keyword, while unusual, is just a
    /// token) and true inside `end`-terminated blocks.
    fn parse_nested(&mut self, out: &mut Vec<Child>, allow_blocks: bool) {
        // Read the current token's text directly (lifetime tied to `src`, not to
        // `&self`) so the mutable calls below do not conflict with a borrow. The
        // caller has already skipped trivia and checked for end-of-input.
        let text = match self.toks.get(self.i) {
            Some(t) => t.span.text(self.src),
            None => return,
        };
        let is_open_delim = text == "(" || text == "[" || text == "{";
        let is_open_block = allow_blocks && is_block_open_kw(text);
        if is_open_delim || is_open_block {
            if self.depth < MAX_DEPTH {
                self.depth += 1;
                let inner = if is_open_block {
                    self.parse_block()
                } else {
                    self.parse_delimited()
                };
                self.depth -= 1;
                out.push(Child::Node(inner));
            } else {
                self.eat(out); // opener
                self.consume_balanced_flat(out, allow_blocks);
                self.note_depth_limit();
            }
        } else {
            self.eat(out);
        }
    }

    /// Iteratively consume a balanced run (opener already eaten), appending every
    /// token as a flat leaf. Used at the depth cap so arbitrarily deep nesting
    /// never recurses further. On unbalanced input it stops at EOF.
    fn consume_balanced_flat(&mut self, out: &mut Vec<Child>, allow_blocks: bool) {
        let mut balance: i32 = 1;
        while balance > 0 {
            self.ws(out);
            let text = match self.toks.get(self.i) {
                Some(t) => t.span.text(self.src),
                None => break,
            };
            if text == "(" || text == "[" || text == "{" {
                balance += 1;
            } else if text == ")" || text == "]" || text == "}" {
                balance -= 1;
            } else if allow_blocks && is_block_open_kw(text) {
                balance += 1;
            } else if allow_blocks && text == "end" {
                balance -= 1;
            }
            self.eat(out);
        }
    }

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "ocaml.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; group flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }
}

/// Classify an item by its leading significant lexeme.
fn classify(children: &[Child], src: &str) -> &'static str {
    let mut head: Option<&str> = None;
    let mut second: Option<&str> = None;
    for c in children {
        match c {
            Child::Token(t) if t.trivia || t.kind == tk::NEWLINE => {}
            Child::Token(t) => {
                if head.is_none() {
                    head = Some(t.span.text(src));
                } else if second.is_none() {
                    second = Some(t.span.text(src));
                    break;
                }
            }
            Child::Node(_) => {
                // A group as the head (e.g. an `(op)` binding name) is not a keyword
                // head; treat as a non-keyword item below.
                if head.is_some() && second.is_none() {
                    second = Some("");
                    break;
                }
                if head.is_none() {
                    head = Some("");
                    break;
                }
            }
        }
    }

    let head = match head {
        Some(h) => h,
        None => return node::ERROR_ITEM,
    };

    match head {
        "let" | "and" => node::BINDING,
        "module" if second == Some("type") => node::MODULE_TYPE,
        "module" => node::MODULE,
        "type" => node::TYPE_DECL,
        "open" => node::OPEN,
        "include" => node::INCLUDE,
        "class" => node::CLASS,
        "exception" => node::EXCEPTION,
        "external" => node::EXTERNAL,
        "val" => node::VAL,
        "" => node::ERROR_ITEM, // a group with nothing classifiable
        // A non-keyword head (`(op) = …`, or a bare expression / application): a
        // recognized top-level expression statement, not an error.
        _ => node::EXPR_ITEM,
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
(* | Example module. *)
open Printf
include Stdlib

type 'a tree =
  | Leaf
  | Node of 'a tree * 'a * 'a tree

type point = { x : int; y : int }

module M = struct
  let secret = 42
  let bump n = n + secret
end

module type S = sig
  val run : unit -> unit
end

exception Boom of string

external id : 'a -> 'a = \"%identity\"

let answer = 42

let add x y = x + y

let main () =
  let n = add answer 1 in
  printf \"%d\\n\" n
;;
";
        let tree = parse("example.ml", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "open X\ntype t = A | B\nlet f x = x\nlet c = 1\nmodule M = struct end\n";
        let tree = parse("m.ml", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::OPEN));
        assert!(kinds.contains(&node::TYPE_DECL));
        assert!(kinds.contains(&node::BINDING));
        assert!(kinds.contains(&node::MODULE));
    }

    #[test]
    fn module_type_distinguished_from_module() {
        let src = "module type S = sig val x : int end\nmodule M = struct let x = 1 end\n";
        let tree = parse("m.ml", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::MODULE_TYPE));
        assert!(kinds.contains(&node::MODULE));
    }

    #[test]
    fn nested_let_in_stays_in_one_item() {
        // The indented `let n = … in` is part of `main`, not its own item.
        let src = "let main () =\n  let n = 1 in\n  n\nlet other = 2\n";
        let tree = parse("m.ml", src);
        let items: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert_eq!(items, vec![node::BINDING, node::BINDING]);
    }

    #[test]
    fn struct_body_does_not_split_outer_module() {
        // The column-0 `let` inside the struct must not end the module item.
        let src = "module M = struct\nlet a = 1\nlet b = 2\nend\nlet c = 3\n";
        let tree = parse("m.ml", src);
        let items: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert_eq!(items, vec![node::MODULE, node::BINDING]);
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let depth = 10_000;
        let src = format!("let x = {}{}", "(".repeat(depth), ")".repeat(depth));
        let tree = parse("deep.ml", &src);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics
                .iter()
                .any(|d| d.code == "ocaml.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }

    #[test]
    fn pathological_block_nesting_does_not_overflow() {
        let depth = 5_000;
        let src = format!(
            "module M = {}{}",
            "struct ".repeat(depth),
            "end ".repeat(depth)
        );
        let tree = parse("deep.ml", &src);
        assert!(tree.is_lossless(), "deeply nested blocks must round-trip");
        assert!(tree
            .diagnostics
            .iter()
            .any(|d| d.code == "ocaml.depth_limit"));
    }
}
