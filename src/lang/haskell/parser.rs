//! Haskell parser producing the language-neutral lossless CST.
//!
//! Strategy (honest, breadth-growable): Haskell is layout-sensitive, and we do
//! **not** reimplement the full layout algorithm. Instead we carve the file into
//! top-level *items* using the one robust, lossless signal that does not require
//! layout: a declaration head is a non-trivia token sitting in **byte-column 0**
//! (start of file, or immediately after a newline with no leading whitespace).
//! Everything from one column-0 head up to (but not including) the next is one
//! item — its continuation lines are indented, so they never look like heads, and
//! balanced delimiter groups (`(...)`, `[...]`, `{...}`) are consumed whole so a
//! column-0 token *inside* a multi-line group never falsely ends the item.
//!
//! Each item is then classified by its leading lexeme (`module`, `import`,
//! `data`, `newtype`, `type`, `class`, `instance`, a type signature `name ::`,
//! an `infix*` fixity, a `foreign` decl, or an ordinary binding `name … = …`).
//! Names and graph facts are extracted from these real tokens in the lowering
//! pass — never invented. Anything unrecognized becomes an `ErrorItem` node that
//! still contains its exact source tokens, so the tree always round-trips.
//!
//! The delimiter recursion is depth-guarded at [`MAX_DEPTH`] (mirroring the Rust
//! parser): beyond the cap the remaining group is consumed as a flat balanced
//! run with a `depth_limit` diagnostic, because a `catch_unwind` cannot catch a
//! stack overflow.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::haskell::lexer::{is_keyword, kind as tk, lex};

/// CST node-kind labels. The lowering interprets these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const MODULE: &str = "Module";
    pub const IMPORT: &str = "Import";
    pub const DATA: &str = "Data";
    pub const NEWTYPE: &str = "Newtype";
    pub const TYPE_ALIAS: &str = "TypeAlias";
    pub const CLASS: &str = "Class";
    pub const INSTANCE: &str = "Instance";
    /// A top-level type signature `name :: Type` (declares a type, defines no
    /// value; the lowering records it but emits no definition node).
    pub const SIGNATURE: &str = "Signature";
    /// A top-level value/function binding `name … = …`.
    pub const BINDING: &str = "Binding";
    pub const FIXITY: &str = "Fixity";
    pub const FOREIGN: &str = "Foreign";
    pub const ERROR_ITEM: &str = "ErrorItem";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum delimiter-nesting depth before the parser stops recursing and consumes
/// the remaining group iteratively. Mirrors the Rust parser; protects against a
/// stack overflow on hostile inputs, which `catch_unwind` cannot catch.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = HaskellParser {
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

struct HaskellParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    depth: usize,
}

impl<'s> HaskellParser<'s> {
    // --- cursor primitives --------------------------------------------------

    /// Append the current token (trivia or not) to `out` and advance.
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

    /// Text of the n-th significant token (skips trivia; newlines count as
    /// significant). `None` only at true end-of-input.
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

    /// Is token `idx` a top-level declaration head: non-trivia, not a newline,
    /// and sitting in byte-column 0 (file start, or directly after a `\n`)?
    fn is_head(&self, idx: usize) -> bool {
        let t = match self.toks.get(idx) {
            Some(t) => t,
            None => return false,
        };
        if t.trivia || t.kind == tk::NEWLINE {
            return false;
        }
        let s = t.span.start as usize;
        s == 0 || self.src.as_bytes().get(s - 1) == Some(&b'\n')
    }

    // --- top level ----------------------------------------------------------

    fn parse_source_file(&mut self) -> Node {
        let mut c = Vec::new();
        // Leading trivia / newlines before the first column-0 head attach to the
        // file directly (lossless either way).
        while self.i < self.toks.len() && !self.is_head(self.i) {
            self.eat(&mut c);
        }
        while self.i < self.toks.len() {
            let item = self.parse_item();
            c.push(Child::Node(item));
        }
        self.make_node(node::SOURCE_FILE, c)
    }

    /// Collect one item: its head token plus everything up to the next column-0
    /// head (at delimiter depth 0). Balanced groups are consumed whole.
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
            let is_open = text == "(" || text == "[" || text == "{";
            if is_open {
                let g = self.parse_delimited(None);
                c.push(Child::Node(g));
            } else {
                self.eat(&mut c);
            }
            consumed_significant = true;
        }
        let kind = classify(&c, self.src);
        if kind == node::ERROR_ITEM {
            self.diags.push(Diagnostic {
                code: "haskell.unrecognized_item",
                message: "token(s) not recognized as a Haskell top-level item".to_string(),
                span: children_span(&c).unwrap_or_else(|| ByteSpan::empty_at(self.cur_offset())),
            });
        }
        self.make_node(kind, c)
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`. The cursor
    /// is at (or before trivia preceding) the opener.
    fn parse_delimited(&mut self, label_override: Option<&'static str>) -> Node {
        let mut g = Vec::new();
        self.ws(&mut g);
        let (close, default_label) = if self.at("(") {
            (")", node::PAREN)
        } else if self.at("[") {
            ("]", node::BRACKET)
        } else if self.at("{") {
            ("}", node::BRACE)
        } else {
            return self.make_node(label_override.unwrap_or(node::ERROR_ITEM), g);
        };
        let label = label_override.unwrap_or(default_label);
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
            if self.at("(") || self.at("[") || self.at("{") {
                if self.depth < MAX_DEPTH {
                    self.depth += 1;
                    let inner = self.parse_delimited(None);
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
    /// deep nesting never recurses further. Balances all delimiter kinds
    /// uniformly; on unbalanced input it stops at EOF.
    fn consume_balanced_flat(&mut self, out: &mut Vec<Child>) {
        let mut balance: i32 = 1;
        while balance > 0 {
            self.ws(out);
            if self.peek_n_text(0).is_none() {
                break;
            }
            if self.at("(") || self.at("[") || self.at("{") {
                balance += 1;
            } else if self.at(")") || self.at("]") || self.at("}") {
                balance -= 1;
            }
            self.eat(out);
        }
    }

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "haskell.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; group flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }
}

/// Classify an item by its leading significant lexeme and the operators present
/// at its top level (`::` ⇒ signature, `=` ⇒ binding).
fn classify(children: &[Child], src: &str) -> &'static str {
    let mut seen = false;
    let mut head_tok: Option<&Token> = None;
    let mut head_is_group = false;
    let mut has_dcolon = false;
    let mut has_eq = false;
    for c in children {
        match c {
            Child::Token(t) if t.trivia || t.kind == tk::NEWLINE => {}
            Child::Token(t) => {
                if !seen {
                    head_tok = Some(t);
                    seen = true;
                }
                if t.kind == tk::OPERATOR {
                    match t.span.text(src) {
                        "::" => has_dcolon = true,
                        "=" => has_eq = true,
                        _ => {}
                    }
                }
            }
            Child::Node(_) => {
                if !seen {
                    head_is_group = true;
                    seen = true;
                }
            }
        }
    }

    if let Some(t) = head_tok {
        let text = t.span.text(src);
        if is_keyword(text) {
            return match text {
                "module" => node::MODULE,
                "import" => node::IMPORT,
                "data" => node::DATA,
                "newtype" => node::NEWTYPE,
                "type" => node::TYPE_ALIAS,
                "class" => node::CLASS,
                "instance" => node::INSTANCE,
                "infix" | "infixl" | "infixr" => node::FIXITY,
                "foreign" => node::FOREIGN,
                _ if has_dcolon => node::SIGNATURE,
                _ if has_eq => node::BINDING,
                _ => node::ERROR_ITEM,
            };
        }
        // A non-keyword head: a variable/constructor/operator declaration.
        if has_dcolon {
            node::SIGNATURE
        } else {
            node::BINDING
        }
    } else if head_is_group {
        // Starts with `(op)` or a paren pattern.
        if has_dcolon {
            node::SIGNATURE
        } else {
            node::BINDING
        }
    } else {
        node::ERROR_ITEM
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
-- | Example module.
{-# LANGUAGE OverloadedStrings #-}
module Data.Example
  ( Foo(..)
  , greet
  ) where

import Data.Maybe (fromMaybe)
import qualified Data.Map as Map

type Name = String

newtype Age = Age Int

data Foo a
  = Bar a
  | Baz
  deriving (Show, Eq)

class Greet a where
  greet :: a -> String

instance Greet Foo where
  greet Baz = \"baz\"
  greet (Bar _) = \"bar\"

answer :: Int
answer = 42

add :: Int -> Int -> Int
add x y = x + y

main :: IO ()
main = do
  let n = add answer 1
  putStrLn (greet Baz)
";
        let tree = parse("Example.hs", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "module M where\ndata T = T\nfoo :: Int\nfoo = 1\nimport X\n";
        let tree = parse("M.hs", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::MODULE));
        assert!(kinds.contains(&node::DATA));
        assert!(kinds.contains(&node::SIGNATURE));
        assert!(kinds.contains(&node::BINDING));
        assert!(kinds.contains(&node::IMPORT));
    }

    #[test]
    fn indented_continuations_stay_in_one_item() {
        // The `data` declaration spans several indented lines: exactly one item.
        let src = "data T\n  = A\n  | B\nx = 1\n";
        let tree = parse("T.hs", src);
        let items: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert_eq!(items, vec![node::DATA, node::BINDING]);
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let depth = 10_000;
        let src = format!("x = {}{}", "(".repeat(depth), ")".repeat(depth));
        let tree = parse("deep.hs", &src);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics
                .iter()
                .any(|d| d.code == "haskell.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }
}
