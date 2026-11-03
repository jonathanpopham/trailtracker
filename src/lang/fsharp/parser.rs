//! F# parser producing the language-neutral lossless CST.
//!
//! Strategy (honest, breadth-growable): F# is layout-sensitive (the offside
//! rule), and we do **not** reimplement the full layout algorithm. Instead we
//! carve the file into top-level *items* using the one robust, lossless signal
//! that does not require layout: a declaration head is a non-trivia token sitting
//! in **byte-column 0** (start of file, or immediately after a newline with no
//! leading whitespace). Everything from one column-0 head up to (but not
//! including) the next is one item — its continuation / indented lines never look
//! like heads, and balanced delimiter groups (`(...)`, `[...]`, `{...}`) are
//! consumed whole so a column-0 token *inside* a multi-line group never falsely
//! ends the item.
//!
//! This means an indented type body (its `member` / `inherit` / `interface`
//! lines) is captured *inside* its `type` item; the lowering pass walks that
//! region to recover methods and base types. The same is true for an indented
//! `module X =` block — see [`lower`](super::lower) for the honest punt there.
//!
//! Each item is classified by the first *structural* keyword among its top-level
//! tokens (`namespace`, `module`, `open`, `type`, `let`, `member`, `inherit`,
//! `interface`, `do`), skipping leading attributes (`[< ... >]`) and access /
//! binding modifiers. Names and graph facts are extracted from the real tokens in
//! the lowering pass — never invented. Anything unrecognized becomes an
//! `ErrorItem` node that still contains its exact source tokens, so the tree
//! always round-trips.
//!
//! The delimiter recursion is depth-guarded at [`MAX_DEPTH`] (mirroring the Rust
//! parser): beyond the cap the remaining group is consumed as a flat balanced
//! run with a `depth_limit` diagnostic, because a `catch_unwind` cannot catch a
//! stack overflow.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::fsharp::lexer::{is_keyword, kind as tk, lex};

/// CST node-kind labels. The lowering interprets these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const NAMESPACE: &str = "Namespace";
    pub const MODULE: &str = "Module";
    pub const OPEN: &str = "Open";
    pub const TYPE_DECL: &str = "TypeDecl";
    /// A top-level value/function binding `let [rec] name … = …`.
    pub const BINDING: &str = "Binding";
    /// A `member` / `static member` / `abstract` declaration sitting at column 0
    /// (rare — members usually live indented inside a `type` item).
    pub const MEMBER: &str = "Member";
    pub const INHERIT: &str = "Inherit";
    pub const INTERFACE: &str = "Interface";
    /// A module-level `do` expression binding.
    pub const DO: &str = "Do";
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
    let mut p = FSharpParser {
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

struct FSharpParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    depth: usize,
}

impl<'s> FSharpParser<'s> {
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
                code: "fsharp.unrecognized_item",
                message: "token(s) not recognized as an F# top-level item".to_string(),
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
            code: "fsharp.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; group flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }
}

/// Access / binding modifiers that may precede a structural keyword and must be
/// skipped when locating it (`let private rec`, `static member`, `abstract`,
/// `override`, `default`, `[<Attr>] let`, …). `abstract`/`override`/`default`
/// stay out of this set: they are themselves member-introducing.
fn is_modifier(text: &str) -> bool {
    matches!(
        text,
        "rec" | "mutable" | "inline" | "private" | "internal" | "public" | "static" | "and"
    )
}

/// Classify an item by the first *structural* keyword among its top-level tokens,
/// skipping leading attribute groups and modifiers. The keyword set is the one
/// the lowering knows how to read.
fn classify(children: &[Child], src: &str) -> &'static str {
    for c in children {
        match c {
            // Attribute groups (`[< ... >]`) and any other leading group are
            // skipped: they never *are* the declaration keyword.
            Child::Node(_) => continue,
            Child::Token(t) if t.trivia || t.kind == tk::NEWLINE => continue,
            Child::Token(t) => {
                let text = t.span.text(src);
                if is_modifier(text) {
                    continue;
                }
                return match text {
                    "namespace" => node::NAMESPACE,
                    "module" => node::MODULE,
                    "open" => node::OPEN,
                    "type" => node::TYPE_DECL,
                    "let" | "use" | "extern" => node::BINDING,
                    "member" | "abstract" | "override" | "default" | "new" | "val" => node::MEMBER,
                    "inherit" => node::INHERIT,
                    "interface" => node::INTERFACE,
                    "do" => node::DO,
                    // A non-keyword head (e.g. a bare expression or a stray `|`
                    // DU case at column 0): an error item, still lossless.
                    _ => node::ERROR_ITEM,
                };
            }
        }
    }
    node::ERROR_ITEM
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

/// Whether `text` is a recognized structural keyword (used by the lowering's
/// within-item scans). Kept here next to [`classify`] so the two stay in sync.
pub fn is_structural_keyword(text: &str) -> bool {
    is_keyword(text)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_and_is_lossless() {
        let src = "\
// | Example module.
namespace Example.Library

open System
open System.Collections.Generic

/// A record type.
type Point =
    { X: int
      Y: int }
    member this.Norm () = this.X + this.Y

type Shape =
    | Circle of float
    | Square of float

[<AbstractClass>]
type Base() =
    abstract member Area : unit -> float

type Derived() =
    inherit Base()
    interface IDisposable with
        member this.Dispose () = ()
    override this.Area () = 0.0

let answer = 42

let rec add x y = x + y

let main () =
    let n = add answer 1
    printfn \"%d\" n
";
        let tree = parse("Example.fs", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "namespace N\nopen System\ntype T = T\nlet foo x = x\nlet bar = 1\n";
        let tree = parse("N.fs", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::NAMESPACE));
        assert!(kinds.contains(&node::OPEN));
        assert!(kinds.contains(&node::TYPE_DECL));
        assert!(kinds.contains(&node::BINDING));
    }

    #[test]
    fn indented_members_stay_in_type_item() {
        // The `type` declaration spans several indented member lines: one item.
        let src = "type T() =\n    member this.A () = 1\n    member this.B () = 2\nlet x = 1\n";
        let tree = parse("T.fs", src);
        let items: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert_eq!(items, vec![node::TYPE_DECL, node::BINDING]);
    }

    #[test]
    fn attributes_and_modifiers_do_not_hide_the_keyword() {
        let src = "[<EntryPoint>]\nlet private main argv = 0\n";
        let tree = parse("M.fs", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::BINDING));
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let depth = 10_000;
        let src = format!("let x = {}{}", "(".repeat(depth), ")".repeat(depth));
        let tree = parse("deep.fs", &src);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics
                .iter()
                .any(|d| d.code == "fsharp.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }
}
