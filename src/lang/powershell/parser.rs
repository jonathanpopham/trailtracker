//! PowerShell parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust, C#, and Bash parsers: definition *headers* are
//! parsed precisely — we always know a `function`/`filter` name, a `class` name
//! and its base list, an `enum` name, a `using` directive — while bodies and
//! command/expression regions are captured as balanced **token-tree groups**
//! (`Paren`/`Bracket`/`Brace`/`Block`) plus flat statement runs, which are
//! perfectly lossless. Graph facts (calls, base lists, assignments, imports) are
//! read off those real tokens in the lowering pass, never invented.
//!
//! PowerShell is statement-oriented (terminated by a newline or `;`) with C#-like
//! `class`/`enum` declarations. The parser recognizes:
//!   - `function Name { … }` / `filter Name { … }` definitions;
//!   - `class Name [ : Base, IFace ] { members }` with members classified as
//!     methods (header ends in a parameter list) or properties;
//!   - `enum Name { … }`;
//!   - `using module|namespace …` directives;
//!   - everything else as a `Statement` (one pipeline / control-flow line),
//!     capturing its `( … )` and `{ … }` regions as nested token-tree groups so
//!     the lowering can find calls inside them.
//!
//! Anything unrecognized still lands in the tree as its exact tokens, so the
//! result always round-trips byte-for-byte. Recursion is depth-guarded at
//! [`MAX_DEPTH`] against hostile bracket nesting, because a `catch_unwind` cannot
//! catch a stack overflow — the guard is the real defense.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::powershell::lexer::{kind as tk, lex};

/// CST node-kind labels. The lowering interprets these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const FUNCTION: &str = "Function";
    pub const CLASS: &str = "Class";
    pub const ENUM: &str = "Enum";
    pub const METHOD: &str = "Method";
    pub const PROPERTY: &str = "Property";
    pub const USING: &str = "Using";
    pub const STATEMENT: &str = "Statement";
    pub const ERROR_STMT: &str = "ErrorStmt";

    pub const NAME: &str = "Name";
    pub const HEADER: &str = "Header";
    pub const SIGNATURE: &str = "Signature";
    pub const INIT: &str = "Init";
    pub const ITEM_BLOCK: &str = "ItemBlock";
    pub const BLOCK: &str = "Block";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat run. Mirrors the Rust/C#/Bash guard exactly — a
/// `catch_unwind` cannot catch a stack overflow, so the guard is the real
/// defense against hostile nesting.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = PowerShellParser {
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

struct PowerShellParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl PowerShellParser<'_> {
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

    /// Eat trivia plus statement-separator "filler" (newlines and `;`) into
    /// `out`, leaving the cursor on the next real token, a `}`, or end of input.
    fn eat_fillers(&mut self, out: &mut Vec<Child>) {
        loop {
            self.ws(out);
            if self.peek_kind() == Some(tk::NEWLINE) || self.at(";") {
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

    fn at(&self, s: &str) -> bool {
        self.peek_n_text(0) == Some(s)
    }

    /// Case-insensitive keyword check at the cursor (PowerShell is case-
    /// insensitive).
    fn at_kw(&self, kw: &str) -> bool {
        matches!(self.peek_n_text(0), Some(t) if t.eq_ignore_ascii_case(kw))
    }

    fn at_ident(&self) -> bool {
        self.peek_kind() == Some(tk::IDENT)
    }

    fn at_newline(&self) -> bool {
        self.peek_kind() == Some(tk::NEWLINE)
    }

    fn at_open(&self) -> bool {
        self.at("(") || self.at("[") || self.at("{")
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

    /// True if the next significant token, skipping trivia and newlines, is `{`.
    fn brace_follows(&self) -> bool {
        let mut j = self.i;
        while j < self.toks.len() {
            let t = &self.toks[j];
            if t.trivia || t.kind == tk::NEWLINE {
                j += 1;
                continue;
            }
            return t.span.text(self.src) == "{";
        }
        false
    }

    /// Eat trivia and newlines up to a following `{` (Allman-style body brace on a
    /// later line), but only when a `{` actually follows — so a bodyless construct
    /// does not swallow the next statement.
    fn eat_to_brace(&mut self, out: &mut Vec<Child>) {
        if self.brace_follows() {
            while self.i < self.toks.len() {
                let t = &self.toks[self.i];
                if t.trivia || t.kind == tk::NEWLINE {
                    self.eat(out);
                } else {
                    break;
                }
            }
        }
    }

    // --- top level ----------------------------------------------------------

    fn parse_source_file(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.eat_fillers(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            let item = self.parse_item();
            c.push(Child::Node(item));
        }
        self.make_node(node::SOURCE_FILE, c)
    }

    // --- items --------------------------------------------------------------

    /// Parse one top-level / block-level item. The cursor is on a real
    /// (non-filler) token. Always makes progress.
    fn parse_item(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        if self.at_kw("function") || self.at_kw("filter") {
            self.finish_function(c)
        } else if self.at_kw("class") {
            self.finish_class(c)
        } else if self.at_kw("enum") {
            self.finish_enum(c)
        } else if self.at_kw("using") {
            self.finish_using(c)
        } else {
            self.finish_statement(c)
        }
    }

    /// `function Name [ (params) ] { body }` / `filter Name { body }`.
    fn finish_function(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // function / filter
        self.ws(&mut c);
        if self.at_ident() {
            c.push(Child::Node(self.name_node()));
        }
        self.ws(&mut c);
        if self.at("(") {
            let sig = self.parse_delimited(Some(node::SIGNATURE));
            c.push(Child::Node(sig));
        }
        self.eat_to_brace(&mut c);
        if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
        }
        self.make_node(node::FUNCTION, c)
    }

    /// `class Name [ : Base, IFace ] { members }`.
    fn finish_class(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // class
        self.ws(&mut c);
        if self.at_ident() {
            c.push(Child::Node(self.name_node()));
        }
        if let Some(h) = self.collect_header(&["{"]) {
            c.push(Child::Node(h));
        }
        self.eat_to_brace(&mut c);
        if self.at("{") {
            let b = self.parse_member_block();
            c.push(Child::Node(b));
        }
        self.make_node(node::CLASS, c)
    }

    /// `enum Name { … }` — the body is captured as a balanced token tree (enum
    /// members are simple value bindings the lowering does not need to split).
    fn finish_enum(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // enum
        self.ws(&mut c);
        if self.at_ident() {
            c.push(Child::Node(self.name_node()));
        }
        if let Some(h) = self.collect_header(&["{"]) {
            c.push(Child::Node(h));
        }
        self.eat_to_brace(&mut c);
        if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
        }
        self.make_node(node::ENUM, c)
    }

    /// `using module X` / `using namespace Y` / `using assembly Z`.
    fn finish_using(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // using
        if let Some(h) = self.collect_header(&[";"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::USING, c)
    }

    /// One statement / pipeline / control-flow line: significant tokens up to a
    /// depth-0 newline or `;`, descending into `( )` / `[ ]` / `{ }` groups so a
    /// whole `if (…) { … }` (and any nested script blocks) stays in one node. The
    /// lowering scans the captured groups to find calls.
    fn finish_statement(&mut self, mut c: Vec<Child>) -> Node {
        let mut consumed_any = false;
        loop {
            self.ws(&mut c);
            if self.peek_kind().is_none() || self.at_newline() || self.at(";") {
                break;
            }
            if self.at_open() {
                let g = self.parse_delimited(None);
                c.push(Child::Node(g));
                consumed_any = true;
            } else {
                self.eat(&mut c);
                consumed_any = true;
            }
        }
        if !consumed_any {
            // Degenerate: nothing significant before a terminator. Force progress
            // so the byte is never dropped and we never spin.
            self.eat(&mut c);
            return self.make_node(node::ERROR_STMT, c);
        }
        self.make_node(node::STATEMENT, c)
    }

    // --- class members ------------------------------------------------------

    /// Parse a class body `{ members }` as a recursive member list.
    fn parse_member_block(&mut self) -> Node {
        if self.depth >= MAX_DEPTH {
            let mut c = Vec::new();
            self.ws(&mut c);
            self.eat(&mut c); // {
            self.consume_balanced_flat(&mut c);
            self.note_depth_limit();
            return self.make_node(node::ITEM_BLOCK, c);
        }
        self.depth += 1;
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // {
        loop {
            self.eat_fillers(&mut c);
            match self.peek_kind() {
                None => break,
                Some(_) if self.at("}") => {
                    self.eat(&mut c);
                    break;
                }
                Some(_) => {
                    let m = self.finish_member();
                    c.push(Child::Node(m));
                }
            }
        }
        let n = self.make_node(node::ITEM_BLOCK, c);
        self.depth -= 1;
        n
    }

    /// A class member: a method/constructor (header ends in a parameter list and
    /// usually a block) or a property/field (`[type]$name [= init]`). Classified
    /// by whether a parameter list follows the header.
    fn finish_member(&mut self) -> Node {
        let mut c = Vec::new();
        if let Some(h) = self.collect_member_header() {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        let kind = if self.at("(") {
            let sig = self.parse_delimited(Some(node::SIGNATURE));
            c.push(Child::Node(sig));
            self.ws(&mut c);
            if self.at("{") {
                let b = self.parse_delimited(Some(node::BLOCK));
                c.push(Child::Node(b));
            }
            node::METHOD
        } else if self.at("{") {
            // Property with an accessor block (uncommon in PowerShell).
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
            node::PROPERTY
        } else if self.at("=") {
            if let Some(init) = self.collect_until_stmt_end(node::INIT) {
                c.push(Child::Node(init));
            }
            node::PROPERTY
        } else {
            node::PROPERTY
        };
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        // Guarantee progress on input we could not classify.
        if c.iter().all(is_trivia_child) {
            self.eat(&mut c);
            self.diags.push(Diagnostic {
                code: "powershell.unrecognized_member",
                message: "token(s) not recognized as a PowerShell class member".to_string(),
                span: children_span(&c).unwrap_or_else(|| ByteSpan::empty_at(self.cur_offset())),
            });
            return self.make_node(node::ERROR_STMT, c);
        }
        self.make_node(kind, c)
    }

    /// Collect a member header (`[type]`, modifiers, the member name) up to the
    /// first structural decider: a parameter list `(`, a block `{`, an
    /// initializer `=`, a `;`, a `}`, or a depth-0 newline. Descends into `[ ]`
    /// type/attribute groups.
    fn collect_member_header(&mut self) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            if self.peek_kind().is_none() || self.at_newline() {
                break;
            }
            if self.at("(") || self.at("{") || self.at("=") || self.at(";") || self.at("}") {
                break;
            }
            if self.at("[") {
                let g = self.parse_delimited(None);
                c.push(Child::Node(g));
            } else {
                self.eat(&mut c);
            }
        }
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(node::HEADER, c))
        }
    }

    // --- shared helpers -----------------------------------------------------

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.eat(&mut c); // the identifier (cursor is at it after caller ws)
        self.make_node(node::NAME, c)
    }

    /// Collect a header region (a class base list, an `enum` underlying type, a
    /// `using` target) until a depth-0 stop token, a `}`, or a newline, descending
    /// into balanced groups. Returns `None` if nothing significant was collected.
    fn collect_header(&mut self, stops: &[&str]) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            if self.peek_kind().is_none() || self.at_newline() {
                break;
            }
            if self.at("}") || stops.iter().any(|s| self.at(s)) {
                break;
            }
            self.ws(&mut c);
            if self.at_open() {
                let g = self.parse_delimited(None);
                c.push(Child::Node(g));
            } else {
                self.eat(&mut c);
            }
        }
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(node::HEADER, c))
        }
    }

    /// Collect tokens up to a depth-0 newline or `;`, descending into groups.
    fn collect_until_stmt_end(&mut self, label: &'static str) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            if self.peek_kind().is_none() || self.at_newline() || self.at(";") {
                break;
            }
            self.ws(&mut c);
            if self.at_open() {
                let g = self.parse_delimited(None);
                c.push(Child::Node(g));
            } else {
                self.eat(&mut c);
            }
        }
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(label, c))
        }
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`. Cursor is at
    /// (or before trivia preceding) the opener.
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
            // Defensive: not actually at an opener.
            return self.make_node(label_override.unwrap_or(node::ERROR_STMT), g);
        };
        let label = label_override.unwrap_or(default_label);
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
                    let inner = self.parse_delimited(None);
                    self.depth -= 1;
                    g.push(Child::Node(inner));
                } else {
                    // Depth cap: flatten the nested group rather than recursing.
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

    /// Iteratively consume a balanced delimiter run (the opener already eaten),
    /// appending every token as a flat leaf. Used at the depth cap so arbitrarily
    /// deep nesting is handled without further recursion.
    fn consume_balanced_flat(&mut self, out: &mut Vec<Child>) {
        let mut balance: i32 = 1;
        while balance > 0 {
            self.ws(out);
            match self.peek_n_text(0) {
                None => break,
                Some("(") | Some("[") | Some("{") => balance += 1,
                Some(")") | Some("]") | Some("}") => balance -= 1,
                _ => {}
            }
            self.eat(out);
        }
    }

    /// Record (once per truncation is enough) that the depth cap flattened
    /// structure — reported, never silent.
    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "powershell.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; group flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }
}

fn is_trivia_child(c: &Child) -> bool {
    matches!(c, Child::Token(t) if t.trivia)
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

    fn kinds_of(root: &Node) -> Vec<&'static str> {
        root.child_nodes().map(|n| n.kind).collect()
    }

    #[test]
    fn parses_and_is_lossless() {
        let src = "\
# a script
using module Pester

$script:Config = 'prod'

function Get-Greeting {
    param([string]$Name)
    Write-Output \"hello, $Name\"
}

class Animal : System.Object, IComparable {
    [string]$Name
    static [int]$Count = 0
    Animal([string]$name) { $this.Name = $name }
    [string] Speak() {
        return (Get-Greeting -Name $this.Name)
    }
}

enum Color { Red; Green; Blue }

if ($script:Config -eq 'prod') {
    Get-Greeting -Name 'world' | Write-Host
} else {
    Write-Host 'dev'
}
";
        let tree = parse("script.ps1", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "function F {}\nclass C { [int]$x; C() {} M() {} }\nenum E { A }\nusing namespace System\n$x = 1\n";
        let tree = parse("t.ps1", src);
        let top = kinds_of(&tree.root);
        assert!(top.contains(&node::FUNCTION), "function: {top:?}");
        assert!(top.contains(&node::CLASS), "class: {top:?}");
        assert!(top.contains(&node::ENUM), "enum: {top:?}");
        assert!(top.contains(&node::USING), "using: {top:?}");
        assert!(top.contains(&node::STATEMENT), "statement: {top:?}");
    }

    #[test]
    fn classifies_class_members() {
        let src = "class C { [int]$Count; C() {} [void] Run([int]$n) { } }";
        let tree = parse("t.ps1", src);
        let class = tree.root.child(node::CLASS).expect("a class");
        let body = class.child(node::ITEM_BLOCK).expect("class body");
        let members = kinds_of(body);
        assert!(members.contains(&node::PROPERTY), "property: {members:?}");
        assert_eq!(
            members.iter().filter(|k| **k == node::METHOD).count(),
            2,
            "ctor + method: {members:?}"
        );
    }

    #[test]
    fn case_insensitive_keywords() {
        let src = "FUNCTION Foo {}\nClass Bar {}\n";
        let tree = parse("t.ps1", src);
        let top = kinds_of(&tree.root);
        assert!(top.contains(&node::FUNCTION));
        assert!(top.contains(&node::CLASS));
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let depth = 10_000;
        let src = format!(
            "function X {{ {}{} }}",
            "(".repeat(depth),
            ")".repeat(depth)
        );
        let tree = parse("deep.ps1", &src);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics
                .iter()
                .any(|d| d.code == "powershell.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }

    #[test]
    fn edge_inputs_round_trip() {
        for src in [
            "",                                    // empty
            "   \n\t  \n",                         // only trivia
            "<# unterminated block comment",       // unterminated block comment
            "\"unterminated string",               // unterminated string
            "@\"\nno closer here\n",               // unterminated here-string
            "$x = @{ a = 1; b = 2 }",              // hashtable
            "Get-Foo | Where-Object { $_ -gt 1 }", // pipeline + script block
            "λ ☃ €",                               // non-ascii error tokens
        ] {
            let tree = parse("edge.ps1", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }

    #[test]
    fn output_is_deterministic() {
        let src = "class C : B { M() { f } }\n$x = 1\n";
        let a = parse("t.ps1", src);
        let b = parse("t.ps1", src);
        assert_eq!(a.to_json().to_line(), b.to_json().to_line());
    }
}
