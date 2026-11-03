//! Apex parser producing the language-neutral lossless CST. Forked from the Java
//! parser ([`crate::lang::java::parser`]) — same "precise headers, balanced
//! token-tree bodies" strategy — with the Apex deviations:
//!
//! - **Case-insensitive keyword matching.** [`ApexParser::at`] compares tokens
//!   case-insensitively, so `Public`, `WITH SHARING`, and `Trigger` are all
//!   recognized. Bytes are never altered; only the structural comparison folds
//!   case.
//! - **Sharing modifiers.** `with sharing` / `without sharing` /
//!   `inherited sharing` are two-word class modifiers, consumed in
//!   [`ApexParser::parse_modifiers`].
//! - **Triggers.** A top-level `trigger Name on SObject (before insert, …) { … }`
//!   parses to a [`node::TRIGGER`] with a `Name`, a `Header` (holding `on
//!   SObject (events)`), and a `Block` body. Inline SOQL/SOSL inside the body is
//!   captured as balanced `Bracket` groups, interpreted by the lowering.
//!
//! Anything unrecognized still lands in the tree as its exact tokens, so the
//! result always round-trips byte-for-byte. Recursion is depth-guarded at
//! [`MAX_DEPTH`].

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::apex::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const COMPILATION_UNIT: &str = "CompilationUnit";
    pub const CLASS: &str = "Class";
    pub const INTERFACE: &str = "Interface";
    pub const ENUM: &str = "Enum";
    pub const ANNOTATION_TYPE: &str = "AnnotationType";
    pub const TRIGGER: &str = "Trigger";
    pub const METHOD: &str = "Method";
    pub const FIELD: &str = "Field";
    pub const INIT_BLOCK: &str = "InitBlock";
    pub const ANNOTATION: &str = "Annotation";
    pub const ERROR_ITEM: &str = "ErrorItem";

    pub const NAME: &str = "Name";
    pub const HEADER: &str = "Header";
    pub const SIGNATURE: &str = "Signature";
    pub const PARAMS: &str = "Params";
    pub const FIELD_INIT: &str = "FieldInit";
    pub const ITEM_BLOCK: &str = "ItemBlock";

    pub const BLOCK: &str = "Block";
    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// The leading single-word declaration modifiers recognized before a declarator.
/// The two-word `with/without/inherited sharing` modifiers are handled specially
/// in [`ApexParser::parse_modifiers`].
const MODIFIER_KEYWORDS: &[&str] = &[
    "public",
    "private",
    "protected",
    "global",
    "static",
    "final",
    "abstract",
    "virtual",
    "override",
    "transient",
    "testmethod",
    "webservice",
];

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat balanced run.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = ApexParser {
        src: source,
        toks,
        i: 0,
        diags: Vec::new(),
        depth: 0,
    };
    let root = p.parse_compilation_unit();
    ParseTree {
        source_id: SourceId::from_path(path),
        path: path.to_string(),
        source: source.to_string(),
        root,
        diagnostics: p.diags,
    }
}

struct ApexParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> ApexParser<'s> {
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

    fn peek_kind(&self) -> Option<&'static str> {
        self.peek_kind_n(0)
    }

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

    /// Case-insensitive match of the next significant token (Apex keywords fold
    /// case; punctuation has no case, so this is exact for punctuation).
    fn at(&self, s: &str) -> bool {
        self.peek_n_text(0)
            .map(|t| t.eq_ignore_ascii_case(s))
            .unwrap_or(false)
    }

    fn at_n(&self, n: usize, s: &str) -> bool {
        self.peek_n_text(n)
            .map(|t| t.eq_ignore_ascii_case(s))
            .unwrap_or(false)
    }

    fn at_ident(&self) -> bool {
        self.peek_kind() == Some(tk::IDENT)
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

    // --- top level ----------------------------------------------------------

    fn parse_compilation_unit(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            let item = self.parse_top_item();
            c.push(Child::Node(item));
        }
        self.make_node(node::COMPILATION_UNIT, c)
    }

    fn parse_top_item(&mut self) -> Node {
        let mut c = Vec::new();
        self.parse_modifiers(&mut c);
        self.ws(&mut c);
        if self.at("trigger") {
            return self.finish_trigger(c);
        }
        self.finish_member_or_type(c)
    }

    /// `[modifiers] trigger Name on SObject (events) { body }`.
    fn finish_trigger(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // trigger
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        // `on SObject (before insert, after update, …)` up to the body.
        if let Some(h) = self.collect_region(node::HEADER, &["{", ";"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
        } else if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::TRIGGER, c)
    }

    // --- members and type declarations --------------------------------------

    fn parse_member(&mut self) -> Node {
        let mut c = Vec::new();
        self.parse_modifiers(&mut c);
        self.ws(&mut c);
        self.finish_member_or_type(c)
    }

    fn finish_member_or_type(&mut self, mut c: Vec<Child>) -> Node {
        if self.at_type_keyword() {
            return self.finish_type_decl(c);
        }
        // A static or instance initializer block: `{ ... }`.
        if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
            return self.make_node(node::INIT_BLOCK, c);
        }
        // Otherwise a method, constructor, field, or property. Collect the
        // declarator prefix up to the first significant `(`, `=`, `;`, or `{`.
        if let Some(sig) = self.collect_region(node::SIGNATURE, &["(", "=", ";", "{", "}"]) {
            c.push(Child::Node(sig));
        }
        self.ws(&mut c);
        if self.at("(") {
            // Method or constructor.
            let params = self.parse_delimited(Some(node::PARAMS));
            c.push(Child::Node(params));
            // Trailing clauses up to the body.
            if let Some(h) = self.collect_region(node::HEADER, &["{", ";"]) {
                c.push(Child::Node(h));
            }
            self.ws(&mut c);
            if self.at("{") {
                let b = self.parse_delimited(Some(node::BLOCK));
                c.push(Child::Node(b));
            } else if self.at(";") {
                self.eat(&mut c); // abstract / interface method
            }
            self.make_node(node::METHOD, c)
        } else {
            // Field or property declaration: capture the initializer / property
            // accessor block up to `;`.
            if let Some(h) = self.collect_region(node::FIELD_INIT, &[";", "}"]) {
                c.push(Child::Node(h));
            }
            self.ws(&mut c);
            if self.at(";") {
                self.eat(&mut c);
            }
            self.make_node(node::FIELD, c)
        }
    }

    /// `[modifiers] class|interface|enum|@interface Name <header> { body }`.
    fn finish_type_decl(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        let kind = if self.at("class") {
            node::CLASS
        } else if self.at("interface") {
            node::INTERFACE
        } else if self.at("enum") {
            node::ENUM
        } else {
            node::ANNOTATION_TYPE // `@interface`
        };
        if self.at("@") {
            self.eat(&mut c); // @
            self.ws(&mut c);
            self.eat(&mut c); // interface
        } else {
            self.eat(&mut c); // class/interface/enum
        }
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        // Generics, `extends`/`implements`.
        if let Some(h) = self.collect_region(node::HEADER, &["{", ";"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_item_block(node::ITEM_BLOCK);
            c.push(Child::Node(b));
        } else if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(kind, c)
    }

    /// `{ members }` parsed as a recursive member list.
    fn parse_item_block(&mut self, label: &'static str) -> Node {
        if self.depth >= MAX_DEPTH {
            let mut c = Vec::new();
            self.ws(&mut c);
            self.eat(&mut c); // {
            self.consume_balanced_flat(&mut c);
            self.note_depth_limit();
            return self.make_node(label, c);
        }
        self.depth += 1;
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // {
        loop {
            self.ws(&mut c);
            match self.peek_kind() {
                None => break,
                Some(_) if self.at("}") => {
                    self.eat(&mut c);
                    break;
                }
                Some(_) => {
                    let member = self.parse_member();
                    c.push(Child::Node(member));
                }
            }
        }
        let node = self.make_node(label, c);
        self.depth -= 1;
        node
    }

    /// Collect leading annotations, single-word modifiers, and the two-word
    /// `with/without/inherited sharing` modifiers into `c`. Stops before
    /// `@interface` (an annotation-type declaration, not an annotation).
    fn parse_modifiers(&mut self, c: &mut Vec<Child>) {
        loop {
            self.ws(c);
            if self.at("@") && !self.at_n(1, "interface") {
                let ann = self.parse_annotation();
                c.push(Child::Node(ann));
            } else if (self.at("with") || self.at("without") || self.at("inherited"))
                && self.at_n(1, "sharing")
            {
                self.eat(c); // with / without / inherited
                self.ws(c);
                self.eat(c); // sharing
            } else if self.at_modifier() {
                self.eat(c);
            } else {
                break;
            }
        }
    }

    /// `@Name` / `@a.b.Name` / `@Name(args)`.
    fn parse_annotation(&mut self) -> Node {
        let mut a = Vec::new();
        self.ws(&mut a);
        self.eat(&mut a); // @
        loop {
            self.ws(&mut a);
            if self.at_ident() {
                self.eat(&mut a);
            } else {
                break;
            }
            self.ws(&mut a);
            if self.at(".") {
                self.eat(&mut a);
            } else {
                break;
            }
        }
        self.ws(&mut a);
        if self.at("(") {
            let g = self.parse_delimited(None);
            a.push(Child::Node(g));
        }
        self.make_node(node::ANNOTATION, a)
    }

    // --- type keyword dispatch ----------------------------------------------

    fn at_modifier(&self) -> bool {
        self.peek_n_text(0)
            .map(|t| MODIFIER_KEYWORDS.iter().any(|m| m.eq_ignore_ascii_case(t)))
            .unwrap_or(false)
    }

    fn at_type_keyword(&self) -> bool {
        self.at("class")
            || self.at("interface")
            || self.at("enum")
            || (self.at("@") && self.at_n(1, "interface"))
    }

    // --- shared helpers -----------------------------------------------------

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.eat(&mut c); // the identifier (cursor is at it after caller ws)
        self.make_node(node::NAME, c)
    }

    /// Collect tokens (descending into balanced groups) until a significant stop
    /// token at delimiter depth 0, or end of input.
    fn collect_region(&mut self, label: &'static str, stops: &[&str]) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            if self.peek_kind().is_none() {
                break;
            }
            if stops.iter().any(|s| self.at(s)) {
                break;
            }
            if self.at_open() {
                self.ws(&mut c);
                let inner = self.parse_delimited(None);
                c.push(Child::Node(inner));
            } else {
                self.ws(&mut c);
                self.eat(&mut c);
            }
        }
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(label, c))
        }
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`.
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
            return self.make_node(label_override.unwrap_or(node::ERROR_ITEM), g);
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

    /// Iteratively consume a balanced delimiter run (opener already eaten).
    fn consume_balanced_flat(&mut self, out: &mut Vec<Child>) {
        let mut balance: i32 = 1;
        while balance > 0 {
            self.ws(out);
            if self.peek_kind().is_none() {
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
            code: "apex.depth_limit",
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
// a class
public with sharing class Point implements Comparable {
    private final Integer x;
    public Integer y { get; set; }

    public Point(Integer x, Integer y) {
        this.x = x;
        this.y = y;
    }

    @AuraEnabled
    public static List<Contact> load() {
        return [SELECT Id, Name FROM Contact WHERE Name = 'Bob'];
    }
}

public enum Season { WINTER, SPRING }
";
        let tree = parse("Point.cls", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_types() {
        let src = "class A {} interface B {} enum C { X }";
        let tree = parse("T.cls", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::CLASS), "class: {kinds:?}");
        assert!(kinds.contains(&node::INTERFACE), "interface: {kinds:?}");
        assert!(kinds.contains(&node::ENUM), "enum: {kinds:?}");
    }

    #[test]
    fn case_insensitive_keywords() {
        // Upper-cased keywords still parse structurally.
        let src = "PUBLIC WITHOUT SHARING CLASS C { PUBLIC VOID M() {} }";
        let tree = parse("C.cls", src);
        let class = tree.root.children_of(node::CLASS).next().expect("a class");
        let block = class.child(node::ITEM_BLOCK).expect("class body");
        assert_eq!(block.children_of(node::METHOD).count(), 1);
        assert!(tree.is_lossless());
    }

    #[test]
    fn trigger_is_parsed() {
        let src =
            "trigger CaseTrigger on Case (before insert, after update) {\n  System.debug('x');\n}";
        let tree = parse("CaseTrigger.trigger", src);
        let trig = tree
            .root
            .children_of(node::TRIGGER)
            .next()
            .expect("a Trigger node");
        assert_eq!(
            trig.child(node::NAME)
                .and_then(|n| n.tokens().next())
                .map(|t| t.span.text(src)),
            Some("CaseTrigger")
        );
        assert!(trig.child(node::BLOCK).is_some(), "trigger has a body");
        assert!(tree.is_lossless());
    }

    #[test]
    fn methods_and_fields_nest_in_class() {
        let src = "class C {\n  Integer field = 1;\n  void m() {}\n  C() {}\n}";
        let tree = parse("C.cls", src);
        let class = tree.root.children_of(node::CLASS).next().expect("a class");
        let block = class.child(node::ITEM_BLOCK).expect("class body");
        assert_eq!(block.children_of(node::METHOD).count(), 2, "m() + ctor");
        assert_eq!(block.children_of(node::FIELD).count(), 1, "one field");
    }

    #[test]
    fn inline_soql_is_a_bracket_group() {
        let src = "class C { void m() { List<Contact> cs = [SELECT Id FROM Contact]; } }";
        let tree = parse("C.cls", src);
        let has_bracket = tree.root.walk().any(|n| n.kind == node::BRACKET);
        assert!(has_bracket, "inline SOQL becomes a Bracket token tree");
        assert!(tree.is_lossless());
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let deep_braces = format!(
            "class C {{ void m() {{ {}{} }} }}",
            "{".repeat(10_000),
            "}".repeat(10_000)
        );
        let mut deep_types = String::new();
        for _ in 0..2_000 {
            deep_types.push_str("class C { ");
        }
        deep_types.push_str(&"}".repeat(2_000));
        for src in [deep_braces, deep_types] {
            let tree = parse("deep.cls", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics
                    .iter()
                    .any(|d| d.code == "apex.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "class C { void m() { foo(1, 2 }", // unterminated paren
            "class C { String s = '☃'; }",     // multi-byte string
            "",                                // empty file
            "// only a comment\n",             // no code
            "class C { ; ; }",                 // stray semicolons
        ] {
            let tree = parse("edge.cls", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
