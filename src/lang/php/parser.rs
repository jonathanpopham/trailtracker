//! PHP parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust and Python parsers: item *headers* are parsed
//! precisely — we always know a `function`'s name, a `class`'s `extends`/
//! `implements`, a `namespace` path, a `use` import — while bodies and expression
//! regions are captured as balanced delimiter groups (`Paren`/`Bracket`/`Brace`)
//! plus flat tokens, which is perfectly lossless. Graph facts (calls, type refs,
//! base classes) are extracted from those real tokens in the lowering pass, never
//! invented.
//!
//! Unlike Python, PHP blocks are brace-delimited, so the parser is closer in
//! shape to the Rust one: a `{ … }` body is a [`node::BLOCK`] of nested items.
//! PHP is also a *template* language — files start in HTML mode — so the lexer's
//! `inline_html` / `open_tag` / `close_tag` tokens (which are non-trivia) appear
//! interleaved with code and are captured as [`node::MARKUP`] nodes.
//!
//! Anything unrecognized still lands in the tree as its exact tokens (a
//! [`node::SIMPLE_STMT`] / [`node::ERROR_STMT`] node), so the result always
//! round-trips byte-for-byte. The recursion is depth-guarded at [`MAX_DEPTH`]
//! against hostile nesting — a `catch_unwind` cannot catch a stack overflow, so
//! the guard is the real defense.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::php::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const NAMESPACE: &str = "Namespace";
    pub const FUNCTION: &str = "Function";
    pub const CLASS: &str = "Class";
    pub const INTERFACE: &str = "Interface";
    pub const TRAIT: &str = "Trait";
    pub const ENUM: &str = "Enum";
    pub const USE: &str = "Use";
    pub const REQUIRE: &str = "Require";
    pub const CONST: &str = "Const";
    pub const ATTRIBUTE: &str = "Attribute";
    pub const COMPOUND: &str = "Compound";
    pub const SIMPLE_STMT: &str = "SimpleStmt";
    pub const ERROR_STMT: &str = "ErrorStmt";
    pub const MARKUP: &str = "Markup";

    pub const NAME: &str = "Name";
    pub const HEADER: &str = "Header";
    pub const BLOCK: &str = "Block";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat balanced run. Protects against stack overflow on
/// pathological or hostile inputs — mirrors the Rust/Python guard exactly.
const MAX_DEPTH: usize = 256;

/// Statement-introducing keywords that own a brace `{ … }` *block* (as opposed to
/// an expression like `match` whose braces are just a group).
const CONTROL_KEYWORDS: &[&str] = &[
    "if", "else", "elseif", "for", "foreach", "while", "do", "switch", "try", "catch", "finally",
    "declare",
];

/// Member/visibility modifiers that may precede a definition.
const MODIFIERS: &[&str] = &[
    "abstract",
    "final",
    "readonly",
    "public",
    "private",
    "protected",
    "static",
    "var",
];

const REQUIRE_KEYWORDS: &[&str] = &["require", "require_once", "include", "include_once"];

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = PhpParser {
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

struct PhpParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    depth: usize,
}

impl<'s> PhpParser<'s> {
    // --- cursor primitives --------------------------------------------------

    /// Append the current token (trivia or not) to `out` and advance.
    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading **trivia** tokens (whitespace, comments) into
    /// `out`. Markup tokens (`inline_html`/`open_tag`/`close_tag`) are *not*
    /// trivia and are left in place — they are handled as [`node::MARKUP`].
    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
        }
    }

    /// Kind of the n-th significant (non-trivia) token from the cursor.
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

    /// Text of the n-th significant token from the cursor. The lifetime is tied to
    /// the *source* (`'s`), not to the `&self` borrow, so the result can be matched
    /// while `&mut self` parsing methods run in the match arms (the `span` is
    /// `Copy`, so no borrow of `self` is held).
    fn peek_n_text(&self, n: usize) -> Option<&'s str> {
        let mut j = self.i;
        let mut count = 0;
        while j < self.toks.len() {
            if self.toks[j].trivia {
                j += 1;
                continue;
            }
            if count == n {
                let span = self.toks[j].span; // `ByteSpan` is `Copy`
                return Some(span.text(self.src));
            }
            count += 1;
            j += 1;
        }
        None
    }

    fn peek_text(&self) -> Option<&'s str> {
        self.peek_n_text(0)
    }

    /// Case-insensitive match against the next significant token's text (PHP
    /// keywords are case-insensitive).
    fn at(&self, s: &str) -> bool {
        self.peek_text()
            .map(|t| t.eq_ignore_ascii_case(s))
            .unwrap_or(false)
    }

    fn at_open(&self) -> bool {
        matches!(self.peek_text(), Some("(") | Some("[") | Some("{"))
    }

    fn at_markup(&self) -> bool {
        matches!(
            self.peek_kind(),
            Some(tk::INLINE_HTML) | Some(tk::OPEN_TAG) | Some(tk::CLOSE_TAG)
        )
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
            let mut lead = Vec::new();
            self.ws(&mut lead);
            if self.i >= self.toks.len() {
                c.extend(lead); // trailing trivia
                break;
            }
            let item = self.parse_item(lead);
            c.push(Child::Node(item));
        }
        self.make_node(node::SOURCE_FILE, c)
    }

    /// Parse one top-level or block-level item, prefixed with any already-eaten
    /// leading trivia. Always consumes at least one token (progress guaranteed).
    fn parse_item(&mut self, mut c: Vec<Child>) -> Node {
        // Verbatim template markup (inline HTML / `<?php` / `?>`).
        if self.at_markup() {
            self.eat(&mut c);
            return self.make_node(node::MARKUP, c);
        }

        // Leading PHP 8 attributes `#[ … ]` attach to the definition they precede.
        while self.peek_text() == Some("#[") {
            let attr = self.parse_attribute();
            c.push(Child::Node(attr));
            self.ws(&mut c);
        }

        // Visibility / abstract / final / readonly / static modifiers.
        while self.at_modifier() {
            self.eat(&mut c);
            self.ws(&mut c);
        }

        if self.at_named_function() {
            self.finish_function(c)
        } else if self.at("class") {
            self.finish_classlike(c, node::CLASS)
        } else if self.at("interface") {
            self.finish_classlike(c, node::INTERFACE)
        } else if self.at("trait") {
            self.finish_classlike(c, node::TRAIT)
        } else if self.at("enum") && self.peek_kind_n(1) == Some(tk::NAME) {
            self.finish_classlike(c, node::ENUM)
        } else if self.at("namespace") {
            self.finish_namespace(c)
        } else if self.at("use") {
            self.finish_use(c)
        } else if self.at("const") {
            self.finish_const(c)
        } else if self.at_require() {
            self.finish_require(c)
        } else {
            self.finish_statement(c)
        }
    }

    fn at_modifier(&self) -> bool {
        // A modifier only counts if it actually precedes another definition token
        // or another modifier — otherwise (e.g. `static::x()`, `static $v;`) it is
        // part of an ordinary statement and is collected there. We accept it as a
        // modifier when the following significant token is itself a modifier or a
        // definition keyword.
        match self.peek_text() {
            Some(t) if MODIFIERS.iter().any(|m| t.eq_ignore_ascii_case(m)) => {
                matches!(
                    self.peek_n_text(1).map(|s| s.to_ascii_lowercase()),
                    Some(ref n) if MODIFIERS.contains(&n.as_str())
                        || matches!(n.as_str(),
                            "function" | "class" | "const" | "interface" | "trait" | "enum")
                )
            }
            _ => false,
        }
    }

    fn at_require(&self) -> bool {
        match self.peek_text() {
            Some(t) => REQUIRE_KEYWORDS.iter().any(|k| t.eq_ignore_ascii_case(k)),
            None => false,
        }
    }

    /// `function NAME(...)` / `function &NAME(...)` — a *named* definition, as
    /// opposed to an anonymous closure `function (...) {…}` (an expression).
    fn at_named_function(&self) -> bool {
        if !self.at("function") {
            return false;
        }
        if self.peek_n_text(1) == Some("&") {
            self.peek_kind_n(2) == Some(tk::NAME)
        } else {
            self.peek_kind_n(1) == Some(tk::NAME)
        }
    }

    // --- definitions --------------------------------------------------------

    /// `function [&] NAME (params) [: ret] { body }` or `… ;` (abstract/interface
    /// method).
    fn finish_function(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // function
        self.ws(&mut c);
        if self.at("&") {
            self.eat(&mut c);
            self.ws(&mut c);
        }
        if self.peek_kind() == Some(tk::NAME) {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(h) = self.collect_header() {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("{") {
            let block = self.parse_block();
            c.push(Child::Node(block));
        } else if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::FUNCTION, c)
    }

    /// `class/interface/trait/enum NAME [extends …] [implements …] [: backing] {…}`.
    fn finish_classlike(&mut self, mut c: Vec<Child>, kind: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // the class-like keyword
        self.ws(&mut c);
        if self.peek_kind() == Some(tk::NAME) {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(h) = self.collect_header() {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("{") {
            let block = self.parse_block();
            c.push(Child::Node(block));
        } else if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(kind, c)
    }

    /// `namespace A\B;` or `namespace A\B { … }` (or the bare global `namespace {`).
    fn finish_namespace(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // namespace
        if let Some(h) = self.collect_header() {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("{") {
            let block = self.parse_block();
            c.push(Child::Node(block));
        } else if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::NAMESPACE, c)
    }

    /// `use A\B\C [as D];`, `use function A\b;`, `use A\{B, C};`, and in-class
    /// `use Trait { … }` adaptations. Everything up to the terminating `;` is
    /// captured (descending into any group, including `{}` adaptation blocks).
    fn finish_use(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // use
        self.collect_until_semicolon(&mut c);
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::USE, c)
    }

    /// `const NAME = expr [, NAME2 = expr2 …];`.
    fn finish_const(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // const
        self.collect_until_semicolon(&mut c);
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::CONST, c)
    }

    /// `require|require_once|include|include_once expr;`.
    fn finish_require(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // the require/include keyword
        self.collect_until_semicolon(&mut c);
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::REQUIRE, c)
    }

    /// PHP 8 attribute `#[ … ]`. The opener `#[` is one punct token; the matching
    /// `]` closes it. Inner balanced groups are captured.
    fn parse_attribute(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // `#[`
        loop {
            self.ws(&mut c);
            match self.peek_text() {
                None => break,
                Some("]") => {
                    self.eat(&mut c);
                    break;
                }
                _ if self.at_open() => {
                    let g = self.parse_delimited();
                    c.push(Child::Node(g));
                }
                _ => self.eat(&mut c),
            }
        }
        self.make_node(node::ATTRIBUTE, c)
    }

    // --- statements ---------------------------------------------------------

    /// A non-definition statement. Collects tokens (descending into balanced
    /// groups) up to a terminating `;`, a control-structure body `{ … }`, or the
    /// enclosing block's `}`. A trailing brace block makes it a [`node::COMPOUND`]
    /// (so nested definitions inside `if`/`for`/etc. are still discovered);
    /// otherwise it is a [`node::SIMPLE_STMT`]. Guaranteed to consume ≥1 token.
    fn finish_statement(&mut self, mut c: Vec<Child>) -> Node {
        let control = matches!(
            self.peek_text().map(|s| s.to_ascii_lowercase()),
            Some(ref t) if CONTROL_KEYWORDS.contains(&t.as_str())
        );
        let mut consumed = false;
        let mut has_block = false;
        loop {
            self.ws(&mut c);
            match self.peek_text() {
                None => break,
                Some(";") => {
                    self.eat(&mut c);
                    consumed = true;
                    break;
                }
                Some("}") => break, // closes the enclosing block; leave it
                Some("{") => {
                    if control || !consumed {
                        // A control-structure body or a bare `{ … }` block: parse
                        // it as nested items so definitions inside are found.
                        let block = self.parse_block();
                        c.push(Child::Node(block));
                        has_block = true;
                        consumed = true;
                        break;
                    } else {
                        // An expression brace (`match (…) { … }`, array, closure):
                        // capture it as a group, not a statement block.
                        let g = self.parse_delimited();
                        c.push(Child::Node(g));
                        consumed = true;
                    }
                }
                _ if self.at_markup() => break, // markup starts a new item
                _ if self.at_open() => {
                    let g = self.parse_delimited();
                    c.push(Child::Node(g));
                    consumed = true;
                }
                _ => {
                    self.eat(&mut c);
                    consumed = true;
                }
            }
        }
        if !consumed {
            // Defensive: a stray `}` or markup at statement position — guarantee
            // forward progress by consuming exactly one token.
            self.eat(&mut c);
            return self.make_node(node::ERROR_STMT, c);
        }
        let kind = if has_block {
            node::COMPOUND
        } else {
            node::SIMPLE_STMT
        };
        self.make_node(kind, c)
    }

    // --- shared helpers -----------------------------------------------------

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.eat(&mut c); // the identifier (cursor is at it after caller ws)
        self.make_node(node::NAME, c)
    }

    /// Collect a definition header — tokens (descending into `()`/`[]` groups) up
    /// to the body `{` or the terminating `;` at depth 0. The `{`/`;` itself stays
    /// with the parent. Used for function signatures, class `extends`/`implements`
    /// clauses, and namespace paths.
    fn collect_header(&mut self) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            match self.peek_text() {
                None => break,
                Some("{") | Some(";") | Some("}") => break,
                _ if self.at_markup() => break,
                Some("(") | Some("[") => {
                    let g = self.parse_delimited();
                    c.push(Child::Node(g));
                }
                _ => self.eat(&mut c),
            }
        }
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(node::HEADER, c))
        }
    }

    /// Collect tokens (descending into *all* balanced groups, including `{}`) up
    /// to the terminating `;` at depth 0, leaving the `;` for the caller. Used by
    /// `use`/`const`/`require` whose bodies are never statement blocks.
    fn collect_until_semicolon(&mut self, out: &mut Vec<Child>) {
        loop {
            self.ws(out);
            match self.peek_text() {
                None => break,
                Some(";") | Some("}") => break,
                _ if self.at_markup() => break,
                _ if self.at_open() => {
                    let g = self.parse_delimited();
                    out.push(Child::Node(g));
                }
                _ => self.eat(out),
            }
        }
    }

    /// Parse a brace `{ … }` block as a sequence of nested items. Depth-guarded:
    /// beyond [`MAX_DEPTH`] the body is consumed as a flat balanced run rather than
    /// recursing, so deeply nested braces cannot overflow.
    fn parse_block(&mut self) -> Node {
        if self.depth >= MAX_DEPTH {
            let mut c = Vec::new();
            self.eat(&mut c); // `{`
            self.consume_balanced_flat(&mut c);
            self.note_depth_limit();
            return self.make_node(node::BLOCK, c);
        }
        self.depth += 1;
        let mut c = Vec::new();
        self.eat(&mut c); // `{`
        loop {
            let mut lead = Vec::new();
            self.ws(&mut lead);
            match self.peek_text() {
                None => {
                    c.extend(lead); // unterminated block; still lossless
                    break;
                }
                Some("}") => {
                    c.extend(lead);
                    self.eat(&mut c); // `}`
                    break;
                }
                _ => {
                    let item = self.parse_item(lead);
                    c.push(Child::Node(item));
                }
            }
        }
        self.depth -= 1;
        self.make_node(node::BLOCK, c)
    }

    /// Parse a balanced delimiter group `(…)`, `[…]`, or `{…}` as a *flat token*
    /// group (its contents are not parsed as statements). Depth-guarded.
    fn parse_delimited(&mut self) -> Node {
        let mut g = Vec::new();
        self.ws(&mut g);
        let (close, label) = match self.peek_text() {
            Some("(") => (")", node::PAREN),
            Some("[") => ("]", node::BRACKET),
            Some("{") => ("}", node::BRACE),
            _ => return self.make_node(node::ERROR_STMT, g), // defensive
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
                _ if self.at_open() => {
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

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "php.depth_limit",
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
<?php
namespace App\\Models;

use App\\Contracts\\Saveable;
require_once 'helpers.php';

const VERSION = '1.0';

#[Entity]
abstract class Point implements Saveable
{
    use Loggable;

    public int $x = 0;

    public function __construct(int $x, int $y)
    {
        $this->x = $x;
        $this->y = $y;
    }

    public function norm(): float
    {
        return sqrt($this->x * $this->x + $this->y * $this->y);
    }
}

interface Saveable
{
    public function save(): bool;
}

function add(int $a, int $b): int
{
    if ($a > $b) {
        return $a;
    } else {
        return $b;
    }
}
?>
<p>Trailing markup</p>
";
        let tree = parse("mod.php", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "<?php\nuse A\\B;\nclass C {\n    public function m() {}\n}\nfunction f() {}\n";
        let tree = parse("t.php", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::USE), "use not found: {kinds:?}");
        assert!(kinds.contains(&node::CLASS), "class not found: {kinds:?}");
        assert!(
            kinds.contains(&node::FUNCTION),
            "function not found: {kinds:?}"
        );
    }

    #[test]
    fn methods_nest_inside_class_blocks() {
        let src = "<?php class C {\n  public function a() {}\n  private function b() {}\n}\n";
        let tree = parse("t.php", src);
        let class = tree
            .root
            .children_of(node::CLASS)
            .next()
            .expect("a class node");
        let block = class.child(node::BLOCK).expect("class has a block");
        let methods: Vec<&str> = block
            .children_of(node::FUNCTION)
            .filter_map(|f| f.child(node::NAME))
            .filter_map(|n| n.tokens().next())
            .map(|t| t.span.text(src))
            .collect();
        assert_eq!(methods, vec!["a", "b"]);
    }

    #[test]
    fn abstract_method_without_body() {
        let src = "<?php interface I {\n  public function go(): void;\n}\n";
        let tree = parse("t.php", src);
        let iface = tree
            .root
            .children_of(node::INTERFACE)
            .next()
            .expect("an interface");
        let block = iface.child(node::BLOCK).expect("interface block");
        assert!(block.children_of(node::FUNCTION).next().is_some());
        assert!(tree.is_lossless());
    }

    #[test]
    fn match_braces_are_not_a_block() {
        // `match` braces must be captured as an expression group, not split into a
        // statement block, and the statement must still round-trip.
        let src = "<?php $y = match ($x) { 1 => 'a', default => 'b' };\n";
        let tree = parse("t.php", src);
        assert!(tree.is_lossless());
        // It is a simple statement, not a compound (no nested-item block).
        assert!(tree.root.children_of(node::COMPOUND).next().is_none());
    }

    #[test]
    fn inline_html_round_trips() {
        let src = "<ul>\n<?php foreach ($xs as $x): ?>\n<li><?= $x ?></li>\n<?php endforeach; ?>\n</ul>\n";
        let tree = parse("tpl.php", src);
        assert!(tree.is_lossless(), "template must round-trip");
        assert!(tree.root.children_of(node::MARKUP).next().is_some());
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        // Far deeper than MAX_DEPTH on both axes; must not stack-overflow and must
        // stay lossless.
        let deep_parens = format!("<?php $x = {}{};\n", "(".repeat(10_000), ")".repeat(10_000));
        let deep_braces = format!("<?php {}{}\n", "if(true){".repeat(5_000), "}".repeat(5_000));
        for src in [deep_parens, deep_braces] {
            let tree = parse("deep.php", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics.iter().any(|d| d.code == "php.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "<?php function f( {\n",           // unterminated paren
            "<?php $λ = '☃';\n",               // multi-byte identifiers/strings
            "",                                // empty file
            "plain html, no php at all\n",     // never enters PHP mode
            "<?php $s = <<<EOT\nunterminated", // unterminated heredoc
        ] {
            let tree = parse("edge.php", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
