//! Swift parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust parser ([`crate::lang::rust::parser`]): item
//! *headers* are parsed precisely — we always know a `func`'s name, a type's
//! name, an `import` path, a property's binder — while bodies and expression
//! regions are captured as balanced **token-tree groups** (`Paren`/`Bracket`/
//! `Brace`) plus flat tokens, which is perfectly lossless. Graph facts (calls,
//! type refs, inheritance) are extracted from these real tokens in the lowering
//! pass, never invented.
//!
//! Swift, like Rust, is brace-delimited (newlines are trivia), so type bodies are
//! recursively parsed as member item lists and nested definitions stay
//! first-class. Because Swift has no statement terminator, header/signature
//! regions stop at the body `{`, the enclosing `}`, or the start of the next
//! member declaration (a declaration keyword or `@attribute`). Type-position
//! keywords like `Self`/`Any`/`some` are deliberately *not* treated as boundaries
//! so a return type such as `-> Self` is not torn off the signature.
//!
//! Anything unrecognized still lands in the tree as its exact tokens (an
//! `ErrorItem` node plus a `Diagnostic`), so the result always round-trips
//! byte-for-byte. The recursion is depth-guarded at [`MAX_DEPTH`] against hostile
//! nesting — a `catch_unwind` cannot catch a stack overflow.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::swift::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const FUNCTION: &str = "Function";
    pub const INIT: &str = "Init";
    pub const DEINIT: &str = "Deinit";
    pub const SUBSCRIPT: &str = "Subscript";
    pub const CLASS: &str = "Class";
    pub const STRUCT: &str = "Struct";
    pub const ENUM: &str = "Enum";
    pub const PROTOCOL: &str = "Protocol";
    pub const ACTOR: &str = "Actor";
    pub const EXTENSION: &str = "Extension";
    pub const TYPEALIAS: &str = "TypeAlias";
    pub const IMPORT: &str = "Import";
    pub const PROPERTY: &str = "Property";
    pub const ENUM_CASE: &str = "EnumCase";
    pub const OPERATOR_DECL: &str = "OperatorDecl";
    pub const ERROR_ITEM: &str = "ErrorItem";

    pub const NAME: &str = "Name";
    pub const HEADER: &str = "Header";
    pub const SIGNATURE: &str = "Signature";
    pub const ITEM_BLOCK: &str = "ItemBlock";
    pub const BLOCK: &str = "Block";
    pub const ATTR: &str = "Attr";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat balanced run. Protects against stack overflow on
/// pathological or hostile inputs — mirrors the Rust/Python parsers exactly,
/// since a `catch_unwind` cannot catch a stack overflow.
const MAX_DEPTH: usize = 256;

/// Keywords (and modifiers) that begin a member declaration. A header/signature
/// region ends when one of these appears at delimiter depth 0, because Swift has
/// no statement terminator. Deliberately excludes type/expression keywords
/// (`Self`, `Any`, `some`, `any`, `where`, `throws`, …) that legitimately occur
/// inside a signature.
const MEMBER_START_KW: &[&str] = &[
    "func",
    "init",
    "deinit",
    "subscript",
    "var",
    "let",
    "class",
    "struct",
    "enum",
    "protocol",
    "extension",
    "actor",
    "typealias",
    "associatedtype",
    "case",
    "import",
    "operator",
    "precedencegroup",
    "macro",
    "public",
    "private",
    "fileprivate",
    "internal",
    "open",
    "static",
    "final",
    "override",
    "required",
    "convenience",
    "lazy",
    "weak",
    "unowned",
    "mutating",
    "nonmutating",
    "dynamic",
    "optional",
    "indirect",
    "infix",
    "prefix",
    "postfix",
    "nonisolated",
    "distributed",
];

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = SwiftParser {
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

struct SwiftParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> SwiftParser<'s> {
    // --- cursor primitives --------------------------------------------------

    /// Append the current token (trivia or not) to `out` and advance.
    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading trivia tokens into `out`.
    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
        }
    }

    /// Kind of the next significant (non-trivia) token.
    fn peek_kind(&self) -> Option<&'static str> {
        let mut j = self.i;
        while j < self.toks.len() && self.toks[j].trivia {
            j += 1;
        }
        self.toks.get(j).map(|t| t.kind)
    }

    /// Text of the n-th significant token from the cursor.
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
        self.peek_n_text(0) == Some(s)
    }

    fn at_ident(&self) -> bool {
        self.peek_kind() == Some(tk::IDENT)
    }

    fn next_is_ident(&self) -> bool {
        self.peek_kind_n(1) == Some(tk::IDENT)
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

    fn at_open(&self) -> bool {
        self.at("(") || self.at("[") || self.at("{")
    }

    /// True at the start of a member declaration (a declaration keyword, a
    /// modifier, or an `@attribute`). Used to bound terminator-less regions.
    fn at_member_start(&self) -> bool {
        if self.at("@") {
            return true;
        }
        matches!(self.peek_text(), Some(t) if MEMBER_START_KW.contains(&t))
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
            self.ws(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            let item = self.parse_item();
            c.push(Child::Node(item));
        }
        self.make_node(node::SOURCE_FILE, c)
    }

    /// Parse `{ members }` as a recursive declaration list (type/extension body).
    fn parse_item_block(&mut self) -> Node {
        // Depth guard: beyond the cap, stop recursing and consume the body as a
        // flat balanced run. Lossless, never a stack overflow.
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
            self.ws(&mut c);
            match self.peek_kind() {
                None => break,
                Some(_) if self.at("}") => {
                    self.eat(&mut c);
                    break;
                }
                Some(_) => {
                    let item = self.parse_item();
                    c.push(Child::Node(item));
                }
            }
        }
        let node = self.make_node(node::ITEM_BLOCK, c);
        self.depth -= 1;
        node
    }

    // --- items / members ----------------------------------------------------

    fn parse_item(&mut self) -> Node {
        let mut c = Vec::new();

        // Attributes: `@available(...)`, `@objc`, property wrappers, …
        loop {
            self.ws(&mut c);
            if self.at("@") {
                let attr = self.parse_attr();
                c.push(Child::Node(attr));
            } else {
                break;
            }
        }

        // Leading modifiers before the declaration keyword. `class`/`static` can
        // be method/property modifiers (`class func`, `static let`); only treat
        // `class` as a modifier when a member keyword follows it.
        loop {
            self.ws(&mut c);
            match self.peek_text() {
                Some(
                    "public" | "private" | "fileprivate" | "internal" | "open" | "static" | "final"
                    | "override" | "required" | "convenience" | "lazy" | "weak" | "unowned"
                    | "mutating" | "nonmutating" | "dynamic" | "optional" | "indirect" | "infix"
                    | "prefix" | "postfix" | "nonisolated" | "distributed" | "isolated",
                ) => self.eat(&mut c),
                Some("class")
                    if matches!(
                        self.peek_n_text(1),
                        Some("func" | "var" | "let" | "subscript" | "static")
                    ) =>
                {
                    self.eat(&mut c) // `class` as a member modifier
                }
                _ => break,
            }
            // `private(set)` and friends: an access modifier may carry a `(set)`.
            self.ws(&mut c);
            if self.at("(") {
                let g = self.parse_delimited(None);
                c.push(Child::Node(g));
            }
        }

        // Dispatch on the declaration keyword.
        self.ws(&mut c);
        match self.peek_text() {
            Some("func") => self.finish_func(c),
            Some("init") => self.finish_init(c),
            Some("deinit") => self.finish_deinit(c),
            Some("subscript") => self.finish_subscript(c),
            Some("class") => self.finish_type(c, node::CLASS),
            Some("struct") => self.finish_type(c, node::STRUCT),
            Some("enum") => self.finish_type(c, node::ENUM),
            Some("protocol") => self.finish_type(c, node::PROTOCOL),
            Some("actor") if self.next_is_ident() => self.finish_type(c, node::ACTOR),
            Some("extension") => self.finish_extension(c),
            Some("typealias") | Some("associatedtype") => self.finish_typealias(c),
            Some("import") => self.finish_import(c),
            Some("let") | Some("var") => self.finish_property(c),
            Some("case") => self.finish_case(c),
            Some("operator") | Some("precedencegroup") => self.finish_operator(c),
            _ => self.finish_error_item(c),
        }
    }

    /// `@name` or `@name(args)`.
    fn parse_attr(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // @
        self.ws(&mut c);
        if self.at_ident() {
            self.eat(&mut c); // attribute name
        }
        self.ws(&mut c);
        if self.at("(") {
            let g = self.parse_delimited(None);
            c.push(Child::Node(g));
        }
        self.make_node(node::ATTR, c)
    }

    fn finish_func(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // func
        self.ws(&mut c);
        // Name: a plain or backtick identifier, or an operator symbol for an
        // operator method (`func + (...)`).
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        } else if !self.at("(") && !self.at("<") && self.peek_kind().is_some() {
            let n = self.name_node(); // operator name token
            c.push(Child::Node(n));
        }
        if let Some(sig) = self.collect_signature(node::SIGNATURE) {
            c.push(Child::Node(sig));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
        }
        self.make_node(node::FUNCTION, c)
    }

    fn finish_init(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        let n = self.name_node(); // init
        c.push(Child::Node(n));
        self.ws(&mut c);
        // Failable initializers: `init?` / `init!`.
        if self.at("?") || self.at("!") {
            self.eat(&mut c);
        }
        if let Some(sig) = self.collect_signature(node::SIGNATURE) {
            c.push(Child::Node(sig));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
        }
        self.make_node(node::INIT, c)
    }

    fn finish_deinit(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        let n = self.name_node(); // deinit
        c.push(Child::Node(n));
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
        }
        self.make_node(node::DEINIT, c)
    }

    fn finish_subscript(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        let n = self.name_node(); // subscript
        c.push(Child::Node(n));
        if let Some(sig) = self.collect_signature(node::SIGNATURE) {
            c.push(Child::Node(sig));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
        }
        self.make_node(node::SUBSCRIPT, c)
    }

    /// `class`/`struct`/`enum`/`protocol`/`actor` NAME <generics> : inherits { … }.
    fn finish_type(&mut self, mut c: Vec<Child>, kind: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // the type keyword
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        // Generic params, inheritance clause, `where` clause — up to the body `{`.
        if let Some(h) = self.collect_header(node::HEADER) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_item_block();
            c.push(Child::Node(b));
        }
        self.make_node(kind, c)
    }

    /// `extension Type : protocols where … { … }`. The extended type's name lives
    /// in the header; lowering resolves it.
    fn finish_extension(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // extension
        if let Some(h) = self.collect_header(node::HEADER) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_item_block();
            c.push(Child::Node(b));
        }
        self.make_node(node::EXTENSION, c)
    }

    /// `typealias Name = Type` / `associatedtype Name: Constraint = Default`.
    fn finish_typealias(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // typealias / associatedtype
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        if let Some(h) = self.collect_header(node::HEADER) {
            c.push(Child::Node(h));
        }
        self.make_node(node::TYPEALIAS, c)
    }

    fn finish_import(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // import
        self.ws(&mut c);
        // A submodule import names a kind first: `import func Module.symbol`,
        // `import struct A.B`. Eat that kind keyword so it is not mistaken for the
        // start of the next declaration.
        if matches!(
            self.peek_text(),
            Some("struct" | "class" | "enum" | "protocol" | "typealias" | "func" | "var" | "let",)
        ) && self.next_is_ident()
        {
            self.eat(&mut c);
        }
        // `import Foundation`, the dotted path of a submodule import, etc.
        if let Some(h) = self.collect_header(node::HEADER) {
            c.push(Child::Node(h));
        }
        self.make_node(node::IMPORT, c)
    }

    /// `let`/`var` binding: a stored, computed, or observed property/constant.
    fn finish_property(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // let / var
        self.ws(&mut c);
        // Binding name (or a tuple pattern, captured as a Paren group).
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        } else if self.at("(") {
            let g = self.parse_delimited(None);
            c.push(Child::Node(g));
        }
        // Type annotation and/or initializer, up to a computed-property `{` or the
        // next member.
        if let Some(h) = self.collect_header(node::HEADER) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
        }
        self.make_node(node::PROPERTY, c)
    }

    /// `case North, South(Int)` (an enum case) or `case .x` patterns reached at
    /// member level. Captured up to the next member.
    fn finish_case(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // case
        self.collect_until_member_boundary(&mut c);
        self.make_node(node::ENUM_CASE, c)
    }

    /// `infix operator +++ : Precedence` / `precedencegroup Name { … }`.
    fn finish_operator(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // operator / precedencegroup
        if let Some(h) = self.collect_header(node::HEADER) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
        }
        self.make_node(node::OPERATOR_DECL, c)
    }

    fn finish_error_item(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        let start = self.cur_offset();
        if self.at_open() {
            let g = self.parse_delimited(None);
            c.push(Child::Node(g));
        } else {
            // Consume at least one token to guarantee progress, then any run up to
            // the next member boundary so statements stay together.
            self.eat(&mut c);
            self.collect_until_member_boundary(&mut c);
        }
        self.diags.push(Diagnostic {
            code: "swift.unrecognized_item",
            message: "token(s) not recognized as a Swift declaration".to_string(),
            span: children_span(&c).unwrap_or_else(|| ByteSpan::empty_at(start)),
        });
        self.make_node(node::ERROR_ITEM, c)
    }

    // --- shared helpers -----------------------------------------------------

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.eat(&mut c); // the identifier/keyword/operator token
        self.make_node(node::NAME, c)
    }

    /// Collect a header region: tokens (descending into balanced groups) up to the
    /// body `{`, the enclosing `}`, the next member declaration, or EOF. Used for
    /// type inheritance clauses, property annotations/initializers, imports, etc.
    fn collect_header(&mut self, label: &'static str) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            if self.peek_kind().is_none() {
                break;
            }
            if self.at("{") || self.at("}") || self.at_member_start() {
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

    /// Collect a function/subscript signature: identical bounds to
    /// [`SwiftParser::collect_signature`]'s caller needs — generics, the parameter
    /// list, the return clause, and a `where` clause — stopping at the body `{`,
    /// the enclosing `}`, the next member, or EOF.
    fn collect_signature(&mut self, label: &'static str) -> Option<Node> {
        self.collect_header(label)
    }

    /// Append tokens (descending into balanced groups) up to the next member
    /// boundary, the enclosing `}`, or EOF. Used to keep enum cases and stray
    /// statements intact without consuming the following declaration.
    fn collect_until_member_boundary(&mut self, out: &mut Vec<Child>) {
        loop {
            if self.peek_kind().is_none() {
                break;
            }
            if self.at("}") || self.at_member_start() {
                break;
            }
            if self.at_open() {
                self.ws(out);
                let inner = self.parse_delimited(None);
                out.push(Child::Node(inner));
            } else {
                self.ws(out);
                self.eat(out);
            }
        }
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`. The cursor is
    /// at (or before trivia preceding) the opener.
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

    /// Iteratively consume a balanced delimiter run (opener already eaten),
    /// appending every token as a flat leaf. Used at the depth cap so arbitrarily
    /// deep nesting is handled without further recursion.
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

    /// Record (once per truncation is enough) that the depth cap flattened
    /// structure — reported, never silent.
    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "swift.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; group flattened"),
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
// a file
import Foundation

let version = \"1.0\"

@objc
public class Point: NSObject, Codable {
    var x: Int
    var y: Int

    init(x: Int, y: Int) {
        self.x = x
        self.y = y
    }

    func norm() -> Double {
        return sqrt(self.x * self.x + self.y * self.y)
    }
}

protocol Shape {
    func area() -> Double
}

struct Circle: Shape {
    let r: Double
    func area() -> Double { 3.14 * r * r }
}

enum Direction {
    case north, south
    case east
    func opposite() -> Direction { self }
}

extension Circle {
    func describe() -> String { \"circle\" }
}

func add(a: Int, b: Int) -> Int { a + b }
";
        let tree = parse("mod.swift", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_items() {
        let src = "import UIKit\nclass C {}\nstruct S {}\nenum E { case a }\nprotocol P {}\nfunc f() {}\n";
        let tree = parse("t.swift", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::IMPORT), "import: {kinds:?}");
        assert!(kinds.contains(&node::CLASS), "class: {kinds:?}");
        assert!(kinds.contains(&node::STRUCT), "struct: {kinds:?}");
        assert!(kinds.contains(&node::ENUM), "enum: {kinds:?}");
        assert!(kinds.contains(&node::PROTOCOL), "protocol: {kinds:?}");
        assert!(kinds.contains(&node::FUNCTION), "func: {kinds:?}");
    }

    #[test]
    fn methods_nest_inside_type_bodies() {
        let src = "class C {\n    func a() {}\n    func b() {}\n}\n";
        let tree = parse("t.swift", src);
        let class = tree.root.children_of(node::CLASS).next().expect("a class");
        let block = class.child(node::ITEM_BLOCK).expect("class body");
        let methods: Vec<&str> = block
            .children_of(node::FUNCTION)
            .filter_map(|f| f.child(node::NAME))
            .filter_map(|n| n.tokens().next())
            .map(|t| t.span.text(src))
            .collect();
        assert_eq!(methods, vec!["a", "b"]);
    }

    #[test]
    fn protocol_method_without_body_does_not_swallow_next_member() {
        let src = "protocol P {\n    func a() -> Int\n    func b()\n}\n";
        let tree = parse("t.swift", src);
        let proto = tree
            .root
            .children_of(node::PROTOCOL)
            .next()
            .expect("a protocol");
        let block = proto.child(node::ITEM_BLOCK).expect("protocol body");
        let count = block.children_of(node::FUNCTION).count();
        assert_eq!(count, 2, "both requirements are distinct functions");
    }

    #[test]
    fn enum_cases_are_captured() {
        let src = "enum E {\n    case a\n    case b(Int)\n    func f() {}\n}\n";
        let tree = parse("t.swift", src);
        let e = tree.root.children_of(node::ENUM).next().expect("an enum");
        let block = e.child(node::ITEM_BLOCK).expect("enum body");
        assert_eq!(block.children_of(node::ENUM_CASE).count(), 2);
        assert_eq!(block.children_of(node::FUNCTION).count(), 1);
        assert!(tree.is_lossless());
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        // Far deeper than MAX_DEPTH; must not stack-overflow and must round-trip.
        let depth = 10_000;
        let src = format!("func x() {{ {}{} }}", "(".repeat(depth), ")".repeat(depth));
        let tree = parse("deep.swift", &src);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics
                .iter()
                .any(|d| d.code == "swift.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "func f(a: Int",          // unterminated paren
            "let λ = \"☃\" // uni\n", // multi-byte identifiers/strings
            "",                       // empty file
            "\n\n   \n// trailing\n", // only trivia
            "let s = \"oops\n",       // unterminated string
        ] {
            let tree = parse("edge.swift", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
