//! Solidity parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Rust and Java parsers ([`crate::lang::java::parser`]):
//! declaration *headers* are parsed precisely — we always know a contract's name
//! and its `is` bases, a function's name/params/`returns`, an `import` path, a
//! state variable's name — while function bodies and expression regions are
//! captured as balanced **token-tree groups** (`Paren`/`Bracket`/`Brace`) plus
//! flat tokens, which is perfectly lossless. Graph facts (calls, type refs) are
//! extracted from these real token trees in the lowering pass, never invented.
//!
//! Unlike Java members (distinguished only by a trailing `(`), most Solidity
//! members are keyword-led (`function`/`constructor`/`modifier`/`event`/`error`/
//! `struct`/`enum`/`using`), so the parser dispatches on the leading keyword and
//! treats anything else as a state-variable declaration.
//!
//! Anything unrecognized still lands in the tree as its exact tokens, so the
//! result always round-trips byte-for-byte. The recursion is depth-guarded at
//! [`MAX_DEPTH`] against hostile nesting (both nested contracts and nested
//! delimiters), because a `catch_unwind` cannot catch a stack overflow. The two
//! item loops also carry an explicit progress guard so a non-advancing dispatch
//! can never spin.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::solidity::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const SOURCE_UNIT: &str = "SourceUnit";
    pub const PRAGMA: &str = "Pragma";
    pub const IMPORT: &str = "Import";
    pub const USING: &str = "Using";
    pub const CONTRACT: &str = "Contract";
    pub const INTERFACE: &str = "Interface";
    pub const LIBRARY: &str = "Library";
    pub const STRUCT: &str = "Struct";
    pub const ENUM: &str = "Enum";
    pub const EVENT: &str = "Event";
    pub const ERROR_DEF: &str = "ErrorDef";
    pub const FUNCTION: &str = "Function";
    pub const STATE_VAR: &str = "StateVar";
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

/// Leading declaration modifiers recognized before a contract-like keyword.
const MODIFIER_KEYWORDS: &[&str] = &["abstract"];

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat balanced run. Protects against stack overflow on
/// pathological or hostile inputs — mirrors the Rust/Java guards exactly
/// ([`crate::lang::rust::parser`] uses the same 256), since a `catch_unwind`
/// cannot catch a stack overflow.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = SolidityParser {
        src: source,
        toks,
        i: 0,
        diags: Vec::new(),
        depth: 0,
    };
    let root = p.parse_source_unit();
    ParseTree {
        source_id: SourceId::from_path(path),
        path: path.to_string(),
        source: source.to_string(),
        root,
        diagnostics: p.diags,
    }
}

struct SolidityParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> SolidityParser<'s> {
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

    fn at(&self, s: &str) -> bool {
        self.peek_n_text(0) == Some(s)
    }

    fn at_ident(&self) -> bool {
        self.peek_kind() == Some(tk::IDENT)
    }

    fn at_open(&self) -> bool {
        self.at("(") || self.at("[") || self.at("{")
    }

    fn next_is_ident(&self) -> bool {
        self.peek_kind_n(1) == Some(tk::IDENT)
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

    fn parse_source_unit(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            let before = self.i;
            let item = self.parse_item();
            // Progress guard: a dispatch that consumed nothing would spin forever;
            // force one token forward as an ErrorItem instead. Always lossless.
            if self.i == before {
                let mut e = Vec::new();
                self.eat(&mut e);
                c.push(Child::Node(self.make_node(node::ERROR_ITEM, e)));
            } else {
                c.push(Child::Node(item));
            }
        }
        self.make_node(node::SOURCE_UNIT, c)
    }

    /// Dispatch one top-level or contract-body item on its leading keyword.
    fn parse_item(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        if self.at("pragma") {
            return self.finish_directive(c, node::PRAGMA);
        }
        if self.at("import") {
            return self.finish_directive(c, node::IMPORT);
        }
        if self.at("using") {
            return self.finish_directive(c, node::USING);
        }
        // Leading modifiers (`abstract`) before a contract-like keyword.
        self.parse_modifiers(&mut c);
        self.ws(&mut c);
        if self.at("contract") || self.at("interface") || self.at("library") {
            return self.finish_contract(c);
        }
        if self.at("struct") {
            return self.finish_braced_type(c, node::STRUCT);
        }
        if self.at("enum") {
            return self.finish_braced_type(c, node::ENUM);
        }
        if self.at("event") {
            return self.finish_signature_decl(c, node::EVENT);
        }
        if self.at("error") && self.next_is_ident() {
            return self.finish_signature_decl(c, node::ERROR_DEF);
        }
        if self.at("function")
            || self.at("constructor")
            || self.at("modifier")
            || self.at("receive")
            || self.at("fallback")
        {
            return self.finish_function(c);
        }
        // Anything else: a state variable / constant declaration.
        self.finish_state_var(c)
    }

    /// A `;`-terminated directive: `pragma …;`, `import …;`, `using …;`. The whole
    /// payload is captured as a `Header` region so the lowering can read the path
    /// (import) or the rest verbatim.
    fn finish_directive(&mut self, mut c: Vec<Child>, label: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // pragma / import / using
        if let Some(h) = self.collect_region(node::HEADER, &[";"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(label, c)
    }

    /// `[abstract] contract|interface|library Name [is Base1, Base2(args)] { body }`.
    fn finish_contract(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        let kind = if self.at("contract") {
            node::CONTRACT
        } else if self.at("interface") {
            node::INTERFACE
        } else {
            node::LIBRARY
        };
        self.eat(&mut c); // contract / interface / library
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        // `is Base, Base(args)` — captured as a Header up to the body.
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

    /// `struct Name { … }` / `enum Name { A, B }` — body kept as a balanced brace
    /// group (members are not individually broken out).
    fn finish_braced_type(&mut self, mut c: Vec<Child>, label: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // struct / enum
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
        } else if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(label, c)
    }

    /// `event Name(params) [anonymous];` / `error Name(params);`.
    fn finish_signature_decl(&mut self, mut c: Vec<Child>, label: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // event / error
        self.ws(&mut c);
        if self.at_ident() {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        self.ws(&mut c);
        if self.at("(") {
            let params = self.parse_delimited(Some(node::PARAMS));
            c.push(Child::Node(params));
        }
        if let Some(h) = self.collect_region(node::HEADER, &[";"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(label, c)
    }

    /// `function Name(params) <mods> [returns (types)] { body }|;`, plus
    /// `constructor(params) <mods> { body }`, `modifier Name(params) <mods> { body }`,
    /// and `receive()/fallback() <mods> { body }`. The leading keyword is retained
    /// in `c` so the lowering can classify the function kind.
    fn finish_function(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // function / constructor / modifier / receive / fallback
        self.ws(&mut c);
        // Optional name: a `function`/`modifier` has one; `constructor`/`receive`/
        // `fallback` go straight to their parameter list.
        if self.at_ident() && !self.at("(") {
            let n = self.name_node();
            c.push(Child::Node(n));
        }
        self.ws(&mut c);
        if self.at("(") {
            let params = self.parse_delimited(Some(node::PARAMS));
            c.push(Child::Node(params));
        }
        // Visibility/mutability modifiers, `returns (...)`, modifier-invocations —
        // captured up to the body or terminating `;`.
        if let Some(h) = self.collect_region(node::HEADER, &["{", ";"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at("{") {
            let b = self.parse_delimited(Some(node::BLOCK));
            c.push(Child::Node(b));
        } else if self.at(";") {
            self.eat(&mut c); // interface / abstract function, no body
        }
        self.make_node(node::FUNCTION, c)
    }

    /// A state variable / constant declaration: `<type> [visibility] [constant|
    /// immutable] name [= expr];`.
    fn finish_state_var(&mut self, mut c: Vec<Child>) -> Node {
        if let Some(sig) = self.collect_region(node::SIGNATURE, &["=", ";", "{", "}"]) {
            c.push(Child::Node(sig));
        }
        self.ws(&mut c);
        if self.at("=") {
            if let Some(init) = self.collect_region(node::FIELD_INIT, &[";", "}"]) {
                c.push(Child::Node(init));
            } else {
                // `=` with nothing after it before the stop: still eat it.
                self.eat(&mut c);
            }
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::STATE_VAR, c)
    }

    /// `{ members }` parsed as a recursive member list (contract / interface /
    /// library body).
    fn parse_item_block(&mut self, label: &'static str) -> Node {
        // Depth guard: beyond the cap, stop recursing into members and consume the
        // body as a flat balanced run. Lossless, never a stack overflow.
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
                    let before = self.i;
                    let member = self.parse_item();
                    if self.i == before {
                        // Progress guard inside the body loop.
                        let mut e = Vec::new();
                        self.eat(&mut e);
                        c.push(Child::Node(self.make_node(node::ERROR_ITEM, e)));
                    } else {
                        c.push(Child::Node(member));
                    }
                }
            }
        }
        let node = self.make_node(label, c);
        self.depth -= 1;
        node
    }

    /// Collect leading modifier keywords (`abstract`) into `c`.
    fn parse_modifiers(&mut self, c: &mut Vec<Child>) {
        loop {
            self.ws(c);
            if self.at_modifier() {
                self.eat(c);
            } else {
                break;
            }
        }
    }

    fn at_modifier(&self) -> bool {
        self.peek_n_text(0)
            .map(|t| MODIFIER_KEYWORDS.contains(&t))
            .unwrap_or(false)
    }

    // --- shared helpers -----------------------------------------------------

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.eat(&mut c); // the identifier (cursor is at it after caller ws)
        self.make_node(node::NAME, c)
    }

    /// Collect tokens (descending into balanced groups) until a significant stop
    /// token at delimiter depth 0, or end of input. Returns `None` if nothing was
    /// collected.
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

    /// Record (once per truncation) that the depth cap flattened structure —
    /// reported, never silent.
    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "solidity.depth_limit",
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
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import \"./Ownable.sol\";
import {IERC20} from \"@openzeppelin/contracts/token/IERC20.sol\";

/** @title A token. */
interface IThing {
    function ping() external view returns (uint256);
}

abstract contract Base {
    uint256 internal value;
    constructor(uint256 v) { value = v; }
}

contract Token is Base, IThing {
    mapping(address => uint256) public balances;
    uint256 public constant CAP = 1_000_000;
    address immutable owner;

    event Transfer(address indexed from, address indexed to, uint256 amount);
    error InsufficientBalance(uint256 have, uint256 need);

    struct Account { uint256 bal; bool frozen; }
    enum State { Open, Closed }

    modifier onlyOwner() { require(msg.sender == owner); _; }

    constructor() Base(0) { }

    function ping() external view override returns (uint256) { return value; }

    function transfer(address to, uint256 amount) public onlyOwner {
        balances[msg.sender] -= amount;
        balances[to] += amount;
        emit Transfer(msg.sender, to, amount);
    }

    receive() external payable {}
    fallback() external {}
}
";
        let tree = parse("Token.sol", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_decls() {
        let src = "contract A {} interface B {} library C {} struct D { uint x; } enum E { X }";
        let tree = parse("T.sol", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::CONTRACT), "contract: {kinds:?}");
        assert!(kinds.contains(&node::INTERFACE), "interface: {kinds:?}");
        assert!(kinds.contains(&node::LIBRARY), "library: {kinds:?}");
        assert!(kinds.contains(&node::STRUCT), "struct: {kinds:?}");
        assert!(kinds.contains(&node::ENUM), "enum: {kinds:?}");
    }

    #[test]
    fn members_nest_in_contract() {
        let src = "contract C {\n  uint256 x = 1;\n  function m() public {}\n  constructor() {}\n}";
        let tree = parse("C.sol", src);
        let c = tree
            .root
            .children_of(node::CONTRACT)
            .next()
            .expect("a contract");
        let block = c.child(node::ITEM_BLOCK).expect("contract body");
        assert_eq!(
            block.children_of(node::FUNCTION).count(),
            2,
            "m() and the constructor are Functions"
        );
        assert_eq!(
            block.children_of(node::STATE_VAR).count(),
            1,
            "one state var"
        );
    }

    #[test]
    fn event_and_error_are_recognized() {
        let src = "contract C { event E(uint x); error Bad(uint y); }";
        let tree = parse("C.sol", src);
        let kinds: Vec<&str> = tree.root.walk().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::EVENT), "event: {kinds:?}");
        assert!(kinds.contains(&node::ERROR_DEF), "error: {kinds:?}");
    }

    #[test]
    fn receive_and_fallback_are_functions() {
        let src = "contract C { receive() external payable {} fallback() external {} }";
        let tree = parse("C.sol", src);
        let fns = tree
            .root
            .walk()
            .filter(|n| n.kind == node::FUNCTION)
            .count();
        assert_eq!(fns, 2, "receive + fallback");
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        // Far deeper than MAX_DEPTH on both axes; must not stack-overflow and must
        // stay lossless.
        let deep_braces = format!(
            "contract C {{ function m() public {{ {}{} }} }}",
            "{".repeat(10_000),
            "}".repeat(10_000)
        );
        let mut deep_types = String::new();
        for _ in 0..2_000 {
            deep_types.push_str("contract C { ");
        }
        deep_types.push_str(&"}".repeat(2_000));
        for src in [deep_braces, deep_types] {
            let tree = parse("deep.sol", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics
                    .iter()
                    .any(|d| d.code == "solidity.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "contract C { function m() public { foo(1, 2 }", // unterminated paren
            "contract λ { string s = \"☃\"; }",              // multi-byte
            "",                                              // empty file
            "// only a comment\n",                           // no code
            "contract C { ; ; }",                            // stray semicolons
            "pragma solidity >=0.7.0 <0.9.0;",               // version range
        ] {
            let tree = parse("edge.sol", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
