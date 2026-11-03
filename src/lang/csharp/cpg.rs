//! The deterministic Code Property Graph overlay for C# (ADR-0003).
//!
//! Mirrors the Rust overlay ([`crate::ir::cpg`]) — same ontology (`Statement`
//! nodes, `FLOWS_TO`, may-reach `DATA_DEP`), same statement-id scheme
//! (`stmt::{qual}#{line}::{n}` + one virtual `::exit`), same conservative
//! principles — adapted to C#'s statement grammar over the lossless token tree:
//!
//! - `if`/`else` (embedded or block bodies), `while`, `do … while`, `for`,
//!   `foreach`, `switch` sections, `break`/`continue`, `return`, `throw`,
//!   `try`/`catch`/`finally`, `using`/`lock` statements, bare-block splicing.
//! - **`break` binds to the nearest enclosing loop OR switch** (C# semantics);
//!   `continue` binds to the nearest enclosing loop only.
//! - **`throw` is modeled as function exit** (role `throw`), like an early
//!   return. A `throw` that a *local* `catch` in the same function would
//!   intercept is still edged to the exit — the may-transfer `branch/catch`
//!   edge from the enclosing `try` covers the local-catch path at section
//!   grain. Documented in the ADR; defended there.
//! - **`catch` is a may-transfer branch target of the `try` statement**, not a
//!   successor of every throwing statement: edging every try-body statement to
//!   every catch would fabricate O(n·m) claims the token tree cannot support.
//! - `goto` (label / `case`) diverges with no modeled edge — the target is not
//!   claimed. Absence over fabrication.
//!
//! Everything is deterministic and std-only: ids come from a fixed pre-order
//! walk, and all output goes through the de-duplicating `BTreeMap` [`Graph`].

use crate::core::cst::{Child, Node, Token};
use crate::core::json::Json;
use crate::core::span::{ByteSpan, LineIndex};
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::csharp::lexer::{is_keyword, kind as tk};
use crate::lang::csharp::parser::node as cst;

/// Maximum characters of collapsed source text used as a statement node name.
const NAME_LIMIT: usize = 48;

/// C# predefined-type keywords (plus `var`): the tokens that can open a local
/// declaration and count as "type-ish" before a declared name.
const PREDEFINED_TYPES: &[&str] = &[
    "bool", "byte", "char", "decimal", "double", "float", "int", "long", "object", "sbyte",
    "short", "string", "uint", "ulong", "ushort", "var",
];

/// Compound assignment operators (they read the old value AND redefine).
const COMPOUND_ASSIGN: &[&str] = &[
    "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=", "??=",
];

/// Emit the CPG overlay for one C# method body into `g`.
///
/// `fn_id` is the method's base-graph id (`fn::{qual}#{line}`); statement ids
/// derive from it, so the overlay attaches to the exact node the base graph
/// declared. `header` is the method's `Header` CST node (for parameter names).
pub fn emit_method_cpg(g: &mut Graph, fn_id: &str, block: &Node, header: Option<&Node>, src: &str) {
    let stem = fn_id.strip_prefix("fn::").unwrap_or(fn_id);
    let prefix = format!("stmt::{stem}");
    let li = LineIndex::new(src);

    let els = inner_elems(block, src);
    let mut stmts = segment(&els, src);

    let exit_id = format!("{prefix}::exit");
    let mut em = Emitter {
        g,
        src,
        li: &li,
        fn_id,
        prefix: &prefix,
        exit_id: &exit_id,
        next: 0,
    };
    em.g.upsert_node(
        exit_id.clone(),
        ont::STATEMENT,
        "<exit>",
        vec![("virtual", Json::Bool(true)), ("role", Json::str("exit"))],
    );
    em.g.add_edge(fn_id, edge::CONTAINS, exit_id.clone(), vec![]);

    let entry = vec![Exit {
        from: fn_id.to_string(),
        role: "entry",
        branch: None,
    }];
    let mut loops: Vec<LoopCtx> = Vec::new();
    let mut breaks: Vec<BreakCtx> = Vec::new();
    let final_exits = em.emit_block(&mut stmts, entry, &mut loops, &mut breaks);
    let exit = exit_id.clone();
    em.join(final_exits, &exit);

    // Data flow: def-use chains over the same statement tree.
    let mut env = Env::new();
    if let Some(h) = header {
        for name in param_names(h, src) {
            env.insert(name, vec![(fn_id.to_string(), "param")]);
        }
    }
    let mut df = DataFlow { g: em.g, src };
    df.data_block(&stmts, &mut env, &[]);
}

// ---------------------------------------------------------------------------
// Element view (identical shape to the Rust overlay's).
// ---------------------------------------------------------------------------

/// One significant element of a token-tree level: a token or a balanced group.
enum E<'a> {
    T(&'a Token),
    G(&'a Node),
}

impl<'a> E<'a> {
    fn span(&self) -> ByteSpan {
        match self {
            E::T(t) => t.span,
            E::G(n) => n.span,
        }
    }

    fn text(&self, src: &'a str) -> Option<&'a str> {
        match self {
            E::T(t) => Some(t.span.text(src)),
            E::G(_) => None,
        }
    }

    fn is_brace(&self) -> bool {
        matches!(self, E::G(n) if n.kind == cst::BRACE || n.kind == cst::BLOCK)
    }

    fn is_paren(&self) -> bool {
        matches!(self, E::G(n) if n.kind == cst::PAREN)
    }

    fn ident_text(&self, src: &'a str) -> Option<&'a str> {
        match self {
            E::T(t) if t.kind == tk::IDENT && !is_keyword(t.span.text(src)) => {
                Some(t.span.text(src))
            }
            _ => None,
        }
    }
}

fn reborrow<'a>(e: &E<'a>) -> E<'a> {
    match e {
        E::T(t) => E::T(t),
        E::G(n) => E::G(n),
    }
}

/// Non-trivia elements of `node`.
fn elems<'a>(node: &'a Node) -> Vec<E<'a>> {
    let mut v = Vec::new();
    for c in &node.children {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => v.push(E::T(t)),
            Child::Node(n) => v.push(E::G(n)),
        }
    }
    v
}

/// Elements of a brace group (or flat expression-body region) without its
/// `{` / `}` delimiter tokens. An expression-bodied member's `Block` node has
/// no braces — its elements pass through unchanged and segment as one flat
/// statement, which is exactly what `=> expr` is.
fn inner_elems<'a>(group: &'a Node, src: &str) -> Vec<E<'a>> {
    let mut v = elems(group);
    if v.first().and_then(|e| e.text(src)) == Some("{") {
        v.remove(0);
    }
    if v.last().and_then(|e| e.text(src)) == Some("}") {
        v.pop();
    }
    v
}

// ---------------------------------------------------------------------------
// Statement segmentation
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum K {
    Expr,
    Local,
    Return,
    Throw,
    Break,
    Continue,
    Goto,
    YieldBreak,
    Item,
    If,
    While,
    DoWhile,
    For,
    Foreach,
    Switch,
    Try,
    Using,
    Lock,
}

impl K {
    fn label(self) -> &'static str {
        match self {
            K::Expr => "expr",
            K::Local => "local",
            K::Return => "return",
            K::Throw => "throw",
            K::Break => "break",
            K::Continue => "continue",
            K::Goto => "goto",
            K::YieldBreak => "yield-break",
            K::Item => "item",
            K::If => "if",
            K::While => "while",
            K::DoWhile => "do",
            K::For => "for",
            K::Foreach => "foreach",
            K::Switch => "switch",
            K::Try => "try",
            K::Using => "using",
            K::Lock => "lock",
        }
    }
}

/// One segmented statement. `header` holds the flat element run for flat
/// kinds, and the `(…)` header region for structured kinds.
struct Stmt<'a> {
    kind: K,
    span: ByteSpan,
    header: Vec<E<'a>>,
    /// `if`: then. `while`/`do`/`for`/`foreach`/`using`/`lock`: body.
    /// `try`: the try block.
    body: Option<Vec<Stmt<'a>>>,
    /// `if` only: the else continuation (an `else if` is one nested If).
    else_part: Option<Vec<Stmt<'a>>>,
    /// `switch`: case sections. `try`: catch clauses.
    arms: Vec<Arm<'a>>,
    /// `try` only: the finally block.
    finally_part: Option<Vec<Stmt<'a>>>,
    /// Assigned during emission (pre-order); consumed by the data-flow pass.
    id: Option<String>,
}

/// A `switch` section (its stacked `case …:`/`default:` labels + statements)
/// or a `catch` clause (its `(Type name)` header + block).
struct Arm<'a> {
    span: ByteSpan,
    /// Section labels / catch declaration (+ `when` filter) elements.
    header: Vec<E<'a>>,
    body: Vec<Stmt<'a>>,
    /// True for a `default:` section (affects the implicit-path edge).
    is_default: bool,
    id: Option<String>,
}

fn blank_stmt<'a>(kind: K, span: ByteSpan, header: Vec<E<'a>>) -> Stmt<'a> {
    Stmt {
        kind,
        span,
        header,
        body: None,
        else_part: None,
        arms: Vec::new(),
        finally_part: None,
        id: None,
    }
}

fn segment<'a>(els: &[E<'a>], src: &'a str) -> Vec<Stmt<'a>> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < els.len() {
        let before = i;
        let (stmts, next) = parse_one(els, i, src);
        out.extend(stmts);
        i = if next > before { next } else { before + 1 }; // progress guarantee
    }
    out
}

/// Parse one statement at `i`. Returns the produced statements (zero for a
/// stray `;`, several for a spliced bare block) and the index just past them.
fn parse_one<'a>(els: &[E<'a>], i: usize, src: &'a str) -> (Vec<Stmt<'a>>, usize) {
    // Empty statement.
    if els[i].text(src) == Some(";") {
        return (Vec::new(), i + 1);
    }
    // Bare block statement: splice inline.
    if els[i].is_brace() {
        if let E::G(b) = &els[i] {
            return (segment(&inner_elems(b, src), src), i + 1);
        }
    }

    match els[i].text(src) {
        Some("if") => {
            let (stmt, end) = parse_if(els, i, src);
            (vec![stmt], end)
        }
        Some("while") => {
            let (header, body_idx) = paren_header(els, i + 1);
            let (body, end) = parse_embedded(els, body_idx, src);
            let mut s = blank_stmt(K::While, span_range(els, i, end), header);
            s.body = Some(body);
            (vec![s], end)
        }
        Some("do") => {
            let (body, mut k) = parse_embedded(els, i + 1, src);
            // `while (cond) ;`
            let mut header = Vec::new();
            if els.get(k).and_then(|e| e.text(src)) == Some("while") {
                k += 1;
                if els.get(k).map(|e| e.is_paren()) == Some(true) {
                    header.push(reborrow(&els[k]));
                    k += 1;
                }
                if els.get(k).and_then(|e| e.text(src)) == Some(";") {
                    k += 1;
                }
            }
            let mut s = blank_stmt(K::DoWhile, span_range(els, i, k), header);
            s.body = Some(body);
            (vec![s], k)
        }
        Some("for") | Some("foreach") => {
            let kind = if els[i].text(src) == Some("for") {
                K::For
            } else {
                K::Foreach
            };
            let (header, body_idx) = paren_header(els, i + 1);
            let (body, end) = parse_embedded(els, body_idx, src);
            let mut s = blank_stmt(kind, span_range(els, i, end), header);
            s.body = Some(body);
            (vec![s], end)
        }
        Some("switch") => {
            let (header, body_idx) = paren_header(els, i + 1);
            let (arms, end) = switch_sections(els, body_idx, src);
            let mut s = blank_stmt(K::Switch, span_range(els, i, end), header);
            s.arms = arms;
            (vec![s], end)
        }
        Some("try") => {
            let (stmt, end) = parse_try(els, i, src);
            (vec![stmt], end)
        }
        Some("return") => flat(els, i, K::Return, src),
        Some("throw") => flat(els, i, K::Throw, src),
        Some("break") => flat(els, i, K::Break, src),
        Some("continue") => flat(els, i, K::Continue, src),
        Some("goto") => flat(els, i, K::Goto, src),
        Some("yield") => {
            if els.get(i + 1).and_then(|e| e.text(src)) == Some("break") {
                flat(els, i, K::YieldBreak, src)
            } else {
                flat(els, i, K::Expr, src) // `yield return e;` continues
            }
        }
        Some("using") if els.get(i + 1).map(|e| e.is_paren()) == Some(true) => {
            let (header, body_idx) = paren_header(els, i + 1);
            let (body, end) = parse_embedded(els, body_idx, src);
            let mut s = blank_stmt(K::Using, span_range(els, i, end), header);
            s.body = Some(body);
            (vec![s], end)
        }
        Some("using") => {
            // `using var x = …;` — a declaration with to-end-of-block scope;
            // segmented as a flat Local (the scope nuance is not modeled).
            let end = scan_to_semi(els, i, src);
            let k = classify_flat(&els[i + 1..end], src);
            (
                vec![blank_stmt(
                    k,
                    span_range(els, i, end),
                    els[i..end].iter().map(reborrow).collect(),
                )],
                end,
            )
        }
        Some("lock") | Some("fixed") => {
            let (header, body_idx) = paren_header(els, i + 1);
            let (body, end) = parse_embedded(els, body_idx, src);
            let mut s = blank_stmt(K::Lock, span_range(els, i, end), header);
            s.body = Some(body);
            (vec![s], end)
        }
        Some("checked") | Some("unchecked") | Some("unsafe")
            if els.get(i + 1).map(|e| e.is_brace()) == Some(true) =>
        {
            // No flow semantics: splice the block inline.
            if let E::G(b) = &els[i + 1] {
                return (segment(&inner_elems(b, src), src), i + 2);
            }
            (Vec::new(), i + 2)
        }
        _ => {
            // Local function in statement position: an Item (does not execute).
            if let Some(end) = local_fn_end(els, i, src) {
                return (
                    vec![blank_stmt(
                        K::Item,
                        span_range(els, i, end),
                        els[i..end].iter().map(reborrow).collect(),
                    )],
                    end,
                );
            }
            // Goto label (`name:`): fold away, parse the labeled statement.
            if els[i].ident_text(src).is_some()
                && els.get(i + 1).and_then(|e| e.text(src)) == Some(":")
                && i + 2 < els.len()
            {
                return parse_one(els, i + 2, src);
            }
            let end = scan_to_semi(els, i, src);
            let k = classify_flat(&els[i..end], src);
            (
                vec![blank_stmt(
                    k,
                    span_range(els, i, end),
                    els[i..end].iter().map(reborrow).collect(),
                )],
                end,
            )
        }
    }
}

/// A flat keyword-led statement: everything through the depth-0 `;`.
fn flat<'a>(els: &[E<'a>], i: usize, kind: K, src: &'a str) -> (Vec<Stmt<'a>>, usize) {
    let end = scan_to_semi(els, i, src);
    (
        vec![blank_stmt(
            kind,
            span_range(els, i, end),
            els[i..end].iter().map(reborrow).collect(),
        )],
        end,
    )
}

/// Expr vs Local for a flat statement (see [`flat_shape`]).
fn classify_flat(els: &[E<'_>], src: &str) -> K {
    match flat_shape(els, src) {
        FlatShape::Decl { .. } => K::Local,
        _ => K::Expr,
    }
}

/// End index (exclusive) past the first depth-0 `;`, or the run's end.
fn scan_to_semi(els: &[E<'_>], from: usize, src: &str) -> usize {
    let mut k = from;
    while k < els.len() {
        k += 1;
        if els[k - 1].text(src) == Some(";") {
            return k;
        }
    }
    els.len()
}

/// The `(…)` header group at `idx` (when present) and the body's index.
fn paren_header<'a>(els: &[E<'a>], idx: usize) -> (Vec<E<'a>>, usize) {
    if els.get(idx).map(|e| e.is_paren()) == Some(true) {
        (vec![reborrow(&els[idx])], idx + 1)
    } else {
        (Vec::new(), idx)
    }
}

/// An embedded statement body: a block (segmented) or one single statement.
fn parse_embedded<'a>(els: &[E<'a>], idx: usize, src: &'a str) -> (Vec<Stmt<'a>>, usize) {
    match els.get(idx) {
        Some(e) if e.is_brace() => {
            if let E::G(b) = e {
                (segment(&inner_elems(b, src), src), idx + 1)
            } else {
                (Vec::new(), idx + 1)
            }
        }
        Some(_) => parse_one(els, idx, src),
        None => (Vec::new(), idx),
    }
}

fn parse_if<'a>(els: &[E<'a>], i: usize, src: &'a str) -> (Stmt<'a>, usize) {
    let (header, body_idx) = paren_header(els, i + 1);
    let (then_block, mut end) = parse_embedded(els, body_idx, src);
    let mut else_part = None;
    if els.get(end).and_then(|e| e.text(src)) == Some("else") {
        let (block, block_end) = parse_embedded(els, end + 1, src);
        else_part = Some(block); // `else if` arrives as one nested If statement
        end = block_end;
    }
    let mut s = blank_stmt(K::If, span_range(els, i, end), header);
    s.body = Some(then_block);
    s.else_part = else_part;
    (s, end)
}

fn parse_try<'a>(els: &[E<'a>], i: usize, src: &'a str) -> (Stmt<'a>, usize) {
    let (body, mut k) = parse_embedded(els, i + 1, src);
    let mut arms = Vec::new();
    while els.get(k).and_then(|e| e.text(src)) == Some("catch") {
        let arm_start = k;
        k += 1;
        let mut header = Vec::new();
        if els.get(k).map(|e| e.is_paren()) == Some(true) {
            header.push(reborrow(&els[k]));
            k += 1;
        }
        if els.get(k).and_then(|e| e.text(src)) == Some("when") {
            k += 1;
            if els.get(k).map(|e| e.is_paren()) == Some(true) {
                header.push(reborrow(&els[k]));
                k += 1;
            }
        }
        let (block, next) = parse_embedded(els, k, src);
        arms.push(Arm {
            span: span_range(els, arm_start, next),
            header,
            body: block,
            is_default: false,
            id: None,
        });
        k = next;
    }
    let mut finally_part = None;
    if els.get(k).and_then(|e| e.text(src)) == Some("finally") {
        let (block, next) = parse_embedded(els, k + 1, src);
        finally_part = Some(block);
        k = next;
    }
    let mut s = blank_stmt(K::Try, span_range(els, i, k), Vec::new());
    s.body = Some(body);
    s.arms = arms;
    s.finally_part = finally_part;
    (s, k)
}

/// Parse the section list of the switch brace at `idx`.
fn switch_sections<'a>(els: &[E<'a>], idx: usize, src: &'a str) -> (Vec<Arm<'a>>, usize) {
    let Some(E::G(b)) = els.get(idx) else {
        return (Vec::new(), idx);
    };
    let inner = inner_elems(b, src);
    let mut arms = Vec::new();
    let mut i = 0;
    while i < inner.len() {
        if !label_starts_at(&inner, i, src) {
            i += 1; // stray tokens before the first label: skip, stay lossless
            continue;
        }
        let sec_start = i;
        // Stacked labels: consume `case …:` / `default:` runs.
        let mut header_end = i;
        while label_starts_at(&inner, header_end, src) {
            header_end = past_label(&inner, header_end, src);
        }
        let is_default = inner[sec_start..header_end]
            .iter()
            .any(|e| e.text(src) == Some("default"));
        let header: Vec<E<'a>> = inner[sec_start..header_end].iter().map(reborrow).collect();
        // Section body: statements until the next label at this level.
        let mut j = header_end;
        while j < inner.len() && !label_starts_at(&inner, j, src) {
            j += 1;
        }
        let body = segment(&inner[header_end..j], src);
        arms.push(Arm {
            span: span_range(&inner, sec_start, j.max(sec_start + 1)),
            header,
            body,
            is_default,
            id: None,
        });
        i = j;
    }
    (arms, idx + 1)
}

/// True when a `case …:` / `default:` section label begins at `i`. `case`
/// after `goto` is a jump, not a label; `default` is a label only when its
/// very next element is `:` (else it is the `default` literal/expression).
fn label_starts_at(els: &[E<'_>], i: usize, src: &str) -> bool {
    let prev_is_goto = i > 0 && els[i - 1].text(src) == Some("goto");
    match els.get(i).and_then(|e| e.text(src)) {
        Some("case") => !prev_is_goto,
        Some("default") => !prev_is_goto && els.get(i + 1).and_then(|e| e.text(src)) == Some(":"),
        _ => false,
    }
}

/// Index just past a label starting at `i` (past its depth-0 `:`).
fn past_label(els: &[E<'_>], i: usize, src: &str) -> usize {
    let mut k = i;
    while k < els.len() {
        k += 1;
        if els[k - 1].text(src) == Some(":") {
            return k;
        }
    }
    els.len()
}

/// If a local function declaration starts at `i`, the index just past it.
/// Signal: before any depth-0 `;`, `=`, or `new`, a non-keyword identifier
/// (or a `>` closing its generic clause) directly precedes a `Paren` group
/// that is followed by a `{ }` body, an `=>` expression body, or a `where`
/// constraint clause. Local functions are Items — they do not execute inline.
fn local_fn_end(els: &[E<'_>], i: usize, src: &str) -> Option<usize> {
    let mut k = i;
    while k < els.len() {
        match els[k].text(src) {
            Some(";") | Some("=") | Some("new") => return None,
            _ => {}
        }
        if els[k].is_paren() && k > i {
            let prev_ok = els[k - 1].ident_text(src).is_some() || els[k - 1].text(src) == Some(">");
            if !prev_ok {
                return None;
            }
            return match els.get(k + 1) {
                Some(e) if e.is_brace() => Some(k + 2),
                Some(e) if e.text(src) == Some("=>") => Some(scan_to_semi(els, k + 1, src)),
                Some(e) if e.text(src) == Some("where") => {
                    // Skip constraint tokens to the body brace.
                    let mut m = k + 2;
                    while m < els.len() && !els[m].is_brace() {
                        if els[m].text(src) == Some(";") {
                            return None;
                        }
                        m += 1;
                    }
                    if m < els.len() {
                        Some(m + 1)
                    } else {
                        None
                    }
                }
                _ => None,
            };
        }
        if els[k].is_brace() {
            return None;
        }
        k += 1;
    }
    None
}

fn span_range(els: &[E<'_>], from: usize, to: usize) -> ByteSpan {
    let hi = to.min(els.len()).max(from + 1).min(els.len());
    if from >= els.len() {
        return ByteSpan::empty_at(0);
    }
    let mut span = els[from].span();
    for e in &els[from..hi] {
        span = span.merge(e.span());
    }
    span
}

// ---------------------------------------------------------------------------
// Emission: statement nodes + FLOWS_TO control flow
// ---------------------------------------------------------------------------

/// A dangling flow source, exactly as in the Rust overlay.
struct Exit {
    from: String,
    role: &'static str,
    branch: Option<&'static str>,
}

impl Exit {
    fn seq(from: String) -> Exit {
        Exit {
            from,
            role: "seq",
            branch: None,
        }
    }
}

/// `continue` targets the nearest enclosing loop's header.
struct LoopCtx {
    header_id: String,
}

/// `break` targets the nearest enclosing loop OR switch (C# semantics), so
/// break collection is a separate stack that both push.
struct BreakCtx {
    breaks: Vec<Exit>,
}

struct Emitter<'a, 'g> {
    g: &'g mut Graph,
    src: &'a str,
    li: &'g LineIndex,
    fn_id: &'g str,
    prefix: &'g str,
    exit_id: &'g str,
    next: usize,
}

impl<'a, 'g> Emitter<'a, 'g> {
    fn emit_node(&mut self, kind_label: &'static str, span: ByteSpan, name: String) -> String {
        let id = format!("{}::{}", self.prefix, self.next);
        self.next += 1;
        let line = self.li.line_col(span.start).line;
        self.g.upsert_node(
            id.clone(),
            ont::STATEMENT,
            name,
            vec![
                ("stmt_kind", Json::str(kind_label)),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(span.start as u64)),
                ("span_end", Json::U64(span.end as u64)),
            ],
        );
        self.g
            .add_edge(self.fn_id, edge::CONTAINS, id.clone(), vec![]);
        id
    }

    fn flow(&mut self, from: &str, to: &str, role: &'static str, branch: Option<&'static str>) {
        let mut props = vec![("role", Json::str(role))];
        if let Some(b) = branch {
            props.push(("branch", Json::str(b)));
        }
        if role == "loop-back" || role == "continue" {
            props.push(("back_edge", Json::Bool(true)));
        }
        self.g.add_edge(from, edge::FLOWS_TO, to, props);
    }

    fn join(&mut self, incoming: Vec<Exit>, to: &str) {
        for e in incoming {
            self.flow(&e.from, to, e.role, e.branch);
        }
    }

    fn emit_block(
        &mut self,
        stmts: &mut [Stmt<'a>],
        incoming: Vec<Exit>,
        loops: &mut Vec<LoopCtx>,
        breaks: &mut Vec<BreakCtx>,
    ) -> Vec<Exit> {
        let mut pending = incoming;
        for s in stmts.iter_mut() {
            pending = self.emit_stmt(s, pending, loops, breaks);
        }
        pending
    }

    fn emit_stmt(
        &mut self,
        s: &mut Stmt<'a>,
        incoming: Vec<Exit>,
        loops: &mut Vec<LoopCtx>,
        breaks: &mut Vec<BreakCtx>,
    ) -> Vec<Exit> {
        let name = self.stmt_name(s);
        let id = self.emit_node(s.kind.label(), s.span, name);
        s.id = Some(id.clone());
        self.join(incoming, &id);

        match s.kind {
            K::Expr | K::Local | K::Item => vec![Exit::seq(id)],
            K::Return => {
                let exit = self.exit_id.to_string();
                self.flow(&id, &exit, "return", None);
                Vec::new()
            }
            K::Throw => {
                // Abnormal completion: modeled as function exit (the enclosing
                // try's branch/catch edge covers a local catch at section
                // grain — see the module docs and ADR-0003).
                let exit = self.exit_id.to_string();
                self.flow(&id, &exit, "throw", None);
                Vec::new()
            }
            K::YieldBreak => {
                let exit = self.exit_id.to_string();
                self.flow(&id, &exit, "yield-break", None);
                Vec::new()
            }
            K::Goto => Vec::new(), // target unmodeled: honest absence
            K::Break => {
                if let Some(ctx) = breaks.last_mut() {
                    ctx.breaks.push(Exit {
                        from: id,
                        role: "break",
                        branch: None,
                    });
                }
                Vec::new()
            }
            K::Continue => {
                if let Some(l) = loops.last() {
                    let header = l.header_id.clone();
                    self.flow(&id, &header, "continue", None);
                }
                Vec::new()
            }
            K::If => {
                let then_in = vec![Exit {
                    from: id.clone(),
                    role: "branch",
                    branch: Some("then"),
                }];
                let mut exits = match s.body.as_mut() {
                    Some(b) => self.emit_block(b, then_in, loops, breaks),
                    None => then_in,
                };
                let else_in = vec![Exit {
                    from: id.clone(),
                    role: "branch",
                    branch: Some("else"),
                }];
                match s.else_part.as_mut() {
                    Some(b) => exits.extend(self.emit_block(b, else_in, loops, breaks)),
                    None => exits.extend(else_in),
                }
                exits
            }
            K::While | K::For | K::Foreach | K::DoWhile => {
                loops.push(LoopCtx {
                    header_id: id.clone(),
                });
                breaks.push(BreakCtx { breaks: Vec::new() });
                let body_in = vec![Exit {
                    from: id.clone(),
                    role: "branch",
                    branch: Some("body"),
                }];
                let body_exits = match s.body.as_mut() {
                    Some(b) => self.emit_block(b, body_in, loops, breaks),
                    None => body_in,
                };
                for e in body_exits {
                    self.flow(&e.from, &id, "loop-back", e.branch);
                }
                loops.pop();
                let ctx = breaks.pop().expect("break ctx pushed above");
                let mut exits = ctx.breaks;
                // Every C# loop form tests a condition (or an iterator) at the
                // header, so all exit at the header too. (`for(;;)` still gets
                // a loop-exit edge — a documented over-approximation; C# has
                // no `loop` keyword to make infinite loops a grammar fact.)
                exits.push(Exit {
                    from: id,
                    role: "loop-exit",
                    branch: None,
                });
                exits
            }
            K::Switch => {
                breaks.push(BreakCtx { breaks: Vec::new() });
                let mut exits = Vec::new();
                let mut has_default = false;
                for arm in s.arms.iter_mut() {
                    has_default |= arm.is_default;
                    let arm_name = truncate(collapse(&els_text(&arm.header, self.src)));
                    let arm_id = self.emit_node("arm", arm.span, arm_name);
                    arm.id = Some(arm_id.clone());
                    let b = if arm.is_default { "default" } else { "case" };
                    self.flow(&id, &arm_id, "branch", Some(b));
                    // Dangling section exits (e.g. `goto case` recovery) merge
                    // conservatively into the continuation.
                    let section =
                        self.emit_block(&mut arm.body, vec![Exit::seq(arm_id)], loops, breaks);
                    exits.extend(section);
                }
                let ctx = breaks.pop().expect("switch break ctx pushed above");
                exits.extend(ctx.breaks);
                if !has_default {
                    // No default: the scrutinee may match nothing.
                    exits.push(Exit {
                        from: id,
                        role: "branch",
                        branch: Some("implicit"),
                    });
                }
                exits
            }
            K::Try => {
                let try_in = vec![Exit {
                    from: id.clone(),
                    role: "branch",
                    branch: Some("try"),
                }];
                let mut exits = match s.body.as_mut() {
                    Some(b) => self.emit_block(b, try_in, loops, breaks),
                    None => try_in,
                };
                for arm in s.arms.iter_mut() {
                    let arm_name = truncate(format!(
                        "catch {}",
                        collapse(&els_text(&arm.header, self.src))
                    ));
                    let arm_id = self.emit_node("catch", arm.span, arm_name);
                    arm.id = Some(arm_id.clone());
                    // May-transfer: the try statement branches to each catch.
                    self.flow(&id, &arm_id, "branch", Some("catch"));
                    exits.extend(self.emit_block(
                        &mut arm.body,
                        vec![Exit::seq(arm_id)],
                        loops,
                        breaks,
                    ));
                }
                match s.finally_part.as_mut() {
                    Some(fin) => self.emit_block(fin, exits, loops, breaks),
                    None => exits,
                }
            }
            K::Using | K::Lock => {
                let body_in = vec![Exit::seq(id)];
                match s.body.as_mut() {
                    Some(b) => self.emit_block(b, body_in, loops, breaks),
                    None => body_in,
                }
            }
        }
    }

    fn stmt_name(&self, s: &Stmt<'a>) -> String {
        let text = match s.kind {
            K::If | K::While | K::For | K::Foreach | K::Switch | K::Using | K::Lock => {
                format!(
                    "{} {}",
                    s.kind.label(),
                    collapse(&els_text(&s.header, self.src))
                )
            }
            K::DoWhile => format!("do while {}", collapse(&els_text(&s.header, self.src))),
            K::Try => "try".to_string(),
            _ => collapse(s.span.text(self.src)),
        };
        truncate(text)
    }
}

fn els_text<'a>(els: &[E<'a>], src: &'a str) -> String {
    if els.is_empty() {
        return String::new();
    }
    let mut span = els[0].span();
    for e in els {
        span = span.merge(e.span());
    }
    span.text(src).to_string()
}

fn collapse(text: &str) -> String {
    let mut out = String::with_capacity(text.len().min(NAME_LIMIT * 2));
    let mut in_ws = false;
    for ch in text.chars() {
        if ch.is_whitespace() {
            if !in_ws && !out.is_empty() {
                out.push(' ');
            }
            in_ws = true;
        } else {
            out.push(ch);
            in_ws = false;
        }
    }
    while out.ends_with(' ') {
        out.pop();
    }
    out
}

fn truncate(text: String) -> String {
    if text.chars().count() <= NAME_LIMIT {
        return text;
    }
    text.chars().take(NAME_LIMIT).collect()
}

// ---------------------------------------------------------------------------
// DATA_DEP: conservative intra-method def-use chains (may-reach, no kills
// through places, block-scoped declarations) — same semantics as the Rust
// overlay, C#'s surface: typed/`var` declarations, assignments and compound
// assignments to bare names, `for` initializers, `foreach` iteration
// variables, `catch (Type name)` bindings, parameters.
// ---------------------------------------------------------------------------

/// Definition sites that may reach a point: `(node id, def kind)`.
type Defs = Vec<(String, &'static str)>;
/// Variable name → reaching definition sites.
type Env = std::collections::BTreeMap<String, Defs>;
/// Names (re)bound in the current block, with the entry they shadowed.
type Saved = std::collections::BTreeMap<String, Option<Defs>>;
/// A pre-applied, block-scoped definition: `(name, def site, def kind)`.
type PreDef = (String, String, &'static str);

/// The shape of a flat statement, for def extraction.
enum FlatShape {
    /// `x = e` / `x op= e` — a redefinition of a bare name.
    Assign {
        name: String,
        compound: bool,
        rhs_from: usize,
    },
    /// `T a = e, b …;` / `var x = e;` / `T x;` — one or more declarators.
    Decl { parts: Vec<DeclPart> },
    /// Anything else: reads only.
    Plain,
}

/// One declarator: its name (when confidently identified) and the element
/// range of its initializer.
struct DeclPart {
    name: Option<String>,
    rhs: Option<(usize, usize)>,
}

struct DataFlow<'a, 'g> {
    g: &'g mut Graph,
    src: &'a str,
}

impl<'a, 'g> DataFlow<'a, 'g> {
    fn data_block(&mut self, stmts: &[Stmt<'a>], env: &mut Env, predefs: &[PreDef]) {
        let mut saved = Saved::new();
        for (name, site, kind) in predefs {
            saved
                .entry(name.clone())
                .or_insert_with(|| env.get(name).cloned());
            env.insert(name.clone(), vec![(site.clone(), kind)]);
        }
        for s in stmts {
            self.data_stmt(s, env, &mut saved);
        }
        for (name, old) in saved {
            match old {
                Some(defs) => {
                    env.insert(name, defs);
                }
                None => {
                    env.remove(&name);
                }
            }
        }
    }

    fn data_stmt(&mut self, s: &Stmt<'a>, env: &mut Env, saved: &mut Saved) {
        let id = match &s.id {
            Some(id) => id.clone(),
            None => return,
        };
        match s.kind {
            K::Expr | K::Local => match flat_shape(&s.header, self.src) {
                FlatShape::Assign {
                    name,
                    compound,
                    rhs_from,
                } => {
                    if compound {
                        self.emit_reads(&id, &s.header, env);
                    } else {
                        self.emit_reads(&id, &s.header[rhs_from.min(s.header.len())..], env);
                    }
                    env.insert(name, vec![(id.clone(), "assign")]);
                }
                FlatShape::Decl { parts } => {
                    for p in &parts {
                        if let Some((a, b)) = p.rhs {
                            self.emit_reads(
                                &id,
                                &s.header[a.min(s.header.len())..b.min(s.header.len())],
                                env,
                            );
                        }
                    }
                    for p in parts {
                        if let Some(name) = p.name {
                            saved
                                .entry(name.clone())
                                .or_insert_with(|| env.get(&name).cloned());
                            env.insert(name, vec![(id.clone(), "local")]);
                        }
                    }
                }
                FlatShape::Plain => self.emit_reads(&id, &s.header, env),
            },
            K::Return | K::Throw | K::Break | K::Continue | K::Goto | K::YieldBreak => {
                self.emit_reads(&id, &s.header, env);
            }
            K::Item => {}
            K::If => {
                self.emit_reads(&id, &s.header, env);
                let mut then_env = env.clone();
                if let Some(b) = &s.body {
                    self.data_block(b, &mut then_env, &[]);
                }
                match &s.else_part {
                    Some(b) => {
                        let mut else_env = env.clone();
                        self.data_block(b, &mut else_env, &[]);
                        *env = union_env(then_env, &else_env);
                    }
                    None => *env = union_env(then_env, env),
                }
            }
            K::While => {
                self.emit_reads(&id, &s.header, env);
                self.loop_body(s, env, &[]);
            }
            K::DoWhile => {
                // Condition runs after the body: its reads see body defs too.
                self.loop_body(s, env, &[]);
                self.emit_reads(&id, &s.header, env);
            }
            K::For => {
                // `for (init; cond; incr)` — the init's declarations def at
                // the for node, scoped to the loop; the whole header reads.
                let predefs: Vec<PreDef> = for_init_defs(&s.header, self.src)
                    .into_iter()
                    .map(|n| (n, id.clone(), "local"))
                    .collect();
                let mut header_env = env.clone();
                for (name, site, kind) in &predefs {
                    header_env.insert(name.clone(), vec![(site.clone(), kind)]);
                }
                self.emit_reads(&id, &s.header, &header_env);
                self.loop_body(s, env, &predefs);
            }
            K::Foreach => {
                // `foreach (var x in e)` — e reads; x defs at the node,
                // scoped to the body.
                let (defs, read_els) = foreach_split(&s.header, self.src);
                self.emit_reads(&id, &read_els, env);
                let predefs: Vec<PreDef> =
                    defs.into_iter().map(|n| (n, id.clone(), "loop")).collect();
                self.loop_body(s, env, &predefs);
            }
            K::Switch => {
                self.emit_reads(&id, &s.header, env);
                if s.arms.is_empty() {
                    return;
                }
                let mut merged: Option<Env> = None;
                let mut has_default = false;
                for arm in &s.arms {
                    has_default |= arm.is_default;
                    if let Some(arm_id) = &arm.id {
                        // Label expressions/patterns read (guards, constants).
                        self.emit_reads(arm_id, &arm.header, env);
                    }
                    let mut arm_env = env.clone();
                    self.data_block(&arm.body, &mut arm_env, &[]);
                    merged = Some(match merged {
                        Some(m) => union_env(m, &arm_env),
                        None => arm_env,
                    });
                }
                if let Some(mut m) = merged {
                    if !has_default {
                        m = union_env(m, env); // the implicit no-match path
                    }
                    *env = m;
                }
            }
            K::Try => {
                let mut try_env = env.clone();
                if let Some(b) = &s.body {
                    self.data_block(b, &mut try_env, &[]);
                }
                // A catch may run after any prefix of the try block: its
                // environment is the union of the pre-try and post-try states.
                let catch_base = union_env(try_env.clone(), env);
                let mut merged = try_env;
                for arm in &s.arms {
                    let mut arm_env = catch_base.clone();
                    let predefs: Vec<PreDef> = match &arm.id {
                        Some(arm_id) => catch_defs(&arm.header, self.src)
                            .into_iter()
                            .map(|n| (n, arm_id.clone(), "pattern"))
                            .collect(),
                        None => Vec::new(),
                    };
                    self.data_block(&arm.body, &mut arm_env, &predefs);
                    merged = union_env(merged, &arm_env);
                }
                if let Some(fin) = &s.finally_part {
                    self.data_block(fin, &mut merged, &[]);
                }
                *env = merged;
            }
            K::Using | K::Lock => {
                // `using (var x = e)` — e reads; x defs at the node, scoped to
                // the body, which always executes exactly once.
                let predefs: Vec<PreDef> = for_init_defs(&s.header, self.src)
                    .into_iter()
                    .map(|n| (n, id.clone(), "local"))
                    .collect();
                self.emit_reads(&id, &s.header, env);
                if let Some(b) = &s.body {
                    self.data_block(b, env, &predefs);
                }
            }
        }
    }

    /// Loop bodies are walked twice, exactly as in the Rust overlay: pass 1
    /// discovers body defs, the merge makes them reach the header, pass 2
    /// re-walks so uses see previous-iteration defs through the back edge.
    fn loop_body(&mut self, s: &Stmt<'a>, env: &mut Env, predefs: &[PreDef]) {
        let Some(body) = &s.body else {
            return;
        };
        let mut body_env = env.clone();
        self.data_block(body, &mut body_env, predefs);
        let merged = union_env(body_env, env);
        let mut second = merged.clone();
        self.data_block(body, &mut second, predefs);
        *env = merged;
    }

    /// Emit a `DATA_DEP` edge (use → every may-reaching def) for each read of
    /// an environment-known variable. Skips member names after `.`/`?.`/`->`,
    /// `global::`-style qualifications, keywords, and the `_` discard. Named
    /// arguments (`f(count: n)`) are NOT skipped — a name before `:` may also
    /// be a ternary's middle operand, and a spurious read on a rare collision
    /// is the conservative direction for may-reach.
    fn emit_reads(&mut self, stmt_id: &str, els: &[E<'a>], env: &Env) {
        let toks = flat_tokens(els);
        for (k, t) in toks.iter().enumerate() {
            if t.kind != tk::IDENT {
                continue;
            }
            let text = t.span.text(self.src);
            if is_keyword(text) || text == "_" {
                continue;
            }
            let prev = if k > 0 {
                Some(toks[k - 1].span.text(self.src))
            } else {
                None
            };
            let next = toks.get(k + 1).map(|n| n.span.text(self.src));
            if prev == Some(".") || prev == Some("?.") || prev == Some("->") {
                continue;
            }
            if prev == Some("::") || next == Some("::") {
                continue;
            }
            if let Some(defs) = env.get(text) {
                for (site, kind) in defs {
                    self.g.add_edge(
                        stmt_id,
                        edge::DATA_DEP,
                        site.clone(),
                        vec![
                            ("var", Json::str(text.to_string())),
                            ("def", Json::str(*kind)),
                        ],
                    );
                }
            }
        }
    }
}

/// Merge two may-reach environments: per name, the union of def sites.
fn union_env(mut a: Env, b: &Env) -> Env {
    for (name, defs) in b {
        let entry = a.entry(name.clone()).or_default();
        for d in defs {
            if !entry.contains(d) {
                entry.push(d.clone());
            }
        }
    }
    a
}

// ---------------------------------------------------------------------------
// Flat-statement shape analysis (defs)
// ---------------------------------------------------------------------------

fn is_predefined_type(text: &str) -> bool {
    PREDEFINED_TYPES.contains(&text)
}

/// True when `e` can end the *type* part of a declaration, directly before
/// the declared name: a type identifier, a predefined-type keyword, a generic
/// close, a nullable `?`, or an array-rank `[]` group.
fn type_ish(e: &E<'_>, src: &str) -> bool {
    match e {
        E::T(t) => {
            let text = t.span.text(src);
            (t.kind == tk::IDENT && !is_keyword(text))
                || is_predefined_type(text)
                || text == ">"
                || text == "?"
        }
        E::G(n) => n.kind == cst::BRACKET,
    }
}

/// Classify a flat statement's element run (trailing `;` included, harmless).
fn flat_shape(els: &[E<'_>], src: &str) -> FlatShape {
    // Compound assignment to a bare name: `x op= e`.
    for (q, e) in els.iter().enumerate() {
        let Some(text) = e.text(src) else { continue };
        if COMPOUND_ASSIGN.contains(&text) {
            if q == 1 {
                if let Some(name) = els[0].ident_text(src) {
                    return FlatShape::Assign {
                        name: name.to_string(),
                        compound: true,
                        rhs_from: q + 1,
                    };
                }
            }
            return FlatShape::Plain;
        }
        if text == "=" {
            // Simple assignment / declaration with initializer.
            if q == 0 {
                return FlatShape::Plain;
            }
            let Some(name) = els[q - 1].ident_text(src) else {
                return FlatShape::Plain; // `a[i] = e`, `p.f = e`, …
            };
            if q >= 2 && matches!(els[q - 2].text(src), Some(".") | Some("?.") | Some("->")) {
                return FlatShape::Plain;
            }
            if q == 1 {
                return FlatShape::Assign {
                    name: name.to_string(),
                    compound: false,
                    rhs_from: q + 1,
                };
            }
            // Type tokens precede the name: a declaration. The type part must
            // end type-ish (`int x = …`, `List<int> x = …`, `int[] x = …`);
            // anything else (`a.b x = …`? impossible; `await x = …`) is Plain.
            if !type_ish(&els[q - 2], src) {
                return FlatShape::Plain;
            }
            return FlatShape::Decl {
                parts: decl_parts(els, src),
            };
        }
        if text == ";" {
            break;
        }
    }
    // No assignment token: an uninitialized declaration `T x;`?
    let significant: Vec<usize> = (0..els.len())
        .filter(|&k| els[k].text(src) != Some(";"))
        .collect();
    if significant.len() >= 2 {
        let last = significant[significant.len() - 1];
        let prev = significant[significant.len() - 2];
        let head_ok = match els[significant[0]].text(src) {
            Some(t) => !is_keyword(t) || is_predefined_type(t),
            None => false,
        };
        if head_ok && els[last].ident_text(src).is_some() && type_ish(&els[prev], src) {
            return FlatShape::Decl {
                parts: vec![DeclPart {
                    name: els[last].ident_text(src).map(str::to_string),
                    rhs: None,
                }],
            };
        }
    }
    FlatShape::Plain
}

/// Split a declaration statement into declarators at depth-0, angle-0 commas.
/// Each part contributes the identifier before its `=` (or its trailing
/// identifier) and the element range of its initializer.
fn decl_parts(els: &[E<'_>], src: &str) -> Vec<DeclPart> {
    let mut parts = Vec::new();
    let mut angle: i32 = 0;
    let mut start = 0;
    let mut k = 0;
    while k <= els.len() {
        let at_end = k == els.len();
        let text = if at_end { None } else { els[k].text(src) };
        if let Some(t) = text {
            adjust_angle(&mut angle, t);
        }
        let at_cut = at_end || (angle == 0 && matches!(text, Some(",") | Some(";")));
        if at_cut {
            let part = &els[start..k];
            if !part.is_empty() {
                let eq = part.iter().position(|e| e.text(src) == Some("="));
                let name = match eq {
                    Some(q) if q >= 1 => part[q - 1].ident_text(src).map(str::to_string),
                    Some(_) => None,
                    None => part
                        .last()
                        .and_then(|e| e.ident_text(src))
                        .map(str::to_string),
                };
                let rhs = eq.map(|q| (start + q + 1, k));
                parts.push(DeclPart { name, rhs });
            }
            start = k + 1;
        }
        k += 1;
    }
    parts
}

fn adjust_angle(depth: &mut i32, text: &str) {
    for c in text.chars() {
        match c {
            '<' => *depth += 1,
            '>' => *depth -= 1,
            _ => {}
        }
    }
    if *depth < 0 {
        *depth = 0;
    }
}

/// Declared names in a `for`/`using` header's initializer clause: the paren
/// group's contents up to the first depth-0 `;`, run through the same
/// declaration shape analysis as a flat statement.
fn for_init_defs(header: &[E<'_>], src: &str) -> Vec<String> {
    let Some(E::G(p)) = header.first() else {
        return Vec::new();
    };
    let inner = paren_inner(p, src);
    let end = inner
        .iter()
        .position(|e| e.text(src) == Some(";"))
        .unwrap_or(inner.len());
    match flat_shape(&inner[..end], src) {
        FlatShape::Decl { parts } => parts.into_iter().filter_map(|p| p.name).collect(),
        FlatShape::Assign { .. } | FlatShape::Plain => Vec::new(),
    }
}

/// `foreach (PATTERN in EXPR)`: the bound names and the EXPR elements to read.
fn foreach_split<'a>(header: &[E<'a>], src: &'a str) -> (Vec<String>, Vec<E<'a>>) {
    let Some(E::G(p)) = header.first() else {
        return (Vec::new(), Vec::new());
    };
    let inner = paren_inner(p, src);
    let Some(in_idx) = inner.iter().position(|e| e.text(src) == Some("in")) else {
        return (Vec::new(), inner);
    };
    let pat = &inner[..in_idx];
    let reads: Vec<E<'a>> = inner[in_idx + 1..].iter().map(reborrow).collect();
    // Tuple deconstruction: names inside the group directly before `in` (the
    // last identifier of each comma segment). Simple form: the last
    // identifier of the pattern run.
    let mut names = Vec::new();
    match pat.last() {
        Some(E::G(g)) if g.kind == cst::PAREN => {
            let tup = paren_inner(g, src);
            let mut segment_last: Option<String> = None;
            for e in &tup {
                if e.text(src) == Some(",") {
                    if let Some(n) = segment_last.take() {
                        names.push(n);
                    }
                    continue;
                }
                if let Some(t) = e.ident_text(src) {
                    segment_last = Some(t.to_string());
                }
            }
            if let Some(n) = segment_last {
                names.push(n);
            }
        }
        _ => {
            if let Some(n) = pat.iter().rev().find_map(|e| e.ident_text(src)) {
                names.push(n.to_string());
            }
        }
    }
    (names, reads)
}

/// `catch (ExceptionType name)` — the bound name, when one is declared. The
/// declaration shape rule applies: the last element must be a non-keyword
/// identifier preceded by something type-ish (`catch (Exception)` binds
/// nothing — its lone identifier is the type).
fn catch_defs(header: &[E<'_>], src: &str) -> Vec<String> {
    let Some(E::G(p)) = header.first() else {
        return Vec::new();
    };
    let inner = paren_inner(p, src);
    if inner.len() >= 2 {
        let last = &inner[inner.len() - 1];
        let prev = &inner[inner.len() - 2];
        if let Some(name) = last.ident_text(src) {
            if type_ish(prev, src) {
                return vec![name.to_string()];
            }
        }
    }
    Vec::new()
}

/// A paren group's contents without its `(` / `)` delimiters.
fn paren_inner<'a>(p: &'a Node, src: &str) -> Vec<E<'a>> {
    let mut v = elems(p);
    if v.first().and_then(|e| e.text(src)) == Some("(") {
        v.remove(0);
    }
    if v.last().and_then(|e| e.text(src)) == Some(")") {
        v.pop();
    }
    v
}

/// Every non-trivia token under `els`, in source order (groups flattened).
fn flat_tokens<'a>(els: &[E<'a>]) -> Vec<&'a Token> {
    let mut out = Vec::new();
    for e in els {
        match e {
            E::T(t) => out.push(*t),
            E::G(n) => node_tokens(n, &mut out),
        }
    }
    out
}

fn node_tokens<'a>(n: &'a Node, out: &mut Vec<&'a Token>) {
    for c in &n.children {
        match c {
            Child::Token(t) if !t.trivia => out.push(t),
            Child::Token(_) => {}
            Child::Node(inner) => node_tokens(inner, out),
        }
    }
}

/// Parameter names bound by a method header: the last direct `Paren` child is
/// the parameter list (the same rule `header_is_method` uses); each depth-0,
/// angle-0 comma segment contributes its last non-keyword identifier before
/// any `=` default value.
fn param_names(header: &Node, src: &str) -> Vec<String> {
    let mut last_paren: Option<&Node> = None;
    for c in &header.children {
        if let Child::Node(n) = c {
            if n.kind == cst::PAREN {
                last_paren = Some(n);
            }
        }
    }
    let Some(p) = last_paren else {
        return Vec::new();
    };
    let inner = paren_inner(p, src);
    let mut out = Vec::new();
    let mut angle: i32 = 0;
    let mut start = 0;
    let mut k = 0;
    while k <= inner.len() {
        let at_end = k == inner.len();
        let text = if at_end { None } else { inner[k].text(src) };
        if let Some(t) = text {
            adjust_angle(&mut angle, t);
        }
        if at_end || (angle == 0 && text == Some(",")) {
            let part = &inner[start..k];
            let cut = part
                .iter()
                .position(|e| e.text(src) == Some("="))
                .unwrap_or(part.len());
            if let Some(name) = part[..cut].iter().rev().find_map(|e| e.ident_text(src)) {
                if !out.contains(&name.to_string()) {
                    out.push(name.to_string());
                }
            }
            start = k + 1;
        }
        k += 1;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::csharp::parser::parse;
    use crate::lang::frontend::SourceFile;

    fn base_and_cpg(src: &str) -> (Graph, Graph) {
        let tree = parse("Sample.cs", src);
        let file = SourceFile {
            rel_path: "Sample.cs".to_string(),
            module_path: vec![],
            source: &tree.source,
            root: &tree.root,
        };
        let base = crate::lang::csharp::lower::lower("Demo", std::slice::from_ref(&file), &[]);
        let cpg =
            crate::lang::csharp::lower::lower_with_cpg("Demo", std::slice::from_ref(&file), &[]);
        (base, cpg)
    }

    /// All FLOWS_TO edges as `from -role[/branch]-> to`, with the shared
    /// statement-id prefix stripped for readable assertions.
    fn flows(g: &Graph) -> Vec<String> {
        let mut v: Vec<String> = g
            .edges()
            .filter(|e| e.kind == edge::FLOWS_TO)
            .map(|e| {
                let role = match e.props.get("role") {
                    Some(Json::Str(s)) => s.clone(),
                    _ => String::new(),
                };
                let branch = match e.props.get("branch") {
                    Some(Json::Str(s)) => format!("/{s}"),
                    _ => String::new(),
                };
                format!("{} -{role}{branch}-> {}", short(&e.from), short(&e.to))
            })
            .collect();
        v.sort();
        v
    }

    fn short(id: &str) -> String {
        id.rsplit("::").next().unwrap_or(id).to_string()
    }

    fn cpg_flows(src: &str) -> Vec<String> {
        let (_, g) = base_and_cpg(src);
        flows(&g)
    }

    /// All DATA_DEP edges as `use -var/defkind-> def`, prefix-stripped.
    fn deps(g: &Graph) -> Vec<String> {
        let mut v: Vec<String> = g
            .edges()
            .filter(|e| e.kind == edge::DATA_DEP)
            .map(|e| {
                let var = match e.props.get("var") {
                    Some(Json::Str(s)) => s.clone(),
                    _ => String::new(),
                };
                let def = match e.props.get("def") {
                    Some(Json::Str(s)) => s.clone(),
                    _ => String::new(),
                };
                format!("{} -{var}/{def}-> {}", short(&e.from), short(&e.to))
            })
            .collect();
        v.sort();
        v
    }

    fn cpg_deps(src: &str) -> Vec<String> {
        let (_, g) = base_and_cpg(src);
        deps(&g)
    }

    // --- control flow: exact-edge assertions per construct -------------------

    #[test]
    fn sequential_flow_entry_to_exit() {
        let got = cpg_flows("class C { void M() { A(); B(); } }");
        assert_eq!(got, vec!["0 -seq-> 1", "1 -seq-> exit", "C.M#1 -entry-> 0"]);
    }

    #[test]
    fn if_else_with_embedded_bodies_branches_and_merges() {
        // C# allows non-block embedded bodies: `if (c) A(); else B();`.
        let got = cpg_flows("class C { void M(bool c) { if (c) A(); else B(); D(); } }");
        assert_eq!(
            got,
            vec![
                "0 -branch/else-> 2",
                "0 -branch/then-> 1",
                "1 -seq-> 3",
                "2 -seq-> 3",
                "3 -seq-> exit",
                "C.M#1 -entry-> 0",
            ]
        );
    }

    #[test]
    fn if_without_else_falls_through() {
        let got = cpg_flows("class C { void M(bool c) { if (c) { A(); } B(); } }");
        assert_eq!(
            got,
            vec![
                "0 -branch/else-> 2",
                "0 -branch/then-> 1",
                "1 -seq-> 2",
                "2 -seq-> exit",
                "C.M#1 -entry-> 0",
            ]
        );
    }

    #[test]
    fn while_loop_with_break_and_continue() {
        let got = cpg_flows(
            "class C { void M(bool c) { while (c) { if (c) { break; } if (c) { continue; } A(); } B(); } }",
        );
        assert_eq!(
            got,
            vec![
                "0 -branch/body-> 1",
                "0 -loop-exit-> 6",
                "1 -branch/else-> 3",
                "1 -branch/then-> 2",
                "2 -break-> 6",
                "3 -branch/else-> 5",
                "3 -branch/then-> 4",
                "4 -continue-> 0",
                "5 -loop-back-> 0",
                "6 -seq-> exit",
                "C.M#1 -entry-> 0",
            ]
        );
    }

    #[test]
    fn do_while_has_the_loop_shape_with_do_kind() {
        let got = cpg_flows("class C { void M(bool c) { do { A(); } while (c); B(); } }");
        assert_eq!(
            got,
            vec![
                "0 -branch/body-> 1",
                "0 -loop-exit-> 2",
                "1 -loop-back-> 0",
                "2 -seq-> exit",
                "C.M#1 -entry-> 0",
            ]
        );
        let (_, g) = base_and_cpg("class C { void M(bool c) { do { A(); } while (c); B(); } }");
        let do_node = g
            .nodes()
            .find(|n| n.props.get("stmt_kind") == Some(&Json::str("do")))
            .expect("a do-kind statement");
        assert!(do_node.name.starts_with("do while"));
    }

    #[test]
    fn foreach_loops_like_while() {
        let got =
            cpg_flows("class C { void M(int[] xs) { foreach (var x in xs) { A(x); } B(); } }");
        assert_eq!(
            got,
            vec![
                "0 -branch/body-> 1",
                "0 -loop-exit-> 2",
                "1 -loop-back-> 0",
                "2 -seq-> exit",
                "C.M#1 -entry-> 0",
            ]
        );
    }

    #[test]
    fn switch_break_exits_the_switch_not_a_loop() {
        // s0=switch, s1=arm(case 0), s2=A();, s3=break, s4=arm(case 1),
        // s5=return 1;, s6=arm(default), s7=B();, s8=break, s9=D();, s10=return 0;
        let got = cpg_flows(
            "class C { int M(int x) { switch (x) { case 0: A(); break; case 1: return 1; default: B(); break; } D(); return 0; } }",
        );
        assert_eq!(
            got,
            vec![
                "0 -branch/case-> 1",
                "0 -branch/case-> 4",
                "0 -branch/default-> 6",
                "1 -seq-> 2",
                "10 -return-> exit",
                "2 -seq-> 3",
                "3 -break-> 9",
                "4 -seq-> 5",
                "5 -return-> exit",
                "6 -seq-> 7",
                "7 -seq-> 8",
                "8 -break-> 9",
                "9 -seq-> 10",
                "C.M#1 -entry-> 0",
            ]
        );
    }

    #[test]
    fn switch_without_default_keeps_the_implicit_path() {
        // s0=switch, s1=arm, s2=break, s3=after: the scrutinee may match
        // nothing, so the switch itself reaches the continuation.
        let got = cpg_flows("class C { void M(int x) { switch (x) { case 0: break; } A(); } }");
        assert_eq!(
            got,
            vec![
                "0 -branch/case-> 1",
                "0 -branch/implicit-> 3",
                "1 -seq-> 2",
                "2 -break-> 3",
                "3 -seq-> exit",
                "C.M#1 -entry-> 0",
            ]
        );
    }

    #[test]
    fn break_inside_a_switch_inside_a_loop_binds_to_the_switch() {
        // s0=while, s1=switch, s2=arm, s3=break(switch!), s4=after-switch:
        // the break reaches A() inside the loop, NOT the loop exit.
        let got = cpg_flows(
            "class C { void M(bool c, int x) { while (c) { switch (x) { case 0: break; } A(); } } }",
        );
        assert_eq!(
            got,
            vec![
                "0 -branch/body-> 1",
                "0 -loop-exit-> exit",
                "1 -branch/case-> 2",
                "1 -branch/implicit-> 4",
                "2 -seq-> 3",
                "3 -break-> 4",
                "4 -loop-back-> 0",
                "C.M#1 -entry-> 0",
            ]
        );
    }

    #[test]
    fn try_catch_finally_may_transfer_and_merge() {
        // s0=try, s1=A, s2=catch, s3=B, s4=F(finally), s5=D.
        let got = cpg_flows(
            "class C { void M() { try { A(); } catch (IOException e) { B(); } finally { F(); } D(); } }",
        );
        assert_eq!(
            got,
            vec![
                "0 -branch/catch-> 2",
                "0 -branch/try-> 1",
                "1 -seq-> 4",
                "2 -seq-> 3",
                "3 -seq-> 4",
                "4 -seq-> 5",
                "5 -seq-> exit",
                "C.M#1 -entry-> 0",
            ]
        );
    }

    #[test]
    fn throw_diverges_to_exit() {
        let got = cpg_flows("class C { void M(bool c) { if (c) { throw new E(); } A(); } }");
        assert_eq!(
            got,
            vec![
                "0 -branch/else-> 2",
                "0 -branch/then-> 1",
                "1 -throw-> exit",
                "2 -seq-> exit",
                "C.M#1 -entry-> 0",
            ]
        );
    }

    #[test]
    fn expression_bodied_method_is_one_statement() {
        let got = cpg_flows("class C { int M(int x) => x + 1; }");
        assert_eq!(got, vec!["0 -seq-> exit", "C.M#1 -entry-> 0"]);
    }

    #[test]
    fn local_function_is_an_item_not_flow() {
        // s0=item (local fn does not execute inline), s1=call.
        let got = cpg_flows("class C { void M() { int F(int a) { return a; } Use(F(1)); } }");
        assert_eq!(got, vec!["0 -seq-> 1", "1 -seq-> exit", "C.M#1 -entry-> 0"]);
        let (_, g) = base_and_cpg("class C { void M() { int F(int a) { return a; } Use(F(1)); } }");
        assert!(g
            .nodes()
            .any(|n| n.props.get("stmt_kind") == Some(&Json::str("item"))));
    }

    // --- data flow: exact def-use assertions ----------------------------------

    #[test]
    fn params_are_defs_at_the_function() {
        let got = cpg_deps("class C { int Add(int a, int b) { return a + b; } }");
        assert_eq!(got, vec!["0 -a/param-> C.Add#1", "0 -b/param-> C.Add#1"]);
    }

    #[test]
    fn local_decl_and_use_chain() {
        let got = cpg_deps("class C { void M() { int a = 1; int b = a + 1; Use(b); } }");
        assert_eq!(got, vec!["1 -a/local-> 0", "2 -b/local-> 1"]);
    }

    #[test]
    fn var_decl_is_a_local_def() {
        let got = cpg_deps("class C { void M() { var a = Mk(); Use(a); } }");
        assert_eq!(got, vec!["1 -a/local-> 0"]);
    }

    #[test]
    fn branch_defs_join_instead_of_replacing() {
        let got = cpg_deps("class C { void M(bool c) { int x = 1; if (c) { x = 2; } Use(x); } }");
        assert_eq!(
            got,
            vec!["1 -c/param-> C.M#1", "3 -x/assign-> 2", "3 -x/local-> 0"]
        );
    }

    #[test]
    fn compound_assignment_reads_its_old_value() {
        let got = cpg_deps("class C { void M() { int x = 1; x += 2; Use(x); } }");
        assert_eq!(got, vec!["1 -x/local-> 0", "2 -x/assign-> 1"]);
    }

    #[test]
    fn projection_store_is_a_read_not_a_def() {
        let got = cpg_deps("class C { void M() { var x = Mk(); x.F = 1; Use(x); } }");
        assert_eq!(got, vec!["1 -x/local-> 0", "2 -x/local-> 0"]);
    }

    #[test]
    fn foreach_binds_its_iteration_variable() {
        let got = cpg_deps("class C { void M(int[] xs) { foreach (var x in xs) { Use(x); } } }");
        assert_eq!(got, vec!["0 -xs/param-> C.M#1", "1 -x/loop-> 0"]);
    }

    #[test]
    fn for_initializer_defs_at_the_for_node() {
        // s0=for (i defined at it, self-read in cond/incr), s1=body use.
        let got = cpg_deps("class C { void M(int n) { for (int i = 0; i < n; i++) { Use(i); } } }");
        assert_eq!(
            got,
            vec!["0 -i/local-> 0", "0 -n/param-> C.M#1", "1 -i/local-> 0"]
        );
    }

    #[test]
    fn catch_variable_is_a_def_at_the_catch_clause() {
        // s0=try, s1=A();, s2=catch, s3=Log(e);
        let got = cpg_deps("class C { void M() { try { A(); } catch (Exception e) { Log(e); } } }");
        assert_eq!(got, vec!["3 -e/pattern-> 2"]);
    }

    #[test]
    fn catch_without_a_variable_binds_nothing() {
        let got = cpg_deps("class C { void M() { try { A(); } catch (Exception) { B(); } } }");
        assert_eq!(got, Vec::<String>::new());
    }

    #[test]
    fn loop_back_edge_reaches_earlier_uses() {
        // Through the back edge, the body's use may read its own later def.
        let got = cpg_deps(
            "class C { void M(bool c) { int x = 0; while (c) { Use(x); x = Next(x); } } }",
        );
        assert_eq!(
            got,
            vec![
                "1 -c/param-> C.M#1",
                "2 -x/assign-> 3",
                "2 -x/local-> 0",
                "3 -x/assign-> 3",
                "3 -x/local-> 0",
            ]
        );
    }

    #[test]
    fn decl_scope_ends_at_block_end() {
        let got = cpg_deps(
            "class C { void M(bool c) { int x = 1; if (c) { int y = 2; Use(y); } Use(x); } }",
        );
        assert_eq!(
            got,
            vec!["1 -c/param-> C.M#1", "3 -y/local-> 2", "4 -x/local-> 0"]
        );
    }

    #[test]
    fn multi_declarator_statement_defs_every_name() {
        let got = cpg_deps("class C { void M() { int a = 1, b = 2; Use(a); Use(b); } }");
        assert_eq!(got, vec!["1 -a/local-> 0", "2 -b/local-> 0"]);
    }

    // --- the hand-verified nontrivial method (mirrors the corpus fixture) ----

    const SCORE: &str = "class C {\n    public int Score(int[] xs) {\n        int total = 0;\n        foreach (var x in xs) {\n            if (x < 0) { continue; }\n            total += x;\n        }\n        switch (total) {\n            case 0: return -1;\n            default: break;\n        }\n        return total;\n    }\n}\n";

    #[test]
    fn hand_verified_cfg_for_score() {
        // Statements (pre-order): s0 `int total = 0;`, s1 foreach, s2 if,
        // s3 continue, s4 `total += x;`, s5 switch, s6 arm `case 0:`,
        // s7 `return -1;`, s8 arm `default:`, s9 break, s10 `return total;`.
        // Every edge below was derived by hand from C# semantics — see the
        // K3a report for the derivation.
        let got = cpg_flows(SCORE);
        assert_eq!(
            got,
            vec![
                "0 -seq-> 1",
                "1 -branch/body-> 2",
                "1 -loop-exit-> 5",
                "10 -return-> exit",
                "2 -branch/else-> 4",
                "2 -branch/then-> 3",
                "3 -continue-> 1",
                "4 -loop-back-> 1",
                "5 -branch/case-> 6",
                "5 -branch/default-> 8",
                "6 -seq-> 7",
                "7 -return-> exit",
                "8 -seq-> 9",
                "9 -break-> 10",
                "C.Score#2 -entry-> 0",
            ]
        );
    }

    #[test]
    fn hand_verified_data_deps_for_score() {
        let got = cpg_deps(SCORE);
        assert_eq!(
            got,
            vec![
                "1 -xs/param-> C.Score#2",
                "10 -total/assign-> 4",
                "10 -total/local-> 0",
                "2 -x/loop-> 1",
                "4 -total/assign-> 4",
                "4 -total/local-> 0",
                "4 -x/loop-> 1",
                "5 -total/assign-> 4",
                "5 -total/local-> 0",
            ]
        );
    }

    // --- invariants -----------------------------------------------------------

    #[test]
    fn cpg_lowering_is_byte_deterministic() {
        let (_, first) = base_and_cpg(SCORE);
        let (_, second) = base_and_cpg(SCORE);
        assert_eq!(
            first.to_jsonl(),
            second.to_jsonl(),
            "two CPG runs over the same source must be byte-identical"
        );
    }

    #[test]
    fn cpg_output_is_a_strict_superset_of_base() {
        let (base, cpg) = base_and_cpg(SCORE);
        let cpg_jsonl = cpg.to_jsonl();
        let cpg_lines: std::collections::BTreeSet<&str> = cpg_jsonl.lines().collect();
        for line in base.to_jsonl().lines() {
            assert!(
                cpg_lines.contains(line),
                "base line missing from cpg output: {line}"
            );
        }
        assert!(cpg.node_count() > base.node_count(), "overlay must add");
    }

    #[test]
    fn top_level_statement_entry_markers_get_no_overlay() {
        // The synthetic main shares one fn id across several statement blocks;
        // it is excluded from the overlay by design (no id collisions).
        let src = "var builder = WebApplication.CreateBuilder(args);\nvar app = builder.Build();\napp.Run();\n";
        let (_, g) = base_and_cpg(src);
        assert_eq!(g.count_nodes_of(ont::STATEMENT), 0);
    }
}
