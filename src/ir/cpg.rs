//! The deterministic Code Property Graph overlay (ADR-0003).
//!
//! Given one function's lossless body token tree, emit fine-grained
//! [`crate::ir::ontology::node::STATEMENT`] nodes plus intra-function
//! `FLOWS_TO` (control flow) and `DATA_DEP` (def-use) edges. Opt-in: only the
//! `cpg` pipeline path calls this, so the base graph and its goldens never
//! move.
//!
//! Bodies are balanced token trees (ADR-0001), not statement ASTs, so this
//! module performs **statement segmentation** over the tree. It relies on
//! grammar facts, never guesses: a `;` inside a nested group is invisible at
//! statement level because groups are atomic, and Rust bans bare `{`
//! expressions in `if`/`while`/`for`/`match` headers, so the first depth-0
//! `Brace` after such a keyword is always the body.
//!
//! Everything here is deterministic and std-only: statement ids are assigned
//! by a fixed pre-order walk, and all output goes through the de-duplicating
//! `BTreeMap`-ordered [`Graph`] API.

use crate::core::cst::{Child, Node, Token};
use crate::core::span::{ByteSpan, LineIndex};
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::rust::lexer::{is_keyword, kind as tk};
use crate::lang::rust::parser::node as cst;

use crate::core::json::Json;

/// Maximum characters of collapsed source text used as a statement node name.
const NAME_LIMIT: usize = 48;

/// Emit the CPG overlay for one function into `g`.
///
/// `fn_id` is the function's base-graph id (`fn::{qual}#{line}`); statement ids
/// derive from it (`stmt::{qual}#{line}::{n}`), so the overlay attaches to the
/// exact node the base graph declared.
pub fn emit_function_cpg(
    g: &mut Graph,
    fn_id: &str,
    block: &Node,
    signature: Option<&Node>,
    src: &str,
) {
    let _ = emit_function_cpg_stmts(g, fn_id, block, signature, src);
}

/// [`emit_function_cpg`], returning the segmented statement tree with the
/// assigned node ids. Identical emission — the rewrite engine (ADR-0006)
/// consumes the returned tree so rules and overlay share ONE segmentation.
pub(crate) fn emit_function_cpg_stmts<'a>(
    g: &mut Graph,
    fn_id: &str,
    block: &'a Node,
    signature: Option<&Node>,
    src: &'a str,
) -> Vec<Stmt<'a>> {
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
    // Virtual exit node: every function with a body has exactly one.
    em.g.upsert_node(
        exit_id.clone(),
        ont::STATEMENT,
        "<exit>",
        vec![("virtual", Json::Bool(true)), ("role", Json::str("exit"))],
    );
    em.g.add_edge(fn_id, edge::CONTAINS, exit_id.clone(), vec![]);

    // Control flow: the function entry reaches the first statement; whatever
    // falls off the end reaches the exit node.
    let entry = vec![Exit {
        from: fn_id.to_string(),
        role: "entry",
        branch: None,
    }];
    let mut loops: Vec<LoopCtx> = Vec::new();
    let final_exits = em.emit_block(&mut stmts, entry, &mut loops);
    let exit = exit_id.clone();
    em.join(final_exits, &exit);

    // Data flow: def-use chains over the same statement tree (ids assigned
    // above). Parameters are definition sites at the function node itself.
    let mut env = Env::new();
    if let Some(sig) = signature {
        for name in param_names(sig, src) {
            env.insert(name, vec![(fn_id.to_string(), "param")]);
        }
    }
    let mut df = DataFlow { g: em.g, src };
    df.data_block(&stmts, &mut env, &[]);
    stmts
}

// ---------------------------------------------------------------------------
// Element view: the non-trivia children of a token-tree node.
// ---------------------------------------------------------------------------

/// One significant element of a token-tree level: a token or a balanced group.
pub(crate) enum E<'a> {
    T(&'a Token),
    G(&'a Node),
}

impl<'a> E<'a> {
    pub(crate) fn span(&self) -> ByteSpan {
        match self {
            E::T(t) => t.span,
            E::G(n) => n.span,
        }
    }

    pub(crate) fn text(&self, src: &'a str) -> Option<&'a str> {
        match self {
            E::T(t) => Some(t.span.text(src)),
            E::G(_) => None,
        }
    }

    pub(crate) fn is_brace(&self) -> bool {
        matches!(self, E::G(n) if n.kind == cst::BRACE || n.kind == cst::BLOCK)
    }
}

/// Non-trivia elements of `node`.
pub(crate) fn elems<'a>(node: &'a Node) -> Vec<E<'a>> {
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

/// Elements of a brace group without its `{` / `}` delimiter tokens.
pub(crate) fn inner_elems<'a>(brace: &'a Node, src: &str) -> Vec<E<'a>> {
    let mut v = elems(brace);
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

/// Statement classification. `Item` covers declarations in statement position
/// (control flows through them trivially — they do not execute).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum StmtKind {
    Let,
    Expr,
    Return,
    Break,
    Continue,
    Item,
    If,
    While,
    For,
    Loop,
    Match,
}

impl StmtKind {
    pub(crate) fn label(self) -> &'static str {
        match self {
            StmtKind::Let => "let",
            StmtKind::Expr => "expr",
            StmtKind::Return => "return",
            StmtKind::Break => "break",
            StmtKind::Continue => "continue",
            StmtKind::Item => "item",
            StmtKind::If => "if",
            StmtKind::While => "while",
            StmtKind::For => "for",
            StmtKind::Loop => "loop",
            StmtKind::Match => "match",
        }
    }
}

/// One segmented statement. Structured kinds carry their sub-blocks; `els`
/// always covers the whole construct (header + bodies) for span/name purposes.
pub(crate) struct Stmt<'a> {
    pub(crate) kind: StmtKind,
    pub(crate) span: ByteSpan,
    /// Header elements: for `if`/`while`/`for`/`match` the condition/pattern
    /// region between the keyword and the body; for `let`/`expr`/… the whole
    /// flat element run.
    pub(crate) header: Vec<E<'a>>,
    /// `if`: then-block. `while`/`for`/`loop`: body.
    pub(crate) body: Option<Vec<Stmt<'a>>>,
    /// The brace group holding `body`, when one exists — the rewrite engine
    /// (ADR-0006) needs the exact `{ … }` byte spans; emission ignores it.
    pub(crate) body_group: Option<&'a Node>,
    /// `if` only: the else continuation.
    pub(crate) else_part: Option<ElsePart<'a>>,
    /// `match` only.
    pub(crate) arms: Vec<Arm<'a>>,
    /// Loop label (`'outer`) for `while`/`for`/`loop` statements, exactly as it
    /// appears in source (leading apostrophe included). Labeled `break`/
    /// `continue` target the loop whose label matches theirs.
    pub(crate) label: Option<String>,
    /// Assigned during emission (pre-order); consumed by the data-flow pass.
    pub(crate) id: Option<String>,
}

pub(crate) enum ElsePart<'a> {
    Block(&'a Node, Vec<Stmt<'a>>),
    If(Box<Stmt<'a>>),
}

/// One match arm: pattern elements, then either a block body or a flat
/// expression body.
pub(crate) struct Arm<'a> {
    pub(crate) span: ByteSpan,
    pub(crate) pattern: Vec<E<'a>>,
    pub(crate) block: Option<Vec<Stmt<'a>>>,
    /// Flat expression body (empty when `block` is set). Consumed by the
    /// control-flow pass (divergence detection) and the data-flow pass (reads).
    pub(crate) expr: Vec<E<'a>>,
    pub(crate) id: Option<String>,
}

/// Item-starting keywords in statement position.
fn is_item_start(word: &str) -> bool {
    matches!(
        word,
        "fn" | "struct"
            | "enum"
            | "trait"
            | "impl"
            | "mod"
            | "use"
            | "static"
            | "type"
            | "macro_rules"
            | "extern"
    )
}

/// Segment one block level's elements into statements. Bare `{}` and
/// `unsafe {}` block statements are spliced inline (their statements join this
/// sequence), matching ADR-0003.
pub(crate) fn segment<'a>(els: &[E<'a>], src: &'a str) -> Vec<Stmt<'a>> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < els.len() {
        // Empty statements.
        if els[i].text(src) == Some(";") {
            i += 1;
            continue;
        }
        // Loop labels: `'name :` prefixes a loop/block; fold into the statement.
        let start = i;
        let mut j = i;
        let mut label: Option<String> = None;
        if matches!(&els[j], E::T(t) if t.kind == tk::LIFETIME)
            && els.get(j + 1).and_then(|e| e.text(src)) == Some(":")
        {
            label = els[j].text(src).map(str::to_string);
            j += 2;
            if j >= els.len() {
                // Dangling label; consume to avoid an infinite loop.
                i = j;
                continue;
            }
        }

        match els[j].text(src) {
            Some("let") => {
                let end = scan_to_semi(els, j, src);
                out.push(flat_stmt(StmtKind::Let, &els[start..end], src));
                i = end;
            }
            Some("return") => {
                let end = scan_to_semi(els, j, src);
                out.push(flat_stmt(StmtKind::Return, &els[start..end], src));
                i = end;
            }
            Some("break") => {
                let end = scan_to_semi(els, j, src);
                out.push(flat_stmt(StmtKind::Break, &els[start..end], src));
                i = end;
            }
            Some("continue") => {
                let end = scan_to_semi(els, j, src);
                out.push(flat_stmt(StmtKind::Continue, &els[start..end], src));
                i = end;
            }
            Some("if") => {
                let (stmt, end) = parse_if(els, start, j, src);
                out.push(stmt);
                i = end;
            }
            Some("while") | Some("for") => {
                let kind = if els[j].text(src) == Some("while") {
                    StmtKind::While
                } else {
                    StmtKind::For
                };
                let (header, body_idx) = header_until_brace(els, j + 1, src);
                let (group, body, end) = body_at(els, body_idx, src);
                out.push(Stmt {
                    kind,
                    span: span_of(&els[start..end]),
                    header,
                    body: Some(body),
                    body_group: group,
                    else_part: None,
                    arms: Vec::new(),
                    label,
                    id: None,
                });
                i = end;
            }
            Some("loop") => {
                let (group, body, end) = body_at(els, j + 1, src);
                out.push(Stmt {
                    kind: StmtKind::Loop,
                    span: span_of(&els[start..end]),
                    header: Vec::new(),
                    body: Some(body),
                    body_group: group,
                    else_part: None,
                    arms: Vec::new(),
                    label,
                    id: None,
                });
                i = end;
            }
            Some("match") => {
                let (header, body_idx) = header_until_brace(els, j + 1, src);
                let (arms, end) = arms_at(els, body_idx, src);
                out.push(Stmt {
                    kind: StmtKind::Match,
                    span: span_of(&els[start..end]),
                    header,
                    body: None,
                    body_group: None,
                    else_part: None,
                    arms,
                    label: None,
                    id: None,
                });
                i = end;
            }
            Some("unsafe") if els.get(j + 1).map(|e| e.is_brace()) == Some(true) => {
                // `unsafe { … }` block statement: splice inline.
                if let E::G(b) = &els[j + 1] {
                    out.extend(segment(&inner_elems(b, src), src));
                }
                i = j + 2;
            }
            // Item declarations in statement position, including modifier-
            // prefixed ones (`unsafe fn`, `async fn`, `const fn`, `const X`).
            // A plain `unsafe {}` was spliced above; `async {}` stays an Expr
            // (its body does not execute inline).
            Some(word)
                if is_item_start(word)
                    || word == "const"
                    || (matches!(word, "unsafe" | "async")
                        && els.get(j + 1).and_then(|e| e.text(src)) == Some("fn")) =>
            {
                let end = scan_item(els, j, src);
                out.push(flat_stmt(StmtKind::Item, &els[start..end], src));
                i = end;
            }
            None if els[j].is_brace() => {
                // Bare `{ … }` block statement: splice inline.
                if let E::G(b) = &els[j] {
                    out.extend(segment(&inner_elems(b, src), src));
                }
                i = j + 1;
            }
            _ => {
                let end = scan_to_semi(els, j, src);
                out.push(flat_stmt(StmtKind::Expr, &els[start..end], src));
                i = end;
            }
        }
    }
    out
}

fn flat_stmt<'a>(kind: StmtKind, els: &[E<'a>], src: &'a str) -> Stmt<'a> {
    let _ = src;
    Stmt {
        kind,
        span: span_of(els),
        header: els.iter().map(reborrow).collect(),
        body: None,
        body_group: None,
        else_part: None,
        arms: Vec::new(),
        label: None,
        id: None,
    }
}

pub(crate) fn reborrow<'a>(e: &E<'a>) -> E<'a> {
    match e {
        E::T(t) => E::T(t),
        E::G(n) => E::G(n),
    }
}

/// End index (exclusive) of a flat statement: past the first depth-0 `;`, or
/// the end of the element run (a tail expression).
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

/// End index (exclusive) of an item in statement position: through the first
/// depth-0 `;` or the first depth-0 brace group, whichever comes first
/// (function/impl/mod/trait bodies are brace groups; `use`/`const`/tuple
/// structs end with `;`).
fn scan_item(els: &[E<'_>], from: usize, src: &str) -> usize {
    let mut k = from;
    while k < els.len() {
        if els[k].text(src) == Some(";") {
            return k + 1;
        }
        if els[k].is_brace() {
            // A brace body ends the item (`fn f() {}`); a brace *initializer*
            // (`const X: Foo = Foo { a: 1 };`) is followed by the real `;`.
            if els.get(k + 1).and_then(|e| e.text(src)) == Some(";") {
                return k + 2;
            }
            return k + 1;
        }
        k += 1;
    }
    els.len()
}

/// Collect header elements from `from` until the first depth-0 brace group
/// (the body). Returns the header and the body's index.
fn header_until_brace<'a>(els: &[E<'a>], from: usize, _src: &str) -> (Vec<E<'a>>, usize) {
    let mut header = Vec::new();
    let mut k = from;
    while k < els.len() && !els[k].is_brace() {
        header.push(reborrow(&els[k]));
        k += 1;
    }
    (header, k)
}

/// Segment the brace group at `idx` as a statement block. Returns the group
/// node, the block's statements, and the index just past the group.
fn body_at<'a>(
    els: &[E<'a>],
    idx: usize,
    src: &'a str,
) -> (Option<&'a Node>, Vec<Stmt<'a>>, usize) {
    if let Some(E::G(b)) = els.get(idx) {
        (Some(*b), segment(&inner_elems(b, src), src), idx + 1)
    } else {
        (None, Vec::new(), idx)
    }
}

/// Parse `if <cond> { … } [else if … | else { … }]` starting at `start`
/// (which may include a label prefix); `kw` is the index of the `if` keyword.
fn parse_if<'a>(els: &[E<'a>], start: usize, kw: usize, src: &'a str) -> (Stmt<'a>, usize) {
    let (header, body_idx) = header_until_brace(els, kw + 1, src);
    let (then_group, then_block, mut end) = body_at(els, body_idx, src);
    let mut else_part = None;
    if els.get(end).and_then(|e| e.text(src)) == Some("else") {
        let after = end + 1;
        if els.get(after).and_then(|e| e.text(src)) == Some("if") {
            let (nested, nested_end) = parse_if(els, after, after, src);
            else_part = Some(ElsePart::If(Box::new(nested)));
            end = nested_end;
        } else if els.get(after).map(|e| e.is_brace()) == Some(true) {
            let (group, block, block_end) = body_at(els, after, src);
            else_part = group.map(|g| ElsePart::Block(g, block));
            end = block_end;
        } else {
            // Malformed else; stop at the keyword so progress is guaranteed.
            end = after;
        }
    }
    (
        Stmt {
            kind: StmtKind::If,
            span: span_of(&els[start..end]),
            header,
            body: Some(then_block),
            body_group: then_group,
            else_part,
            arms: Vec::new(),
            label: None,
            id: None,
        },
        end,
    )
}

/// Parse the arm list of the brace group at `idx`. Returns the arms and the
/// index just past the group.
fn arms_at<'a>(els: &[E<'a>], idx: usize, src: &'a str) -> (Vec<Arm<'a>>, usize) {
    let Some(E::G(b)) = els.get(idx) else {
        return (Vec::new(), idx);
    };
    let inner = inner_elems(b, src);
    let mut arms = Vec::new();
    let mut i = 0;
    while i < inner.len() {
        // Pattern: everything until the depth-0 `=>`.
        let pat_start = i;
        while i < inner.len() && inner[i].text(src) != Some("=>") {
            i += 1;
        }
        if i >= inner.len() {
            break; // no arrow: tolerate (trailing tokens are not an arm)
        }
        let pattern: Vec<E<'a>> = inner[pat_start..i].iter().map(reborrow).collect();
        i += 1; // past `=>`
        if pattern.is_empty() && i > inner.len() {
            break;
        }
        // Body: a brace group, or a flat expression up to the depth-0 `,`.
        if inner.get(i).map(|e| e.is_brace()) == Some(true) {
            let (_, block, next) = body_at(&inner, i, src);
            let arm_span = span_of(&inner[pat_start..next]);
            i = next;
            if inner.get(i).and_then(|e| e.text(src)) == Some(",") {
                i += 1;
            }
            arms.push(Arm {
                span: arm_span,
                pattern,
                block: Some(block),
                expr: Vec::new(),
                id: None,
            });
        } else {
            let body_start = i;
            while i < inner.len() && inner[i].text(src) != Some(",") {
                i += 1;
            }
            let expr: Vec<E<'a>> = inner[body_start..i].iter().map(reborrow).collect();
            let arm_span = span_of(&inner[pat_start..i.max(pat_start + 1).min(inner.len())]);
            if inner.get(i).and_then(|e| e.text(src)) == Some(",") {
                i += 1;
            }
            arms.push(Arm {
                span: arm_span,
                pattern,
                block: None,
                expr,
                id: None,
            });
        }
    }
    (arms, idx + 1)
}

pub(crate) fn span_of(els: &[E<'_>]) -> ByteSpan {
    let mut it = els.iter().map(E::span);
    match it.next() {
        Some(first) => it.fold(first, ByteSpan::merge),
        None => ByteSpan::empty_at(0),
    }
}

// ---------------------------------------------------------------------------
// Emission: statement nodes + FLOWS_TO control flow
// ---------------------------------------------------------------------------

/// A dangling flow source: a statement whose execution continues at whatever
/// comes next, together with the semantics the eventual edge should carry.
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

/// Innermost-first stack entry for `break`/`continue` targeting. `label` is the
/// loop's `'name` label when present, so labeled `break`/`continue` can target
/// an outer loop instead of the innermost one.
struct LoopCtx {
    header_id: String,
    pub(crate) label: Option<String>,
    breaks: Vec<Exit>,
}

/// The `'label` a `break`/`continue` statement targets: the lifetime token
/// directly after the keyword (`els[0]` is the keyword itself).
fn jump_label<'a>(els: &[E<'a>], src: &'a str) -> Option<&'a str> {
    match els.get(1) {
        Some(E::T(t)) if t.kind == tk::LIFETIME => Some(t.span.text(src)),
        _ => None,
    }
}

/// The loop a `break` targets: the labeled loop when a label is given (`None`
/// if no loop carries it — e.g. a label on a spliced bare block, which the CPG
/// does not model; absence over fabrication), else the innermost.
fn break_target<'l>(loops: &'l mut [LoopCtx], label: Option<&str>) -> Option<&'l mut LoopCtx> {
    match label {
        Some(l) => loops
            .iter_mut()
            .rev()
            .find(|c| c.label.as_deref() == Some(l)),
        None => loops.last_mut(),
    }
}

/// The loop a `continue` targets (same rule as [`break_target`], read-only).
fn continue_target<'l>(loops: &'l [LoopCtx], label: Option<&str>) -> Option<&'l LoopCtx> {
    match label {
        Some(l) => loops.iter().rev().find(|c| c.label.as_deref() == Some(l)),
        None => loops.last(),
    }
}

/// True when the element run contains a depth-0 `?` try operator: a `?` token
/// counts unless its next significant element is a non-keyword identifier —
/// that shape is the `?Sized` relaxed bound (`dyn Write + ?Sized`), the only
/// other depth-0 use of `?` in statement position (angle brackets are not
/// groups, so bound tokens sit at depth 0 in a `let` type ascription).
/// Nested groups are deliberately NOT scanned: a `?` inside a group may belong
/// to a closure body, which exits the closure, not the function — absence over
/// fabrication (ADR-0003).
pub(crate) fn has_try_operator(els: &[E<'_>], src: &str) -> bool {
    for (k, e) in els.iter().enumerate() {
        if e.text(src) != Some("?") {
            continue;
        }
        let next_is_bound_ident = matches!(
            els.get(k + 1),
            Some(E::T(t))
                if (t.kind == tk::IDENT || t.kind == tk::RAW_IDENT)
                    && !is_keyword(t.span.text(src))
        );
        if !next_is_bound_ident {
            return true;
        }
    }
    false
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
    /// Create the node for one statement and record its id.
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

    /// Emit one FLOWS_TO edge with its auditable semantics.
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

    /// Connect every pending exit to `to`.
    fn join(&mut self, incoming: Vec<Exit>, to: &str) {
        for e in incoming {
            self.flow(&e.from, to, e.role, e.branch);
        }
    }

    /// Emit nodes + flow for a statement block. `incoming` are the dangling
    /// sources that reach the block's first statement; the return value is the
    /// block's own dangling exits (passthrough when the block is empty —
    /// exactly what an empty branch means).
    fn emit_block(
        &mut self,
        stmts: &mut [Stmt<'a>],
        incoming: Vec<Exit>,
        loops: &mut Vec<LoopCtx>,
    ) -> Vec<Exit> {
        let mut pending = incoming;
        for s in stmts.iter_mut() {
            pending = self.emit_stmt(s, pending, loops);
        }
        pending
    }

    /// Emit one statement: its node, the edges from `incoming`, and its
    /// sub-structure. Returns the dangling exits that continue past it.
    /// A diverging statement (`return`, `break`, `continue`, a `loop` with no
    /// `break`) returns no exits — absence of flow is information.
    fn emit_stmt(
        &mut self,
        s: &mut Stmt<'a>,
        incoming: Vec<Exit>,
        loops: &mut Vec<LoopCtx>,
    ) -> Vec<Exit> {
        let name = self.stmt_name(s);
        let id = self.emit_node(s.kind.label(), s.span, name);
        s.id = Some(id.clone());
        self.join(incoming, &id);

        // `?`-operator: a depth-0 try in the statement's own token run is an
        // implicit early exit — one additional FLOWS_TO → exit, distinguished
        // by role "try-exit". The ordinary exits below are the Ok path. Items
        // do not execute (`?Sized` bounds in a nested `fn` signature are not
        // control flow of this function).
        if s.kind != StmtKind::Item && has_try_operator(&s.header, self.src) {
            let exit = self.exit_id.to_string();
            self.flow(&id, &exit, "try-exit", None);
        }

        match s.kind {
            StmtKind::Let | StmtKind::Expr | StmtKind::Item => vec![Exit::seq(id)],
            StmtKind::Return => {
                let exit = self.exit_id.to_string();
                self.flow(&id, &exit, "return", None);
                Vec::new()
            }
            StmtKind::Break => {
                let label = jump_label(&s.header, self.src);
                if let Some(l) = break_target(loops, label) {
                    l.breaks.push(Exit {
                        from: id,
                        role: "break",
                        branch: None,
                    });
                }
                // `break` outside a loop is not valid Rust, and a label with no
                // matching loop (a labeled bare block, which is spliced) has no
                // modeled target; emit nothing either way.
                Vec::new()
            }
            StmtKind::Continue => {
                let label = jump_label(&s.header, self.src);
                if let Some(l) = continue_target(loops, label) {
                    let header = l.header_id.clone();
                    self.flow(&id, &header, "continue", None);
                }
                Vec::new()
            }
            StmtKind::If => {
                // True path.
                let then_in = vec![Exit {
                    from: id.clone(),
                    role: "branch",
                    branch: Some("then"),
                }];
                let mut exits = match s.body.as_mut() {
                    Some(b) => self.emit_block(b, then_in, loops),
                    None => then_in,
                };
                // False path.
                let else_in = vec![Exit {
                    from: id.clone(),
                    role: "branch",
                    branch: Some("else"),
                }];
                match s.else_part.as_mut() {
                    Some(ElsePart::Block(_, b)) => {
                        exits.extend(self.emit_block(b, else_in, loops));
                    }
                    Some(ElsePart::If(nested)) => {
                        exits.extend(self.emit_stmt(nested, else_in, loops));
                    }
                    // No else: the false path falls through to the merge point.
                    None => exits.extend(else_in),
                }
                exits
            }
            StmtKind::While | StmtKind::For | StmtKind::Loop => {
                loops.push(LoopCtx {
                    header_id: id.clone(),
                    label: s.label.clone(),
                    breaks: Vec::new(),
                });
                let body_in = vec![Exit {
                    from: id.clone(),
                    role: "branch",
                    branch: Some("body"),
                }];
                let body_exits = match s.body.as_mut() {
                    Some(b) => self.emit_block(b, body_in, loops),
                    None => body_in,
                };
                // The back edge: body completion re-tests the header.
                for e in body_exits {
                    self.flow(&e.from, &id, "loop-back", e.branch);
                }
                let ctx = loops.pop().expect("loop ctx pushed above");
                let mut exits = ctx.breaks;
                // `loop` exits only via break; while/for also exit at the header.
                if s.kind != StmtKind::Loop {
                    exits.push(Exit {
                        from: id,
                        role: "loop-exit",
                        branch: None,
                    });
                }
                exits
            }
            StmtKind::Match => {
                let mut exits = Vec::new();
                let has_arms = !s.arms.is_empty();
                for arm in s.arms.iter_mut() {
                    let arm_name = format!("{} =>", collapse(&arm_pattern_text(arm, self.src)));
                    let arm_id = self.emit_node("arm", arm.span, truncate(arm_name));
                    arm.id = Some(arm_id.clone());
                    self.flow(&id, &arm_id, "branch", Some("arm"));
                    if let Some(block) = arm.block.as_mut() {
                        exits.extend(self.emit_block(block, vec![Exit::seq(arm_id)], loops));
                    } else {
                        exits.extend(self.arm_expr_exits(arm_id, &arm.expr, loops));
                    }
                }
                if !has_arms {
                    exits.push(Exit::seq(id));
                }
                exits
            }
        }
    }

    /// Exits of a flat (non-block) match-arm body. Diverging bodies —
    /// `return …`, `break [label]`, `continue [label]` — are wired like their
    /// statement forms, and a depth-0 `?` adds the same try-exit edge a
    /// statement would get.
    fn arm_expr_exits(
        &mut self,
        arm_id: String,
        expr: &[E<'a>],
        loops: &mut [LoopCtx],
    ) -> Vec<Exit> {
        if has_try_operator(expr, self.src) {
            let exit = self.exit_id.to_string();
            self.flow(&arm_id, &exit, "try-exit", None);
        }
        match expr.first().and_then(|e| e.text(self.src)) {
            Some("return") => {
                let exit = self.exit_id.to_string();
                self.flow(&arm_id, &exit, "return", None);
                Vec::new()
            }
            Some("break") => {
                let label = jump_label(expr, self.src);
                if let Some(l) = break_target(loops, label) {
                    l.breaks.push(Exit {
                        from: arm_id,
                        role: "break",
                        branch: None,
                    });
                }
                Vec::new()
            }
            Some("continue") => {
                let label = jump_label(expr, self.src);
                if let Some(l) = continue_target(loops, label) {
                    let header = l.header_id.clone();
                    self.flow(&arm_id, &header, "continue", None);
                }
                Vec::new()
            }
            _ => vec![Exit::seq(arm_id)],
        }
    }

    /// Deterministic human-readable name: header text for structured kinds,
    /// full text otherwise; whitespace collapsed, truncated.
    fn stmt_name(&self, s: &Stmt<'a>) -> String {
        let text = match s.kind {
            StmtKind::If => format!("if {}", collapse(&els_text(&s.header, self.src))),
            StmtKind::While => format!("while {}", collapse(&els_text(&s.header, self.src))),
            StmtKind::For => format!("for {}", collapse(&els_text(&s.header, self.src))),
            StmtKind::Match => format!("match {}", collapse(&els_text(&s.header, self.src))),
            StmtKind::Loop => "loop".to_string(),
            _ => collapse(s.span.text(self.src)),
        };
        truncate(text)
    }
}

fn arm_pattern_text<'a>(arm: &Arm<'a>, src: &'a str) -> String {
    els_text(&arm.pattern, src)
}

/// Source text of an element run (from first to last span, inclusive).
fn els_text<'a>(els: &[E<'a>], src: &'a str) -> String {
    if els.is_empty() {
        return String::new();
    }
    span_of(els).text(src).to_string()
}

/// Collapse all whitespace runs to single spaces.
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

/// Truncate to [`NAME_LIMIT`] characters on a char boundary.
fn truncate(text: String) -> String {
    if text.chars().count() <= NAME_LIMIT {
        return text;
    }
    text.chars().take(NAME_LIMIT).collect()
}

// ---------------------------------------------------------------------------
// DATA_DEP: conservative intra-function def-use chains (ADR-0003)
// ---------------------------------------------------------------------------
//
// A second walk over the same statement tree (ids were assigned by the flow
// pass) threads a definition environment: variable name → the set of
// definition sites that MAY reach the current point. Branch bodies run on
// cloned environments that are unioned at the merge, so a definition inside a
// branch joins the reaching set instead of replacing it; a straight-line
// (re)definition replaces it. Loop bodies are walked twice so a use textually
// before a def still sees the previous iteration's def through the back edge
// (the second walk only adds edges — the graph API dedups). `let`-introduced
// names are restored at block end (lexical scope); plain assignments to outer
// names survive. No aliasing claims: `x.f = v` and `*p = v` are reads of
// `x`/`p`, never defs or kills.

/// Definition sites that may reach a point: `(node id, def kind)`.
type Defs = Vec<(String, &'static str)>;
/// Variable name → reaching definition sites.
type Env = std::collections::BTreeMap<String, Defs>;
/// Names (re)bound in the current block, with the entry they shadowed
/// (`None` = the name was previously unbound). Restored at block end.
type Saved = std::collections::BTreeMap<String, Option<Defs>>;

/// A pre-applied, block-scoped definition: `(name, def site, def kind)` —
/// `if let` / `while let` / `for` / match-arm pattern bindings.
type PreDef = (String, String, &'static str);

struct DataFlow<'a, 'g> {
    g: &'g mut Graph,
    src: &'a str,
}

impl<'a, 'g> DataFlow<'a, 'g> {
    /// Walk a block: apply `predefs` (scoped to this block), process each
    /// statement, then restore every name this block (re)bound.
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
            None => return, // never emitted (defensive)
        };
        match s.kind {
            StmtKind::Let => {
                // `let PATTERN(: TYPE)? (= RHS)? ;` — reads first (self-
                // reference sees the old defs), then the binding replaces.
                let eq = top_index(&s.header, "=", self.src);
                if let Some(eq) = eq {
                    self.emit_reads(&id, &s.header[eq + 1..], env);
                }
                let cut = top_index(&s.header, ":", self.src)
                    .into_iter()
                    .chain(eq)
                    .min()
                    .unwrap_or(s.header.len());
                for name in pattern_defs(&s.header[1.min(cut)..cut], self.src) {
                    saved
                        .entry(name.clone())
                        .or_insert_with(|| env.get(&name).cloned());
                    env.insert(name, vec![(id.clone(), "let")]);
                }
            }
            StmtKind::Expr => {
                // Assignment to a bare name is a def; anything else is reads.
                let (target, compound) = assign_target(&s.header, self.src);
                match target {
                    Some(name) => {
                        if compound {
                            // `x += …` reads the old value of x too.
                            self.emit_reads(&id, &s.header, env);
                        } else {
                            self.emit_reads(&id, &s.header[2..], env);
                        }
                        env.insert(name, vec![(id.clone(), "assign")]);
                    }
                    None => self.emit_reads(&id, &s.header, env),
                }
            }
            StmtKind::Return | StmtKind::Break | StmtKind::Continue => {
                self.emit_reads(&id, &s.header, env);
            }
            StmtKind::Item => {} // declarations do not execute
            StmtKind::If => {
                let (predefs, read_els) = let_header_split(&s.header, &id, self.src);
                self.emit_reads(&id, &read_els, env);
                let mut then_env = env.clone();
                if let Some(b) = &s.body {
                    self.data_block(b, &mut then_env, &predefs);
                }
                match &s.else_part {
                    Some(ElsePart::Block(_, b)) => {
                        let mut else_env = env.clone();
                        self.data_block(b, &mut else_env, &[]);
                        *env = union_env(then_env, &else_env);
                    }
                    Some(ElsePart::If(nested)) => {
                        let mut else_env = env.clone();
                        // The nested if is its own statement (with its own
                        // block scoping); a fresh Saved keeps this honest.
                        let mut nested_saved = Saved::new();
                        self.data_stmt(nested, &mut else_env, &mut nested_saved);
                        *env = union_env(then_env, &else_env);
                    }
                    // No else: the pre-state survives the false path.
                    None => *env = union_env(then_env, env),
                }
            }
            StmtKind::While | StmtKind::Loop => {
                let (predefs, read_els) = let_header_split(&s.header, &id, self.src);
                self.emit_reads(&id, &read_els, env);
                self.loop_body(s, env, &predefs);
            }
            StmtKind::For => {
                // `for PATTERN in EXPR { … }`: EXPR reads; PATTERN binds,
                // scoped to the body.
                let in_idx = top_index(&s.header, "in", self.src);
                let (pat_els, read_els) = match in_idx {
                    Some(k) => (&s.header[..k], &s.header[k + 1..]),
                    None => (&s.header[..0], &s.header[..]),
                };
                self.emit_reads(&id, read_els, env);
                let predefs: Vec<PreDef> = pattern_defs(pat_els, self.src)
                    .into_iter()
                    .map(|n| (n, id.clone(), "loop"))
                    .collect();
                self.loop_body(s, env, &predefs);
            }
            StmtKind::Match => {
                self.emit_reads(&id, &s.header, env);
                if s.arms.is_empty() {
                    return;
                }
                let mut merged: Option<Env> = None;
                for arm in &s.arms {
                    let arm_id = match &arm.id {
                        Some(a) => a.clone(),
                        None => continue,
                    };
                    // `PATTERN (if GUARD)? =>`: bindings def at the arm node,
                    // scoped to the arm; the guard reads (bindings visible).
                    let guard_idx = top_index(&arm.pattern, "if", self.src);
                    let pat_els = match guard_idx {
                        Some(k) => &arm.pattern[..k],
                        None => &arm.pattern[..],
                    };
                    let predefs: Vec<PreDef> = pattern_defs(pat_els, self.src)
                        .into_iter()
                        .map(|n| (n, arm_id.clone(), "pattern"))
                        .collect();
                    let mut arm_env = env.clone();
                    // Apply bindings for the guard + body region.
                    let mut arm_saved = Saved::new();
                    for (name, site, kind) in &predefs {
                        arm_saved
                            .entry(name.clone())
                            .or_insert_with(|| arm_env.get(name).cloned());
                        arm_env.insert(name.clone(), vec![(site.clone(), kind)]);
                    }
                    if let Some(k) = guard_idx {
                        self.emit_reads(&arm_id, &arm.pattern[k + 1..], &arm_env);
                    }
                    match &arm.block {
                        Some(b) => self.data_block(b, &mut arm_env, &[]),
                        None => self.emit_reads(&arm_id, &arm.expr, &arm_env),
                    }
                    // Arm bindings go out of scope at the arm's end.
                    for (name, old) in arm_saved {
                        match old {
                            Some(defs) => {
                                arm_env.insert(name, defs);
                            }
                            None => {
                                arm_env.remove(&name);
                            }
                        }
                    }
                    merged = Some(match merged {
                        Some(m) => union_env(m, &arm_env),
                        None => arm_env,
                    });
                }
                if let Some(m) = merged {
                    *env = m; // match is exhaustive: only arm paths continue
                }
            }
        }
    }

    /// Process a loop body twice: pass 1 discovers body defs; the merge makes
    /// them reach the header; pass 2 re-walks with the merged environment so
    /// uses see previous-iteration defs through the back edge. Pass 2 only
    /// adds edges (the graph dedups); its env changes are discarded.
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
    /// an environment-known variable in `els`. Consumer → producer, exactly as
    /// the ontology defines the edge.
    fn emit_reads(&mut self, stmt_id: &str, els: &[E<'a>], env: &Env) {
        let toks = flat_tokens(els);
        for (k, t) in toks.iter().enumerate() {
            if t.kind != tk::IDENT && t.kind != tk::RAW_IDENT {
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
            // Path segments, field/method names after `.`, struct-literal
            // field names / ascriptions before `:`, and macro names are not
            // variable reads.
            if prev == Some("::")
                || next == Some("::")
                || prev == Some(".")
                || next == Some(":")
                || next == Some("!")
            {
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

/// Index of the first depth-0 element whose text is `what`.
pub(crate) fn top_index(els: &[E<'_>], what: &str, src: &str) -> Option<usize> {
    els.iter().position(|e| e.text(src) == Some(what))
}

/// For `if let` / `while let` headers: split into block-scoped pattern
/// bindings (def site = the statement itself) and the elements to read
/// (the scrutinee after `=`; plain headers read everything).
fn let_header_split<'a>(
    header: &[E<'a>],
    stmt_id: &str,
    src: &'a str,
) -> (Vec<PreDef>, Vec<E<'a>>) {
    if header.first().and_then(|e| e.text(src)) != Some("let") {
        return (Vec::new(), header.iter().map(reborrow).collect());
    }
    let eq = top_index(header, "=", src).unwrap_or(header.len());
    let predefs = pattern_defs(&header[1.min(eq)..eq], src)
        .into_iter()
        .map(|n| (n, stmt_id.to_string(), "pattern"))
        .collect();
    let reads = header
        .get(eq + 1..)
        .unwrap_or(&[])
        .iter()
        .map(reborrow)
        .collect();
    (predefs, reads)
}

/// `(target, compound)` when the statement is an assignment to a bare name:
/// `x = …` / `x op= …`. Projections (`x.f = …`, `x[i] = …`) and deref stores
/// (`*p = …`) return `None` — mutations through a place are reads, not defs
/// (no aliasing claims).
pub(crate) fn assign_target(els: &[E<'_>], src: &str) -> (Option<String>, bool) {
    let first = match els.first() {
        Some(E::T(t)) if t.kind == tk::IDENT || t.kind == tk::RAW_IDENT => t.span.text(src),
        _ => return (None, false),
    };
    if is_keyword(first) {
        return (None, false);
    }
    match els.get(1).and_then(|e| e.text(src)) {
        Some("=") => (Some(first.to_string()), false),
        Some("+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | "<<=" | ">>=") => {
            (Some(first.to_string()), true)
        }
        _ => (None, false),
    }
}

/// Binding names in a pattern region. Conservative by construction:
/// - keywords (`mut`, `ref`, `box`, `self`, …) and `_` are never bindings;
/// - path segments (adjacent to `::`) are types/variants, not bindings;
/// - struct-pattern field names (followed by `:`) name fields, not bindings;
/// - idents directly followed by an opening group are constructors;
/// - uppercase-initial idents are types/variants/consts by Rust convention
///   (the compiler lints otherwise), never bindings.
pub(crate) fn pattern_defs(els: &[E<'_>], src: &str) -> Vec<String> {
    let toks = flat_tokens(els);
    let mut out = Vec::new();
    for (k, t) in toks.iter().enumerate() {
        if t.kind != tk::IDENT && t.kind != tk::RAW_IDENT {
            continue;
        }
        let text = t.span.text(src);
        if is_keyword(text) || text == "_" {
            continue;
        }
        if text.chars().next().is_some_and(|c| c.is_uppercase()) {
            continue;
        }
        let prev = if k > 0 {
            Some(toks[k - 1].span.text(src))
        } else {
            None
        };
        let next = toks.get(k + 1).map(|n| n.span.text(src));
        if prev == Some("::") || next == Some("::") || next == Some(":") {
            continue;
        }
        if matches!(next, Some("(") | Some("{") | Some("[") | Some("!")) {
            continue; // constructor or macro, not a binding
        }
        if !out.contains(&text.to_string()) {
            out.push(text.to_string());
        }
    }
    out
}

/// Every non-trivia token under `els`, in source order (groups flattened).
pub(crate) fn flat_tokens<'a>(els: &[E<'a>]) -> Vec<&'a Token> {
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

/// Parameter names bound by a function signature: the contents of the first
/// depth-0 parenthesis group outside any generic-parameter angle region.
fn param_names(sig: &Node, src: &str) -> Vec<String> {
    let els = elems(sig);
    let mut angle: i32 = 0;
    let mut params: Option<&Node> = None;
    for e in &els {
        match e {
            E::T(t) => {
                let text = t.span.text(src);
                if text == "->" {
                    break; // return type follows; params were before it
                }
                for ch in text.chars() {
                    if ch == '<' {
                        angle += 1;
                    } else if ch == '>' {
                        angle -= 1;
                    }
                }
                if angle < 0 {
                    angle = 0;
                }
            }
            E::G(n) => {
                if angle == 0 && n.kind == cst::PAREN {
                    params = Some(n);
                    break;
                }
            }
        }
    }
    let Some(p) = params else {
        return Vec::new();
    };
    let inner = {
        let mut v = elems(p);
        if v.first().and_then(|e| e.text(src)) == Some("(") {
            v.remove(0);
        }
        if v.last().and_then(|e| e.text(src)) == Some(")") {
            v.pop();
        }
        v
    };
    // Split at depth-0 commas; each parameter's pattern is what precedes `:`.
    let mut out = Vec::new();
    let mut start = 0;
    let mut k = 0;
    while k <= inner.len() {
        let at_comma = k < inner.len() && inner[k].text(src) == Some(",");
        if at_comma || k == inner.len() {
            let part = &inner[start..k];
            let colon = top_index(part, ":", src).unwrap_or(part.len());
            for name in pattern_defs(&part[..colon], src) {
                if !out.contains(&name) {
                    out.push(name);
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
    use crate::lang::rust::parser::parse;

    /// Parse `src` as a file, find the first function's block, and segment it.
    fn stmts_of(src: &str) -> usize {
        let tree = parse("t.rs", src);
        let f = tree
            .root
            .walk()
            .find(|n| n.kind == cst::FUNCTION)
            .expect("function");
        let block = f.child(cst::BLOCK).expect("block");
        let els = inner_elems(block, src);
        segment(&els, &tree.source).len()
    }

    #[test]
    fn segments_flat_statements() {
        assert_eq!(stmts_of("fn f() { let a = 1; let b = 2; a + b }"), 3);
    }

    #[test]
    fn semicolons_inside_groups_are_invisible() {
        assert_eq!(stmts_of("fn f() { g(|| { x(); y(); }); h(); }"), 2);
    }

    #[test]
    fn if_else_is_one_statement() {
        assert_eq!(
            stmts_of("fn f(x: i32) { if x > 0 { a(); } else { b(); } done(); }"),
            2
        );
    }

    #[test]
    fn bare_and_unsafe_blocks_are_spliced() {
        assert_eq!(stmts_of("fn f() { { a(); b(); } unsafe { c(); } }"), 3);
    }

    #[test]
    fn nested_items_do_not_swallow_statements() {
        // unsafe/async/const fn items and a const with a brace initializer
        // must each be one Item statement, not an Expr that eats the rest.
        assert_eq!(
            stmts_of("fn f() { unsafe fn g() {} a(); }"),
            2,
            "unsafe fn item + following expr"
        );
        assert_eq!(
            stmts_of("fn f() { async fn g() {} a(); }"),
            2,
            "async fn item + following expr"
        );
        assert_eq!(
            stmts_of("fn f() { const N: usize = 3; a(); }"),
            2,
            "const item + following expr"
        );
        assert_eq!(
            stmts_of("fn f() { const P: Point = Point { x: 1 }; a(); }"),
            2,
            "brace-initialized const item + following expr"
        );
    }

    // --- emission through the real lowering ---------------------------------

    fn base_and_cpg(src: &str) -> (Graph, Graph) {
        use crate::lang::frontend::SourceFile;
        let tree = parse("lib.rs", src);
        let file = SourceFile {
            rel_path: "lib.rs".to_string(),
            module_path: vec![],
            source: &tree.source,
            root: &tree.root,
        };
        let base = crate::ir::lower::lower("demo", std::slice::from_ref(&file), &[]);
        let cpg = crate::ir::lower::lower_with_cpg("demo", std::slice::from_ref(&file), &[]);
        (base, cpg)
    }

    #[test]
    fn statement_nodes_attach_to_the_function() {
        let (_, g) = base_and_cpg("fn f() { let a = 1; let b = 2; a + b }");
        // 3 statements + the virtual exit node.
        assert_eq!(g.count_nodes_of(ont::STATEMENT), 4);
        assert!(g.has_node("stmt::crate::f#1::exit"));
        assert!(g.has_node("stmt::crate::f#1::0"));
        // Every statement is contained by the function.
        let fn_id = "fn::crate::f#1";
        let contained = g
            .edges()
            .filter(|e| e.kind == edge::CONTAINS && e.from == fn_id && e.to.starts_with("stmt::"))
            .count();
        assert_eq!(contained, 4);
    }

    // --- control flow: exact-edge assertions per construct ------------------

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

    #[test]
    fn sequential_flow_entry_to_exit() {
        // fn(id=f#1) -entry-> s0 -seq-> s1 -seq-> exit
        let got = cpg_flows("fn f() { a(); b(); }");
        assert_eq!(got, vec!["0 -seq-> 1", "1 -seq-> exit", "f#1 -entry-> 0",]);
    }

    #[test]
    fn if_else_branches_and_merges() {
        // s0=let, s1=if, s2=then-expr, s3=else-expr, s4=after
        let got = cpg_flows("fn f(x: i32) { let y = x; if y > 0 { a(); } else { b(); } c(); }");
        assert_eq!(
            got,
            vec![
                "0 -seq-> 1",
                "1 -branch/else-> 3",
                "1 -branch/then-> 2",
                "2 -seq-> 4",
                "3 -seq-> 4",
                "4 -seq-> exit",
                "f#1 -entry-> 0",
            ]
        );
    }

    #[test]
    fn if_without_else_falls_through() {
        // s0=if, s1=then-expr, s2=after: the false path is an explicit edge.
        let got = cpg_flows("fn f(x: bool) { if x { a(); } b(); }");
        assert_eq!(
            got,
            vec![
                "0 -branch/else-> 2",
                "0 -branch/then-> 1",
                "1 -seq-> 2",
                "2 -seq-> exit",
                "f#1 -entry-> 0",
            ]
        );
    }

    #[test]
    fn while_loop_has_back_edge_and_exit() {
        // s0=while, s1=body-expr, s2=after
        let got = cpg_flows("fn f(x: bool) { while x { a(); } b(); }");
        assert_eq!(
            got,
            vec![
                "0 -branch/body-> 1",
                "0 -loop-exit-> 2",
                "1 -loop-back-> 0",
                "2 -seq-> exit",
                "f#1 -entry-> 0",
            ]
        );
    }

    #[test]
    fn loop_exits_only_via_break() {
        // s0=loop, s1=if, s2=break, s3=body-tail, s4=after
        let got = cpg_flows("fn f(x: bool) { loop { if x { break; } a(); } b(); }");
        assert_eq!(
            got,
            vec![
                "0 -branch/body-> 1",
                "1 -branch/else-> 3",
                "1 -branch/then-> 2",
                "2 -break-> 4",
                "3 -loop-back-> 0",
                "4 -seq-> exit",
                "f#1 -entry-> 0",
            ]
        );
    }

    #[test]
    fn continue_is_a_back_edge() {
        // s0=while, s1=if, s2=continue, s3=tail
        let got = cpg_flows("fn f(x: bool) { while x { if x { continue; } a(); } }");
        assert_eq!(
            got,
            vec![
                "0 -branch/body-> 1",
                "0 -loop-exit-> exit",
                "1 -branch/else-> 3",
                "1 -branch/then-> 2",
                "2 -continue-> 0",
                "3 -loop-back-> 0",
                "f#1 -entry-> 0",
            ]
        );
        // The back edges are marked.
        let (_, g) = base_and_cpg("fn f(x: bool) { while x { if x { continue; } a(); } }");
        let marked = g
            .edges()
            .filter(|e| e.kind == edge::FLOWS_TO)
            .filter(|e| e.props.get("back_edge") == Some(&Json::Bool(true)))
            .count();
        assert_eq!(marked, 2, "continue + loop-back are both back edges");
    }

    #[test]
    fn match_arms_branch_and_merge() {
        // s0=let, s1=match, s2=arm1, s3=arm1-body, s4=arm2, s5=after
        let got = cpg_flows(
            "fn f(x: Option<i32>) { let y = x; match y { Some(v) => { a(); } None => b(), } c(); }",
        );
        assert_eq!(
            got,
            vec![
                "0 -seq-> 1",
                "1 -branch/arm-> 2",
                "1 -branch/arm-> 4",
                "2 -seq-> 3",
                "3 -seq-> 5",
                "4 -seq-> 5",
                "5 -seq-> exit",
                "f#1 -entry-> 0",
            ]
        );
    }

    #[test]
    fn early_return_diverges_to_exit() {
        // s0=if, s1=return, s2=after — no seq edge out of the return.
        let got = cpg_flows("fn f(x: bool) -> i32 { if x { return 1; } 2 }");
        assert_eq!(
            got,
            vec![
                "0 -branch/else-> 2",
                "0 -branch/then-> 1",
                "1 -return-> exit",
                "2 -seq-> exit",
                "f#1 -entry-> 0",
            ]
        );
    }

    #[test]
    fn match_arm_with_return_expr_diverges() {
        // s0=match, s1=arm1(return), s2=arm2, s3=after
        let got = cpg_flows(
            "fn f(x: Option<i32>) -> i32 { match x { None => return 0, Some(v) => a(), } b(); 1 }",
        );
        assert_eq!(
            got,
            vec![
                "0 -branch/arm-> 1",
                "0 -branch/arm-> 2",
                "1 -return-> exit",
                "2 -seq-> 3",
                "3 -seq-> 4",
                "4 -seq-> exit",
                "f#1 -entry-> 0",
            ]
        );
    }

    // --- `?`-operator early exit: exact-edge assertions ----------------------

    #[test]
    fn try_operator_adds_an_early_exit_edge() {
        // s0: let a = h()?; — Ok path continues to s1, Err path exits.
        let got = cpg_flows("fn f() -> Result<(), E> { let a = h()?; g(a); }");
        assert_eq!(
            got,
            vec![
                "0 -seq-> 1",
                "0 -try-exit-> exit",
                "1 -seq-> exit",
                "f#1 -entry-> 0",
            ]
        );
    }

    #[test]
    fn try_in_a_condition_header_adds_the_exit_edge() {
        // s0: if h()? — the header's `?` may exit before the branch is taken.
        let got = cpg_flows("fn f() -> Result<(), E> { if h()? { a(); } b(); }");
        assert_eq!(
            got,
            vec![
                "0 -branch/else-> 2",
                "0 -branch/then-> 1",
                "0 -try-exit-> exit",
                "1 -seq-> 2",
                "2 -seq-> exit",
                "f#1 -entry-> 0",
            ]
        );
    }

    #[test]
    fn try_in_a_flat_match_arm_adds_the_exit_edge() {
        // s0=match, s1=arm(h()?), s2=after — the arm body may exit early.
        let got =
            cpg_flows("fn f(x: Option<u8>) -> Result<(), E> { match x { Some(_) => h()?, None => (), } t(); }");
        assert_eq!(
            got,
            vec![
                "0 -branch/arm-> 1",
                "0 -branch/arm-> 2",
                "1 -seq-> 3",
                "1 -try-exit-> exit",
                "2 -seq-> 3",
                "3 -seq-> exit",
                "f#1 -entry-> 0",
            ]
        );
    }

    #[test]
    fn sized_bound_question_mark_is_not_a_try_exit() {
        // `?Sized` is a relaxed bound, not control flow (angle brackets are not
        // groups, so the `?` sits at depth 0 of the let header).
        let got = cpg_flows("fn f() { let x: Box<dyn W + ?Sized> = mk(); use_it(x); }");
        assert_eq!(got, vec!["0 -seq-> 1", "1 -seq-> exit", "f#1 -entry-> 0"]);
    }

    #[test]
    fn try_inside_a_nested_group_is_not_claimed() {
        // A `?` inside a group may belong to a closure body (which exits the
        // closure, not the function): pinned as NOT claimed (ADR-0003).
        let got = cpg_flows("fn f() { g(|| h()?); t(); }");
        assert_eq!(got, vec!["0 -seq-> 1", "1 -seq-> exit", "f#1 -entry-> 0"]);
    }

    // --- labeled break/continue: exact-edge assertions ------------------------

    #[test]
    fn labeled_break_targets_the_outer_loop() {
        // s0='outer: while a, s1=inner while b, s2=break 'outer, s3=after.
        let got = cpg_flows(
            "fn f(a: bool, b: bool) { 'outer: while a { while b { break 'outer; } } t(); }",
        );
        assert_eq!(
            got,
            vec![
                "0 -branch/body-> 1",
                "0 -loop-exit-> 3",
                "1 -branch/body-> 2",
                "1 -loop-back-> 0",
                "2 -break-> 3",
                "3 -seq-> exit",
                "f#1 -entry-> 0",
            ]
        );
    }

    #[test]
    fn labeled_continue_targets_the_outer_loop_header() {
        // s0='outer: while a, s1=inner while b, s2=continue 'outer.
        let got = cpg_flows(
            "fn f(a: bool, b: bool) { 'outer: while a { while b { continue 'outer; } } }",
        );
        assert_eq!(
            got,
            vec![
                "0 -branch/body-> 1",
                "0 -loop-exit-> exit",
                "1 -branch/body-> 2",
                "1 -loop-back-> 0",
                "2 -continue-> 0",
                "f#1 -entry-> 0",
            ]
        );
    }

    #[test]
    fn unlabeled_break_still_targets_the_innermost_loop() {
        // s0='outer: while a, s1=inner while b, s2=break (inner), s3=after.
        // The inner break-exit becomes the outer loop's back edge.
        let got =
            cpg_flows("fn f(a: bool, b: bool) { 'outer: while a { while b { break; } } t(); }");
        assert_eq!(
            got,
            vec![
                "0 -branch/body-> 1",
                "0 -loop-exit-> 3",
                "1 -branch/body-> 2",
                "1 -loop-back-> 0",
                "2 -loop-back-> 0",
                "3 -seq-> exit",
                "f#1 -entry-> 0",
            ]
        );
    }

    #[test]
    fn labeled_break_out_of_a_labeled_loop_statement() {
        // s0='outer: loop, s1=if c, s2=break 'outer, s3=body tail, s4=after.
        // The `loop` exits ONLY via the labeled break.
        let got = cpg_flows("fn f(c: bool) { 'outer: loop { if c { break 'outer; } a(); } t(); }");
        assert_eq!(
            got,
            vec![
                "0 -branch/body-> 1",
                "1 -branch/else-> 3",
                "1 -branch/then-> 2",
                "2 -break-> 4",
                "3 -loop-back-> 0",
                "4 -seq-> exit",
                "f#1 -entry-> 0",
            ]
        );
    }

    #[test]
    fn label_with_no_matching_loop_emits_no_edge() {
        // A labeled bare block is spliced (its label is not a loop); the break
        // has no modeled target — honest absence, not a fabricated edge.
        let got = cpg_flows("fn f(c: bool) { 'blk: { if c { break 'blk; } a(); } t(); }");
        assert_eq!(
            got,
            vec![
                "0 -branch/else-> 2",
                "0 -branch/then-> 1",
                "2 -seq-> 3",
                "3 -seq-> exit",
                "f#1 -entry-> 0",
            ]
        );
    }

    #[test]
    fn labeled_break_in_a_flat_match_arm() {
        // s0='outer: loop, s1=match c, s2=arm true(break 'outer), s3=arm false,
        // s4=after. The arm's labeled break exits the outer loop.
        let got = cpg_flows(
            "fn f(c: bool) { 'outer: loop { match c { true => break 'outer, false => (), } } t(); }",
        );
        assert_eq!(
            got,
            vec![
                "0 -branch/body-> 1",
                "1 -branch/arm-> 2",
                "1 -branch/arm-> 3",
                "2 -break-> 4",
                "3 -loop-back-> 0",
                "4 -seq-> exit",
                "f#1 -entry-> 0",
            ]
        );
    }

    // --- expression-position control flow: the pinned abstraction ------------

    #[test]
    fn expression_position_if_stays_one_statement() {
        // ADR-0003 (K3a): control flow in expression position is NOT
        // decomposed — `let x = if …` is one Let statement, no internal
        // branch/merge edges. Statement grain is a contract.
        let got = cpg_flows("fn f(c: bool) { let x = if c { 1 } else { 2 }; g(x); }");
        assert_eq!(got, vec!["0 -seq-> 1", "1 -seq-> exit", "f#1 -entry-> 0"]);
    }

    #[test]
    fn expression_position_if_reads_from_both_branches() {
        // The may-reach union a decomposed merge would produce: the Let reads
        // the condition and both branch values.
        let got = cpg_deps("fn f(c: bool, a: i32, b: i32) { let x = if c { a } else { b }; x; }");
        assert_eq!(
            got,
            vec![
                "0 -a/param-> f#1",
                "0 -b/param-> f#1",
                "0 -c/param-> f#1",
                "1 -x/let-> 0",
            ]
        );
    }

    // --- data flow: exact def-use assertions ---------------------------------

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

    #[test]
    fn let_def_and_use_chain() {
        // s0: let a = 1; s1: let b = a + 1; s2: b;
        let got = cpg_deps("fn f() { let a = 1; let b = a + 1; b }");
        assert_eq!(got, vec!["1 -a/let-> 0", "2 -b/let-> 1"]);
    }

    #[test]
    fn params_are_defs_at_the_function() {
        // s0 reads both parameters.
        let got = cpg_deps("fn add(a: i32, b: i32) -> i32 { a + b }");
        assert_eq!(got, vec!["0 -a/param-> add#1", "0 -b/param-> add#1"]);
    }

    #[test]
    fn straight_line_assignment_replaces() {
        // s0: let x = 1; s1: x = 2; s2: y reads x -> only the assign reaches.
        let got = cpg_deps("fn f() { let x = 1; x = 2; let y = x; }");
        assert_eq!(got, vec!["2 -x/assign-> 1"]);
    }

    #[test]
    fn compound_assignment_reads_its_old_value() {
        // s1: x += 1 reads x (def s0) and redefines it; s2 reads the assign.
        let got = cpg_deps("fn f() { let mut x = 1; x += 1; x; }");
        assert_eq!(got, vec!["1 -x/let-> 0", "2 -x/assign-> 1"]);
    }

    #[test]
    fn branch_defs_join_instead_of_replacing() {
        // s0: let mut x = 1; s1: if c; s2: x = 2 (then); s3: use x.
        // Both the original let and the conditional assign may reach s3.
        let got = cpg_deps("fn f(c: bool) { let mut x = 1; if c { x = 2; } x; }");
        assert_eq!(
            got,
            vec!["1 -c/param-> f#1", "3 -x/assign-> 2", "3 -x/let-> 0"]
        );
    }

    #[test]
    fn else_branch_covers_both_paths() {
        // if/else where both branches redefine: the original def is killed.
        let got = cpg_deps("fn f(c: bool) { let mut x = 1; if c { x = 2; } else { x = 3; } x; }");
        assert_eq!(
            got,
            vec!["1 -c/param-> f#1", "4 -x/assign-> 2", "4 -x/assign-> 3"]
        );
    }

    #[test]
    fn loop_back_edge_reaches_earlier_uses() {
        // s0: let mut x = 0; s1: while c; s2: use x (body); s3: x = f(x).
        // Through the back edge, s2 may read s3's def from a prior iteration.
        let got = cpg_deps("fn f(c: bool) { let mut x = 0; while c { g(x); x = h(x); } x; }");
        assert_eq!(
            got,
            vec![
                "1 -c/param-> f#1",
                "2 -x/assign-> 3",
                "2 -x/let-> 0",
                "3 -x/assign-> 3",
                "3 -x/let-> 0",
                "4 -x/assign-> 3",
                "4 -x/let-> 0",
            ]
        );
    }

    #[test]
    fn let_scope_ends_at_block_end() {
        // The inner `let x` shadows only inside the branch; the outer read
        // links to the outer def alone.
        let got = cpg_deps("fn f(c: bool) { let x = 1; if c { let x = 2; x; } x; }");
        assert_eq!(
            got,
            vec!["1 -c/param-> f#1", "3 -x/let-> 2", "4 -x/let-> 0"]
        );
    }

    #[test]
    fn match_arm_bindings_are_defs_at_the_arm() {
        // s0: match p; s1: arm Some(v); s2: v (body); s3: arm None.
        let got = cpg_deps("fn f(p: Option<i32>) { match p { Some(v) => { v; } None => {} } }");
        assert_eq!(got, vec!["0 -p/param-> f#1", "2 -v/pattern-> 1"]);
    }

    #[test]
    fn projection_store_is_a_read_not_a_def() {
        // `x.f = 1` must not kill the let def; the later read still sees it.
        let got = cpg_deps("fn f() { let mut x = mk(); x.f = 1; x; }");
        assert_eq!(got, vec!["1 -x/let-> 0", "2 -x/let-> 0"]);
    }

    #[test]
    fn for_loop_binds_its_pattern() {
        // s0: for i in xs; s1: use i.
        let got = cpg_deps("fn f(xs: Vec<i32>) { for i in xs { g(i); } }");
        assert_eq!(got, vec!["0 -xs/param-> f#1", "1 -i/loop-> 0"]);
    }

    #[test]
    fn cpg_lowering_is_byte_deterministic() {
        let src = "fn f(c: bool) -> i32 { let mut x = 0; while c { if x > 9 { break; } x += 1; } \
                   match x { 0 => return -1, n => n, } }";
        let (_, first) = base_and_cpg(src);
        let (_, second) = base_and_cpg(src);
        assert_eq!(
            first.to_jsonl(),
            second.to_jsonl(),
            "two CPG runs over the same source must be byte-identical"
        );
    }

    #[test]
    fn cpg_output_is_a_strict_superset_of_base() {
        let src = "fn add(a: i32, b: i32) -> i32 { a + b }\nfn run() { let x = add(1, 2); x; }";
        let (base, cpg) = base_and_cpg(src);
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
}
