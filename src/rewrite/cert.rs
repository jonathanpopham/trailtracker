//! Equivalence certificates for rewrite proposals (ADR-0007).
//!
//! Given the ORIGINAL file bytes and a verified proposal — and nothing else —
//! recompute the statement-level CPG (ADR-0003) of every function before and
//! after the rewrite (edits applied in memory, never on disk), and check that
//! the graphs match modulo EXACTLY the remapping the proposal's rule licenses:
//!
//! - `dead-branch-elim` v1: the unreachable branch subgraph is deleted, its
//!   incident edges re-stitched onto the spliced live branch; no dependency
//!   between surviving statements may appear, and one may disappear only when
//!   the affected region defines that variable.
//! - `loop-to-iterator` v1: the pair's statement subgraph collapses to ONE
//!   `let` whose external `DATA_DEP` in-set is identical to the pair's and
//!   which becomes the sole definition read by the accumulator's former users.
//! - `extract-function` v1: the run's subgraph relocates behind a deferred
//!   call (`let NAME = || {…}; NAME();`) with the external DFG cut preserved:
//!   in-cut = captures, out-cut (span-local `let`s used after) = returns.
//! - `redundant-clone-elim` v1: the graphs do not change AT ALL — the after
//!   CPG must equal the before CPG under the 1:1 statement mapping (the
//!   statement still reads the binding, now moving instead of copying), and
//!   the last-use precondition is re-proved from the before graph: no
//!   statement CFG-reachable after the clone reads the binding's definition.
//! - `slice-param` v1: the graphs do not change AT ALL — the edit lives in
//!   the SIGNATURE, outside every statement span, so the after CPG must
//!   equal the before CPG under the identity statement mapping; the
//!   preconditions (recognized parameter shape, slice/str-safe uses only,
//!   function never taken as a value) are re-proved from the before tree.
//!
//! Two layers (ADR-0007): structural verification (this module's graph
//! checks, run first — they produce the semantically precise failure) and
//! licensed-emission replay (the proposal's edits must byte-match what this
//! binary's recognizer+emitter produce for the original file, run last).
//! The per-rule SCHEMA obligation — why any application matching the
//! recognizer preserves behavior — lives in ADR-0007 and, where feasible, in
//! Kani harnesses (`eval/src/kani_proofs.rs`, self-skipping without Kani).
//!
//! Deterministic: no wall clock anywhere; same binary + same inputs ⇒
//! byte-identical certificate, `cert_hash` included.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use crate::core::json::Json;
use crate::core::span::ByteSpan;
use crate::graph::Graph;
use crate::ir::cpg::{assign_target, pattern_defs, top_index, ElsePart, Stmt, StmtKind};
use crate::ir::ontology::edge;
use crate::lang::rust::lexer::kind as tk;
use crate::lang::rust::parser::parse;
use crate::rewrite::edit::apply_edits;
use crate::rewrite::proposal::{fingerprint, Proposal, ProposedEdit};
use crate::rewrite::rules::{analyze_file, rule_by_id, FileCpg, FnUnit, RuleOptions};

pub const SCHEMA: &str = "trailtracker.rewrite-cert/v1";

/// The assumptions block (ADR-0007) — carried verbatim in every certificate.
pub const ASSUMPTIONS: &[&str] = &[
    "conservative may-reach def-use: DATA_DEP is may-reach, not must-reach; cut equality is equality of conservative sets",
    "no aliasing analysis: `x.f = v` and `*p = v` are reads, never definitions or kills",
    "side-effect and panic ORDER within collapsed regions is per-rule: dead-branch deletes only unreachable code; loop-to-iterator reuses the original expressions verbatim in the original per-element order; extract-function relocates the statements verbatim behind an immediately-executed call",
    "statement grain: sub-statement corruption is caught by the licensed-emission replay, not the graph checks",
    "closure-parameter shadow reads: names bound inside a collapsed region may re-read same-named outer definitions at statement grain; these add conservative may-deps only and are licensed when they target a surviving definition of that name",
    "model fidelity: where a Kani harness exists it proves the schema over a bounded model; the model-to-Rust mapping is a recorded argument, not a machine-checked fact",
    "the after text must parse cleanly; certification refuses diagnostics rather than guessing",
    "Clone/Drop trait contract (redundant-clone-elim): `Clone::clone`'s only observable effect is producing the owned copy and `Drop` releases exactly what `Clone` acquired; eliminating a proven-last-use clone moves the original's drop from the cloned binding's scope end to the moved-to binding's drop point — programs observing clone side effects or the drop ORDER of clone-eliminated values are outside the model",
    "std Deref contract (slice-param): `Vec<T>: Deref<Target = [T]>` and `String: Deref<Target = str>`, and every allowlisted method call resolves through that deref to the SAME slice/str implementation before and after; every direct call site coerces to the more general type, while uses of the enclosing function as a first-class value (fn-pointer/closure position) are refused within the analyzed file and are outside the model beyond it",
];

const ADR: &str = "docs/decisions/0007-equivalence-certificates.md";

/// The schema obligation a certificate points at: the ADR anchor plus the
/// Kani harness name, or MANUAL when the argument is not model-checkable.
fn obligation_for(rule_id: &str, version: &str) -> Option<(String, &'static str)> {
    match (rule_id, version) {
        ("dead-branch-elim", "1") => Some((
            format!("{ADR}#dead-branch-elim-v1--licensed-remapping"),
            "k3c_dead_branch_schema",
        )),
        ("loop-to-iterator", "1") => Some((
            format!("{ADR}#loop-to-iterator-v1--licensed-remapping"),
            "k3c_loop_fold_schema",
        )),
        ("extract-function", "1") => Some((
            format!("{ADR}#extract-function-v1--licensed-remapping"),
            "MANUAL",
        )),
        ("redundant-clone-elim", "1") => Some((
            format!("{ADR}#redundant-clone-elim-v1--licensed-remapping"),
            "k3c_clone_elim_schema",
        )),
        ("if-let-to-match", "1") => Some((
            format!("{ADR}#if-let-to-match-v1--licensed-remapping"),
            "k3c_if_let_match_schema",
        )),
        ("slice-param", "1") => Some((
            format!("{ADR}#slice-param-v1--licensed-remapping"),
            "MANUAL",
        )),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Failure + certificate documents
// ---------------------------------------------------------------------------

/// A verification failure: the machine-readable check that failed plus the
/// exact fact that broke. Fail-closed and precise, never a shrug.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertFailure {
    /// snake_case, stable across runs — agents can branch on it.
    pub check: String,
    pub detail: String,
}

impl CertFailure {
    fn new(check: &str, detail: impl Into<String>) -> CertFailure {
        CertFailure {
            check: check.to_string(),
            detail: detail.into(),
        }
    }
}

impl std::fmt::Display for CertFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.check, self.detail)
    }
}

/// The `trailtracker.rewrite-cert/v1` document. Everything in it is
/// recomputable from the original file plus the proposal; `cert_hash` is
/// change-detection (the proposal-hash construction), not cryptography — the
/// trust anchor is recomputation (`rewrite verify`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Certificate {
    pub rule_id: String,
    pub rule_version: String,
    pub obligation_ref: String,
    /// Kani harness name, or "MANUAL".
    pub obligation_kani: String,
    pub proposal_hash: String,
    pub dir: String,
    pub file: String,
    pub before_fingerprint: String,
    pub after_fingerprint: String,
    pub before_cpg_hash: String,
    pub after_cpg_hash: String,
    /// Before-side ids (`fn::{name}#{line}`) of the functions the rule verified.
    pub affected: Vec<String>,
    pub unaffected_verified: u64,
    /// The remapping facts verified, one per entry — machine-readable.
    pub checks: Vec<String>,
}

impl Certificate {
    fn body_json(&self) -> Json {
        Json::obj([
            ("schema", Json::str(SCHEMA)),
            (
                "rule",
                Json::obj([
                    ("id", Json::str(self.rule_id.clone())),
                    ("version", Json::str(self.rule_version.clone())),
                ]),
            ),
            (
                "schema_obligation",
                Json::obj([
                    ("ref", Json::str(self.obligation_ref.clone())),
                    ("kani", Json::str(self.obligation_kani.clone())),
                ]),
            ),
            ("proposal_hash", Json::str(self.proposal_hash.clone())),
            ("dir", Json::str(self.dir.clone())),
            ("file", Json::str(self.file.clone())),
            (
                "before_fingerprint",
                Json::str(self.before_fingerprint.clone()),
            ),
            (
                "after_fingerprint",
                Json::str(self.after_fingerprint.clone()),
            ),
            ("before_cpg_hash", Json::str(self.before_cpg_hash.clone())),
            ("after_cpg_hash", Json::str(self.after_cpg_hash.clone())),
            (
                "functions",
                Json::obj([
                    (
                        "affected",
                        Json::Array(self.affected.iter().map(|s| Json::str(s.clone())).collect()),
                    ),
                    ("unaffected_verified", Json::U64(self.unaffected_verified)),
                ]),
            ),
            (
                "checks",
                Json::Array(self.checks.iter().map(|s| Json::str(s.clone())).collect()),
            ),
            (
                "assumptions",
                Json::Array(ASSUMPTIONS.iter().map(|s| Json::str(*s)).collect()),
            ),
        ])
    }

    /// FNV-1a-64 over the canonical single-line body (minus `cert_hash`) —
    /// exactly the proposal-hash construction.
    pub fn hash(&self) -> String {
        fingerprint(self.body_json().to_line().as_bytes())
    }

    pub fn to_json(&self) -> Json {
        let Json::Object(mut map) = self.body_json() else {
            unreachable!("body_json builds an object");
        };
        map.insert("cert_hash".to_string(), Json::str(self.hash()));
        Json::Object(map)
    }
}

// ---------------------------------------------------------------------------
// Canonical per-function CPG view
// ---------------------------------------------------------------------------

/// A statement-graph node key, stable across the rewrite: statement ids are
/// pre-order indices (`stmt::{stem}::{n}`), so `S(n)` names the n-th node of
/// ONE function's emission regardless of byte offsets or line numbers.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Nk {
    Fun,
    S(usize),
    Exit,
}

impl std::fmt::Display for Nk {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Nk::Fun => write!(f, "fn"),
            Nk::Exit => write!(f, "exit"),
            Nk::S(n) => write!(f, "s{n}"),
        }
    }
}

type FlowEdge = (Nk, Nk, String, String); // from, to, role, branch
type DepEdge = (Nk, Nk, String, String); // use, def, var, def-kind

/// One function's edges under canonical keys.
struct FnEdges {
    flows: BTreeSet<FlowEdge>,
    deps: BTreeSet<DepEdge>,
}

fn prop_str(props: &BTreeMap<String, Json>, key: &str) -> String {
    match props.get(key) {
        Some(Json::Str(s)) => s.clone(),
        _ => String::new(),
    }
}

/// Extract one function's FLOWS_TO + DATA_DEP edges from the emitted graph.
fn fn_edges(g: &Graph, fn_id: &str) -> FnEdges {
    let stem = fn_id.strip_prefix("fn::").unwrap_or(fn_id);
    let prefix = format!("stmt::{stem}::");
    let key = |id: &str| -> Option<Nk> {
        if id == fn_id {
            return Some(Nk::Fun);
        }
        let rest = id.strip_prefix(&prefix)?;
        if rest == "exit" {
            Some(Nk::Exit)
        } else {
            rest.parse().ok().map(Nk::S)
        }
    };
    let mut flows = BTreeSet::new();
    let mut deps = BTreeSet::new();
    for e in g.edges() {
        let (Some(f), Some(t)) = (key(&e.from), key(&e.to)) else {
            continue;
        };
        match e.kind {
            k if k == edge::FLOWS_TO => {
                flows.insert((
                    f,
                    t,
                    prop_str(&e.props, "role"),
                    prop_str(&e.props, "branch"),
                ));
            }
            k if k == edge::DATA_DEP => {
                deps.insert((f, t, prop_str(&e.props, "var"), prop_str(&e.props, "def")));
            }
            _ => {}
        }
    }
    FnEdges { flows, deps }
}

/// Pre-order key of a statement (the `n` of `stmt::…::{n}`).
fn skey(id: &Option<String>) -> Option<usize> {
    id.as_ref()?.rsplit("::").next()?.parse().ok()
}

/// Collapse all whitespace runs to single spaces (the text-equality lens:
/// reindentation is licensed everywhere, token streams never are).
fn collapse(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
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

// ---------------------------------------------------------------------------
// Shape sequences: linearized statement trees with structural markers
// ---------------------------------------------------------------------------

/// One entry of a linearized statement tree. Sequence equality of shapes is
/// tree equality: `Open`/`Close` markers pin the nesting, `Node` entries pin
/// per-statement kind + whitespace-collapsed text.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Shape {
    Node {
        key: Option<usize>,
        kind: &'static str,
        text: String,
        span: ByteSpan,
    },
    Open(&'static str),
    Close,
    /// Expected sequences only: a rule-inserted statement slot.
    New {
        slot: usize,
    },
}

/// A dead-branch-elim application site (for expected-shape emission).
#[derive(Clone, Copy)]
struct DeadSite {
    span: ByteSpan,
    lit: bool,
}

/// An if-let-to-match application site (for expected-shape emission).
#[derive(Clone)]
struct IfLetSite {
    span: ByteSpan,
    /// Whitespace-collapsed scrutinee text — the `match` node's expected text.
    scrut: String,
}

/// The tree-level transformation a rule licenses, applied while emitting the
/// EXPECTED shape sequence from the before tree.
enum Xf<'x> {
    None,
    Dead(&'x [DeadSite]),
    /// `loop-to-iterator`: each pair `(S1 span, S2 span)` becomes one New slot.
    Pairs(&'x [(ByteSpan, ByteSpan)]),
    /// `extract-function`: the run covering this span becomes two New slots.
    Run(ByteSpan),
    /// `if-let-to-match`: each site's `if` node becomes a `match` node plus
    /// two New arm slots wrapping the verbatim branch bodies.
    IfLet(&'x [IfLetSite]),
}

fn dead_site(s: &Stmt<'_>, sites: &[DeadSite]) -> Option<bool> {
    if s.kind != StmtKind::If {
        return None;
    }
    sites.iter().find(|d| d.span == s.span).map(|d| d.lit)
}

fn node_text(s: &Stmt<'_>, src: &str) -> String {
    match s.kind {
        StmtKind::If | StmtKind::While | StmtKind::For | StmtKind::Match => {
            collapse(crate::ir::cpg::span_of(&s.header).text(src))
        }
        StmtKind::Loop => String::new(),
        _ => collapse(s.span.text(src)),
    }
}

struct ShapeCtx<'a> {
    src: &'a str,
    out: Vec<Shape>,
    slot: usize,
}

fn shape_stmts<'a>(stmts: &[Stmt<'a>], xf: &Xf<'_>, cx: &mut ShapeCtx<'a>) {
    let mut i = 0;
    while i < stmts.len() {
        let s = &stmts[i];
        match xf {
            Xf::Pairs(pairs)
                if pairs
                    .iter()
                    .any(|(a, b)| s.span == *a && stmts.get(i + 1).map(|n| n.span) == Some(*b)) =>
            {
                cx.out.push(Shape::New { slot: cx.slot });
                cx.slot += 1;
                i += 2;
                continue;
            }
            Xf::Run(span) if s.span.start == span.start => {
                let mut j = i;
                while j < stmts.len() && stmts[j].span.end <= span.end {
                    j += 1;
                }
                cx.out.push(Shape::New { slot: cx.slot });
                cx.out.push(Shape::New { slot: cx.slot + 1 });
                cx.slot += 2;
                i = j;
                continue;
            }
            Xf::Dead(sites) => {
                if let Some(lit) = dead_site(s, sites) {
                    dead_replacement_stmt(s, lit, xf, cx);
                    i += 1;
                    continue;
                }
            }
            Xf::IfLet(sites) => {
                if s.kind == StmtKind::If {
                    if let Some(site) = sites.iter().find(|d| d.span == s.span) {
                        if_let_replacement_stmt(s, site, xf, cx);
                        i += 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
        shape_stmt(s, xf, cx);
        i += 1;
    }
}

/// Statement-position replacement of a recognized `if let … else { … }`
/// (ADR-0007, if-let-to-match): the `if` node becomes a `match` node whose
/// text is the scrutinee; two New arm slots wrap the verbatim branch bodies
/// (pattern arm first, `_` arm second).
fn if_let_replacement_stmt<'a>(s: &Stmt<'a>, site: &IfLetSite, xf: &Xf<'_>, cx: &mut ShapeCtx<'a>) {
    cx.out.push(Shape::Node {
        key: skey(&s.id),
        kind: "match",
        text: site.scrut.clone(),
        span: s.span,
    });
    cx.out.push(Shape::New { slot: cx.slot });
    cx.slot += 1;
    cx.out.push(Shape::Open("arm"));
    if let Some(b) = &s.body {
        shape_stmts(b, xf, cx);
    }
    cx.out.push(Shape::Close);
    cx.out.push(Shape::New { slot: cx.slot });
    cx.slot += 1;
    cx.out.push(Shape::Open("arm"));
    if let Some(ElsePart::Block(_, b)) = &s.else_part {
        shape_stmts(b, xf, cx);
    }
    cx.out.push(Shape::Close);
}

fn shape_stmt<'a>(s: &Stmt<'a>, xf: &Xf<'_>, cx: &mut ShapeCtx<'a>) {
    cx.out.push(Shape::Node {
        key: skey(&s.id),
        kind: s.kind.label(),
        text: node_text(s, cx.src),
        span: s.span,
    });
    if let Some(b) = &s.body {
        cx.out.push(Shape::Open("body"));
        shape_stmts(b, xf, cx);
        cx.out.push(Shape::Close);
    }
    match &s.else_part {
        Some(ElsePart::Block(_, b)) => {
            cx.out.push(Shape::Open("else"));
            shape_stmts(b, xf, cx);
            cx.out.push(Shape::Close);
        }
        Some(ElsePart::If(nested)) => {
            if let Xf::Dead(sites) = xf {
                if let Some(lit) = dead_site(nested, sites) {
                    dead_replacement_else(nested, lit, xf, cx);
                    return arms_shape(s, xf, cx);
                }
            }
            cx.out.push(Shape::Open("elseif"));
            shape_stmt(nested, xf, cx);
            cx.out.push(Shape::Close);
        }
        None => {}
    }
    arms_shape(s, xf, cx);
}

fn arms_shape<'a>(s: &Stmt<'a>, xf: &Xf<'_>, cx: &mut ShapeCtx<'a>) {
    for arm in &s.arms {
        let mut text = collapse(crate::ir::cpg::span_of(&arm.pattern).text(cx.src));
        if !arm.expr.is_empty() {
            let _ = write!(
                text,
                " => {}",
                collapse(crate::ir::cpg::span_of(&arm.expr).text(cx.src))
            );
        }
        cx.out.push(Shape::Node {
            key: skey(&arm.id),
            kind: "arm",
            text,
            span: arm.span,
        });
        if let Some(b) = &arm.block {
            cx.out.push(Shape::Open("arm"));
            shape_stmts(b, xf, cx);
            cx.out.push(Shape::Close);
        }
    }
}

/// Statement-position replacement of a literal-condition `if` (ADR-0007,
/// dead-branch-elim): the live branch's statements splice in place.
fn dead_replacement_stmt<'a>(s: &Stmt<'a>, lit: bool, xf: &Xf<'_>, cx: &mut ShapeCtx<'a>) {
    if lit {
        if let Some(b) = &s.body {
            shape_stmts(b, xf, cx);
        }
        return;
    }
    match &s.else_part {
        Some(ElsePart::Block(_, b)) => shape_stmts(b, xf, cx),
        Some(ElsePart::If(nested)) => {
            if let Xf::Dead(sites) = xf {
                if let Some(l) = dead_site(nested, sites) {
                    return dead_replacement_stmt(nested, l, xf, cx);
                }
            }
            shape_stmt(nested, xf, cx);
        }
        None => {}
    }
}

/// Else-position replacement (`… else if LITERAL …`): the parent keeps a
/// brace-wrapped else (or the trailing chain, or nothing).
fn dead_replacement_else<'a>(nested: &Stmt<'a>, lit: bool, xf: &Xf<'_>, cx: &mut ShapeCtx<'a>) {
    if lit {
        cx.out.push(Shape::Open("else"));
        if let Some(b) = &nested.body {
            shape_stmts(b, xf, cx);
        }
        cx.out.push(Shape::Close);
        return;
    }
    match &nested.else_part {
        Some(ElsePart::Block(_, b)) => {
            cx.out.push(Shape::Open("else"));
            shape_stmts(b, xf, cx);
            cx.out.push(Shape::Close);
        }
        Some(ElsePart::If(n2)) => {
            if let Xf::Dead(sites) = xf {
                if let Some(l) = dead_site(n2, sites) {
                    return dead_replacement_else(n2, l, xf, cx);
                }
            }
            cx.out.push(Shape::Open("elseif"));
            shape_stmt(n2, xf, cx);
            cx.out.push(Shape::Close);
        }
        None => {}
    }
}

fn shapes_of(f: &FnUnit<'_>, src: &str, xf: &Xf<'_>) -> Vec<Shape> {
    let mut cx = ShapeCtx {
        src,
        out: Vec::new(),
        slot: 0,
    };
    shape_stmts(&f.stmts, xf, &mut cx);
    cx.out
}

/// The node correspondence produced by aligning an expected shape sequence
/// against the after tree's actual one.
struct Mapping {
    /// Surviving before key → after key.
    map: BTreeMap<usize, usize>,
    /// New-slot index → (after key, after stmt kind label).
    news: BTreeMap<usize, (usize, &'static str)>,
}

impl Mapping {
    fn nk(&self, n: Nk) -> Option<Nk> {
        match n {
            Nk::Fun => Some(Nk::Fun),
            Nk::Exit => Some(Nk::Exit),
            Nk::S(k) => self.map.get(&k).copied().map(Nk::S),
        }
    }
}

/// Align expected against actual. `text_free_spans`: before-side spans whose
/// Node text may legitimately differ (nested-function Item statements whose
/// interior another function's verifier owns).
fn align(
    fn_name: &str,
    expected: &[Shape],
    actual: &[Shape],
    text_free_spans: &[ByteSpan],
) -> Result<Mapping, CertFailure> {
    let fail = |i: usize, want: &str, got: &str| {
        CertFailure::new(
            "tree_remapping_mismatch",
            format!(
                "fn `{fn_name}`: after tree diverges from the licensed transformation at \
                 entry {i}: expected {want}, found {got}"
            ),
        )
    };
    if expected.len() != actual.len() {
        return Err(CertFailure::new(
            "tree_remapping_mismatch",
            format!(
                "fn `{fn_name}`: after tree has {} entries where the licensed transformation \
                 produces {}",
                actual.len(),
                expected.len()
            ),
        ));
    }
    let mut m = Mapping {
        map: BTreeMap::new(),
        news: BTreeMap::new(),
    };
    for (i, (e, a)) in expected.iter().zip(actual.iter()).enumerate() {
        match (e, a) {
            (
                Shape::Node {
                    key: Some(bk),
                    kind,
                    text,
                    span,
                },
                Shape::Node {
                    key: Some(ak),
                    kind: kind2,
                    text: text2,
                    ..
                },
            ) => {
                if kind != kind2 {
                    return Err(fail(
                        i,
                        &format!("{kind} `{text}`"),
                        &format!("{kind2} `{text2}`"),
                    ));
                }
                let text_free = *kind == "item"
                    && text_free_spans
                        .iter()
                        .any(|s| span.start <= s.start && s.end <= span.end);
                if text != text2 && !text_free {
                    return Err(fail(
                        i,
                        &format!("{kind} `{text}`"),
                        &format!("{kind2} `{text2}`"),
                    ));
                }
                m.map.insert(*bk, *ak);
            }
            (
                Shape::New { slot },
                Shape::Node {
                    key: Some(ak),
                    kind,
                    ..
                },
            ) => {
                m.news.insert(*slot, (*ak, kind));
            }
            (Shape::Open(x), Shape::Open(y)) if x == y => {}
            (Shape::Close, Shape::Close) => {}
            _ => {
                return Err(fail(i, &format!("{e:?}"), &format!("{a:?}")));
            }
        }
    }
    Ok(m)
}

// ---------------------------------------------------------------------------
// Region facts recomputed from the before tree (never from the proposal)
// ---------------------------------------------------------------------------

/// Every statement/arm key in these subtrees.
fn subtree_keys(stmts: &[Stmt<'_>]) -> BTreeSet<usize> {
    let mut keys = BTreeSet::new();
    crate::rewrite::rules::walk_stmts(stmts, &mut |s| {
        if let Some(k) = skey(&s.id) {
            keys.insert(k);
        }
        for arm in &s.arms {
            if let Some(k) = skey(&arm.id) {
                keys.insert(k);
            }
        }
    });
    keys
}

/// Names defined anywhere in these subtrees (`let`/`for`/`if let`/`while let`
/// patterns, plain and compound assignments, match-arm patterns). Slightly
/// generous by construction — used only to JUSTIFY licensed dependency
/// changes, never to create expectations.
fn region_defs(stmts: &[&Stmt<'_>], src: &str) -> BTreeSet<String> {
    let mut defs = BTreeSet::new();
    for root in stmts {
        crate::rewrite::rules::walk_stmt(root, &mut |s| {
            match s.kind {
                StmtKind::Let => {
                    let cut = top_index(&s.header, ":", src)
                        .into_iter()
                        .chain(top_index(&s.header, "=", src))
                        .min()
                        .unwrap_or(s.header.len());
                    defs.extend(pattern_defs(&s.header[1.min(cut)..cut], src));
                }
                StmtKind::Expr => {
                    if let (Some(t), _) = assign_target(&s.header, src) {
                        defs.insert(t);
                    }
                }
                StmtKind::For => {
                    if let Some(ix) = top_index(&s.header, "in", src) {
                        defs.extend(pattern_defs(&s.header[..ix], src));
                    }
                }
                StmtKind::If | StmtKind::While => {
                    if s.header.first().and_then(|e| e.text(src)) == Some("let") {
                        let eq = top_index(&s.header, "=", src).unwrap_or(s.header.len());
                        defs.extend(pattern_defs(&s.header[1.min(eq)..eq], src));
                    }
                }
                _ => {}
            }
            for arm in &s.arms {
                let guard = top_index(&arm.pattern, "if", src).unwrap_or(arm.pattern.len());
                defs.extend(pattern_defs(&arm.pattern[..guard], src));
            }
        });
    }
    defs
}

/// Does before-node `d` define `var`? (Statement defs per `region_defs`, or a
/// function parameter when `d` is the function node with `def=param`.)
fn is_def_of(d: Nk, def_kind: &str, var: &str, by_key: &BTreeMap<usize, Vec<String>>) -> bool {
    match d {
        Nk::Fun => def_kind == "param",
        Nk::S(k) => by_key
            .get(&k)
            .is_some_and(|names| names.iter().any(|n| n == var)),
        Nk::Exit => false,
    }
}

/// Per-statement-key defined names for one function (justification lookups).
fn defs_by_key(f: &FnUnit<'_>, src: &str) -> BTreeMap<usize, Vec<String>> {
    let mut out: BTreeMap<usize, Vec<String>> = BTreeMap::new();
    crate::rewrite::rules::walk_stmts(&f.stmts, &mut |s| {
        let shallow: Vec<String> = match s.kind {
            StmtKind::Let => {
                let cut = top_index(&s.header, ":", src)
                    .into_iter()
                    .chain(top_index(&s.header, "=", src))
                    .min()
                    .unwrap_or(s.header.len());
                pattern_defs(&s.header[1.min(cut)..cut], src)
            }
            StmtKind::Expr => match assign_target(&s.header, src) {
                (Some(t), _) => vec![t],
                _ => Vec::new(),
            },
            StmtKind::For => match top_index(&s.header, "in", src) {
                Some(ix) => pattern_defs(&s.header[..ix], src),
                None => Vec::new(),
            },
            StmtKind::If | StmtKind::While => {
                if s.header.first().and_then(|e| e.text(src)) == Some("let") {
                    let eq = top_index(&s.header, "=", src).unwrap_or(s.header.len());
                    pattern_defs(&s.header[1.min(eq)..eq], src)
                } else {
                    Vec::new()
                }
            }
            _ => Vec::new(),
        };
        if let Some(k) = skey(&s.id) {
            out.insert(k, shallow);
        }
        for arm in &s.arms {
            if let Some(k) = skey(&arm.id) {
                let guard = top_index(&arm.pattern, "if", src).unwrap_or(arm.pattern.len());
                out.insert(k, pattern_defs(&arm.pattern[..guard], src));
            }
        }
    });
    out
}

// ---------------------------------------------------------------------------
// The certify driver
// ---------------------------------------------------------------------------

/// Certify `proposal` against the ORIGINAL `source` bytes: recompute the
/// before/after CPGs and verify the rule's licensed remapping, then replay the
/// licensed emission. Returns the certificate or the exact failed check.
pub fn certify(source: &str, proposal: &Proposal) -> Result<Certificate, CertFailure> {
    let (obligation_ref, obligation_kani) =
        obligation_for(&proposal.rule_id, &proposal.rule_version).ok_or_else(|| {
            CertFailure::new(
                "unknown_rule",
                format!(
                    "no schema obligation is on file for rule `{}` v{} — this build cannot \
                     certify it",
                    proposal.rule_id, proposal.rule_version
                ),
            )
        })?;
    if proposal.edits.is_empty() {
        return Err(CertFailure::new(
            "nothing_to_certify",
            "the proposal contains no edits",
        ));
    }
    let before_fp = fingerprint(source.as_bytes());
    if before_fp != proposal.file_fingerprint {
        return Err(CertFailure::new(
            "file_fingerprint_mismatch",
            format!(
                "the file is {before_fp} but the proposal expects {}",
                proposal.file_fingerprint
            ),
        ));
    }
    for (k, e) in proposal.edits.iter().enumerate() {
        let (s, t) = (e.span.start as usize, e.span.end as usize);
        if t > source.len() || source.get(s..t) != Some(e.before.as_str()) {
            return Err(CertFailure::new(
                "edit_before_mismatch",
                format!("edit {k} does not match the bytes at {s}..{t}"),
            ));
        }
    }

    let after_src = apply_edits(source, &proposal.span_edits())
        .map_err(|e| CertFailure::new("edits_not_applicable", e.to_string()))?;

    let tree_b = parse(&proposal.file, source);
    if !tree_b.is_lossless() || !tree_b.diagnostics.is_empty() {
        return Err(CertFailure::new(
            "before_parse_unclean",
            format!(
                "the original file has {} parse diagnostic(s); a certificate may not build on \
                 a guessed tree",
                tree_b.diagnostics.len()
            ),
        ));
    }
    let tree_a = parse(&proposal.file, &after_src);
    if !tree_a.is_lossless() || !tree_a.diagnostics.is_empty() {
        return Err(CertFailure::new(
            "after_parse_unclean",
            format!(
                "the rewritten text has {} parse diagnostic(s)",
                tree_a.diagnostics.len()
            ),
        ));
    }

    let cb = analyze_file(&tree_b);
    let ca = analyze_file(&tree_a);

    if cb.fns.len() != ca.fns.len() {
        return Err(CertFailure::new(
            "function_set_changed",
            format!(
                "before has {} function(s), after has {} — a span rewrite may not add or \
                 remove functions",
                cb.fns.len(),
                ca.fns.len()
            ),
        ));
    }
    for (fb, fa) in cb.fns.iter().zip(ca.fns.iter()) {
        if fb.name != fa.name {
            return Err(CertFailure::new(
                "function_set_changed",
                format!(
                    "function order/name changed: `{}` became `{}`",
                    fb.name, fa.name
                ),
            ));
        }
    }

    // Every edit must sit inside at least one function body — or, for rules
    // that rewrite the signature (slice-param), inside a function signature.
    let contains =
        |block: ByteSpan, span: ByteSpan| block.start <= span.start && span.end <= block.end;
    let within = |f: &FnUnit<'_>, span: ByteSpan| {
        contains(f.block.span, span) || f.sig.is_some_and(|s| contains(s.span, span))
    };
    for e in &proposal.edits {
        if !cb.fns.iter().any(|f| within(f, e.span)) {
            return Err(CertFailure::new(
                "edit_outside_function",
                format!(
                    "edit at bytes {}..{} is not inside any function body or signature",
                    e.span.start, e.span.end
                ),
            ));
        }
    }
    // Innermost owner per edit (nested fns: the innermost fn's verifier owns
    // the edit; enclosing fns see it as an Item-text change, licensed below).
    let owner_of = |span: ByteSpan| -> usize {
        cb.fns
            .iter()
            .enumerate()
            .filter(|(_, f)| within(f, span))
            .min_by_key(|(_, f)| f.block.span.end - f.block.span.start)
            .map(|(i, _)| i)
            .expect("checked above")
    };
    let mut edits_by_fn: BTreeMap<usize, Vec<&ProposedEdit>> = BTreeMap::new();
    for e in &proposal.edits {
        edits_by_fn.entry(owner_of(e.span)).or_default().push(e);
    }

    let mut checks: Vec<String> = Vec::new();
    let mut affected: Vec<String> = Vec::new();
    let mut unaffected = 0u64;

    for (i, (fb, fa)) in cb.fns.iter().zip(ca.fns.iter()).enumerate() {
        let owned = edits_by_fn.get(&i);
        let touched: Vec<ByteSpan> = proposal
            .edits
            .iter()
            .map(|e| e.span)
            .filter(|s| contains(fb.block.span, *s))
            .collect();
        match owned {
            Some(edits) => {
                affected.push(fb.fn_id.clone());
                verify_affected(proposal, &cb, fb, &ca, fa, edits, &mut checks)?;
            }
            None if touched.is_empty() => {
                verify_unaffected(&cb, fb, &ca, fa, &[])?;
                unaffected += 1;
            }
            None => {
                // Encloses another function that owns the edit(s): identical
                // except Item-statement text covering those spans.
                verify_unaffected(&cb, fb, &ca, fa, &touched)?;
                checks.push(format!(
                    "fn `{}`: unchanged except nested-function item text owned by an inner \
                     function's verifier",
                    fb.fn_id
                ));
                unaffected += 1;
            }
        }
    }

    // Layer 2b: licensed-emission replay — every proposal edit must byte-match
    // an edit this binary's recognizer+emitter produce for the original file.
    replay(source, proposal, &cb, &mut checks)?;

    checks.push(format!(
        "replayed licensed emission: {} edit(s) byte-identical to this binary's \
         recognizer+emitter output for the original file",
        proposal.edits.len()
    ));

    Ok(Certificate {
        rule_id: proposal.rule_id.clone(),
        rule_version: proposal.rule_version.clone(),
        obligation_ref,
        obligation_kani: obligation_kani.to_string(),
        proposal_hash: proposal.hash(),
        dir: proposal.dir.clone(),
        file: proposal.file.clone(),
        before_fingerprint: before_fp,
        after_fingerprint: fingerprint(after_src.as_bytes()),
        before_cpg_hash: cpg_hash(&cb),
        after_cpg_hash: cpg_hash(&ca),
        affected,
        unaffected_verified: unaffected,
        checks,
    })
}

/// Canonical hash of a whole file's per-function CPGs: shapes + edges under
/// pre-order keys — the comparison substrate itself, attested.
fn cpg_hash(ctx: &FileCpg<'_>) -> String {
    let mut buf = String::new();
    for f in &ctx.fns {
        let _ = write!(buf, "fn {} {{", f.name);
        for sh in shapes_of(f, ctx.src, &Xf::None) {
            let _ = write!(buf, "{sh:?};");
        }
        let ed = fn_edges(&ctx.graph, &f.fn_id);
        for (a, b, r, br) in &ed.flows {
            let _ = write!(buf, "F {a}->{b} {r} {br};");
        }
        for (a, b, v, d) in &ed.deps {
            let _ = write!(buf, "D {a}->{b} {v} {d};");
        }
        let _ = write!(buf, "}}");
    }
    fingerprint(buf.as_bytes())
}

/// An unaffected function: canonically identical CPG (shape, control flow,
/// data flow). `item_spans` licenses text drift ONLY on Item statements
/// containing a nested function another verifier owns.
fn verify_unaffected(
    cb: &FileCpg<'_>,
    fb: &FnUnit<'_>,
    ca: &FileCpg<'_>,
    fa: &FnUnit<'_>,
    item_spans: &[ByteSpan],
) -> Result<(), CertFailure> {
    let expected = shapes_of(fb, cb.src, &Xf::None);
    let actual = shapes_of(fa, ca.src, &Xf::None);
    let m = align(&fb.name, &expected, &actual, item_spans)?;
    let eb = fn_edges(&cb.graph, &fb.fn_id);
    let ea = fn_edges(&ca.graph, &fa.fn_id);
    let map_flow = |e: &FlowEdge| -> Option<FlowEdge> {
        Some((m.nk(e.0)?, m.nk(e.1)?, e.2.clone(), e.3.clone()))
    };
    let expected_flows: BTreeSet<FlowEdge> = eb.flows.iter().filter_map(&map_flow).collect();
    let expected_deps: BTreeSet<DepEdge> = eb.deps.iter().filter_map(&map_flow).collect();
    if expected_flows != ea.flows || expected_deps != ea.deps {
        return Err(CertFailure::new(
            "unaffected_function_changed",
            format!(
                "fn `{}` is outside every edit span but its CPG changed",
                fb.name
            ),
        ));
    }
    Ok(())
}

/// Dispatch the rule-specific remapping verifier for one affected function.
fn verify_affected(
    proposal: &Proposal,
    cb: &FileCpg<'_>,
    fb: &FnUnit<'_>,
    ca: &FileCpg<'_>,
    fa: &FnUnit<'_>,
    edits: &[&ProposedEdit],
    checks: &mut Vec<String>,
) -> Result<(), CertFailure> {
    match proposal.rule_id.as_str() {
        "dead-branch-elim" => verify_dead_branch(cb, fb, ca, fa, edits, checks),
        "loop-to-iterator" => verify_loop_chain(cb, fb, ca, fa, edits, checks),
        "extract-function" => verify_extract_fn(cb, fb, ca, fa, edits, checks),
        "redundant-clone-elim" => verify_clone_elim(cb, fb, ca, fa, edits, checks),
        "if-let-to-match" => verify_if_let_match(cb, fb, ca, fa, edits, checks),
        "slice-param" => verify_slice_param(cb, fb, ca, fa, edits, checks),
        other => Err(CertFailure::new(
            "unknown_rule",
            format!("no remapping verifier for rule `{other}`"),
        )),
    }
}

// ---------------------------------------------------------------------------
// Rule 1 verifier: dead-branch-elim
// ---------------------------------------------------------------------------

struct DeadInfo {
    key: usize,
    live_branch: &'static str,
    /// First statement of the live branch (survives), when one exists.
    live_first: Option<usize>,
    /// Keys removed by this site: the `if` itself plus the dead subtree.
    removed: BTreeSet<usize>,
}

/// Find the target `if` statement of one dead-branch edit: same end as the
/// edit span (the span may extend left over a dangling `else`), condition the
/// literal token `true`/`false` — all re-derived from the tree, never trusted.
fn find_dead_target<'s, 'a>(
    fb: &'s FnUnit<'a>,
    src: &str,
    edit: &ProposedEdit,
) -> Result<(&'s Stmt<'a>, bool), CertFailure> {
    let mut found: Option<&'s Stmt<'a>> = None;
    crate::rewrite::rules::walk_stmts(&fb.stmts, &mut |s| {
        if s.kind == StmtKind::If
            && s.span.end == edit.span.end
            && s.span.start >= edit.span.start
            && found.is_none()
        {
            let gap = &src[edit.span.start as usize..s.span.start as usize];
            if gap.is_empty() || gap.trim() == "else" {
                found = Some(s);
            }
        }
    });
    let s = found.ok_or_else(|| {
        CertFailure::new(
            "site_not_recognized",
            format!(
                "no `if` statement matches the edit span {}..{}",
                edit.span.start, edit.span.end
            ),
        )
    })?;
    if s.header.len() != 1 {
        return Err(CertFailure::new(
            "site_not_recognized",
            "the target `if` condition is not a single token".to_string(),
        ));
    }
    match s.header[0].text(src) {
        Some("true") => Ok((s, true)),
        Some("false") => Ok((s, false)),
        other => Err(CertFailure::new(
            "site_not_recognized",
            format!(
                "the target `if` condition is `{}`, not the literal token true/false",
                other.unwrap_or("<group>")
            ),
        )),
    }
}

fn verify_dead_branch(
    cb: &FileCpg<'_>,
    fb: &FnUnit<'_>,
    ca: &FileCpg<'_>,
    fa: &FnUnit<'_>,
    edits: &[&ProposedEdit],
    checks: &mut Vec<String>,
) -> Result<(), CertFailure> {
    let src = cb.src;
    let mut sites: Vec<DeadSite> = Vec::new();
    let mut infos: Vec<DeadInfo> = Vec::new();
    let mut region_stmts_defs: BTreeSet<String> = BTreeSet::new();

    for edit in edits {
        let (s, lit) = find_dead_target(fb, src, edit)?;
        let key = skey(&s.id).ok_or_else(|| {
            CertFailure::new("site_not_recognized", "target statement has no CPG id")
        })?;
        let (live_first, live_slice, dead_keys): (Option<usize>, Vec<&Stmt<'_>>, BTreeSet<usize>) =
            if lit {
                let live: Vec<&Stmt<'_>> = s.body.as_deref().unwrap_or(&[]).iter().collect();
                let dead = match &s.else_part {
                    Some(ElsePart::Block(_, b)) => subtree_keys(b),
                    Some(ElsePart::If(n)) => subtree_keys(std::slice::from_ref(&**n)),
                    None => BTreeSet::new(),
                };
                (live.first().and_then(|f| skey(&f.id)), live, dead)
            } else {
                let dead = s.body.as_ref().map(|b| subtree_keys(b)).unwrap_or_default();
                let live: Vec<&Stmt<'_>> = match &s.else_part {
                    Some(ElsePart::Block(_, b)) => b.iter().collect(),
                    Some(ElsePart::If(n)) => vec![&**n],
                    None => Vec::new(),
                };
                (live.first().and_then(|f| skey(&f.id)), live, dead)
            };
        // Region defs (justification lens): the if + both branches.
        region_stmts_defs.extend(region_defs(&[s], src));
        let _ = live_slice;
        let mut removed = dead_keys;
        removed.insert(key);
        sites.push(DeadSite { span: s.span, lit });
        infos.push(DeadInfo {
            key,
            live_branch: if lit { "then" } else { "else" },
            live_first,
            removed,
        });
    }

    // Tree: the after tree must equal the licensed transformation.
    let expected = shapes_of(fb, src, &Xf::Dead(&sites));
    let actual = shapes_of(fa, ca.src, &Xf::None);
    let m = align(&fb.name, &expected, &actual, &[])?;

    let removed_all: BTreeSet<usize> = infos.iter().flat_map(|i| i.removed.clone()).collect();
    let surviving = |n: Nk| -> bool {
        match n {
            Nk::Fun | Nk::Exit => true,
            Nk::S(k) => !removed_all.contains(&k),
        }
    };
    let info_of = |k: usize| infos.iter().find(|i| i.key == k);

    let eb = fn_edges(&cb.graph, &fb.fn_id);
    let ea = fn_edges(&ca.graph, &fa.fn_id);

    // The literal condition reads/defines nothing: any DATA_DEP incident to a
    // target `if` node is an unlicensed shape.
    for (u, d, var, _) in &eb.deps {
        for i in &infos {
            if *u == Nk::S(i.key) || *d == Nk::S(i.key) {
                return Err(CertFailure::new(
                    "if_condition_has_data_deps",
                    format!(
                        "fn `{}`: DATA_DEP var={var} touches the literal-condition `if` \
                         (s{}) — outside the licensed shape",
                        fb.name, i.key
                    ),
                ));
            }
        }
    }

    // CFG: re-stitch incoming edges of each removed `if` onto the live entry
    // (or transitively onto the fallthrough target when the live branch is
    // empty), drop everything incident to removed nodes, keep the rest.
    let resolve = |start_key: usize| -> Result<(Nk, bool), CertFailure> {
        let mut k = start_key;
        let mut loopback = false;
        loop {
            let info = info_of(k).ok_or_else(|| {
                CertFailure::new(
                    "cfg_remapping_mismatch",
                    format!(
                        "fn `{}`: control falls into removed statement s{k} that is not a \
                         certified site",
                        fb.name
                    ),
                )
            })?;
            if let Some(lf) = info.live_first {
                return Ok((Nk::S(lf), loopback));
            }
            let mut outs: Vec<&FlowEdge> = eb
                .flows
                .iter()
                .filter(|(f, _, _, b)| *f == Nk::S(k) && b == info.live_branch)
                .collect();
            outs.sort();
            let Some((_, t, r, _)) = outs.first().copied() else {
                return Err(CertFailure::new(
                    "cfg_remapping_mismatch",
                    format!(
                        "fn `{}`: removed `if` s{k} has no fallthrough edge on its live \
                         branch",
                        fb.name
                    ),
                ));
            };
            loopback |= r == "loop-back";
            match t {
                Nk::S(tk2) if removed_all.contains(tk2) => k = *tk2,
                other => return Ok((*other, loopback)),
            }
        }
    };

    let mut expected_flows: BTreeSet<FlowEdge> = BTreeSet::new();
    for (f, t, r, b) in &eb.flows {
        match (surviving(*f), surviving(*t)) {
            (true, true) => {
                let (mf, mt) = (m.nk(*f), m.nk(*t));
                let (Some(mf), Some(mt)) = (mf, mt) else {
                    return Err(CertFailure::new(
                        "cfg_remapping_mismatch",
                        format!("fn `{}`: surviving node lost its mapping", fb.name),
                    ));
                };
                expected_flows.insert((mf, mt, r.clone(), b.clone()));
            }
            (true, false) => {
                let Nk::S(tk2) = t else { unreachable!() };
                if info_of(*tk2).is_none() {
                    return Err(CertFailure::new(
                        "cfg_remapping_mismatch",
                        format!(
                            "fn `{}`: surviving statement flows into removed non-site s{tk2}",
                            fb.name
                        ),
                    ));
                }
                let (target, loopback) = resolve(*tk2)?;
                let Some(mf) = m.nk(*f) else {
                    return Err(CertFailure::new(
                        "cfg_remapping_mismatch",
                        format!("fn `{}`: surviving node lost its mapping", fb.name),
                    ));
                };
                let Some(mt) = m.nk(target) else {
                    return Err(CertFailure::new(
                        "cfg_remapping_mismatch",
                        format!("fn `{}`: re-stitch target lost its mapping", fb.name),
                    ));
                };
                let role = if loopback {
                    "loop-back".to_string()
                } else {
                    r.clone()
                };
                expected_flows.insert((mf, mt, role, b.clone()));
            }
            // Edges FROM removed nodes (the dead subtree's own flow, the if's
            // branch edges) are deleted with the region.
            (false, _) => {}
        }
    }
    diff_edges(
        &fb.name,
        "cfg_remapping_mismatch",
        "FLOWS_TO",
        &expected_flows,
        &ea.flows,
        |_| false,
    )?;

    // DFG: no new dependency may appear; a dependency between surviving
    // statements may disappear only when the region defines that variable.
    let mut expected_deps: BTreeSet<DepEdge> = BTreeSet::new();
    for (u, d, var, def) in &eb.deps {
        if surviving(*u) && surviving(*d) {
            let (Some(mu), Some(md)) = (m.nk(*u), m.nk(*d)) else {
                continue;
            };
            expected_deps.insert((mu, md, var.clone(), def.clone()));
        }
    }
    let mut shrunk: Vec<String> = Vec::new();
    for e in expected_deps.difference(&ea.deps) {
        if region_stmts_defs.contains(&e.2) {
            shrunk.push(format!("{} -> {} var={}", e.0, e.1, e.2));
        } else {
            return Err(CertFailure::new(
                "dfg_dependency_lost",
                format!(
                    "fn `{}`: DATA_DEP {} -> {} var={} disappeared but the eliminated region \
                     defines no `{}`",
                    fb.name, e.0, e.1, e.2, e.2
                ),
            ));
        }
    }
    if let Some(e) = ea.deps.difference(&expected_deps).next() {
        return Err(CertFailure::new(
            "dfg_dependency_added",
            format!(
                "fn `{}`: new DATA_DEP {} -> {} var={} appeared — dead-branch elimination \
                 licenses no new dependencies",
                fb.name, e.0, e.1, e.2
            ),
        ));
    }

    checks.push(format!(
        "fn `{}` [dead-branch-elim]: {} site(s) re-derived as literal-condition `if`; after \
         tree equals the licensed splice; CFG re-stitched exactly ({} edges verified); DFG: \
         0 added, {} shrunk (each justified by a definition in the eliminated region)",
        fb.fn_id,
        infos.len(),
        ea.flows.len(),
        shrunk.len()
    ));
    Ok(())
}

/// Report the first difference between an expected and an actual edge set.
/// `allowed_extra` filters licensed after-side additions (records them via
/// the return list instead of failing).
fn diff_edges(
    fn_name: &str,
    check: &str,
    kind: &str,
    expected: &BTreeSet<FlowEdge>,
    actual: &BTreeSet<FlowEdge>,
    mut allowed_extra: impl FnMut(&FlowEdge) -> bool,
) -> Result<Vec<FlowEdge>, CertFailure> {
    if let Some(e) = expected.difference(actual).next() {
        return Err(CertFailure::new(
            check,
            format!(
                "fn `{fn_name}`: expected {kind} edge {} -> {} ({} {}) is absent after the \
                 rewrite",
                e.0, e.1, e.2, e.3
            ),
        ));
    }
    let mut allowed = Vec::new();
    for e in actual.difference(expected) {
        if allowed_extra(e) {
            allowed.push(e.clone());
            continue;
        }
        return Err(CertFailure::new(
            check,
            format!(
                "fn `{fn_name}`: unlicensed {kind} edge {} -> {} ({} {}) appeared after the \
                 rewrite",
                e.0, e.1, e.2, e.3
            ),
        ));
    }
    Ok(allowed)
}

// ---------------------------------------------------------------------------
// Rule 2 verifier: loop-to-iterator
// ---------------------------------------------------------------------------

struct PairInfo {
    s1: usize,
    s2: usize,
    /// All keys of the pair (S1, S2, body subtree, arms).
    keys: BTreeSet<usize>,
    acc: String,
    /// Names bound inside the pair (loop var, ACC) — the shadow-read lens.
    bound: BTreeSet<String>,
    /// New-slot index (document order) — resolves to the after `let` T.
    slot: usize,
}

fn verify_loop_chain(
    cb: &FileCpg<'_>,
    fb: &FnUnit<'_>,
    ca: &FileCpg<'_>,
    fa: &FnUnit<'_>,
    edits: &[&ProposedEdit],
    checks: &mut Vec<String>,
) -> Result<(), CertFailure> {
    let src = cb.src;

    // Locate each pair in the before tree (re-derived from spans, not facts).
    let mut pair_spans: Vec<(ByteSpan, ByteSpan)> = Vec::new();
    let mut infos: Vec<PairInfo> = Vec::new();
    for (slot, edit) in edits.iter().enumerate() {
        let mut found: Option<FoundPair> = None;
        find_pair(&fb.stmts, edit.span, src, &mut found)?;
        let Some((a, b, s1, s2, keys, acc, bound)) = found else {
            return Err(CertFailure::new(
                "site_not_recognized",
                format!(
                    "fn `{}`: no adjacent `let mut` + `for` pair tiles the edit span {}..{}",
                    fb.name, edit.span.start, edit.span.end
                ),
            ));
        };
        pair_spans.push((a, b));
        infos.push(PairInfo {
            s1,
            s2,
            keys,
            acc,
            bound,
            slot,
        });
    }

    let eb = fn_edges(&cb.graph, &fb.fn_id);
    let ea = fn_edges(&ca.graph, &fa.fn_id);

    // Recheck the licensed precondition: no early exit leaves any pair.
    for i in &infos {
        for (f, t, r, _) in &eb.flows {
            if let Nk::S(k) = f {
                if i.keys.contains(k)
                    && matches!(r.as_str(), "break" | "continue" | "return" | "try-exit")
                {
                    return Err(CertFailure::new(
                        "pair_has_early_exit",
                        format!(
                            "fn `{}`: FLOWS_TO role={r} leaves the loop pair (s{k} -> {t})",
                            fb.name
                        ),
                    ));
                }
            }
        }
    }

    // Tree: pair → exactly one `let` statement.
    let expected = shapes_of(fb, src, &Xf::Pairs(&pair_spans));
    let actual = shapes_of(fa, ca.src, &Xf::None);
    let m = align(&fb.name, &expected, &actual, &[])?;
    let mut t_of: BTreeMap<usize, Nk> = BTreeMap::new(); // pair index -> T
    for (idx, info) in infos.iter().enumerate() {
        let Some((ak, kind)) = m.news.get(&info.slot).copied() else {
            return Err(CertFailure::new(
                "tree_remapping_mismatch",
                format!(
                    "fn `{}`: replacement statement for pair {idx} not found",
                    fb.name
                ),
            ));
        };
        if kind != "let" {
            return Err(CertFailure::new(
                "tree_remapping_mismatch",
                format!(
                    "fn `{}`: pair {idx} must collapse to a `let` statement, found `{kind}`",
                    fb.name
                ),
            ));
        }
        t_of.insert(idx, Nk::S(ak));
    }

    let removed_all: BTreeSet<usize> = infos.iter().flat_map(|i| i.keys.clone()).collect();
    let pair_of = |k: usize| -> Option<usize> { infos.iter().position(|i| i.keys.contains(&k)) };
    let surviving = |n: Nk| -> bool {
        match n {
            Nk::Fun | Nk::Exit => true,
            Nk::S(k) => !removed_all.contains(&k),
        }
    };
    let map_surv = |n: Nk, m: &Mapping| -> Result<Nk, CertFailure> {
        m.nk(n).ok_or_else(|| {
            CertFailure::new(
                "cfg_remapping_mismatch",
                format!("fn `{}`: surviving node lost its mapping", fb.name),
            )
        })
    };

    // CFG.
    let mut expected_flows: BTreeSet<FlowEdge> = BTreeSet::new();
    for (f, t, r, b) in &eb.flows {
        let fs = surviving(*f);
        let ts = surviving(*t);
        match (fs, ts) {
            (true, true) => {
                expected_flows.insert((map_surv(*f, &m)?, map_surv(*t, &m)?, r.clone(), b.clone()));
            }
            (true, false) => {
                // Control from a survivor enters a pair only at its S1.
                let Nk::S(k) = t else { unreachable!() };
                let Some(p) = pair_of(*k) else { unreachable!() };
                if infos[p].s1 != *k {
                    return Err(CertFailure::new(
                        "cfg_remapping_mismatch",
                        format!(
                            "fn `{}`: control enters the loop pair at s{k}, not at its \
                             `let` — outside the licensed shape",
                            fb.name
                        ),
                    ));
                }
                expected_flows.insert((map_surv(*f, &m)?, t_of[&p], r.clone(), b.clone()));
            }
            (false, _) => {
                let Nk::S(k) = f else { unreachable!() };
                let Some(p) = pair_of(*k) else { unreachable!() };
                let internal = match t {
                    Nk::S(tk2) => pair_of(*tk2) == Some(p),
                    _ => false,
                };
                if internal {
                    continue; // the pair's internal structure disappears with it
                }
                // The pair's only outward flow is S2's loop exit (possibly
                // rewritten to loop-back by an enclosing loop's join).
                if *k != infos[p].s2 || !matches!(r.as_str(), "loop-exit" | "loop-back") {
                    return Err(CertFailure::new(
                        "cfg_remapping_mismatch",
                        format!(
                            "fn `{}`: unlicensed flow leaves the loop pair: s{k} -> {t} \
                             role={r}",
                            fb.name
                        ),
                    ));
                }
                let role = if r == "loop-back" { "loop-back" } else { "seq" };
                let target = match t {
                    Nk::S(tk2) => match pair_of(*tk2) {
                        Some(q) if infos[q].s1 == *tk2 => t_of[&q],
                        Some(_) => {
                            return Err(CertFailure::new(
                                "cfg_remapping_mismatch",
                                format!(
                                    "fn `{}`: loop exit lands inside another pair at s{tk2}",
                                    fb.name
                                ),
                            ))
                        }
                        None => map_surv(*t, &m)?,
                    },
                    other => map_surv(*other, &m)?,
                };
                expected_flows.insert((t_of[&p], target, role.to_string(), String::new()));
            }
        }
    }
    diff_edges(
        &fb.name,
        "cfg_remapping_mismatch",
        "FLOWS_TO",
        &expected_flows,
        &ea.flows,
        |_| false,
    )?;

    // DFG: the collapse must preserve the external cut exactly.
    let by_key = defs_by_key(fb, src);
    let mut expected_deps: BTreeSet<DepEdge> = BTreeSet::new();
    let mut in_cut = 0usize;
    let mut out_cut = 0usize;
    for (u, d, var, def) in &eb.deps {
        let us = surviving(*u);
        let ds = surviving(*d);
        match (us, ds) {
            (true, true) => {
                let (Some(mu), Some(md)) = (m.nk(*u), m.nk(*d)) else {
                    continue;
                };
                expected_deps.insert((mu, md, var.clone(), def.clone()));
            }
            (false, true) => {
                // Pair reads an outside definition: the in-cut moves to T.
                let Nk::S(k) = u else { unreachable!() };
                let p = pair_of(*k).expect("removed key belongs to a pair");
                expected_deps.insert((t_of[&p], map_surv(*d, &m)?, var.clone(), def.clone()));
                in_cut += 1;
            }
            (true, false) => {
                // A survivor reads a definition inside the pair: licensed only
                // for the accumulator, re-attaching to T with def=let.
                let Nk::S(k) = d else { unreachable!() };
                let p = pair_of(*k).expect("removed key belongs to a pair");
                if *var != infos[p].acc {
                    return Err(CertFailure::new(
                        "dfg_cut_mismatch",
                        format!(
                            "fn `{}`: {u} reads `{var}` from inside the loop pair — only \
                             the accumulator `{}` may escape",
                            fb.name, infos[p].acc
                        ),
                    ));
                }
                expected_deps.insert((map_surv(*u, &m)?, t_of[&p], var.clone(), "let".to_string()));
                out_cut += 1;
            }
            (false, false) => {
                let (Nk::S(ku), Nk::S(kd)) = (u, d) else {
                    unreachable!()
                };
                let (pu, pd) = (pair_of(*ku).unwrap(), pair_of(*kd).unwrap());
                if pu == pd {
                    continue; // internal to one pair: collapses with it
                }
                // One pair's chain reading another pair's accumulator.
                if *var != infos[pd].acc {
                    return Err(CertFailure::new(
                        "dfg_cut_mismatch",
                        format!(
                            "fn `{}`: cross-pair DATA_DEP var={var} outside the licensed \
                             accumulator shape",
                            fb.name
                        ),
                    ));
                }
                expected_deps.insert((t_of[&pu], t_of[&pd], var.clone(), "let".to_string()));
            }
        }
    }
    // Missing edges are never licensed here; extras only via shadow reads.
    if let Some(e) = expected_deps.difference(&ea.deps).next() {
        return Err(CertFailure::new(
            "dfg_cut_mismatch",
            format!(
                "fn `{}`: expected DATA_DEP {} -> {} var={} (def={}) is absent — the \
                 external cut of the collapsed loop changed",
                fb.name, e.0, e.1, e.2, e.3
            ),
        ));
    }
    let mut shadows = 0usize;
    for e in ea.deps.difference(&expected_deps) {
        let from_t = infos
            .iter()
            .enumerate()
            .find(|(idx, i)| t_of[idx] == e.0 && i.bound.contains(&e.2));
        let target_defines = is_def_of_after(e.1, &e.3, &e.2, &m, &by_key);
        if from_t.is_some() && target_defines {
            shadows += 1; // licensed closure-parameter shadow read
            continue;
        }
        return Err(CertFailure::new(
            "dfg_cut_mismatch",
            format!(
                "fn `{}`: unlicensed DATA_DEP {} -> {} var={} appeared after the rewrite",
                fb.name, e.0, e.1, e.2
            ),
        ));
    }

    checks.push(format!(
        "fn `{}` [loop-to-iterator]: {} pair(s) re-derived; each collapsed to one `let` with \
         no early-exit edges; CFG loop structure removed exactly; DFG external cut preserved \
         (in-cut {} edge(s), accumulator out-cut {} edge(s), {} licensed shadow read(s))",
        fb.fn_id,
        infos.len(),
        in_cut,
        out_cut,
        shadows
    ));
    Ok(())
}

/// Does the AFTER node `d` (mapped back to before space where possible) define
/// `var`? Used by the shadow-read allowance.
fn is_def_of_after(
    d: Nk,
    def_kind: &str,
    var: &str,
    m: &Mapping,
    by_key: &BTreeMap<usize, Vec<String>>,
) -> bool {
    match d {
        Nk::Fun => def_kind == "param",
        Nk::Exit => false,
        Nk::S(ak) => {
            let Some((bk, _)) = m.map.iter().find(|(_, a)| **a == ak) else {
                return false;
            };
            is_def_of(Nk::S(*bk), def_kind, var, by_key)
        }
    }
}

/// One located `loop-to-iterator` pair: (S1 span, S2 span, S1 key, S2 key,
/// all pair keys, accumulator name, names bound inside the pair).
type FoundPair = (
    ByteSpan,
    ByteSpan,
    usize,
    usize,
    BTreeSet<usize>,
    String,
    BTreeSet<String>,
);

/// Locate the `let mut` + `for` pair tiling `span` (recursive over blocks).
fn find_pair(
    stmts: &[Stmt<'_>],
    span: ByteSpan,
    src: &str,
    found: &mut Option<FoundPair>,
) -> Result<(), CertFailure> {
    for (i, s) in stmts.iter().enumerate() {
        if s.span.start == span.start && s.kind == StmtKind::Let && found.is_none() {
            if let Some(next) = stmts.get(i + 1) {
                if next.kind == StmtKind::For && next.span.end == span.end {
                    // Re-derive ACC from the `let mut NAME` header.
                    let acc = match (
                        s.header.first().and_then(|e| e.text(src)),
                        s.header.get(1).and_then(|e| e.text(src)),
                        s.header.get(2),
                    ) {
                        (Some("let"), Some("mut"), Some(e)) => match e {
                            crate::ir::cpg::E::T(t)
                                if t.kind == tk::IDENT || t.kind == tk::RAW_IDENT =>
                            {
                                t.span.text(src).to_string()
                            }
                            _ => {
                                return Err(CertFailure::new(
                                    "site_not_recognized",
                                    "the pair's first statement does not bind a single \
                                     `let mut` identifier",
                                ))
                            }
                        },
                        _ => {
                            return Err(CertFailure::new(
                                "site_not_recognized",
                                "the pair's first statement is not `let mut NAME …`",
                            ))
                        }
                    };
                    let mut keys = subtree_keys(std::slice::from_ref(next));
                    keys.extend(subtree_keys(std::slice::from_ref(s)));
                    let mut bound: BTreeSet<String> = BTreeSet::new();
                    bound.insert(acc.clone());
                    if let Some(ix) = top_index(&next.header, "in", src) {
                        bound.extend(pattern_defs(&next.header[..ix], src));
                    }
                    bound.extend(region_defs(&[next], src));
                    *found = Some((
                        s.span,
                        next.span,
                        skey(&s.id).unwrap_or(usize::MAX),
                        skey(&next.id).unwrap_or(usize::MAX),
                        keys,
                        acc,
                        bound,
                    ));
                    return Ok(());
                }
            }
        }
        if let Some(b) = &s.body {
            find_pair(b, span, src, found)?;
        }
        match &s.else_part {
            Some(ElsePart::Block(_, b)) => find_pair(b, span, src, found)?,
            Some(ElsePart::If(n)) => find_pair(std::slice::from_ref(&**n), span, src, found)?,
            None => {}
        }
        for arm in &s.arms {
            if let Some(b) = &arm.block {
                find_pair(b, span, src, found)?;
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Rule 3 verifier: extract-function
// ---------------------------------------------------------------------------

fn verify_extract_fn(
    cb: &FileCpg<'_>,
    fb: &FnUnit<'_>,
    ca: &FileCpg<'_>,
    fa: &FnUnit<'_>,
    edits: &[&ProposedEdit],
    checks: &mut Vec<String>,
) -> Result<(), CertFailure> {
    let src = cb.src;
    let [edit] = edits else {
        return Err(CertFailure::new(
            "site_not_recognized",
            format!(
                "extract-function proposals carry exactly one edit; fn `{}` has {}",
                fb.name,
                edits.len()
            ),
        ));
    };
    let span = edit.span;

    // Locate the run in the before tree.
    let mut run_keys: BTreeSet<usize> = BTreeSet::new();
    let mut run_first: Option<usize> = None;
    let mut run_stmts: Vec<&Stmt<'_>> = Vec::new();
    locate_run(&fb.stmts, span, &mut run_stmts);
    if run_stmts.is_empty() {
        return Err(CertFailure::new(
            "site_not_recognized",
            format!(
                "fn `{}`: no contiguous statement run tiles the edit span {}..{}",
                fb.name, span.start, span.end
            ),
        ));
    }
    for s in &run_stmts {
        run_keys.extend(subtree_keys(std::slice::from_ref(*s)));
    }
    run_first = run_stmts.first().and_then(|s| skey(&s.id)).or(run_first);
    let Some(run_first) = run_first else {
        return Err(CertFailure::new(
            "site_not_recognized",
            "run's first statement has no CPG id",
        ));
    };

    let eb = fn_edges(&cb.graph, &fb.fn_id);
    let ea = fn_edges(&ca.graph, &fa.fn_id);

    // Recheck the licensed precondition: control may not leave the span.
    for (f, t, r, _) in &eb.flows {
        let Nk::S(k) = f else { continue };
        if !run_keys.contains(k) {
            continue;
        }
        let escapes = match r.as_str() {
            "return" | "try-exit" => true,
            "break" | "continue" => match t {
                Nk::S(tk2) => !run_keys.contains(tk2),
                _ => true,
            },
            _ => false,
        };
        if escapes {
            return Err(CertFailure::new(
                "span_jumps_outside",
                format!(
                    "fn `{}`: FLOWS_TO role={r} leaves the span (s{k} -> {t})",
                    fb.name
                ),
            ));
        }
    }

    // Tree: run → exactly [T1: let closure, T2: call].
    let expected = shapes_of(fb, src, &Xf::Run(span));
    let actual = shapes_of(fa, ca.src, &Xf::None);
    let m = align(&fb.name, &expected, &actual, &[])?;
    let (Some((t1k, t1_kind)), Some((t2k, t2_kind))) =
        (m.news.get(&0).copied(), m.news.get(&1).copied())
    else {
        return Err(CertFailure::new(
            "tree_remapping_mismatch",
            format!("fn `{}`: replacement statements not found", fb.name),
        ));
    };
    if t1_kind != "let" || !matches!(t2_kind, "let" | "expr") {
        return Err(CertFailure::new(
            "tree_remapping_mismatch",
            format!(
                "fn `{}`: the run must become a `let` closure plus a call statement, found \
                 `{t1_kind}` + `{t2_kind}`",
                fb.name
            ),
        ));
    }
    let (t1, t2) = (Nk::S(t1k), Nk::S(t2k));

    // The relocated body is verbatim: the run's collapsed text must appear
    // inside the closure statement's collapsed text.
    let t1_span = find_after_span(fa, t1k).ok_or_else(|| {
        CertFailure::new(
            "tree_remapping_mismatch",
            "closure statement span not found",
        )
    })?;
    let run_text = collapse(
        &src[run_stmts[0].span.start as usize..run_stmts[run_stmts.len() - 1].span.end as usize],
    );
    let t1_text = collapse(&ca.src[t1_span.start as usize..t1_span.end as usize]);
    if !t1_text.contains(&run_text) {
        return Err(CertFailure::new(
            "closure_body_not_verbatim",
            format!(
                "fn `{}`: the extracted span's statements do not appear verbatim inside the \
                 closure",
                fb.name
            ),
        ));
    }
    // The closure name, re-derived from the after tree (never the proposal).
    let name = closure_name(fa, t1k, ca.src).ok_or_else(|| {
        CertFailure::new(
            "tree_remapping_mismatch",
            format!(
                "fn `{}`: could not derive the closure's name from the after tree",
                fb.name
            ),
        )
    })?;

    let surviving = |n: Nk| -> bool {
        match n {
            Nk::Fun | Nk::Exit => true,
            Nk::S(k) => !run_keys.contains(&k),
        }
    };
    let map_surv = |n: Nk| -> Result<Nk, CertFailure> {
        m.nk(n).ok_or_else(|| {
            CertFailure::new(
                "cfg_remapping_mismatch",
                format!("fn `{}`: surviving node lost its mapping", fb.name),
            )
        })
    };

    // CFG.
    let mut expected_flows: BTreeSet<FlowEdge> = BTreeSet::new();
    expected_flows.insert((t1, t2, "seq".to_string(), String::new()));
    let mut continuations: BTreeSet<Nk> = BTreeSet::new();
    let mut cont_loopback = false;
    for (f, t, r, b) in &eb.flows {
        match (surviving(*f), surviving(*t)) {
            (true, true) => {
                expected_flows.insert((map_surv(*f)?, map_surv(*t)?, r.clone(), b.clone()));
            }
            (true, false) => {
                let Nk::S(k) = t else { unreachable!() };
                if *k != run_first {
                    return Err(CertFailure::new(
                        "cfg_remapping_mismatch",
                        format!(
                            "fn `{}`: control enters the span at s{k}, not at its first \
                             statement — outside the licensed shape",
                            fb.name
                        ),
                    ));
                }
                expected_flows.insert((map_surv(*f)?, t1, r.clone(), b.clone()));
            }
            (false, true) => {
                continuations.insert(*t);
                cont_loopback |= r == "loop-back";
            }
            (false, false) => {} // internal: relocates into the closure
        }
    }
    if continuations.len() > 1 {
        return Err(CertFailure::new(
            "cfg_remapping_mismatch",
            format!(
                "fn `{}`: the span has {} continuation targets; the licensed shape has one",
                fb.name,
                continuations.len()
            ),
        ));
    }
    if let Some(t) = continuations.first() {
        let role = if cont_loopback { "loop-back" } else { "seq" };
        expected_flows.insert((t2, map_surv(*t)?, role.to_string(), String::new()));
    }
    diff_edges(
        &fb.name,
        "cfg_remapping_mismatch",
        "FLOWS_TO",
        &expected_flows,
        &ea.flows,
        |_| false,
    )?;

    // DFG: the external cut is the parameter/return contract.
    let by_key = defs_by_key(fb, src);
    let run_bound = region_defs(&run_stmts, src);
    // Which vars are PLAIN- or compound-assigned in the run (mutation clause)?
    let mut run_assigned: BTreeSet<String> = BTreeSet::new();
    for s in &run_stmts {
        crate::rewrite::rules::walk_stmt(s, &mut |st| {
            if let (Some(t), _) = assign_target(&st.header, src) {
                run_assigned.insert(t);
            }
        });
    }

    let mut expected_deps: BTreeSet<DepEdge> = BTreeSet::new();
    expected_deps.insert((t2, t1, name.clone(), "let".to_string()));
    let mut mutation_uses: Vec<(Nk, String)> = Vec::new();
    let mut in_cut = 0usize;
    let mut returns = 0usize;
    for (u, d, var, def) in &eb.deps {
        match (surviving(*u), surviving(*d)) {
            (true, true) => {
                let (Some(mu), Some(md)) = (m.nk(*u), m.nk(*d)) else {
                    continue;
                };
                expected_deps.insert((mu, md, var.clone(), def.clone()));
            }
            (false, true) => {
                // In-cut: the closure captures exactly what the span read.
                expected_deps.insert((t1, map_surv(*d)?, var.clone(), def.clone()));
                in_cut += 1;
            }
            (true, false) => {
                // Out-cut: span-local `let` → return through T2; assignment to
                // an outer name → the def relocates behind the closure.
                match def.as_str() {
                    "let" => {
                        expected_deps.insert((map_surv(*u)?, t2, var.clone(), "let".to_string()));
                        returns += 1;
                    }
                    "assign" => {
                        mutation_uses.push((map_surv(*u)?, var.clone()));
                    }
                    other => {
                        return Err(CertFailure::new(
                            "dfg_cut_mismatch",
                            format!(
                                "fn `{}`: {u} reads `{var}` from a def-kind `{other}` site \
                                 inside the span — outside the licensed shape",
                                fb.name
                            ),
                        ));
                    }
                }
            }
            (false, false) => {} // internal to the relocated body
        }
    }
    if let Some(e) = expected_deps.difference(&ea.deps).next() {
        return Err(CertFailure::new(
            "dfg_cut_mismatch",
            format!(
                "fn `{}`: expected DATA_DEP {} -> {} var={} (def={}) is absent — the \
                 span's external cut changed",
                fb.name, e.0, e.1, e.2, e.3
            ),
        ));
    }
    let mut shadows = 0usize;
    for e in ea.deps.difference(&expected_deps) {
        // Licensed extras: (a) shadow reads from T1/T2 of names bound in the
        // run; (b) statement-grain relocation of in-run assignments — reads of
        // an assigned var re-attach to surviving definitions of it.
        let from_new = e.0 == t1 || e.0 == t2;
        let target_defines = is_def_of_after(e.1, &e.3, &e.2, &m, &by_key);
        let shadow = from_new && run_bound.contains(&e.2) && target_defines;
        let mutation = run_assigned.contains(&e.2) && target_defines;
        if shadow || mutation {
            shadows += 1;
            continue;
        }
        return Err(CertFailure::new(
            "dfg_cut_mismatch",
            format!(
                "fn `{}`: unlicensed DATA_DEP {} -> {} var={} appeared after the rewrite",
                fb.name, e.0, e.1, e.2
            ),
        ));
    }
    // Every former reader of an in-span assignment must still read that var.
    for (mu, var) in &mutation_uses {
        let still_reads = ea.deps.iter().any(|(u, _, v, _)| u == mu && v == var);
        if !still_reads {
            return Err(CertFailure::new(
                "mutation_use_lost",
                format!(
                    "fn `{}`: {mu} read `{var}` from an assignment inside the span, but reads \
                     nothing for `{var}` after the rewrite",
                    fb.name
                ),
            ));
        }
    }

    checks.push(format!(
        "fn `{}` [extract-function]: run of {} statement(s) re-derived; no control edge \
         leaves the span; body relocated verbatim into closure `{}`; CFG re-stitched behind \
         the deferred call; DFG cut preserved (captures {} edge(s), returns {} edge(s), \
         {} statement-grain relocation(s))",
        fb.fn_id,
        run_stmts.len(),
        name,
        in_cut,
        returns,
        shadows
    ));
    Ok(())
}

/// Collect the contiguous run of statements tiling `span` (recursive).
fn locate_run<'s, 'a>(stmts: &'s [Stmt<'a>], span: ByteSpan, out: &mut Vec<&'s Stmt<'a>>) {
    if !out.is_empty() {
        return;
    }
    let mut i = 0;
    while i < stmts.len() {
        let s = &stmts[i];
        if s.span.start == span.start {
            let mut j = i;
            while j < stmts.len() && stmts[j].span.end <= span.end {
                j += 1;
            }
            if j > i && stmts[j - 1].span.end == span.end {
                out.extend(&stmts[i..j]);
                return;
            }
        }
        if s.span.start <= span.start && span.end <= s.span.end {
            if let Some(b) = &s.body {
                locate_run(b, span, out);
            }
            match &s.else_part {
                Some(ElsePart::Block(_, b)) => locate_run(b, span, out),
                Some(ElsePart::If(n)) => locate_run(std::slice::from_ref(&**n), span, out),
                None => {}
            }
            for arm in &s.arms {
                if let Some(b) = &arm.block {
                    locate_run(b, span, out);
                }
            }
        }
        i += 1;
    }
}

/// The byte span of the after statement with pre-order key `k`.
fn find_after_span(fa: &FnUnit<'_>, k: usize) -> Option<ByteSpan> {
    let mut found = None;
    crate::rewrite::rules::walk_stmts(&fa.stmts, &mut |s| {
        if skey(&s.id) == Some(k) {
            found = Some(s.span);
        }
    });
    found
}

/// The name bound by the after `let` statement with key `k` (`let [mut] NAME`).
fn closure_name(fa: &FnUnit<'_>, k: usize, src: &str) -> Option<String> {
    let mut name = None;
    crate::rewrite::rules::walk_stmts(&fa.stmts, &mut |s| {
        if skey(&s.id) != Some(k) || s.kind != StmtKind::Let {
            return;
        }
        let idx = if s.header.get(1).and_then(|e| e.text(src)) == Some("mut") {
            2
        } else {
            1
        };
        if let Some(crate::ir::cpg::E::T(t)) = s.header.get(idx) {
            if t.kind == tk::IDENT || t.kind == tk::RAW_IDENT {
                name = Some(t.span.text(src).to_string());
            }
        }
    });
    name
}

// ---------------------------------------------------------------------------
// Rule 4 verifier: redundant-clone-elim
// ---------------------------------------------------------------------------
//
// The strongest licensed remapping of the catalog: NONE. The after tree must
// equal the before tree with only the `.clone()` bytes deleted from each site
// statement's text, and the after CPG (control flow AND data flow) must be
// IDENTICAL to the before CPG under the resulting 1:1 statement mapping — the
// site statement still reads the binding (a move reads exactly like a copy at
// statement grain), and `clone` itself is a method name the DFG never records.
// The safety precondition — the last-use proof — is re-derived entirely from
// the BEFORE graph: `DATA_DEP` is conservative may-reach def-use (ADR-0003),
// so an over-approximation that shows NO reader of the binding's definition
// among the statements CFG-reachable after the site can only err by inventing
// readers (refusing valid sites), never by missing one.

/// One re-derived clone-elimination site.
struct CloneSite {
    /// The site statement's pre-order key.
    key: usize,
    /// The cloned binding.
    var: String,
    /// The single reaching definition's key.
    def: usize,
}

fn verify_clone_elim(
    cb: &FileCpg<'_>,
    fb: &FnUnit<'_>,
    ca: &FileCpg<'_>,
    fa: &FnUnit<'_>,
    edits: &[&ProposedEdit],
    checks: &mut Vec<String>,
) -> Result<(), CertFailure> {
    let src = cb.src;
    let eb = fn_edges(&cb.graph, &fb.fn_id);
    let ea = fn_edges(&ca.graph, &fa.fn_id);
    let loop_keys = loop_body_keys(&fb.stmts);

    // Re-derive each site from the before tree + graph — never from the
    // proposal's claims.
    let mut sites: Vec<CloneSite> = Vec::new();
    // Site statement key → the `.clone()` spans deleted from its text.
    let mut excised: BTreeMap<usize, Vec<ByteSpan>> = BTreeMap::new();
    for edit in edits {
        let stmt = innermost_stmt(&fb.stmts, edit.span).ok_or_else(|| {
            CertFailure::new(
                "site_not_recognized",
                format!(
                    "fn `{}`: no statement contains the edit span {}..{}",
                    fb.name, edit.span.start, edit.span.end
                ),
            )
        })?;
        let key = skey(&stmt.id).ok_or_else(|| {
            CertFailure::new(
                "site_not_recognized",
                format!("fn `{}`: the containing statement has no CPG node", fb.name),
            )
        })?;
        // The statement's SHAPE must recognize exactly this span (RHS-exact
        // `let` or plain path-call argument) — re-derived, not trusted.
        let sites_here = crate::rewrite::rules::clone_elim::recognized_sites(stmt, src);
        let Some((var, _)) = sites_here.iter().find(|(_, sp)| *sp == edit.span) else {
            return Err(CertFailure::new(
                "site_not_recognized",
                format!(
                    "fn `{}`: bytes {}..{} are not a recognized `x.clone()` site (RHS of a \
                     `let` or a whole argument of a plain path call)",
                    fb.name, edit.span.start, edit.span.end
                ),
            ));
        };
        if loop_keys.contains(&key) {
            return Err(CertFailure::new(
                "clone_in_loop",
                format!(
                    "fn `{}`: statement s{key} sits inside a loop body — the clone may \
                     execute repeatedly and the move is only legal once",
                    fb.name
                ),
            ));
        }
        if crate::rewrite::rules::clone_elim::count_ident(stmt, var, src) != 1 {
            return Err(CertFailure::new(
                "receiver_reused_in_statement",
                format!(
                    "fn `{}`: `{var}` occurs more than once in statement s{key}",
                    fb.name
                ),
            ));
        }
        // Exactly one reaching definition, of kind `let`, at a statement.
        let defs: BTreeSet<(Nk, String)> = eb
            .deps
            .iter()
            .filter(|(u, _, v, _)| *u == Nk::S(key) && v == var)
            .map(|(_, d, _, k)| (*d, k.clone()))
            .collect();
        let def = match defs.iter().next() {
            Some((Nk::S(d), kind)) if defs.len() == 1 && kind == "let" => *d,
            _ => {
                return Err(CertFailure::new(
                    "receiver_def_not_single_let",
                    format!(
                        "fn `{}`: `{var}` at s{key} must have exactly one reaching \
                         definition of kind `let`; the before graph records {:?}",
                        fb.name, defs
                    ),
                ));
            }
        };
        let def_ok = find_stmt_by_key(&fb.stmts, def)
            .is_some_and(|d| crate::rewrite::rules::clone_elim::bare_let_binds(d, var, src));
        if !def_ok {
            return Err(CertFailure::new(
                "receiver_def_not_bare_let",
                format!(
                    "fn `{}`: definition s{def} of `{var}` is not a bare \
                     `let [mut] {var} …` binding",
                    fb.name
                ),
            ));
        }
        // THE LAST-USE PROOF: no statement CFG-reachable after the site reads
        // the definition. May-reach DATA_DEP over-approximates readers, so an
        // empty set here is sound evidence.
        let after = flow_successors(&eb, Nk::S(key));
        for (u, d, v, _) in &eb.deps {
            if *d == Nk::S(def) && v == var && *u != Nk::S(key) && after.contains(u) {
                return Err(CertFailure::new(
                    "cloned_value_read_later",
                    format!(
                        "fn `{}`: {u} reads `{var}` (DATA_DEP -> s{def}) and is reachable \
                         after the clone at s{key} — the clone is not the last use",
                        fb.name
                    ),
                ));
            }
        }
        sites.push(CloneSite {
            key,
            var: var.clone(),
            def,
        });
        excised.entry(key).or_default().push(edit.span);
    }

    // Tree: identical except each site statement's text loses exactly its
    // `.clone()` bytes.
    let mut expected = shapes_of(fb, src, &Xf::None);
    for sh in &mut expected {
        if let Shape::Node {
            key: Some(k),
            text,
            span,
            ..
        } = sh
        {
            if let Some(spans) = excised.get(k) {
                *text = collapse(&excise_spans(src, *span, spans));
            }
        }
    }
    let actual = shapes_of(fa, ca.src, &Xf::None);
    let m = align(&fb.name, &expected, &actual, &[])?;

    // Graphs: ZERO delta. Every before edge maps 1:1 and nothing appears.
    let map_edge = |e: &FlowEdge| -> Result<FlowEdge, CertFailure> {
        match (m.nk(e.0), m.nk(e.1)) {
            (Some(a), Some(b)) => Ok((a, b, e.2.clone(), e.3.clone())),
            _ => Err(CertFailure::new(
                "tree_remapping_mismatch",
                format!("fn `{}`: statement lost its mapping", fb.name),
            )),
        }
    };
    let expected_flows: BTreeSet<FlowEdge> =
        eb.flows.iter().map(&map_edge).collect::<Result<_, _>>()?;
    let expected_deps: BTreeSet<DepEdge> =
        eb.deps.iter().map(&map_edge).collect::<Result<_, _>>()?;
    diff_edges(
        &fb.name,
        "cfg_remapping_mismatch",
        "FLOWS_TO",
        &expected_flows,
        &ea.flows,
        |_| false,
    )?;
    diff_edges(
        &fb.name,
        "dfg_remapping_mismatch",
        "DATA_DEP",
        &expected_deps,
        &ea.deps,
        |_| false,
    )?;

    let described: Vec<String> = sites
        .iter()
        .map(|s| format!("`{}` at s{} (def s{})", s.var, s.key, s.def))
        .collect();
    checks.push(format!(
        "fn `{}` [redundant-clone-elim]: {} site(s) re-derived as proven last uses \
         ({}); no reader of any cloned binding is CFG-reachable after its site; after \
         CPG identical to before under the 1:1 statement mapping — FLOWS_TO and \
         DATA_DEP unchanged, only the `.clone()` call text deleted",
        fb.fn_id,
        sites.len(),
        described.join(", ")
    ));
    Ok(())
}

/// The statement (any depth) with the smallest span containing `span`.
fn innermost_stmt<'s, 'a>(stmts: &'s [Stmt<'a>], span: ByteSpan) -> Option<&'s Stmt<'a>> {
    let mut best: Option<&'s Stmt<'a>> = None;
    crate::rewrite::rules::walk_stmts(stmts, &mut |s| {
        if s.span.start <= span.start && span.end <= s.span.end {
            let tighter =
                best.is_none_or(|b| (s.span.end - s.span.start) < (b.span.end - b.span.start));
            if tighter {
                best = Some(s);
            }
        }
    });
    best
}

/// Find a statement (any depth) by pre-order key.
fn find_stmt_by_key<'s, 'a>(stmts: &'s [Stmt<'a>], key: usize) -> Option<&'s Stmt<'a>> {
    let mut found: Option<&'s Stmt<'a>> = None;
    crate::rewrite::rules::walk_stmts(stmts, &mut |s| {
        if found.is_none() && skey(&s.id) == Some(key) {
            found = Some(s);
        }
    });
    found
}

/// Keys of every statement (and arm) that sits inside a loop body.
fn loop_body_keys(stmts: &[Stmt<'_>]) -> BTreeSet<usize> {
    fn walk(stmts: &[Stmt<'_>], in_loop: bool, out: &mut BTreeSet<usize>) {
        for s in stmts {
            stmt(s, in_loop, out);
        }
    }
    fn stmt(s: &Stmt<'_>, in_loop: bool, out: &mut BTreeSet<usize>) {
        if in_loop {
            if let Some(k) = skey(&s.id) {
                out.insert(k);
            }
        }
        let body_in = in_loop || matches!(s.kind, StmtKind::For | StmtKind::While | StmtKind::Loop);
        if let Some(b) = &s.body {
            walk(b, body_in, out);
        }
        match &s.else_part {
            Some(ElsePart::Block(_, b)) => walk(b, in_loop, out),
            Some(ElsePart::If(nested)) => stmt(nested, in_loop, out),
            None => {}
        }
        for arm in &s.arms {
            if in_loop {
                if let Some(k) = skey(&arm.id) {
                    out.insert(k);
                }
            }
            if let Some(b) = &arm.block {
                walk(b, in_loop, out);
            }
        }
    }
    let mut out = BTreeSet::new();
    walk(stmts, false, &mut out);
    out
}

/// Nodes reachable from `start` via one or more `FLOWS_TO` edges. The CFG is
/// syntactic (every branch present), so this OVER-approximates "can execute
/// after" — the safe direction for a refusal check.
fn flow_successors(edges: &FnEdges, start: Nk) -> BTreeSet<Nk> {
    let mut seen: BTreeSet<Nk> = BTreeSet::new();
    let mut queue: Vec<Nk> = vec![start];
    while let Some(n) = queue.pop() {
        for (f, t, _, _) in &edges.flows {
            if *f == n && seen.insert(*t) {
                queue.push(*t);
            }
        }
    }
    seen
}

/// The text of `stmt_span` with the byte ranges in `cuts` removed.
fn excise_spans(src: &str, stmt_span: ByteSpan, cuts: &[ByteSpan]) -> String {
    let mut sorted: Vec<ByteSpan> = cuts.to_vec();
    sorted.sort_by_key(|s| s.start);
    let mut out = String::new();
    let mut cursor = stmt_span.start as usize;
    for c in sorted {
        let (s, e) = (c.start as usize, c.end as usize);
        if s >= cursor && e <= stmt_span.end as usize {
            out.push_str(&src[cursor..s]);
            cursor = e;
        }
    }
    out.push_str(&src[cursor..stmt_span.end as usize]);
    out
}

// ---------------------------------------------------------------------------
// Rule 6 verifier: slice-param
// ---------------------------------------------------------------------------
//
// Like redundant-clone-elim, the licensed remapping is NONE — and stronger
// still: the edit rewrites a parameter TYPE in the signature, outside every
// statement span, so not even a statement's text may change. The after CPG
// (shape, control flow, data flow) must be IDENTICAL to the before CPG under
// the identity statement mapping. The preconditions are re-proved from the
// before tree and graph, never taken from the proposal: the edit span must
// be a recognized `&[lifetime] Vec<T>` / `&[lifetime] String` parameter
// site, the replacement must be the licensed emission for that site, every
// occurrence of the parameter in the body must be a slice/str-safe use, and
// the enclosing function must never be taken as a first-class value in the
// file (deref coercion covers direct calls only).

fn verify_slice_param(
    cb: &FileCpg<'_>,
    fb: &FnUnit<'_>,
    ca: &FileCpg<'_>,
    fa: &FnUnit<'_>,
    edits: &[&ProposedEdit],
    checks: &mut Vec<String>,
) -> Result<(), CertFailure> {
    use crate::rewrite::rules::slice_param;

    let src = cb.src;
    // Re-derive the recognized parameter sites from the before signature —
    // never from the proposal's claims.
    let sites = slice_param::recognized_param_sites(fb, src);
    let mut described: Vec<String> = Vec::new();
    for edit in edits {
        let Some(site) = sites.iter().find(|s| s.span == edit.span) else {
            return Err(CertFailure::new(
                "site_not_recognized",
                format!(
                    "fn `{}`: bytes {}..{} are not a recognized `&[lifetime] Vec<T>` / \
                     `&[lifetime] String` parameter type of the signature",
                    fb.name, edit.span.start, edit.span.end
                ),
            ));
        };
        if edit.after != site.after {
            return Err(CertFailure::new(
                "replacement_not_licensed",
                format!(
                    "fn `{}`: the licensed replacement for parameter `{}` is `{}`, the \
                     proposal writes `{}`",
                    fb.name, site.name, site.after, edit.after
                ),
            ));
        }
        // Deref coercion covers direct calls only: the function must never be
        // taken as a first-class value anywhere in the file.
        if let Some(off) = slice_param::fn_value_use(src, &fb.name) {
            return Err(CertFailure::new(
                "function_used_as_value",
                format!(
                    "`{}` is used as a first-class value at byte {off} (not a direct \
                     call); a fn-pointer/closure position is not coercion-compatible \
                     with the changed parameter type",
                    fb.name
                ),
            ));
        }
        // Every occurrence of the parameter must be a slice/str-safe use —
        // re-proved token-by-token from the before tree.
        if let Err((check, detail)) = slice_param::licensed_uses(fb, src, site) {
            return Err(CertFailure::new(
                check,
                format!("fn `{}`: {detail}", fb.name),
            ));
        }
        described.push(format!("`{}` -> `{}`", site.name, site.after));
    }

    // Tree: identical — the edits live in the signature, outside every
    // statement span, so no statement's kind, text, or nesting may change.
    let expected = shapes_of(fb, src, &Xf::None);
    let actual = shapes_of(fa, ca.src, &Xf::None);
    let m = align(&fb.name, &expected, &actual, &[])?;

    // Graphs: ZERO delta. Every before edge maps 1:1 and nothing appears.
    let eb = fn_edges(&cb.graph, &fb.fn_id);
    let ea = fn_edges(&ca.graph, &fa.fn_id);
    let map_edge = |e: &FlowEdge| -> Result<FlowEdge, CertFailure> {
        match (m.nk(e.0), m.nk(e.1)) {
            (Some(a), Some(b)) => Ok((a, b, e.2.clone(), e.3.clone())),
            _ => Err(CertFailure::new(
                "tree_remapping_mismatch",
                format!("fn `{}`: statement lost its mapping", fb.name),
            )),
        }
    };
    let expected_flows: BTreeSet<FlowEdge> =
        eb.flows.iter().map(&map_edge).collect::<Result<_, _>>()?;
    let expected_deps: BTreeSet<DepEdge> =
        eb.deps.iter().map(&map_edge).collect::<Result<_, _>>()?;
    diff_edges(
        &fb.name,
        "cfg_remapping_mismatch",
        "FLOWS_TO",
        &expected_flows,
        &ea.flows,
        |_| false,
    )?;
    diff_edges(
        &fb.name,
        "dfg_remapping_mismatch",
        "DATA_DEP",
        &expected_deps,
        &ea.deps,
        |_| false,
    )?;

    checks.push(format!(
        "fn `{}` [slice-param]: {} parameter site(s) re-derived as slice/str-safe \
         generalizations ({}); every parameter use resolves through Deref to the \
         identical slice/str implementation and the function is never taken as a \
         first-class value; after CPG identical to before under the identity \
         statement mapping — the edit lives in the signature, outside every \
         statement span",
        fb.fn_id,
        described.len(),
        described.join(", ")
    ));
    Ok(())
}

// ---------------------------------------------------------------------------
// Layer 2b: licensed-emission replay
// ---------------------------------------------------------------------------

fn replay(
    src: &str,
    proposal: &Proposal,
    cb: &FileCpg<'_>,
    _checks: &mut [String],
) -> Result<(), CertFailure> {
    let rule = rule_by_id(&proposal.rule_id).ok_or_else(|| {
        CertFailure::new(
            "unknown_rule",
            format!(
                "rule `{}` is not registered in this build",
                proposal.rule_id
            ),
        )
    })?;
    if rule.version() != proposal.rule_version {
        return Err(CertFailure::new(
            "rule_version_mismatch",
            format!(
                "this build ships {} v{}, the proposal was made by v{} — re-propose",
                rule.id(),
                rule.version(),
                proposal.rule_version
            ),
        ));
    }
    let opts = if rule.requires_lines() {
        // Reconstruct the targeting options from the edit itself: the run's
        // line range from its span, the name from the emitted closure `let`.
        let e = &proposal.edits[0];
        let la = crate::rewrite::rules::line_of(src, e.span.start as usize);
        let lb = crate::rewrite::rules::line_of(src, (e.span.end as usize).saturating_sub(1));
        let name = emitted_let_name(&e.after);
        RuleOptions {
            lines: Some((la, lb)),
            name,
        }
    } else {
        RuleOptions::default()
    };
    let outcome = rule.propose(cb, &opts).map_err(|e| {
        CertFailure::new(
            "replay_mismatch",
            format!("re-running the recognizer failed: {e}"),
        )
    })?;
    for (k, e) in proposal.edits.iter().enumerate() {
        let matched = outcome
            .edits
            .iter()
            .any(|r| r.span == e.span && r.before == e.before && r.after == e.after);
        if !matched {
            return Err(CertFailure::new(
                "replay_mismatch",
                format!(
                    "edit {k} (bytes {}..{}) is not byte-identical to any edit this binary's \
                     {} v{} emits for the original file — the after text is not the licensed \
                     emission",
                    e.span.start,
                    e.span.end,
                    rule.id(),
                    rule.version()
                ),
            ));
        }
    }
    Ok(())
}

/// `let [mut] NAME` prefix of an emitted replacement (replay reconstruction).
fn emitted_let_name(after: &str) -> Option<String> {
    let rest = after.trim_start().strip_prefix("let ")?;
    let rest = rest.trim_start();
    let rest = rest.strip_prefix("mut ").unwrap_or(rest).trim_start();
    let end = rest
        .find(|c: char| !(c == '_' || c.is_ascii_alphanumeric()))
        .unwrap_or(rest.len());
    if end == 0 {
        return None;
    }
    Some(rest[..end].to_string())
}

// ---------------------------------------------------------------------------
// Rule 5 verifier: if-let-to-match
// ---------------------------------------------------------------------------

struct IfLetInfo {
    key: usize,
    /// Whitespace-collapsed pattern text (the first arm's expected pattern).
    pat: String,
    /// New-slot index of the pattern arm; the `_` arm is `slot + 1`.
    slot: usize,
}

/// Find and re-derive the target `if let … else { … }` of one edit: span
/// identity, `let` header, block else-part, and the place-expression
/// scrutinee — all recomputed from the tree, never trusted from the proposal.
fn find_if_let_target<'s, 'a>(
    fb: &'s FnUnit<'a>,
    src: &str,
    edit: &ProposedEdit,
) -> Result<(&'s Stmt<'a>, usize), CertFailure> {
    let mut found: Option<&'s Stmt<'a>> = None;
    crate::rewrite::rules::walk_stmts(&fb.stmts, &mut |s| {
        if s.kind == StmtKind::If && s.span == edit.span && found.is_none() {
            found = Some(s);
        }
    });
    let s = found.ok_or_else(|| {
        CertFailure::new(
            "site_not_recognized",
            format!(
                "no `if` statement matches the edit span {}..{}",
                edit.span.start, edit.span.end
            ),
        )
    })?;
    if s.header.first().and_then(|e| e.text(src)) != Some("let") {
        return Err(CertFailure::new(
            "site_not_recognized",
            "the target `if` condition is not an `if let`".to_string(),
        ));
    }
    if s.header
        .iter()
        .filter(|e| e.text(src) == Some("let"))
        .count()
        > 1
    {
        return Err(CertFailure::new(
            "site_not_recognized",
            "the target condition chains more than one `let`".to_string(),
        ));
    }
    if !matches!(&s.else_part, Some(ElsePart::Block(_, _))) {
        return Err(CertFailure::new(
            "site_not_recognized",
            "the target `if let` has no block else-part".to_string(),
        ));
    }
    let eq = s
        .header
        .iter()
        .position(|e| e.text(src) == Some("="))
        .filter(|&i| i > 1 && i + 1 < s.header.len())
        .ok_or_else(|| {
            CertFailure::new(
                "site_not_recognized",
                "the target `if let` header has no top-level `=`".to_string(),
            )
        })?;
    let place = s.header[eq + 1..].iter().all(|e| match e {
        crate::ir::cpg::E::G(_) => false,
        crate::ir::cpg::E::T(t) => {
            t.kind == tk::IDENT
                || t.kind == tk::RAW_IDENT
                || t.kind == tk::INT
                || matches!(t.span.text(src), "." | "::" | "self")
        }
    });
    if !place {
        return Err(CertFailure::new(
            "site_not_recognized",
            "the target scrutinee is not a place expression — a non-place may create \
             temporaries whose drop order differs between `if let` and `match`"
                .to_string(),
        ));
    }
    Ok((s, eq))
}

fn verify_if_let_match(
    cb: &FileCpg<'_>,
    fb: &FnUnit<'_>,
    ca: &FileCpg<'_>,
    fa: &FnUnit<'_>,
    edits: &[&ProposedEdit],
    checks: &mut Vec<String>,
) -> Result<(), CertFailure> {
    let src = cb.src;
    let mut sites: Vec<IfLetSite> = Vec::new();
    let mut infos: Vec<IfLetInfo> = Vec::new();
    for edit in edits {
        let (s, eq) = find_if_let_target(fb, src, edit)?;
        let key = skey(&s.id).ok_or_else(|| {
            CertFailure::new("site_not_recognized", "target statement has no CPG id")
        })?;
        sites.push(IfLetSite {
            span: s.span,
            scrut: collapse(crate::ir::cpg::span_of(&s.header[eq + 1..]).text(src)),
        });
        infos.push(IfLetInfo {
            key,
            pat: collapse(crate::ir::cpg::span_of(&s.header[1..eq]).text(src)),
            slot: 0,
        });
    }
    // Slot order = shape-emission order = pre-order = span order.
    let mut order: Vec<usize> = (0..sites.len()).collect();
    order.sort_by_key(|&i| (sites[i].span.start, sites[i].span.end));
    for (j, &i) in order.iter().enumerate() {
        infos[i].slot = 2 * j;
    }

    let expected = shapes_of(fb, src, &Xf::IfLet(&sites));
    let actual = shapes_of(fa, ca.src, &Xf::None);
    let m = align(&fb.name, &expected, &actual, &[])?;

    // Arm nodes: the two New slots per site must be arm nodes of the mapped
    // match statement, in pattern-then-wildcard order, both block-bodied.
    let mut arm_pat_of: BTreeMap<usize, Nk> = BTreeMap::new(); // before key -> arm node
    let mut arm_wild_of: BTreeMap<usize, Nk> = BTreeMap::new();
    for info in &infos {
        let mk = *m.map.get(&info.key).ok_or_else(|| {
            CertFailure::new(
                "tree_remapping_mismatch",
                format!("fn `{}`: rewritten `if let` lost its mapping", fb.name),
            )
        })?;
        let mut arm_keys = [0usize; 2];
        for (i, k) in arm_keys.iter_mut().enumerate() {
            let (ak, kind) = m.news.get(&(info.slot + i)).copied().ok_or_else(|| {
                CertFailure::new(
                    "tree_remapping_mismatch",
                    format!("fn `{}`: replacement arm {i} not found", fb.name),
                )
            })?;
            if kind != "arm" {
                return Err(CertFailure::new(
                    "tree_remapping_mismatch",
                    format!(
                        "fn `{}`: replacement slot {i} must be a match arm, found `{kind}`",
                        fb.name
                    ),
                ));
            }
            *k = ak;
        }
        // Re-derive the after match statement and pin its arm shape.
        let mut after_stmt: Option<&Stmt<'_>> = None;
        crate::rewrite::rules::walk_stmts(&fa.stmts, &mut |s| {
            if skey(&s.id) == Some(mk) && after_stmt.is_none() {
                after_stmt = Some(s);
            }
        });
        let a = after_stmt.ok_or_else(|| {
            CertFailure::new(
                "tree_remapping_mismatch",
                format!("fn `{}`: mapped match statement s{mk} not found", fb.name),
            )
        })?;
        if a.kind != StmtKind::Match || a.arms.len() != 2 {
            return Err(CertFailure::new(
                "tree_remapping_mismatch",
                format!(
                    "fn `{}`: the rewritten statement must be a two-arm `match`",
                    fb.name
                ),
            ));
        }
        let pat0 = collapse(crate::ir::cpg::span_of(&a.arms[0].pattern).text(ca.src));
        let pat1 = collapse(crate::ir::cpg::span_of(&a.arms[1].pattern).text(ca.src));
        if pat0
            != infos
                .iter()
                .find(|i| i.key == info.key)
                .map(|i| i.pat.clone())
                .unwrap_or_default()
            || pat1 != "_"
        {
            return Err(CertFailure::new(
                "tree_remapping_mismatch",
                format!(
                    "fn `{}`: match arms must be `{}` then `_`, found `{pat0}` then `{pat1}`",
                    fb.name,
                    infos
                        .iter()
                        .find(|i| i.key == info.key)
                        .map(|i| i.pat.clone())
                        .unwrap_or_default()
                ),
            ));
        }
        if a.arms[0].block.is_none() || a.arms[1].block.is_none() {
            return Err(CertFailure::new(
                "tree_remapping_mismatch",
                format!("fn `{}`: both match arms must be block-bodied", fb.name),
            ));
        }
        if skey(&a.arms[0].id) != Some(arm_keys[0]) || skey(&a.arms[1].id) != Some(arm_keys[1]) {
            return Err(CertFailure::new(
                "tree_remapping_mismatch",
                format!(
                    "fn `{}`: match arm nodes do not line up with the licensed slots",
                    fb.name
                ),
            ));
        }
        arm_pat_of.insert(info.key, Nk::S(arm_keys[0]));
        arm_wild_of.insert(info.key, Nk::S(arm_keys[1]));
    }

    let site_of = |k: usize| infos.iter().find(|i| i.key == k);
    let map_all = |n: Nk| -> Result<Nk, CertFailure> {
        m.nk(n).ok_or_else(|| {
            CertFailure::new(
                "cfg_remapping_mismatch",
                format!("fn `{}`: node lost its mapping", fb.name),
            )
        })
    };

    let eb = fn_edges(&cb.graph, &fb.fn_id);
    let ea = fn_edges(&ca.graph, &fa.fn_id);

    // CFG: every before edge survives m-mapped, except a site's two branch
    // departures, each of which is re-anchored THROUGH its arm node:
    // `S --branch/then--> T` becomes `M --branch/arm--> ARM_PAT` plus
    // `ARM_PAT --seq--> T'` (role `loop-back` carried through when the
    // loop-closing join had rewritten the departure).
    let mut expected_flows: BTreeSet<FlowEdge> = BTreeSet::new();
    for (f, t, r, b) in &eb.flows {
        if let Nk::S(k) = f {
            if let Some(info) = site_of(*k) {
                if b == "then" || b == "else" {
                    let arm = if b == "then" {
                        arm_pat_of[&info.key]
                    } else {
                        arm_wild_of[&info.key]
                    };
                    expected_flows.insert((
                        map_all(*f)?,
                        arm,
                        "branch".to_string(),
                        "arm".to_string(),
                    ));
                    let role = if r == "loop-back" { "loop-back" } else { "seq" };
                    expected_flows.insert((arm, map_all(*t)?, role.to_string(), String::new()));
                    continue;
                }
                return Err(CertFailure::new(
                    "cfg_remapping_mismatch",
                    format!(
                        "fn `{}`: unlicensed departure from the `if let` site: s{k} -> {t} \
                         role={r} branch={b}",
                        fb.name
                    ),
                ));
            }
        }
        expected_flows.insert((map_all(*f)?, map_all(*t)?, r.clone(), b.clone()));
    }
    diff_edges(
        &fb.name,
        "cfg_remapping_mismatch",
        "FLOWS_TO",
        &expected_flows,
        &ea.flows,
        |_| false,
    )?;

    // DFG (edges run reader → def-site): the site's own reads — the
    // scrutinee — stay on the (now match) node and m-map unchanged; reads OF
    // the site's pattern bindings re-attach their def end from the `if` node
    // to the pattern arm. Nothing else may appear or disappear.
    let mut expected_deps: BTreeSet<DepEdge> = BTreeSet::new();
    for (u, d, var, def) in &eb.deps {
        if let Nk::S(k) = d {
            if let Some(info) = site_of(*k) {
                if def != "pattern" {
                    return Err(CertFailure::new(
                        "dfg_remapping_mismatch",
                        format!(
                            "fn `{}`: unlicensed DATA_DEP var={var} (def={def}) defined at \
                             the `if let` site",
                            fb.name
                        ),
                    ));
                }
                expected_deps.insert((
                    map_all(*u)?,
                    arm_pat_of[&info.key],
                    var.clone(),
                    def.clone(),
                ));
                continue;
            }
        }
        expected_deps.insert((map_all(*u)?, map_all(*d)?, var.clone(), def.clone()));
    }
    diff_edges(
        &fb.name,
        "dfg_remapping_mismatch",
        "DATA_DEP",
        &expected_deps,
        &ea.deps,
        |_| false,
    )?;

    checks.push(format!(
        "fn `{}` [if-let-to-match]: {} site(s) re-derived (place scrutinee re-proved); each \
         `if let` node became the `match` node with its two licensed arm nodes; branch \
         departures re-anchored through the arms exactly; scrutinee reads unchanged and \
         pattern defs re-attached to the pattern arm",
        fb.fn_id,
        infos.len(),
    ));
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rewrite::rules::all_rules;

    /// Run `propose` for `rule` on `src` and wrap the outcome as a proposal.
    fn propose(rule_id: &str, src: &str, opts: RuleOptions) -> Proposal {
        let tree = parse("t.rs", src);
        assert!(tree.is_lossless());
        assert!(tree.diagnostics.is_empty());
        let ctx = analyze_file(&tree);
        let rule = rule_by_id(rule_id).expect("rule registered");
        let outcome = rule.propose(&ctx, &opts).expect("propose");
        Proposal {
            rule_id: rule.id().to_string(),
            rule_version: rule.version().to_string(),
            dir: ".".to_string(),
            file: "t.rs".to_string(),
            file_fingerprint: fingerprint(src.as_bytes()),
            edits: outcome.edits,
            rejections: outcome.rejections,
        }
    }

    fn assert_fails(src: &str, p: &Proposal, check: &str) -> CertFailure {
        let err = certify(src, p).expect_err("corrupted proposal must fail verification");
        assert_eq!(err.check, check, "wrong failure reason: {err}");
        err
    }

    // --- valid applications must certify -------------------------------------

    #[test]
    fn dead_branch_valid_cert_verifies() {
        let src = "fn f() {\n    if true {\n        a();\n        b();\n    } else {\n        c();\n    }\n    done();\n}\n\nfn untouched(x: i32) -> i32 {\n    x + 1\n}\n";
        let p = propose("dead-branch-elim", src, RuleOptions::default());
        assert_eq!(p.edits.len(), 1);
        let cert = certify(src, &p).expect("valid rewrite must certify");
        assert_eq!(cert.rule_id, "dead-branch-elim");
        assert_eq!(cert.affected, vec!["fn::f#1".to_string()]);
        assert_eq!(cert.unaffected_verified, 1);
        assert_eq!(cert.proposal_hash, p.hash());
        assert!(cert.checks.iter().any(|c| c.contains("dead-branch-elim")));
        assert!(cert.obligation_kani.contains("k3c_dead_branch_schema"));
    }

    #[test]
    fn dead_branch_else_position_and_removal_certify() {
        for src in [
            // else-if true keeps braces
            "fn f(c: bool) {\n    if c { a(); } else if true { b(); } else { d(); }\n}\n",
            // if false without else removes the statement
            "fn f() {\n    if false { a(); }\n    done();\n}\n",
            // if false with else-if keeps the chain
            "fn f(c: bool) {\n    if false { a(); } else if c { b(); } else { d(); }\n}\n",
            // dangling else dropped
            "fn f(c: bool) {\n    if c { a(); } else if false { b(); }\n}\n",
            // inside a loop (loop-back re-stitch)
            "fn f(xs: Vec<i32>) {\n    for x in xs {\n        if true { use_it(x); }\n    }\n}\n",
        ] {
            let p = propose("dead-branch-elim", src, RuleOptions::default());
            assert_eq!(p.edits.len(), 1, "{src}");
            certify(src, &p).unwrap_or_else(|e| panic!("{src}: {e}"));
        }
    }

    #[test]
    fn dead_branch_kill_shift_is_justified_shrinkage() {
        // Before: use(x) may read both defs; after the splice the assignment
        // always runs and kills the let — a licensed shrink.
        let src = "fn f() {\n    let mut x = 1;\n    if true {\n        x = 2;\n    }\n    use_it(x);\n}\n";
        let p = propose("dead-branch-elim", src, RuleOptions::default());
        assert_eq!(p.edits.len(), 1);
        let cert = certify(src, &p).expect("kill-shift is licensed shrinkage");
        assert!(
            cert.checks.iter().any(|c| c.contains("1 shrunk")),
            "{:?}",
            cert.checks
        );
    }

    #[test]
    fn loop_chain_valid_certs_verify() {
        for src in [
            "fn f(xs: Vec<i32>) {\n    let mut out = Vec::new();\n    for x in xs {\n        out.push(x * 2);\n    }\n    use_it(out);\n}\n",
            "fn f(xs: Vec<i32>) {\n    let mut sum = 0;\n    for x in xs {\n        sum += x;\n    }\n    use_it(sum);\n}\n",
            "fn f(xs: Vec<i32>, t: i32) {\n    let mut out = Vec::new();\n    for x in xs {\n        if x > t {\n            out.push(x * 2);\n        }\n    }\n    use_it(out);\n}\n",
            "fn f(xs: Vec<i32>) {\n    let mut set = HashSet::new();\n    for x in xs {\n        set.insert(x);\n    }\n    use_it(set);\n}\n",
            // no use after the loop (empty out-cut)
            "fn f(xs: Vec<i32>) {\n    let mut sum = 0;\n    for x in xs {\n        sum += x;\n    }\n}\n",
        ] {
            let p = propose("loop-to-iterator", src, RuleOptions::default());
            assert_eq!(p.edits.len(), 1, "{src}");
            let cert = certify(src, &p).unwrap_or_else(|e| panic!("{src}: {e}"));
            assert!(cert.checks.iter().any(|c| c.contains("loop-to-iterator")));
        }
    }

    #[test]
    fn extract_fn_valid_certs_verify() {
        // No returns; single return; mutation of outer state.
        for (src, lines) in [
            (
                "fn f(x: i32) {\n    setup(x);\n    log(x);\n    done();\n}\n",
                (2, 3),
            ),
            (
                "fn f(x: i32) {\n    let y = x + 1;\n    log(y);\n}\n",
                (2, 2),
            ),
            (
                "fn f(xs: Vec<i32>) {\n    let mut total = 0;\n    total += 1;\n    total *= 2;\n    log(total);\n}\n",
                (3, 4),
            ),
        ] {
            let p = propose(
                "extract-function",
                src,
                RuleOptions {
                    lines: Some(lines),
                    name: None,
                },
            );
            assert_eq!(p.edits.len(), 1, "{src}");
            let cert = certify(src, &p).unwrap_or_else(|e| panic!("{src}: {e}"));
            assert!(cert.checks.iter().any(|c| c.contains("extract-function")));
            assert_eq!(cert.obligation_kani, "MANUAL");
        }
    }

    #[test]
    fn certificate_is_deterministic() {
        let src = "fn f(xs: Vec<i32>) {\n    let mut sum = 0;\n    for x in xs {\n        sum += x;\n    }\n    use_it(sum);\n}\n";
        let p = propose("loop-to-iterator", src, RuleOptions::default());
        let a = certify(src, &p).unwrap().to_json().to_line();
        let b = certify(src, &p).unwrap().to_json().to_line();
        assert_eq!(a, b);
        assert!(a.contains("\"cert_hash\":\"fnv1a64:"), "{a}");
        assert!(a.contains("\"schema\":\"trailtracker.rewrite-cert/v1\""));
    }

    #[test]
    fn cert_hash_is_content_bound() {
        let src = "fn f() {\n    if true { a(); }\n    done();\n}\n";
        let p = propose("dead-branch-elim", src, RuleOptions::default());
        let cert = certify(src, &p).unwrap();
        let mut tampered = cert.clone();
        tampered.after_cpg_hash = "fnv1a64:0000000000000000".to_string();
        assert_ne!(cert.hash(), tampered.hash());
    }

    // --- input-contract failures ---------------------------------------------

    #[test]
    fn stale_file_fails_fingerprint() {
        let src = "fn f() {\n    if true { a(); }\n}\n";
        let p = propose("dead-branch-elim", src, RuleOptions::default());
        let drifted = src.replace("a()", "b()");
        assert_fails(&drifted, &p, "file_fingerprint_mismatch");
    }

    #[test]
    fn empty_proposal_fails() {
        let src = "fn f(c: bool) { if c { a(); } }\n";
        let p = propose("dead-branch-elim", src, RuleOptions::default());
        assert!(p.edits.is_empty());
        assert_fails(src, &p, "nothing_to_certify");
    }

    #[test]
    fn unknown_rule_fails_closed() {
        let src = "fn f() {\n    if true { a(); }\n}\n";
        let mut p = propose("dead-branch-elim", src, RuleOptions::default());
        p.rule_version = "99".to_string();
        assert_fails(src, &p, "unknown_rule");
    }

    #[test]
    fn after_text_that_does_not_parse_fails() {
        let src = "fn f() {\n    if true { a(); }\n    done();\n}\n";
        let mut p = propose("dead-branch-elim", src, RuleOptions::default());
        p.edits[0].after = "a( ;".to_string();
        let err = certify(src, &p).expect_err("must fail");
        // Either a parse diagnostic or (if the tree survives) a tree mismatch.
        assert!(
            err.check == "after_parse_unclean" || err.check == "tree_remapping_mismatch",
            "{err}"
        );
    }

    // --- BITE TESTS: hand-corrupted after-texts must fail precisely ----------
    //
    // A checker that cannot fail is decoration. Each bite corrupts the after
    // text of a valid proposal in a behavior-CHANGING way and asserts the
    // precise machine-readable reason.

    #[test]
    fn bite_dead_branch_wrong_branch_kept() {
        let src = "fn f() {\n    if true {\n        a();\n    } else {\n        b();\n    }\n    done();\n}\n";
        let mut p = propose("dead-branch-elim", src, RuleOptions::default());
        assert_eq!(p.edits[0].after.trim(), "a();");
        p.edits[0].after = "b();".to_string(); // kept the DEAD branch
        let err = assert_fails(src, &p, "tree_remapping_mismatch");
        assert!(err.detail.contains("a()"), "{err}");
    }

    #[test]
    fn bite_dead_branch_swapped_statements() {
        let src = "fn f() {\n    if true {\n        a();\n        b();\n    }\n    done();\n}\n";
        let mut p = propose("dead-branch-elim", src, RuleOptions::default());
        p.edits[0].after = "b();\n    a();".to_string(); // reordered splice
        let err = assert_fails(src, &p, "tree_remapping_mismatch");
        assert!(err.detail.contains("expected"), "{err}");
    }

    #[test]
    fn bite_dead_branch_extra_statement_injected() {
        let src = "fn f() {\n    if true {\n        a();\n    }\n    done();\n}\n";
        let mut p = propose("dead-branch-elim", src, RuleOptions::default());
        p.edits[0].after = "a();\n    launch_missiles();".to_string();
        assert_fails(src, &p, "tree_remapping_mismatch");
    }

    #[test]
    fn bite_dead_branch_extra_mutation_changes_dfg() {
        // Same statement COUNT and kinds, but a new assignment: the tree text
        // differs — and even if it did not, the DFG would.
        let src = "fn f() {\n    let mut x = 1;\n    if true {\n        log(x);\n    }\n    use_it(x);\n}\n";
        let mut p = propose("dead-branch-elim", src, RuleOptions::default());
        assert_eq!(p.edits[0].after.trim(), "log(x);");
        p.edits[0].after = "x = 9;".to_string();
        assert_fails(src, &p, "tree_remapping_mismatch");
    }

    #[test]
    fn bite_loop_dropped_filter() {
        // The corrupted after drops the `if x > t` guard: `t` is no longer
        // read, so the collapsed statement's external in-cut loses an edge.
        let src = "fn f(xs: Vec<i32>, t: i32) {\n    let mut out = Vec::new();\n    for x in xs {\n        if x > t {\n            out.push(x * 2);\n        }\n    }\n    use_it(out);\n}\n";
        let mut p = propose("loop-to-iterator", src, RuleOptions::default());
        assert!(
            p.edits[0].after.contains("filter_map"),
            "{}",
            p.edits[0].after
        );
        p.edits[0].after =
            "let mut out = xs.into_iter().map(|x| x * 2).collect::<Vec<_>>();".to_string();
        let err = assert_fails(src, &p, "dfg_cut_mismatch");
        assert!(err.detail.contains("var=t"), "{err}");
    }

    #[test]
    fn bite_loop_wrong_iterable() {
        // Iterating a different (outer) vec: the in-cut reads the wrong def.
        let src = "fn f(xs: Vec<i32>, ys: Vec<i32>) {\n    use_it(&ys);\n    let mut sum = 0;\n    for x in xs {\n        sum += x;\n    }\n    use_it(sum);\n}\n";
        let mut p = propose("loop-to-iterator", src, RuleOptions::default());
        p.edits[0].after =
            "let mut sum = ys.into_iter().fold(0, |mut sum, x| { sum += x; sum });".to_string();
        let err = assert_fails(src, &p, "dfg_cut_mismatch");
        assert!(
            err.detail.contains("var=xs") || err.detail.contains("var=ys"),
            "{err}"
        );
    }

    #[test]
    fn bite_loop_extra_mutation_in_fold_caught_by_replay() {
        // `sum += 1` injected inside the fold body: statement-grain graphs
        // cannot see inside the single `let` — the replay layer bites.
        let src = "fn f(xs: Vec<i32>) {\n    let mut sum = 0;\n    for x in xs {\n        sum += x;\n    }\n    use_it(sum);\n}\n";
        let mut p = propose("loop-to-iterator", src, RuleOptions::default());
        p.edits[0].after =
            "let mut sum = xs.into_iter().fold(0, |mut sum, x| { sum += x; sum += 1; sum });"
                .to_string();
        let err = assert_fails(src, &p, "replay_mismatch");
        assert!(err.detail.contains("not byte-identical"), "{err}");
    }

    #[test]
    fn bite_loop_split_into_two_statements() {
        let src = "fn f(xs: Vec<i32>) {\n    let mut sum = 0;\n    for x in xs {\n        sum += x;\n    }\n    use_it(sum);\n}\n";
        let mut p = propose("loop-to-iterator", src, RuleOptions::default());
        p.edits[0].after =
            "let mut sum = 0;\n    sum = xs.into_iter().fold(0, |mut sum, x| { sum += x; sum });"
                .to_string();
        assert_fails(src, &p, "tree_remapping_mismatch");
    }

    #[test]
    fn bite_extract_swapped_statements_in_closure() {
        let src = "fn f(x: i32) {\n    setup(x);\n    log(x);\n    done();\n}\n";
        let mut p = propose(
            "extract-function",
            src,
            RuleOptions {
                lines: Some((2, 3)),
                name: None,
            },
        );
        let good = p.edits[0].after.clone();
        assert!(good.contains("setup(x);"), "{good}");
        // Swap the two statements inside the closure body.
        p.edits[0].after = good
            .replace("setup(x);", "@@TMP@@")
            .replace("log(x);", "setup(x);")
            .replace("@@TMP@@", "log(x);");
        let err = assert_fails(src, &p, "closure_body_not_verbatim");
        assert!(err.detail.contains("verbatim"), "{err}");
    }

    #[test]
    fn bite_extract_dropped_statement() {
        let src = "fn f(x: i32) {\n    setup(x);\n    log(x);\n    done();\n}\n";
        let mut p = propose(
            "extract-function",
            src,
            RuleOptions {
                lines: Some((2, 3)),
                name: None,
            },
        );
        p.edits[0].after = p.edits[0].after.replace("        log(x);\n", "");
        let err = certify(src, &p).expect_err("dropping a statement must fail");
        assert!(
            err.check == "closure_body_not_verbatim" || err.check == "dfg_cut_mismatch",
            "{err}"
        );
    }

    #[test]
    fn bite_extract_return_swallowed() {
        // The corrupted after discards the returned binding: use(y) loses its
        // only definition — the after text does not even parse into the
        // licensed two-statement shape with the destructuring let.
        let src = "fn f(x: i32) {\n    let y = x + 1;\n    log(y);\n}\n";
        let mut p = propose(
            "extract-function",
            src,
            RuleOptions {
                lines: Some((2, 2)),
                name: None,
            },
        );
        let good = p.edits[0].after.clone();
        assert!(good.contains("let y = extracted();"), "{good}");
        p.edits[0].after = good.replace("let y = extracted();", "extracted();");
        let err = assert_fails(src, &p, "dfg_cut_mismatch");
        assert!(err.detail.contains("var=y"), "{err}");
    }

    #[test]
    fn bite_extract_extra_mutation_after_call() {
        let src = "fn f(xs: Vec<i32>) {\n    let mut total = 0;\n    total += 1;\n    total *= 2;\n    log(total);\n}\n";
        let mut p = propose(
            "extract-function",
            src,
            RuleOptions {
                lines: Some((3, 4)),
                name: None,
            },
        );
        p.edits[0].after = p.edits[0]
            .after
            .replace("extracted();", "extracted); total = 0;");
        let err = certify(src, &p).expect_err("must fail");
        // Whatever layer sees it first, it must not pass.
        assert!(
            [
                "tree_remapping_mismatch",
                "after_parse_unclean",
                "dfg_cut_mismatch",
                "cfg_remapping_mismatch",
            ]
            .contains(&err.check.as_str()),
            "{err}"
        );
    }

    #[test]
    fn bite_edit_outside_any_function() {
        let src = "const K: i32 = 1;\n\nfn f() {\n    if true { a(); }\n}\n";
        let mut p = propose("dead-branch-elim", src, RuleOptions::default());
        // Retarget the edit at the const item (with a parseable after text —
        // the outside-function refusal must fire on placement, not parsing).
        p.edits[0].span = ByteSpan::new(0, 17);
        p.edits[0].before = src[0..17].to_string();
        p.edits[0].after = "const K: i32 = 2;".to_string();
        assert_fails(src, &p, "edit_outside_function");
    }

    #[test]
    fn bite_collateral_damage_to_neighboring_function() {
        // A hand-built edit that also mutates a neighboring function's text
        // cannot pass: an edit crossing function boundaries is refused on
        // placement, and every function's CPG is rechecked regardless.
        let src = "fn f() {\n    if true { a(); }\n}\nfn g() {\n    b();\n}\n";
        let mut p = propose("dead-branch-elim", src, RuleOptions::default());
        // Extend the edit span to swallow `fn g`'s call and rewrite it.
        let start = p.edits[0].span.start as usize;
        p.edits[0].span = ByteSpan::new(start, src.len());
        p.edits[0].before = src[start..].to_string();
        p.edits[0].after = "a();\n}\nfn g() {\n    evil();\n}\n".to_string();
        let err = certify(src, &p).expect_err("must fail");
        assert!(
            [
                "edit_outside_function",
                "unaffected_function_changed",
                "tree_remapping_mismatch",
            ]
            .contains(&err.check.as_str()),
            "{err}"
        );
    }

    // --- redundant-clone-elim: valid certs + bites ----------------------------

    #[test]
    fn clone_elim_valid_certs_verify() {
        for src in [
            // RHS-of-let shape
            "fn f() {\n    let x = make();\n    let y = x.clone();\n    use_it(y);\n}\n",
            // call-argument shape
            "fn f() {\n    let x = make();\n    take(x.clone());\n}\n",
            // read BEFORE the clone is licensed (last-use is about paths after)
            "fn f() {\n    let x = make();\n    log(&x);\n    let y = x.clone();\n    use_it(y);\n}\n",
            // conditional site: no path after the move reads `x`
            "fn f(c: bool) {\n    let x = make();\n    if c {\n        sink(x.clone());\n    }\n}\n",
        ] {
            let p = propose("redundant-clone-elim", src, RuleOptions::default());
            assert_eq!(p.edits.len(), 1, "{src}: {:?}", p.rejections);
            let cert = certify(src, &p).unwrap_or_else(|e| panic!("{src}: {e}"));
            assert_eq!(cert.rule_id, "redundant-clone-elim");
            assert_eq!(cert.obligation_kani, "k3c_clone_elim_schema");
            assert!(
                cert.checks
                    .iter()
                    .any(|c| c.contains("redundant-clone-elim") && c.contains("last use")),
                "{:?}",
                cert.checks
            );
        }
    }

    #[test]
    fn clone_elim_cert_is_deterministic() {
        let src = "fn f() {\n    let x = make();\n    let y = x.clone();\n    use_it(y);\n}\n";
        let p = propose("redundant-clone-elim", src, RuleOptions::default());
        let a = certify(src, &p).unwrap().to_json().to_line();
        let b = certify(src, &p).unwrap().to_json().to_line();
        assert_eq!(a, b);
        assert!(a.contains("redundant-clone-elim"), "{a}");
    }

    /// Build a hand-crafted clone-elim proposal targeting the `.clone()` at
    /// the `n`-th occurrence in `src` — the wrongful-removal bite vector (the
    /// recognizer refuses these sites, so no honest propose can produce them).
    fn forged_clone_proposal(src: &str, n: usize) -> Proposal {
        let mut at = 0;
        for _ in 0..=n {
            at = src[at..].find(".clone()").expect("occurrence") + at + 1;
        }
        let start = at - 1;
        let span = ByteSpan::new(start, start + ".clone()".len());
        Proposal {
            rule_id: "redundant-clone-elim".to_string(),
            rule_version: "1".to_string(),
            dir: ".".to_string(),
            file: "t.rs".to_string(),
            file_fingerprint: fingerprint(src.as_bytes()),
            edits: vec![ProposedEdit {
                span,
                before: ".clone()".to_string(),
                after: String::new(),
                why_safe: "forged".to_string(),
                cpg_facts: vec![],
            }],
            rejections: vec![],
        }
    }

    #[test]
    fn bite_clone_removed_but_value_read_later() {
        // THE bite this rule exists to catch: removing a clone whose binding
        // IS read afterwards. The recognizer refuses it; a forged proposal
        // must fail verification with the exact last-use reason.
        let src = "fn f() {\n    let x = make();\n    let y = x.clone();\n    use_it(&x);\n}\n";
        let p = forged_clone_proposal(src, 0);
        let err = assert_fails(src, &p, "cloned_value_read_later");
        assert!(err.detail.contains("`x`"), "{err}");
        assert!(err.detail.contains("not the last use"), "{err}");
    }

    #[test]
    fn bite_clone_read_later_on_one_branch_only() {
        // The read happens on only ONE path after the clone — "no read on ANY
        // path" must still refuse.
        let src = "fn f(c: bool) {\n    let x = make();\n    let y = x.clone();\n    if c {\n        use_it(&x);\n    }\n    done(y);\n}\n";
        let p = forged_clone_proposal(src, 0);
        assert_fails(src, &p, "cloned_value_read_later");
    }

    #[test]
    fn bite_clone_in_loop_forged() {
        let src = "fn f(xs: Vec<i32>) {\n    let x = make();\n    for _i in xs {\n        sink(x.clone());\n    }\n}\n";
        let p = forged_clone_proposal(src, 0);
        assert_fails(src, &p, "clone_in_loop");
    }

    #[test]
    fn bite_clone_of_parameter_forged() {
        let src = "fn f(x: String) {\n    let y = x.clone();\n    use_it(y);\n}\n";
        let p = forged_clone_proposal(src, 0);
        assert_fails(src, &p, "receiver_def_not_single_let");
    }

    #[test]
    fn bite_clone_chained_position_forged() {
        // `x.clone().len()` — deleting the clone here is not a licensed site.
        let src =
            "fn f() {\n    let x = make();\n    let y = x.clone().len();\n    use_it(y);\n}\n";
        let p = forged_clone_proposal(src, 0);
        assert_fails(src, &p, "site_not_recognized");
    }

    #[test]
    fn bite_clone_tampered_after_text() {
        // A valid proposal whose after-text is corrupted into a different
        // call: the tree check sees a statement text outside the license.
        let src = "fn f() {\n    let x = make();\n    let y = x.clone();\n    use_it(y);\n}\n";
        let mut p = propose("redundant-clone-elim", src, RuleOptions::default());
        assert_eq!(p.edits.len(), 1);
        p.edits[0].after = ".to_owned()".to_string();
        assert_fails(src, &p, "tree_remapping_mismatch");
    }

    #[test]
    fn bite_clone_whitespace_smuggled_after_caught() {
        // Whitespace smuggled into the after-text: adjacent to a non-space
        // byte the collapsed tree check sees it; adjacent to existing
        // whitespace it collapses away and the replay layer pins the bytes.
        let src = "fn f() {\n    let x = make();\n    let y = x.clone();\n    use_it(y);\n}\n";
        let mut p = propose("redundant-clone-elim", src, RuleOptions::default());
        p.edits[0].after = " ".to_string();
        assert_fails(src, &p, "tree_remapping_mismatch");

        let src2 = "fn f() {\n    let x = make();\n    let y = x.clone() ;\n    use_it(y);\n}\n";
        let mut p2 = propose("redundant-clone-elim", src2, RuleOptions::default());
        assert_eq!(p2.edits.len(), 1, "{:?}", p2.rejections);
        p2.edits[0].after = " ".to_string();
        assert_fails(src2, &p2, "replay_mismatch");
    }

    // --- if-let-to-match: valid certs + bites --------------------------------

    #[test]
    fn if_let_match_valid_certs_verify() {
        for src in [
            "fn f(o: Option<i32>) {\n    if let Some(x) = o { use_it(x); } else { fallback(); }\n    done();\n}\n\nfn untouched(x: i32) -> i32 {\n    x + 1\n}\n",
            // tail-expression position
            "fn f(o: Option<i32>) -> i32 {\n    if let Some(x) = o { x } else { 0 }\n}\n",
            // multi-statement branches
            "fn f(o: Option<i32>) {\n    if let Some(x) = o {\n        a(x);\n        b(x);\n    } else {\n        c();\n    }\n}\n",
            // field scrutinee
            "fn f(s: S) {\n    if let Some(x) = s.field { a(x); } else { b(); }\n}\n",
            // inside a loop (loop-back re-anchoring through the arms)
            "fn f(xs: Vec<Option<i32>>) {\n    for o in xs {\n        if let Some(x) = o { a(x); } else { b(); }\n    }\n}\n",
            // empty then branch
            "fn f(o: Option<i32>) {\n    if let Some(_x) = o {} else { b(); }\n    done();\n}\n",
        ] {
            let p = propose("if-let-to-match", src, RuleOptions::default());
            assert_eq!(p.edits.len(), 1, "{src}: {:?}", p.rejections);
            let cert = certify(src, &p).unwrap_or_else(|e| panic!("{src}: {e}"));
            assert!(cert.checks.iter().any(|c| c.contains("if-let-to-match")));
            assert!(cert.obligation_kani.contains("k3c_if_let_match_schema"));
        }
    }

    #[test]
    fn bite_if_let_swapped_arms() {
        // Wildcard arm first would catch everything: behavior changes.
        let src = "fn f(o: Option<i32>) {\n    if let Some(x) = o { use_it(x); } else { fallback(); }\n}\n";
        let mut p = propose("if-let-to-match", src, RuleOptions::default());
        p.edits[0].after = p.edits[0]
            .after
            .replace("Some(x) => { use_it(x); }", "SWAP1")
            .replace("_ => { fallback(); }", "Some(x) => { use_it(x); }")
            .replace("SWAP1", "_ => { fallback(); }");
        assert_fails(src, &p, "tree_remapping_mismatch");
    }

    #[test]
    fn bite_if_let_dropped_wildcard_arm() {
        // Dropping the `_` arm loses the else path (and exhaustiveness).
        let src = "fn f(o: Option<i32>) {\n    if let Some(x) = o { use_it(x); } else { fallback(); }\n}\n";
        let mut p = propose("if-let-to-match", src, RuleOptions::default());
        p.edits[0].after = "match o {\n        Some(x) => { use_it(x); }\n    }".to_string();
        assert_fails(src, &p, "tree_remapping_mismatch");
    }

    #[test]
    fn bite_if_let_injected_statement() {
        let src = "fn f(o: Option<i32>) {\n    if let Some(x) = o { use_it(x); } else { fallback(); }\n}\n";
        let mut p = propose("if-let-to-match", src, RuleOptions::default());
        p.edits[0].after = p.edits[0]
            .after
            .replace("{ use_it(x); }", "{ use_it(x); launch_missiles(); }");
        assert_fails(src, &p, "tree_remapping_mismatch");
    }

    #[test]
    fn bite_if_let_wrong_scrutinee() {
        // Matching a different binding: the scrutinee read re-wires the DFG
        // (and the match node's text no longer equals the licensed one).
        let src = "fn f(o: Option<i32>, p2: Option<i32>) {\n    use_it(&p2);\n    if let Some(x) = o { use_it(x); } else { fallback(); }\n}\n";
        let mut p = propose("if-let-to-match", src, RuleOptions::default());
        p.edits[0].after = p.edits[0].after.replace("match o {", "match p2 {");
        assert_fails(src, &p, "tree_remapping_mismatch");
    }

    #[test]
    fn bite_if_let_pattern_widened() {
        // `Some(_)` instead of `Some(x)`: the binding def disappears and the
        // then-arm body no longer compiles against the licensed DFG.
        let src = "fn f(o: Option<i32>) {\n    if let Some(x) = o { use_it(x); } else { fallback(); }\n}\n";
        let mut p = propose("if-let-to-match", src, RuleOptions::default());
        p.edits[0].after = p.edits[0].after.replace("Some(x) =>", "Some(_) =>");
        let err = certify(src, &p).expect_err("widened pattern must fail");
        assert!(
            err.check == "tree_remapping_mismatch" || err.check == "dfg_remapping_mismatch",
            "{err}"
        );
    }

    // --- slice-param: valid certs + bites -------------------------------------

    const SLICE_SRC: &str = "fn total(v: &Vec<i32>) -> usize {\n    v.len()\n}\n\nfn untouched(x: i32) -> i32 {\n    x + 1\n}\n";

    #[test]
    fn slice_param_valid_certs_verify() {
        for src in [
            SLICE_SRC,
            // String flavor
            "fn g(s: &String) {\n    if s.is_empty() {\n        log(s.len());\n    }\n}\n",
            // nested generic (merged `>>` token) + iteration
            "fn f(v: &Vec<Vec<u8>>) {\n    for x in v {\n        use_it(x);\n    }\n}\n",
        ] {
            let p = propose("slice-param", src, RuleOptions::default());
            assert_eq!(p.edits.len(), 1, "{src}: {:?}", p.rejections);
            let cert = certify(src, &p).unwrap_or_else(|e| panic!("{src}: {e}"));
            assert_eq!(cert.rule_id, "slice-param");
            assert_eq!(cert.obligation_kani, "MANUAL");
            assert!(
                cert.checks
                    .iter()
                    .any(|c| c.contains("slice-param") && c.contains("identical")),
                "{:?}",
                cert.checks
            );
        }
    }

    #[test]
    fn slice_param_cert_is_deterministic() {
        let p = propose("slice-param", SLICE_SRC, RuleOptions::default());
        let a = certify(SLICE_SRC, &p).unwrap().to_json().to_line();
        let b = certify(SLICE_SRC, &p).unwrap().to_json().to_line();
        assert_eq!(a, b);
        assert!(a.contains("slice-param"), "{a}");
    }

    /// Build a hand-crafted slice-param proposal targeting the first
    /// occurrence of `before` in `src` — the wrongful-generalization bite
    /// vector (the recognizer refuses these sites, so no honest propose can
    /// produce them).
    fn forged_slice_proposal(src: &str, before: &str, after: &str) -> Proposal {
        let start = src.find(before).expect("type text present");
        Proposal {
            rule_id: "slice-param".to_string(),
            rule_version: "1".to_string(),
            dir: ".".to_string(),
            file: "t.rs".to_string(),
            file_fingerprint: fingerprint(src.as_bytes()),
            edits: vec![ProposedEdit {
                span: ByteSpan::new(start, start + before.len()),
                before: before.to_string(),
                after: after.to_string(),
                why_safe: "forged".to_string(),
                cpg_facts: vec![],
            }],
            rejections: vec![],
        }
    }

    #[test]
    fn bite_slice_param_vec_specific_method_is_refused() {
        // THE bite this rule exists to catch: generalizing a parameter whose
        // body calls a Vec-specific method. The recognizer refuses the site;
        // a forged proposal must fail the re-proved precondition.
        let src = "fn f(v: &Vec<i32>) {\n    log(v.capacity());\n}\n";
        let p = forged_slice_proposal(src, "&Vec<i32>", "&[i32]");
        let err = assert_fails(src, &p, "param_method_not_slice_compatible");
        assert!(err.detail.contains("capacity"), "{err}");
    }

    #[test]
    fn bite_slice_param_passed_onward_is_refused() {
        // Passing the parameter to a callee that expects `&Vec<T>` would no
        // longer typecheck — and typechecking is not this engine's oracle,
        // so the verifier must refuse structurally.
        let src = "fn f(v: &Vec<i32>) {\n    helper(v);\n}\n";
        let p = forged_slice_proposal(src, "&Vec<i32>", "&[i32]");
        assert_fails(src, &p, "param_use_not_slice_compatible");
    }

    #[test]
    fn bite_slice_param_fn_used_as_value_is_refused() {
        let src = "fn f(v: &Vec<i32>) {\n    use_len(v.len());\n}\n\nfn c() {\n    reg(f);\n}\n";
        let p = forged_slice_proposal(src, "&Vec<i32>", "&[i32]");
        assert_fails(src, &p, "function_used_as_value");
    }

    #[test]
    fn bite_slice_param_local_type_is_not_a_site() {
        // The same byte string in a LOCAL type annotation is not a parameter.
        let src = "fn f(n: i32) {\n    let v: &Vec<i32> = make();\n    use_it(v.len(), n);\n}\n";
        let p = forged_slice_proposal(src, "&Vec<i32>", "&[i32]");
        assert_fails(src, &p, "site_not_recognized");
    }

    #[test]
    fn bite_slice_param_wrong_replacement() {
        // `&mut [i32]` parses and leaves the CPG untouched — only the
        // re-derived licensed emission catches it.
        let mut p = propose("slice-param", SLICE_SRC, RuleOptions::default());
        p.edits[0].after = "&mut [i32]".to_string();
        assert_fails(SLICE_SRC, &p, "replacement_not_licensed");
    }

    #[test]
    fn bite_slice_param_injected_function() {
        let mut p = propose("slice-param", SLICE_SRC, RuleOptions::default());
        p.edits[0].after = "&[i32]) -> usize { 0 }\n\nfn evil(v: &[i32]".to_string();
        assert_fails(SLICE_SRC, &p, "function_set_changed");
    }

    // --- every registered rule has a schema obligation on file ---------------

    #[test]
    fn every_rule_has_an_obligation() {
        for rule in all_rules() {
            let ob = obligation_for(rule.id(), rule.version());
            assert!(
                ob.is_some(),
                "rule {} v{} has no schema obligation — ADR-0007 requires one per rule",
                rule.id(),
                rule.version()
            );
            let (r, _) = ob.unwrap();
            assert!(r.contains("0007"), "{r}");
        }
    }
}
