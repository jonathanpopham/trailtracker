//! The domains extractor: recover **bounded contexts** from the base graph —
//! the capstone of the understanding stack.
//!
//! v3 (domains-v3): the algorithm is **structural** — deterministic
//! hierarchical clustering of the dependency graph — not lexical. The
//! previous design clustered files by concept-token frequency; a head-to-head
//! against LLM-classified ground truth (`benchmarks/
//! domain_semantics_comparison.md`) showed that lexical frequency measures
//! *vocabulary*, not *responsibility*: on technical codebases it produced
//! buckets like `Prefix`/`Setup`/`Arrow`. Real functional decomposition lives
//! in the dependency structure (who is built on whom) and in the directory
//! structure (how the authors partitioned the work), so v3 clusters **units**
//! (directory-derived modules) by **dependency mass**, with the lexicon
//! demoted from driver to signal (labeling tie-breaks and last-resort
//! placement of structureless code). Deterministic steps:
//!
//! 1. **Scaffold filter, zero ungrouped** — files under build/tooling/
//!    fixture directories ([`SCAFFOLD_SEGMENTS`]), documentation trees/
//!    extensions ([`DOC_SEGMENTS`]/[`DOC_EXTENSIONS`]), machine-generated
//!    files ([`crate::brief_generated::is_generated`]), and files at the
//!    repository root are **excluded from the clustering scope** (their
//!    symbol mass never moves a threshold — junk mass cannot strip a src
//!    file of its domain), but they are never dropped from the *view*: each
//!    lands in a first-class named infrastructure group
//!    ([`GROUP_BUILD_TOOLING`] / [`GROUP_DOCUMENTATION`] /
//!    [`GROUP_GENERATED`] / [`GROUP_REPO_ROOT`]) emitted as a real domain
//!    with `kind: "infrastructure"` and a `reason` prop
//!    (`scaffold`/`docs`/`generated`/`root`). Every file has a named home.
//! 2. **Units** — every eligible file gets a unit: the first two
//!    *load-bearing* directory segments of its path. A segment is skipped as
//!    transparent when it is packaging convention ([`TRANSPARENT_SEGMENTS`]:
//!    `src`, `tests`, `java`, …) or a **trunk** — a directory holding at
//!    least [`TRUNK_NUM`]`/`[`TRUNK_DEN`] of its parent's files (the
//!    single-child chains of Java package roots, the `django/` dir of a
//!    single-package repo). This yields `control-plane/connectors`,
//!    `Ordering.API`, `django/db` — project-then-subsystem granularity.
//! 3. **Unit dependency mass** — every [`DEPENDS`]-family base edge whose
//!    endpoints resolve to two different eligible files contributes to a
//!    directed unit→unit mass matrix; mass to [`ExternalDependency`] nodes is
//!    tallied separately per unit.
//! 4. **Structural priors** (the task-level shape of prior knowledge):
//!    (a) *path families attract* — units sharing their first path segment
//!    get weak star+chain pseudo-edges (weight = total dependency mass /
//!    [`STAR_DIVISOR`], a relative weight), so sibling directories with no
//!    resolvable imports (a TSX dashboard) still cohere; the same
//!    pseudo-edges bridge *suffix-role naming variants* — units whose name
//!    families reduce to one [`family_stem`] (`Webhooks.API` +
//!    `WebhookClient`) are one feature family split across naming
//!    conventions, even when an HTTP boundary leaves them dependency-less;
//!    (b) *high mutual dependency mass attracts* — the modularity objective;
//!    (c) *cross-cutting code forms its own cluster instead of being
//!    absorbed*: **external-integration adapters** (units whose external
//!    mass exceeds all their internal traffic, that are used by ≥ 3 units
//!    and use almost nothing themselves) are pooled into their own
//!    community, and **shared kernels** (units of small name-families
//!    depended on by ≥ 3 other name-families) are pooled into
//!    `Shared/Platform`.
//! 5. **Communities** — deterministic greedy modularity over the unit graph
//!    (Louvain-style local moves in sorted unit order with sorted tie-breaks,
//!    then greedy community merges while any merge improves modularity), all
//!    arithmetic exact integer cross-products. A **legibility cap** rejects
//!    any move/merge that would push one community to
//!    [`CAP_NUM`]`/`[`CAP_DEN`] of all symbols (no structural cluster may
//!    swallow half the codebase), and [`MAX_DOMAINS`] bounds the final count.
//! 6. **Mirror fold and floor** — *mirror units*: a unit that is a
//!    byte-identical prefix-copy of another (every file path equals one
//!    fixed prefix + the original's path, with identical file basenames and
//!    per-file symbol counts) is the same subsystem duplicated (a cloned or
//!    vendored module), and folds into the original *before* clustering —
//!    so duplicating a module, or the whole codebase, doubles every mass
//!    without changing the community structure. *Floor*: communities below
//!    `total/`[`FLOOR_DIVISOR`] symbols are absorbed into their
//!    most-coupled community (cap-respecting). All thresholds are ratios of
//!    symbol masses — duplication scales every mass together, so the
//!    surviving set is duplication-stable (the star weight's floor of 1 is
//!    the only non-ratio, and it only binds when the repo has almost no
//!    dependency mass at all).
//! 7. **Shared/Platform** — pooled shared kernels, unabsorbable floor
//!    leftovers, and files that are *both* conceptless and dependency-less
//!    (pure plumbing) — but **unit loyalty beats the crumb dump**: a file
//!    whose unit's name family is one of its domain's majority (label-
//!    driving) name families never leaves that domain over weak coupling
//!    (an Identity ViewModel with no resolvable edges is Identity code,
//!    not shared plumbing); only crumbs in units foreign to their domain's
//!    identity fall through. When Shared/Platform would be negligible
//!    (< total/[`SHARED_FOLD_DIVISOR`]) it never surfaces as a junk cluster:
//!    each crumb returns to its own unit's domain (the largest domain is the
//!    fallback for crumbs whose unit is itself shared).
//!    7b. **Test-folding** — a file under a test directory
//!    ([`TEST_SEGMENTS`]) belongs to the domain of the code it *exercises*:
//!    the domain receiving its largest dependency mass to non-test files
//!    (outgoing first, incoming as fallback). Folds honor the anti-collapse
//!    cap ([`CAP_NUM`]/[`CAP_DEN`]) like every clustering move — a monolith
//!    with a huge test tree must not read as one domain swallowing the
//!    codebase; cap-rejected tests keep their own community. A test with no
//!    resolvable subject keeps its unit's domain when that domain holds any
//!    production code; a pure-test community with no subjects is test
//!    scaffolding and folds into [`GROUP_BUILD_TOOLING`] — never ungrouped.
//! 8. **Labels, without any LLM** — each domain is named from its strongest
//!    deterministic signal, in order: the dominant path family when it
//!    carries ≥ 2/3 of the domain's symbols (`control-plane`, `dashboard`);
//!    the common name-prefix of its families (`Ordering.API` +
//!    `Ordering.Domain` → `Ordering`); generic container names (`packages`,
//!    `apps`) are replaced by the dominant second segment; label collisions
//!    extend with the dominant second segment (`control-plane/connectors`),
//!    then with the domain's dominant concept token — the lexicon as
//!    tie-break, which is what keeps `Ordering`/`Basket`/`Catalog`-shaped
//!    names on business repos. Honest structural labels beat fake-semantic
//!    ones; an optional LLM naming pass may upgrade them later, outside this
//!    airgap-pure pass.
//! 9. **Emit** — one [`Module`] node per domain (tagged `view: "domains"`,
//!    with `domain`/`label`/`unit_count`/`file_count`/`symbol_count`/
//!    `confidence`/`kind`, plus `reason` on infrastructure groups), one
//!    [`Module`] node per **subdomain** (a unit inside a
//!    domain: `subdomain::{domain}::{unit}`, with `file_count`/
//!    `symbol_count`), domain `CONTAINS` subdomain edges, one member
//!    [`File`] node per owned file (carrying `domain` and `unit`), domain
//!    `CONTAINS` file edges, and counted inter-domain `DEPENDS_ON` edges —
//!    the Domain → Subdomain → File hierarchy.
//!
//! The pass is a pure, deterministic function of the base graph: it walks
//! the `BTreeMap`-ordered node/edge iterators, clusters with sorted
//! tie-breaks and exact integer arithmetic, and writes through the sorted,
//! de-duplicating [`Graph`] API, so the output is byte-stable across runs.
//! The base graph is never mutated. No LLM, no network, no randomness.
//!
//! [`File`]: crate::ir::ontology::node::FILE
//! [`Module`]: crate::ir::ontology::node::MODULE
//! [`ExternalDependency`]: crate::ir::ontology::node::EXTERNAL_DEPENDENCY
//! [`DEPENDS`]: crate::ir::ontology::relation::DEPENDS
//! [`lexicon::tokenize`]: crate::extract::lexicon::tokenize
//! [`lexicon::classify_token`]: crate::extract::lexicon::classify_token

use std::collections::{BTreeMap, BTreeSet};

use crate::brief_generated::is_generated;
use crate::core::json::Json;
use crate::extract::lexicon;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont, parent_relation, relation};

use super::Extractor;

/// Property key marking a node as belonging to the domains view.
const VIEW: &str = "domains";

/// The cross-cutting infrastructure domain: pooled shared kernels, floor
/// leftovers with no coupling, and conceptless+dependency-less files.
const SHARED_DOMAIN: &str = "Shared/Platform";

/// First-class named groups for the files the clustering excludes
/// (zero-ungrouped): every scaffold/docs/generated/root file still gets a
/// named home, emitted as a real domain node with `kind: "infrastructure"`
/// and a `reason` prop — never an "(ungrouped)" blob in the UI.
pub const GROUP_BUILD_TOOLING: &str = "Build & Tooling";
/// See [`GROUP_BUILD_TOOLING`].
pub const GROUP_DOCUMENTATION: &str = "Documentation";
/// See [`GROUP_BUILD_TOOLING`].
pub const GROUP_GENERATED: &str = "Generated";
/// See [`GROUP_BUILD_TOOLING`].
pub const GROUP_REPO_ROOT: &str = "Repo root";

/// `kind` prop value for clustered code domains (including `Shared/Platform`).
pub const KIND_BUSINESS: &str = "business";
/// `kind` prop value for the named infrastructure groups.
pub const KIND_INFRASTRUCTURE: &str = "infrastructure";

/// The `reason` prop of an infrastructure group, `None` for business domains.
pub fn group_reason(name: &str) -> Option<&'static str> {
    match name {
        GROUP_BUILD_TOOLING => Some("scaffold"),
        GROUP_DOCUMENTATION => Some("docs"),
        GROUP_GENERATED => Some("generated"),
        GROUP_REPO_ROOT => Some("root"),
        _ => None,
    }
}

/// Legibility guard: at most this many domains (plus `Shared/Platform`).
/// Beyond it the smallest communities merge into their most-coupled
/// neighbor. The 11-repo eval cohort lands at 3–21 without touching it.
const MAX_DOMAINS: usize = 24;

/// A community below `total/FLOOR_DIVISOR` symbols (0.5%) is absorbed into
/// its most-coupled community instead of surfacing as a domain. Relative to
/// the repo, never an absolute count (duplication stability).
const FLOOR_DIVISOR: u64 = 200;

/// Anti-collapse cap: no move or merge may push one community to
/// `CAP_NUM/CAP_DEN` (48%) of all symbols. One structural cluster owning
/// half the codebase is a collapse, not a domain.
const CAP_NUM: u64 = 12;
/// See [`CAP_NUM`].
const CAP_DEN: u64 = 25;

/// A `Shared/Platform` below `total/SHARED_FOLD_DIVISOR` symbols is noise,
/// not a domain: its crumbs fold into the largest domain instead.
const SHARED_FOLD_DIVISOR: u64 = 1000;

/// Path-family pseudo-edge weight = total dependency mass / STAR_DIVISOR
/// (minimum 1): strong enough to cohere dependency-less sibling dirs, weak
/// enough never to outvote real dependency structure.
const STAR_DIVISOR: u64 = 200;

/// A directory holding at least `TRUNK_NUM/TRUNK_DEN` (3/4) of its parent's
/// files is a *trunk* segment — packaging convention, not decomposition —
/// and is skipped by the unit derivation.
const TRUNK_NUM: u64 = 3;
/// See [`TRUNK_NUM`].
const TRUNK_DEN: u64 = 4;

/// A shared-kernel candidate must live in a name-family owning less than
/// `total/KERNEL_FAMILY_DIVISOR` of all symbols: kernels are small
/// cross-cutting libraries, not major subsystems.
const KERNEL_FAMILY_DIVISOR: u64 = 20;

/// Directory segments (matched case-insensitively) whose files are build
/// scaffolding, tooling, or test fixtures — never domain members. **Must
/// stay sorted and unique** — membership is a binary search, and a test
/// enforces the invariant.
const SCAFFOLD_SEGMENTS: &[&str] = &[
    "__fixtures__",
    "bin",
    "build",
    "dist",
    "fixtures",
    "node_modules",
    "obj",
    "out",
    "scripts",
    "testdata",
    "tools",
    "upgradescripts",
];

/// Directory segments that are packaging convention, not decomposition:
/// always transparent to the unit derivation. **Must stay sorted and
/// unique** (binary-searched, test-enforced).
const TRANSPARENT_SEGMENTS: &[&str] = &[
    "java", "lib", "libs", "main", "source", "src", "test", "tests",
];

/// Directory segments that hold prose documentation, not code decomposition.
/// Files under them are Documentation-group members, excluded from the
/// analyzable clustering scope. **Must stay sorted and unique**
/// (binary-searched, test-enforced).
const DOC_SEGMENTS: &[&str] = &["doc", "docs", "documentation"];

/// File extensions (lowercased) of prose documentation. **Must stay sorted
/// and unique** (binary-searched, test-enforced).
const DOC_EXTENSIONS: &[&str] = &["adoc", "markdown", "md", "rst", "txt"];

/// Directory segments (matched case-insensitively) that mark a file as a
/// *test* for the test-folding rule: tests belong to the domain of the code
/// they exercise, resolved through dependency edges. **Must stay sorted and
/// unique** (binary-searched, test-enforced).
const TEST_SEGMENTS: &[&str] = &["__tests__", "spec", "specs", "test", "tests"];

/// First path segments that are generic containers, not names: a domain
/// label never uses them; the dominant second segment labels instead.
/// **Must stay sorted and unique** (binary-searched, test-enforced).
const GENERIC_LABEL_SEGMENTS: &[&str] = &[
    "(root)", "apps", "crates", "internal", "modules", "packages", "pkg",
];

/// Tokens the shared lexicon classes as `concept` but that can never *label*
/// a domain or count as a concept signal: bare verbs, test-dialect words
/// (`should`, `expect`, `given`), prepositions/connectives, and
/// cross-language framework noise (`constructor`, `returns`, `throws`).
/// **Must stay sorted and unique** (binary-searched, test-enforced).
const NOISE_TOKENS: &[&str] = &[
    "against",
    "all",
    "app",
    "apply",
    "arrange",
    "assert",
    "can",
    "cannot",
    "check",
    "checked",
    "checks",
    "close",
    "common",
    "component",
    "components",
    "consent",
    "constructor",
    "contains",
    "convert",
    "core",
    "correctly",
    "create",
    "custom",
    "date",
    "delete",
    "describe",
    "disabled",
    "dispose",
    "enabled",
    "ensure",
    "ensures",
    "equal",
    "equals",
    "execute",
    "exists",
    "expect",
    "fails",
    "find",
    "found",
    "from",
    "given",
    "global",
    "grace",
    "handle",
    "handled",
    "handles",
    "init",
    "initialize",
    "instance",
    "instances",
    "internal",
    "into",
    "invoke",
    "many",
    "none",
    "one",
    "onto",
    "over",
    "per",
    "prepare",
    "properly",
    "register",
    "required",
    "resolve",
    "resolved",
    "resolves",
    "returns",
    "run",
    "runs",
    "should",
    "shouldnt",
    "succeeds",
    "successfully",
    "then",
    "throw",
    "throws",
    "to",
    "two",
    "undefined",
    "under",
    "upon",
    "use",
    "used",
    "uses",
    "validate",
    "validates",
    "verify",
    "via",
    "when",
    "with",
];

/// Classify a file path into its infrastructure group, or `None` when the
/// file is analyzable code (clustered into business domains). Classification
/// order is deterministic: machine-generated beats docs beats scaffold beats
/// repo-root. Excluded files are dropped from the clustering *scope* (their
/// symbol mass never moves a threshold — scope stability), but they are never
/// ungrouped: each lands in its named group.
pub fn infrastructure_group(path: &str) -> Option<(&'static str, &'static str)> {
    if is_generated(path, "") {
        return Some((GROUP_GENERATED, "generated"));
    }
    let mut segs: Vec<&str> = path.split(['/', '\\']).filter(|s| !s.is_empty()).collect();
    // The filename only matters for the docs extension check; directories
    // drive every other rule.
    let file = segs.pop().unwrap_or("");
    let doc_ext = file
        .rsplit_once('.')
        .map(|(_, e)| e.to_ascii_lowercase())
        .is_some_and(|e| DOC_EXTENSIONS.binary_search(&e.as_str()).is_ok());
    let seg_in = |table: &[&str]| {
        segs.iter().any(|s| {
            let lower = s.to_ascii_lowercase();
            table.binary_search(&lower.as_str()).is_ok()
        })
    };
    if doc_ext || seg_in(DOC_SEGMENTS) {
        return Some((GROUP_DOCUMENTATION, "docs"));
    }
    if seg_in(SCAFFOLD_SEGMENTS) {
        return Some((GROUP_BUILD_TOOLING, "scaffold"));
    }
    if segs.is_empty() {
        return Some((GROUP_REPO_ROOT, "root")); // repo-root stray
    }
    None
}

/// True when a file path is excluded from the analyzable clustering scope
/// (it belongs to an infrastructure group instead — see
/// [`infrastructure_group`]).
fn is_scaffold_path(path: &str) -> bool {
    infrastructure_group(path).is_some()
}

/// True when a path sits under a test directory ([`TEST_SEGMENTS`]) — the
/// population the test-folding rule re-homes by dependency subject.
fn is_test_path(path: &str) -> bool {
    let mut segs: Vec<&str> = path.split(['/', '\\']).filter(|s| !s.is_empty()).collect();
    segs.pop(); // only directories mark a test tree
    segs.iter().any(|s| {
        let lower = s.to_ascii_lowercase();
        TEST_SEGMENTS.binary_search(&lower.as_str()).is_ok()
    })
}

/// A shallow unit for excluded (infrastructure-group) files: their first two
/// directory segments (`src/data-plane`), one segment when that is all there
/// is (`scripts`), `(root)` for repo-root files. Excluded files never run
/// through the trunk-aware unit derivation — their unit is presentation-only
/// (the subdomain row under their group).
fn shallow_unit(path: &str) -> String {
    let mut dirs: Vec<&str> = path.split(['/', '\\']).filter(|s| !s.is_empty()).collect();
    dirs.pop();
    match dirs.len() {
        0 => "(root)".to_string(),
        1 => dirs[0].to_string(),
        _ => format!("{}/{}", dirs[0], dirs[1]),
    }
}

/// Tokenize a symbol name into domain-concept tokens: [`lexicon::tokenize`],
/// keep only tokens classified `concept`, and drop [`NOISE_TOKENS`].
fn concept_tokens(name: &str) -> Vec<String> {
    lexicon::tokenize(name)
        .into_iter()
        .filter(|t| {
            lexicon::classify_token(t) == "concept"
                && NOISE_TOKENS.binary_search(&t.as_str()).is_err()
        })
        .collect()
}

/// One morphological fold step: map a token to a shorter base form that also
/// occurs in `vocab` (`orders`→`order`, `categories`→`category`,
/// `caching`→`cache`, `streaming`→`stream`). `None` when no base form exists.
fn fold_step(token: &str, vocab: &BTreeSet<String>) -> Option<String> {
    if let Some(stem) = token.strip_suffix("ies") {
        let cand = format!("{stem}y");
        if stem.len() >= 3 && vocab.contains(&cand) {
            return Some(cand);
        }
    }
    for suffix in ["es", "s"] {
        if let Some(stem) = token.strip_suffix(suffix) {
            if stem.len() >= 3 && vocab.contains(stem) {
                return Some(stem.to_string());
            }
        }
    }
    if let Some(stem) = token.strip_suffix("ing") {
        if stem.len() >= 3 && vocab.contains(stem) {
            return Some(stem.to_string());
        }
        let cand = format!("{stem}e");
        if stem.len() >= 3 && vocab.contains(&cand) {
            return Some(cand);
        }
    }
    None
}

/// Canonical form of every foldable token in `vocab`, chains compressed to a
/// fixpoint (`orderings`→`ordering`→`order`), bounded for determinism.
fn fold_map(vocab: &BTreeSet<String>) -> BTreeMap<String, String> {
    let mut map: BTreeMap<String, String> = BTreeMap::new();
    for t in vocab {
        if let Some(base) = fold_step(t, vocab) {
            map.insert(t.clone(), base);
        }
    }
    let keys: Vec<String> = map.keys().cloned().collect();
    for k in keys {
        let mut cur = map[&k].clone();
        for _ in 0..4 {
            match map.get(&cur) {
                Some(next) => cur = next.clone(),
                None => break,
            }
        }
        map.insert(k, cur);
    }
    map
}

/// The dominant token of a tally: highest count, ties broken by the
/// lexicographically smallest token (BTreeMap order makes this a single
/// deterministic scan).
fn dominant(tokens: &BTreeMap<String, u64>) -> Option<String> {
    let mut best: Option<(&str, u64)> = None;
    for (tok, count) in tokens {
        match best {
            Some((_, c)) if *count <= c => {}
            _ => best = Some((tok.as_str(), *count)),
        }
    }
    best.map(|(t, _)| t.to_string())
}

/// The first path segment of a unit name: its *path family*
/// (`control-plane/connectors` → `control-plane`).
fn family(unit: &str) -> &str {
    unit.split('/').next().unwrap_or(unit)
}

/// The first name word of a unit's family: its *name family*
/// (`Ordering.API/Commands` → `Ordering`) — the DDD-style prefix that groups
/// `Feature.Tier` projects.
fn name_family(unit: &str) -> &str {
    family(unit)
        .split(['.', '_', '-'])
        .next()
        .unwrap_or(family(unit))
}

/// The last path segment of a unit name (`clone/Basket.API` → `Basket.API`).
fn basename(unit: &str) -> &str {
    unit.rsplit('/').next().unwrap_or(unit)
}

/// The *name stem* of a unit: its name family tokenized, trailing role
/// tokens (`client`, `api`, `service`, …) stripped while more than one token
/// remains, concatenated, and plural-folded (`Webhooks` → `webhook`).
/// `Webhooks.API` and `WebhookClient` share the stem `webhook`: one feature
/// family split across suffix-role naming variants.
fn family_stem(unit: &str) -> String {
    let mut tokens = lexicon::tokenize(name_family(unit));
    while tokens.len() > 1
        && tokens
            .last()
            .is_some_and(|t| lexicon::classify_token(t) == "role")
    {
        tokens.pop();
    }
    let mut stem = tokens.concat();
    if stem.len() >= 5 && stem.ends_with('s') && !stem.ends_with("ss") {
        stem.pop();
    }
    stem
}

/// The common leading word prefix of a set of names, cut at a `.`/`_`/`-`
/// word boundary and keeping the original separators
/// (`Ordering.API`+`Ordering.Domain` → `Ordering`; a single name is its own
/// prefix); empty when they share nothing.
fn common_name_prefix(names: &BTreeSet<&str>) -> String {
    let mut iter = names.iter();
    let Some(first) = iter.next() else {
        return String::new();
    };
    if names.len() == 1 {
        return (*first).to_string();
    }
    // Longest common byte prefix across all names.
    let mut common = first.len();
    for n in names {
        common = common.min(
            first
                .bytes()
                .zip(n.bytes())
                .take_while(|(a, b)| a == b)
                .count(),
        );
    }
    // Trim back to a word boundary: every name must either end here or
    // continue with a separator-delimited word (the boundary byte itself is
    // a separator inside the common prefix, or the cut is exact).
    let is_sep = |b: u8| b == b'.' || b == b'_' || b == b'-';
    let mut cut = common;
    while cut > 0 {
        let boundary = names
            .iter()
            .all(|n| n.len() == cut || n.as_bytes().get(cut).copied().is_some_and(is_sep));
        if boundary && !is_sep(first.as_bytes()[cut - 1]) {
            break;
        }
        cut -= 1;
    }
    first[..cut].to_string()
}

/// Per-domain metadata carried by a [`DomainAssignment`]: everything the
/// emitted domain node states about itself.
#[derive(Clone, Debug)]
pub struct DomainInfo {
    /// The deterministic structural label (same string as the domain name;
    /// `platform` for `Shared/Platform`). Kept as a separate field so an
    /// external naming pass can upgrade names while the structural label
    /// stays attested.
    pub label: String,
    /// Distinct units spanned by the member files.
    pub unit_count: u64,
    /// Member file count.
    pub file_count: u64,
    /// Symbols owned by the member files.
    pub symbol_count: u64,
    /// `high` when one path family carries ≥ 2/3 of the domain's symbols
    /// (the label is strong evidence), `medium` otherwise, `low` for
    /// `Shared/Platform`. Infrastructure groups are `high` — their
    /// membership is a deterministic path classification, not a clustering.
    pub confidence: &'static str,
    /// [`KIND_BUSINESS`] for clustered code domains (including
    /// `Shared/Platform`), [`KIND_INFRASTRUCTURE`] for the named groups.
    pub kind: &'static str,
    /// The group's exclusion reason (`scaffold`/`docs`/`generated`/`root`);
    /// `None` for business domains.
    pub reason: Option<&'static str>,
}

/// The core domain assignment, exposed so other passes (the hierarchy
/// extractor) consume the *same* clustering the domains view emits — one
/// source of truth, never a re-derivation.
#[derive(Clone, Debug, Default)]
pub struct DomainAssignment {
    /// Eligible file node id → owning domain display name. Every eligible
    /// file is assigned exactly once.
    pub file_domain: BTreeMap<String, String>,
    /// Eligible file node id → source path (from the File node's `path`).
    pub file_path: BTreeMap<String, String>,
    /// Eligible file node id → count of symbols the file owns.
    pub file_symbols: BTreeMap<String, u64>,
    /// Eligible file node id → its unit (the subdomain level).
    pub file_unit: BTreeMap<String, String>,
    /// Domain display name → per-domain metadata.
    pub domains: BTreeMap<String, DomainInfo>,
    /// Counted inter-domain dependencies: `(from, to)` display names →
    /// cross-domain [`DEPENDS`]-family edge mass.
    ///
    /// [`DEPENDS`]: crate::ir::ontology::relation::DEPENDS
    pub domain_deps: BTreeMap<(String, String), u64>,
}

/// Deterministic greedy modularity over the unit graph: Louvain-style local
/// moves in sorted node order (ties to the smallest community id), then
/// greedy community merges while any merge still improves modularity. All
/// comparisons are exact integer cross-products (i128) — no floats. The
/// symbol-mass cap is enforced on every move and merge.
struct Modularity {
    /// Symmetric adjacency: `adj[i]` maps neighbor index → edge weight.
    adj: Vec<BTreeMap<usize, u64>>,
    /// Weighted degree per node (sum of incident edge weights).
    deg: Vec<u64>,
    /// Symbol mass per node (for the cap).
    sym: Vec<u64>,
    /// Twice the total edge weight.
    m2: u64,
    /// Total symbol mass of the whole repo (for the cap).
    total: u64,
    /// Community id per node.
    comm: Vec<usize>,
}

impl Modularity {
    fn new(n: usize, sym: Vec<u64>, total: u64) -> Self {
        Modularity {
            adj: vec![BTreeMap::new(); n],
            deg: vec![0; n],
            sym,
            m2: 0,
            total,
            comm: (0..n).collect(),
        }
    }

    fn add_edge(&mut self, i: usize, j: usize, w: u64) {
        if i == j || w == 0 {
            return;
        }
        *self.adj[i].entry(j).or_default() += w;
        *self.adj[j].entry(i).or_default() += w;
        self.deg[i] += w;
        self.deg[j] += w;
        self.m2 += 2 * w;
    }

    /// True when adding `extra` symbols to community `c` (whose current mass
    /// is in `comm_sym`) stays under the anti-collapse cap.
    fn cap_ok(&self, comm_sym: &[u64], c: usize, extra: u64) -> bool {
        (comm_sym[c] + extra) * CAP_DEN < self.total * CAP_NUM
    }

    /// One sweep of local moves in sorted node order. Returns whether any
    /// node moved.
    fn local_pass(&mut self, comm_tot: &mut [u64], comm_sym: &mut [u64]) -> bool {
        let n = self.adj.len();
        let mut moved = false;
        for i in 0..n {
            let ci = self.comm[i];
            // Mass from node i to each neighboring community.
            let mut mass: BTreeMap<usize, u64> = BTreeMap::new();
            for (&j, &w) in &self.adj[i] {
                *mass.entry(self.comm[j]).or_default() += w;
            }
            comm_tot[ci] -= self.deg[i];
            comm_sym[ci] -= self.sym[i];
            let base = (mass.get(&ci).copied().unwrap_or(0) as i128) * (self.m2 as i128)
                - (comm_tot[ci] as i128) * (self.deg[i] as i128);
            let mut best = (base, ci);
            for (&cc, &m) in &mass {
                if cc == ci || !self.cap_ok(comm_sym, cc, self.sym[i]) {
                    continue;
                }
                let gain = (m as i128) * (self.m2 as i128)
                    - (comm_tot[cc] as i128) * (self.deg[i] as i128);
                if gain > best.0 || (gain == best.0 && cc < best.1) {
                    best = (gain, cc);
                }
            }
            comm_tot[best.1] += self.deg[i];
            comm_sym[best.1] += self.sym[i];
            if best.1 != ci {
                self.comm[i] = best.1;
                moved = true;
            }
        }
        moved
    }

    /// Run to fixpoint: local passes, then greedy pairwise community merges
    /// while any merge has positive modularity gain (best gain first, ties
    /// to the lexicographically smallest community pair).
    fn run(&mut self) {
        if self.m2 == 0 {
            return;
        }
        let n = self.adj.len();
        let mut comm_tot = vec![0u64; n];
        let mut comm_sym = vec![0u64; n];
        for i in 0..n {
            comm_tot[self.comm[i]] += self.deg[i];
            comm_sym[self.comm[i]] += self.sym[i];
        }
        for _ in 0..64 {
            if !self.local_pass(&mut comm_tot, &mut comm_sym) {
                break;
            }
        }
        // Greedy completion: merge whole communities while it pays.
        loop {
            let mut ctot: BTreeMap<usize, u64> = BTreeMap::new();
            let mut csym: BTreeMap<usize, u64> = BTreeMap::new();
            let mut cmass: BTreeMap<(usize, usize), u64> = BTreeMap::new();
            for i in 0..n {
                *ctot.entry(self.comm[i]).or_default() += self.deg[i];
                *csym.entry(self.comm[i]).or_default() += self.sym[i];
                for (&j, &w) in &self.adj[i] {
                    let (a, b) = (self.comm[i], self.comm[j]);
                    if a < b {
                        *cmass.entry((a, b)).or_default() += w;
                    }
                }
            }
            let mut best: Option<(i128, usize, usize)> = None;
            for (&(a, b), &w) in &cmass {
                if (csym[&a] + csym[&b]) * CAP_DEN >= self.total * CAP_NUM {
                    continue;
                }
                let gain =
                    (w as i128) * (self.m2 as i128) - (ctot[&a] as i128) * (ctot[&b] as i128);
                if gain > 0 && best.is_none_or(|(g, _, _)| gain > g) {
                    best = Some((gain, a, b));
                }
            }
            let Some((_, a, b)) = best else { break };
            for c in self.comm.iter_mut() {
                if *c == b {
                    *c = a;
                }
            }
        }
    }
}

/// Everything the clustering needs about one unit.
#[derive(Default)]
struct UnitStats {
    symbols: u64,
    fan_in: u64,
    fan_out: u64,
    ext: u64,
    in_units: BTreeSet<String>,
    in_name_families: BTreeSet<String>,
}

/// Run the structural domain clustering (see the module doc) over the base
/// graph. This is the single source of truth for file→domain membership;
/// [`DomainExtractor::extract`] and the hierarchy extractor both build their
/// output from it. Pure and deterministic: same graph, same assignment.
pub fn assign_domains(graph: &Graph) -> DomainAssignment {
    // Node kinds by id, for File detection during the containment walk.
    let kind_of: BTreeMap<&str, &'static str> =
        graph.nodes().map(|n| (n.id.as_str(), n.kind)).collect();

    // Containment parents (child → parent), preferring a File parent so a
    // method reached both by `File DECLARES fn` and `Type HAS_METHOD fn`
    // resolves to its file. First-seen wins among equals (edges iterate in
    // stable signature order), keeping the choice deterministic.
    let mut parent: BTreeMap<&str, &str> = BTreeMap::new();
    for e in graph.edges() {
        if parent_relation(e.kind) != Some(relation::CONTAINMENT) {
            continue;
        }
        let from_is_file = kind_of.get(e.from.as_str()).copied() == Some(ont::FILE);
        match parent.get(e.to.as_str()) {
            None => {
                parent.insert(e.to.as_str(), e.from.as_str());
            }
            Some(existing) => {
                let existing_is_file = kind_of.get(existing).copied() == Some(ont::FILE);
                if from_is_file && !existing_is_file {
                    parent.insert(e.to.as_str(), e.from.as_str());
                }
            }
        }
    }
    // Bounded walk to the owning File: containment chains are shallow;
    // the bound only guards against a malformed cyclic containment.
    fn resolve_file<'g>(
        kind_of: &BTreeMap<&'g str, &'static str>,
        parent: &BTreeMap<&'g str, &'g str>,
        mut id: &'g str,
    ) -> Option<&'g str> {
        for _ in 0..64 {
            if kind_of.get(id).copied() == Some(ont::FILE) {
                return Some(id);
            }
            id = parent.get(id)?;
        }
        None
    }

    // Step 1 — scaffold filter: every File node with a path is tracked
    // (zero-ungrouped: excluded files land in infrastructure groups), and
    // the analyzable subset (`path_of_file`) is what gets clustered.
    let mut all_file_path: BTreeMap<&str, &str> = BTreeMap::new();
    let mut path_of_file: BTreeMap<&str, &str> = BTreeMap::new();
    for n in graph.nodes().filter(|n| n.kind == ont::FILE) {
        if let Some(Json::Str(path)) = n.props.get("path") {
            all_file_path.insert(n.id.as_str(), path.as_str());
            if !is_scaffold_path(path) {
                path_of_file.insert(n.id.as_str(), path.as_str());
            }
        }
    }

    // Per-file symbol counts (all files, so group nodes report honest
    // tallies) and concept-token tallies for the analyzable subset only (the
    // lexicon is a *signal*: Shared/Platform detection, edgeless folds,
    // label tie-breaks). Excluded symbol mass never enters `total` or any
    // clustering threshold — scope stability: junk mass cannot strip a src
    // file of its domain.
    let mut file_symbols: BTreeMap<&str, u64> = BTreeMap::new();
    let mut file_tokens: BTreeMap<&str, BTreeMap<String, u64>> = BTreeMap::new();
    for n in graph.nodes() {
        if n.kind == ont::FILE {
            continue; // files are containers, not symbols.
        }
        let Some(file) = resolve_file(&kind_of, &parent, n.id.as_str()) else {
            continue;
        };
        if !all_file_path.contains_key(file) {
            continue; // no path — not placeable anywhere.
        }
        *file_symbols.entry(file).or_default() += 1;
        if !path_of_file.contains_key(file) {
            continue; // excluded file: counted, never tokenized/clustered.
        }
        let tally = file_tokens.entry(file).or_default();
        for t in concept_tokens(&n.name) {
            *tally.entry(t).or_default() += 1;
        }
    }
    // Morphological fold over the observed vocabulary, applied to every
    // tally so `order`/`orders`/`ordering` count as one concept.
    let vocab: BTreeSet<String> = file_tokens
        .values()
        .flat_map(|t| t.keys().cloned())
        .collect();
    let folds = fold_map(&vocab);
    for tally in file_tokens.values_mut() {
        let folded: Vec<(String, u64)> = tally
            .iter()
            .filter(|(t, _)| folds.contains_key(*t))
            .map(|(t, c)| (folds[t].clone(), *c))
            .collect();
        if folded.is_empty() {
            continue;
        }
        tally.retain(|t, _| !folds.contains_key(t));
        for (base, c) in folded {
            *tally.entry(base).or_default() += c;
        }
    }

    // Analyzable symbol mass only: every threshold below is a ratio of this
    // total, so excluded (scaffold/docs/generated/root) mass cannot move it.
    let total: u64 = path_of_file
        .keys()
        .map(|f| file_symbols.get(f).copied().unwrap_or(0))
        .sum();

    // Step 2 — units: first two load-bearing directory segments per path.
    // Subtree file counts drive the trunk rule.
    let mut subtree: BTreeMap<String, u64> = BTreeMap::new();
    for path in path_of_file.values() {
        let mut dirs: Vec<&str> = path.split(['/', '\\']).filter(|s| !s.is_empty()).collect();
        dirs.pop();
        let mut prefix = String::new();
        *subtree.entry(prefix.clone()).or_default() += 1;
        for seg in &dirs {
            if !prefix.is_empty() {
                prefix.push('/');
            }
            prefix.push_str(seg);
            *subtree.entry(prefix.clone()).or_default() += 1;
        }
    }
    let unit_of = |path: &str| -> String {
        let mut dirs: Vec<&str> = path.split(['/', '\\']).filter(|s| !s.is_empty()).collect();
        dirs.pop();
        let mut picked: Vec<&str> = Vec::new();
        let mut prefix = String::new();
        let mut last_named: Option<&str> = None;
        for seg in dirs {
            let parent_files = subtree.get(&prefix).copied().unwrap_or(0);
            let child = if prefix.is_empty() {
                seg.to_string()
            } else {
                format!("{prefix}/{seg}")
            };
            let child_files = subtree.get(&child).copied().unwrap_or(0);
            let lower = seg.to_ascii_lowercase();
            let forced = TRANSPARENT_SEGMENTS.binary_search(&lower.as_str()).is_ok();
            let transparent = forced || child_files * TRUNK_DEN >= parent_files * TRUNK_NUM;
            if !forced {
                last_named = Some(seg);
            }
            if !transparent {
                picked.push(seg);
            }
            prefix = child;
            if picked.len() == 2 {
                break;
            }
        }
        // A trailing trunk chain (`tests/OnlyProject/…`, `clone/tests/…`)
        // still names its deepest segment, so a prefixed copy derives units
        // symmetric to its original (the mirror fold depends on it).
        if picked.len() < 2 {
            if let Some(l) = last_named {
                if picked.last() != Some(&l) {
                    picked.push(l);
                }
            }
        }
        if picked.is_empty() {
            "(root)".to_string()
        } else {
            picked.join("/")
        }
    };
    let mut file_unit: BTreeMap<&str, String> =
        path_of_file.iter().map(|(f, p)| (*f, unit_of(p))).collect();

    // Mirror-unit fold: a unit that is a byte-identical prefix-copy of
    // another folds into the original before clustering (module-copy /
    // whole-codebase duplication stability). Grouped by (unit basename,
    // sorted file basenames + symbol counts) so the pairwise path check
    // only runs on real candidates.
    {
        let mut unit_files_v: BTreeMap<&str, Vec<(&str, u64)>> = BTreeMap::new();
        for (f, u) in &file_unit {
            unit_files_v
                .entry(u.as_str())
                .or_default()
                .push((path_of_file[f], file_symbols.get(f).copied().unwrap_or(0)));
        }
        let shape = |paths: &[(&str, u64)]| -> Vec<(String, u64)> {
            let mut v: Vec<(String, u64)> = paths
                .iter()
                .map(|(p, s)| (p.rsplit(['/', '\\']).next().unwrap_or(p).to_string(), *s))
                .collect();
            v.sort();
            v
        };
        // Duplicate-candidate key: (unit basename, sorted file basenames +
        // per-file symbol counts). Units sharing a key *may* be mirrors.
        type MirrorKey = (String, Vec<(String, u64)>);
        let mut groups: BTreeMap<MirrorKey, Vec<&str>> = BTreeMap::new();
        for (u, paths) in &unit_files_v {
            groups
                .entry((basename(u).to_string(), shape(paths)))
                .or_default()
                .push(u);
        }
        // b folds into a when every path of b = one fixed prefix + a path
        // of a (files matched in sorted order).
        let folds_into = |a: &str, b: &str| -> bool {
            let mut pa: Vec<&str> = unit_files_v[a].iter().map(|(p, _)| *p).collect();
            let mut pb: Vec<&str> = unit_files_v[b].iter().map(|(p, _)| *p).collect();
            if pa.len() != pb.len() {
                return false;
            }
            pa.sort_unstable();
            pb.sort_unstable();
            let (first_a, first_b) = (pa[0], pb[0]);
            if first_b.len() <= first_a.len() || !first_b.ends_with(first_a) {
                return false;
            }
            let prefix = &first_b[..first_b.len() - first_a.len()];
            pa.iter().zip(&pb).all(|(x, y)| {
                y.len() == prefix.len() + x.len() && y.starts_with(prefix) && y.ends_with(x)
            })
        };
        let mut remap: BTreeMap<String, String> = BTreeMap::new();
        for members in groups.values() {
            if members.len() < 2 {
                continue;
            }
            for i in 0..members.len() {
                if remap.contains_key(members[i]) {
                    continue;
                }
                for j in 0..members.len() {
                    if i == j || remap.contains_key(members[j]) {
                        continue;
                    }
                    if folds_into(members[i], members[j]) {
                        remap.insert(members[j].to_string(), members[i].to_string());
                    }
                }
            }
        }
        if !remap.is_empty() {
            for u in file_unit.values_mut() {
                if let Some(target) = remap.get(u.as_str()) {
                    *u = target.clone();
                }
            }
        }
    }

    let mut stats: BTreeMap<&str, UnitStats> = BTreeMap::new();
    for (f, u) in &file_unit {
        stats.entry(u.as_str()).or_default().symbols += file_symbols.get(f).copied().unwrap_or(0);
    }

    // Step 3 — dependency mass: file-level (kept for coupling + emit) and
    // unit-level, plus per-unit external mass.
    let mut file_deps: BTreeMap<(&str, &str), u64> = BTreeMap::new();
    let mut unit_deps: BTreeMap<(&str, &str), u64> = BTreeMap::new();
    for e in graph.edges() {
        if parent_relation(e.kind) != Some(relation::DEPENDS) {
            continue;
        }
        let from = resolve_file(&kind_of, &parent, e.from.as_str());
        if let Some(from) = from {
            if path_of_file.contains_key(from)
                && kind_of.get(e.to.as_str()).copied() == Some(ont::EXTERNAL_DEPENDENCY)
            {
                stats.entry(file_unit[from].as_str()).or_default().ext += 1;
            }
        }
        let (Some(from), Some(to)) = (from, resolve_file(&kind_of, &parent, e.to.as_str())) else {
            continue;
        };
        if from == to || !path_of_file.contains_key(from) || !path_of_file.contains_key(to) {
            continue;
        }
        *file_deps.entry((from, to)).or_default() += 1;
        let (u, v) = (file_unit[from].as_str(), file_unit[to].as_str());
        if u != v {
            *unit_deps.entry((u, v)).or_default() += 1;
        }
    }
    for ((u, v), c) in &unit_deps {
        stats.entry(u).or_default().fan_out += c;
        let sv = stats.entry(v).or_default();
        sv.fan_in += c;
        sv.in_units.insert(u.to_string());
        if name_family(u) != name_family(v) {
            sv.in_name_families.insert(name_family(u).to_string());
        }
    }

    let units: Vec<&str> = stats.keys().copied().collect();
    let mut name_family_mass: BTreeMap<&str, u64> = BTreeMap::new();
    for u in &units {
        *name_family_mass.entry(name_family(u)).or_default() += stats[u].symbols;
    }

    // Step 4 — prior (c): cross-cutting carve-outs.
    // External-integration adapters: external mass above all internal
    // traffic, consumed by >= 3 units, and consuming almost nothing internal.
    let mut adapters: BTreeSet<&str> = BTreeSet::new();
    for u in &units {
        let s = &stats[u];
        if s.ext > s.fan_in + s.fan_out && s.fan_in > s.fan_out && s.in_units.len() >= 3 {
            adapters.insert(u);
        }
    }
    // Shared kernels: units of small name-families depended on by >= 3
    // other name-families — pooled straight into Shared/Platform.
    let mut kernels: BTreeSet<&str> = BTreeSet::new();
    for u in &units {
        if adapters.contains(u) {
            continue;
        }
        let s = &stats[u];
        if name_family_mass[name_family(u)] * KERNEL_FAMILY_DIVISOR < total
            && s.in_name_families.len() >= 3
            && s.fan_in > s.fan_out
        {
            kernels.insert(u);
        }
    }

    // Step 5 — communities over the remaining units.
    let core: Vec<&str> = units
        .iter()
        .filter(|u| !adapters.contains(*u) && !kernels.contains(*u))
        .copied()
        .collect();
    let uidx: BTreeMap<&str, usize> = core.iter().enumerate().map(|(i, u)| (*u, i)).collect();
    let sym: Vec<u64> = core.iter().map(|u| stats[u].symbols).collect();
    let mut modularity = Modularity::new(core.len(), sym, total.max(1));
    let mut dep_total = 0u64;
    for ((u, v), c) in &unit_deps {
        if let (Some(&i), Some(&j)) = (uidx.get(u), uidx.get(v)) {
            modularity.add_edge(i, j, *c);
            dep_total += c;
        }
    }
    // Prior (a): path-family star+chain pseudo-edges.
    let star_w = (dep_total / STAR_DIVISOR).max(1);
    let mut fam_units: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for u in &core {
        fam_units.entry(family(u)).or_default().push(u);
    }
    for members in fam_units.values() {
        if members.len() < 2 {
            continue;
        }
        // Center: largest symbol mass, ties to the lexicographically last
        // (deterministic either way; matches the sorted-scan below).
        let center = members
            .iter()
            .max_by_key(|u| (stats[**u].symbols, **u))
            .copied()
            .expect("non-empty family");
        let mut prev: Option<&str> = None;
        for u in members {
            if *u != center {
                modularity.add_edge(uidx[*u], uidx[center], star_w);
            }
            if let Some(p) = prev {
                modularity.add_edge(uidx[p], uidx[*u], star_w);
            }
            prev = Some(u);
        }
    }
    // Prior (a′): *suffix-role naming variants attract*. `Webhooks.API` and
    // `WebhookClient` are one feature family split across naming variants —
    // grouping units by name stem adds the same weak star+chain pseudo-edges
    // between the variants. Groups whose units all share one name family are
    // skipped: the stem prior only bridges naming variants, it never adds
    // mass inside a family the other priors already see.
    let mut stem_units: BTreeMap<String, Vec<&str>> = BTreeMap::new();
    for u in &core {
        let stem = family_stem(u);
        if !stem.is_empty() {
            stem_units.entry(stem).or_default().push(u);
        }
    }
    for members in stem_units.values() {
        let names: BTreeSet<&str> = members.iter().map(|u| name_family(u)).collect();
        if names.len() < 2 {
            continue;
        }
        let center = members
            .iter()
            .max_by_key(|u| (stats[**u].symbols, **u))
            .copied()
            .expect("non-empty stem group");
        let mut prev: Option<&str> = None;
        for u in members {
            if *u != center {
                modularity.add_edge(uidx[*u], uidx[center], star_w);
            }
            if let Some(p) = prev {
                modularity.add_edge(uidx[p], uidx[*u], star_w);
            }
            prev = Some(u);
        }
    }
    modularity.run();

    // Collect communities: sorted unit lists, ordered by (-mass, first unit).
    let mut by_comm: BTreeMap<usize, Vec<&str>> = BTreeMap::new();
    for (i, u) in core.iter().enumerate() {
        by_comm.entry(modularity.comm[i]).or_default().push(u);
    }
    let mut communities: Vec<Vec<&str>> = by_comm.into_values().collect();
    if !adapters.is_empty() {
        communities.push(adapters.iter().copied().collect());
    }
    let mass_of = |us: &[&str]| -> u64 { us.iter().map(|u| stats[u].symbols).sum() };
    communities.sort_by(|a, b| {
        mass_of(b)
            .cmp(&mass_of(a))
            .then_with(|| a.first().cmp(&b.first()))
    });

    // Helpers over communities.
    let files_of = |us: &[&str]| -> Vec<&str> {
        let set: BTreeSet<&str> = us.iter().copied().collect();
        path_of_file
            .keys()
            .filter(|f| set.contains(file_unit[*f].as_str()))
            .copied()
            .collect()
    };
    let dominant_concept = |us: &[&str]| -> Option<String> {
        let mut tally: BTreeMap<String, u64> = BTreeMap::new();
        for f in files_of(us) {
            if let Some(t) = file_tokens.get(f) {
                for (tok, c) in t {
                    *tally.entry(tok.clone()).or_default() += c;
                }
            }
        }
        dominant(&tally)
    };
    let coupling = |us: &[&str], vs: &[&str]| -> u64 {
        let a: BTreeSet<&str> = us.iter().copied().collect();
        let b: BTreeSet<&str> = vs.iter().copied().collect();
        unit_deps
            .iter()
            .filter(|((u, v), _)| {
                (a.contains(u) && b.contains(v)) || (b.contains(u) && a.contains(v))
            })
            .map(|(_, c)| *c)
            .sum()
    };

    // Step 6 — floor: absorb sub-floor communities into their most-coupled
    // community (cap-respecting); the uncoupled remainder goes to
    // Shared/Platform.
    communities.sort_by(|a, b| {
        mass_of(b)
            .cmp(&mass_of(a))
            .then_with(|| a.first().cmp(&b.first()))
    });
    let mut surviving: Vec<Vec<&str>> = Vec::new();
    let mut tiny: Vec<Vec<&str>> = Vec::new();
    for us in communities {
        if mass_of(&us) * FLOOR_DIVISOR >= total {
            surviving.push(us);
        } else {
            tiny.push(us);
        }
    }
    let mut shared_units: Vec<&str> = kernels.iter().copied().collect();
    for us in tiny {
        let mut ranked: Vec<(u64, usize)> = surviving
            .iter()
            .enumerate()
            .filter_map(|(k, vs)| {
                let c = coupling(&us, vs);
                (c > 0).then_some((c, k))
            })
            .collect();
        ranked.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));
        let mut placed = false;
        for (_, k) in &ranked {
            if surviving.len() == 1
                || (mass_of(&surviving[*k]) + mass_of(&us)) * CAP_DEN < total * CAP_NUM
            {
                surviving[*k].extend(us.iter().copied());
                surviving[*k].sort_unstable();
                placed = true;
                break;
            }
        }
        if !placed {
            if ranked.is_empty() {
                shared_units.extend(us);
            } else {
                surviving.push(us); // coupled but every target capped
            }
        }
    }
    if surviving.is_empty() && !shared_units.is_empty() {
        // Degenerate repo: nothing but shared plumbing. Emit it as-is.
        surviving.push(std::mem::take(&mut shared_units));
    }

    // Step 6d — legibility guard: at most MAX_DOMAINS communities.
    while surviving.len() > MAX_DOMAINS {
        surviving.sort_by(|a, b| {
            mass_of(b)
                .cmp(&mass_of(a))
                .then_with(|| a.first().cmp(&b.first()))
        });
        let smallest = surviving.pop().expect("len > MAX_DOMAINS >= 1");
        let mut ranked: Vec<(u64, usize)> = surviving
            .iter()
            .enumerate()
            .filter_map(|(k, vs)| {
                let c = coupling(&smallest, vs);
                (c > 0 && (mass_of(vs) + mass_of(&smallest)) * CAP_DEN < total * CAP_NUM)
                    .then_some((c, k))
            })
            .collect();
        ranked.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));
        let k = ranked
            .first()
            .map(|(_, k)| *k)
            .unwrap_or(surviving.len() - 1);
        surviving[k].extend(smallest);
        surviving[k].sort_unstable();
    }
    surviving.sort_by(|a, b| {
        mass_of(b)
            .cmp(&mass_of(a))
            .then_with(|| a.first().cmp(&b.first()))
    });

    // Step 7 — labels (no LLM): dominant path family → common name prefix →
    // generic-container replacement → collision extension (second segment,
    // then concept token, then #k).
    let mut used: BTreeSet<String> = BTreeSet::new();
    let mut labels: Vec<String> = Vec::new();
    // Per domain: the name families of its majority (label-driving) path
    // families — the families whose paths *are* the domain's identity. Used
    // by step 8's unit-loyalty rule.
    let mut loyal_names: Vec<BTreeSet<String>> = Vec::new();
    for us in &surviving {
        let mass = mass_of(us);
        let mut fams: BTreeMap<&str, u64> = BTreeMap::new();
        for u in us {
            *fams.entry(family(u)).or_default() += stats[u].symbols;
        }
        // The label comes from the smallest set of families (largest mass
        // first) that carries >= 2/3 of the domain's symbols: their common
        // name prefix (one family -> its own name), so a stray coupled
        // utility cannot spoil `Ordering.API`+`Ordering.Domain` -> `Ordering`.
        let mut ranked_fams: Vec<(&str, u64)> = fams.iter().map(|(f, m)| (*f, *m)).collect();
        ranked_fams.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
        let mut majority: BTreeSet<&str> = BTreeSet::new();
        let mut acc = 0u64;
        for (f, m) in &ranked_fams {
            majority.insert(f);
            acc += m;
            if acc * 3 >= mass * 2 {
                break;
            }
        }
        loyal_names.push(
            majority
                .iter()
                .map(|f| name_family(f).to_string())
                .collect(),
        );
        let domfam = ranked_fams
            .first()
            .map(|(f, _)| f.to_string())
            .unwrap_or_else(|| "(root)".to_string());
        let prefix = common_name_prefix(&majority);
        let mut cand = if prefix.is_empty() {
            domfam.clone()
        } else {
            prefix
        };
        let dominant_second = || -> Option<String> {
            let mut seconds: BTreeMap<&str, u64> = BTreeMap::new();
            for u in us {
                if let Some((_, rest)) = u.split_once('/') {
                    *seconds.entry(rest).or_default() += stats[u].symbols;
                }
            }
            seconds
                .iter()
                .max_by(|a, b| a.1.cmp(b.1).then(b.0.cmp(a.0)))
                .map(|(s, _)| s.to_string())
        };
        if GENERIC_LABEL_SEGMENTS
            .binary_search(&cand.to_ascii_lowercase().as_str())
            .is_ok()
        {
            if let Some(s) = dominant_second() {
                cand = s;
            } else if let Some(c) = dominant_concept(us) {
                // Degenerate single-unit repo (everything under `src/`, no
                // deeper decomposition): the path carries no name at all, so
                // the concept tie-break is the only honest signal left.
                cand = c;
            }
        }
        // Reserved names a business label may never claim: Shared/Platform
        // and the infrastructure group names.
        let reserved =
            |c: &String| used.contains(c) || c == SHARED_DOMAIN || group_reason(c).is_some();
        if reserved(&cand) {
            if let Some(s) = dominant_second() {
                cand = format!("{cand}/{s}");
            }
        }
        if reserved(&cand) {
            if let Some(c) = dominant_concept(us) {
                cand = format!("{cand}/{c}");
            }
        }
        let base = cand.clone();
        let mut k = 2;
        while reserved(&cand) {
            cand = format!("{base}#{k}");
            k += 1;
        }
        used.insert(cand.clone());
        labels.push(cand);
    }

    // Step 8 — file membership. Unit → domain from the surviving
    // communities; kernels and floor leftovers are Shared/Platform; a file
    // that is both conceptless and dependency-less is pure plumbing and
    // lands in Shared/Platform regardless of its unit.
    let mut unit_domain: BTreeMap<&str, String> = BTreeMap::new();
    for (label, us) in labels.iter().zip(&surviving) {
        for u in us {
            unit_domain.insert(u, label.clone());
        }
    }
    for u in &shared_units {
        unit_domain.insert(u, SHARED_DOMAIN.to_string());
    }
    let mut dep_files: BTreeSet<&str> = BTreeSet::new();
    for (f, t) in file_deps.keys() {
        dep_files.insert(f);
        dep_files.insert(t);
    }
    // Unit loyalty: a file whose unit's path *names* its domain (the unit's
    // name family is one of the domain's majority name families) never
    // leaves that domain just because it is weakly coupled — an Identity
    // ViewModel with no resolvable edges is still Identity code, not shared
    // plumbing. Only crumbs in units foreign to their domain's identity
    // (`Common/Clock.cs` swept into `Ordering` by a neighbor's coupling) are
    // genuinely uncoupled and fall through to Shared/Platform.
    let domain_loyal: BTreeMap<&str, &BTreeSet<String>> = labels
        .iter()
        .map(String::as_str)
        .zip(loyal_names.iter())
        .collect();
    let mut domain_of_file: BTreeMap<&str, String> = BTreeMap::new();
    for f in path_of_file.keys() {
        let conceptless = file_tokens.get(f).is_none_or(|t| t.is_empty());
        let edgeless = !dep_files.contains(f);
        let home = unit_domain[file_unit[f].as_str()].as_str();
        let loyal = domain_loyal
            .get(home)
            .is_some_and(|names| names.contains(name_family(&file_unit[f])));
        let domain = if conceptless && edgeless && !loyal {
            SHARED_DOMAIN.to_string()
        } else {
            home.to_string()
        };
        domain_of_file.insert(f, domain);
    }

    // Test-folding: a file under a test directory belongs to the domain of
    // the code it *exercises*, resolved through dependency edges — robust on
    // full repos where a tests/ tree would otherwise cohere into its own
    // junk community. Subject = the domain receiving the test file's largest
    // outgoing dependency mass to non-test files (incoming mass as the
    // fallback for harnesses that are only imported). Folds honor the same
    // **anti-collapse cap** every clustering move honors: a fold that would
    // push its target to [`CAP_NUM`]/[`CAP_DEN`] of the analyzable symbols
    // is rejected and the test keeps its own community (a monolith with a
    // huge test tree must not read as one domain swallowing the codebase).
    // A test with no resolvable subject keeps its unit's domain when that
    // domain contains any production code; a pure-test community with no
    // subject anywhere is test *scaffolding*, not a bounded context, and
    // folds into Build & Tooling — never ungrouped either way.
    {
        let is_test: BTreeMap<&str, bool> = path_of_file
            .iter()
            .map(|(f, p)| (*f, is_test_path(p)))
            .collect();
        let mut prod_mass: BTreeMap<String, u64> = BTreeMap::new();
        let mut mass_of_domain: BTreeMap<String, u64> = BTreeMap::new();
        for (f, d) in &domain_of_file {
            let sym = file_symbols.get(f).copied().unwrap_or(0);
            *mass_of_domain.entry(d.clone()).or_default() += sym;
            if !is_test[f] {
                *prod_mass.entry(d.clone()).or_default() += sym;
            }
        }
        let mut outgoing: BTreeMap<&str, Vec<(&str, u64)>> = BTreeMap::new();
        let mut incoming: BTreeMap<&str, Vec<(&str, u64)>> = BTreeMap::new();
        for ((a, b), c) in &file_deps {
            outgoing.entry(a).or_default().push((b, *c));
            incoming.entry(b).or_default().push((a, *c));
        }
        // Subjects and homes are read off the PRE-fold assignment (a
        // snapshot), so folds never chain through each other and the
        // relation is a pure function of the clustering.
        let pre_fold: BTreeMap<&str, String> = domain_of_file
            .iter()
            .map(|(f, d)| (*f, d.clone()))
            .collect();
        let subject_of = |f: &str| -> Option<String> {
            for links in [outgoing.get(f), incoming.get(f)] {
                let mut mass: BTreeMap<&str, u64> = BTreeMap::new();
                for (other, c) in links.into_iter().flatten() {
                    if !is_test[other] {
                        *mass.entry(pre_fold[other].as_str()).or_default() += c;
                    }
                }
                // Highest mass, ties to the lexicographically smallest name.
                if let Some((d, _)) = mass.iter().max_by(|x, y| x.1.cmp(y.1).then(y.0.cmp(x.0))) {
                    return Some((*d).to_string());
                }
            }
            None
        };
        // Sorted file-id order: deterministic, and duplication-stable
        // (masses and the cap scale together under whole-repo duplication).
        for f in path_of_file.keys().copied().collect::<Vec<_>>() {
            if !is_test[&f] {
                continue;
            }
            let current = pre_fold[&f].clone();
            let sym = file_symbols.get(&f).copied().unwrap_or(0);
            let target = match subject_of(f) {
                Some(d) => d,
                None => {
                    let home = unit_domain[file_unit[&f].as_str()].clone();
                    if prod_mass.get(&home).copied().unwrap_or(0) > 0 {
                        home
                    } else {
                        GROUP_BUILD_TOOLING.to_string()
                    }
                }
            };
            if target == current {
                continue;
            }
            // Cap check on business targets only (an infrastructure group is
            // named scaffolding, not a cluster the collapse rule protects).
            if group_reason(&target).is_none() {
                let target_mass = mass_of_domain.get(&target).copied().unwrap_or(0);
                if (target_mass + sym) * CAP_DEN >= total.max(1) * CAP_NUM {
                    continue; // fold rejected: the test keeps its community
                }
            }
            *mass_of_domain.entry(current).or_default() -= sym;
            *mass_of_domain.entry(target.clone()).or_default() += sym;
            domain_of_file.insert(f, target);
        }
    }

    // Negligible-Shared fold: crumbs are not a domain. Each crumb file
    // returns to its own unit's domain (a UI primitive rejoins `dashboard`),
    // with the largest domain only as the fallback for crumbs whose unit is
    // itself shared.
    let shared_mass: u64 = domain_of_file
        .iter()
        .filter(|(_, d)| d.as_str() == SHARED_DOMAIN)
        .map(|(f, _)| file_symbols.get(f).copied().unwrap_or(0))
        .sum();
    if shared_mass * SHARED_FOLD_DIVISOR < total {
        if let Some(largest) = labels.first().cloned() {
            for (f, d) in domain_of_file.iter_mut() {
                if d.as_str() != SHARED_DOMAIN {
                    continue;
                }
                let home = unit_domain
                    .get(file_unit[f].as_str())
                    .filter(|u| u.as_str() != SHARED_DOMAIN);
                *d = home.cloned().unwrap_or_else(|| largest.clone());
            }
        }
    }

    // Zero ungrouped: every excluded file joins its first-class named
    // infrastructure group. Their unit is the shallow presentation-only
    // derivation (excluded files never touched the trunk-aware clustering).
    let mut excluded_unit: BTreeMap<&str, String> = BTreeMap::new();
    for (f, path) in &all_file_path {
        if path_of_file.contains_key(f) {
            continue;
        }
        let (group, _reason) =
            infrastructure_group(path).expect("excluded files always classify into a group");
        domain_of_file.insert(f, group.to_string());
        excluded_unit.insert(f, shallow_unit(path));
    }
    let unit_of_file = |f: &str| -> &str {
        file_unit
            .get(f)
            .or_else(|| excluded_unit.get(f))
            .expect("every grouped file has a unit")
            .as_str()
    };

    // Step 9 — rollup into the assignment.
    let mut members: BTreeMap<String, BTreeSet<&str>> = BTreeMap::new();
    for (f, d) in &domain_of_file {
        members.entry(d.clone()).or_default().insert(f);
    }
    let mut assignment = DomainAssignment::default();
    for (name, files) in &members {
        let shared = name == SHARED_DOMAIN;
        let reason = group_reason(name);
        let symbol_count: u64 = files
            .iter()
            .map(|f| file_symbols.get(f).copied().unwrap_or(0))
            .sum();
        let units_in: BTreeSet<&str> = files.iter().map(|f| unit_of_file(f)).collect();
        let mut fam_mass: BTreeMap<&str, u64> = BTreeMap::new();
        for f in files {
            *fam_mass.entry(family(unit_of_file(f))).or_default() +=
                file_symbols.get(f).copied().unwrap_or(0);
        }
        let top_family = fam_mass.values().max().copied().unwrap_or(0);
        let confidence = if reason.is_some() {
            "high" // deterministic path classification, not a clustering
        } else if shared {
            "low"
        } else if top_family * 3 >= symbol_count * 2 {
            "high"
        } else {
            "medium"
        };
        assignment.domains.insert(
            name.clone(),
            DomainInfo {
                label: if shared {
                    "platform".to_string()
                } else {
                    name.clone()
                },
                unit_count: units_in.len() as u64,
                file_count: files.len() as u64,
                symbol_count,
                confidence,
                kind: if reason.is_some() {
                    KIND_INFRASTRUCTURE
                } else {
                    KIND_BUSINESS
                },
                reason,
            },
        );
        for f in files {
            assignment
                .file_domain
                .insert((*f).to_string(), name.clone());
            assignment
                .file_path
                .insert((*f).to_string(), all_file_path[f].to_string());
            assignment
                .file_symbols
                .insert((*f).to_string(), file_symbols.get(f).copied().unwrap_or(0));
            assignment
                .file_unit
                .insert((*f).to_string(), unit_of_file(f).to_string());
        }
    }

    // Counted inter-domain dependencies from cross-domain file deps.
    for ((from, to), count) in &file_deps {
        let (fd, td) = (&domain_of_file[from], &domain_of_file[to]);
        if fd != td {
            *assignment
                .domain_deps
                .entry((fd.clone(), td.clone()))
                .or_default() += count;
        }
    }

    assignment
}

/// Recover the bounded-context (domain) view from the base graph.
pub struct DomainExtractor;

impl Extractor for DomainExtractor {
    fn name(&self) -> &'static str {
        "domains"
    }

    fn extract(&self, graph: &Graph) -> Graph {
        let assignment = assign_domains(graph);
        let mut out = Graph::new();

        for (name, info) in &assignment.domains {
            let mut props = vec![
                ("view", Json::str(VIEW)),
                ("domain", Json::str(name.clone())),
                ("label", Json::str(info.label.clone())),
                ("unit_count", Json::U64(info.unit_count)),
                ("file_count", Json::U64(info.file_count)),
                ("symbol_count", Json::U64(info.symbol_count)),
                ("confidence", Json::str(info.confidence)),
                ("kind", Json::str(info.kind)),
            ];
            if let Some(reason) = info.reason {
                props.push(("reason", Json::str(reason)));
            }
            out.upsert_node(format!("domain::{name}"), ont::MODULE, name.clone(), props);
        }

        // Subdomain rollup: (domain, unit) → file/symbol counts.
        let mut sub: BTreeMap<(String, String), (u64, u64)> = BTreeMap::new();
        for (f, name) in &assignment.file_domain {
            let unit = assignment.file_unit[f].clone();
            let e = sub.entry((name.clone(), unit)).or_default();
            e.0 += 1;
            e.1 += assignment.file_symbols.get(f).copied().unwrap_or(0);
        }
        for ((name, unit), (files, symbols)) in &sub {
            let id = format!("subdomain::{name}::{unit}");
            out.upsert_node(
                id.clone(),
                ont::MODULE,
                unit.clone(),
                vec![
                    ("view", Json::str(VIEW)),
                    ("domain", Json::str(name.clone())),
                    ("subdomain", Json::str(unit.clone())),
                    ("file_count", Json::U64(*files)),
                    ("symbol_count", Json::U64(*symbols)),
                ],
            );
            out.add_edge(format!("domain::{name}"), edge::CONTAINS, id, vec![]);
        }

        for (f, name) in &assignment.file_domain {
            let path = assignment.file_path[f].as_str();
            out.upsert_node(
                format!("unit::{path}"),
                ont::FILE,
                path.rsplit(['/', '\\']).next().unwrap_or(path),
                vec![
                    ("view", Json::str(VIEW)),
                    ("domain", Json::str(name.clone())),
                    ("unit", Json::str(assignment.file_unit[f].clone())),
                    ("path", Json::str(path)),
                    (
                        "symbol_count",
                        Json::U64(assignment.file_symbols.get(f).copied().unwrap_or(0)),
                    ),
                ],
            );
            out.add_edge(
                format!("domain::{name}"),
                edge::CONTAINS,
                format!("unit::{path}"),
                vec![],
            );
        }

        for ((from, to), count) in &assignment.domain_deps {
            out.add_edge(
                format!("domain::{from}"),
                edge::DEPENDS_ON,
                format!("domain::{to}"),
                vec![("count", Json::U64(*count))],
            );
        }

        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Add a File node with a `path` prop; returns its id.
    fn file(g: &mut Graph, path: &str) -> String {
        let name = path.rsplit('/').next().unwrap().to_string();
        let id = format!("file::{path}");
        g.upsert_node(id.clone(), ont::FILE, name, vec![("path", Json::str(path))]);
        id
    }

    /// Add a symbol declared by `file_id`; returns its id.
    fn sym(g: &mut Graph, file_id: &str, kind: &'static str, name: &str) -> String {
        let id = format!("sym::{file_id}::{name}");
        g.upsert_node(id.clone(), kind, name, vec![]);
        g.add_edge(file_id.to_string(), edge::DECLARES, id.clone(), vec![]);
        id
    }

    /// A hand-built eShop-shaped base graph: three DDD contexts across
    /// `Feature.Tier` projects with realistic *dependency structure* (each
    /// API leans on its own Domain project far more than on anything else),
    /// a concept-free utility coupled to Ordering, pure plumbing, and
    /// scaffold/root files. Structural clustering must recover the three
    /// contexts from the dependency graph, whatever the vocabulary says.
    fn sample_base() -> Graph {
        let mut g = Graph::new();

        // Ordering context: API + Domain projects, heavily coupled.
        let f = file(&mut g, "src/Ordering.API/OrdersApi.cs");
        let create_order = sym(&mut g, &f, ont::FUNCTION, "CreateOrder");
        let ship_order = sym(&mut g, &f, ont::FUNCTION, "ShipOrder");
        sym(&mut g, &f, ont::TYPE, "OrderStatus");
        let f = file(&mut g, "src/Ordering.Domain/Order.cs");
        let order = sym(&mut g, &f, ont::TYPE, "Order");
        let order_item = sym(&mut g, &f, ont::TYPE, "OrderItem");
        sym(&mut g, &f, ont::TYPE, "OrderBuyer");
        g.add_edge(create_order.clone(), edge::USES_TYPE, order.clone(), vec![]);
        g.add_edge(create_order.clone(), edge::USES_TYPE, order_item, vec![]);
        g.add_edge(ship_order.clone(), edge::USES_TYPE, order.clone(), vec![]);

        // Catalog context: API + Infrastructure projects, coupled.
        let f = file(&mut g, "src/Catalog.API/CatalogApi.cs");
        let get_brands = sym(&mut g, &f, ont::FUNCTION, "GetCatalogBrands");
        sym(&mut g, &f, ont::TYPE, "CatalogItemDto");
        let f = file(&mut g, "src/Catalog.Infrastructure/CatalogRepository.cs");
        let repo = sym(&mut g, &f, ont::TYPE, "CatalogRepository");
        let brand = sym(&mut g, &f, ont::TYPE, "CatalogBrand");
        sym(&mut g, &f, ont::TYPE, "CatalogType");
        g.add_edge(get_brands.clone(), edge::USES_TYPE, repo.clone(), vec![]);
        g.add_edge(get_brands.clone(), edge::USES_TYPE, brand, vec![]);

        // Basket context: one project, two files, internally coupled.
        let f = file(&mut g, "src/Basket.API/BasketService.cs");
        let bsvc = sym(&mut g, &f, ont::TYPE, "BasketService");
        let bitem = sym(&mut g, &f, ont::TYPE, "BasketItem");
        let f = file(&mut g, "src/Basket.API/BasketRepository.cs");
        let brepo = sym(&mut g, &f, ont::TYPE, "BasketRepository");
        sym(&mut g, &f, ont::FUNCTION, "GetBasketAsync");
        g.add_edge(bsvc.clone(), edge::USES_TYPE, brepo, vec![]);
        let f = file(&mut g, "tests/Basket.UnitTests/BasketServiceTests.cs");
        let btest = sym(&mut g, &f, ont::TYPE, "BasketServiceTests");
        sym(&mut g, &f, ont::FUNCTION, "GetBasketReturnsItems");
        sym(&mut g, &f, ont::FUNCTION, "AddItemUpdatesBasket");
        g.add_edge(btest.clone(), edge::USES_TYPE, bsvc.clone(), vec![]);
        g.add_edge(btest, edge::USES_TYPE, bitem.clone(), vec![]);

        // A utility file with no concept tokens, coupled to Ordering.
        let f = file(&mut g, "src/Common/Guard.cs");
        let guard = sym(&mut g, &f, ont::FUNCTION, "AgainstNull");
        g.add_edge(create_order.clone(), edge::CALLS, guard, vec![]);

        // Pure plumbing: no concept tokens, no dependencies at all.
        let f = file(&mut g, "src/Common/Clock.cs");
        sym(&mut g, &f, ont::FUNCTION, "GetValue");

        // Scaffold + root files that must never surface in the view.
        let f = file(&mut g, "build/Publish.cs");
        sym(&mut g, &f, ont::FUNCTION, "PublishOrderPackages");
        let f = file(&mut g, "Setup.cs");
        sym(&mut g, &f, ont::FUNCTION, "SetupOrderTooling");

        // Light cross-context dependencies (never enough to merge contexts).
        g.add_edge(create_order, edge::USES_TYPE, bitem, vec![]);
        g.add_edge(repo, edge::USES_TYPE, order, vec![]);

        g
    }

    fn domain_of_member(derived: &Graph, path: &str) -> String {
        let id = format!("unit::{path}");
        let n = derived
            .nodes()
            .find(|n| n.id == id)
            .unwrap_or_else(|| panic!("missing member node {id}"));
        match n.props.get("domain") {
            Some(Json::Str(s)) => s.clone(),
            other => panic!("member {id} has no domain prop: {other:?}"),
        }
    }

    #[test]
    fn lookup_tables_are_sorted_and_unique() {
        for (name, table) in [
            ("NOISE_TOKENS", NOISE_TOKENS),
            ("SCAFFOLD_SEGMENTS", SCAFFOLD_SEGMENTS),
            ("TRANSPARENT_SEGMENTS", TRANSPARENT_SEGMENTS),
            ("GENERIC_LABEL_SEGMENTS", GENERIC_LABEL_SEGMENTS),
            ("DOC_SEGMENTS", DOC_SEGMENTS),
            ("DOC_EXTENSIONS", DOC_EXTENSIONS),
            ("TEST_SEGMENTS", TEST_SEGMENTS),
        ] {
            for pair in table.windows(2) {
                assert!(
                    pair[0] < pair[1],
                    "{name} must stay sorted+unique: {:?} !< {:?}",
                    pair[0],
                    pair[1]
                );
            }
        }
    }

    #[test]
    fn structural_clustering_recovers_the_three_contexts() {
        let derived = DomainExtractor.extract(&sample_base());
        for (domain, members) in [
            (
                "Ordering",
                vec![
                    "src/Ordering.API/OrdersApi.cs",
                    "src/Ordering.Domain/Order.cs",
                ],
            ),
            (
                "Catalog",
                vec![
                    "src/Catalog.API/CatalogApi.cs",
                    "src/Catalog.Infrastructure/CatalogRepository.cs",
                ],
            ),
            (
                "Basket",
                vec![
                    "src/Basket.API/BasketService.cs",
                    "src/Basket.API/BasketRepository.cs",
                    "tests/Basket.UnitTests/BasketServiceTests.cs",
                ],
            ),
        ] {
            let id = format!("domain::{domain}");
            let n = derived
                .nodes()
                .find(|n| n.id == id)
                .unwrap_or_else(|| panic!("missing domain node {id}"));
            assert_eq!(n.kind, ont::MODULE);
            assert_eq!(n.props.get("view"), Some(&Json::str(VIEW)));
            assert_eq!(n.props.get("domain"), Some(&Json::str(domain)));
            for path in members {
                assert_eq!(domain_of_member(&derived, path), domain, "{path}");
            }
        }
        // Ordering spans two units (API + Domain) plus the coupled Common
        // utility: label from the common name prefix, high confidence not
        // required (no single family dominates).
        let ordering = derived
            .nodes()
            .find(|n| n.id == "domain::Ordering")
            .expect("domain::Ordering");
        assert_eq!(ordering.props.get("file_count"), Some(&Json::U64(3)));
        assert_eq!(ordering.props.get("unit_count"), Some(&Json::U64(3)));
    }

    #[test]
    fn subdomains_are_emitted_under_their_domain() {
        let derived = DomainExtractor.extract(&sample_base());
        let sub = derived
            .nodes()
            .find(|n| n.id == "subdomain::Ordering::Ordering.Domain")
            .expect("subdomain node for Ordering.Domain");
        assert_eq!(sub.kind, ont::MODULE);
        assert_eq!(sub.props.get("view"), Some(&Json::str(VIEW)));
        assert_eq!(sub.props.get("domain"), Some(&Json::str("Ordering")));
        assert_eq!(
            sub.props.get("subdomain"),
            Some(&Json::str("Ordering.Domain"))
        );
        assert_eq!(sub.props.get("file_count"), Some(&Json::U64(1)));
        assert_eq!(sub.props.get("symbol_count"), Some(&Json::U64(3)));
        assert!(derived.edges().any(|e| e.kind == edge::CONTAINS
            && e.from == "domain::Ordering"
            && e.to == "subdomain::Ordering::Ordering.Domain"));
        // Member files carry their unit (subdomain) too.
        let member = derived
            .nodes()
            .find(|n| n.id == "unit::src/Ordering.Domain/Order.cs")
            .expect("member file node");
        assert_eq!(
            member.props.get("unit"),
            Some(&Json::str("Ordering.Domain"))
        );
    }

    #[test]
    fn coupled_utility_joins_its_dependents_domain() {
        let derived = DomainExtractor.extract(&sample_base());
        assert_eq!(
            domain_of_member(&derived, "src/Common/Guard.cs"),
            "Ordering",
            "Guard.cs has no concept but is called by Ordering code"
        );
        assert!(derived.edges().any(|e| e.kind == edge::CONTAINS
            && e.from == "domain::Ordering"
            && e.to == "unit::src/Common/Guard.cs"));
    }

    #[test]
    fn pure_plumbing_lands_in_shared_platform() {
        let derived = DomainExtractor.extract(&sample_base());
        assert_eq!(
            domain_of_member(&derived, "src/Common/Clock.cs"),
            SHARED_DOMAIN,
            "no concept + no coupling = Shared/Platform"
        );
        let shared = derived
            .nodes()
            .find(|n| n.id == format!("domain::{SHARED_DOMAIN}"))
            .expect("Shared/Platform domain node");
        assert_eq!(shared.props.get("confidence"), Some(&Json::str("low")));
        assert_eq!(shared.props.get("label"), Some(&Json::str("platform")));
    }

    #[test]
    fn excluded_files_get_named_infrastructure_groups() {
        // Zero ungrouped: scaffold and root files surface — in first-class
        // named groups with kind/reason, never in a business domain and
        // never domain-less.
        let derived = DomainExtractor.extract(&sample_base());
        assert_eq!(
            domain_of_member(&derived, "build/Publish.cs"),
            GROUP_BUILD_TOOLING
        );
        assert_eq!(domain_of_member(&derived, "Setup.cs"), GROUP_REPO_ROOT);
        for (id, reason) in [
            ("domain::Build & Tooling", "scaffold"),
            ("domain::Repo root", "root"),
        ] {
            let n = derived
                .nodes()
                .find(|n| n.id == id)
                .unwrap_or_else(|| panic!("missing group node {id}"));
            assert_eq!(n.props.get("kind"), Some(&Json::str(KIND_INFRASTRUCTURE)));
            assert_eq!(n.props.get("reason"), Some(&Json::str(reason)));
            assert_eq!(n.props.get("confidence"), Some(&Json::str("high")));
        }
        // Business domains carry kind=business and no reason.
        let ordering = derived
            .nodes()
            .find(|n| n.id == "domain::Ordering")
            .expect("domain::Ordering");
        assert_eq!(ordering.props.get("kind"), Some(&Json::str(KIND_BUSINESS)));
        assert_eq!(ordering.props.get("reason"), None);
        // Scaffold mass never leaks into the clustering: no `build`-flavored
        // *business* domain.
        assert!(derived
            .nodes()
            .filter(|n| n.id.starts_with("domain::")
                && n.props.get("kind") == Some(&Json::str(KIND_BUSINESS)))
            .all(|n| n.name != "build" && n.name != "Build"));
    }

    #[test]
    fn every_file_node_has_a_domain_home() {
        // The zero-ungrouped invariant itself: every File node with a path
        // in the base graph appears in the view with a domain.
        let base = sample_base();
        let derived = DomainExtractor.extract(&base);
        for n in base.nodes().filter(|n| n.kind == ont::FILE) {
            let Some(Json::Str(path)) = n.props.get("path") else {
                continue;
            };
            assert!(
                !domain_of_member(&derived, path).is_empty(),
                "{path} must have a domain home"
            );
        }
    }

    #[test]
    fn infrastructure_group_classification() {
        // Priority: generated > docs > scaffold > root; analyzable code is None.
        assert_eq!(
            infrastructure_group("src/Db/Migrations/20240101_Init.cs"),
            Some((GROUP_GENERATED, "generated"))
        );
        assert_eq!(
            infrastructure_group("docs/adr/0001-record.md"),
            Some((GROUP_DOCUMENTATION, "docs"))
        );
        assert_eq!(
            infrastructure_group("src/Ordering.API/README.md"),
            Some((GROUP_DOCUMENTATION, "docs"))
        );
        assert_eq!(
            infrastructure_group("scripts/deploy.sh"),
            Some((GROUP_BUILD_TOOLING, "scaffold"))
        );
        assert_eq!(
            infrastructure_group("data-plane/dist/server.js"),
            Some((GROUP_BUILD_TOOLING, "scaffold"))
        );
        assert_eq!(
            infrastructure_group("Program.cs"),
            Some((GROUP_REPO_ROOT, "root"))
        );
        assert_eq!(infrastructure_group("src/Ordering.API/OrdersApi.cs"), None);
        assert_eq!(infrastructure_group("tests/Basket.UnitTests/T.cs"), None);
    }

    #[test]
    fn test_files_fold_into_their_subject_domain() {
        // A test tree whose unit would otherwise cohere into its own junk
        // community: dependency edges name the subject, so the tests join
        // the domain they exercise.
        let mut g = sample_base();
        let f = file(&mut g, "tests/integration/OrderFlowTests.cs");
        let t = sym(&mut g, &f, ont::TYPE, "OrderFlowTests");
        sym(&mut g, &f, ont::FUNCTION, "RunOrderFlow");
        let order = "sym::file::src/Ordering.Domain/Order.cs::Order".to_string();
        g.add_edge(t, edge::USES_TYPE, order, vec![]);
        let derived = DomainExtractor.extract(&g);
        let subject = domain_of_member(&derived, "src/Ordering.Domain/Order.cs");
        assert_eq!(
            domain_of_member(&derived, "tests/integration/OrderFlowTests.cs"),
            subject,
            "test with a resolvable subject joins the subject's domain"
        );
        assert_ne!(subject, GROUP_BUILD_TOOLING);
        assert_ne!(subject, SHARED_DOMAIN);
    }

    #[test]
    fn subjectless_pure_test_files_fold_into_build_tooling() {
        // Integration-test scaffolding with no resolvable dependencies and
        // no production code anywhere in its community: not a bounded
        // context — Build & Tooling, never ungrouped.
        let mut g = sample_base();
        for (path, syms) in [
            (
                "tests/integration/validators/schema.mjs",
                vec!["SchemaValidator", "ValidateSchema"],
            ),
            (
                "tests/integration/validators/graph.mjs",
                vec!["GraphValidator", "ValidateGraph"],
            ),
        ] {
            let f = file(&mut g, path);
            for s in syms {
                sym(&mut g, &f, ont::FUNCTION, s);
            }
        }
        let derived = DomainExtractor.extract(&g);
        for p in [
            "tests/integration/validators/schema.mjs",
            "tests/integration/validators/graph.mjs",
        ] {
            assert_eq!(
                domain_of_member(&derived, p),
                GROUP_BUILD_TOOLING,
                "{p} is subjectless pure-test scaffolding"
            );
        }
        // The subject-coupled Basket unit tests still live in Basket.
        assert_eq!(
            domain_of_member(&derived, "tests/Basket.UnitTests/BasketServiceTests.cs"),
            "Basket"
        );
    }

    #[test]
    fn cross_domain_depends_project_to_counted_domain_edges() {
        let derived = DomainExtractor.extract(&sample_base());
        let e = derived
            .edges()
            .find(|e| {
                e.kind == edge::DEPENDS_ON
                    && e.from == "domain::Ordering"
                    && e.to == "domain::Basket"
            })
            .expect("Ordering -> Basket inter-domain edge");
        assert_eq!(e.props.get("count"), Some(&Json::U64(1)));
        assert!(derived.edges().any(|e| e.kind == edge::DEPENDS_ON
            && e.from == "domain::Catalog"
            && e.to == "domain::Ordering"));
        // Intra-domain deps never self-loop.
        assert!(!derived
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.from == e.to));
    }

    #[test]
    fn vocabulary_never_creates_domains() {
        // The v2 failure mode: files sharing vocabulary (`Prefix`, `Setup`,
        // `Arrow`) but no structure must NOT become a domain. Two files in
        // different, dependency-coupled projects share the token `Prefix`:
        // no `Prefix` domain may appear — membership follows structure.
        let mut g = sample_base();
        let f = file(&mut g, "src/Ordering.API/PrefixCodec.cs");
        let a = sym(&mut g, &f, ont::FUNCTION, "EncodePrefix");
        let f = file(&mut g, "src/Catalog.API/PrefixIndex.cs");
        let b = sym(&mut g, &f, ont::TYPE, "PrefixIndex");
        // Each couples to its own project's code, not to each other.
        let order = "sym::file::src/Ordering.Domain/Order.cs::Order".to_string();
        g.add_edge(a, edge::USES_TYPE, order, vec![]);
        let repo = "sym::file::src/Catalog.Infrastructure/CatalogRepository.cs::CatalogRepository"
            .to_string();
        g.add_edge(b, edge::USES_TYPE, repo, vec![]);
        let derived = DomainExtractor.extract(&g);
        assert!(!derived.has_node("domain::Prefix"));
        assert_eq!(
            domain_of_member(&derived, "src/Ordering.API/PrefixCodec.cs"),
            "Ordering"
        );
        assert_eq!(
            domain_of_member(&derived, "src/Catalog.API/PrefixIndex.cs"),
            "Catalog"
        );
    }

    #[test]
    fn uncoupled_path_family_coheres_by_prefix_prior() {
        // A dashboard tree whose imports never resolve (the TSX shape):
        // zero dependency mass, several sibling dirs. Prior (a) must still
        // give ONE dashboard domain, not fragments.
        let mut g = sample_base();
        for (path, syms) in [
            (
                "dashboard/app/page.tsx",
                vec!["DashboardPage", "UsagePanel"],
            ),
            ("dashboard/app/billing.tsx", vec!["BillingPage"]),
            ("dashboard/components/chart.tsx", vec!["UsageChart"]),
            ("dashboard/components/table.tsx", vec!["KeyTable"]),
        ] {
            let f = file(&mut g, path);
            for s in syms {
                sym(&mut g, &f, ont::FUNCTION, s);
            }
        }
        let derived = DomainExtractor.extract(&g);
        let d = domain_of_member(&derived, "dashboard/app/page.tsx");
        assert_eq!(d, "dashboard", "family prior labels the dashboard tree");
        for p in [
            "dashboard/app/billing.tsx",
            "dashboard/components/chart.tsx",
            "dashboard/components/table.tsx",
        ] {
            assert_eq!(domain_of_member(&derived, p), d, "{p} must join {d}");
        }
    }

    #[test]
    fn whole_codebase_duplication_keeps_the_domain_set_stable() {
        // Mirror fold: duplicating the entire codebase under a new path
        // prefix produces byte-identical community shapes, which fold back
        // into their originals — the domain set must not move.
        let base = sample_base();
        let mut doubled = sample_base();
        // Duplicate the *eligible* universe: a repo-root file (`Setup.cs`)
        // is scaffold before cloning but `clone/Setup.cs` would not be —
        // prefixing legitimately changes the eligibility class of root
        // files, so the duplication relation excludes them.
        let files: Vec<(String, String)> = base
            .nodes()
            .filter(|n| n.kind == ont::FILE)
            .filter_map(|n| match n.props.get("path") {
                Some(Json::Str(p)) if !is_scaffold_path(p) => Some((n.id.clone(), p.clone())),
                _ => None,
            })
            .collect();
        for (fid, path) in &files {
            let clone_file = file(&mut doubled, &format!("clone/{path}"));
            for e in base.edges().filter(|e| &e.from == fid) {
                if parent_relation(e.kind) != Some(relation::CONTAINMENT) {
                    continue;
                }
                let s = base.nodes().find(|n| n.id == e.to).unwrap();
                let id = format!("clone::{}", s.id);
                doubled.upsert_node(id.clone(), s.kind, s.name.clone(), vec![]);
                doubled.add_edge(clone_file.clone(), edge::DECLARES, id, vec![]);
            }
        }
        // Mirror every symbol-level dependency edge into the clone.
        for e in base.edges() {
            if parent_relation(e.kind) != Some(relation::DEPENDS) {
                continue;
            }
            doubled.add_edge(
                format!("clone::{}", e.from),
                e.kind,
                format!("clone::{}", e.to),
                vec![],
            );
        }

        let names = |g: &Graph| -> Vec<String> {
            DomainExtractor
                .extract(g)
                .nodes()
                .filter(|n| n.id.starts_with("domain::"))
                .map(|n| n.name.clone())
                .collect()
        };
        assert_eq!(
            names(&base),
            names(&doubled),
            "whole-codebase duplication must keep the domain set identical"
        );
    }

    #[test]
    fn concept_tokenizer_keeps_nouns_and_drops_noise() {
        assert_eq!(concept_tokens("OrderStatus"), vec!["order"]);
        assert_eq!(concept_tokens("IOrderRepository"), vec!["order"]);
        assert_eq!(concept_tokens("basket_item"), vec!["basket", "item"]);
        assert!(concept_tokens("ShouldPrepareConstructor").is_empty());
        assert!(concept_tokens("CreateDeleteUpdate").is_empty());
    }

    #[test]
    fn scaffold_path_filter() {
        assert!(is_scaffold_path("Program.cs")); // repo root
        assert!(is_scaffold_path("build/Publish.cs"));
        assert!(is_scaffold_path("src/tools/Gen.cs"));
        assert!(is_scaffold_path("scripts/deploy.sh"));
        assert!(is_scaffold_path("src/App/obj/Debug/x.cs"));
        assert!(is_scaffold_path("web/node_modules/pkg/index.js"));
        assert!(is_scaffold_path("src/Db/Migrations/20240101_Init.cs")); // generated
        assert!(is_scaffold_path("data-plane/dist/server.js")); // build output
        assert!(is_scaffold_path("tests/unit/fixtures/big.ts")); // test fixtures
        assert!(!is_scaffold_path("src/Ordering.API/OrdersApi.cs"));
        assert!(!is_scaffold_path("packages/core/router/router.ts"));
    }

    #[test]
    fn name_prefix_and_families() {
        assert_eq!(family("control-plane/connectors"), "control-plane");
        assert_eq!(family("Ordering.API"), "Ordering.API");
        assert_eq!(name_family("Ordering.API/Commands"), "Ordering");
        assert_eq!(basename("clone/Basket.API"), "Basket.API");
        let names: BTreeSet<&str> =
            ["Ordering.API", "Ordering.Domain", "Ordering.UnitTests"].into();
        assert_eq!(common_name_prefix(&names), "Ordering");
        let names: BTreeSet<&str> = ["WebApp", "HybridApp"].into();
        assert_eq!(common_name_prefix(&names), "");
    }

    #[test]
    fn family_stem_bridges_suffix_role_variants() {
        assert_eq!(family_stem("Webhooks.API"), "webhook");
        assert_eq!(family_stem("Webhooks.API/IntegrationEvents"), "webhook");
        assert_eq!(family_stem("WebhookClient"), "webhook");
        assert_eq!(family_stem("WebhookClient/Services"), "webhook");
        // A bare role name keeps its last token: never an empty stem.
        assert_eq!(family_stem("Client"), "client");
        // Unrelated families stay apart.
        assert_ne!(family_stem("Ordering.API"), family_stem("OrderProcessor"));
    }

    #[test]
    fn suffix_role_variants_form_one_domain() {
        // `Webhooks.API` + `WebhookClient`: one feature family split across
        // an HTTP boundary — zero resolvable cross-dependencies. The stem
        // prior must still cluster them together (the eShop Webhooks miss).
        let mut g = sample_base();
        for (path, syms) in [
            (
                "src/Webhooks.API/WebhooksApi.cs",
                vec!["RegisterWebhook", "WebhookSubscription"],
            ),
            (
                "src/Webhooks.API/Services/GrantUrlTester.cs",
                vec!["GrantUrlTester", "TestGrantUrl"],
            ),
            (
                "src/WebhookClient/Services/HooksRepository.cs",
                vec!["HooksRepository", "AddWebhookReceived"],
            ),
            (
                "src/WebhookClient/Endpoints/ReceiveHook.cs",
                vec!["ReceiveHook", "WebhookData"],
            ),
        ] {
            let f = file(&mut g, path);
            for s in syms {
                sym(&mut g, &f, ont::FUNCTION, s);
            }
        }
        let derived = DomainExtractor.extract(&g);
        let d = domain_of_member(&derived, "src/Webhooks.API/WebhooksApi.cs");
        for p in [
            "src/Webhooks.API/Services/GrantUrlTester.cs",
            "src/WebhookClient/Services/HooksRepository.cs",
            "src/WebhookClient/Endpoints/ReceiveHook.cs",
        ] {
            assert_eq!(domain_of_member(&derived, p), d, "{p} must join {d}");
        }
        assert_ne!(d, SHARED_DOMAIN);
    }

    #[test]
    fn unit_loyalty_beats_the_crumb_dump() {
        // A conceptless, dependency-less file inside `Ordering.API` is still
        // Ordering code — its unit's path names its domain (the eShop
        // Identity-ViewModel miss). Contrast `pure_plumbing_lands_in_
        // shared_platform`: `Common/Clock.cs` is equally crumb-like but its
        // unit is foreign to Ordering's majority families, so it stays
        // Shared/Platform.
        let mut g = sample_base();
        let f = file(&mut g, "src/Ordering.API/GlobalUsings.cs");
        sym(&mut g, &f, ont::FUNCTION, "Setup");
        let derived = DomainExtractor.extract(&g);
        assert_eq!(
            domain_of_member(&derived, "src/Ordering.API/GlobalUsings.cs"),
            "Ordering",
            "crumb file in a unit whose name family names its domain stays home"
        );
        // The foreign crumb still lands in Shared/Platform (unchanged).
        assert_eq!(
            domain_of_member(&derived, "src/Common/Clock.cs"),
            SHARED_DOMAIN
        );
    }

    #[test]
    fn morphological_fold() {
        let vocab: BTreeSet<String> = [
            "order",
            "orders",
            "ordering",
            "category",
            "categories",
            "stream",
            "streaming",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        let folds = fold_map(&vocab);
        assert_eq!(folds.get("orders").map(String::as_str), Some("order"));
        assert_eq!(folds.get("ordering").map(String::as_str), Some("order"));
        assert_eq!(
            folds.get("categories").map(String::as_str),
            Some("category")
        );
        assert_eq!(folds.get("streaming").map(String::as_str), Some("stream"));
        assert!(!folds.contains_key("order"));
    }

    #[test]
    fn deterministic_across_runs_and_base_untouched() {
        let base = sample_base();
        let before = base.to_jsonl();
        let a = DomainExtractor.extract(&base).to_jsonl();
        let b = DomainExtractor.extract(&base).to_jsonl();
        assert_eq!(a, b, "output must be byte-identical across runs");
        assert!(!a.is_empty());
        assert_eq!(base.to_jsonl(), before, "base graph must not change");
    }
}
