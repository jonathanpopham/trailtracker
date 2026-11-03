//! `trailtracker nav` — the context-efficient codebase navigator (ADR-0004).
//!
//! The #1 problem in AI software engineering: an agent cannot hold a large
//! codebase in context, and lossy RAG retrieves *approximately*. The
//! navigator serves the agent loop — seed → orient → expand → read → verify
//! impact — as **exact, deterministic, budget-shaped** responses over the
//! primitives this crate already computes:
//!
//! - **[`nav_pack`]** — ONE call that turns a task query into the
//!   highest-value exact subgraph that fits a context budget: seeds (hybrid
//!   search hits with why-evidence), compact explain-cards per seed
//!   (domain/layer/archetype, fan-in/out, blast-radius count), a
//!   domain/layer orientation summary, a ranked read-plan of `file:line`
//!   *spans* (never whole files), and the k-hop DEPENDS-family neighborhood
//!   edge list. Schema `trailtracker.nav-pack/v1`.
//! - **[`nav_expand`]** — exact neighborhood growth from any node,
//!   direction-aware (callers | callees | both), depth-bounded,
//!   budget-truncated with honest truncation markers and a continuation
//!   cursor. Schema `trailtracker.nav-expand/v1`.
//!
//! Both commands render in three [`PackFormat`]s: `json` (the exact object;
//! the budget is defined over that serialization), `text` (a human digest of
//! the same JSON selection), and `prose` (V3, epic E-V: the value-ranked
//! selection as deterministic ADR-0008 sentences through the V1 verbalizer —
//! glossary prelude, read-plan spans stated as facts — with the char budget
//! honest over the prose and truncation marked by the standard omission
//! sentence).
//!
//! # Budget contract
//!
//! `budget` is an exact **character count** over the JSON serialization —
//! deterministic and tokenizer-independent. There is no LLM and no tokenizer
//! anywhere in the navigator; budgets are arithmetic, and the field names say
//! so: `budget_chars` (asked for), `used_chars` (what the selection
//! consumed), `estimated_chars` (what the full, untruncated response would
//! have cost). Every response states whether anything was omitted and
//! exactly how much per section. A minimum share of the budget
//! ([`READ_PLAN_MIN_SHARE_PCT`]) is reserved for the read plan before the
//! core is sized — a pack without spans is not actionable. Truncation is
//! never silent, and when even the minimal core overruns that reserve line
//! the response says `exceeded: true` (best-effort content) instead of
//! failing.
//!
//! # Value ranking
//!
//! The pack keeps the highest-value items: `value(node) = relevance ×
//! proximity × centrality ÷ idf_damp`, where relevance is the fused search
//! score of the best seed reaching the node, proximity is `1/(1+cost)` over
//! DEPENDS-family edges (both directions, ≤ [`PACK_DEPTH`] hops) with
//! `cost = Σ (1 + hub_tax(node))` over every node the walk steps into
//! (seed exempt) — stepping into or through a high-degree utility hub
//! attenuates the signal — and centrality is
//! `1 + ⌊log₂(1+degree)⌋` (integer log — no libm, bit-exact on every
//! platform). `idf_damp = 2^min(⌊log₂(seeds_reaching)⌋, hub_excess_bits)`
//! damps nodes that are BOTH reachable from many seeds AND hubs (generic
//! utilities); nodes reached from few seeds through specific paths keep
//! full signal, and seeds themselves are never damped. Ties break by node
//! id ascending. Same graph, same query, same budget → byte-identical
//! output.
//!
//! # Read-plan spans
//!
//! A symbol's span is `[line, next_symbol_line − 1]` within its owning file,
//! derived purely from the graph (`end_line` omitted = "to end of file";
//! File entries span the whole file). The agent reads 30 lines, not 3000.
//!
//! Pure composition: seeds come from [`HybridIndex`], ownership and target
//! resolution from [`crate::explain`], impact from
//! [`crate::query::blast_radius_set`], classification from the same
//! assignment passes behind `domains`/`layers`/`archetypes`. Nothing is
//! re-derived from source.
//!
//! # Scope (honest)
//!
//! The pack is **code-reading-shaped**: it answers "where is X and what
//! touches it" with spans and exact structure. It is NOT an aggregate
//! reporter — its `orientation` section counts only the budget-shaped
//! *selection*, never the whole repo, so questions like "how many files are
//! in domain X" or "which domains depend on Y" belong to the
//! `domains`/`hierarchy`/`stats` commands, and "who are X's top dependents"
//! to `explain`. (V2 eval, 2026-07-11: nav scored 0/16 on domain-aggregate
//! questions by design while winning top-dependent lookups 12/16.)

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use crate::core::json::Json;
use crate::explain::{file_of_map, resolve, ExplainError};
use crate::extract::archetypes::{classify_with, SymbolFacts, RULES};
use crate::extract::domains::assign_domains;
use crate::extract::layers::assign_layers;
use crate::graph::{Graph, GraphNode};
use crate::ir::ontology::{node as ont, parent_relation, relation};
use crate::query::blast_radius_set;
use crate::search::HybridIndex;
use crate::verbalize::facts::SymbolFact;
use crate::verbalize::glossary::Glossary;
use crate::verbalize::render::assemble;
use crate::verbalize::templates as t;

/// Default character budget: a safe slice of any agent context window.
pub const DEFAULT_BUDGET: usize = 20_000;
/// Default expansion depth for `nav expand`.
pub const DEFAULT_DEPTH: u32 = 2;
/// Fixed neighborhood depth for `nav pack` (matches the search proximity
/// tier's [`MAX_HOPS`](crate::search) intuition: 2 hops of exact structure).
const PACK_DEPTH: u32 = 2;
/// How many search hits seed a pack.
const SEED_COUNT: usize = 8;
/// Read-plan entries are capped before budgeting (they are the densest
/// value-per-char section; more than this is a reading list, not a plan).
const READ_PLAN_MAX: usize = 64;
/// Orientation rows kept per grouping (domains / layers).
const ORIENT_MAX: usize = 12;
/// Headroom for the budget block's own digits and the enclosing skeleton,
/// so `estimated_chars` (computed before the block is filled in) stays an
/// honest upper-bound-ish estimate and real output stays under budget.
const RESERVE: usize = 256;
/// Minimum share, in percent, of the fillable budget (chars left after the
/// response skeleton) guaranteed to read-plan entries before the core is
/// allowed to keep seeds/cards/orientation. A pack whose budget is eaten by
/// seeds+cards carries zero spans and is not actionable — the read plan IS
/// the action. 35% buys a dozen ~130-char spans even at a 6k budget while
/// leaving the majority of the space to identity (seeds/cards/orientation).
/// The reserve is capped at what the read plan can actually spend, so
/// generous budgets are unaffected; and it is a floor, not a ceiling — the
/// read plan still fills first in value order, and whatever it leaves
/// unused the edge fill reclaims.
const READ_PLAN_MIN_SHARE_PCT: usize = 35;
/// Degree bits that carry no hub tax: `⌊log₂(1+degree)⌋ ≤ 3` (degree ≤ 14)
/// is ordinary intra-module fan-out and is never treated as a hub. Only the
/// excess bits above this allowance count as hubness, which keeps small
/// graphs byte-identical to the pre-damping ranking.
const HUB_TAX_FREE_BITS: u32 = 3;
/// Classification fallback (same convention as `explain`).
const UNASSIGNED: &str = "unassigned";

// ---------------------------------------------------------------------------
// Direction
// ---------------------------------------------------------------------------

/// Which way `nav expand` walks the DEPENDS-family edges.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Direction {
    /// Incoming edges only: who depends on / calls the target.
    Callers,
    /// Outgoing edges only: what the target depends on / calls.
    Callees,
    /// Both directions (the default).
    Both,
}

impl Direction {
    /// Parse a CLI/MCP direction string.
    pub fn parse(s: &str) -> Option<Direction> {
        match s {
            "callers" => Some(Direction::Callers),
            "callees" => Some(Direction::Callees),
            "both" => Some(Direction::Both),
            _ => None,
        }
    }

    fn as_str(self) -> &'static str {
        match self {
            Direction::Callers => "callers",
            Direction::Callees => "callees",
            Direction::Both => "both",
        }
    }
}

// ---------------------------------------------------------------------------
// Output format
// ---------------------------------------------------------------------------

/// How `nav pack` / `nav expand` render their selection (V3, epic E-V).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum PackFormat {
    /// The exact `trailtracker.nav-pack/v1` / `nav-expand/v1` object. The
    /// char budget is defined over this serialization.
    Json,
    /// Human digest of the same JSON selection (courtesy view; the budget
    /// still governs the underlying JSON selection).
    #[default]
    Text,
    /// The value-ranked selection rendered through the V1 verbalizer:
    /// ADR-0008 sentences with a glossary prelude, read-plan spans stated as
    /// facts. The char budget is honest over the prose itself — truncation
    /// ends the document with the standard omission sentence.
    Prose,
}

impl PackFormat {
    /// Every format name, for CLI/MCP validation and did-you-mean hints.
    pub const NAMES: &'static [&'static str] = &["json", "text", "prose"];

    /// Parse a CLI/MCP format string.
    pub fn parse(s: &str) -> Option<PackFormat> {
        match s {
            "json" => Some(PackFormat::Json),
            "text" => Some(PackFormat::Text),
            "prose" => Some(PackFormat::Prose),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Shared graph scaffolding
// ---------------------------------------------------------------------------

/// DEPENDS-family adjacency, both directions, sorted + deduped: the exact
/// structural fabric every nav walk uses.
struct Fabric<'g> {
    /// from → sorted (kind, to)
    out: BTreeMap<&'g str, Vec<(&'g str, &'g str)>>,
    /// to → sorted (kind, from)
    inc: BTreeMap<&'g str, Vec<(&'g str, &'g str)>>,
    /// node → distinct undirected DEPENDS-neighbors (centrality input).
    degree: BTreeMap<&'g str, usize>,
}

impl<'g> Fabric<'g> {
    fn build(graph: &'g Graph) -> Fabric<'g> {
        let mut out: BTreeMap<&str, Vec<(&str, &str)>> = BTreeMap::new();
        let mut inc: BTreeMap<&str, Vec<(&str, &str)>> = BTreeMap::new();
        let mut und: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
        for e in graph.edges() {
            if parent_relation(e.kind) != Some(relation::DEPENDS) {
                continue;
            }
            out.entry(e.from.as_str())
                .or_default()
                .push((e.kind, e.to.as_str()));
            inc.entry(e.to.as_str())
                .or_default()
                .push((e.kind, e.from.as_str()));
            und.entry(e.from.as_str())
                .or_default()
                .insert(e.to.as_str());
            und.entry(e.to.as_str())
                .or_default()
                .insert(e.from.as_str());
        }
        for v in out.values_mut() {
            v.sort_unstable();
            v.dedup();
        }
        for v in inc.values_mut() {
            v.sort_unstable();
            v.dedup();
        }
        let degree = und.into_iter().map(|(k, v)| (k, v.len())).collect();
        Fabric { out, inc, degree }
    }

    /// Distinct undirected neighbors of `id`, sorted (BFS frontier fodder).
    fn neighbors(&self, id: &str) -> Vec<&'g str> {
        let mut n: Vec<&str> = Vec::new();
        if let Some(v) = self.out.get(id) {
            n.extend(v.iter().map(|(_, to)| *to));
        }
        if let Some(v) = self.inc.get(id) {
            n.extend(v.iter().map(|(_, from)| *from));
        }
        n.sort_unstable();
        n.dedup();
        n
    }

    /// Integer centrality: `1 + ⌊log₂(1 + degree)⌋`. Bit-exact everywhere.
    fn centrality(&self, id: &str) -> f64 {
        let d = self.degree.get(id).copied().unwrap_or(0);
        f64::from(1 + (d as u64 + 1).ilog2())
    }

    /// Hub tax of `id` (see [`hub_tax_bits`]).
    fn hub_tax(&self, id: &str) -> u32 {
        hub_tax_bits(self.degree.get(id).copied().unwrap_or(0))
    }
}

/// Hub tax: the degree bits of a node beyond the tax-free allowance —
/// `max(0, ⌊log₂(1 + degree)⌋ − HUB_TAX_FREE_BITS)`. Zero for ordinary
/// fan-out (degree ≤ 14), growing logarithmically for genuine utility hubs.
/// Integer log — deterministic, bit-exact on every platform.
fn hub_tax_bits(degree: usize) -> u32 {
    (degree as u64 + 1)
        .ilog2()
        .saturating_sub(HUB_TAX_FREE_BITS)
}

/// IDF-style multi-seed damping divisor: `2^min(⌊log₂(seeds_reaching)⌋,
/// hub_tax_bits(degree))`. A node reachable from many seeds through its own
/// high degree is a generic utility (GuidExtensions-shaped) and its signal
/// is discounted; a node reached from few seeds (reach bits 0) or with
/// ordinary fan-out (tax bits 0) keeps full signal — the damping fires only
/// when BOTH conditions hold. Power of two, exactly representable in f64.
fn idf_damp(seeds_reaching: u32, degree: usize) -> u32 {
    let reach_bits = seeds_reaching.max(1).ilog2();
    1 << reach_bits.min(hub_tax_bits(degree))
}

/// node id → (path, line) for every node with a resolvable source location,
/// plus path → sorted symbol start lines (span derivation). File nodes map
/// to (path, 0).
struct Locations<'g> {
    of: BTreeMap<&'g str, (&'g str, u64)>,
    starts: BTreeMap<&'g str, Vec<u64>>,
}

impl<'g> Locations<'g> {
    fn build(graph: &'g Graph, file_of: &BTreeMap<&'g str, &'g str>) -> Locations<'g> {
        let mut path_of_file: BTreeMap<&str, &str> = BTreeMap::new();
        for n in graph.nodes().filter(|n| n.kind == ont::FILE) {
            if let Some(Json::Str(p)) = n.props.get("path") {
                path_of_file.insert(n.id.as_str(), p.as_str());
            }
        }
        let mut of: BTreeMap<&str, (&str, u64)> = BTreeMap::new();
        let mut starts: BTreeMap<&str, Vec<u64>> = BTreeMap::new();
        for n in graph.nodes() {
            let (path, line) = if n.kind == ont::FILE {
                match path_of_file.get(n.id.as_str()) {
                    Some(p) => (*p, 0),
                    None => continue,
                }
            } else {
                let Some(file) = file_of.get(n.id.as_str()) else {
                    continue;
                };
                let Some(p) = path_of_file.get(file) else {
                    continue;
                };
                (*p, prop_u64(n, "line"))
            };
            of.insert(n.id.as_str(), (path, line));
            if n.kind != ont::FILE && line > 0 {
                starts.entry(path).or_default().push(line);
            }
        }
        for v in starts.values_mut() {
            v.sort_unstable();
            v.dedup();
        }
        Locations { of, starts }
    }

    /// The span of a node: `(path, start, end)`; `end == None` = to EOF.
    /// File nodes span the whole file (start 1).
    fn span(&self, node: &GraphNode) -> Option<(&'g str, u64, Option<u64>)> {
        let (path, line) = self.of.get(node.id.as_str()).copied()?;
        if node.kind == ont::FILE {
            return Some((path, 1, None));
        }
        if line == 0 {
            return Some((path, 1, None));
        }
        let end = self
            .starts
            .get(path)
            .and_then(|lines| lines.iter().find(|&&l| l > line))
            .map(|next| next - 1);
        Some((path, line, end))
    }
}

fn prop_u64(node: &GraphNode, key: &str) -> u64 {
    match node.props.get(key) {
        Some(Json::U64(n)) => *n,
        Some(Json::I64(n)) if *n >= 0 => *n as u64,
        _ => 0,
    }
}

/// Serialized char cost of one JSON array item (its line plus a comma).
fn cost(j: &Json) -> usize {
    j.to_line().len() + 1
}

/// The shared budget block. All figures are exact character counts — no
/// tokenizer exists here. `used_chars` is the analytic sum of the skeleton
/// and every kept item (within [`RESERVE`] of the real output);
/// `estimated_chars` is what the full, untruncated response would have cost.
struct BudgetReport {
    budget: usize,
    used: usize,
    full_estimate: usize,
    truncated: bool,
    exceeded: bool,
    omitted: Vec<(&'static str, usize)>,
}

impl BudgetReport {
    fn json(&self) -> Json {
        Json::obj([
            ("budget_chars", self.budget.into()),
            ("used_chars", self.used.into()),
            ("estimated_chars", self.full_estimate.into()),
            ("truncated", self.truncated.into()),
            ("exceeded", self.exceeded.into()),
            (
                "omitted",
                Json::Object(
                    self.omitted
                        .iter()
                        .map(|(k, v)| ((*k).to_string(), Json::U64(*v as u64)))
                        .collect(),
                ),
            ),
        ])
    }
}

// ---------------------------------------------------------------------------
// nav pack
// ---------------------------------------------------------------------------

/// One selected node with its ranking evidence.
struct Ranked<'g> {
    node: &'g GraphNode,
    /// Best `seed_score / (1 + cost)` over all seeds, where `cost` sums
    /// `1 + hub_tax(node)` over every node the walk steps into (seed
    /// exempt).
    relevance: f64,
    /// Minimum hops from any seed (0 = is a seed).
    hops: u32,
    /// Name of the seed the minimum-hop path comes from.
    via: &'g str,
    /// 1-based rank of the seed itself (0 = not a seed).
    seed_rank: usize,
    /// relevance × centrality ÷ idf_damp (proximity is inside relevance).
    value: f64,
}

impl Ranked<'_> {
    fn why(&self) -> String {
        if self.seed_rank > 0 {
            format!("seed #{}", self.seed_rank)
        } else {
            let unit = if self.hops == 1 { "hop" } else { "hops" };
            format!("{} {unit} from {}", self.hops, self.via)
        }
    }
}

/// Build the one-call context pack for `query` against `graph` (analyzed
/// from `dir`), sized to `budget` chars of JSON. Returns the rendered pack —
/// human text, or one `trailtracker.nav-pack/v1` object when `json` is set.
/// Deterministic; an unmatched query yields an honest empty pack.
pub fn nav_pack(
    graph: &Graph,
    query: &str,
    dir: &str,
    budget: usize,
    format: PackFormat,
) -> String {
    let seeds = HybridIndex::build(graph).search(query, SEED_COUNT);
    let by_id: BTreeMap<&str, &GraphNode> = graph.nodes().map(|n| (n.id.as_str(), n)).collect();
    let fabric = Fabric::build(graph);
    let file_of = file_of_map(graph);
    let locations = Locations::build(graph, &file_of);
    let domains = assign_domains(graph);
    let layers = assign_layers(graph);

    // --- select: seeds + their ≤PACK_DEPTH-hop neighborhood, ranked --------
    let mut selected: BTreeMap<&str, Ranked> = BTreeMap::new();
    for (i, s) in seeds.iter().enumerate() {
        let Some(node) = by_id.get(s.id.as_str()) else {
            continue;
        };
        selected.insert(
            s.id.as_str(),
            Ranked {
                node,
                relevance: s.score,
                hops: 0,
                via: node.name.as_str(),
                seed_rank: i + 1,
                value: 0.0,
            },
        );
    }
    // Per-seed bounded BFS (seed order = rank order, so equal-hop/equal-score
    // updates deterministically keep the earlier seed). Each walk carries an
    // accumulated path cost: every node the walk steps INTO costs
    // `1 + hub_tax(node)` — waypoints and destination alike — so a neighbor
    // reached through (or sitting at) a high-degree utility hub carries less
    // signal than one reached through a specific path, and a monster hub's
    // centrality reward is cancelled by its own arrival tax instead of
    // dominating the ranking. The seed itself is exempt: its hubness is
    // search evidence, not propagation noise. Within one wave every
    // candidate takes the minimum cost over its frontier parents
    // (deterministic: the arrival tax is per-candidate and `min` over
    // parents is order-independent); nodes keep the cost of the wave that
    // first reached them, and under the fixed depth bound deeper waves can
    // only add cost, so this layered walk is the exact minimum over all
    // hop-minimal paths.
    let mut seed_reach: BTreeMap<&str, u32> = BTreeMap::new();
    for s in &seeds {
        let Some(seed_node) = by_id.get(s.id.as_str()) else {
            continue;
        };
        let mut cost_of: BTreeMap<&str, u32> = BTreeMap::new();
        cost_of.insert(s.id.as_str(), 0);
        let mut frontier: Vec<&str> = vec![s.id.as_str()];
        for hops in 1..=PACK_DEPTH {
            let mut wave: BTreeMap<&str, u32> = BTreeMap::new();
            for &u in &frontier {
                let base = cost_of[u];
                for v in fabric.neighbors(u) {
                    if cost_of.contains_key(v) {
                        continue;
                    }
                    let step = base + 1 + fabric.hub_tax(v);
                    wave.entry(v)
                        .and_modify(|c| *c = (*c).min(step))
                        .or_insert(step);
                }
            }
            let mut next: Vec<&str> = Vec::new();
            for (v, c) in wave {
                cost_of.insert(v, c);
                next.push(v);
                *seed_reach.entry(v).or_default() += 1;
                let Some(node) = by_id.get(v) else { continue };
                let contribution = s.score / f64::from(1 + c);
                match selected.get_mut(v) {
                    Some(r) => {
                        if contribution > r.relevance {
                            r.relevance = contribution;
                        }
                        if hops < r.hops {
                            r.hops = hops;
                            r.via = seed_node.name.as_str();
                        }
                    }
                    None => {
                        selected.insert(
                            v,
                            Ranked {
                                node,
                                relevance: contribution,
                                hops,
                                via: seed_node.name.as_str(),
                                seed_rank: 0,
                                value: 0.0,
                            },
                        );
                    }
                }
            }
            frontier = next;
        }
    }
    for (id, r) in selected.iter_mut() {
        // Seeds are never damped: their presence is direct search evidence;
        // the IDF damping corrects *propagated* graph signal only.
        let damp = if r.seed_rank > 0 {
            1
        } else {
            idf_damp(
                seed_reach.get(id).copied().unwrap_or(1),
                fabric.degree.get(id).copied().unwrap_or(0),
            )
        };
        r.value = r.relevance * fabric.centrality(id) / f64::from(damp);
    }
    // Value order: descending, id ascending — the one ranking every
    // budget-truncated section consumes.
    let mut order: Vec<&str> = selected.keys().copied().collect();
    order.sort_by(|a, b| {
        selected[b]
            .value
            .total_cmp(&selected[a].value)
            .then_with(|| a.cmp(b))
    });

    // --- seeds section ------------------------------------------------------
    let seed_items: Vec<Json> = seeds
        .iter()
        .enumerate()
        .map(|(i, s)| {
            Json::obj([
                ("rank", (i + 1).into()),
                ("id", Json::str(s.id.as_str())),
                ("name", Json::str(s.name.as_str())),
                ("kind", Json::str(s.kind)),
                ("path", Json::str(s.path.as_str())),
                ("score", Json::F64(s.score)),
                (
                    "why",
                    Json::Array(s.why.iter().map(|w| Json::str(w.as_str())).collect()),
                ),
            ])
        })
        .collect();

    // --- compact cards (one per seed) ----------------------------------------
    let classify_node = |node: &GraphNode| -> (String, String, &'static str) {
        let file_id: Option<&str> = if node.kind == ont::FILE {
            Some(node.id.as_str())
        } else {
            file_of.get(node.id.as_str()).copied()
        };
        let domain = file_id
            .and_then(|f| domains.file_domain.get(f))
            .cloned()
            .unwrap_or_else(|| UNASSIGNED.to_string());
        let layer = file_id
            .and_then(|f| layers.file_unit.get(f))
            .and_then(|u| layers.unit_layer.get(u))
            .cloned()
            .unwrap_or_else(|| UNASSIGNED.to_string());
        let path = locations
            .of
            .get(node.id.as_str())
            .map(|(p, _)| *p)
            .unwrap_or("");
        let declared = if path.is_empty() { None } else { Some(path) };
        let archetype = classify_with(RULES, &SymbolFacts::of(node, declared));
        (domain, layer, archetype)
    };
    let cards_data: Vec<CardData> = seeds
        .iter()
        .filter_map(|s| by_id.get(s.id.as_str()).copied())
        .map(|node| {
            let (domain, layer, archetype) = classify_node(node);
            let (path, line) = locations
                .of
                .get(node.id.as_str())
                .copied()
                .unwrap_or(("", 0));
            let fan_in = fabric.inc.get(node.id.as_str()).map_or(0, Vec::len);
            let fan_out = fabric.out.get(node.id.as_str()).map_or(0, Vec::len);
            let blast = blast_radius_set(graph, std::slice::from_ref(&node.id)).len();
            CardData {
                id: node.id.as_str(),
                name: node.name.as_str(),
                kind: node.kind,
                path,
                line,
                domain,
                layer,
                archetype,
                fan_in,
                fan_out,
                blast,
            }
        })
        .collect();
    let card_items: Vec<Json> = cards_data
        .iter()
        .map(|c| {
            Json::obj([
                ("id", Json::str(c.id)),
                ("name", Json::str(c.name)),
                ("kind", Json::str(c.kind)),
                ("path", Json::str(c.path)),
                ("line", Json::U64(c.line)),
                ("domain", Json::str(c.domain.as_str())),
                ("layer", Json::str(c.layer.as_str())),
                ("archetype", Json::str(c.archetype)),
                ("fan_in", c.fan_in.into()),
                ("fan_out", c.fan_out.into()),
                ("blast_count", c.blast.into()),
            ])
        })
        .collect();

    // --- orientation ----------------------------------------------------------
    let mut domain_counts: BTreeMap<String, usize> = BTreeMap::new();
    let mut layer_counts: BTreeMap<String, usize> = BTreeMap::new();
    for r in selected.values() {
        let (domain, layer, _) = classify_node(r.node);
        *domain_counts.entry(domain).or_default() += 1;
        *layer_counts.entry(layer).or_default() += 1;
    }
    let top = |counts: &BTreeMap<String, usize>| -> Vec<(String, usize)> {
        let mut v: Vec<(String, usize)> = counts.iter().map(|(k, n)| (k.clone(), *n)).collect();
        v.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
        v.truncate(ORIENT_MAX);
        v
    };
    let domain_rows: Vec<(String, String, usize)> = top(&domain_counts)
        .into_iter()
        .map(|(d, n)| {
            let label = domains
                .domains
                .get(&d)
                .map(|i| i.label.clone())
                .unwrap_or_else(|| d.clone());
            (d, label, n)
        })
        .collect();
    let layer_rows: Vec<(String, usize)> = top(&layer_counts);
    let orientation = Json::obj([
        (
            "domains",
            Json::Array(
                domain_rows
                    .iter()
                    .map(|(d, label, n)| {
                        Json::obj([
                            ("domain", Json::str(d.as_str())),
                            ("label", Json::str(label.as_str())),
                            ("nodes", (*n).into()),
                        ])
                    })
                    .collect(),
            ),
        ),
        (
            "layers",
            Json::Array(
                layer_rows
                    .iter()
                    .map(|(l, n)| {
                        Json::obj([("layer", Json::str(l.as_str())), ("nodes", (*n).into())])
                    })
                    .collect(),
            ),
        ),
    ]);

    // --- read plan (value order, deduped spans, capped) ------------------------
    let mut read_entries: Vec<ReadEntry> = Vec::new();
    let mut seen_span: BTreeSet<(&str, u64)> = BTreeSet::new();
    for id in &order {
        if read_entries.len() >= READ_PLAN_MAX {
            break;
        }
        let r = &selected[id];
        let Some((path, start, end)) = locations.span(r.node) else {
            continue;
        };
        if !seen_span.insert((path, start)) {
            continue;
        }
        read_entries.push(ReadEntry {
            path,
            start,
            end,
            id: r.node.id.as_str(),
            name: r.node.name.as_str(),
            kind: r.node.kind,
            why: r.why(),
        });
    }
    let read_items: Vec<Json> = read_entries
        .iter()
        .map(|r| {
            let mut fields = vec![
                ("path", Json::str(r.path)),
                ("start_line", Json::U64(r.start)),
            ];
            if let Some(e) = r.end {
                fields.push(("end_line", Json::U64(e)));
            }
            fields.push(("id", Json::str(r.id)));
            fields.push(("name", Json::str(r.name)));
            fields.push(("kind", Json::str(r.kind)));
            fields.push(("why", Json::str(r.why.as_str())));
            Json::obj(fields)
        })
        .collect();

    // --- neighborhood edges (both endpoints selected; value order) -------------
    let in_selected = |id: &str| selected.contains_key(id);
    let mut edge_entries: Vec<(f64, Json, &str, &str, &str)> = Vec::new();
    for e in graph.edges() {
        if parent_relation(e.kind) != Some(relation::DEPENDS) {
            continue;
        }
        if !in_selected(e.from.as_str()) || !in_selected(e.to.as_str()) {
            continue;
        }
        let v = selected[e.from.as_str()]
            .value
            .max(selected[e.to.as_str()].value);
        let j = Json::obj([
            ("from", Json::str(e.from.as_str())),
            ("kind", Json::str(e.kind)),
            ("to", Json::str(e.to.as_str())),
        ]);
        edge_entries.push((v, j, e.from.as_str(), e.kind, e.to.as_str()));
    }
    edge_entries.sort_by(|a, b| {
        b.0.total_cmp(&a.0)
            .then_with(|| (a.2, a.3, a.4).cmp(&(b.2, b.3, b.4)))
    });
    edge_entries.dedup_by(|a, b| (a.2, a.3, a.4) == (b.2, b.3, b.4));
    let edge_total = edge_entries.len();

    // --- prose format: the same selection, rendered through the V1
    // verbalizer. The budget is honest over the prose itself (assemble's
    // omission sentence), not over the JSON this format never emits.
    if format == PackFormat::Prose {
        let edge_pairs: Vec<(&str, &str)> = edge_entries.iter().map(|e| (e.2, e.4)).collect();
        return pack_prose(
            graph,
            &cards_data,
            &domain_rows,
            &layer_rows,
            selected.len(),
            &read_entries,
            &edge_pairs,
            &by_id,
            &locations,
            budget,
        );
    }
    let edge_items: Vec<Json> = edge_entries.into_iter().map(|(_, j, _, _, _)| j).collect();

    // --- budget fill -------------------------------------------------------------
    // Skeleton: the pack with every section empty (budget digits covered by
    // RESERVE). The core (seeds, cards, orientation) may keep itself only
    // outside the read-plan reserve — a guaranteed minimum share of the
    // fillable space (READ_PLAN_MIN_SHARE_PCT) so every viable pack carries
    // actionable spans; read-plan then edges fill the remainder in value
    // order, edges reclaiming whatever the read plan leaves unused.
    let skeleton = pack_json(
        dir,
        query,
        &BudgetReport {
            budget,
            used: 0,
            full_estimate: 0,
            truncated: false,
            exceeded: false,
            omitted: vec![("seeds", 0), ("cards", 0), ("read_plan", 0), ("edges", 0)],
        },
        &[],
        &[],
        &orientation,
        &[],
        &[],
        selected.len(),
        edge_total,
    )
    .to_line()
    .len();
    let limit = budget.saturating_sub(RESERVE);
    let orientation_cost = orientation.to_line().len();

    // The read-plan reserve: a floor carved out of the fillable space before
    // the core is sized — never less than the top span (so granularity cannot
    // starve the plan), never more than what the plan can actually spend
    // (generous budgets are unaffected). If even the minimal core overruns
    // the reserved line, the pack is honestly `exceeded`: the budget cannot
    // hold a well-formed (actionable) pack, and what fits is best-effort.
    let fillable = limit.saturating_sub(skeleton);
    let read_plan_full_cost: usize = read_items.iter().map(cost).sum();
    let first_span_cost = read_items.first().map(cost).unwrap_or(0);
    let read_reserve = (fillable * READ_PLAN_MIN_SHARE_PCT / 100)
        .max(first_span_cost)
        .min(read_plan_full_cost);
    let core_limit = limit.saturating_sub(read_reserve);

    let mut n_seeds = seed_items.len();
    let mut n_cards = card_items.len();
    let mut keep_orientation = true;
    let core = |ns: usize, nc: usize, orient: bool| -> usize {
        skeleton
            + seed_items[..ns].iter().map(cost).sum::<usize>()
            + card_items[..nc].iter().map(cost).sum::<usize>()
            + if orient { orientation_cost } else { 0 }
    };
    while core(n_seeds, n_cards, keep_orientation) > core_limit {
        if n_cards > 0 {
            n_cards -= 1;
        } else if n_seeds > 1 {
            n_seeds -= 1;
        } else if keep_orientation {
            keep_orientation = false;
        } else {
            break; // exceeded: even the minimal core overruns the reserve line.
        }
    }
    let mut total = core(n_seeds, n_cards, keep_orientation);
    let exceeded = total > core_limit;

    let mut n_read = 0usize;
    for item in &read_items {
        let c = cost(item);
        if total + c > limit {
            break;
        }
        total += c;
        n_read += 1;
    }
    let mut n_edges = 0usize;
    for item in &edge_items {
        let c = cost(item);
        if total + c > limit {
            break;
        }
        total += c;
        n_edges += 1;
    }

    let omitted = vec![
        ("seeds", seed_items.len() - n_seeds),
        ("cards", card_items.len() - n_cards),
        ("read_plan", read_items.len() - n_read),
        ("edges", edge_total - n_edges),
    ];
    let truncated = omitted.iter().any(|(_, n)| *n > 0) || !keep_orientation;
    let full_estimate = skeleton
        + seed_items.iter().map(cost).sum::<usize>()
        + card_items.iter().map(cost).sum::<usize>()
        + orientation_cost
        + read_items.iter().map(cost).sum::<usize>()
        + edge_items.iter().map(cost).sum::<usize>();
    let report = BudgetReport {
        budget,
        used: total,
        full_estimate,
        truncated,
        exceeded,
        omitted,
    };

    let empty_orientation = Json::obj([
        ("domains", Json::Array(Vec::new())),
        ("layers", Json::Array(Vec::new())),
    ]);
    let pack = pack_json(
        dir,
        query,
        &report,
        &seed_items[..n_seeds],
        &card_items[..n_cards],
        if keep_orientation {
            &orientation
        } else {
            &empty_orientation
        },
        &read_items[..n_read],
        &edge_items[..n_edges],
        selected.len(),
        edge_total,
    );
    match format {
        PackFormat::Json => pack.to_line(),
        // Prose returned above, right after the selection was finalized.
        PackFormat::Text | PackFormat::Prose => {
            pack_text(query, dir, &report, &seeds, n_seeds, &pack)
        }
    }
}

/// Assemble the `trailtracker.nav-pack/v1` object.
#[allow(clippy::too_many_arguments)] // one private assembly point, mirrors the schema
fn pack_json(
    dir: &str,
    query: &str,
    report: &BudgetReport,
    seeds: &[Json],
    cards: &[Json],
    orientation: &Json,
    read_plan: &[Json],
    edges: &[Json],
    node_count: usize,
    edge_count_total: usize,
) -> Json {
    Json::obj([
        ("schema", Json::str("trailtracker.nav-pack/v1")),
        ("command", Json::str("nav pack")),
        ("dir", Json::str(dir)),
        ("query", Json::str(query)),
        ("budget", report.json()),
        ("seeds", Json::Array(seeds.to_vec())),
        ("cards", Json::Array(cards.to_vec())),
        ("orientation", orientation.clone()),
        ("read_plan", Json::Array(read_plan.to_vec())),
        (
            "neighborhood",
            Json::obj([
                ("depth", Json::U64(u64::from(PACK_DEPTH))),
                ("node_count", node_count.into()),
                ("edge_count_total", edge_count_total.into()),
                ("edges", Json::Array(edges.to_vec())),
            ]),
        ),
    ])
}

/// Human rendering of a pack: a section-by-section digest of the same JSON
/// selection (the budget is defined over the JSON serialization; the text
/// view is a courtesy).
fn pack_text(
    query: &str,
    dir: &str,
    report: &BudgetReport,
    seeds: &[crate::search::SearchResult],
    n_seeds: usize,
    pack: &Json,
) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "nav pack: \"{query}\" in {dir}");
    let _ = writeln!(
        out,
        "  budget {} chars — used {}, full pack would be {}, truncated {}{}",
        report.budget,
        report.used,
        report.full_estimate,
        if report.truncated { "yes" } else { "no" },
        if report.exceeded {
            " (EXCEEDED: even the minimal core is over budget)"
        } else {
            ""
        }
    );
    let _ = writeln!(out, "  seeds ({n_seeds})");
    for (i, s) in seeds.iter().take(n_seeds).enumerate() {
        let _ = write!(
            out,
            "    {:>2}. {:.3}  {} ({})",
            i + 1,
            s.score,
            s.name,
            s.kind
        );
        if !s.path.is_empty() {
            let _ = write!(out, "  {}", s.path);
        }
        let _ = writeln!(out);
        if !s.why.is_empty() {
            let _ = writeln!(out, "         {}", s.why.join(" · "));
        }
    }
    // The remaining sections render straight from the assembled JSON so text
    // and JSON can never disagree about what was selected.
    let section = |out: &mut String, label: &str, key: &str| {
        if let Some(Json::Array(items)) = pack_get(pack, key) {
            let _ = writeln!(out, "  {label} ({})", items.len());
            for item in items {
                let _ = writeln!(out, "    {}", item.to_line());
            }
        }
    };
    section(&mut out, "cards", "cards");
    if let Some(orientation) = pack_get(pack, "orientation") {
        let _ = writeln!(out, "  orientation {}", orientation.to_line());
    }
    section(&mut out, "read plan", "read_plan");
    if let Some(Json::Object(n)) = pack_get(pack, "neighborhood") {
        let count = |k: &str| match n.get(k) {
            Some(Json::U64(v)) => *v,
            _ => 0,
        };
        let shown = match n.get("edges") {
            Some(Json::Array(e)) => e.len(),
            _ => 0,
        };
        let _ = writeln!(
            out,
            "  neighborhood: depth {}, {} nodes, {} edges shown of {}",
            count("depth"),
            count("node_count"),
            shown,
            count("edge_count_total"),
        );
        if let Some(Json::Array(edges)) = n.get("edges") {
            for e in edges {
                let _ = writeln!(out, "    {}", e.to_line());
            }
        }
    }
    out
}

/// Field access on an assembled `Json::obj` (writer-only JSON module — this
/// is the one read helper nav needs for the text renderer).
fn pack_get<'j>(pack: &'j Json, key: &str) -> Option<&'j Json> {
    match pack {
        Json::Object(map) => map.get(key),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Prose rendering (V3): the selection as ADR-0008 sentences
// ---------------------------------------------------------------------------

/// Per-seed card facts. The JSON `cards` section and the prose sentences
/// render from this one struct, so the two formats can never disagree about
/// what a seed is.
struct CardData<'g> {
    id: &'g str,
    name: &'g str,
    kind: &'static str,
    path: &'g str,
    line: u64,
    domain: String,
    layer: String,
    archetype: &'static str,
    fan_in: usize,
    fan_out: usize,
    blast: usize,
}

/// One read-plan entry. The JSON `read_plan` section and the prose span
/// sentences render from this one struct.
struct ReadEntry<'g> {
    path: &'g str,
    start: u64,
    end: Option<u64>,
    id: &'g str,
    name: &'g str,
    kind: &'static str,
    why: String,
}

/// Render the pack selection as one verbalized document: glossary prelude
/// (`F1..Fn` over the seeds, seed rank = value rank), then the read-plan
/// spans, the seed cards, the orientation rows, and the neighborhood edges —
/// value-first, because [`assemble`]'s budget cut keeps a prefix and the
/// read plan IS the action. Deterministic; honest truncation via the
/// standard omission sentence.
#[allow(clippy::too_many_arguments)] // one private assembly point
fn pack_prose(
    graph: &Graph,
    cards: &[CardData],
    domain_rows: &[(String, String, usize)],
    layer_rows: &[(String, usize)],
    selection_size: usize,
    read_entries: &[ReadEntry],
    edges: &[(&str, &str)],
    by_id: &BTreeMap<&str, &GraphNode>,
    locations: &Locations,
    budget: usize,
) -> String {
    let total_nodes = graph.node_count() as u64;
    let symbol_facts: Vec<SymbolFact> = cards
        .iter()
        .map(|c| SymbolFact {
            id: c.id.to_string(),
            name: c.name.to_string(),
            kind: c.kind,
            path: c.path.to_string(),
            line: c.line,
            domain: c.domain.clone(),
            layer: c.layer.clone(),
            archetype: c.archetype,
            fan_in: c.fan_in as u64,
            fan_out: c.fan_out as u64,
            blast: c.blast as u64,
            dependents: Vec::new(),
        })
        .collect();
    let glossary = Glossary::over(&[], &symbol_facts);

    // R5 (deterministic ordering): only the card block leads sentences with
    // handles, and it walks F1..Fn in glossary order. Read-plan and edge
    // sentences use the identity form as subject (handles appear only
    // mid-sentence), so the value ordering of those sections cannot violate
    // the non-decreasing-subject rule.
    let mut body: Vec<String> = Vec::new();
    for r in read_entries {
        body.push(t::read_span(&t::ReadSpan {
            subject: None,
            kind: r.kind,
            name: r.name,
            path: r.path,
            start: r.start,
            end: r.end,
        }));
    }
    for c in cards {
        let Some(subject) = glossary.symbol(c.id) else {
            continue;
        };
        body.push(t::node_identity(&t::NodeIdentity {
            subject,
            kind: c.kind,
            name: c.name,
            domain: &c.domain,
            layer: &c.layer,
            archetype: c.archetype,
        }));
        body.push(t::hotspot_fan_in(&t::Hotspot {
            subject,
            degree: c.fan_in as u64,
            total_nodes,
        }));
        body.push(t::hotspot_fan_out(&t::Hotspot {
            subject,
            degree: c.fan_out as u64,
            total_nodes,
        }));
        body.push(t::blast_radius(&t::BlastRadius {
            subject,
            affected: c.blast as u64,
            total_nodes,
        }));
    }
    for (_, label, n) in domain_rows {
        body.push(t::domain_nodes(&t::DomainNodes {
            name: label,
            nodes: *n as u64,
            total_nodes: selection_size as u64,
        }));
    }
    for (layer, n) in layer_rows {
        body.push(t::layer_nodes(&t::LayerNodes {
            layer,
            nodes: *n as u64,
            total_nodes: selection_size as u64,
        }));
    }
    for (from, to) in edges {
        body.push(prose_edge(&glossary, by_id, locations, from, to, false));
    }
    assemble(glossary, body, Some(budget)).to_text()
}

/// One DEPENDS-family edge as a sentence. The `to` endpoint uses the
/// glossary handle where one was minted; the `from` endpoint does so only
/// when `handle_from` is set — a handle-led sentence is subject to R5's
/// non-decreasing-subject order, which value-ordered edge lists cannot
/// promise (pack passes `false`; expand's single-handle document passes
/// `true`).
fn prose_edge<'g>(
    glossary: &Glossary,
    by_id: &BTreeMap<&'g str, &'g GraphNode>,
    locations: &Locations<'g>,
    from: &'g str,
    to: &'g str,
    handle_from: bool,
) -> String {
    fn endpoint<'a, 'g>(
        glossary: &'a Glossary,
        by_id: &BTreeMap<&'g str, &'g GraphNode>,
        locations: &Locations<'g>,
        id: &'g str,
    ) -> (Option<&'a str>, &'static str, &'g str, &'g str) {
        let (name, kind) = by_id
            .get(id)
            .map(|n| (n.name.as_str(), n.kind))
            .unwrap_or((id, "?"));
        let path = locations.of.get(id).map(|(p, _)| *p).unwrap_or("");
        (glossary.symbol(id), kind, name, path)
    }
    let (f_subj, f_kind, f_name, f_path) = endpoint(glossary, by_id, locations, from);
    let (t_subj, t_kind, t_name, t_path) = endpoint(glossary, by_id, locations, to);
    t::depends_edge(
        &t::EdgeEndpoint {
            subject: if handle_from { f_subj } else { None },
            kind: f_kind,
            name: f_name,
            path: f_path,
        },
        &t::EdgeEndpoint {
            subject: t_subj,
            kind: t_kind,
            name: t_name,
            path: t_path,
        },
    )
}

// ---------------------------------------------------------------------------
// nav expand
// ---------------------------------------------------------------------------

/// Grow the exact DEPENDS-family neighborhood around `target` (resolved with
/// the `explain` contract): direction-aware, depth-bounded, budget-truncated
/// with a continuation cursor. Returns the rendered result in the requested
/// [`PackFormat`]: human text, one `trailtracker.nav-expand/v1` object, or
/// the ADR-0008 prose page.
#[allow(clippy::too_many_arguments)] // the CLI surface, one flag per knob
pub fn nav_expand(
    graph: &Graph,
    target: &str,
    dir: &str,
    depth: u32,
    direction: Direction,
    budget: usize,
    cursor: usize,
    format: PackFormat,
) -> Result<String, ExplainError> {
    let node = resolve(graph, target)?;
    let fabric = Fabric::build(graph);
    let file_of = file_of_map(graph);
    let locations = Locations::build(graph, &file_of);
    let by_id: BTreeMap<&str, &GraphNode> = graph.nodes().map(|n| (n.id.as_str(), n)).collect();

    // Node levels: BFS from the target following the direction constraint.
    let step = |id: &str| -> Vec<&str> {
        match direction {
            Direction::Callers => fabric
                .inc
                .get(id)
                .map(|v| v.iter().map(|(_, from)| *from).collect())
                .unwrap_or_default(),
            Direction::Callees => fabric
                .out
                .get(id)
                .map(|v| v.iter().map(|(_, to)| *to).collect())
                .unwrap_or_default(),
            Direction::Both => fabric.neighbors(id),
        }
    };
    let mut level: BTreeMap<&str, u32> = BTreeMap::new();
    level.insert(node.id.as_str(), 0);
    let mut frontier: Vec<&str> = vec![node.id.as_str()];
    for hops in 1..=depth {
        let mut next: Vec<&str> = Vec::new();
        for &u in &frontier {
            for v in step(u) {
                if level.contains_key(v) {
                    continue;
                }
                level.insert(v, hops);
                next.push(v);
            }
        }
        frontier = next;
    }

    // Edge set: every direction-eligible DEPENDS-family edge whose traversal
    // endpoint sits strictly inside the depth bound. hops = that endpoint's
    // level + 1 (the wave on which the walk crosses the edge).
    let mut edges: Vec<(u32, &str, &str, &str)> = Vec::new();
    for e in graph.edges() {
        if parent_relation(e.kind) != Some(relation::DEPENDS) {
            continue;
        }
        let (from, to) = (e.from.as_str(), e.to.as_str());
        let anchor = match direction {
            // callers: we walk incoming edges outward from `to`.
            Direction::Callers => level.get(to).copied(),
            // callees: we walk outgoing edges from `from`.
            Direction::Callees => level.get(from).copied(),
            Direction::Both => match (level.get(from), level.get(to)) {
                (Some(a), Some(b)) => Some(*a.min(b)),
                (Some(a), None) => Some(*a),
                (None, Some(b)) => Some(*b),
                (None, None) => None,
            },
        };
        let Some(h) = anchor else { continue };
        if h >= depth {
            continue;
        }
        // Both endpoints must be inside the neighborhood.
        if !level.contains_key(from) || !level.contains_key(to) {
            continue;
        }
        edges.push((h + 1, from, e.kind, to));
    }
    edges.sort_unstable();
    edges.dedup();
    let total_edges = edges.len();

    // --- prose format: identity + fan facts + the edge page from `cursor`,
    // rendered through the V1 verbalizer; the budget is honest over the
    // prose (assemble's omission sentence covers any cut tail).
    if format == PackFormat::Prose {
        return Ok(expand_prose(
            graph, node, &fabric, &locations, &by_id, &edges, cursor, budget,
        ));
    }

    // Page from the cursor under the budget: per-edge cost plus the cost of
    // any endpoint node entry the page newly introduces.
    let edge_json = |(hops, from, kind, to): &(u32, &str, &str, &str)| {
        Json::obj([
            ("from", Json::str(*from)),
            ("kind", Json::str(*kind)),
            ("to", Json::str(*to)),
            ("hops", Json::U64(u64::from(*hops))),
        ])
    };
    let node_json = |id: &str| -> Json {
        let (path, line) = locations.of.get(id).copied().unwrap_or(("", 0));
        let (name, kind) = by_id
            .get(id)
            .map(|n| (n.name.as_str(), n.kind))
            .unwrap_or((id, "?"));
        Json::obj([
            ("id", Json::str(id)),
            ("name", Json::str(name)),
            ("kind", Json::str(kind)),
            ("path", Json::str(path)),
            ("line", Json::U64(line)),
            (
                "hops",
                Json::U64(u64::from(level.get(id).copied().unwrap_or(0))),
            ),
        ])
    };

    let identity = Json::obj([
        ("id", Json::str(node.id.as_str())),
        ("name", Json::str(node.name.as_str())),
        ("kind", Json::str(node.kind)),
        (
            "path",
            Json::str(
                locations
                    .of
                    .get(node.id.as_str())
                    .map(|(p, _)| *p)
                    .unwrap_or(""),
            ),
        ),
        ("line", Json::U64(prop_u64(node, "line"))),
    ]);

    // Skeleton cost: the response with no edges/nodes.
    let skeleton = expand_json(
        dir,
        target,
        &identity,
        direction,
        depth,
        &BudgetReport {
            budget,
            used: 0,
            full_estimate: 0,
            truncated: false,
            exceeded: false,
            omitted: vec![("edges", 0)],
        },
        total_edges,
        cursor,
        None,
        &[],
        &[],
    )
    .to_line()
    .len();
    let limit = budget.saturating_sub(RESERVE);

    let cursor = cursor.min(total_edges);
    let mut total = skeleton;
    let mut page: Vec<Json> = Vec::new();
    let mut page_nodes: BTreeMap<&str, Json> = BTreeMap::new();
    let mut exceeded = false;
    for entry in edges.iter().skip(cursor) {
        let ej = edge_json(entry);
        let mut c = cost(&ej);
        let mut new_nodes: Vec<(&str, Json)> = Vec::new();
        for id in [entry.1, entry.3] {
            if !page_nodes.contains_key(id) && new_nodes.iter().all(|(n, _)| *n != id) {
                let nj = node_json(id);
                c += cost(&nj);
                new_nodes.push((id, nj));
            }
        }
        if total + c > limit {
            if page.is_empty() && cursor < total_edges {
                // Honest floor: always make progress — one edge per call even
                // when the budget cannot hold it.
                exceeded = true;
            } else {
                break;
            }
        }
        total += c;
        page.push(ej);
        for (id, nj) in new_nodes {
            page_nodes.insert(id, nj);
        }
        if exceeded {
            break;
        }
    }
    let returned = page.len();
    let truncated = cursor + returned < total_edges;
    let next_cursor = truncated.then_some(cursor + returned);
    // What the whole neighborhood (cursor 0, nothing omitted) would cost.
    let full_estimate = {
        let mut sum = skeleton;
        let mut seen: BTreeSet<&str> = BTreeSet::new();
        for entry in &edges {
            sum += cost(&edge_json(entry));
            for id in [entry.1, entry.3] {
                if seen.insert(id) {
                    sum += cost(&node_json(id));
                }
            }
        }
        sum
    };
    let report = BudgetReport {
        budget,
        used: total,
        full_estimate,
        truncated,
        exceeded,
        omitted: vec![("edges", total_edges - cursor - returned)],
    };
    let nodes: Vec<Json> = page_nodes.into_values().collect();

    let doc = expand_json(
        dir,
        target,
        &identity,
        direction,
        depth,
        &report,
        total_edges,
        cursor,
        next_cursor,
        &nodes,
        &page,
    );
    match format {
        PackFormat::Json => Ok(doc.to_line()),
        // Prose returned above, right after the edge set was finalized.
        PackFormat::Text | PackFormat::Prose => Ok(expand_text(
            node,
            dir,
            direction,
            depth,
            &report,
            total_edges,
            cursor,
            &doc,
        )),
    }
}

/// Render one expansion page as a verbalized document: the target's
/// glossary line and fan facts, then one sentence per edge from `cursor` in
/// the deterministic edge order. The char budget applies to the prose; a cut
/// tail ends with the standard omission sentence.
#[allow(clippy::too_many_arguments)] // one private assembly point
fn expand_prose(
    graph: &Graph,
    node: &GraphNode,
    fabric: &Fabric,
    locations: &Locations,
    by_id: &BTreeMap<&str, &GraphNode>,
    edges: &[(u32, &str, &str, &str)],
    cursor: usize,
    budget: usize,
) -> String {
    let (path, line) = locations
        .of
        .get(node.id.as_str())
        .copied()
        .unwrap_or(("", 0));
    let fan_in = fabric.inc.get(node.id.as_str()).map_or(0, Vec::len);
    let fan_out = fabric.out.get(node.id.as_str()).map_or(0, Vec::len);
    // Only identity and fan fields feed the glossary + fan sentences;
    // classification is not computed on the expand path.
    let fact = SymbolFact {
        id: node.id.clone(),
        name: node.name.clone(),
        kind: node.kind,
        path: path.to_string(),
        line,
        domain: String::new(),
        layer: String::new(),
        archetype: "",
        fan_in: fan_in as u64,
        fan_out: fan_out as u64,
        blast: 0,
        dependents: Vec::new(),
    };
    let glossary = Glossary::for_target(&fact);
    let total_nodes = graph.node_count() as u64;

    let mut body: Vec<String> = Vec::new();
    if let Some(subject) = glossary.symbol(node.id.as_str()) {
        body.push(t::hotspot_fan_in(&t::Hotspot {
            subject,
            degree: fan_in as u64,
            total_nodes,
        }));
        body.push(t::hotspot_fan_out(&t::Hotspot {
            subject,
            degree: fan_out as u64,
            total_nodes,
        }));
    }
    for (_, from, _, to) in edges.iter().skip(cursor.min(edges.len())) {
        body.push(prose_edge(&glossary, by_id, locations, from, to, true));
    }
    assemble(glossary, body, Some(budget)).to_text()
}

/// Assemble the `trailtracker.nav-expand/v1` object.
#[allow(clippy::too_many_arguments)] // one private assembly point, mirrors the schema
fn expand_json(
    dir: &str,
    target: &str,
    identity: &Json,
    direction: Direction,
    depth: u32,
    report: &BudgetReport,
    total_edges: usize,
    cursor: usize,
    next_cursor: Option<usize>,
    nodes: &[Json],
    edges: &[Json],
) -> Json {
    Json::obj([
        ("schema", Json::str("trailtracker.nav-expand/v1")),
        ("command", Json::str("nav expand")),
        ("dir", Json::str(dir)),
        ("target", Json::str(target)),
        ("identity", identity.clone()),
        ("direction", Json::str(direction.as_str())),
        ("depth", Json::U64(u64::from(depth))),
        ("budget", report.json()),
        ("total_edges", total_edges.into()),
        ("cursor", cursor.into()),
        ("returned", edges.len().into()),
        ("truncated", report.truncated.into()),
        (
            "next_cursor",
            match next_cursor {
                Some(c) => c.into(),
                None => Json::Null,
            },
        ),
        ("nodes", Json::Array(nodes.to_vec())),
        ("edges", Json::Array(edges.to_vec())),
    ])
}

/// Human rendering of an expansion page.
#[allow(clippy::too_many_arguments)] // private renderer, mirrors the schema
fn expand_text(
    node: &GraphNode,
    dir: &str,
    direction: Direction,
    depth: u32,
    report: &BudgetReport,
    total_edges: usize,
    cursor: usize,
    doc: &Json,
) -> String {
    let mut out = String::new();
    let _ = writeln!(
        out,
        "nav expand: {} ({}) — {} in {dir}",
        node.name, node.kind, node.id
    );
    let _ = writeln!(
        out,
        "  direction {} · depth {depth} · {total_edges} edge(s) total",
        direction.as_str()
    );
    let shown = match pack_get(doc, "edges") {
        Some(Json::Array(e)) => e.len(),
        _ => 0,
    };
    let _ = writeln!(
        out,
        "  page: cursor {cursor}, {shown} edge(s), truncated {}{}",
        if report.truncated { "yes" } else { "no" },
        match pack_get(doc, "next_cursor") {
            Some(Json::U64(c)) => format!(" (continue with --cursor {c})"),
            _ => String::new(),
        }
    );
    if let Some(Json::Array(edges)) = pack_get(doc, "edges") {
        for e in edges {
            let _ = writeln!(out, "    {}", e.to_line());
        }
    }
    if let Some(Json::Array(nodes)) = pack_get(doc, "nodes") {
        let _ = writeln!(out, "  nodes ({})", nodes.len());
        for n in nodes {
            let _ = writeln!(out, "    {}", n.to_line());
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    fn calc() -> Graph {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("eval/corpus/calc");
        crate::pipeline::analyze_dir(&root)
            .expect("calc corpus analyzes")
            .graph
    }

    // -- nav pack -----------------------------------------------------------

    #[test]
    fn pack_is_deterministic_and_carries_every_section() {
        let g = calc();
        let a = nav_pack(
            &g,
            "parse expression",
            "d",
            DEFAULT_BUDGET,
            PackFormat::Json,
        );
        let b = nav_pack(
            &g,
            "parse expression",
            "d",
            DEFAULT_BUDGET,
            PackFormat::Json,
        );
        assert_eq!(a, b, "pack must be byte-identical across runs");
        for key in [
            "\"schema\":\"trailtracker.nav-pack/v1\"",
            "\"budget\":",
            "\"seeds\":",
            "\"cards\":",
            "\"orientation\":",
            "\"read_plan\":",
            "\"neighborhood\":",
            "\"budget_chars\":",
            "\"used_chars\":",
            "\"estimated_chars\":",
        ] {
            assert!(a.contains(key), "missing {key} in:\n{a}");
        }
    }

    #[test]
    fn pack_seeds_lead_with_the_best_hit_and_cards_match_seeds() {
        let g = calc();
        let out = nav_pack(&g, "parse", "d", DEFAULT_BUDGET, PackFormat::Json);
        // The seed list mirrors hybrid search: parse is the top hit (object
        // keys serialize sorted, so `id` leads each seed entry).
        assert!(
            out.contains("\"seeds\":[{\"id\":\"fn::crate::parser::parse#7\""),
            "top seed wrong:\n{out}"
        );
        // Its compact card is present with classification + impact.
        assert!(out.contains("\"blast_count\":"), "{out}");
        assert!(
            out.contains("\"domain\":\"op\"") || out.contains("\"domain\":"),
            "{out}"
        );
        assert!(out.contains("\"archetype\":"), "{out}");
    }

    #[test]
    fn pack_read_plan_spans_are_ranges_not_files() {
        let g = calc();
        let out = nav_pack(&g, "parse", "d", DEFAULT_BUDGET, PackFormat::Json);
        // parse starts at src/parser.rs:7; its span must start there and the
        // plan must carry an explicit start_line.
        assert!(
            out.contains("\"path\":\"src/parser.rs\",\"start_line\":7"),
            "parse span missing:\n{out}"
        );
        // At least one span is bounded (an end_line exists somewhere).
        assert!(out.contains("\"end_line\":"), "no bounded span:\n{out}");
    }

    #[test]
    fn pack_honors_the_budget_and_marks_truncation_honestly() {
        let g = calc();
        let full = nav_pack(&g, "parse expression", "d", 200_000, PackFormat::Json);
        assert!(
            full.contains("\"truncated\":false"),
            "huge budget must not truncate:\n{full}"
        );
        let tight = nav_pack(&g, "parse expression", "d", 2_000, PackFormat::Json);
        assert!(
            tight.len() <= 2_000,
            "output ({} chars) must fit the 2000-char budget",
            tight.len()
        );
        assert!(
            tight.contains("\"truncated\":true"),
            "tight budget must mark truncation:\n{tight}"
        );
        assert!(full.len() > tight.len());
        // Determinism under truncation too.
        assert_eq!(
            tight,
            nav_pack(&g, "parse expression", "d", 2_000, PackFormat::Json)
        );
    }

    // -- FIX 1: read-plan reserve --------------------------------------------

    #[test]
    fn pack_reserves_a_read_plan_share_at_every_viable_budget() {
        let g = calc();
        // Sweep tight budgets: whenever the core fits (`exceeded: false`),
        // the pack must carry at least one actionable span. Before the
        // READ_PLAN_MIN_SHARE_PCT reserve, seeds+cards could eat the whole
        // budget and return a pack with zero read-plan entries.
        for budget in (900..4000).step_by(50) {
            let out = nav_pack(&g, "parse expression", "d", budget, PackFormat::Json);
            assert!(
                out.len() <= budget,
                "budget {budget}: output {} chars overruns",
                out.len()
            );
            if out.contains("\"exceeded\":true") {
                continue;
            }
            assert!(
                out.contains("\"read_plan\":[{"),
                "budget {budget}: viable pack with zero read-plan spans:\n{out}"
            );
        }
    }

    // -- FIX 2: hub damping ---------------------------------------------------

    #[test]
    fn hub_tax_is_zero_for_ordinary_fanout_and_grows_logarithmically() {
        assert_eq!(hub_tax_bits(0), 0);
        assert_eq!(hub_tax_bits(14), 0, "degree 14 is tax-free fan-out");
        assert_eq!(hub_tax_bits(15), 1, "degree 15 is the first taxed hub");
        assert_eq!(hub_tax_bits(63), 3, "⌊log₂ 64⌋ − 3");
        assert_eq!(hub_tax_bits(500), 5);
    }

    #[test]
    fn idf_damp_fires_only_when_multi_seed_and_hub_coincide() {
        // Few seeds through a specific path: full signal even for a hub.
        assert_eq!(idf_damp(1, 1000), 1);
        // Many seeds reaching a small node: shared specific logic, keep it.
        assert_eq!(idf_damp(8, 6), 1);
        // Many seeds AND a hub: the GuidExtensions shape — damped.
        assert_eq!(idf_damp(8, 1000), 8, "2^min(log2 8 = 3, tax 6) = 8");
        // The damping is capped by whichever evidence is weaker.
        assert_eq!(idf_damp(2, 1000), 2, "2 seeds only cap the damp at 2");
        assert_eq!(idf_damp(8, 20), 2, "degree 20 has 1 excess bit");
    }

    /// A synthetic hub graph: 8 query-matching seed functions all calling
    /// one 200-caller utility hub, one specific helper called by a single
    /// seed, and one node two specific hops out. The damping must sink the
    /// hub and its riders below the specific path.
    fn hub_graph() -> Graph {
        use crate::ir::ontology::edge;
        let mut g = Graph::new();
        let fun = |g: &mut Graph, path: &str, name: &str, line: u64| -> String {
            let file_id = format!("file::{path}");
            g.upsert_node(
                file_id.clone(),
                ont::FILE,
                path.rsplit('/').next().unwrap().to_string(),
                vec![("path", Json::str(path))],
            );
            let id = format!("fn::{name}");
            g.upsert_node(
                id.clone(),
                ont::FUNCTION,
                name.to_string(),
                vec![("line", Json::U64(line))],
            );
            g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
            id
        };
        let hub = fun(&mut g, "src/u/util.rs", "shared_util", 5);
        let detail = fun(&mut g, "src/a/detail.rs", "session_detail", 5);
        let deep = fun(&mut g, "src/a/deep.rs", "deep_step", 5);
        for c in ["a", "b", "c", "d", "e", "f", "g", "h"] {
            let seed = fun(
                &mut g,
                &format!("src/a/{c}.rs"),
                &format!("alpha_play_{c}"),
                5,
            );
            g.add_edge(seed.clone(), edge::CALLS, hub.clone(), vec![]);
            if c == "a" {
                g.add_edge(seed, edge::CALLS, detail.clone(), vec![]);
            }
        }
        g.add_edge(detail, edge::CALLS, deep, vec![]);
        for i in 0..200 {
            let caller = fun(
                &mut g,
                &format!("src/c/ctrl_{i:03}.rs"),
                &format!("ctrl_{i:03}"),
                5,
            );
            g.add_edge(caller, edge::CALLS, hub.clone(), vec![]);
        }
        g
    }

    #[test]
    fn pack_damps_utility_hubs_and_their_riders_below_specific_paths() {
        let g = hub_graph();
        let out = nav_pack(&g, "alpha play", "d", 200_000, PackFormat::Json);
        // All eight alpha functions are the seeds (nothing else matches).
        assert!(
            out.match_indices("\"name\":\"alpha_play_").count() >= 8,
            "alpha functions must seed the pack:\n{out}"
        );
        // Rank positions inside the read_plan section (top-level keys
        // serialize sorted: read_plan sits between "query" and "schema").
        let at = out.find("\"read_plan\":[").expect("read_plan present");
        let end = out[at..].find(",\"schema\"").expect("schema follows") + at;
        let plan = &out[at..end];
        let pos = |needle: &str| plan.find(needle);
        // Absence from the plan is maximal sinking (the hub may fall out of
        // the READ_PLAN_MAX top slots entirely).
        let hub = pos("\"name\":\"shared_util\"").unwrap_or(usize::MAX);
        let detail = pos("\"name\":\"session_detail\"").expect("detail in plan");
        let deep = pos("\"name\":\"deep_step\"").expect("deep in plan");
        let first_ctrl = pos("\"name\":\"ctrl_").unwrap_or(usize::MAX);
        // The specific 1-hop helper and even the specific 2-hop node beat
        // the 208-degree hub reached from all eight seeds (arrival tax +
        // 8-seed IDF damping) and beat every unrelated rider pulled in
        // through the hub (the walk pays the hub's tax on the way through).
        assert!(
            detail < hub,
            "specific helper must outrank the hub:\n{plan}"
        );
        assert!(
            deep < hub,
            "specific 2-hop path must outrank the hub:\n{plan}"
        );
        assert!(
            detail < first_ctrl,
            "helper must outrank the riders:\n{plan}"
        );
        assert!(
            deep < first_ctrl,
            "specific 2-hop path must outrank the riders:\n{plan}"
        );
        // And the specific nodes sit in the top ranks: only the 8 seeds may
        // precede them (rank = count of entries before the match).
        let rank = |at: usize| plan[..at].matches("\"why\":").count();
        assert!(rank(detail) <= 8, "helper out of top ranks:\n{plan}");
        assert!(rank(deep) <= 9, "deep step out of top ranks:\n{plan}");
        // The riders' evidence says how they got in.
        assert!(
            out.contains("2 hops from alpha_play_"),
            "rider why-evidence missing:\n{out}"
        );
    }

    #[test]
    fn pack_with_impossible_budget_still_answers_and_says_exceeded() {
        let g = calc();
        let out = nav_pack(&g, "parse", "d", 300, PackFormat::Json);
        assert!(out.contains("\"exceeded\":true"), "{out}");
        // Still carries the single most relevant seed.
        assert!(out.contains("fn::crate::parser::parse#7"), "{out}");
    }

    #[test]
    fn pack_unmatched_query_yields_an_honest_empty_pack() {
        let g = calc();
        // A featureless query: no BM25 terms, no embeddable n-grams.
        let out = nav_pack(&g, "---///---", "d", DEFAULT_BUDGET, PackFormat::Json);
        assert!(out.contains("\"seeds\":[]"), "{out}");
        assert!(out.contains("\"node_count\":0"), "{out}");
        assert!(out.contains("\"truncated\":false"), "{out}");
    }

    #[test]
    fn pack_text_view_renders_sections() {
        let g = calc();
        let out = nav_pack(&g, "parse", "d", DEFAULT_BUDGET, PackFormat::Text);
        for needle in [
            "nav pack: \"parse\"",
            "seeds (",
            "read plan (",
            "neighborhood:",
        ] {
            assert!(out.contains(needle), "missing `{needle}`:\n{out}");
        }
    }

    // -- nav expand ---------------------------------------------------------

    #[test]
    fn expand_directions_partition_the_neighborhood() {
        let g = calc();
        let run = |direction| {
            nav_expand(
                &g,
                "fn::crate::parser::parse#7",
                "d",
                1,
                direction,
                DEFAULT_BUDGET,
                0,
                PackFormat::Json,
            )
            .expect("parse resolves")
        };
        let callers = run(Direction::Callers);
        let callees = run(Direction::Callees);
        let both = run(Direction::Both);
        let count = |s: &str| -> usize {
            let key = "\"total_edges\":";
            let at = s.find(key).unwrap() + key.len();
            s[at..]
                .chars()
                .take_while(char::is_ascii_digit)
                .collect::<String>()
                .parse()
                .unwrap()
        };
        assert!(count(&both) >= count(&callers).max(count(&callees)));
        assert!(count(&both) <= count(&callers) + count(&callees));
        // Depth-1 caller edges all terminate at the target.
        assert!(
            callers.contains("\"to\":\"fn::crate::parser::parse#7\""),
            "{callers}"
        );
        assert!(
            !callers.contains("\"hops\":2"),
            "depth 1 must not reach hop 2"
        );
    }

    #[test]
    fn expand_cursor_pages_cover_everything_exactly_once() {
        let g = calc();
        // A budget that forces several pages.
        let mut cursor = 0usize;
        let mut collected: Vec<String> = Vec::new();
        for _ in 0..100 {
            let out = nav_expand(
                &g,
                "fn::crate::parser::parse#7",
                "d",
                2,
                Direction::Both,
                1_500,
                cursor,
                PackFormat::Json,
            )
            .unwrap();
            assert!(out.len() <= 1_500 || out.contains("\"exceeded\":true"));
            for part in out.split("{\"from\":").skip(1) {
                let edge: String = part.chars().take_while(|c| *c != '}').collect();
                collected.push(edge);
            }
            if let Some(at) = out.find("\"next_cursor\":") {
                let rest = &out[at + "\"next_cursor\":".len()..];
                if rest.starts_with("null") {
                    break;
                }
                cursor = rest
                    .chars()
                    .take_while(char::is_ascii_digit)
                    .collect::<String>()
                    .parse()
                    .unwrap();
            } else {
                break;
            }
        }
        let full = nav_expand(
            &g,
            "fn::crate::parser::parse#7",
            "d",
            2,
            Direction::Both,
            10_000_000,
            0,
            PackFormat::Json,
        )
        .unwrap();
        let full_edges: Vec<String> = full
            .split("{\"from\":")
            .skip(1)
            .map(|p| p.chars().take_while(|c| *c != '}').collect())
            .collect();
        assert_eq!(
            collected, full_edges,
            "paged union must equal the unpaged edge list, in order"
        );
        let mut dedup = collected.clone();
        dedup.dedup();
        assert_eq!(dedup, collected, "no page overlap");
    }

    #[test]
    fn expand_resolution_reuses_the_explain_contract() {
        let g = calc();
        // Ambiguous name.
        match nav_expand(
            &g,
            "reset",
            "d",
            2,
            Direction::Both,
            DEFAULT_BUDGET,
            0,
            PackFormat::Json,
        ) {
            Err(ExplainError::Ambiguous { target, candidates }) => {
                assert_eq!(target, "reset");
                assert!(candidates.len() >= 2);
            }
            other => panic!("expected Ambiguous, got {other:?}"),
        }
        // Unknown target.
        match nav_expand(
            &g,
            "NoSuchThing",
            "d",
            2,
            Direction::Both,
            DEFAULT_BUDGET,
            0,
            PackFormat::Json,
        ) {
            Err(ExplainError::NotFound { .. }) => {}
            other => panic!("expected NotFound, got {other:?}"),
        }
        // File path resolves.
        let out = nav_expand(
            &g,
            "src/parser.rs",
            "d",
            1,
            Direction::Both,
            DEFAULT_BUDGET,
            0,
            PackFormat::Json,
        )
        .unwrap();
        assert!(out.contains("\"id\":\"file::src/parser.rs\""), "{out}");
    }

    #[test]
    fn expand_is_deterministic() {
        let g = calc();
        let a = nav_expand(
            &g,
            "parse",
            "d",
            2,
            Direction::Both,
            DEFAULT_BUDGET,
            0,
            PackFormat::Json,
        )
        .unwrap();
        let b = nav_expand(
            &g,
            "parse",
            "d",
            2,
            Direction::Both,
            DEFAULT_BUDGET,
            0,
            PackFormat::Json,
        )
        .unwrap();
        assert_eq!(a, b);
        assert!(a.contains("\"schema\":\"trailtracker.nav-expand/v1\""));
    }

    // -- prose format (V3) ----------------------------------------------------

    /// Rebuild the declared glossary from a prose document's prelude lines
    /// (`F1 = ...`), then check the whole document against ADR-0008.
    fn assert_prose_conforms(doc: &str) {
        use crate::verbalize::grammar::{self, Handle};
        let lines: Vec<&str> = doc.lines().collect();
        let handles: Vec<Handle> = lines
            .iter()
            .filter_map(|l| {
                let (h, exp) = l.split_once(" = ")?;
                (h.starts_with('F') && h[1..].chars().all(|c| c.is_ascii_digit()))
                    .then(|| Handle::new(h, exp))
            })
            .collect();
        let vs = grammar::check(&lines, &handles);
        assert!(vs.is_empty(), "prose violates ADR-0008: {vs:#?}\n{doc}");
    }

    #[test]
    fn pack_prose_is_grammar_clean_deterministic_and_budgeted() {
        let g = calc();
        let a = nav_pack(&g, "parse expression", "d", 30_000, PackFormat::Prose);
        let b = nav_pack(&g, "parse expression", "d", 30_000, PackFormat::Prose);
        assert_eq!(a, b, "prose must be deterministic");
        assert!(a.chars().count() <= 30_000, "{} chars", a.chars().count());
        // Glossary prelude first, read-plan spans as facts.
        assert!(a.starts_with("F1 = "), "{a}");
        assert!(a.contains(" spans "), "{a}");
        assert_prose_conforms(&a);
    }

    #[test]
    fn pack_prose_truncation_is_honest() {
        let g = calc();
        let full = nav_pack(&g, "parse expression", "d", 200_000, PackFormat::Prose);
        let tight = nav_pack(&g, "parse expression", "d", 600, PackFormat::Prose);
        assert!(full.len() > tight.len());
        assert!(
            tight.chars().count() <= 600,
            "{} chars",
            tight.chars().count()
        );
        assert!(tight.contains("The budget omits"), "{tight}");
        assert_eq!(
            tight,
            nav_pack(&g, "parse expression", "d", 600, PackFormat::Prose),
            "truncated prose must be deterministic"
        );
        assert_prose_conforms(&tight);
    }

    #[test]
    fn pack_prose_unmatched_query_is_honestly_empty() {
        let g = calc();
        let out = nav_pack(&g, "---///---", "d", DEFAULT_BUDGET, PackFormat::Prose);
        assert!(!out.contains(" = "), "no handles without seeds: {out}");
        assert_prose_conforms(&out);
    }

    #[test]
    fn expand_prose_is_grammar_clean_and_pages_from_cursor() {
        let g = calc();
        let run = |cursor: usize| {
            nav_expand(
                &g,
                "fn::crate::parser::parse#7",
                "d",
                2,
                Direction::Both,
                DEFAULT_BUDGET,
                cursor,
                PackFormat::Prose,
            )
            .expect("parse resolves")
        };
        let a = run(0);
        assert_eq!(a, run(0), "prose must be deterministic");
        assert!(a.starts_with("F1 = "), "{a}");
        assert!(a.contains("F1 has fan-in "), "{a}");
        assert!(a.chars().count() <= DEFAULT_BUDGET);
        assert_prose_conforms(&a);
        // A later cursor drops edge sentences but keeps the prelude.
        let later = run(10_000);
        assert!(later.starts_with("F1 = "), "{later}");
        assert!(later.len() < a.len(), "{later}");
        assert_prose_conforms(&later);
    }
}
