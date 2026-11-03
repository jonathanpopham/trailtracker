# ADR-0004: The context-efficient codebase navigator (`nav`)

Status: accepted (amended 2026-07-07: read-plan reserve + hub damping,
bead trailtracker-nav-dogfood-fixes-7nd — see "Dogfood amendments" below)
Date: 2026-07-07
Bead: trailtracker-frontier-context-nav-akv (K1)

## Context

The #1 operational problem in AI software engineering is that agents cannot
hold a large codebase in context. The dominant workaround — RAG over embedded
chunks — retrieves *approximately*: it returns text that looks like the
query, with no guarantee the retrieved set is closed under the dependencies
that actually matter, and no way to say what was left out. An agent editing a
million-line codebase on approximate context makes confidently wrong edits.

TrailTracker already computes the exact substrate the agent needs, all
deterministic and local: hybrid search with why-evidence (`search`), the
one-card understanding primitive (`explain`), reverse-reachability impact
(`query blast-radius`), the Domain→Unit→File→Symbol spine (`hierarchy`), and
the raw code graph. What is missing is the *workflow surface*: one call that
turns a task description into the smallest exact subgraph an agent should
load, sized to a context budget.

## Decision

The navigator is a **workflow over existing exact primitives** — it derives
nothing new from source. It is packaged as:

1. a CLI command family, `trailtracker nav <subcommand>`:
   - `nav pack "<task query>" [DIR] [--budget N] [--json]`
   - `nav expand <target> [DIR] [--depth K] [--direction callers|callees|both]
     [--budget N] [--cursor N] [--json]`
2. two MCP tools, `nav_pack` and `nav_expand`, on the existing stdio server
   (tool count 12 → 14), envelope-consistent with the rest of the surface.

### The agent loop it serves

```
task description
  → seed      nav pack: hybrid search hits, each with why-evidence
  → orient    nav pack: domain/layer aggregation of the selected subgraph
  → expand    nav pack neighborhood (k=2) / nav expand from any node:
              exact callers/callees/deps, direction-aware, depth-bounded
  → read      nav pack read-plan: ranked file:line SPANS, not whole files
  → verify    per-seed blast-radius counts (same machinery as
              `query blast-radius`), then `explain`/`query` for depth
```

One `nav pack` call answers seed+orient+expand+read+verify-impact at once;
`nav expand` is the continuation primitive when the agent needs more of the
graph around one node.

### Budgeting (the core contract)

The navigator contains no LLM and no tokenizer; budgets are exact character
counts; all ranking is the deterministic search/graph stack. The consumer is
an LLM; the producer is arithmetic.

- Every response carries a `budget` block named in chars so the no-tokenizer
  nature is unmistakable in the surface itself: `budget_chars` (asked for),
  `used_chars` (what the selection consumed), `estimated_chars` (what the
  full, untruncated response would have cost), whether truncation happened,
  and exactly what was omitted (counts per section).
- `--budget <chars>` is the character budget — a proxy for the consuming
  agent's context window. Deterministic and tokenizer-independent; tokens
  vary by model, chars do not. Default 20000.
- The pack returns the **highest-value exact subgraph that fits**. Value of a
  node is `relevance × proximity × centrality ÷ idf_damp`:
  - relevance: the fused search score of the seed it is reached from
    (seeds carry their own score),
  - proximity: `1/(1+cost)` from the best seed, where the walk (over
    DEPENDS-family edges, both directions, bounded at 2 for the pack) pays
    `1 + hub_tax(node)` for every node it steps into — waypoints and
    destination alike, seed exempt. `hub_tax = max(0, ⌊log₂(1+degree)⌋ − 3)`
    (see "Dogfood amendments"); on a hub-free path `cost = hops` exactly,
  - centrality: `1 + ⌊log₂(1 + degree)⌋` over the same DEPENDS-family
    adjacency — a *moderate* hub two hops out beats a leaf one hop out only
    when the search signal is close, which is the intended behavior; a
    monster hub's reward is cancelled by its own arrival tax,
  - idf_damp: `2^min(⌊log₂(seeds_reaching)⌋, hub_tax_bits)` — nodes that are
    BOTH reachable from many seeds AND hubs are generic utilities and are
    damped; seeds themselves are never damped (their presence is direct
    search evidence, damping corrects propagated signal only).
- Fill order is fixed: core (meta, seeds, per-seed compact cards,
  orientation) first — but the core may only keep itself outside the
  **read-plan reserve**: `max(35% of the fillable space, the top span's
  cost)`, capped at what the read plan can actually spend. A pack without
  spans is not actionable, so the reserve is a floor the core cannot eat;
  read-plan entries then fill first in value order (they may exceed the
  reserve), and neighborhood edges fill and reclaim whatever the read plan
  left unused. When even the minimal core (one seed, no cards, no
  orientation) overruns the reserve line, seeds/cards have already shrunk
  as far as they can and the response says so honestly
  (`budget.exceeded: true`, best-effort content) rather than failing.
- Truncation is never silent: omitted counts are exact, and `nav expand`
  carries a continuation `cursor` (an offset into the deterministically
  sorted edge list) so a follow-up call resumes exactly where the page ended.

### Determinism

Everything is a pure function of (graph, arguments). Seeds come from the
already-deterministic `HybridIndex`; BFS walks sorted adjacency; all ranking
sorts use `total_cmp` descending with node-id ascending tie-breaks; greedy
budget fill consumes items in that fixed order. Same repo, same query, same
budget → byte-identical output. This is the moat versus lossy RAG: the pack
is *reproducible evidence*, not a sample.

### Read-plan spans

The graph knows every symbol's `path` and starting `line`. A symbol's span is
`[line, next_symbol_line - 1]` within its file (open-ended for the last
symbol — `end_line` omitted means "to end of file"). This is derived purely
from the graph, exact for well-formed files, and lets the agent read 30
lines instead of a 3000-line file. File-node entries span the whole file.

### Schemas

- `trailtracker.nav-pack/v1`: `{schema, command, dir, query, budget{...},
  seeds[], cards[], orientation{domains[], layers[]}, read_plan[],
  neighborhood{depth, node_count, edge_count_total, edges[]}}`
- `trailtracker.nav-expand/v1`: `{schema, command, dir, target,
  identity{...}, direction, depth, budget{...}, total_edges, cursor,
  returned, truncated, next_cursor, nodes[], edges[]}`

### Error contract

`nav expand` reuses the `explain` target-resolution contract verbatim:
exact node id → exact file path → exact symbol name; ambiguous name exits 2
with the candidate list, unknown target exits 3 with hybrid-search
suggestions. The MCP tools map those to the existing `AMBIGUOUS_TARGET` /
`TARGET_NOT_FOUND` structured errors.

## Dogfood amendments (2026-07-07, trailtracker-nav-dogfood-fixes-7nd)

The first dogfood pass (this repo + the jellyfin decider eval) surfaced two
K1-filed defects, both fixed here. Constants live in `src/nav.rs` with the
same rationale.

### 1. Read-plan reserve (`READ_PLAN_MIN_SHARE_PCT = 35`)

Live repro: `nav pack "where are domain labels decided" . --budget 6000`
returned a pack whose seeds+cards consumed the entire budget — zero (later
one) read-plan spans. A pack without spans is not actionable: the read plan
IS the action. Fix: before the core is sized, a floor of
`clamp(35% × (limit − skeleton), min = cost(top span), max = cost(whole
plan))` is reserved for read-plan entries; the core shrink loop (cards →
seeds → orientation, never below one seed) targets `limit − reserve`.
35% buys a dozen ~130-char spans at a 6k budget while leaving the majority
to identity; the `min` clamp stops item granularity from starving the plan;
the `max` clamp makes generous budgets bit-identical to the old fill.
`budget.exceeded` now means "even the minimal core overruns the reserve
line" — i.e. the budget cannot hold a *well-formed* (actionable) pack, and
the content is best-effort. Post-fix the 6k repro yields 9 spans.

### 2. Hub damping (`HUB_TAX_FREE_BITS = 3`)

The jellyfin eval's finding 1: `GuidExtensions.IsNullOrEmpty` (degree 533)
ranked read-plan #1 and ~14 unrelated controllers rode in "2 hops from
PingPlaybackSession" via `RequestHelpers` — the centrality factor rewarded
exactly the nodes proximity should discount. Two deterministic, integer-log
mechanisms (both no-ops when every degree ≤ 14, so small graphs and all
goldens are byte-identical):

- **Arrival/waypoint hub tax.** The seed walk pays `1 + hub_tax(node)` for
  every node it steps into, where `hub_tax = ⌊log₂(1+degree)⌋ − 3` clamped
  at 0. Cost replaces hops in the proximity denominator. Waypoint taxing
  sinks the riders (2 hops *through* a hub); destination taxing cancels the
  monster hub's own centrality reward `1 + ⌊log₂(1+degree)⌋` asymptotically
  (`(1+b)/(1+hops+(b−3)) → 1`), while moderate hubs keep the original
  "central beats leaf when signal is close" behavior. The seed itself is
  exempt: its hubness is search evidence, not propagation noise.
- **IDF multi-seed damping.** `value ÷ 2^min(⌊log₂(seeds_reaching)⌋,
  hub_tax_bits(node))` — the eval's fix candidate. It fires only when a
  node is BOTH reachable from many seeds AND a hub; shared *specific* logic
  (many seeds, ordinary degree) and local hubs (one seed) keep full signal.
  Seeds are never damped.

Jellyfin after-numbers (same eval): GuidExtensions #1 → #30, controller
files in the read plan 18 → 4 (unrelated ones 16 → 3),
`UpdateNowPlayingItem` (the true
state mutator) and two `SessionInfo.cs` method spans entered the plan —
the previously-documented "SessionInfo named nowhere" gap closed — while
compression stayed 12.0× vs disciplined grep and every previously-contained
answer remained. Full numbers: `docs/evals/nav-context-efficiency.md`.

- **LLM-summarized context packs** — rejected: breaks the airgap, the
  determinism guarantee, and the whole point (exactness).
- **Token counting with a real tokenizer** — rejected: std-only crate, and
  any specific tokenizer would be wrong for half the models. Chars are
  deterministic and conservative; the response reports both.
- **Returning file contents in the pack** — rejected: the navigator's job is
  to tell the agent *what to read and why*, not to duplicate the filesystem
  into context. Precise spans keep the read step under the agent's control
  (and its own budget).
- **A persistent index/server** — deferred: analysis is fast enough to run
  per call (and `--incremental` already caches lowering); statelessness
  keeps the MCP server pure orchestration.

## Consequences

- Two new CLI subcommands and two new MCP tools; everything additive.
  Goldens (base-graph + ontology views) are untouched by construction — nav
  only *reads* the graph.
- `explain`'s internal resolver becomes `pub(crate)` so nav reuses the exact
  resolution semantics instead of forking them.
- The decider eval (jellyfin, 2,105 files): measure chars-to-answer for
  grep-plus-read-whole-files versus one `nav pack --budget 20000`, and verify
  by hand that the pack names the right symbols. Reported honestly either
  way in `docs/evals/nav-context-efficiency.md`.
