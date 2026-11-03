# The Lexicon & Domain Classification

_Design recorded 2026-07-01. **Design only** — no implementation exists or may
begin until the Phase-1 exit criteria (external node **and** flagship edge
verification) are met; see the [roadmap](./roadmap.md) and issue #1. This
document is the clean-room record of independent derivation: every term,
algorithm, and structure here was chosen on its own merits and deliberately
avoids the vocabulary of any prior system._

## Scope — two ontologies, one boundary

| | The Atlas | The Lexicon |
|---|---|---|
| Answers | what code **is** | what code is **about** |
| Grounded in | grammar — provable from source | curated world-knowledge |
| Contents | 9 node / 9 edge kinds ([ir-atlas.md](./ir-atlas.md)) | `Concept` nodes + `SIGNALS` edges |
| Grows by | the [extension protocol](./ir-atlas.md#extending-the-ir) | curation + corpus mining |
| Verified by | canonical-parser oracles, goldens, Kani | its own goldens (see § Versioning) |

The boundary is hard: the Atlas never contains meaning judgments; the Lexicon
never contains structural facts. Classification *reads* both and writes its
results back into the Atlas graph as `GROUPING` edges with provenance.

The Lexicon **ships** (it is a data file the std-only binary reads — no
network, no LLM, no new dependencies). The mining tools that help build it
live in the never-shipped eval crate.

## The hierarchy

```
Universe → System → Region → District → Code
```

- **Universe** — the whole analysis graph; may span multiple repos.
- **System** — one repo (C4's "Software System"; multiple per Universe).
- **Region** — coarse architectural cluster.
- **District** — fine cluster within a Region.
- **Code** — the existing `Function` / `Type` leaves. Not new nodes.

Rejected names, for the record: *Component/Element* (web-loaded),
*Container* (implies deployable), and any term used by prior art in this
space (clean-room discipline).

## Grouping edges

Two new edge kinds under a new read-side super-relation `GROUPING`, kept
fully distinct from the syntactic `CONTAINMENT` family:

| Kind | Domain → Range | Means |
|---|---|---|
| `CLASSIFIED_INTO` | Function/Type → District/Region | a leaf's assigned cluster |
| `ROLLS_UP_TO` | District → Region → System → Universe | cluster parentage |

Both point child → parent, like the rest of the lattice. They enter the
ontology through the standard [extension protocol](./ir-atlas.md#extending-the-ir)
when implementation starts — same PR updates `ontology.rs`, the Atlas doc, and
the machine-readable jsonl.

## Partitioning — deterministic by specification, not by hope

Hierarchical **Leiden (CPM)** over the dependency-weighted graph (the
`DEPENDS` super-relation: CALLS + USES_TYPE + IMPORTS + DEPENDS_ON), coarse
resolution → Regions, fine → Districts. Std-only, hand-rolled, ~O(edges) per
pass.

"Deterministic" is specified, not assumed. All four of the following are part
of the contract and each gets a regression test:

1. **Fixed seed** and **stable iteration order** — nodes visited in
   lexicographic node-id order, never hash order.
2. **Pinned tie-breaking.** Leiden's local-move phase encounters equal-gain
   choices; on a tie, a node joins the community whose lexicographically
   smallest member id is smallest. No unspecified tie remains.
3. **Versioned resolution constants.** The CPM resolution parameters
   (`RESOLUTION_REGION`, `RESOLUTION_DISTRICT`) are named, versioned
   constants. Changing either reshuffles every user's Regions, so a change is
   a **semver-major event for the classifier** and requires re-blessing the
   clustering goldens deliberately.
4. **Directory-seeded prior.** Leiden accepts an initial partition; ours is
   seeded from top-level directory structure (deterministic, free, and it is
   the mental model the repo's own authors already expressed). Leiden then
   refines — it may merge or split seed communities, but it starts from the
   humans' map instead of fighting it.

**Hub handling.** High-in-degree, low-cohesion nodes (utils, helpers, shared
kernels) are not forced into whichever Region the resolution parameter
favors. A node whose classification is not robust — its assignment flips
under the documented perturbation check — is labeled `infrastructure` with
the evidence attached, exactly as the CALLS ladder preserves ambiguity as a
`candidates` set rather than guessing. Never guess; show the evidence.

## Cluster identity across runs — names label identities, they are not identities

The semantic-diff story (TT-49: "what changed architecturally between commit
N and N+1?") requires clusters to be *matchable* across runs, and naive
content-derived identity breaks the moment a file moves. The contract:

- A Region/District carries a **persistent identity**, assigned at first
  appearance.
- On a new run, clusters inherit identity from the previous run's cluster
  with **maximum member overlap** (Jaccard over member node-ids;
  deterministic tie-break by smallest member id). A cluster with no match
  above the floor is *born*; an unmatched old cluster is *retired*. Births,
  retirements, merges, and splits are first-class diff events.
- The **name** (§ Naming) is a label attached to the identity. A rename with
  stable membership and a membership change with a stable name are different,
  separately reportable events.

**Stability eval** (built with the classifier, not after): run the clusterer
on commits N and N+1 of a pinned corpus repo and assert cluster churn is
proportionate to code churn — a one-file change must not reshuffle the map.
Same-input byte-reproducibility goes in the regress goldens; this eval covers
*proportionate response to small input change*, which is the property users
actually feel.

## Naming — never an LLM (hard rule)

Deterministic fusion of four evidence sources, in priority order:

1. **Package→Concept signals** (highest): the cluster's `ExternalDependency`
   nodes matched against Lexicon `SIGNALS` edges.
2. **Path/directory consensus** across members.
3. **TF-IDF** over member identifiers.
4. **Central representative** (highest within-cluster degree) as the fallback
   qualifier.

The winning `Concept` names the cluster; every Region/District carries
**naming provenance** — the evidence rows that produced its name — so a name
is never an unexplained assertion.

## The Lexicon data model

`Concept` nodes (Authentication, Web, Persistence, Serialization, …) and
`SIGNALS` edges (package / path-fragment / identifier-keyword → Concept, per
ecosystem, with a weight). Same self-describing graph-jsonl format as
[`ir-atlas.graph.jsonl`](./ir-atlas.graph.jsonl), separate file, so it loads
and visualizes like any other TrailTracker graph.

**Seeding:** hand-curated core mappings + mining the eval corpus — the pinned
verification repos are already a labeled sample of which packages dominate
each ecosystem. Mining tooling lives in the eval crate; the curated output
ships.

**Versioning (the Lexicon is data, and data drifts):** the file carries a
semver of its own, and classification output records which Lexicon version
named it. Lexicon edits go through their own golden: a curation change that
silently renames Regions across every user's graph must show up as a diff a
human blesses, exactly like a parser change against the corpus goldens.

## Pipeline (end to end)

```
Atlas graph ──(DEPENDS projection)──▶ Leiden (seeded, pinned)
     ▲                                   │ Regions/Districts
     │                                   ▼
     │                        identity matching vs previous run
     │                                   │
     │                        evidence gathering per cluster
     │                                   │
     │                        Lexicon SIGNALS match ──▶ Concept name
     │                                   │
     └── GROUPING edges + naming provenance written back ──┘
```

Output is part of the deterministic graph: byte-identical on reruns, coverable
by regress goldens, hash-attestable — which is precisely what an LLM-named
hierarchy can never be.

## Exit criteria (mirrors roadmap Phase 3)

A real polyglot corpus repo produces a stable, named hierarchy; reruns are
byte-identical; the stability eval passes on adjacent commits; every name has
provenance; all of it gated in CI alongside the existing goldens.
