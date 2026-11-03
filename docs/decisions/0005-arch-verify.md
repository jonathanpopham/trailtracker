# 0005 — Continuous architecture verification (`arch-verify` / `arch-init`)

- **Status:** Accepted
- **Date:** 2026-07-07

## Context
The ontology views *recover* architecture: `domains` clusters files into
business domains, `layers` places units on the clean-architecture onion and
flags direction violations. Both are **descriptive** — they report what the
code is, and nothing fails when the code quietly stops being what the team
intended. The gap between "report" and "contract" is exactly the territory
ArchUnit (JVM) and dependency-cruiser (JS) occupy: humans declare the
INTENDED architecture, a tool verifies the ACTUAL code against it, CI fails
on drift. Neither incumbent is cross-language, and neither grounds its rules
in a recovered graph — they re-derive structure from imports per ecosystem.

TrailTracker already has every ingredient: a deterministic base graph across
56 languages, a deterministic file→domain clustering
([`assign_domains`](../../src/extract/domains.rs)), a deterministic
unit→layer placement with violation semantics
([`assign_layers`](../../src/extract/layers.rs)), and a ground-truth format
that already expresses "a domain is a set of path prefixes"
([`eshop_domains.json`](../../benchmarks/ground_truth/eshop_domains.json)).
What is missing is the *contract*: a human-authored spec and a gating
verifier.

Two constraints bind the design:

1. **Golden output must not move.** The corpus regression gate pins `graph`
   and the four ontology views byte-for-byte. Verification must be strictly
   additive: new commands, no changes to existing emissions.
2. **The tool stays read-only and deterministic.** `arch-verify` must be a
   pure function of (spec, analyzed tree) — same inputs, same findings, same
   exit code — and must never write into the target repo on its own.

## Decision

### The spec: `.trailtracker-arch.json`, human-authored intent
`trailtracker arch-verify <DIR>` reads `<DIR>/.trailtracker-arch.json`
(override: `--spec PATH`). The spec reuses the ground-truth shape the
benchmark already proved out — **a domain is a name plus repo-relative
`pathPrefixes`** — and adds a rule list:

```json
{
  "format": "trailtracker.arch-spec/v1",
  "domains": [
    { "name": "Ordering", "pathPrefixes": ["src/Ordering."] },
    { "name": "Basket",   "pathPrefixes": ["src/Basket.API/"] }
  ],
  "rules": [
    { "type": "domain-existence",            "domain": "Ordering" },
    { "type": "domain-containment",          "domain": "Ordering" },
    { "type": "forbidden-dependency",        "from": "Ordering", "to": "Basket" },
    { "type": "forbidden-layer-dependency",  "from": "Domain",   "to": "Infrastructure" }
  ]
}
```

A file belongs to the declared domain whose prefix matches its path;
longest prefix wins, ties go to declaration order; unmatched files are out
of scope (exactly the ground-truth semantics). Every rule accepts an
optional `id` (default: derived, e.g. `forbidden-dependency:Ordering->Basket`)
and `severity` (`error` default, or `warn`). Unknown **top-level keys** are
ignored (forward compatibility; `arch-init` uses this for advisory
baggage), but an unknown **rule type**, a rule referencing an undeclared
domain or layer, a duplicate domain name, or malformed JSON is a usage
error — the spec fails **closed** (exit 2 with a fix line), never
half-evaluates.

### Rule vocabulary v1 — small and high-signal
1. **`domain-existence`** — the declared domain must be recovered non-empty:
   at least one analyzable file matches its prefixes. Catches architecture
   erosion (a declared component that no longer exists in code).
2. **`domain-containment`** — files under the domain's prefixes must still
   *cluster with* that domain. Mechanism: each recovered business cluster is
   anchored to the declared domain owning the majority of its files; a member
   file of declared domain X whose recovered cluster is anchored to a
   different declared domain Y has migrated (evidence: `path — declared X,
   clusters with Y`). Files in unanchored clusters (e.g. `Shared/Platform`)
   do not fire — only a *defection to another declared domain* is drift.
3. **`forbidden-dependency`** — no DEPENDS-family edge may point from a file
   of domain `from` to a file of domain `to`. Evaluated over the actual
   cross-domain edges (endpoints resolved to files by the same containment
   walk the extractors use, then to declared domains by prefix). Evidence:
   edge count + example `fromPath -[KIND]-> toPath` pairs.
4. **`forbidden-layer-dependency`** — the layer view's violation semantics,
   but spec-driven and gating instead of informational: unit→unit dependency
   mass is aggregated by the recovered `unit_layer` placement, and the rule
   fires when any mass flows `from`-layer → `to`-layer. Evidence: aggregate
   count + example unit pairs. Layer names are validated against the six
   canonical layers (`Domain`, `Application`, `Infrastructure`,
   `Presentation`, `Test`, `Shared`).

Deliberately **out** of v1: allowed-list dependency modes ("A may ONLY
depend on B,C"), cycle detection, wildcard/regex domain matching, symbol-level
rules. Each is a compatible extension of the same spec; v1 ships the four
rules that catch the drift classes we have actually watched happen (file
migration, boundary erosion, layering inversion, component death).

### Verify is a pure function; exit codes are the API
`verify(spec, analysis) → findings` lives in `src/arch.rs` and touches no
I/O; the CLI wraps it. Findings carry rule id, type, severity, message, and
bounded evidence (≤ 5 examples per finding, full counts always). Output is
a human table by default, `--json` emits one
`trailtracker.arch-verify/v1` envelope. Exit codes extend the E1
dictionary: **0** spec holds (no findings, or warn-only), **1** at least one
`error`-severity finding (the CI gate), **2** usage/spec error, **3** DIR or
spec path missing, **4** analysis failure. `warn` reports without gating —
the adoption ramp for rules a team is not ready to enforce.

### `arch-init` — adopt in one command
`trailtracker arch-init <DIR>` bootstraps a spec from the CURRENT recovered
architecture: recovered business domains become declared domains with
`pathPrefixes` derived by the same greedy dominant-prefix set-cover
`gt_bootstrap.py` proved out (a prefix counts when ≥ 80% of the files it
matches are cluster members; prefixes are added until ≥ 80% of members are
covered), plus `domain-existence` + `domain-containment` rules per domain.
The current inter-domain dependencies are recorded as an **advisory
`observedDependencies` baseline** (ignored by verify) with a `notes` scaffold
explaining how to promote an observed edge into a `forbidden-dependency`
rule. The spec prints to stdout (stdout is data; redirect to adopt) or
writes via `-o PATH`, refusing to overwrite an existing file — the tool
never silently mutates a target.

### JSON reading
The runtime crate keeps its writer-only JSON policy for its own output. The
defensive reader that `enrich-domains` used for backend replies is promoted
to `core::json::read` and shared: a spec file is exactly the same category
of input — external, untrusted, parsed defensively, never re-emitted
byte-for-byte.

## Consequences
- The ontology stack becomes an enforceable contract: a 3-line CI step
  (`trailtracker arch-verify .`) fails the build the moment a forbidden
  dependency, a layering inversion, or a domain defection lands.
- Cross-language for free: rules are evaluated over the recovered graph, so
  one spec grammar covers all 56 frontends — ArchUnit territory without the
  JVM fence.
- `domain-containment` gates on the *clustering*, which makes the clustering
  itself load-bearing: a future change to `assign_domains` that reshuffles
  clusters will surface as containment findings in consumer CI. That is the
  point (drift detection), but extractor changes now carry a compatibility
  duty documented by the cohort gate.
- Additive by construction: no existing command, emission, or golden moves.
