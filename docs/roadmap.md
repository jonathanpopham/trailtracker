# Roadmap

This roadmap is grounded in the architect requirements and the hard operating
context of airgapped defense installations.

## Operating context: no LLM in the runtime

The deployed environment is airgapped defense hardware. **There is no LLM available
at analysis time.** The consumers of the graph are deterministic tools, query
engines, and human analysts.

Consequences that shape every design decision:

- Call/type resolution must be **deterministic and auditable**, not model-assisted.
- **Ambiguity is preserved, never guessed.** Where a reference cannot be resolved
  to exactly one definition, TrailTracker emits the candidate set and the reason —
  it does not pick one. There is no LLM disambiguation step.
- "Linearize for LLMs" is demoted from a primary driver. Tiered/streamed output is
  still valuable, but justified by tooling, query cost, and analyst workflow — not
  by LLM consumption.

## Call-resolution design: deterministic scope ladder

A reference is resolved by walking scopes from most-specific to least-specific. The
**first level that yields any candidates decides the outcome** — the search does not
continue past a level that already matched:

1. **Receiver** — `self.m()` / `Self::m()` / method calls inside an `impl`: resolve
   against the methods of the enclosing `impl`'s `Self` type.
2. **Local** — definitions in the same module/file.
3. **Qualified** — `a::b::foo()` or `Type::new()`: the leading path segments are a
   native Rust scope hint (the call site carries the full path for free). Resolve
   against the module/type the qualifier names, mapped through the file's `use`
   imports.
4. **Import** — a simple name brought into the file by a `use`.
5. **Global** — a name that is unique across the entire crate.

Outcome at the deciding level:

- exactly **1** candidate → `resolved`, with `resolution` = the level name
  (`receiver` / `local` / `qualified` / `import` / `global`).
- **>1** candidates → `ambiguous`: emit the `CALLS` edge to an explicit
  `UnresolvedSymbol` *plus* a `candidates` property listing every candidate id.
  Never pick one.
- **0** at every level → `external`: an explicit `ExternalDependency` /
  `UnresolvedSymbol` node.

Every `CALLS` edge records provenance: `resolution`, `candidate_count`, `method`,
`callee`, and (when present) `qualifier`. The call graph is fully auditable by
construction — a requirement for defense validation.

**The `global_method` rung (member calls, unknown receiver).** When a member call
`x.m()` reaches the global fallback, the honest candidate set is every same-name
method **plus** every same-name free function in languages whose member syntax can
reach one (namespace imports and function-valued properties in TS/JS, `mod.f()` in
Python/Mojo/Zig, `pkg.F()` selectors in Go, table fields in Lua, top-level
extensions in Kotlin/Scala). Free functions are **counterevidence only**: they
widen the set (forcing an ambiguous edge) but a member call is never *resolved* to
a free function on name evidence alone — with no same-name project method the call
stays `external`. This is what keeps a repo's one `private json()` method from
absorbing every `response.json()` in the codebase, and a lone `log()` helper from
absorbing every `console.log()`.

### Design properties

- **AST/token-tree extraction**, not regex — calls come from the real lossless
  token tree.
- **Full path qualifiers are native**, not a per-language heuristic.
- **Candidate sets preserved**, never guessed — airgap-safe and deterministic.
- **Resolution provenance on every edge** — conservative and auditable.

## Prioritized backlog

### P0 — call-resolution ladder + first-class ambiguity

Replace the current "unique-name-or-unresolved" resolver with the scope ladder
above. Concretely:

- Retain the **full call path** at the call site (currently only the last segment is
  kept); thread it through as the qualifier hint.
- Build a **symbol table with scope**: module path + owner type are already encoded
  in every node's `qualified_name`; index by `(simple_name)`, `(module, name)`,
  `(type, method)`.
- Build a per-file **import map** from `use` declarations for the import level.
- Emit `candidates` + `resolution` + `candidate_count` on `CALLS` edges; extend
  `stats` with `resolved/ambiguous/external` counts by level.

### P1 — defensive, conservative processing

- Wrap each file's parse + lower in `catch_unwind` so one malformed file cannot
  abort a whole-repo run (matches the "conservative failure modes for defense code"
  requirement). Record the failure as an explicit diagnostic node, never silence it.
- Keep all slicing UTF-8/bounds safe (already true via `ByteSpan::text`).

### P2 — graph-quality analyses (std-only, deterministic)

- **Circular-dependency detection** (Tarjan SCC) over `IMPORTS`/`CONTAINS`.
- **Per-function complexity metrics** (cyclomatic = branch/decision count off the
  CST) as node properties.
- **Merkle/incremental indexing**: hash each file (FNV-1a already available), cache
  its subgraph, re-lower only changed files. Feeds the speed + eval requirements.

### P3 — output, breadth, and bigger lanes

- **Tiered output** for tooling/analysts (manifest → architecture → symbol index →
  full detail), and **AST-aware source chunking** off the lossless CST. Justified by
  query cost and analyst workflow, not LLM consumption.
- **Manifest grammars** onto the proven core: Cargo/TOML, MSBuild XML, and `.sln`.
- **Taint / dead-code / blast-radius** analyses as derived graph views.
- **SQLite + recursive-CTE importer** and **JSON-LD / N-Quads export** as optional,
  out-of-runtime serialization targets (edges are already triples).

### Cross-cutting — eval harness + formal verification (IMPLEMENTED, build-time)

**Decision:** verification is a **build/CI step, not a shipped feature.** The
deliverable is the `trailtracker` CLI executable. CI records test outcomes
and the binary SHA-256 in a verification report; this is evidence from checks,
not a proof of whole-program correctness. Kani is an optional, non-blocking
additional check. None of the verification tooling enters the runtime binary.

Structure (shipped): a cargo **workspace** keeps the runtime crate std-only and
zero-dep; a separate, never-shipped `eval` member holds the harness (also
std-only).

Implemented:

- **Hermetic property/fuzz harness** (`eval/src/property.rs`): own deterministic
  xorshift PRNG + generators (random chars, token soup, real-source mutations);
  asserts the universal invariants — no panic, lossless round-trip, deterministic
  output — with seed-reproducible failures.
- **Self-analysis regression** (`eval/src/regression.rs`): runs TrailTracker on
  the repo twice; asserts lossless=100%, zero error bytes, zero parse failures,
  byte-identical output across runs, plausibility lower bounds.
- **Hash-attestable report** (`eval/src/verify.rs` + std-only SHA-256 in
  `eval/src/sha256.rs`): deterministic JSON report carrying regression + property
  results and the SHA-256 of the built binary; the report's own SHA-256 is
  printed for attestation. Non-zero exit blocks CI.
- **Bounded formal proof** (`eval/src/kani_proofs.rs`, `#[cfg(kani)]` only): Kani
  checks Rust parser losslessness for strings of at most five characters from
  a selected ASCII alphabet. This does not prove all frontend semantics.
- **CI** (`.github/workflows/ci.yml`) + portable local mirror
  (`scripts/verify.sh`): fmt → clippy(-D warnings) → build → test → verify gate →
  upload report; separate Kani job.

Still open: golden fixtures, vendored multi-repo corpus, A/B graph-diff harness,
throughput/memory benchmarks, and a ground-truth oracle (canonical-parser diff) for
definition recall/precision.
