# 0006 — The rewrite engine: propose-then-approve span rewrites

- **Status:** Accepted
- **Date:** 2026-07-07

## Context
Everything TrailTracker shipped before this ADR is read-only: the analyzer
parses, lowers, scores, and reports, and its golden gates pin that behavior
byte-for-byte. K3b introduces the first code-MODIFYING capability. The
governing requirement (Jonathan, 2026-07-07) is a design law, not a feature
request: **"it needs approval just like an agent."** A rewrite is an actor
with write access to source; it gets the same two-phase discipline agents get
— a reviewable proposal first, an explicit approval step second, and no path
that collapses the two.

Two existing assets make span rewrites tractable and auditable:

1. **The lossless CST (ADR-0001).** Every byte of source has a home in the
   tree, so a rewrite can be expressed as a set of byte-span replacements and
   the untouched remainder is *provably* untouched — reconstruction outside
   the edited spans is byte-identical by construction, testable with the same
   machinery the losslessness gate already uses.
2. **The deterministic CPG overlay (ADR-0003).** Statement spans, `FLOWS_TO`
   control flow, and may-reach `DATA_DEP` are exactly the facts a rewrite
   rule must consult to argue safety — and because they are deterministic,
   the argument is reproducible.

K3c (equivalence certificates) attaches to whatever format this ADR defines,
so the proposal document must be a stable, hashable, machine-readable unit.

## Decision

### The contract (non-negotiable)
Two commands, two phases, no shortcut:

- **`trailtracker rewrite propose <rule> <target> [DIR] [-o proposal.json]`**
  analyzes and emits: a unified diff on stdout (the human review surface) and
  a `trailtracker.rewrite-proposal/v1` JSON document (`-o` writes it;
  `--json` emits it on stdout instead of the diff). **Propose never writes
  source.** There is no `--apply` flag on `propose`, and there never will be.
- **`trailtracker rewrite apply --proposal proposal.json [DIR]`** is the only
  writing path, and it refuses unless *all* of the following hold:
  1. the proposal parses as `trailtracker.rewrite-proposal/v1`;
  2. its `proposal_hash` verifies (recomputed over the canonical body — a
     tampered or hand-edited proposal is rejected, exit 4);
  3. the target file's **current** content fingerprint equals the proposal's
     `file_fingerprint` — the file is unchanged since it was proposed.
     A stale file is exit 4 with the fix line: re-run `rewrite propose`;
  4. every edit's `before` text still matches the bytes at its span
     (belt-and-braces under 3).
  Apply touches **only** the proposal's spans, writes atomically (temp file
  in the target's directory + rename), and reports what changed. There is no
  `--force`, no `--skip-verify`, no environment variable override.
- **`trailtracker rewrite rules`** lists rule ids, versions, and recognized
  shapes (machine-readable with `--json`), so agents can discover the
  vocabulary without trying commands.

No flag combination may skip the two-step. The approval artifact is the
proposal file itself: possessing a hash-valid proposal that matches the
file's current bytes *is* the approval token, and it self-invalidates the
moment the file drifts.

### The proposal document: `trailtracker.rewrite-proposal/v1`
One JSON object per propose run:

```json
{
  "schema": "trailtracker.rewrite-proposal/v1",
  "rule": {"id": "dead-branch-elim", "version": "1"},
  "dir": "<DIR as given>",
  "file": "<target path, relative to DIR>",
  "file_fingerprint": "fnv1a64:<16 hex over the file's exact bytes>",
  "edits": [
    {
      "span": {"start": 120, "end": 190},
      "before": "<exact original bytes of the span>",
      "after": "<replacement bytes>",
      "why_safe": "<one-sentence safety argument>",
      "cpg_facts": ["<the CPG facts consulted, one per line>"]
    }
  ],
  "rejections": [
    {"span": {"start": 300, "end": 350},
     "reason": "machine_readable_snake_case",
     "detail": "<human sentence>"}
  ],
  "proposal_hash": "fnv1a64:<16 hex>"
}
```

- **Fingerprints are FNV-1a-64** (`fnv1a64:<16 hex>`), the same std-only hash
  the dossier and enrich attestations use. This is a *change-detection*
  fingerprint, not a cryptographic signature — the threat model is drift and
  accident, not an adversary forging proposals; K3c's certificates are the
  place for stronger claims.
- **`proposal_hash`** is FNV-1a-64 over the canonical single-line JSON
  serialization (sorted keys, the repo's deterministic writer) of the whole
  document *minus the `proposal_hash` member itself*. Verification
  recomputes; any drift in any field — spans, texts, why-safe, rejections —
  invalidates.
- **`before`/`after` carry the full span texts**, so a reviewer (or K3c) can
  audit the exact byte delta without re-running analysis, and apply can
  verify per-span.
- **`why_safe` + `cpg_facts`** are the rule's safety argument: `why_safe` is
  the sentence, `cpg_facts` the deterministic evidence (statement ids, edge
  roles, def sites) pulled from the real CPG emission for the target file.
  Statement ids in `cpg_facts` are proposal-scoped (`fn::{name}#{line}`-rooted,
  derived from the target file alone) — self-consistent within the document.
- **`rejections`** record near-miss sites the recognizer refused, each with a
  machine-readable `reason`. Refusals are output, not silence — the same
  honesty rule the parser diagnostics follow.

### Determinism: no wall clock anywhere
The proposal contains **no timestamp**. Same binary + same file ⇒
byte-identical proposal, hash included. This follows the dossier precedent
("attests a content fingerprint, never a wall clock") and keeps the
determinism test trivial: run propose twice, compare bytes. Rejected
alternative: an enrich-style attestation timestamp excluded from the hash —
rejected because a field outside the hash is a field apply cannot defend, and
because rewrite (unlike enrich) has no non-deterministic input to attest.
When K3c needs signing time, it belongs in the *certificate*, not the
proposal.

### Span-edit engine: the safety invariant
The engine's one primitive: given `(source, [(byte_span, replacement)])`,
produce the new source. Invariants, each enforced and tested:

- **Outside-span identity:** every byte outside the edited spans is
  byte-identical in the output (test: empty edit set reproduces the source
  exactly; apply-then-revert round-trips to the original bytes).
- **Overlap rejection:** overlapping or out-of-bounds spans are an error,
  never a silent reorder. Edits are applied in deterministic
  descending-start order so earlier spans' offsets are never disturbed.
- **Char-boundary safety:** span endpoints must fall on UTF-8 boundaries
  (they always do when they come from the CST, whose spans are token spans —
  the check defends against hand-built proposals).

### Rule anatomy
A rule is `(id, version, recognizer, emitter)`:

- The **recognizer** walks the target file's statement tree (the same
  segmentation the CPG uses — one machinery, no drift) and partitions
  candidate sites into *recognized* (→ edits) and *near-miss* (→ rejections
  with machine-readable reasons). Recognizers are conservative by charter:
  a shape outside the documented grammar is rejected, never guessed at.
- The **emitter** produces the replacement bytes plus the `why_safe` /
  `cpg_facts` payload, consulting the CPG graph emitted for the enclosing
  function.
- **Versioning:** the version is part of the proposal and the hash; a rule
  whose recognized grammar or emission changes must bump it, because K3c
  certificates will bind to `(rule id, version)`.
- **Outermost-only per pass:** when recognized sites nest (a dead branch
  inside a dead branch), one propose run emits only the outermost — inner
  spans would shift under the outer edit. Re-running propose after apply
  reaches the newly exposed sites. Iteration over cleverness.

### Rule 1 — `dead-branch-elim` v1 (literal conditions only)
Recognized: statement-position `if` whose condition is **exactly the single
token `true` or `false`**. No constant propagation, no `!true`, no `1 == 1` —
a literal token is a grammar fact; everything else is a claim this rule does
not make.

- `if true { A } [else …]` → the then-block's statements (dedented by the
  excess indentation, a whitespace-only transformation).
- `if false { A } else { B }` → the else-block's statements.
- `if false { A } else if …` → the else-continuation (the trailing if-chain).
- `if false { A }` (no else) → the statement is removed.

Why-safe cites the CPG branch edge set: the statement's
`FLOWS_TO branch=then/else` edges prove exactly one successor set is
reachable under a literal condition, and the eliminated statement ids are
listed. Expression-position `if` (e.g. `let x = if true {…}`) is one `let`
statement at CPG grain (ADR-0003) and is **not** recognized (rejection:
`condition_not_literal` never fires for it; it is simply not a candidate) —
statement grain is the contract.

### Rule 2 — `loop-to-iterator` v1 (the honest family)
Recognized: an **adjacent statement pair** at one block level —

```text
S1: let mut ACC[: TYPE] = INIT;
S2: for X in ITER { BODY }
```

with all of: `X` a single bare identifier; the loop unlabeled; `ITER` and the
body's non-receiver positions free of `ACC`; no `?` in `ITER`; and `BODY`
exactly one of

- (a) `ACC.method(ARGS);`
- (b) `ACC op= EXPR;` (compound assignment)
- (c) `if COND { (a) | (b) }` — no `else`, no `?` in `COND`.

CPG facts consulted and cited: `ACC`'s def-site set at the loop is exactly
`{S1}` (single def, `DATA_DEP var=ACC`); the body statements have **no**
`FLOWS_TO` edges with role `break`, `continue`, `return`, or `try-exit`
(no early exit can escape the loop body).

Emission — exactness over elegance:

- (a) as `push` with `Vec::new()` / `vec![]` init, no `if`:
  `let mut ACC = ITER.into_iter().map(|X| ARG).collect::<Vec<_>>();`
  (with a `: TYPE` ascription present, plain `.collect()`).
- (a) as `push` with the `if` wrapper:
  `.filter_map(|X| if COND { Some(ARG) } else { None }).collect…` — the
  closure takes `X` **by value**, exactly like the loop body did; this is why
  `filter_map` is emitted instead of the textbook `.filter(p).map(f)`, whose
  `filter` closure receives `&Item` and silently changes types.
- everything else: the fold form
  `let mut ACC = ITER.into_iter().fold(INIT, |mut ACC, X| { BODY ACC });`
  which reuses the body text verbatim — same operators, same method calls,
  any accumulator type, no type claims.

`for x in xs` desugars to `IntoIterator::into_iter(xs)`, so `.into_iter()` is
the exact desugaring, not a style choice. The original `mut` on `ACC` is
preserved (the binding may be mutated after the loop); a possibly-unused
`mut` warning is accepted and documented rather than risking a compile break
by guessing at later mutations. Everything outside this grammar is a
rejection with a machine-readable reason (`loop_pattern_not_bare_ident`,
`body_not_single_accumulation`, `if_has_else`, `acc_read_in_body`,
`acc_in_iterable`, `body_has_early_exit`, `loop_labeled`, …).

### Rule 3 — `extract-function` v1 (the honest version: closure extraction)
Full `fn` extraction requires **parameter and return types**, and TrailTracker
has no compiler and refuses to fabricate types (the resolution-ladder
philosophy). Honest scoping therefore ships **extraction to a named local
closure**, which the type system infers end-to-end:

```text
let mut NAME = || {
    <span statements, verbatim, one indent deeper>
    (ret1, ret2)            // only when returns exist
};
let (ret1, ret2) = NAME();  // destructured; `mut` per the original `let`s
```

- **Target:** `--lines A-B --name NAME`; the span must tile a contiguous run
  of whole statements at one block level inside one function (rejections:
  `span_not_whole_statements`, `span_crosses_blocks`, `span_empty`,
  `span_outside_function`).
- **Parameters become captures.** Free variables read by the span capture by
  reference/`&mut` exactly as the inline code borrowed them — the CPG
  `DATA_DEP` edges from span statements to outside def sites *are* the
  parameter list, and they are cited in `cpg_facts`.
- **Returns from may-reach:** names whose def sites lie inside the span and
  which have `DATA_DEP` uses after it are returned as a tuple and
  destructured at the call site (`mut`-ness carried from the original `let`).
- **Refusals via the CPG:** any `FLOWS_TO` edge with role `return` or
  `try-exit` from a span statement, or a `break`/`continue` edge whose
  target lies outside the span, rejects the site
  (`span_jumps_outside`) — a `break` to a loop wholly inside the span is
  fine, and the edge set proves which is which. (Note the conservative
  corner: a break's edge targets the statement AFTER its loop, so a loop
  that is the LAST statement of the span has its break edge land outside
  and is refused — a legit site lost to honesty, with the edge cited.)
- **Tail honesty (v1 implementation, beyond the list above):** when the run
  ends at a block tail whose value propagates to the function's value (the
  fn-body tail, or a tail chained to it through value-position `if`/`match`),
  a discarded closure call would swallow that value — rejected as
  `span_ends_in_tail_expression`. Tails of statement-position bodies are
  `()`-typed and remain extractable; the descent tracks value-position with
  a `tail_matters` flag.
- The closure binding is `mut` when the span mutates captured state
  (assignment to a pre-existing name, method call on one, `&mut`, or a macro
  invocation — conservative toward `mut`, whose worst case is a lint
  warning, never a compile break).

This is deliberately smaller than textbook Extract Function. When TrailTracker
grows type information, `extract-function` v2 can emit a real `fn`; v1 says
exactly what it does and does all of what it says.

### CLI + gates
`rewrite` registers per the E1 conventions: stdout data / stderr diagnostics,
exit 0 success, 2 usage, 3 missing path, 4 analysis-or-verification failure,
EPIPE-tolerant writes, did-you-mean on unknown subcommands/rules, and an
entry in `capabilities`. A propose run with zero recognized sites exits 0
(an empty result is an answer, not an error) and still reports its
rejections; `apply` refuses an empty-edit proposal (exit 2 — there is
nothing to approve). `propose` additionally refuses (exit 4) any file that
carries parse diagnostics: statement segmentation on a file that did not
parse cleanly could misplace spans, and a rewrite may not build on a
guessed tree. The analyzer's own gates are untouched: `graph`, `cpg`,
`stats`, goldens, and the corpus regression suite must remain byte-identical
— the rewrite engine is a *consumer* of the analysis, never a mutation of it.

### What K3c attaches to
The proposal is the certificate's subject: K3c binds an equivalence argument
to `(rule id, rule version, proposal_hash)`. That is why the hash covers
every byte of the body, why rules are versioned, and why `before`/`after`
texts are embedded rather than referenced — a certificate must be checkable
against the proposal alone, offline.

## Alternatives considered
1. **`rewrite <rule> --apply` in one step.** Rejected without discussion:
   violates the governing requirement. The two-phase shape is the point.
2. **Diff-based apply (store only a unified diff, apply with fuzz).**
   Rejected: fuzzy patching is exactly the "file drifted underneath the
   approval" hazard the fingerprint exists to prevent. Byte spans + a file
   fingerprint make staleness a hard error instead of a heuristic.
3. **Full-file `after` snapshot instead of span edits.** Rejected: hides
   *what changed* from review, breaks the outside-span identity proof, and
   bloats proposals; span edits are the CST-native unit.
4. **AST re-synthesis (transform tree, re-print).** Rejected: re-printing
   destroys the lossless guarantee for every untouched byte (comments,
   spacing) and would move goldens. Span splicing preserves them by
   construction.
5. **Timestamped attestation à la enrich.** Rejected — see the determinism
   section.
6. **Typed `fn` extraction via heuristic type guessing.** Rejected: a wrong
   parameter type is fabrication with a compile error attached. Closure
   capture is what the language provides for exactly this situation.

## Consequences
- TrailTracker gains a write capability whose every write is pre-imaged,
  hash-bound, and reviewable; agents (MCP) get **no** rewrite tool in this
  slice — whether and how agents may propose is K3d's decision, and apply
  approval stays with the human in any case.
- The CPG becomes load-bearing for safety arguments, which is new pressure
  on its honesty guarantees — exactly the pressure ADR-0003's
  under-claiming policy was built for.
- Rules are deliberately narrow; the mechanism (proposal format, span
  engine, gates) is the durable asset, and each future rule is an additive,
  versioned unit K3c can certify independently.
