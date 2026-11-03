# 0007 — Rule-wise equivalence certificates for rewrites

- **Status:** Accepted
- **Date:** 2026-07-08

## Context

ADR-0006 gave TrailTracker its first write capability, governed by
propose-then-approve: a rewrite ships as a hash-bound, reviewable proposal, and
`apply` refuses anything tampered or stale. That contract defends the
*integrity* of a proposal — the bytes you approve are the bytes that land. It
says nothing yet about the *truth* of a proposal: whether the `after` text
actually preserves the behavior of the `before` text. `why_safe` and
`cpg_facts` are an argument, but nothing re-checks the argument.

K3c closes that gap. Every rewrite proposal gains a **checkable certificate of
behavior preservation** (`trailtracker.rewrite-cert/v1`), and a verifier that
recomputes everything from the original source and the proposal alone —
trusting nothing cached, nothing claimed.

### Honest scope: general equivalence is undecidable

Whether two arbitrary programs are equivalent is undecidable (Rice's theorem);
no tool can certify arbitrary rewrites, and TrailTracker will not pretend to.
What IS tractable is **rule-wise certification**: each rewrite rule is a narrow,
versioned transformation schema, and for a narrow schema one can

1. state — once, per `(rule id, version)` — why *any* application matching the
   recognizer preserves behavior (the **schema obligation**), and
2. check — per application — that this particular before/after pair is really
   an instance of that schema and nothing more (**structural verification**).

The certificate is the conjunction: "this application matches rule R vN's
recognized shape, its graphs differ by exactly the remapping R vN licenses, and
R vN's preservation argument is stated here / machine-checked there." A
certificate is NOT a proof that the whole program is correct, that the code
compiles, or that any transformation outside the three shipped rules is safe.

## Decision

### Two-layer certification

**Layer 1 — schema obligation (per rule, once).** Each rule carries a formal
statement of the argument that its recognized shape → emitted shape mapping
preserves behavior. Where the argument reduces to a finite claim about a small
semantic model, it is encoded as a Kani harness over that model
(`eval/src/kani_proofs.rs` pattern: `#[cfg(kani)]`-gated, self-skipping when
Kani is absent — `scripts/verify.sh` runs it only if `cargo-kani` is
installed). Where it does not, it is marked **MANUAL** with its assumptions
listed explicitly. Model proofs are proofs about the *model*; the fidelity of
the model to Rust semantics is itself an assumption and is recorded as one.

**Layer 2 — structural verification (per application).** The checker
recomputes, from the original file bytes and the proposal alone:

- the statement-level CPG (ADR-0003: `FLOWS_TO` control flow + conservative
  may-reach `DATA_DEP` def-use) of every function in the file **before** the
  rewrite, and
- the same for the **after** text (edits applied in memory — never on disk),

then verifies that the two sets of graphs are identical *modulo exactly the
remapping the rule licenses* (declared below per rule). Unaffected functions
must have canonically identical CPGs. The affected function's graphs must
differ by the licensed remapping and by nothing else.

Structural verification is grounded in a **node correspondence** built from the
statement trees: the before tree, transformed by the licensed tree-level
rewrite, must match the after tree statement-for-statement on `(kind,
whitespace-collapsed source text, recursive structure)`. Statement ids are
pre-order indices, so the correspondence is a total, deterministic map; every
graph fact is then compared under it. A corrupted after-text — swapped
statements, a dropped filter, an injected mutation — breaks the text match, the
edge match, or the cut match, and the failure names the exact fact that broke.

**Layer 2b — licensed-emission replay (per application, belt to 2a's braces).**
The rules are deterministic: same binary + same file ⇒ same emission
(ADR-0006). The checker therefore also re-runs the rule's recognizer+emitter on
the original file and requires every proposal edit to byte-match a recomputed
edit. Replay alone would be circular ("the emitter agrees with itself"); the
graph checks alone can miss sub-statement corruption (a whole `let` chain is
ONE statement node at CPG grain). Together they are complementary: replay pins
the bytes to the licensed emission, structure pins the graphs to the licensed
remapping. Verification runs the structural checks first (they produce the
semantically precise failure reasons) and replay last.

### The licensed remappings, declared per rule

The vocabulary: for one function, `CFG` = the `FLOWS_TO` edge set with `role`
and `branch` props; `DFG` = the `DATA_DEP` edge set with `var` and `def` props;
a statement's *subtree* = it plus everything nested under it (bodies, else
parts, arms). "Text-equal" always means whitespace-collapsed source text —
reindentation is licensed everywhere, token streams never are.

#### `dead-branch-elim` v1 — licensed remapping

Let `S` be the recognized `if` statement (condition literally `true`/`false`),
`LIVE` its reachable branch's statement list (possibly empty), `DEAD` the
unreachable subtree (possibly empty).

- **Tree:** the after tree equals the before tree with `S` replaced in place by
  `LIVE`'s statements (statement position) or with the parent's else-part
  rewritten per the six shapes in ADR-0006 (else position). All other
  statements text-equal and structurally identical.
- **CFG:** after = before with (a) every edge incident to `S` or to a `DEAD`
  statement deleted; (b) each former in-edge `P → S` (role `r`, branch `b`)
  re-stitched to `LIVE`'s first statement as `(r, b)` — or, when `LIVE` is
  empty, to the target `M` of `S`'s fallthrough edge, with role `loop-back`
  substituted for `r` iff the `S → M` fallthrough itself carried `loop-back`
  (the loop-closing join rewrites roles; the checker mirrors exactly that).
  All edges between surviving statements are unchanged.
- **DFG:** no *new* dependency may appear between surviving statements. A
  dependency between surviving statements may *disappear* only when the
  affected region (`S` + `DEAD` + `LIVE`) contains a definition of that
  variable — deleting the branch merge can only shrink may-reach sets, and
  only for variables the region defines. Dependencies incident to deleted
  statements are deleted. `S` itself must have no `DATA_DEP` edges (a literal
  condition reads nothing) — anything else is unlicensed and fails.
- **Why it preserves behavior (schema obligation):** a literal condition makes
  exactly one `FLOWS_TO branch=…` edge traversable; the other branch is
  unreachable code, and removing unreachable code plus the now-trivial test
  changes no execution. The condition itself is a pure literal — evaluating it
  had no effects. Encoded as Kani harness `k3c_dead_branch_schema` over a
  bounded model (programs of guarded statement lists over a small mutable
  state; splice(p) and p produce identical final states for all bounded p).

#### `loop-to-iterator` v1 — licensed remapping

Let `S1` be the recognized `let mut ACC = INIT;`, `S2` the `for` loop, `T` the
single replacement `let` statement.

- **Tree:** the after tree equals the before tree with the adjacent pair
  `[S1, S2(+subtree)]` replaced by exactly one flat `let` statement `T`. All
  other statements text-equal and structurally identical.
- **CFG:** edges among surviving statements unchanged. Each former in-edge
  `P → S1` (role `r`, branch `b`) becomes `P → T (r, b)`. Each former
  `loop-exit` edge `S2 → M` becomes `T → M (seq)` — the loop's exit collapses
  to straight-line fall-through. The pair's internal structure (`branch=body`,
  `loop-back`) disappears with it. `T` has no `try-exit`, `return`, `break`,
  or `continue` edge (and the before pair was licensed only if its subtree had
  none — re-checked).
- **DFG:** `T`'s external read set — the `(var, def-site)` pairs of `DATA_DEP`
  edges leaving `T` — is IDENTICAL to the pair's external read set (edges from
  `S1`+`S2`-subtree to definitions outside the pair), modulo the
  shadow-read clause (assumption 5). `T`'s external def role:
  every statement that read `ACC` from the pair (`def` sites `S1` or the
  body's accumulation statement) reads it from `T` after, with `def=let`, and
  from nothing else; no other statement gains or loses a dependency. The loop
  variable `X` was scoped to the pair and exports nothing.
- **Why it preserves behavior (schema obligation):** `for x in xs` desugars to
  `IntoIterator::into_iter(xs)`, so the chain iterates the identical sequence.
  With a single reaching definition of `ACC`, no early exit, no `?`, `ACC`
  unread in the body outside receiver position and absent from the iterable,
  the loop is exactly a left fold; `map`/`filter_map` are the specializations
  where the fold operation is `Vec::push` (guarded or not). The emitted
  closures reuse the original `ITER`/`COND`/`ARG`/body expressions verbatim,
  so per-element evaluation order and effects (including panics) are
  preserved by construction. Encoded as Kani harness `k3c_loop_fold_schema`
  over a bounded model (fold/map/filter_map vs. loop accumulation agree on
  all bounded inputs and operations).

#### `extract-function` v1 — licensed remapping

Let `R` be the recognized run of whole statements, `T1` the emitted closure
`let`, `T2` the emitted call statement. (v1 extracts to a *closure*, ADR-0006;
there is no function-level `CALLS` edge at statement grain — the relocation is
behind a deferred call whose capture list and return tuple ARE the classical
parameter/return contract, checked below as the DFG cut.)

- **Tree:** the after tree equals the before tree with `R` replaced by exactly
  two flat statements `[T1, T2]`. All other statements text-equal and
  structurally identical. `R`'s collapsed text appears verbatim (modulo
  whitespace) inside `T1` — the body is relocated, never rewritten.
- **CFG:** edges among surviving statements unchanged. Former in-edges
  `P → R_first (r, b)` become `P → T1 (r, b)`; `T1 → T2` is `seq`; former
  out-edges `R_last → M (r, b)` become `T2 → M (r, b)`. Neither `T1` nor `T2`
  has any `return`/`try-exit`/`break`/`continue` edge (and the before run was
  licensed only if no such edge left `R`'s subtree — re-checked, with
  break/continue edges whose targets stay inside `R` permitted).
- **DFG (the cut):** *parameters* — the external read set of `{T1, T2}`
  (excluding `T2`'s read of the closure name, which `T1` defines) equals `R`'s
  external read set as `(var, def-site)` pairs. *Returns* — every statement
  that read a span-local `let` binding of `R` from inside `R` reads the same
  variable from `T2` (`def=let`) after. *Mutations through capture* — for a
  variable assigned (not `let`-bound) in `R`, the def site moves inside the
  closure where statement-grain DFG cannot see it: after the rewrite, its
  reads re-attach to the definitions that reached the span's entry. Such a
  variable's after-edges must target surviving before-definitions of that same
  variable, and every former reader of the in-span assignment must still read
  the variable. This is the one place the statement-grain DFG coarsens rather
  than maps 1:1, and the certificate says so per-variable instead of hiding it.
- **Why it preserves behavior (schema obligation):** MANUAL. The argument:
  a closure called immediately at its definition site executes the identical
  statements in the identical environment — captures borrow exactly as the
  inline code borrowed (the compiler infers the minimal capture, which cannot
  be *less* than what the inline reads required), and the returned tuple
  rebinds exactly the names whose definitions escape the span. The obligation
  is manual because capture-mode inference and borrow-shape preservation are
  properties of the Rust compiler, not of a finite model this repo can check;
  the type system re-verifies every application at compile time, which is the
  strongest available backstop. Assumptions listed below apply.

#### `redundant-clone-elim` v1 — licensed remapping

*(Added 2026-07-11 — the first catalog rule after the founding three. The
recognizer, its refusal vocabulary, and the emission live in
`src/rewrite/rules/clone_elim.rs`.)*

Let `S` be the recognized statement holding the clone site — either
`let [mut] Y [: TYPE] = X.clone();` with the RHS exactly `X.clone()`, or a
plain path call `PATH(…, X.clone(), …);` with the argument exactly
`X.clone()` — where `X` is a bare local. The emission is the minimal edit:
delete the `.clone()` bytes (from the `.` to the `)`), leaving `X` in place.

- **Tree:** the after tree equals the before tree statement-for-statement;
  the ONLY licensed text change is `S`'s collapsed text losing exactly the
  `.clone()` call at the recognized position. No statement appears, moves, or
  disappears — the node correspondence is total and 1:1.
- **CFG:** after = before under the correspondence, edge-for-edge. Nothing is
  licensed to change: the statement set and order are untouched.
- **DFG:** after = before under the correspondence, edge-for-edge. `S` read
  `X` before (the clone's receiver) and reads `X` after (the moved value);
  `clone` is a method name the DFG never records as a variable. **Zero graph
  delta is the license** — the strongest remapping in the catalog: any
  appearing or disappearing edge fails verification.
- **Preconditions re-proved by the checker from the before graph** (never
  taken from the proposal):
  1. the edit span is a recognized site of `S`'s shape (re-derived from the
     statement tree);
  2. `S` is not inside any loop body (the clone may execute repeatedly; a
     move is legal at most once) — `clone_in_loop`;
  3. `X` occurs exactly once in `S` (argument-evaluation order must not
     observe the moved value) — `receiver_reused_in_statement`;
  4. `X` has exactly ONE reaching definition at `S`, of kind `let`, and that
     definition is a bare single-ident `let [mut] X …` binding (parameters,
     `ref` patterns, and destructurings may bind by reference — a claim this
     rule does not make) — `receiver_def_not_single_let` /
     `receiver_def_not_bare_let`;
  5. **the last-use proof:** no statement CFG-reachable after `S` (the
     `FLOWS_TO` successor closure) carries a `DATA_DEP` edge for `X` to that
     definition — `cloned_value_read_later`. Reads on paths that can only
     execute BEFORE `S` are permitted: a move at last use cannot invalidate a
     read that already happened.
- **Why it preserves behavior (schema obligation):** the clone's only effect
  was to produce an owned copy so the original could stay behind — and the
  CPG proves nothing is behind: no execution reads `X`'s binding after `S`.
  Moving the original into the position the copy occupied therefore yields
  the identical value to every subsequent observer, and no code observes the
  vacated binding. **The soundness direction is the key argument:** `DATA_DEP`
  is conservative may-reach def-use (ADR-0003) — it over-approximates
  readers, recording every read any execution could perform (macro
  arguments, closure bodies, and nested groups are token-scanned; `x.f = v`
  counts as a read of `x` under assumption 2). An analysis that can only err
  by INVENTING readers makes a "no reader after `S`" conclusion trustworthy:
  its failure mode is refusing a valid site, never permitting an invalid
  one. The same one-sidedness holds for the CFG side: the `FLOWS_TO`
  successor closure is syntactic (every branch edge present), so it
  over-approximates "can execute after `S`". Encoded as Kani harness
  `k3c_clone_elim_schema` over a bounded model (an owned-slot store where
  clone copies and move vacates the source slot; under the assumption that no
  later operation reads the source slot — the last-use fact — all bounded
  programs observe identical final states; dropping the assumption breaks
  the proof). The Clone/Drop trait contract is a recorded assumption
  (assumption 8), not part of the model.

#### `if-let-to-match` v1 — licensed remapping

*(Added 2026-07-12. The recognizer, its refusal vocabulary, and the emission
live in `src/rewrite/rules/if_let_match.rs`.)*

Let `S` be the recognized statement-position `if let PAT = PLACE { A } else
{ B }`, where `PLACE` is a place expression — identifiers, `self`, `.`/`::`
segments, and integer tuple-field indices only, with no groups (no calls,
indexing, or parens) — and the else-part is a plain block (no `else if`
chain, no let-chain condition, no else-position site: `else match` is not
grammatical). The emission reuses every sub-expression verbatim:

    match PLACE {
        PAT => { A }
        _ => { B }
    }

- **Tree:** the after tree equals the before tree with `S`'s node relabeled
  `if → match` and its text relabeled from the full `let` header to `PLACE`
  alone, plus exactly two NEW arm nodes — the `PAT` arm wrapping `A`'s
  statements and the `_` arm wrapping `B`'s statements, in that order, both
  block-bodied. `A` and `B`'s statements survive text-equal and structurally
  identical inside the arms; everything outside `S` is untouched.
- **CFG:** every edge among surviving statements is unchanged under the
  correspondence. `S`'s two branch departures are re-anchored THROUGH the
  arms exactly: `S --branch/then--> T` becomes `M --branch/arm--> ARM_PAT`
  plus `ARM_PAT --seq--> T'`, and likewise `else → ARM_WILD`; when the
  loop-closing join had rewritten a departure to `loop-back` (an empty
  branch as the last statement of a loop body), the arm's outgoing edge
  carries `loop-back` in its place. No other edge may appear or disappear.
- **DFG** (edges run reader → def-site): `S`'s own reads — the scrutinee —
  stay on the match node unchanged (both forms read `PLACE` exactly once,
  before any branch decision). Reads of `PAT`'s bindings re-attach their def
  end from `S` to `ARM_PAT` (the CPG places match-arm pattern definitions on
  the arm node, `def=pattern` on both sides). Any other definition attributed
  to `S`, and any appearing or disappearing edge, fails verification.
- **Preconditions re-proved by the checker from the before graph** (never
  taken from the proposal): the edit span is a recognized site — `if`
  statement, single-`let` header, top-level `=`, block else-part, and the
  place-expression scrutinee re-derived token-by-token from the tree.
- **Why it preserves behavior (schema obligation):** `if let … else` is
  defined by the language as sugar for exactly this two-arm `match`; with
  every sub-expression reused verbatim, scrutinee evaluation, pattern
  matching, binding, and both branch bodies are the same program. The one
  divergence the desugar CAN exhibit — Rust 2024 drops `if let` scrutinee
  temporaries before the else block, while `match` holds them for the whole
  statement — is excluded structurally: a place expression produces no
  temporary, so there is nothing whose drop order could differ. Encoded as
  Kani harness `k3c_if_let_match_schema` (both forms over an arbitrary
  bounded scrutinee produce equal observables for all inputs).

#### `slice-param` v1 — licensed remapping

*(Added 2026-07-12. The recognizer, its refusal vocabulary, and the emission
live in `src/rewrite/rules/slice_param.rs`.)*

Let `P` be a recognized parameter `name: &[lifetime] Vec<T>` (resp.
`name: &[lifetime] String`) of a function `F`. The emission rewrites the type
span alone — `&[lifetime] [T]` (resp. `&[lifetime] str`), the inner type `T`
and the lifetime reused verbatim — and nothing else. `&mut` borrows,
by-value parameters, path-qualified `std::vec::Vec`, and pattern parameters
are not candidates.

- **Tree:** the after tree IS the before tree. The edit lives in the
  signature, outside every statement span, so no statement's kind, text, or
  nesting may change; the identity mapping must align exactly.
- **CFG and DFG:** ZERO delta — the strongest remapping in the catalog,
  shared with `redundant-clone-elim`. Every `FLOWS_TO` and `DATA_DEP` edge
  maps 1:1 under the identity; any appearing or disappearing edge fails
  verification. The parameter's `def=param` edges still target the function
  node: the binding's name and readers are untouched.
- **Preconditions re-proved by the checker from the before tree** (never
  taken from the proposal):
  1. the edit span is a recognized parameter-type site of `F`'s signature,
     re-derived token-by-token — `site_not_recognized`;
  2. the replacement is byte-identical to the licensed emission for that
     site — `replacement_not_licensed`;
  3. every occurrence of `name` in `F`'s body is a licensed use: a method
     call in the slice-safe (resp. str-safe) vocabulary — methods that
     resolve on `&Vec<T>`/`&String` THROUGH `Deref` to the very same
     `[T]`/`str` implementation the rewritten parameter calls directly —
     indexing `name[…]` (`Index` forwards through the same deref), or
     `for … in name` iteration (`Vec` flavor only; both sides iterate `&T`).
     A method outside the vocabulary is
     `param_method_not_slice_compatible`; any other occurrence (passing
     `name` onward, `&name`, macro arguments, rebinding) is
     `param_use_not_slice_compatible`;
  4. `F`'s name never occurs in the file other than as its definition or a
     direct call `F(…)` — `function_used_as_value` (deref coercion applies
     at call sites, not to fn-pointer/closure values).
- **Why it preserves behavior (schema obligation):** the body is unchanged
  and every use of the parameter resolves to the identical function before
  and after (the std `Deref` contract, assumption 9), so `F` computes the
  same value with the same effects. At every existing direct call site the
  argument expression that coerced to `&Vec<T>`/`&String` coerces to
  `&[T]`/`&str` (deref coercion is part of the coercion lattice), so every
  existing caller compiles to the same call — and new callers holding only a
  slice/str gain access: the signature is STRICTLY more general. The
  argument is a library-contract argument about `std`, not a bounded-model
  fact, so the obligation is **MANUAL** (the extract-function precedent):
  the typed part — deref/coercion resolution — is the Rust type system's
  own guarantee, and the untyped residue (a same-named shadowing binding, a
  same-named macro) is excluded by the conservative token-level refusals
  above.

### The assumptions block (goes in every certificate)

1. **Conservative may-reach def-use.** `DATA_DEP` is may-reach, not must-reach
   (ADR-0003). Cut equality is equality of conservative sets.
2. **No aliasing analysis.** `x.f = v` and `*p = v` are reads of `x`/`p`,
   never definitions or kills. A rewrite whose safety depends on alias facts
   is outside every rule's recognizer by construction.
3. **Panic and side-effect order within collapsed regions is per-rule:**
   dead-branch deletes only unreachable code (nothing that could run is
   moved); loop-to-iterator preserves order by construction because the
   emitted closures are the original expressions verbatim in the original
   per-element order; extract-function relocates the statements verbatim
   behind an immediately-executed call.
4. **Statement grain.** The CPG models statements, not sub-expressions;
   sub-statement corruption is caught by the replay check (2b), not the graph
   checks (2a).
5. **Closure-parameter shadow reads.** Names bound *inside* a collapsed
   region (the loop variable, a fold's accumulator parameter, a span-local
   `let`) may, after the rewrite, re-read same-named *outer* definitions at
   statement grain — the DFG does not model closure-internal binders. Such
   extra edges add conservative may-dependencies only; the checker licenses
   them exactly when the variable is bound in the region and the edge targets
   a surviving definition of that name, and counts them in the certificate.
6. **Model fidelity (where a Kani harness exists).** The harness proves the
   schema over a bounded model; the mapping from model to Rust semantics is
   an argument, recorded here, not a machine-checked fact.
7. **The after text must parse cleanly.** Certification refuses (rather than
   guesses at) an after-text with parse diagnostics, exactly as `propose`
   refuses a dirty before-text.
8. **Clone/Drop trait contract (`redundant-clone-elim`).** `Clone::clone`'s
   only observable effect is producing the owned copy, and `Drop` releases
   exactly what `Clone` acquired. Eliminating a proven-last-use clone moves
   the original value's drop from the cloned binding's scope end to the
   moved-to binding's drop point; under the contract the net resource effect
   is identical (one acquire/release pair fewer, the surviving value dropped
   once). Rust does not enforce the contract: a pathological `Clone` with
   side effects, or a program observing the drop ORDER of clone-eliminated
   values, is outside the model. A wrong-type receiver (e.g. `x: &T`, where
   deleting `.clone()` changes the produced type) is a loud compile error,
   never silent misbehavior — and the recognizer already refuses parameters
   and non-bare-`let` bindings for exactly this reason.
9. **std Deref contract (`slice-param`).** `Vec<T>: Deref<Target = [T]>` and
   `String: Deref<Target = str>`, and every method in the rule's slice-safe /
   str-safe vocabulary resolves on the borrowed owner THROUGH that deref to
   the very same slice/str implementation the rewritten parameter calls
   directly — identical observable function before and after. Every direct
   call site coerces to the more general type (deref coercion). Uses of the
   enclosing function as a first-class value (fn-pointer/closure position)
   are refused within the analyzed file; a taker in ANOTHER file is outside
   the model — and a loud compile error, never silent misbehavior.

### The certificate document: `trailtracker.rewrite-cert/v1`

One JSON object per certified proposal, deterministic (no wall clock — the
dossier/proposal precedent; same input ⇒ byte-identical certificate):

```json
{
  "schema": "trailtracker.rewrite-cert/v1",
  "rule": {"id": "…", "version": "…"},
  "schema_obligation": {
    "ref": "docs/decisions/0007-equivalence-certificates.md#<rule anchor>",
    "kani": "<harness name>" | "MANUAL"
  },
  "proposal_hash": "fnv1a64:<the certified proposal's hash>",
  "file": "<relative path>",
  "before_fingerprint": "fnv1a64:<original file bytes>",
  "after_fingerprint": "fnv1a64:<rewritten bytes, in memory>",
  "before_cpg_hash": "fnv1a64:<canonical before CPG of the whole file>",
  "after_cpg_hash": "fnv1a64:<canonical after CPG of the whole file>",
  "functions": {"affected": ["fn::…"], "unaffected_verified": <count>},
  "checks": ["<machine-readable remapping facts verified, one per entry>"],
  "assumptions": ["<the numbered assumptions above, verbatim>"],
  "cert_hash": "fnv1a64:<canonical body minus cert_hash>"
}
```

- `checks` is the explicit list of remapping facts the verifier established —
  auditable without re-running, re-checkable by re-running.
- The CPG hashes are over the canonical per-function serialization (pre-order
  statement keys, collapsed text, sorted edge tuples) — the comparison
  substrate itself, attested.
- `cert_hash` follows the proposal-hash construction exactly (FNV-1a-64 over
  the canonical single-line JSON minus the hash member): change-detection, not
  cryptography; the trust anchor is *recomputation*, which `rewrite verify`
  performs from source + proposal alone.

### Certificate placement: alongside, never embedded

The certificate binds to `proposal_hash`, so it cannot live inside the hashed
proposal body (a document cannot contain its own hash's preimage), and
ADR-0006 already rejected fields outside the hash ("a field outside the hash
is a field apply cannot defend"). Therefore: the certificate is a **separate
document**. `rewrite propose -o p.json` writes `p.cert.json` beside it;
`rewrite verify` recomputes one on demand. The proposal schema is unchanged —
v1 proposals remain valid, and a proposal without a certificate is still
applyable (until K3d decides otherwise; see Consequences).

### CLI

- **`rewrite propose`** additionally certifies every non-empty proposal it
  emits and writes the certificate beside the proposal file (`-o p.json` ⇒
  `p.cert.json`). A proposal this binary cannot certify is a bug — propose
  fails loudly (exit 4) rather than shipping an uncertified rewrite.
- **`rewrite verify --proposal p.json [DIR] [--json] [-o cert.json]`** — the
  independent checker: reads ONLY the original file and the proposal, trusts
  nothing cached (not even a previously written certificate), recomputes the
  before/after CPGs and every remapping fact, and emits the certificate
  (human summary on stdout; `--json` emits the document; `-o` writes it).
  Exit 0 = verified, 4 = verification failed with the exact failed check.
- **`rewrite apply --require-cert`** — runs the full verification before
  writing; any failed check refuses the apply (exit 4). In K3c this is an
  opt-in flag: apply's existing guarantees (hash, fingerprint, span match)
  are integrity checks and remain unconditional. **Recommendation to K3d:**
  make `--require-cert` the default once the end-to-end flow has soaked, with
  no opt-out flag — the two-phase contract plus a mandatory certificate is
  the intended end state.

  **Resolved (K3d, 2026-07-11): implemented as recommended.** `rewrite apply`
  now runs the full equivalence verification unconditionally and refuses to
  write on any failed check. A `--no-cert` opt-out was considered and
  rejected: apply is the only writing path, the certificate is recomputed in
  milliseconds from inputs apply already holds, and an escape hatch would
  make "every applied rewrite is certified" a policy instead of an invariant.
  `--require-cert` remains accepted as a no-op (it re-asserts the default) so
  existing scripts and agent playbooks keep working. The end-to-end
  demonstration lives at `demos/verified-rewrite/`.

## Alternatives considered

1. **Full semantic equivalence checking (symbolic execution, translation
   validation).** Rejected: undecidable in general, and dishonest to
   approximate silently. Rule-wise certification states exactly what is
   checked and what is assumed.
2. **Trust the proposal's `cpg_facts` as the certificate.** Rejected: those
   facts were computed by the same code path that proposed the edit. The
   verifier recomputes from source and compares graphs; the proposal's claims
   are never inputs to verification.
3. **Embed the certificate in the proposal document.** Rejected — see
   "alongside, never embedded"; forced by ADR-0006's own hash discipline.
4. **Graph checks only (no replay).** Rejected: a whole `let` chain is one
   statement node; an injected `+ 1` inside the emitted fold body can leave
   every graph fact intact. Replay pins the exact bytes to the licensed
   emission.
5. **Replay only (no graph checks).** Rejected: circular — the emitter
   agreeing with itself certifies determinism, not behavior preservation, and
   gives no defense against emitter bugs on unanticipated shapes.
6. **Kani proofs over the real CPG code instead of schema models.** Rejected
   for now: the CPG emitter is string- and allocation-heavy, far outside
   Kani's tractable envelope; bounded schema models capture the semantic core
   of the obligation. Revisit if the harness envelope grows.

## Consequences

- "Verified Refactoring" becomes a true sentence with stated bounds:
  every proposal ships with a certificate whose every fact is recomputable
  from the source and the proposal alone.
- The CPG's honesty guarantees now carry a second load: they are the
  comparison substrate for equivalence. Any future loosening of ADR-0003's
  conservatism weakens certificates and must bump every rule version.
- Rules must keep their recognizers narrow: the certificate machinery verifies
  exactly the declared remapping, so widening a rule's grammar without
  widening its declared remapping fails verification — the system defends
  itself against optimistic rule growth.
- K3d owns: making `--require-cert` the apply default, and whether agents may
  run `propose`/`verify` (apply approval stays human regardless, ADR-0006).
