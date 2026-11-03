# Verified rewrite, end to end

This demo runs TrailTracker's complete verified-rewrite loop on a real file
and shows every claim being checked by machinery that does not trust the
claimant. Run it yourself:

```sh
cargo build --release
bash demos/verified-rewrite/run.sh
```

`transcript.txt` is a captured run of exactly that command — every hash in it
was produced by the built binary, and because proposals and certificates are
timestamp-free and deterministic, your run produces the same documents and
the same hashes from the same binary and fixture.

## What happens

1. **`rewrite propose loop-to-iterator orders.rs`** analyzes the fixture and
   emits a unified diff (the human review surface) plus a hash-bound
   `trailtracker.rewrite-proposal/v1` document. Propose never writes source.
   It also refuses to emit any non-empty proposal it cannot certify, and
   writes the `trailtracker.rewrite-cert/v1` certificate beside the proposal.
2. **The certificate** names the rule id and version, points at the rule's
   schema obligation (the once-per-rule preservation argument in ADR-0007,
   Kani-checked over a bounded model where tractable), records before/after
   file fingerprints and before/after CPG hashes, lists the licensed
   remapping checks that passed, and states its assumptions in full.
3. **`rewrite verify`** is the independent checker. It reads only the
   original file and the proposal — not the certificate propose wrote, not
   any cache — recomputes both CPGs, re-derives the licensed remapping, and
   replays the licensed emission byte-for-byte. It reproduces the identical
   certificate, hash included.
4. **Tampering** with one character of the proposal (`o.id` → `o.id + 1`)
   makes verification refuse with exit 4 and the exact reason: the canonical
   body no longer hashes to the recorded `proposal_hash`. The bytes you
   reviewed are the only bytes that can ever land.
5. **`rewrite apply`** is the only writing path, and since K3d it re-runs the
   full equivalence verification by default before writing — `--require-cert`
   is now simply the default, there is no `--no-cert`, no `--force`, no
   `--skip-verify`. The write is atomic and touches only the proposed spans.
6. **Re-verifying the spent proposal** fails: the file now carries the
   certificate's `after` fingerprint (compare line for line in the
   transcript), so the proposal has self-invalidated. A proposal approves
   exactly one application of exactly one diff, exactly once.

## Why this proves behavior is preserved — the skeptic's tour

**"The tool checking its own work is circular."** Two answers. First, the
verifier recomputes everything from the original file bytes and the proposal
alone; the proposal's `why_safe` prose and `cpg_facts` are never inputs to
verification. Second, the check is two independent layers that fail on
different lies: the *structural* layer recomputes the before and after code
property graphs (statement-level control flow + conservative may-reach
def-use) and demands they differ by **exactly the remapping the rule
licenses** — declared per rule, in writing, in ADR-0007 — and by nothing
else; the *replay* layer re-runs the recognizer+emitter and demands every
edit byte-match. Graphs catch a wrong transformation; replay catches
sub-statement corruption a whole-statement graph would miss.

**"Where's the actual proof?"** Split where the decidability boundary is.
Per rule, once: the schema obligation — why *any* application matching this
recognizer preserves behavior — stated formally and, where it reduces to a
finite claim about a small semantic model, machine-checked as a Kani harness
(`k3c_loop_fold_schema` in the transcript). Per application: a decidable
structural check that this concrete before/after pair really is an instance
of that schema and nothing more. The certificate is the conjunction.

**"What about the unchanged code?"** Certified too: every unaffected
function's CPG must be canonically identical before and after
(`1 unaffected re-verified` in the transcript), and the CST is lossless
(ADR-0001), so bytes outside the edited spans are untouched by construction.

**"So it proves equivalence in general?"** No, and it never claims to —
general program equivalence is undecidable (Rice's theorem), which is exactly
why the design is rule-wise. The certificate proves this application is an
instance of a narrow, versioned schema whose preservation argument is stated
and checked, **under the assumptions printed inside the certificate itself**:
conservative may-reach data dependencies, no aliasing analysis, statement
grain (with replay covering sub-statement bytes), and bounded-model fidelity
for the Kani-checked obligations. A certificate that hides its assumptions is
marketing; these ship in the document, and the verifier re-states them on
every run.

## Files

- `fixture/orders.rs` — the committed fixture (never modified in place)
- `run.sh` — the demo; copies the fixture to `workdir/` and runs the loop
- `transcript.txt` — a captured real run of `run.sh`
- `workdir/` — scratch output of the last run (regenerated every run)
