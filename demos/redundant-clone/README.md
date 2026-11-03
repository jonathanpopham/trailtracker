# Verified redundant-`.clone()` elimination, end to end

The first *value-delivering* rule in TrailTracker's verified-rewrite catalog:
removing a `.clone()` that the CPG's data-flow proves is unnecessary. A clone
is redundant when the cloned binding is never read again on any path after the
call — the original can simply be *moved* into the position the copy occupied.
This demo runs the complete loop on a real file and shows every claim being
checked by machinery that does not trust the claimant.

```sh
cargo build --release
bash demos/redundant-clone/run.sh
```

`transcript.txt` is a captured run of exactly that command — every hash in it
was produced by the built binary, and because proposals and certificates are
timestamp-free and deterministic, your run reproduces the same documents and
hashes from the same binary and fixture.

## The fixture

`fixture/config.rs` has three functions:

- **`build`** clones `raw` into `owned` and never touches `raw` again — a
  `DATA_DEP`-proven last use. The clone is redundant; the rule removes it.
- **`merge`** clones `base` but then reads `base.len()` — the clone is **not**
  the last use. The rule refuses the site with the machine-readable reason
  `cloned_value_read_later`, showing the exact `DATA_DEP` edge that blocks it.
- **`render`** is untouched, giving the certificate an unaffected function to
  re-verify.

## Why it is safe (the soundness argument)

The proof is the CPG's `DATA_DEP` overlay (ADR-0003), which is **conservative
may-reach** def-use: it records *every* read any execution could perform. The
direction this rule needs is therefore sound. When the graph shows **no reader
of the binding among the statements CFG-reachable after the clone**, no
execution reads it — because an over-approximating analysis can only err by
*inventing* readers, never by *missing* one. Its failure mode is refusing a
valid site (too cautious), never permitting an invalid one. The removal is the
minimal edit: delete the `.clone()` bytes, leaving the binding in place. The
certificate's licensed remapping is **zero graph delta** — the after CPG must
equal the before CPG under the 1:1 statement mapping — plus the re-derived
last-use precondition. See ADR-0007,
`#redundant-clone-elim-v1--licensed-remapping`, and the bounded Kani harness
`k3c_clone_elim_schema`.

## The bite

Removing a clone whose value **is** read later is exactly the wrongful rewrite
this rule must never make. Two independent guards catch it: the recognizer
refuses the site up front (`cloned_value_read_later`, shown on `merge` above),
and if a proposal were forged by hand, the certifier re-derives the last-use
proof from the before graph and fails the same way — apply runs that
verification by default and refuses to write.
