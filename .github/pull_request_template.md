# Summary

<!-- What does this change do, and why? -->

## Analyzer impact

<!-- Does this change what TrailTracker emits (nodes, edges, resolution)? -->

- [ ] No change to analyzer output (pure refactor / docs / tooling)
- [ ] Changes analyzer output — goldens updated and reviewed (see below)

## Regression gate

The corpus regression gate (`regress`) diffs every vendored known-codebase
crate against its committed golden. It runs in CI and must be green.

- [ ] `bash scripts/verify.sh` passes locally (fmt · clippy · test · verify · **regress**)
- [ ] If analyzer output changed: ran `cargo run -p trailtracker-eval --bin regress -- --update`,
      **reviewed the golden diff**, and committed `eval/golden/*.jsonl` in this PR
- [ ] If behavior changed: added/extended a corpus fixture under `eval/corpus/`
      that exercises it

## Invariants (must never regress)

- [ ] Lossless round-trip holds (100% files reconstruct source)
- [ ] Output is deterministic (byte-identical across runs)
- [ ] No new external dependencies in the runtime crate (`std`-only, airgap-safe)

## Reviewer notes

<!-- Anything the reviewer should pay special attention to. -->
