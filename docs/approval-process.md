# Build & Approval Process

TrailTracker is experimental analysis tooling. The `trailtracker` CLI is the
shipped artifact; changes must pass the regression checks before merge.
Passing those checks is not a certification of semantic correctness.

## The flow

```
feature branch ──► open PR ──► CI gate (must be green) ──► owner review ──► merge to main
                                     │
                                     └── fmt · clippy · test · verify · regress · (kani)
```

1. **Branch.** No direct pushes to `main`. Work happens on a feature branch.
2. **Open a PR.** The PR template (`.github/pull_request_template.md`) walks
   through the analyzer-impact and regression checklist.
3. **CI gate runs** (`.github/workflows/ci.yml`, job `compile · test · eval`).
   Every step is blocking:
   - `cargo fmt --all -- --check` — formatting
   - `cargo clippy --workspace --all-targets -- -D warnings` — lints as errors
   - `cargo build --release` — compiles
   - `cargo test --workspace` — unit + integration tests
   - **verify** — self-analysis regression + property/fuzz (20k cases) +
     hash-attestable report
   - **regress** — golden-snapshot regression over the known-codebase corpus
   - **kani** (separate job) — bounded formal proof of losslessness
     (non-blocking until the toolchain is pinned)
4. **Owner review.** `CODEOWNERS` requires review from the code owner. Changes
   under `eval/golden/` (the regression contract) always require explicit review
   of the diff.
5. **Merge.** Only when CI is green and review is approved.

## The regression eval (the heart of the gate)

`eval/corpus/` holds vendored, self-contained Rust crates — *known codebases*
that never change. `eval/golden/<name>.jsonl` is the committed, expected graph
output for each. Because TrailTracker guarantees **deterministic, byte-identical**
output, any diff between a fresh run and the golden is a *real semantic change*
in the analyzer.

The `regress` binary loops every corpus crate, analyzes it, and diffs against its
golden:

```bash
# Check (CI does this; exits non-zero on any regression)
cargo run -p trailtracker-eval --bin regress -- --root .

# Bless intentional changes, then review + commit the updated goldens
cargo run -p trailtracker-eval --bin regress -- --update
git add eval/golden
```

### Adding a corpus case

1. Drop a self-contained crate at `eval/corpus/<name>/` (a `Cargo.toml` +
   `src/`). It is analyzed as *source text* and never compiled, so it may
   reference unvendored deps to exercise external-dependency detection.
2. `cargo run -p trailtracker-eval --bin regress -- --update` to generate
   `eval/golden/<name>.jsonl`.
3. Commit both the crate and its golden.

## Local mirror

`scripts/verify.sh` runs the exact CI gate locally. Run it before every push:

```bash
bash scripts/verify.sh
```

## Required branch-protection settings (configure once on GitHub)

On `main` → Settings → Branches → Branch protection rule:

- [x] Require a pull request before merging
- [x] Require approvals (≥ 1) and require review from Code Owners
- [x] Require status checks to pass before merging → **`compile · test · eval`**
- [x] Require branches to be up to date before merging
- [x] Do not allow bypassing the above settings
