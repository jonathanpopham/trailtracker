#!/usr/bin/env bash
# Portable local mirror of the CI correctness gate. Run from the repo root.
# Deployment hardware is still unknown, so the gate is CI-system-agnostic: this
# script is the single entrypoint, and CI just calls the same steps.
set -euo pipefail

cd "$(dirname "$0")/.."

echo "==> format check"
cargo fmt --all -- --check

echo "==> clippy (deny warnings)"
cargo clippy --workspace --all-targets -- -D warnings

echo "==> build release"
cargo build --release

echo "==> tests"
cargo test --workspace

echo "==> verification gate"
cargo run --release -p trailtracker-eval --bin verify -- \
  --root . \
  --binary target/release/trailtracker \
  --out verification-report.json \
  --cases "${VERIFY_CASES:-20000}"

echo "==> corpus regression gate (golden snapshots)"
cargo run --release -p trailtracker-eval --bin regress -- --root .

echo "==> ontology view golden gate (domains/archetypes/layers/hierarchy)"
bash benchmarks/golden_check.sh

echo "==> report:"
cat verification-report.json
echo

# Optional: formal proof if Kani is installed locally.
if command -v cargo-kani >/dev/null 2>&1; then
  echo "==> formal verification (kani)"
  cargo kani -p trailtracker-eval
else
  echo "==> kani not installed; skipping formal proof (install: cargo install --locked kani-verifier && cargo kani setup)"
fi

echo "==> verification gate complete"
