#!/usr/bin/env bash
# The local and hosted formal gate use the same verifier and safety checks.
set -euo pipefail
cd "$(dirname "$0")/.."

version=$(cargo kani --version)
if [[ "${version%%$'\n'*}" != 'Kani Rust Verifier 0.68.0 (cargo plugin)' ]]; then
  echo "Expected Kani 0.68.0; got: $version" >&2
  exit 1
fi

# No safety/unwinding checks are disabled. Timeouts fail the gate.
cargo kani -p trailtracker-eval --output-format terse \
  -Z unstable-options --harness-timeout 300
python3 scripts/check_verification_mutations.py kani
