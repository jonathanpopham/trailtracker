#!/usr/bin/env bash
# Golden regression gate for the ONTOLOGY VIEWS (derived extractors).
#
# The base-graph goldens (eval/golden/*.jsonl, checked by the `regress`
# binary) freeze the canonical graph. This gate freezes the four ontology
# views layered on top of it — domains, archetypes, layers, hierarchy — run
# over the same self-contained eval/corpus fixtures. Every extractor is a
# pure, deterministic function of the base graph (byte-identical JSONL for
# the same input by design), so ANY diff against a frozen golden is a real
# semantic change in an extractor or in the pipeline beneath it, and this
# script exits non-zero.
#
# Usage:
#   bash benchmarks/golden_check.sh              # compare (CI / verify.sh)
#   UPDATE_GOLDENS=1 bash benchmarks/golden_check.sh   # re-bless after an
#       intentional change; then review `git diff benchmarks/ontology_goldens/`
#       before committing.
#
# Env:
#   BINARY  path to the trailtracker binary (default: target/release/trailtracker)
set -euo pipefail

cd "$(dirname "$0")/.."

BINARY="${BINARY:-target/release/trailtracker}"
GOLDEN_DIR="benchmarks/ontology_goldens"
CORPUS_DIR="eval/corpus"

VIEWS=(domains archetypes layers hierarchy)
FIXTURES=(apexorg calc sflinked sforg sfperms shapes)

if [ ! -x "$BINARY" ]; then
  echo "golden_check: binary not found at $BINARY (run \`cargo build --release\` first)" >&2
  exit 1
fi

mkdir -p "$GOLDEN_DIR"

fail=0
checked=0
for view in "${VIEWS[@]}"; do
  for fixture in "${FIXTURES[@]}"; do
    golden="$GOLDEN_DIR/${fixture}__${view}.jsonl"
    actual="$("$BINARY" extract "$view" "$CORPUS_DIR/$fixture")"

    if [ "${UPDATE_GOLDENS:-}" = "1" ]; then
      printf '%s' "$actual" > "$golden"
      echo "WROTE     ${fixture}__${view}"
      continue
    fi

    if [ ! -f "$golden" ]; then
      echo "NO-GOLDEN ${fixture}__${view}  (run UPDATE_GOLDENS=1 $0, review, commit)"
      fail=1
      continue
    fi

    if printf '%s' "$actual" | diff -u "$golden" - > /dev/null 2>&1; then
      echo "PASS      ${fixture}__${view}"
      checked=$((checked + 1))
    else
      echo "REGRESSED ${fixture}__${view}"
      printf '%s' "$actual" | diff -u "$golden" - | head -40 || true
      fail=1
    fi
  done
done

if [ "${UPDATE_GOLDENS:-}" = "1" ]; then
  echo "ontology goldens re-blessed — review: git diff $GOLDEN_DIR/"
  exit 0
fi

if [ "$fail" -ne 0 ]; then
  echo "ontology golden gate FAILED — a derived view drifted from its frozen golden." >&2
  echo "If the change is intentional: UPDATE_GOLDENS=1 bash benchmarks/golden_check.sh, review the diff, commit." >&2
  exit 1
fi

echo "ontology golden gate PASSED ($checked view goldens byte-identical)"
