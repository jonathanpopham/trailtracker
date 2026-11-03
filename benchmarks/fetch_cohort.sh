#!/usr/bin/env bash
# Fetch the ontology eval cohort at pinned commits — reproducible, shallow.
# Usage: COHORT_DIR=/path/to/cohort ./benchmarks/fetch_cohort.sh
# Default COHORT_DIR: ./benchmarks/.cohort (gitignored).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
COHORT_DIR="${COHORT_DIR:-$here/.cohort}"
mkdir -p "$COHORT_DIR"

# stdlib-only manifest read (python is already a benchmark dependency).
python3 - "$here/cohort.json" <<'PY' | while IFS=$'\t' read -r name url sha; do
import json, sys
for r in json.load(open(sys.argv[1]))["cohort"]:
    print(f"{r['name']}\t{r['url']}\t{r['sha']}")
PY
  dir="$COHORT_DIR/$name"
  if [ -f "$dir/.cohort_sha" ] && [ "$(cat "$dir/.cohort_sha")" = "$sha" ]; then
    echo "  $name @ ${sha:0:12} (cached)"; continue
  fi
  echo "  fetching $name @ ${sha:0:12} ..."
  rm -rf "$dir"; git init -q "$dir"
  git -C "$dir" remote add origin "$url"
  # GitHub allows fetching a specific commit; --depth 1 keeps it lean.
  git -C "$dir" fetch -q --depth 1 origin "$sha"
  git -C "$dir" checkout -q FETCH_HEAD
  echo "$sha" > "$dir/.cohort_sha"
done
echo "cohort ready in $COHORT_DIR"
