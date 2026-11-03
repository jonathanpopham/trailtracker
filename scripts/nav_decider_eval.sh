#!/usr/bin/env bash
# K1 decider eval (ADR-0004): context efficiency of `nav pack` versus a
# grep-driven agent on a real question against a real large codebase.
#
# Question: "where is playback session state managed and what breaks if I
# change it?" against the jellyfin server (~2,100 C# files).
#
# Measures, honestly:
#   (a) chars an agent would load reading WHOLE candidate files found by grep
#       (naive: every file mentioning playback+session; disciplined: the top
#       10 by match count),
#   (b) the nav-pack response at --budget 20000, plus the chars of the
#       file:line spans its read-plan actually asks the agent to read.
#
# Usage: JELLYFIN=/path/to/jellyfin bash scripts/nav_decider_eval.sh
# Results doc: docs/evals/nav-context-efficiency.md
set -euo pipefail

cd "$(dirname "$0")/.."
BINARY="${BINARY:-target/release/trailtracker}"
JELLYFIN="${JELLYFIN:?set JELLYFIN to the jellyfin checkout}"
QUERY="where is playback session state managed"
BUDGET=20000
OUT="$(mktemp -d)"
trap 'rm -rf "$OUT"' EXIT

echo "== corpus =="
find "$JELLYFIN" -name '*.cs' | wc -l | xargs echo "  .cs files:"

echo "== (a) grep baseline =="
( cd "$JELLYFIN" && grep -rli --include='*.cs' "playback" . \
    | xargs grep -li "session" ) > "$OUT/naive.txt"
NAIVE_FILES=$(wc -l < "$OUT/naive.txt" | tr -d ' ')
NAIVE_CHARS=$(cd "$JELLYFIN" && xargs wc -c < "$OUT/naive.txt" | tail -1 | awk '{print $1}')
echo "  naive (playback AND session, whole files): $NAIVE_FILES files, $NAIVE_CHARS chars"

( cd "$JELLYFIN" && while read -r f; do
    printf '%s %s %s\n' "$(grep -cio playback "$f")" "$(wc -c < "$f")" "$f"
  done < "$OUT/naive.txt" | sort -rn | head -10 ) > "$OUT/top10.txt"
TOP10_CHARS=$(awk '{s+=$2} END {print s}' "$OUT/top10.txt")
echo "  disciplined (top-10 by match count, whole files): $TOP10_CHARS chars"

echo "== (b) nav pack =="
"$BINARY" nav pack "$QUERY" "$JELLYFIN" --budget "$BUDGET" --json > "$OUT/pack.json"
PACK_CHARS=$(wc -c < "$OUT/pack.json" | tr -d ' ')
echo "  pack response: $PACK_CHARS chars (budget $BUDGET)"

python3 - "$OUT/pack.json" "$JELLYFIN" <<'EOF'
import json, os, sys
pack = json.load(open(sys.argv[1])); root = sys.argv[2]
def span_chars(entries):
    total = 0
    for r in entries:
        p = os.path.join(root, r["path"])
        lines = open(p, encoding="utf-8", errors="replace").read().splitlines(keepends=True)
        total += len("".join(lines[r["start_line"] - 1 : r.get("end_line", len(lines))]))
    return total
plan = pack["read_plan"]
print("  read-plan spans: %d entries, %d chars if ALL read, %d chars for the top 10"
      % (len(plan), span_chars(plan), span_chars(plan[:10])))
print("  budget block:", json.dumps(pack["budget"]))
# Answer-containment probes (the hand-verified ground truth):
text = json.dumps(pack)
for probe in ["Emby.Server.Implementations/Session/SessionManager.cs",
              "OnPlaybackStart", "OnPlaybackProgress",
              "PlaystateController", "SessionInfoWebSocketListener",
              "PlaybackProgressInfo", "SessionInfo.cs", "PlayState"]:
    print("  contains %-55s %s" % (probe, probe in text))
EOF

echo "== ratios =="
python3 -c "
naive, top10, pack = $NAIVE_CHARS, $TOP10_CHARS, $PACK_CHARS
print('  pack vs naive grep:        %.1fx' % (naive / pack))
print('  pack vs disciplined grep:  %.1fx' % (top10 / pack))
"
echo "(interpretation + hand verification: docs/evals/nav-context-efficiency.md)"
