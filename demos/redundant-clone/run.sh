#!/usr/bin/env bash
# demos/redundant-clone — the verified redundant-.clone() elimination loop.
#
# propose (redundant clone removed, read-later decoy refused) -> certificate ->
# independent verify -> apply (certified BY DEFAULT) -> re-verify self-invalidated.
#
# Run from anywhere:   bash demos/redundant-clone/run.sh
# Capture transcript:  bash demos/redundant-clone/run.sh > transcript.txt 2>&1
# Uses TT_BIN if set, else target/release/trailtracker at the repo root.
set -u
cd "$(dirname "$0")"
ROOT="$(cd ../.. && pwd)"
BIN="${TT_BIN:-$ROOT/target/release/trailtracker}"
if [ ! -x "$BIN" ]; then
  echo "trailtracker binary not found at $BIN — build it first: cargo build --release" >&2
  exit 3
fi

rm -rf workdir
mkdir workdir
cp fixture/config.rs workdir/config.rs

tt() {
  printf '\n$ trailtracker %s\n' "$*"
  "$BIN" "$@"
  local rc=$?
  printf '(exit %d)\n' "$rc"
  return $rc
}

echo "== redundant-clone-elim, end to end =="
echo "binary : $("$BIN" version)"
echo "fixture: workdir/config.rs (copied from fixture/config.rs)"

echo
echo "-- 1. propose: analyze, emit the diff + a hash-bound proposal + cert ----"
echo "   build() has a proven-redundant clone (raw dead after the copy);"
echo "   merge() clones base but READS it after — reported as a rejection."
tt rewrite propose redundant-clone-elim config.rs workdir -o workdir/proposal.json || exit 1

echo
echo "-- 2. the certificate: the last-use proof, machine-checkable -----------"
printf '\n$ python3 -m json.tool workdir/proposal.cert.json\n'
python3 -m json.tool workdir/proposal.cert.json 2>/dev/null || cat workdir/proposal.cert.json

echo
echo "-- 3. verify: the INDEPENDENT check ------------------------------------"
echo "   reads only the original file + the proposal, recomputes both CPGs,"
echo "   re-derives the last-use proof, replays the licensed emission."
tt rewrite verify --proposal workdir/proposal.json || exit 1

echo
echo "-- 4. apply: the only writing path, certified BY DEFAULT ----------------"
tt rewrite apply --proposal workdir/proposal.json || exit 1
printf '\n$ sed -n "10,12p" workdir/config.rs\n'
sed -n '10,12p' workdir/config.rs

echo
echo "-- 5. re-verify: the proposal has self-invalidated ----------------------"
tt rewrite verify --proposal workdir/proposal.json
if [ $? -ne 4 ]; then echo "DEMO FAILED: spent proposal was not refused with exit 4" >&2; exit 1; fi

echo
echo "== done: proposed, certified, independently verified, decoy refused, =="
echo "==       applied under the default certificate gate, self-invalidated =="
