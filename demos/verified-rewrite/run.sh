#!/usr/bin/env bash
# demos/verified-rewrite — the end-to-end Verified Refactoring.
#
# propose -> certificate -> independent verify -> tamper refused ->
# apply (certified BY DEFAULT since K3d) -> re-verify shows the file moved.
#
# Run from anywhere:   bash demos/verified-rewrite/run.sh
# Capture transcript:  bash demos/verified-rewrite/run.sh > transcript.txt 2>&1
# Uses TT_BIN if set, else target/release/trailtracker at the repo root.
set -u
cd "$(dirname "$0")"
ROOT="$(cd ../.. && pwd)"
BIN="${TT_BIN:-$ROOT/target/release/trailtracker}"
if [ ! -x "$BIN" ]; then
  echo "trailtracker binary not found at $BIN — build it first: cargo build --release" >&2
  exit 3
fi

# Fresh scratch copy: the committed fixture is never modified.
rm -rf workdir
mkdir workdir
cp fixture/orders.rs workdir/orders.rs

# Echo each command like a shell session, then run it and report the exit code.
tt() {
  printf '\n$ trailtracker %s\n' "$*"
  "$BIN" "$@"
  local rc=$?
  printf '(exit %d)\n' "$rc"
  return $rc
}

echo "== verified rewrite, end to end =="
echo "binary : $("$BIN" version)"
echo "fixture: workdir/orders.rs (copied from fixture/orders.rs)"

echo
echo "-- 1. propose: analyze, emit the diff + a hash-bound proposal ----------"
echo "   propose NEVER writes source; -o also writes the equivalence"
echo "   certificate beside the proposal (proposal.cert.json)."
tt rewrite propose loop-to-iterator orders.rs workdir -o workdir/proposal.json || exit 1

echo
echo "-- 2. the certificate ---------------------------------------------------"
echo "   rule id + version, the schema-obligation reference, before/after file"
echo "   fingerprints and CPG hashes, the licensed remapping checks, and the"
echo "   stated assumptions. Everything below is recomputable from the source"
echo "   file and the proposal alone."
printf '\n$ python3 -m json.tool workdir/proposal.cert.json\n'
python3 -m json.tool workdir/proposal.cert.json 2>/dev/null || cat workdir/proposal.cert.json

echo
echo "-- 3. verify: the INDEPENDENT check ------------------------------------"
echo "   reads only the original file + the proposal, trusts nothing cached"
echo "   (not even the certificate propose wrote), recomputes the before/after"
echo "   CPGs, re-derives the licensed remapping, replays the emission."
tt rewrite verify --proposal workdir/proposal.json || exit 1

echo
echo "-- 4. tamper with the proposal: verification must refuse ---------------"
echo "   one character of drift in the approved bytes (o.id -> o.id + 1):"
printf '\n$ sed -i.orig "s/Some(o.id)/Some(o.id + 1)/" workdir/proposal.json\n'
sed -i.orig 's/Some(o\.id)/Some(o.id + 1)/' workdir/proposal.json
tt rewrite verify --proposal workdir/proposal.json
if [ $? -ne 4 ]; then echo "DEMO FAILED: tampered proposal was not refused with exit 4" >&2; exit 1; fi
printf '\n$ mv workdir/proposal.json.orig workdir/proposal.json   # restore the honest proposal\n'
mv workdir/proposal.json.orig workdir/proposal.json

echo
echo "-- 5. apply: the only writing path, certified BY DEFAULT ----------------"
echo "   since K3d, apply always re-runs the full equivalence verification"
echo "   before writing (--require-cert is the default; there is no --no-cert)."
tt rewrite apply --proposal workdir/proposal.json || exit 1

printf '\n$ cat workdir/orders.rs\n'
cat workdir/orders.rs

echo
echo "-- 6. re-verify: the proposal has self-invalidated ----------------------"
echo "   the file now carries the certificate's AFTER fingerprint, so the"
echo "   spent proposal no longer matches — a proposal approves exactly one"
echo "   application, exactly once."
tt rewrite verify --proposal workdir/proposal.json
if [ $? -ne 4 ]; then echo "DEMO FAILED: spent proposal was not refused with exit 4" >&2; exit 1; fi

echo
echo "== done: proposed, certified, independently verified, tamper refused, =="
echo "==       applied under the default certificate gate, self-invalidated =="
