#!/usr/bin/env python3
"""Tier-1 eval gate (deterministic, no LLM): does TrailTracker's own extraction
match the hand-labeled ground truth? Derives an operation-set for each labeled
flow directly from `trailtracker graph` and scores it against
ground_truth/<Flow>.json. Fails (exit 1) if any flow's F1 < THRESHOLD.

This is the CI regression gate on extraction quality — the precondition for the
artifact being trustworthy enough to help an agent.

Usage: tier1_gate.py [--corpus benchmarks/fixtures/coral] [--threshold 0.95]
"""
from __future__ import annotations
import argparse, json, subprocess, sys
from pathlib import Path

TT = Path(__file__).resolve().parent.parent
BIN = TT / "target" / "release" / "trailtracker"
GT_DIR = TT / "benchmarks" / "ground_truth"


def load_graph(corpus: Path) -> tuple[dict, list]:
    out = subprocess.run([str(BIN), "graph", str(corpus)], capture_output=True, text=True).stdout
    nodes, edges = {}, []
    for line in out.splitlines():
        if not line.strip():
            continue
        r = json.loads(line)
        (nodes.__setitem__(r["id"], r) if r["record"] == "node" else edges.append(r))
    return nodes, edges


def jprop(node: dict, key: str):
    v = node["properties"].get(key)
    if v is None:
        return None
    try:
        return json.loads(v) if isinstance(v, str) and v[:1] in "[{" else v
    except json.JSONDecodeError:
        return v


def opset_for(flow: str, nodes: dict, edges: list) -> dict:
    """Derive the operation-set for a flow from the graph (deterministic)."""
    els = [n for n in nodes.values()
           if n["properties"].get("type_kind") == "flow_element"
           and n["properties"].get("flow") == flow]
    elids = {n["id"] for n in els}
    # element -> its touched sobject (via USES_TYPE)
    touch = {}
    for e in edges:
        if e["kind"] == "USES_TYPE" and e["from"] in elids and e["to"].startswith("sobject::"):
            touch[e["from"]] = e["to"].split("::", 1)[1]
    objects, mutations, queries, calls = set(), [], [], set()
    for n in els:
        k = n["properties"].get("element_kind", "")
        obj = touch.get(n["id"])
        if obj:
            objects.add(obj)
        if k in ("recordCreates", "recordUpdates", "recordDeletes"):
            op = {"recordCreates": "create", "recordUpdates": "update",
                  "recordDeletes": "delete"}[k]
            fields = [ia.get("field") for ia in (jprop(n, "inputAssignments") or [])
                      if ia.get("field")]
            mutations.append({"op": op, "object": obj or "?", "fields": fields})
        if k == "recordLookups":
            qf = jprop(n, "queriedFields") or []
            queries.append({"object": obj or "?", "fields": list(qf)})
        if k in ("actionCalls", "subflows"):
            for e in edges:
                if e["kind"] == "CALLS" and e["from"] == n["id"]:
                    calls.add(nodes.get(e["to"], {}).get("name", e["to"]))
    binds = [n for n in nodes.values()
             if str(n["properties"].get("type_kind", "")).startswith("flow_")
             and n["properties"].get("flow") == flow]
    inputs = [n["name"] for n in binds if n["properties"].get("isInput") == "true"]
    outputs = [n["name"] for n in binds if n["properties"].get("isOutput") == "true"]
    return {"objects": sorted(objects), "mutations": mutations, "queries": queries,
            "calls": sorted(calls), "inputs": inputs, "outputs": outputs}


def atoms(op: dict) -> set:
    a = set()
    for o in op.get("objects") or []:
        a.add(f"object:{o}")
    for m in op.get("mutations") or []:
        a.add(f"mut:{m.get('op')}:{m.get('object')}")
        for f in m.get("fields") or []:
            a.add(f"write:{m.get('object')}.{f}")
    for q in op.get("queries") or []:
        a.add(f"query:{q.get('object')}")
        for f in q.get("fields") or []:
            a.add(f"read:{q.get('object')}.{f}")
    for c in op.get("calls") or []:
        a.add(f"call:{c}")
    for i in op.get("inputs") or []:
        a.add(f"input:{i}")
    for o in op.get("outputs") or []:
        a.add(f"output:{o}")
    return a


def f1(gt: set, got: set) -> tuple[float, float, float]:
    tp = len(gt & got)
    p = tp / len(got) if got else 0.0
    r = tp / len(gt) if gt else 0.0
    return (2 * p * r / (p + r) if (p + r) else 0.0), p, r


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", default=str(TT / "benchmarks" / "fixtures" / "coral"))
    ap.add_argument("--threshold", type=float, default=0.95)
    args = ap.parse_args()
    nodes, edges = load_graph(Path(args.corpus))
    failed = False
    for gt_file in sorted(GT_DIR.glob("*.json")):
        gt = json.loads(gt_file.read_text())
        if "flow" not in gt:
            # ground_truth/ is shared across gates; domain-clustering GTs
            # (eshop_domains.json, ...) have no "flow" key and are scored by
            # their own harness, not this one.
            print(f"[SKIP] {gt_file.name}: no 'flow' key (not a flow ground truth)")
            continue
        flow = gt["flow"]
        fixture = Path(args.corpus) / "flows" / f"{flow}.flow-meta.xml"
        if not fixture.exists():
            # A GT without its fixture cannot be scored here (e.g.
            # Mega_Intake_Orchestrator: the synthetic flow of the 2026-07-04
            # decisive eval was never added to the corpus; only its GT and
            # result records were kept). A fixture that IS present but
            # extracts nothing still fails honestly below.
            print(f"[SKIP] {flow}: fixture {fixture.name} not in corpus")
            continue
        got = opset_for(flow, nodes, edges)
        score, p, r = f1(atoms(gt), atoms(got))
        ok = score >= args.threshold
        failed |= not ok
        print(f"[{'PASS' if ok else 'FAIL'}] {flow}: F1={score:.3f} (p={p:.3f} r={r:.3f})")
        if not ok:
            print(f"   missed:       {sorted(atoms(gt) - atoms(got))}")
            print(f"   hallucinated: {sorted(atoms(got) - atoms(gt))}")
    print(f"\ntier-1 extraction gate: {'FAIL' if failed else 'PASS'} (threshold {args.threshold})")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
