#!/usr/bin/env python3
"""Salesforce-rebuild eval runner (Tier 2, local via claude -p).

For a flow, run two isolated arms — baseline (raw flow XML) and treatment (raw
XML + `trailtracker rebuild-brief`) — invoking the same model, then grade each
arm's emitted operation-set against a hand-labeled ground truth (recall /
precision / F1) and report efficiency (num_turns, cost).

Usage: runner.py <Flow_Name> <corpus_dir> [--model claude-opus-4-8]
"""
from __future__ import annotations
import json, os, re, subprocess, sys, tempfile, shutil, argparse
from pathlib import Path

TT = Path(__file__).resolve().parent.parent
BIN = TT / "target" / "release" / "trailtracker"
PROMPT = (TT / "benchmarks" / "arm_prompt.txt").read_text()


def atoms(op: dict) -> set[str]:
    """Normalize an operation-set (ground truth OR arm output) to comparable atoms."""
    a: set[str] = set()
    for o in op.get("objects") or []:
        a.add(f"object:{o}")
    for m in op.get("mutations") or []:
        obj = m.get("object", "?")
        a.add(f"mut:{m.get('op','?')}:{obj}")
        for f in m.get("fields") or []:
            a.add(f"write:{obj}.{f}")
    for q in op.get("queries") or []:
        obj = q.get("object", "?")
        a.add(f"query:{obj}")
        for f in q.get("fields") or []:
            a.add(f"read:{obj}.{f}")
    for c in op.get("calls") or []:
        a.add(f"call:{c}")
    for i in op.get("inputs") or []:
        a.add(f"input:{i}")
    for o in op.get("outputs") or []:
        a.add(f"output:{o}")
    return a


def score(gt: set[str], got: set[str]) -> dict:
    tp = len(gt & got)
    prec = tp / len(got) if got else 0.0
    rec = tp / len(gt) if gt else 0.0
    f1 = 2 * prec * rec / (prec + rec) if (prec + rec) else 0.0
    return {"precision": round(prec, 3), "recall": round(rec, 3), "f1": round(f1, 3),
            "tp": tp, "predicted": len(got), "gold": len(gt),
            "missed": sorted(gt - got), "hallucinated": sorted(got - gt)}


def flow_file(corpus: Path, flow: str) -> Path:
    hits = list(corpus.rglob(f"{flow}.flow-meta.xml"))
    if not hits:
        sys.exit(f"flow {flow} not found under {corpus}")
    return hits[0]


def run_arm(name: str, workspace: Path, model: str) -> dict:
    r = subprocess.run(
        ["claude", "-p", PROMPT, "--output-format", "json", "--model", model],
        cwd=workspace, capture_output=True, text=True, timeout=600,
    )
    try:
        out = json.loads(r.stdout)
    except json.JSONDecodeError:
        return {"error": "bad json", "stdout": r.stdout[:400], "stderr": r.stderr[:400]}
    text = out.get("result", "")
    m = re.search(r"<OPERATIONS>\s*(\{.*?\})\s*</OPERATIONS>", text, re.S)
    ops = {}
    if m:
        try:
            ops = json.loads(m.group(1))
        except json.JSONDecodeError:
            ops = {"_parse_error": True}
    return {"arm": name, "num_turns": out.get("num_turns"),
            "cost_usd": round(out.get("total_cost_usd", 0), 3), "ops": ops,
            "found_operations_block": bool(m)}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("flow")
    ap.add_argument("corpus")
    ap.add_argument("--model", default="claude-opus-4-8")
    args = ap.parse_args()
    corpus = Path(args.corpus).resolve()

    gt = json.loads((TT / "benchmarks" / "ground_truth" / f"{args.flow}.json").read_text())
    gt_atoms = atoms(gt)
    src = flow_file(corpus, args.flow)
    brief = subprocess.run([str(BIN), "rebuild-brief", args.flow, str(corpus)],
                           capture_output=True, text=True).stdout

    results = []
    for arm, extra in (("baseline", False), ("treatment", True)):
        ws = Path(tempfile.mkdtemp(prefix=f"eval-{arm}-"))
        shutil.copy(src, ws / src.name)
        if extra:
            (ws / "REBUILD_BRIEF.md").write_text(brief)
        res = run_arm(arm, ws, args.model)
        if "ops" in res:
            res["score"] = score(gt_atoms, atoms(res["ops"]))
        results.append(res)
        shutil.rmtree(ws, ignore_errors=True)

    print(f"\n=== EVAL: {args.flow}  (model {args.model}) ===")
    print(f"ground-truth atoms: {len(gt_atoms)}")
    for r in results:
        if "score" not in r:
            print(f"\n[{r.get('arm','?')}] ERROR: {r}")
            continue
        s = r["score"]
        print(f"\n[{r['arm']}]  turns={r['num_turns']}  cost=${r['cost_usd']}  "
              f"ops_block={r['found_operations_block']}")
        print(f"   F1={s['f1']}  precision={s['precision']}  recall={s['recall']}  "
              f"(tp {s['tp']}/{s['gold']}, predicted {s['predicted']})")
        if s["missed"]:
            print(f"   missed:       {s['missed']}")
        if s["hallucinated"]:
            print(f"   hallucinated: {s['hallucinated']}")
    if len(results) == 2 and all("score" in r for r in results):
        b, t = results[0]["score"], results[1]["score"]
        df1 = round(t["f1"] - b["f1"], 3)
        turns_ratio = (results[1]["num_turns"] / results[0]["num_turns"]
                       if results[0]["num_turns"] else None)
        print(f"\n=== UPLIFT ===  ΔF1 = {df1:+}   turns treatment/baseline = "
              f"{round(turns_ratio,2) if turns_ratio else '?'}")
        json.dump({"flow": args.flow, "baseline": results[0], "treatment": results[1],
                   "delta_f1": df1},
                  open(TT / "benchmarks" / f"result-{args.flow}.json", "w"), indent=1)


if __name__ == "__main__":
    main()
