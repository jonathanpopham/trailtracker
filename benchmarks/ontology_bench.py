#!/usr/bin/env python3
"""Ontology eval suite: run the extractors across the pinned cohort and score
quality. `--check` turns it into a CI gate (non-zero exit on regression).

The point is dropout — never trust one repo. The thresholds below are permanent
*acceptance criteria*, not fitted numbers: a domain view must not collapse (one
domain swallowing the codebase) or shatter (junk explosion), and the layer view
must not be inert (everything Shared). A change to the extractors that breaks any
cohort repo fails the gate.

A second, SEMANTIC axis (dom3-semantic-benchmark) scores domain clusters against
known-truth decompositions via semantic_alignment.py — the vocabulary-vs-
responsibility failure class has perfect shape and is invisible to the checks
above; alignment macro-F1 against a ground truth catches it. Repos with a file
in GROUND_TRUTH gain the axis; repos without one are unaffected.

  python3 benchmarks/ontology_bench.py            # human report
  python3 benchmarks/ontology_bench.py --check     # CI gate, exit 1 on failure
Env: TT_BIN (trailtracker binary), COHORT_DIR (where the cohort is checked out).
"""
import argparse, json, os, subprocess, sys, time
from pathlib import Path

import semantic_alignment as sa

HERE = Path(__file__).parent
BIN = os.environ.get("TT_BIN", str(HERE.parent / "target/release/trailtracker"))
COHORT_DIR = Path(os.environ.get("COHORT_DIR", HERE / ".cohort"))
COHORT = json.loads((HERE / "cohort.json").read_text())["cohort"]

# Permanent acceptance criteria (not fitted to any repo).
MAX_TOP_SHARE = 0.5      # one domain owning >=50% of symbols == collapse
MIN_DOMAINS = 3
MAX_DOMAINS = 25         # beyond this == shatter
MAX_JUNK = 0             # tiny (<=3 symbol) domains
CORE_LAYERS = {"Presentation", "Application", "Domain", "Infrastructure"}
MIN_CORE_LAYERS = 2      # layer view must place units in >=2 core layers

# Semantic axis: alignment against known-truth decompositions (see
# semantic_alignment.py and domain_semantics_comparison.md). Repos with a
# ground truth get a macro-F1 gate; all other repos are unaffected.
MIN_SEMANTIC_F1 = 0.70


def load_ground_truths():
    """{cohort repo name: gt path} from ground_truth/*.json — TOP LEVEL ONLY.

    A file activates the semantic axis iff its "repo" names a cohort repo and
    it has a "domains" list (other GT flavors, e.g. flow ground truths like
    Create_Booking.json, are ignored). ground_truth/drafts/ is deliberately
    NOT scanned: drafts are machine-derived from the extractor's own clusters
    (gt_bootstrap.py) and gating on them would be circular — the extractor
    grading its own homework. A draft becomes real ground truth only after
    human review moves it up into ground_truth/ (protocol:
    ground_truth/drafts/README.md).
    """
    out = {}
    names = {r["name"] for r in COHORT}
    for p in sorted((HERE / "ground_truth").glob("*.json")):
        try:
            gt = json.loads(p.read_text())
        except (json.JSONDecodeError, OSError):
            continue
        if gt.get("repo") in names and isinstance(gt.get("domains"), list):
            out[gt["repo"]] = p
    return out


GROUND_TRUTH = load_ground_truths()


def run(extractor, repo_dir):
    r = subprocess.run([BIN, "extract", extractor, str(repo_dir)],
                       capture_output=True, text=True, timeout=300)
    nodes, edges = [], []
    for l in r.stdout.splitlines():
        if not l.strip():
            continue
        o = json.loads(l)
        (nodes if o.get("record") == "node" else edges).append(o)
    return nodes, edges


def score(repo):
    repo_dir = COHORT_DIR / repo["name"]
    out = {"repo": repo["name"], "split": repo["split"],
           "tier": repo.get("tier", "gate"), "lang": repo.get("lang", "")}
    # domains — business clusters only. The zero-ungrouped emit adds up to
    # four named infrastructure groups (Build & Tooling / Documentation /
    # Generated / Repo root, kind="infrastructure") as first-class domain
    # nodes; they are deterministic path classifications, not clusterings,
    # so the collapse/shatter/junk thresholds keep judging what they always
    # judged: the business clustering. (Nodes without a `kind` prop — old
    # binaries — count as business.)
    dn, _ = run("domains", repo_dir)
    doms = [n["properties"] for n in dn if "domain" in n.get("properties", {}) and "unit_count" in n["properties"]
            and n["properties"].get("kind", "business") == "business"]
    tot = sum(d["symbol_count"] for d in doms) or 1
    doms.sort(key=lambda d: -d["symbol_count"])
    out["domains"] = {
        "n": len(doms),
        "top_share": round(doms[0]["symbol_count"] / tot, 2) if doms else 0,
        "junk": sum(1 for d in doms if d["symbol_count"] <= 3),
        "top5": [(d["domain"], d.get("label", ""), round(d["symbol_count"] / tot, 2)) for d in doms[:5]],
    }
    # archetypes
    an, _ = run("archetypes", repo_dir)
    arch = {n["properties"]["archetype"]: n["properties"]["count"]
            for n in an if n.get("properties", {}).get("archetype") and "count" in n["properties"]}
    out["archetypes"] = {"classified": sum(v for k, v in arch.items() if k != "Unclassified"),
                         "unclassified": arch.get("Unclassified", 0)}
    # lexicon
    ln, _ = run("lexicon", repo_dir)
    con = sorted([n["properties"] for n in ln if n.get("properties", {}).get("token_class") == "concept"],
                 key=lambda p: -p["count"])
    out["lexicon"] = {"top": [c["token"] for c in con[:8]]}
    # layers — distribution + violations
    yn, ye = run("layers", repo_dir)
    layers = {n["properties"]["layer"]: n["properties"]["unit_count"]
              for n in yn if "layer" in n.get("properties", {}) and "unit_count" in n["properties"]}
    out["layers"] = {"dist": layers,
                     "core": sorted(k for k in layers if k in CORE_LAYERS),
                     "violations": sum(1 for e in ye if e.get("properties", {}).get("violation"))}
    # semantic alignment (only for repos with a ground truth); reuses the
    # domains run — File nodes carry the CONTAINS domain->file assignment
    gt_path = GROUND_TRUTH.get(repo["name"])
    if gt_path and gt_path.is_file():
        gt = json.loads(gt_path.read_text())
        out["semantic"] = sa.score_clusters(sa.clusters_from_nodes(dn), gt)
    return out



def checks(d):
    """Return list of (ok, label) permanent-threshold checks for a repo."""
    out = []
    if "domains" in d:  # shape axis (semantic-only rows, skip it)
        dm, ly = d["domains"], d["layers"]
        out += [
            (dm["top_share"] < MAX_TOP_SHARE, f"domains top_share {int(dm['top_share']*100)}% < {int(MAX_TOP_SHARE*100)}%"),
            (MIN_DOMAINS <= dm["n"] <= MAX_DOMAINS, f"domains n={dm['n']} in [{MIN_DOMAINS},{MAX_DOMAINS}]"),
            (dm["junk"] <= MAX_JUNK, f"domains junk={dm['junk']} <= {MAX_JUNK}"),
            (len(ly["core"]) >= MIN_CORE_LAYERS, f"layers core={ly['core']} (>= {MIN_CORE_LAYERS})"),
        ]
    if "semantic" in d:  # semantic axis (only repos with a ground truth)
        f1 = d["semantic"]["macro_f1"]
        err = d["semantic"].get("error")
        label = f"semantic macro-F1 {f1:.3f} >= {MIN_SEMANTIC_F1:.2f}" + (f" ({err})" if err else "")
        out.append((f1 >= MIN_SEMANTIC_F1, label))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="CI gate: exit 1 if any repo fails a threshold")
    args = ap.parse_args()

    if not COHORT_DIR.is_dir() or not any((COHORT_DIR / r["name"]).is_dir() for r in COHORT):
        print(f"cohort not found in {COHORT_DIR} — run benchmarks/fetch_cohort.sh first", file=sys.stderr)
        return 2

    results = [score(r) for r in COHORT if (COHORT_DIR / r["name"]).is_dir()]
    (HERE / "ontology_bench_results.json").write_text(json.dumps(results, indent=1))

    if args.check:
        gate = [d for d in results if d["tier"] == "gate"]
        explore = [d for d in results if d["tier"] != "gate"]
        failed = 0
        for d in gate:
            bad = [lbl for ok, lbl in checks(d) if not ok]
            print(f"[{'PASS' if not bad else 'FAIL'}] {d['repo']:<18}{d['lang']:<11}" + ("" if not bad else "-> " + "; ".join(bad)))
            failed += bool(bad)
        for d in explore:
            bad = [lbl for ok, lbl in checks(d) if not ok]
            print(f"[{'ok  ' if not bad else 'warn'}] {d['repo']:<18}{d['lang']:<11}(explore, non-gating)")
        for d in results:  # per-domain alignment detail for the semantic axis
            if "semantic" in d:
                print()
                print(sa.render(d["semantic"], d["repo"]))
        print(f"\n{len(gate)-failed}/{len(gate)} gate repos pass; {len(explore)} explore repos benchmarked (not gating).")
        return 1 if failed else 0

    shaped = [d for d in results if "domains" in d]   # semantic-only rows have no shape data
    print(f"{'repo':<18}{'lang':<11}{'domains':<9}{'top%':<7}{'junk':<6}{'layers':<8}{'arch✓':<8}{'viol'}")
    print("-" * 74)
    for d in shaped:
        core = "".join(l[0] for l in d["layers"]["core"]) or "-"   # P/A/D/I initials
        print(f"{d['repo']:<18}{d['lang']:<11}{d['domains']['n']:<9}{int(d['domains']['top_share']*100):<7}"
              f"{d['domains']['junk']:<6}{core:<8}{d['archetypes']['classified']:<8}{d['layers']['violations']}")
    print("\n=== domains top-5 (share) ===")
    for d in shaped:
        print(f"  {d['repo']:<18} " + " · ".join(f"{n}({l},{int(s*100)}%)" for n, l, s in d["domains"]["top5"]))
    print("\n=== lexicon concepts ===")
    for d in shaped:
        print(f"  {d['repo']:<18} {', '.join(d['lexicon']['top'])}")
    for d in results:
        if "semantic" in d:
            print()
            print(sa.render(d["semantic"], d["repo"]))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
