#!/usr/bin/env python3
"""Semantic alignment scorer: recovered domain clusters vs known-truth decompositions.

The shape gate (ontology_bench thresholds) catches collapse/shatter/junk but is
blind to the vocabulary-vs-responsibility failure class: clusters can have
perfect shape while grouping files by implementation nouns instead of business
responsibility (see domain_semantics_comparison.md). This scorer measures the
thing the shape gate can't see — do the recovered clusters *align with the
actual decomposition* of the system?

Ground-truth format (benchmarks/ground_truth/*.json):
  { "repo": ..., "domains": [ {"name": ..., <membership>}, ... ] }
where <membership> is one of:
  "pathPrefixes": [...]  — file belongs iff its repo-relative path starts with
                           one of the prefixes (objective, no LLM needed);
  "keyFiles":     [...]  — explicit representative file paths (e.g. an LLM
                           ground truth that names key files per domain).

Scoring (deterministic):
  * The extractor's file universe is the set of File nodes emitted by
    `trailtracker extract domains <dir>` (properties.path + properties.domain,
    i.e. the CONTAINS domain->file assignment).
  * Each GT domain's member set = universe files matching its prefixes/keyFiles.
  * Scope = union of all GT member sets. Files outside scope (e.g. e2e/, tests
    the GT doesn't claim) are excluded from purity — the GT marks scope.
  * Each GT domain is mapped to the recovered cluster with the largest overlap
    (ties broken by cluster name; clusters may be shared across GT domains).
      coverage (recall)    = |cluster ∩ gt| / |gt|
      purity   (precision) = |cluster ∩ gt| / |cluster ∩ scope|
      f1 = harmonic mean; a GT domain with no files in the universe scores 0
           (a wrong prefix must bite, not silently vanish).
  * macro-F1 = unweighted mean of per-GT-domain F1.

Usage:
  python3 benchmarks/semantic_alignment.py <ground_truth.json> <repo_dir>
  python3 benchmarks/semantic_alignment.py <ground_truth.json> --jsonl <domains.jsonl>
Env: TT_BIN (trailtracker binary; default ~/geist/trailtracker/target/release/trailtracker)

stdlib-only; also importable (score_repo / score_clusters) by ontology_bench.py.
"""
import json, os, subprocess, sys
from pathlib import Path

DEFAULT_BIN = str(Path.home() / "geist/trailtracker/target/release/trailtracker")


def clusters_from_nodes(objs):
    """Parsed `extract domains` records -> {recovered_domain: set(file paths)}.

    Infrastructure groups (domain nodes with kind="infrastructure": the named
    homes for scaffold/docs/generated/root files, zero-ungrouped) are excluded
    from the universe: the ground truths describe the *business* decomposition
    of analyzable code, and a pathPrefixes GT would otherwise start claiming
    generated files (EF migrations under src/Ordering.*) that no business
    cluster can ever contain. Old outputs without `kind` are unaffected.
    """
    objs = list(objs)
    infra = {o.get("properties", {}).get("domain")
             for o in objs
             if o.get("record") == "node"
             and o.get("properties", {}).get("kind") == "infrastructure"}
    clusters = {}
    for o in objs:
        if o.get("record") == "node" and o.get("kind") == "File":
            p = o.get("properties", {})
            if "path" in p and "domain" in p and p["domain"] not in infra:
                clusters.setdefault(p["domain"], set()).add(p["path"])
    return clusters


def load_clusters(lines):
    """Parse `extract domains` JSONL lines -> {recovered_domain: set(file paths)}."""
    return clusters_from_nodes(json.loads(l) for l in lines if l.strip())


def extract_clusters(repo_dir, bin_path=None):
    """Run the domains extractor on repo_dir and parse its File nodes."""
    bin_path = bin_path or os.environ.get("TT_BIN", DEFAULT_BIN)
    r = subprocess.run([bin_path, "extract", "domains", str(repo_dir)],
                       capture_output=True, text=True, timeout=300)
    if r.returncode != 0:
        raise RuntimeError(f"extract domains failed on {repo_dir}: {r.stderr.strip()[:200]}")
    return load_clusters(r.stdout.splitlines())


def gt_members(domain, universe):
    prefixes = domain.get("pathPrefixes")
    if prefixes:
        return {f for f in universe if any(f.startswith(pre) for pre in prefixes)}
    keyfiles = set(domain.get("keyFiles") or ())
    return universe & keyfiles


def score_clusters(clusters, gt):
    """Deterministic alignment of recovered clusters against a ground truth.

    Returns {"macro_f1": float, "per_domain": [row, ...]} where each row has
    gt_domain, matched cluster, gt_files, coverage, purity, f1.
    """
    universe = set().union(*clusters.values()) if clusters else set()
    members = {d["name"]: gt_members(d, universe) for d in gt["domains"]}
    scope = set().union(*members.values()) if members else set()
    rows = []
    for name in (d["name"] for d in gt["domains"]):
        gt_files = members[name]
        if not gt_files or not clusters:
            rows.append({"gt_domain": name, "matched": None, "gt_files": len(gt_files),
                         "coverage": 0.0, "purity": 0.0, "f1": 0.0})
            continue
        best = min(clusters, key=lambda c: (-len(clusters[c] & gt_files), c))
        hit = clusters[best] & gt_files
        in_scope = clusters[best] & scope
        cov = len(hit) / len(gt_files)
        pur = len(hit) / len(in_scope) if in_scope else 0.0
        f1 = 2 * cov * pur / (cov + pur) if (cov + pur) else 0.0
        rows.append({"gt_domain": name, "matched": best, "gt_files": len(gt_files),
                     "coverage": round(cov, 3), "purity": round(pur, 3), "f1": round(f1, 3)})
    macro = sum(r["f1"] for r in rows) / len(rows) if rows else 0.0
    return {"macro_f1": round(macro, 3), "per_domain": rows}


def score_repo(gt_path, repo_dir, bin_path=None):
    gt = json.loads(Path(gt_path).read_text())
    return score_clusters(extract_clusters(repo_dir, bin_path), gt)


def render(result, title=""):
    out = []
    if title:
        out.append(f"=== semantic alignment: {title} ===")
    out.append(f"{'GT domain':<18}{'matched cluster':<26}{'files':>6}{'cover':>8}{'purity':>8}{'f1':>7}")
    for r in result["per_domain"]:
        out.append(f"{r['gt_domain']:<18}{str(r['matched']):<26}{r['gt_files']:>6}"
                   f"{r['coverage']:>8.3f}{r['purity']:>8.3f}{r['f1']:>7.3f}")
    out.append(f"macro-F1: {result['macro_f1']:.3f}")
    return "\n".join(out)


def main(argv):
    if len(argv) < 3:
        print(__doc__.strip().splitlines()[0], file=sys.stderr)
        print("usage: semantic_alignment.py <ground_truth.json> (<repo_dir> | --jsonl <domains.jsonl>)",
              file=sys.stderr)
        return 2
    gt_path = argv[1]
    gt = json.loads(Path(gt_path).read_text())
    if argv[2] == "--jsonl":
        clusters = load_clusters(Path(argv[3]).read_text().splitlines())
    else:
        clusters = extract_clusters(argv[2])
    result = score_clusters(clusters, gt)
    print(render(result, gt.get("repo", "")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
