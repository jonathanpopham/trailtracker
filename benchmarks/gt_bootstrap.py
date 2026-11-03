#!/usr/bin/env python3
"""Bootstrap DRAFT semantic ground truths for cohort repos that lack one.

For each cohort repo without a hand-derived ground truth this runner:
  1. runs the deterministic domains extractor (`trailtracker extract domains`)
     to get the business clusters (infrastructure groups dropped — same rule
     as semantic_alignment.clusters_from_nodes);
  2. runs the attested LLM naming pass (`trailtracker enrich-domains --json`)
     to get human-meaningful names + the attestation block; if enrichment
     fails or times out, falls back to the deterministic structural names;
  3. derives pathPrefixes per cluster: greedy set-cover over directory
     prefixes (full file paths as last resort), each prefix "owned" by the
     cluster (>= OWN_THRESH of the universe files it matches are members),
     until >= COVER_TARGET of member files are covered;
  4. writes benchmarks/ground_truth/drafts/<repo>_domains.draft.json with a
     REVIEW-REQUIRED header, the attestation, per-domain file counts, and
     review hints where we have real architectural knowledge of the project;
  5. self-scores the draft against the same clusters via semantic_alignment
     (validates the FORMAT + prefix derivation, not the truth — a self-derived
     draft is circular until a human reviews it; see drafts/README.md).

Drafts are INERT: ontology_bench.py only loads ground_truth/*.json (top
level), never ground_truth/drafts/. Promotion = human review + move.

Usage:
  python3 benchmarks/gt_bootstrap.py [repo ...]     # default: all 10
Env: TT_BIN (trailtracker binary), COHORT_DIR (cohort checkouts).
stdlib-only.
"""
import datetime
import json
import os
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

import semantic_alignment as sa

HERE = Path(__file__).parent
DRAFTS = HERE / "ground_truth" / "drafts"
BIN = os.environ.get("TT_BIN", sa.DEFAULT_BIN)
COHORT_DIR = Path(os.environ.get("COHORT_DIR", HERE / ".cohort"))
COHORT = json.loads((HERE / "cohort.json").read_text())["cohort"]

# Repos that already have a reviewed ground truth in ground_truth/ are skipped.
HAVE_GT = {"eShop"}

COVER_TARGET = 0.80   # prefixes must cover >= 80% of a cluster's member files
OWN_THRESH = 0.80     # a prefix counts only if >=80% of universe files it matches are members
MAX_PREFIXES = 60     # readability cap; actual coverage is recorded either way
ENRICH_TIMEOUT = 600  # seconds per repo for the LLM naming pass

# Review hints: real architectural knowledge about each project, to anchor
# Jonathan's 10-minute review against the project's documented structure.
REVIEW_HINTS = {
    "django": (
        "Django's documented decomposition: django/db (ORM), django/forms, "
        "django/http + django/urls (request/routing), django/template, "
        "django/core (handlers/mail/cache/management), and django/contrib/* "
        "as separate pluggable apps (admin, auth, sessions, contenttypes, "
        "gis, postgres...). Check whether clusters split contrib apps apart "
        "or lump them; tests/ mirrors app names."
    ),
    "jellyfin": (
        "Jellyfin's real split: Jellyfin.Api (HTTP controllers), "
        "MediaBrowser.Controller (abstractions/interfaces), "
        "Emby.Server.Implementations (concrete services), MediaBrowser.Model "
        "(DTOs), Jellyfin.Server (host), MediaBrowser.MediaEncoding "
        "(ffmpeg). A good GT keeps the server/controller (implementation vs "
        "abstraction) split visible rather than merging by feature noun."
    ),
    "nest": (
        "NestJS is a packages/* monorepo: core (DI/runtime), common "
        "(decorators/interfaces), microservices, websockets, "
        "platform-express / platform-fastify (HTTP adapters), testing. "
        "Domain boundaries should track packages/<name>/."
    ),
    "nopCommerce": (
        "nopCommerce layered monolith: src/Libraries/Nop.Core (domain "
        "entities), Nop.Data (EF), Nop.Services (business services by area: "
        "Catalog/Orders/Customers/...), src/Presentation/Nop.Web (+ "
        "Framework). Decide whether GT domains should be layers (as the "
        "code is organized) or commerce features (Catalog/Order/Customer) "
        "that cut across Nop.Services + Nop.Web."
    ),
    "bitwarden-server": (
        "Bitwarden server: src/Core carries feature folders (Auth, Vault, "
        "Billing, AdminConsole, Tools, KeyManagement...), with thin hosts "
        "src/Api, src/Identity, src/Admin, src/Events*, src/Notifications. "
        "Feature truth mostly lives INSIDE src/Core/<Feature>/ — check "
        "prefixes reach into it rather than stopping at src/Core/."
    ),
    "OrchardCore": (
        "OrchardCore modular CMS: src/OrchardCore.Modules/OrchardCore.<X>/ "
        "one module per feature (Contents, Media, Users, Workflows...), "
        "src/OrchardCore/ = framework libraries. With ~100 modules the GT "
        "must group modules into a handful of areas, not one per module."
    ),
    "Radarr": (
        "Radarr: src/NzbDrone.Core is the real domain (Movies, Indexers, "
        "Download clients, MediaFiles, Notifications under feature "
        "folders), src/Radarr.Api.V3 (HTTP API), src/NzbDrone.Common "
        "(infra), frontend/ (React UI). Check clusters didn't merge "
        "Core feature folders into one blob."
    ),
    "hugo": (
        "Hugo: hugolib (site build core), markup (rendering), resources "
        "(asset pipeline), tpl (template funcs), modules + hugofs + config, "
        "commands (CLI). Go package dirs are the honest boundaries."
    ),
    "dubbo": (
        "Apache Dubbo maven modules: dubbo-rpc-* (protocols), "
        "dubbo-remoting-* (transport), dubbo-registry-* (service "
        "discovery), dubbo-cluster (LB/routing), dubbo-config-* (API/"
        "spring), dubbo-metadata-*, dubbo-common. GT should track the "
        "dubbo-<subsystem> module families."
    ),
    "alacritty": (
        "Alacritty workspace: alacritty/ (GUI: display, renderer, config, "
        "input) vs alacritty_terminal/ (VT emulation core: grid, vte "
        "handling) vs alacritty_config(_derive) (config plumbing). The "
        "extractor splits alacritty/ into two clusters (window/config vs "
        "input/event) — decide if that split is real or one GUI domain."
    ),
}


def enrich(repo_dir):
    """Run `enrich-domains --json`. Returns (names, attestation_str) or
    (None, fallback_reason)."""
    try:
        r = subprocess.run([BIN, "enrich-domains", str(repo_dir), "--json"],
                           capture_output=True, text=True, timeout=ENRICH_TIMEOUT)
    except subprocess.TimeoutExpired:
        return None, f"enrich-domains timed out after {ENRICH_TIMEOUT}s"
    if r.returncode != 0:
        return None, f"enrich-domains exit {r.returncode}: {r.stderr.strip()[:200]}"
    doc = json.loads(r.stdout)
    att = doc["attestation"]
    names = {c["domain"]: {"name": c["name"], "description": c["description"],
                           "responsibilities": c["responsibilities"]}
             for c in doc["clusters"]}
    att_str = (f"backend={att['backend']} model={att['model']} "
               f"prompt_hash={att['prompt_hash']} timestamp={att['timestamp']}")
    return names, att_str


def derive_prefixes(members, universe):
    """Greedy owned-prefix cover of a cluster's member files.

    Candidates are every directory prefix (with trailing '/') plus every full
    member path (ownership 1.0 by construction, the last-resort candidate).
    A candidate qualifies iff >= OWN_THRESH of the universe files it matches
    are members. Greedy picks max newly-covered files, tie-broken by shorter
    then lexicographically smaller prefix, until COVER_TARGET is reached.
    Returns (sorted_prefixes, covered_count).
    """
    def prefixes_of(path):
        parts = path.split("/")
        for i in range(1, len(parts)):
            yield "/".join(parts[:i]) + "/"
        yield path

    total = defaultdict(int)
    for f in universe:
        for pre in prefixes_of(f):
            total[pre] += 1
    own_files = defaultdict(set)
    for f in members:
        for pre in prefixes_of(f):
            own_files[pre].add(f)

    cands = {pre: fs for pre, fs in own_files.items()
             if len(fs) / total[pre] >= OWN_THRESH}
    covered, chosen = set(), []
    need = COVER_TARGET * len(members)
    while len(covered) < need and len(chosen) < MAX_PREFIXES and cands:
        best = max(cands, key=lambda p: (len(cands[p] - covered), -len(p)))
        # deterministic tie-break: among equals prefer shortest, then lexical
        gain = len(cands[best] - covered)
        if gain == 0:
            break
        ties = [p for p in cands
                if len(cands[p] - covered) == gain and len(p) == len(best)]
        best = min(ties)
        chosen.append(best)
        covered |= cands[best]
        # drop subsumed candidates (they can no longer add anything new)
        cands = {p: fs for p, fs in cands.items() if fs - covered}
    return sorted(chosen), len(covered)


def bootstrap(repo):
    repo_dir = COHORT_DIR / repo["name"]
    clusters = sa.extract_clusters(repo_dir, BIN)
    universe = set().union(*clusters.values()) if clusters else set()
    names, att = enrich(repo_dir)
    source = (f"DRAFT auto-derived from trailtracker's own deterministic clusters; "
              f"names via attested enrich-domains ({att})" if names else
              f"DRAFT auto-derived from trailtracker's own deterministic clusters; "
              f"LLM naming unavailable, structural labels used (reason: {att})")

    domains, used = [], set()
    for dom in sorted(clusters, key=lambda d: -len(clusters[d])):
        members = clusters[dom]
        prefixes, covered = derive_prefixes(members, universe)
        naming = (names or {}).get(dom)
        name = naming["name"] if naming else dom
        if name in used:  # LLM names are not guaranteed unique across clusters
            name = f"{name} ({dom})"
        used.add(name)
        entry = {
            "name": name,
            "structuralCluster": dom,
            "pathPrefixes": prefixes,
            "fileCount": len(members),
            "prefixCoverage": round(covered / len(members), 3) if members else 0.0,
        }
        if naming:
            entry["description"] = naming["description"]
            entry["responsibilities"] = naming["responsibilities"]
        domains.append(entry)

    draft = {
        "repo": repo["name"],
        "REVIEW-REQUIRED": (
            "DRAFT — machine-derived from the extractor's own clusters "
            "(circular: scoring it against the extractor validates format, "
            "not truth). A human must review names + prefixes against the "
            "project's real architecture before this file may move to "
            "ground_truth/. See drafts/README.md for the review protocol."
        ),
        "source": source,
        "date": datetime.date.today().isoformat(),
        "sha": repo["sha"],
        "format": ("pathPrefixes: a file belongs to a ground-truth domain iff "
                   "its repo-relative path starts with one of the prefixes. "
                   "Files matching no domain are out-of-scope and excluded "
                   "from purity."),
        "derivation": (f"prefixes = greedy cover of each cluster's member files by "
                       f"directory prefixes owned >= {int(OWN_THRESH*100)}% by the "
                       f"cluster (full paths as last resort), target coverage >= "
                       f"{int(COVER_TARGET*100)}%; infrastructure groups dropped."),
        "domains": domains,
    }
    hint = REVIEW_HINTS.get(repo["name"])
    if hint:
        draft["reviewHint"] = hint

    out = DRAFTS / f"{repo['name']}_domains.draft.json"
    out.write_text(json.dumps(draft, indent=1) + "\n")

    self_score = sa.score_clusters(clusters, draft)
    return draft, self_score, out


def main(argv):
    only = set(argv[1:])
    DRAFTS.mkdir(parents=True, exist_ok=True)
    rows = []
    for repo in COHORT:
        if repo["name"] in HAVE_GT or (only and repo["name"] not in only):
            continue
        if not (COHORT_DIR / repo["name"]).is_dir():
            print(f"[skip] {repo['name']}: not checked out in {COHORT_DIR} "
                  f"(run benchmarks/fetch_cohort.sh)", file=sys.stderr)
            continue
        print(f"[run ] {repo['name']} ...", flush=True)
        try:
            draft, score, out = bootstrap(repo)
        except Exception as e:
            print(f"[FAIL] {repo['name']}: {e}", file=sys.stderr)
            rows.append((repo["name"], "-", "-", f"FAILED: {e}"))
            continue
        att = "attested-LLM" if "enrich-domains (backend=" in draft["source"] else "structural-fallback"
        rows.append((repo["name"], len(draft["domains"]), score["macro_f1"], att))
        print(sa.render(score, f"{repo['name']} (self-derived draft — format check only)"))
        print(f"       -> {out}\n", flush=True)

    print(f"{'repo':<18}{'domains':>8}{'self-F1':>9}  naming")
    print("-" * 55)
    for name, n, f1, att in rows:
        print(f"{name:<18}{n:>8}{f1:>9}  {att}")
    print("\nDrafts are INERT until reviewed + moved to ground_truth/ "
          "(see ground_truth/drafts/README.md).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
