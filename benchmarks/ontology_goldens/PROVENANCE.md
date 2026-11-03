# Ontology view goldens — provenance

Frozen 2026-07-06 on branch `w2/goldens`.

Re-blessed 2026-07-06 on branch `dom3/structural` (domains-v3): the domains
extractor moved from lexical token-frequency clustering to deterministic
structural clustering (greedy modularity over unit dependency mass, path
priors, mirror fold). Domain names changed from vocabulary buckets
(`Case`, `Op`, `Area`, `Assign`) to structural path labels (`classes`,
`flows`, `objects`, `triggers`; concept tie-break `op`/`area` for
single-unit repos with no path decomposition). The hierarchy goldens moved
with them (the hierarchy view consumes `assign_domains`).

Each file `<fixture>__<view>.jsonl` is the byte-exact stdout of:

    target/release/trailtracker extract <view> eval/corpus/<fixture>

for every view in {domains, archetypes, layers, hierarchy} crossed with every
self-contained corpus fixture in {apexorg, calc, sflinked, sforg, sfperms,
shapes}. Extractors are pure, deterministic functions of the base graph
(see `src/extract/mod.rs`), so outputs are byte-stable by design — no
scrubbing is needed and comparison is exact (`diff -u`).

Checked by `benchmarks/golden_check.sh`, invoked from `scripts/verify.sh`
after the base-graph corpus regression gate. Any diff fails the gate.

To re-bless after an intentional extractor change:

    UPDATE_GOLDENS=1 bash benchmarks/golden_check.sh
    git diff benchmarks/ontology_goldens/   # review EVERY change
    git add benchmarks/ontology_goldens/ && git commit
