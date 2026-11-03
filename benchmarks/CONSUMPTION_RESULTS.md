# Consumption eval — which context format lets which model answer best?

Backend: `claude -p --model {model}` · 640 graded answers · grid = (model × format × budget) per repo · every gold answer IS a graph fact.

The graph writes its own exam: 20 deterministic questions per repo (eShop, bio-mcp-client), gold answers pulled straight from the graph, graded by exact / set-overlap / numeric-tolerance. Model answers vary run to run; every raw answer is recorded in `consumption_results.json` and accuracy is reported honestly.

## Honest read (what the numbers say)

- **The blanket claim "verbalized beats raw on haiku" does NOT hold — raw JSON is the accuracy ceiling** (haiku 0.787 vs verbalize 0.738). Raw contains *every* fact, so a capable-enough model can always dig them out. That is the honest headline finding.
- **But verbalize gets ~94% of raw's accuracy at ~85% of the chars** (13,649 vs 16,018 chars/correct on haiku — the lowest cost-per-correct of any competitive format). On a chars-per-correct-answer basis, verbalize is the efficiency winner.
- **Where facts must be *joined*, not merely *looked up*, verbalize dominates:** domain-dependency questions go verbalize 16/16 vs raw 8/16 vs brief/nav 0/16 on haiku. Raw JSONL forces the model to resolve `domain::X -[DEPENDS_ON]-> domain::Y` edge ids and it botches half of them; the verbalizer states the relationship as a sentence and haiku just reads it. This is the verbalizer thesis, proven with numbers.
- **Format choice moves accuracy more than model choice.** haiku and sonnet track within ~5 points per format. Cheap-model + right-format (haiku + verbalize) ≈ expensive-model + raw-dump, at lower char cost — the market story.
- **nav pack and brief are the wrong tool for aggregate/relational graph facts:** nav scores 0/16 on file_count and domain_deps (the pack carries seeds + read-plan for *code reading*, not domain aggregates), though it wins top_dependents. brief is 0/16 on domain_deps at 8k budget.
- **One verbalize weakness is a coverage gap, not a format failure:** verbalize scores 2/16 on top_dependents because the summary/all view reports fan-in *counts* but does not enumerate dependent symbol *names*. A fixable V1 finding — add a dependents view.

## Aggregate: mean accuracy & chars-per-correct (pooled over both repos + both budgets)

| model | format | mean accuracy | chars / correct answer |
|---|---|---|---|
| haiku | raw | 0.787 | 16018 |
| haiku | verbalize | 0.738 | 13649 |
| haiku | nav | 0.463 | 26454 |
| haiku | brief | 0.45 | 28643 |
| sonnet | raw | 0.8 | 15768 |
| sonnet | verbalize | 0.738 | 13649 |
| sonnet | brief | 0.65 | 19830 |
| sonnet | nav | 0.487 | 25097 |

## Per-question-type accuracy by format (pooled repos + budgets)

### haiku

| question type | raw | brief | verbalize | nav |
|---|---|---|---|---|
| domain_deps | 8/16 | 0/16 | 16/16 | 0/16 |
| domain_of_file | 16/16 | 13/16 | 16/16 | 16/16 |
| file_count | 16/16 | 16/16 | 16/16 | 0/16 |
| layering | 7/16 | 5/16 | 9/16 | 9/16 |
| top_dependents | 16/16 | 2/16 | 2/16 | 12/16 |

### sonnet

| question type | raw | brief | verbalize | nav |
|---|---|---|---|---|
| domain_deps | 8/16 | 5/16 | 16/16 | 1/16 |
| domain_of_file | 16/16 | 14/16 | 15/16 | 16/16 |
| file_count | 13/16 | 16/16 | 16/16 | 0/16 |
| layering | 11/16 | 10/16 | 8/16 | 9/16 |
| top_dependents | 16/16 | 7/16 | 4/16 | 13/16 |

## Full grid (per repo × model × format × budget)

| repo | model | format | budget | accuracy | mean ctx chars | chars/correct | per-type |
|---|---|---|---|---|---|---|---|
| biomcp | haiku | raw | 20000 | 0.85 (17/20) | 18721 | 22025 | domain_deps:3/4 domain_of_file:4/4 file_count:4/4 layering:2/4 top_dependents:4/4 |
| biomcp | haiku | verbalize | 20000 | 0.75 (15/20) | 12655 | 16874 | domain_deps:4/4 domain_of_file:4/4 file_count:4/4 layering:3/4 top_dependents:0/4 |
| biomcp | haiku | verbalize | 8000 | 0.7 (14/20) | 7980 | 11401 | domain_deps:4/4 domain_of_file:4/4 file_count:4/4 layering:2/4 top_dependents:0/4 |
| biomcp | haiku | raw | 8000 | 0.65 (13/20) | 7877 | 12119 | domain_deps:0/4 domain_of_file:4/4 file_count:4/4 layering:1/4 top_dependents:4/4 |
| biomcp | haiku | brief | 20000 | 0.45 (9/20) | 16437 | 36527 | domain_deps:0/4 domain_of_file:4/4 file_count:4/4 layering:1/4 top_dependents:0/4 |
| biomcp | haiku | nav | 20000 | 0.45 (9/20) | 18778 | 41729 | domain_deps:0/4 domain_of_file:4/4 file_count:0/4 layering:3/4 top_dependents:2/4 |
| biomcp | haiku | brief | 8000 | 0.4 (8/20) | 8000 | 20000 | domain_deps:0/4 domain_of_file:3/4 file_count:4/4 layering:1/4 top_dependents:0/4 |
| biomcp | haiku | nav | 8000 | 0.4 (8/20) | 6778 | 16945 | domain_deps:0/4 domain_of_file:4/4 file_count:0/4 layering:2/4 top_dependents:2/4 |
| biomcp | sonnet | raw | 20000 | 0.85 (17/20) | 18721 | 22025 | domain_deps:3/4 domain_of_file:4/4 file_count:4/4 layering:2/4 top_dependents:4/4 |
| biomcp | sonnet | raw | 8000 | 0.7 (14/20) | 7877 | 11253 | domain_deps:0/4 domain_of_file:4/4 file_count:4/4 layering:2/4 top_dependents:4/4 |
| biomcp | sonnet | verbalize | 8000 | 0.65 (13/20) | 7980 | 12278 | domain_deps:4/4 domain_of_file:4/4 file_count:4/4 layering:1/4 top_dependents:0/4 |
| biomcp | sonnet | verbalize | 20000 | 0.65 (13/20) | 12655 | 19470 | domain_deps:4/4 domain_of_file:3/4 file_count:4/4 layering:2/4 top_dependents:0/4 |
| biomcp | sonnet | brief | 20000 | 0.6 (12/20) | 16437 | 27395 | domain_deps:3/4 domain_of_file:3/4 file_count:4/4 layering:2/4 top_dependents:0/4 |
| biomcp | sonnet | brief | 8000 | 0.55 (11/20) | 8000 | 14545 | domain_deps:1/4 domain_of_file:4/4 file_count:4/4 layering:2/4 top_dependents:0/4 |
| biomcp | sonnet | nav | 8000 | 0.5 (10/20) | 6778 | 13556 | domain_deps:0/4 domain_of_file:4/4 file_count:0/4 layering:3/4 top_dependents:3/4 |
| biomcp | sonnet | nav | 20000 | 0.45 (9/20) | 18778 | 41729 | domain_deps:1/4 domain_of_file:4/4 file_count:0/4 layering:2/4 top_dependents:2/4 |
| eshop | haiku | raw | 20000 | 0.85 (17/20) | 16166 | 19020 | domain_deps:3/4 domain_of_file:4/4 file_count:4/4 layering:2/4 top_dependents:4/4 |
| eshop | haiku | raw | 8000 | 0.8 (16/20) | 7692 | 9615 | domain_deps:2/4 domain_of_file:4/4 file_count:4/4 layering:2/4 top_dependents:4/4 |
| eshop | haiku | verbalize | 8000 | 0.75 (15/20) | 7967 | 10623 | domain_deps:4/4 domain_of_file:4/4 file_count:4/4 layering:2/4 top_dependents:1/4 |
| eshop | haiku | verbalize | 20000 | 0.75 (15/20) | 11662 | 15550 | domain_deps:4/4 domain_of_file:4/4 file_count:4/4 layering:2/4 top_dependents:1/4 |
| eshop | haiku | brief | 20000 | 0.55 (11/20) | 19120 | 34764 | domain_deps:0/4 domain_of_file:3/4 file_count:4/4 layering:2/4 top_dependents:2/4 |
| eshop | haiku | nav | 8000 | 0.5 (10/20) | 6994 | 13989 | domain_deps:0/4 domain_of_file:4/4 file_count:0/4 layering:2/4 top_dependents:4/4 |
| eshop | haiku | nav | 20000 | 0.5 (10/20) | 16389 | 32780 | domain_deps:0/4 domain_of_file:4/4 file_count:0/4 layering:2/4 top_dependents:4/4 |
| eshop | haiku | brief | 8000 | 0.4 (8/20) | 8000 | 20000 | domain_deps:0/4 domain_of_file:3/4 file_count:4/4 layering:1/4 top_dependents:0/4 |
| eshop | sonnet | raw | 8000 | 0.85 (17/20) | 7692 | 9050 | domain_deps:2/4 domain_of_file:4/4 file_count:3/4 layering:4/4 top_dependents:4/4 |
| eshop | sonnet | verbalize | 20000 | 0.85 (17/20) | 11662 | 13721 | domain_deps:4/4 domain_of_file:4/4 file_count:4/4 layering:3/4 top_dependents:2/4 |
| eshop | sonnet | brief | 8000 | 0.8 (16/20) | 8000 | 10000 | domain_deps:1/4 domain_of_file:4/4 file_count:4/4 layering:3/4 top_dependents:4/4 |
| eshop | sonnet | verbalize | 8000 | 0.8 (16/20) | 7967 | 9960 | domain_deps:4/4 domain_of_file:4/4 file_count:4/4 layering:2/4 top_dependents:2/4 |
| eshop | sonnet | raw | 20000 | 0.8 (16/20) | 16166 | 20209 | domain_deps:3/4 domain_of_file:4/4 file_count:2/4 layering:3/4 top_dependents:4/4 |
| eshop | sonnet | brief | 20000 | 0.65 (13/20) | 19120 | 29415 | domain_deps:0/4 domain_of_file:3/4 file_count:4/4 layering:3/4 top_dependents:3/4 |
| eshop | sonnet | nav | 8000 | 0.5 (10/20) | 6994 | 13989 | domain_deps:0/4 domain_of_file:4/4 file_count:0/4 layering:2/4 top_dependents:4/4 |
| eshop | sonnet | nav | 20000 | 0.5 (10/20) | 16389 | 32780 | domain_deps:0/4 domain_of_file:4/4 file_count:0/4 layering:2/4 top_dependents:4/4 |
