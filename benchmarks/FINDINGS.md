# Pilot findings (2026-07-04)

First eval run: `Create_Booking` (coral-cloud), baseline vs treatment, Opus 4.8,
via `claude -p`, isolated temp workspaces.

## Result
| arm | F1 | precision | recall | turns | cost |
|---|---|---|---|---|---|
| baseline (raw flow XML) | 1.00 | 1.00 | 1.00 | 3 | $0.31 |
| treatment (+ rebuild-brief) | 1.00 | 1.00 | 1.00 | 4 | $0.32 |
**ΔF1 = 0.00. Treatment used 1 MORE turn.** A tie — the artifact did not help.

## Honest reading
1. **The harness works** end to end: isolated arms, `claude -p` with usable
   metrics (turns/cost), operation-set grading, F1. This is reusable.
2. **This flow is too trivial to differentiate.** Single object, self-contained
   in one XML file, no Apex to resolve. The baseline agent read the file and got
   everything right in 3 turns; the brief added a read without adding value —
   confirms the predicted "trivial flows tie (or slightly regress on
   efficiency)" case. Coral flows call *standard* actions, so there is nothing
   for the artifact's resolution to save the baseline from hunting.
3. **Biggest lesson — ground-truth methodology.** The first hand-label was
   WRONG: it missed the lookup's `<queriedFields>` (Experience_Name__c, Date__c)
   and only caught `<field>Id</field>`. Our OWN extractor got those right. So a
   hand-label was less accurate than the tool — hand-labeling is error-prone and
   does not scale, and it accidentally validated extraction accuracy. We need a
   better ground-truth source (behavioral diff, or judge-model + verification)
   before scaling to 10 projects.

## Where uplift should appear (test these next)
- **Apex-heavy reimplementation** (NPSP/EDA/apex-recipes): the baseline must
  hunt across `.cls` files and reconstruct the call graph + DML; the artifact
  pre-resolves it. This is the predicted win.
- **Cross-file / cross-object flows** with real custom Apex `actionCalls` (not
  standard actions), where resolution + inlining save hunting and misses.
- A **complex** flow (depth ≥ 8) where the baseline is more likely to miss steps.

## Methodology fixes surfaced
- Ground truth must be verified/independent (hand-label is fragile).
- The brief's "scoped data model" lists all fields on a touched object; consider
  distinguishing fields the flow USES from fields merely on the object (a
  precision aid for the consuming agent).

---

# Decisive result (2026-07-04): the tool is unnecessary for flow rewrite

Test: a synthetic **depth-45, 45-element** flow (branches, loops, DML on 3
objects, 7 apex actionCalls, 14 mutations, 8 queries) — a stand-in for the
"60-deep nightmare." Model: **Fable 5**, via `claude -p`.

| arm | F1 | precision | recall | turns | cost |
|---|---|---|---|---|---|
| baseline (raw flow XML alone) | **1.00** | 1.00 | 1.00 | 3 | $0.86 |
| treatment (+ our rebuild-brief) | 1.00 | 1.00 | 1.00 | 5 | $1.43 |

**Fable 5 read the 45-deep flow and extracted every operation perfectly, from
the raw XML, in 3 turns. Our artifact added zero quality and made it 67% slower
and ~1.7× more expensive.**

Jonathan's framing settles it: *"if you can synthesize it, you can rewrite it."*
A model powerful enough to author a complex flow trivially rewrites one. Depth
is scary to a human, not to a frontier model reading one regular XML file.

## Conclusion
For **rewriting Salesforce flows/Apex, a frontier model does not need this
tool.** The rebuild value proposition is refuted at the scale we can test.
This is a *good* outcome — the eval, run cheaply, saved us from building the
Workflow IR (wave 5) and everything after it.

## What this does NOT refute (but we have no evidence it's needed either)
- **Org-scale** scoping (hundreds of interdependent files exceeding a model's
  reliable context) — untested; agentic models with read/grep + large context
  may already handle it. Do not build speculatively; test the specific failure
  if a real engagement surfaces one.
- **Human-facing** assessment (the Ontoloom org map, blast-radius, report) for
  a non-technical stakeholder — a different, smaller product, not a rewrite aid.

## Decision
**Stop building TrailTracker for the rebuild use case.** The experiment did not justify building the planned Workflow IR. This decision
concerns the Salesforce rewrite-assistance use case; the later, narrowly scoped
Rust rewrite rules and their verification are separate work.
