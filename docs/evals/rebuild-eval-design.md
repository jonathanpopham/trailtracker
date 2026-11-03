# Eval: does the artifact actually help an agent rebuild Salesforce logic?

- **Status:** Design / thread (2026-07-03)
- **Owner:** Jonathan
- **Why this exists:** we have been building the extraction artifact on a
  *hypothesis* of what helps an agent. This eval **validates or refutes** it. If
  Opus 4.8 + our artifact does not beat Opus 4.8 alone, the artifact is not
  adding value and we have failed — better to learn that on 3 flows than after
  building the whole Workflow IR.

## The claim under test

> Given the task "reimplement this Salesforce automation on a target platform,"
> an agent equipped with our artifact is **faster** (fewer tool calls/turns),
> **more complete** (higher recall of steps/dependencies), **more precise**
> (fewer hallucinated or missed operations), and **more correct** (behavioral
> equivalence) than the same agent given only the raw Salesforce metadata.

If true → we have a product/moat. If false → we're a nice graph nobody needs.

## Design

- **Corpus**: 10 Salesforce projects of *varied complexity*. Public seed set
  (trailheadapps: coral-cloud, ebikes, dreamhouse, and flow-heavy community
  repos); augment with anonymized real orgs when access allows. Deliberately
  include **hard cases** (flow → apex → apex, cross-object, co-firing
  validation/workflow rules) — that's where the artifact should win; trivial
  single-object flows may tie, and that's honest.
- **Task**: for each automation, "produce an equivalent implementation on
  target T" (T = a neutral target first — TypeScript/Python that replicates the
  behavior — before Medplum-specific, so grading isn't confounded by FHIR
  mapping difficulty).
- **Arms**:
  - **Baseline**: agent (Opus 4.8) + the raw `sf project retrieve` files.
  - **Treatment**: agent (Opus 4.8) + the raw files + our artifact
    (rebuild-brief today; the MCP-over-model surface later).
  - Same model, same prompt, same budget — only the artifact differs.

## Metrics

1. **Efficiency** — tool calls / turns / tokens to a complete answer. (The
   artifact pre-resolves cross-references, so the agent shouldn't have to hunt.)
2. **Recall** — fraction of the automation's true operations/dependencies the
   rebuild reproduces (queries, mutations, branches, called code, touched
   fields). Missing a co-firing validation rule or a called class = a miss.
3. **Precision** — fraction of the rebuild's operations that are actually in the
   original (no hallucinated fields/steps). **F1 = harmonic mean** of the two.
4. **Behavioral equivalence** — the gold standard: run the original and the
   rebuild on the same inputs, diff outputs. Hard for Salesforce (needs an org
   or a characterization harness); approximate early with a hand-labeled
   "expected operations" ground truth per flow, upgrade to behavioral later.
5. **Human completeness/correctness judgment** — did it miss anything, invent
   anything, get the order wrong.

Ground truth: a hand-authored "operation set" per flow (the queries, mutations,
branches, calls, fields it must reproduce) — the same thing our extractor
produces, but authored independently so we're not grading ourselves against
ourselves.

## Where we predict we win — and where we don't (state it before running)

- **Win**: complex, cross-referenced, multi-file automations at scale — the
  agent-hunting cost and the miss-rate both explode for the baseline, and our
  resolution + scoping collapse them.
- **Tie**: trivial single-object flows the agent can read whole from one file.
- **Lose (the failure mode to watch)**: if our extraction is *wrong or
  incomplete*, we mislead the agent — worse than nothing. Extraction accuracy is
  therefore the precondition; the verify.sh/oracle discipline is what protects
  it. Also lose if the artifact is verbose/noisy enough to bloat context without
  proportional help.

## Run it small, first (recommendation)

Do not wait for "down the road." Run **n=1–3 now**, before wave 5:
- Pick one Coral Cloud flow (e.g. `Send_Verification_Code`, depth 8).
- Arm A: agent + the raw `.flow-meta.xml` + `.cls` files → reimplement.
- Arm B: same agent + `trailtracker rebuild-brief` output → reimplement.
- Measure tool calls + recall against a hand-labeled operation set.
A 3-flow pilot tells us what an agent actually needs — which stops us building
the wrong thing in wave 5. This is the cheapest de-risking available.

## Decisions (2026-07-04)
- **Rebuild target:** neutral **TypeScript** (isolates the artifact's value from
  FHIR-mapping difficulty; Medplum pass is a later realism check).
- **Agent invocation:** local `claude -p --output-format json` (gives
  `num_turns`, `result`, `total_cost_usd`, tokens); each arm in an isolated temp
  dir. CI's LLM tier waits on a provisioned API key.
- **Ground truth:** hand-labeled operation-sets for the pilot flows, authored
  from the **raw** flow XML (not our tool's output — no self-grading).
- **Grading is on a structured operation-set** each arm emits alongside its TS
  (queries/mutations/branches/calls/fields), so we compare op-sets rather than
  parse arbitrary TypeScript.

## Success criteria

### Tier 1 — extraction quality (CI gate, deterministic, no LLM)
Our extractor's operation-set for each fixture flow must match the hand-labeled
ground truth with **F1 ≥ 0.95**. A code change that drops any fixture below
0.95 **fails CI**. This protects the artifact's trustworthiness — a wrong
artifact is worse than none, so this is the precondition for Tier 2.

### Tier 2 — agent uplift (product validation, LLM, release/manual)
Primary go/no-go (measured on the **complex-flow subset**):
- **F1 uplift:** treatment F1 ≥ baseline F1 **+ 0.10** (must clearly win where
  it matters).
- **Efficiency:** treatment `num_turns` ≤ **0.6×** baseline (resolution cuts
  hunting).
- **Precision floor:** treatment precision ≥ **0.85** absolute **and** ≥
  baseline (must not mislead the agent).
- **No-harm:** on trivial flows treatment F1 ≥ baseline (ties OK, no regression).

We have **failed** (stop and rethink, don't keep building) if:
- treatment F1 ≤ baseline on complex flows → the artifact adds no value;
- treatment precision < baseline → the artifact *misleads* (extraction bug —
  fix Tier 1 first);
- efficiency is not better → not worth the build cost.

Product-level (beyond a single run):
- Uplift must hold across **both** flow-heavy (coral) and **apex-heavy**
  (NPSP/EDA/apex-recipes) projects.
- Ship the **minimal** artifact that clears the bars — cut anything that does
  not move F1 or efficiency.

Thresholds are v0; recalibrate after the pilot.

## Corpus (2026-07-04)
Real, mixed by design: flow-heavy **coral-cloud** (10 flows) + apex-heavy
**NPSP** (1044 apex), **EDA** (625 apex), **apex-recipes** (139 apex), plus
**dreamhouse**. Finding: large real orgs are Apex-dominant, so the eval tests
Apex reimplementation as much as Flow — which is realistic.

## Open questions the eval answers (do we understand the problem?)

- Is a **static brief** enough, or does the agent need a **navigable/queryable
  surface** (MCP: "expand this call", "give me this object's fields") to avoid
  context bloat? (Hypothesis: navigable > static for anything non-trivial.)
- How critical are **line cites** vs **resolution + scoping + structure**?
  (Hypothesis: lines are for human verification; the agent cares about
  complete-resolved-scoped semantics.)
- Is the true unit a **flow**, or an **object's reactive behavior** (all the
  automation that fires on save, in order)? (Hypothesis: the latter — a flow in
  isolation is not the whole story.)
- What's the **minimum** artifact that wins? (Cut everything that doesn't move
  the metrics.)
