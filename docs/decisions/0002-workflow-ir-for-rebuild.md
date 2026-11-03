# 0002 — A Workflow IR is the model for rebuilding Salesforce automations

- **Status:** Accepted
- **Date:** 2026-07-03

## Context

TrailTracker can now extract a Salesforce org into a connected graph: objects,
fields, relationships, flows (with element logic + depth + intra-flow data
flow), Apex (call graph + DML), formulas, the flow→Apex linker, permissions,
and workflow rules — all local, deterministic, verified, with a query/report
surface. This is a strong **assessment** tool.

But assessment is not the goal. The goal is to **rebuild** these workflows on a
different platform (Medplum), and ideally to **clean them up** in the process —
real orgs accrete flows that are far deeper and more redundant than they need
to be.

The honest gap surfaced when we asked "could an agent rebuild this from what we
produce?" No: the graph gives *structure, scope, and resolution*, but a rebuild
needs the **complete operational semantics** — typed variables, full expression
logic (not just which fields are referenced), every element's parameters, the
actual called code, and provenance (file:line). And "clean up first" needs
something you can *optimize*, which a position-free semantic graph is not.

## Decision

**Lift each Salesforce automation into a canonical, platform-neutral Workflow
IR, and treat rebuild and cleanup as operations on that IR.**

```
Flow  →  lift  →  Workflow IR  →  (optimize)  →  lower  →  Medplum Bot
```

- **direct rebuild (structure-preserving)** = lower the IR directly to the target: each source
  step maps to a target step, structure and semantics preserved.
- **Cleaned-up rebuild** ("the gist, cleaner") = run IR→IR optimization passes
  (dead-branch elimination, redundant-query merge, constant folding) first,
  then lower. This deliberately relaxes strict structure preservation for a better
  result — and it is only possible because there is a real IR to transform.

The Workflow IR is the "good model first"; rebuild and cleanup are both
functions of it. This is the compiler pattern applied to workflow migration:
the Salesforce element vocabulary is *surface syntax*; the IR is the
*semantics*; the target codegen is *lowering*.

### What the model must capture (the rebuild requirements)

1. **Type system** — objects, fields *with types*, picklist value sets,
   relationships, record types.
2. **Data environment** — the flow's typed variables, formulas, constants,
   collections (its memory).
3. **Control flow** — the ordered/branching element graph. (Have.)
4. **Operations** — complete per-step semantics for every element kind
   (query / mutate / assign / branch / loop / screen / wait / fault).
5. **Expression language** — parsed ASTs of every condition/formula/assignment,
   not merely the referenced fields.
6. **Called logic** — Apex invocables and subflows, resolved and either
   modeled or inlined as source.
7. **Effects** — per-step reads/writes.
8. **Provenance** — file:line on everything, for verification.
9. **Platform assumptions** — order-of-execution, transaction/governor and
   security context — documented as annotations, not replicated.

## Consequences

- **The IR is the product, not the graph.** The graph remains the index and the
  analysis surface; the Workflow IR is what a rebuild consumes. TrailTracker
  grows a second output shape (operational, per-workflow) alongside the
  structural graph.
- **"direct rebuild (structure-preserving)" becomes tractable and honest.** Even a perfect IR does
  not auto-generate a running Medplum app — a flow assumes the whole Salesforce
  runtime (governor limits, order of execution, security). The IR gives the
  *complete specification*; lowering produces a *faithful scaffold* a human or
  agent finishes. We do not oversell a magic transpile.
- **Cleanup is systematic, not manual.** Optimization is IR→IR passes with a
  reported diff — auditable, deterministic, and reviewable before rebuild.
- **Build arc** (tracked in `docs/prompts/goal-workflow-ir-rebuild.md`):
  Wave 4 builds the foundations — an expression AST parser, the flow data
  environment + element completeness, and a `rebuild-brief` generator that is
  the immediate "hand it to an agent" deliverable (scoped data model + ordered
  steps with full logic + inlined Apex source + provenance + a Medplum
  scaffold). Wave 5 builds the Workflow IR proper, the lifting pass, the
  optimization passes, and the Medplum-Bot lowering.
- **Constraints unchanged.** std-only, deterministic, airgapped, no LLM in the
  path, `verify.sh` green. The IR and every pass are deterministic and
  hash-attestable, consistent with decision 0001.

## Alternatives considered

- **Hand the agent the raw files.** Rejected as the *whole* answer: it dumps 46
  Apex files and the org and says "good luck." TrailTracker's value is producing
  a *scoped, resolved, complete-but-minimal* package — which requires the graph
  (scope + resolution) plus the IR (semantics).
- **Ship only the structural graph + a summary spec.** Rejected: a summary of
  steps (depth, element counts, which fields) is an assessment, not a rebuild
  input, and it cannot be optimized.
- **A direct Flow→Medplum transpiler with no IR.** Rejected: no place to clean
  up, no reuse across targets, and it welds the hardest problem (platform
  semantics) to the codegen. The IR isolates concerns.
