# Ontology roadmap — the understanding stack

The brief and every visualization are downstream of the ontologies. This is the
upstream: a layered, deterministic set of ontologies, each a spec + an
`Extractor` that emits an Ontoloom-loadable graph. "Perfect the ontologies"
means: every tier below is defined, extensible, deterministic, and **verified
against a real large repo (eShop)** with known ground truth.

## The tiers

1. **Structural** (`src/ir/ontology.rs`) — node kinds (File/Module/Package/
   Function/Type/Constant/Macro/…) + edge kinds folded into the relation lattice
   (CONTAINMENT/DEPENDS/SPECIALIZES/CONTROL/DATA). *Have.*
2. **Data** (`extract/data_ontology.rs`) — Entity/Attribute/Relationship. *Have.*
3. **Workflow** (`extract/workflow_spec.rs`) — flow/steps. *Have (Salesforce).*
4. **Lexicon** (`extract/lexicon.rs`) — **the keystone.** Split every identifier
   into tokens; rank; classify each as a **role token** (`Service`, `Repository`,
   `Command`, `Event`, `Handler`, `Controller`, `Dto`…) or a **concept token**
   (`Order`, `Basket`, `Catalog`, `Payment`, `Buyer`…). Role tokens drive
   archetypes; concept tokens drive domains. *Build first.*
5. **Archetype** (`extract/archetypes.rs`) — *what kind of thing* each node is,
   via an **extensible rule table** (name patterns + structural signals +
   language kind): Controller, Service, Repository, Aggregate, Entity,
   ValueObject, DomainEvent, Command, Query, Handler, Factory, DTO/Contract,
   Interface, Configuration, Middleware, Extension, Migration, Test, Mock,
   EntryPoint, Client, Enum, Exception. Seed vocabulary = DDD + web merged.
6. **Layer** (`extract/layers.rs`) — Domain/Application/Infrastructure/
   API-Presentation/Shared per unit (by convention + dependency direction), with
   **violation flags** (Domain→Infrastructure is a smell). eShop is clean DDD →
   expect ~0 violations (ground truth).
7. **Domain** (`extract/domains.rs`) — **the capstone.** Bounded contexts, not a
   heuristic grouping.

## Domain algorithm (v3, shipped 2026-07-06)

**Deterministic hierarchical STRUCTURAL clustering** — dependency communities,
not vocabulary. (The first shipped algorithm clustered by dominant concept
token; a technical-service comparison showed that measures vocabulary, not
responsibility — see `benchmarks/domain_semantics_comparison.md`. It was
replaced in place; the `lexicon` extractor keeps its correct role as the token
table / labeling signal.)

- **Membership**: units (trunk/transparent path segments, mirror-fold) merged by
  greedy modularity over dependency mass — exact integer arithmetic, sorted
  tie-breaks, ratio-only thresholds (duplication-stable), adapter/kernel
  carve-outs, path-family priors. Byte-stable; never reads symbol names
  (rename-invariance holds by construction — MR2 is byte-identity).
- **Labels**: deterministic (dominant path segment; concept token as tie-break)
  — honest `control-plane`-style names.
- **Semantics (optional)**: `trailtracker enrich-domains` — an attested LLM pass
  (model + prompt-hash) names clusters ControlPlaneAPI-style and writes
  responsibilities; membership is never altered; the airgap runtime stays
  LLM-free.
- **Verified**: semantic benchmark (`benchmarks/semantic_alignment.py`) scores
  cluster↔truth alignment against a hand-derived eShop truth, wired into the
  CI gate with a 0.70 floor. Broader semantic ground truths remain future work.

## Terminology (because "project" was unclear)

The hierarchy levels, defined once so the UI + tutorial can name them:
- **Domain** — a bounded context (business capability). *Derived.*
- **Subdomain / Module** — a namespace/package within a domain.
- **Project** — a *compilation unit / deployable*: a `.csproj` in .NET, a
  package/module root elsewhere. (This is what "project" means.)
- **File** → **Symbol** (Type/Function/Constant), each carrying its **archetype**.

## Emit + Ontoloom

Every extractor emits the canonical Ontoloom wire graph. The capstone is a
**hierarchical emit** (Domain→…→Symbol, each node carrying archetype + layer +
domain labels) that the UI can lazily expand. See the UI/Ontoloom backlog in
`~/ontoloom/docs/backlog.md`.

## Waves

- **B1 (foundation, parallel):** Lexicon · Archetype · Layer extractors.
- **B2 (capstone):** Domain extractor (stands on B1 + project topology).
- **B3:** hierarchical emit format + Ontoloom ingest (processing steps into
  Ontoloom so it can load a codebase directly).

Every extractor: `Extractor` trait, deterministic (byte-stable JSONL), a unit
test + an **eShop assertion**, `verify.sh` green at integration.
