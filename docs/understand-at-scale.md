# Understand at Scale — the brief as a large-codebase understanding engine

This historical evaluation explores deterministic structural summaries for
large codebases. Timings below describe the recorded checkout and machine;
they are not a guarantee for every repository or evidence of agent uplift.

## The scale test (2026-07-06) — evidence, not hope

Ran `brief` on **dotnet/eShop** — a real 527-C#-file .NET microservices app.

- **Speed:** 4,130 nodes / 9,775 edges over 540 files in **0.077s**. This measurement covers local graph construction and briefing.
- **Accuracy (genuinely good):** correctly identified `IntegrationEvent`
  (fan-in 37) as the event-bus backbone; surfaced the DDD Ordering aggregate
  (`IOrderRepository`, `OrderStatus`, `Buyer`), the DI interface surface
  (`ISettingsService`, `INavigationService`), and **5 real dependency cycles**.

Full output archived at `docs/evals/eshop-brief-baseline.md`.

## The six gaps the scale test exposed (the build backlog)

Each is dead-center for enterprise .NET understanding:

1. **Entry points missed** — "No main detected"; misses modern top-level-
   statement `Program.cs` / minimal-API hosting. → **Wave A (entrypoints)**
2. **Generated code drowns signal** — EF migrations (`*.Designer.cs`),
   gRPC/proto (`Basket.cs`) dominate largest-units + fan-out. → **Wave A
   (generated)**
3. **No service/project topology** — doesn't read `.csproj`/`.sln`, so it can't
   say "here are the services and how they depend." → **Wave A (projects)**
4. **No architectural layering** — Domain/Application/Infrastructure/API layers
   + violation detection (Domain→Infrastructure smell). → **Wave B**
5. **Dep map is 535 file-pairs** — needs project→project and namespace→namespace
   rollups to be legible at scale. → **Wave B**
6. **DI / interface-implementation not surfaced** — which class implements
   `IOrderRepository`, where it's registered (`AddScoped<IFoo,Foo>`). → **Wave B**

## Waves

- **Wave A (running):** generated-code denoise · project/solution topology ·
  modern .NET entry points. Verified against eShop.
- **Wave B (queued):** layer detection + violations · project/namespace dep
  rollups · DI + interface-impl surfacing.
- **The decider (after B):** a *scale comprehension A/B* — grade brief-grounded
  vs bare-exploration answers to architecture questions on eShop (a repo too big
  to hold). Small-scale A/B was a wash (see `benchmarks/FINDINGS.md`); this is the honest test of whether grounding wins at scale.

## Guardrail

This is NOT the retired rebuild work (rewriting flows/apex — killed by eval,
`benchmarks/FINDINGS.md`). This is *understanding at scale*, a different and
unproven-but-plausible use, requiring task-level evaluation. Every wave is verified
against a real large repo; the decider settles the thesis empirically.

## Overfit test — jellyfin (2026-07-06)

Ran the stack cold on jellyfin (2,103 C# files, `Vendor.Feature` naming — the
opposite of eShop's `Feature.Tier`). Result:

- **Brief, Archetypes, Lexicon GENERALIZE.** The lexicon nailed jellyfin's
  domain vocabulary with zero tuning: `media, library, stream, audio, video,
  image, user, channel`.
- **Domains OVERFIT and collapsed** to 1 mega-domain. Cause: `domain_key` takes
  the leading namespace segment — eShop `Ordering.API`→`Ordering` (feature), but
  jellyfin `Jellyfin.LiveTv`→`Jellyfin` (vendor). String-parsing project names is
  convention-dependent.

**Lesson: structural + vocabulary ontologies generalize; name-parsing heuristics
do not.** The fix is NOT more name heuristics (that overfits to jellyfin). It is
to redesign domains around **concept-token co-occurrence + dependency coupling**
(cluster files whose symbols share dominant lexicon concepts and that depend on
each other) — convention-agnostic, and it leans on the lexicon, which already
generalized. Re-test any new domain algorithm on BOTH eShop and jellyfin.
