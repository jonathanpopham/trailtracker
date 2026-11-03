# Continuous architecture verification — `arch-verify` / `arch-init`

*(ADR-0005; schema `trailtracker.arch-spec/v1` in, `trailtracker.arch-verify/v1` out.)*

The ontology views recover what the code **is**. `arch-verify` enforces what
it is **supposed to be**: humans declare the intended architecture in a
`.trailtracker-arch.json` spec, TrailTracker verifies the actual code against
it, and CI fails the moment drift lands. ArchUnit / dependency-cruiser
territory — but deterministic, cross-language (all 56 frontends), and
grounded in the recovered graph instead of per-ecosystem import scraping.

## Adopt in one command

```console
$ trailtracker arch-init . -o .trailtracker-arch.json
$ trailtracker arch-verify .
```

`arch-init` bootstraps the spec from the *current* recovered architecture:
each business domain becomes a declared domain with derived `pathPrefixes`
(dominant-prefix set-cover), every domain gets a `domain-existence` rule
(`error` — it holds today by construction) and a `domain-containment` rule
(`warn` — the adoption ramp), and the observed inter-domain dependencies are
recorded as an advisory `observedDependencies` baseline. A freshly
bootstrapped spec never gates; intent is added by editing it.

## The spec

```json
{
  "format": "trailtracker.arch-spec/v1",
  "domains": [
    { "name": "Ordering", "pathPrefixes": ["src/Ordering."] },
    { "name": "Basket",   "pathPrefixes": ["src/Basket.API/"] }
  ],
  "rules": [
    { "type": "domain-existence",           "domain": "Ordering" },
    { "type": "domain-containment",         "domain": "Ordering", "severity": "warn" },
    { "type": "forbidden-dependency",       "from": "Ordering", "to": "Basket" },
    { "type": "forbidden-layer-dependency", "from": "Domain", "to": "Infrastructure" }
  ]
}
```

| rule | fires when | catches |
|---|---|---|
| `domain-existence` | no analyzable file matches the domain's prefixes | architecture erosion (a declared component died) |
| `domain-containment` | files under the prefixes cluster with a *different* declared domain | file/unit migration drift |
| `forbidden-dependency` | any DEPENDS-family edge crosses `from` → `to` | boundary violations, with file-level edge evidence |
| `forbidden-layer-dependency` | dependency mass flows `from`-layer → `to`-layer | layering inversions (e.g. Domain → Infrastructure) |

Rules take optional `id` and `severity` (`error` default; `warn` reports
without gating). Parsing fails **closed**: malformed JSON, an unknown rule
type, an undeclared domain, or an unknown layer is exit 2 with a fix line.
Exit codes: **0** spec holds (clean or warn-only), **1** error findings (the
CI gate), **2** usage/spec error, **3** missing DIR or spec, **4** analysis
failure.

## Real transcript — dotnet/eShop (cohort SHA 9b4f943)

Bootstrap, then declare one piece of intent the way a reviewer would —
"the Catalog service must not reach into Ordering":

```console
$ trailtracker arch-init eShop -o eShop/.trailtracker-arch.json
$ # hand-add one rule to the spec:
$ #   { "type": "forbidden-dependency", "from": "Catalog.API", "to": "Ordering" }
$ trailtracker arch-verify eShop
trailtracker arch-verify: eShop
spec: eShop/.trailtracker-arch.json — 10 domain(s), 21 rule(s)
findings (2):
  [error] forbidden-dependency:Catalog.API->Ordering: forbidden dependency: 'Catalog.API' depends on 'Ordering' (9 edge(s))
        evidence: src/Catalog.API/IntegrationEvents/CatalogIntegrationEventService.cs -[CALLS]-> src/Ordering.Domain/SeedWork/IUnitOfWork.cs
        evidence: src/Catalog.API/IntegrationEvents/EventHandling/OrderStatusChangedToAwaitingValidationIntegrationEventHandler.cs -[CALLS]-> src/Ordering.API/Application/IntegrationEvents/Events/OrderStockRejectedIntegrationEvent.cs
        evidence: src/Catalog.API/IntegrationEvents/EventHandling/OrderStatusChangedToAwaitingValidationIntegrationEventHandler.cs -[CALLS]-> src/Ordering.API/Application/IntegrationEvents/Events/OrderStockConfirmedIntegrationEvent.cs
        evidence: src/Catalog.API/IntegrationEvents/EventHandling/OrderStatusChangedToPaidIntegrationEventHandler.cs -[CALLS]-> src/Ordering.Domain/SeedWork/IUnitOfWork.cs
        evidence: src/Catalog.API/Apis/CatalogApi.cs -[CALLS]-> src/Ordering.Domain/SeedWork/IUnitOfWork.cs
  [warn] domain-containment:WebApp: 1 file(s) declared in 'WebApp' cluster with a different declared domain
        evidence: src/HybridApp/GlobalSuppressions.cs — declared 'WebApp', clusters with 'Shared/Platform' (anchored to 'Shared/Platform')
status: violated (exit 1)
$ echo $?
1
```

The nine edges are real: eShop's Catalog service consumes Ordering's
integration events by referencing `Ordering.API` event types and
`Ordering.Domain.SeedWork` directly — exactly the coupling a
"services communicate only via the event bus" intent forbids. The `warn`
finding reports without gating.

`--json` emits one `trailtracker.arch-verify/v1` object with the same
findings (`{id, type, severity, message, count, examples[]}`) plus
`status`/`exit` for machine consumers.

## CI

The whole gate is one step (the spec lives in the repo):

```yaml
- name: Architecture gate
  run: |
    curl -fsSL <trailtracker-release-url> -o trailtracker && chmod +x trailtracker
    ./trailtracker arch-verify . --json
```

Exit 1 fails the job; findings land in the log with file-level evidence.
Byte-deterministic: the same tree and spec always produce the same report,
so a red gate is a real architectural change, never flake.
