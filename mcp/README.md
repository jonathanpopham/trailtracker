# TrailTracker MCP server (gs-B1/B2)

Exposes TrailTracker's deterministic extractors as live MCP tools so an agent
can load **only the relevant subgraph** of a huge codebase instead of stuffing
files into context. The server is pure orchestration: every tool shells out to
the existing `trailtracker` binary. **No LLM, no network, no state** — it stays
deterministic and airgap-pure by construction (the only side effect is spawning
the binary).

```
Claude Code  ── stdio JSON-RPC 2.0 ──>  mcp/trailtracker_mcp.py  ── argv ──>  trailtracker <cmd> <dir>
                                        (Python 3 stdlib only)                 (std-only Rust binary)
```

## Files

| File | What |
|---|---|
| `mcp/trailtracker_mcp.py` | The server. Single file, Python 3 stdlib only, zero install. |
| `mcp/test_mcp.py` | E2E suite: spawns the real server, drives the real binary on `eval/corpus/calc`. |
| `mcp/test_e2e_cohort.py` | Cohort E2E: drives the live server against real benchmark repos (set `COHORT_DIR`). |

Run tests: `python3 mcp/test_mcp.py` (exit 0 = green; currently 163/163).
Debug logging: `TRAILTRACKER_MCP_LOG=debug`.

## Why Python stdlib (not a Rust bin)

Per the `mcp-server-design` rubric the server is a thin protocol adapter — all
the intelligence lives in the binary. Choosing Python stdlib over a workspace
Rust bin because:

1. **Zero install, zero build** — `python3` ships on macOS/Linux; no pip, no
   cargo step before an agent can use it. `.mcp.json` points straight at the file.
2. **Workspace isolation** — the Rust workspace (and `scripts/verify.sh`)
   is untouched; no new bin target, no clippy/fmt/test surface, no risk to the
   golden-regression gate.
3. **Right tool for the layer** — JSON-RPC line framing + `subprocess` +
   pagination is ~450 lines of stdlib Python; a std-only Rust version would
   hand-roll JSON serialization for no runtime benefit (the binary dominates
   latency anyway).

The airgap policy (ADR-001, std-only, no supply chain) still holds: the server
imports only `json, os, subprocess, sys, time, pathlib`.

## Binary resolution (in order)

1. `TRAILTRACKER_BIN` env var
2. `<worktree>/target/release/trailtracker` (sibling of `mcp/`)
3. `~/geist/trailtracker/target/release/trailtracker`

Resolved per call, so building the binary after server start Just Works.
Missing binary → structured `BINARY_MISSING` error with build instructions.

## Tool surface (16 tools)

Every tool takes a required `repo_path` (absolute path of the directory to
analyze). Results come back as one `text` content item.

| Tool | Binary command | Returns | Paged |
|---|---|---|---|
| `brief` | `trailtracker brief <dir>` | Markdown codebase brief (overview, architecture, entry points, hotspots, cycles, synthesis). **Recommended first call.** | no |
| `stats` | `trailtracker stats <dir>` | Plain-text coverage + graph statistics (trust calibration). | no |
| `graph` | `trailtracker graph <dir>` | Full canonical graph, JSON envelope. | **yes** |
| `domains` | `extract domains <dir>` | Business-domain clustering. | yes |
| `archetypes` | `extract archetypes <dir>` | Structural role classification. | yes |
| `layers` | `extract layers <dir>` | Architectural layers + violations. | yes |
| `lexicon` | `extract lexicon <dir>` | Codebase vocabulary (concept tokens). | yes |
| `hierarchy` | `extract hierarchy <dir>` | Domain→Project→File→Symbol tree. | yes |
| `data_ontology` | `extract data-ontology <dir>` | Entity/field/relationship data model. | yes |
| `workflow_spec` | `extract workflow-spec <dir>` | Recovered end-to-end flows. | yes |
| `search` | `trailtracker search "<query>" <dir>` | Hybrid BM25 + hash-embedding retrieval, ranked hits with `why` explanations. | no (limit ≤ 200) |
| `explain` | `trailtracker explain <target> <dir>` | One card per file/symbol: identity, classification, fan-in/out, blast radius, neighbors. | no |
| `arch_verify` | `trailtracker arch-verify <dir> [--spec PATH]` | Architecture drift report (`trailtracker.arch-verify/v1`): findings with evidence against the committed `.trailtracker-arch.json` intent spec. | no |
| `violations` | `trailtracker violations <dir>` | Spec-free FULL layer-violations report (`trailtracker.violations/v1`): every outward-pointing dependency at unit grain — perpetrating unit pairs, layer-pair totals, file-level evidence, ranked worst-first. | no |
| `nav_pack` | `trailtracker nav pack "<query>" <dir> --budget N` | The context navigator (ADR-0004): one character-budgeted exact context pack — seeds, cards, orientation, read-plan spans, 2-hop neighborhood. | budgeted (chars) |
| `nav_expand` | `trailtracker nav expand <target> <dir>` | Direction-aware depth-k neighborhood around any node, cursor-paged under a char budget. | budgeted + cursor |

Tool names are snake_case (agent-friendly, becomes
`mcp__trailtracker__data_ontology`); the server maps them to the binary's
kebab-case extractor names.

### Paged JSON envelope

JSONL-emitting tools parse the binary's JSONL into a JSON object:

```json
{
  "tool": "domains",
  "extractor": "domains",
  "repo_path": "/abs/path",
  "total_records": 24,
  "offset": 0,
  "returned": 24,
  "truncated": false,
  "next_offset": null,
  "records": [ { "record": "node", "id": "...", "kind": "...", "properties": {...} }, ... ]
}
```

**Large-output safety:** default `limit` is **2000 records**; `limit: 0` means
unlimited (documented as dangerous — jellyfin's ~20k-node graph would flood
context). `truncated: true` + `next_offset` tell the agent exactly how to page.
Extractor output order is byte-deterministic, so paging is stable across calls.

### Input schema (paged tools; `brief`/`stats` take only `repo_path`)

```json
{
  "type": "object",
  "properties": {
    "repo_path": { "type": "string" },
    "limit":     { "type": "integer", "minimum": 0, "default": 2000 },
    "offset":    { "type": "integer", "minimum": 0, "default": 0 }
  },
  "required": ["repo_path"],
  "additionalProperties": false
}
```

## Error shapes

Per the assignment, all failures are **JSON-RPC error objects** (not
`isError: true` tool results), each with a machine-parseable `data.type` and an
actionable `data.hint`:

| Code | `data.type` | When | Hint carries |
|---|---|---|---|
| -32601 | — | unknown method | supported methods |
| -32602 | `UNKNOWN_TOOL` | bad tool name | `available_tools` list |
| -32602 | `MISSING_REPO_PATH` | no `repo_path` | how to discover it (`pwd`) |
| -32602 | `PLACEHOLDER_PATH` | `/path/to/...`, `YOUR_*`, `<...>` | replace with real path |
| -32602 | `REPO_PATH_NOT_FOUND` | dir doesn't exist | resolved path + server cwd |
| -32602 | `INVALID_PAGING` | bad `limit`/`offset` | valid forms |
| -32000 | `BINARY_MISSING` | no trailtracker binary | searched paths + build cmd |
| -32001 | `ANALYSIS_FAILED` | binary exit ≠ 0 | argv + full stderr |
| -32002 | `TIMEOUT` | > `TRAILTRACKER_TIMEOUT_SECS` (300s) | how to raise it |
| -32003 | `OUTPUT_UNPARSEABLE` | binary emitted non-JSON line | flags it as a TT bug |

Mistake-detection per the skill: placeholder paths are intercepted before the
binary runs; string digits are coerced for `limit`/`offset` (forgive by
default); relative paths resolve but the error educates about absolute paths.

## Agent UX decisions (skill rubric)

- **16 tools, one cluster, no overlap** — each maps 1:1 to a deterministic view.
- **Guided workflow** — the `initialize.instructions` field tells the agent the
  intended order: `brief` → `stats` → derived views → raw `graph` last.
- **Discovery in descriptions** — every description says when to use it, what
  the envelope looks like, and one Do/Don't.
- **Determinism as a feature** — same repo in, same bytes out; agents can cache
  and diff results safely.
- **Shipped since the original 10-tool design** — `search` (gs-G2, std-only
  hybrid retrieval, tool #11), `explain` (tool #12, which solves the target
  discovery UX by resolving ids/paths/names with structured
  `AMBIGUOUS_TARGET`/`TARGET_NOT_FOUND` errors), and the K1 navigator
  (`nav_pack` #13 / `nav_expand` #14: character-budgeted exact context packs —
  chars, not tokens; there is no tokenizer anywhere in the stack) and `arch_verify` (#15, ADR-0005: spec-driven drift gating, findings-as-data)
  and `violations` (#16, the spec-free full layer-violations report at unit
  grain — the perpetrators the `layers` aggregate loses); a raw
  `query`/`rebuild_brief` surface remains a candidate for a follow-up.

## Wiring into Claude Code

Add to the project's `.mcp.json` (or merge into an existing `mcpServers` map):

```json
{
  "mcpServers": {
    "trailtracker": {
      "command": "python3",
      "args": ["/path/to/trailtracker/mcp/trailtracker_mcp.py"]
    }
  }
}
```

Tools then appear as `mcp__trailtracker__brief`, `mcp__trailtracker__domains`,
etc. Optional env: `TRAILTRACKER_TIMEOUT_SECS` (default 300),
`TRAILTRACKER_MCP_LOG=debug`.

Smoke test without Claude Code:

```bash
printf '%s\n%s\n%s\n' \
  '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2025-06-18","capabilities":{},"clientInfo":{"name":"smoke","version":"0"}}}' \
  '{"jsonrpc":"2.0","id":2,"method":"tools/list"}' \
  '{"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"brief","arguments":{"repo_path":"'"$PWD"'/eval/corpus/calc"}}}' \
  | python3 mcp/trailtracker_mcp.py
```
