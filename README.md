# TrailTracker

Local code graphs, architecture summaries, and evidence for coding agents.

TrailTracker analyzes a repository and produces a deterministic graph of its
files, definitions, imports, and calls. It derives architecture views from that
graph and helps you find the code relevant to a task. The default Rust binary
uses only the standard library: no external crates, model calls, or network
services. `unsafe` is forbidden in the runtime crate.

**Status: early release, v0.1.1.** Language depth varies. Graphs and derived
views are analysis aids, not a compiler's complete semantic model. Read the
[limitations](#limitations) before relying on a finding.

## Build and try it

Download a native archive from [the v0.1.1 release](https://github.com/jonathanpopham/trailtracker/releases/tag/v0.1.1),
or see [the project page](https://jonathanpopham.com/trailtracker/) for downloads
by operating system and processor. Extract it and run `./trailtracker help`
(`.\trailtracker.exe help` in PowerShell). Copy the binary to a directory on your
`PATH` to use `trailtracker` from any directory. macOS binaries are unsigned.
The release includes SHA-256 checksums; the MCP adapter is in the source tree.

To build from source:

Install Rust 1.90.0 or newer, then:

```sh
git clone https://github.com/jonathanpopham/trailtracker.git
cd trailtracker
cargo build --release --locked

./target/release/trailtracker brief /path/to/repo
./target/release/trailtracker stats /path/to/repo
./target/release/trailtracker search "payment processing" /path/to/repo --json
```

With rustup, `rust-toolchain.toml` selects the project's pinned toolchain.
There is no crates.io package.

## What you can do

| Task | Command |
|---|---|
| Orient yourself in a repository | `trailtracker brief REPO` |
| Inspect parsing and call-resolution coverage | `trailtracker stats REPO` |
| Export the underlying graph | `trailtracker graph REPO` |
| Inspect architecture groupings | `trailtracker extract domains REPO` |
| Inspect layers and dependency violations | `trailtracker extract layers REPO` |
| Find symbols and inspect their relationships | `trailtracker search "query" REPO --json`, `trailtracker explain SYMBOL REPO` |
| Estimate the affected code around a symbol | `trailtracker query blast-radius SYMBOL REPO --json` |
| Get a bounded context pack and source read plan | `trailtracker nav pack "task description" REPO --budget 20000 --json` |
| Review dead-code candidates and their evidence | `trailtracker deadcode REPO --min-confidence high` |
| Generate an interactive HTML report | `trailtracker dossier REPO -o report.html` |
| Inspect narrowly scoped Rust rewrite rules | `trailtracker rewrite rules --json` |

Use `trailtracker capabilities` for the machine-readable command contract.
Context budgets are measured in characters, not tokens. Dead-code findings
need review; exit status 1 means findings for that command.

## How it works

```text
source files -> language front ends -> lossless syntax trees -> shared IR
                                                               |
                                                       canonical code graph
                                                               |
                                   architecture views / queries / agent context
```

The engine registers 58 language front ends. Call resolution records whether a
target is resolved, ambiguous, or external, and retains candidate sets where
resolution is ambiguous. Stable ordering makes repeated analysis of unchanged
input comparable byte for byte.

Seven derived views cover data, workflows, vocabulary, archetypes, layers,
domains, and hierarchy. Domain membership uses deterministic structural
clustering. A separately enabled `enrich` feature can invoke a model to label
clusters; it is excluded from default builds and cannot change membership.

The Rust rewrite path separates proposing, verifying, and applying changes.
Its checker recomputes before-and-after control/data-flow graphs and checks the
remapping allowed by a specific rule. Certificates carry their assumptions;
they do not prove arbitrary program equivalence or replace compilation and
tests. See [the certificate design](docs/decisions/0007-equivalence-certificates.md).

## Coding-agent integration

The MCP adapter uses Python 3's standard library and runs the local binary.
Build the binary first, then add this configuration to your MCP client:

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

The adapter exposes summaries, graph queries, search, symbol explanations,
architecture checks, dead-code evidence, and context navigation. See
[the MCP guide](mcp/README.md) for tool schemas and configuration.

## Verification and evidence

```sh
bash scripts/verify.sh
python3 mcp/test_mcp.py
```

The local gate runs formatting, Clippy, workspace tests, a 20,000-case property
harness, self-analysis, and frozen graph/ontology comparisons. It emits a JSON
report containing the binary hash. CI also compares selected language front
ends with external parsers and evaluates ontology views on a pinned cohort of
11 repositories across six languages.

Kani harnesses add bounded checks when Kani is installed. The parser harness
covers the Rust parser on strings of at most five characters from a selected
ASCII alphabet. Rewrite harnesses cover small semantic models under documented
assumptions. Kani is optional locally and non-blocking in the current CI.

Recorded evaluations, including unfavorable results, are in
[benchmarks](benchmarks/) and [docs/evals](docs/evals/). The eShop domain
evaluation reported macro-F1 0.923 against its reviewed decomposition; this is
one semantic fixture, not a general accuracy guarantee. Context-format
experiments measure consumption of graph facts, not independent correctness
of the graph itself.

## Limitations

- Lossless parsing preserves source bytes; it does not establish complete or
  correct semantic understanding. Front-end depth and resolution vary by language.
- Domains, archetypes, layers, and dead-code classifications are heuristic.
  Reflection, dynamic dispatch, framework registration, and cross-language calls
  can leave gaps. Inspect coverage and evidence before acting.
- Statement-level control/data-flow analysis and rewrite rules currently focus
  on Rust. Rewrite verification has explicit aliasing, type, and side-effect
  assumptions; see the rule documentation.
- Default analysis runs locally without a model. Optional enrichment invokes an
  external model runner. Commands such as `dossier` and `rewrite apply` write
  files; consult each command's help for its output paths.
- This is experimental developer tooling, not a certified safety-critical tool.

## Development

`src/` contains the runtime; `eval/` holds development-only verification tools;
`mcp/` holds the Python adapter; `docs-site/` is the optional documentation site.
The runtime remains independent of the website's JavaScript dependencies.

Bug reports are welcome. Outside code contributions are not currently accepted;
the maintainer may independently implement fixes described in an issue.

## License

Copyright (c) 2026 Jonathan Popham. All rights reserved.
No open-source license is granted. This release makes the source available for
inspection under the existing all-rights-reserved terms.
