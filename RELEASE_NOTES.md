TrailTracker's first experimental release: local code graphs, architecture
summaries, and evidence for humans and coding agents.

- Get oriented with `brief`, inspect analysis coverage with `stats`, and query
  definitions, imports, calls, and a symbol's blast radius.
- Explore seven derived architecture views, or generate an interactive HTML dossier.
- Give a coding agent a bounded context pack and file/line read plan with `nav pack`.
- Review dead-code candidates with their evidence and confidence levels.
- Connect the local binary to an MCP client using the Python standard-library adapter.

The default runtime is built with Rust 1.90.0, standard library only, with `unsafe` forbidden.
It requires no model or network service for analysis. Language depth varies across
the 58 registered front ends; architecture views and dead-code findings need review.
This is experimental developer tooling, not a compiler or a certified analysis tool.

Copyright (c) 2026 Jonathan Popham. All rights reserved. No open-source license
is granted; third-party regression fixtures retain their own notices and licenses.

## Downloads

Choose the archive for your operating system and processor. macOS downloads are
provided separately for Apple Silicon (`aarch64`) and Intel (`x86_64`). The Linux
download targets x86-64 GNU/Linux and is built on Ubuntu 22.04. Windows is x86-64.

Extract the archive, then run `./trailtracker brief /path/to/repo` (PowerShell:
`.\trailtracker.exe brief C:\path\to\repo`). On macOS/Linux, copy the binary to a
directory on your `PATH` if desired. The macOS binaries are unsigned.

`SHA256SUMS.txt` covers the downloads and the verification report. To check a
download, compare `shasum -a 256 FILE` on macOS, `sha256sum FILE` on Linux, or
`Get-FileHash FILE -Algorithm SHA256` in PowerShell with the matching entry.

Source builds: `cargo build --release --locked`. There is no crates.io package.
The MCP adapter is included in the source tree under `mcp/`.

## Verification

The release workflow gates publication on formatting, Clippy, workspace tests,
20,000 generated property cases, self-analysis, corpus/ontology snapshots, and MCP
integration. Each native build runs workspace tests and smoke-tests its extracted
archive. The attached verification report describes the Linux gate binary; its
hash is distinct from the archive checksums.

Kani proofs are optional and are not a release requirement. Lossless parsing and
bounded rewrite checks do not establish complete semantic correctness.
