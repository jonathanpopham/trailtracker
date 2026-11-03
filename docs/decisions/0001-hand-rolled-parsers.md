# 0001 — Hand-rolled, std-only parsers (not tree-sitter, not native runtimes)

- **Status:** Accepted
- **Date:** 2026-06-29

## Context
TrailTracker analyzes 56+ languages and must ship as a single, self-contained
binary onto **airgapped defense hardware**. The deployment context treats the
supply chain as a hard attack surface: the shipped artifact may carry **no runtime
dependencies**. It is also a "lives on the line" tool, so memory safety and
auditable, deterministic behavior are first-class requirements.

A separate question is *accuracy*: a hand-written parser can silently diverge from
what a language actually means. We need a way to know ours is correct without
shipping someone else's parser.

## Decision
**Hand-roll every language front end (lexer + parser + lowering) in std-only Rust,
with zero runtime dependencies.** Normalize all languages into one shared IR (the
Atlas). Verify accuracy by diffing our output, **test-only in CI**, against each
language's *real* canonical parser (Python `ast`, Ruby `Ripper`, `go/parser`,
`tsc`, `universal-ctags`). Those external parsers live only in the never-shipped
`eval` crate and never enter the binary.

## Alternatives considered
1. **Bundle language runtimes** (python3, ruby, go, node, ctags, …) and shell out.
   Rejected: catastrophic supply chain — shipping and trusting 50+ external
   toolchains, each with its own CVEs and transitive deps. Also not one self-
   contained binary.
2. **Vendor tree-sitter grammars compiled into the binary.** Rejected: in practice
   the 56 grammars are independent third-party forks on independent release
   clocks with drifting ABIs; keeping them all building is a standing
   infrastructure burden we would not control (direct prior experience). It also
   introduces C + FFI into an otherwise 100% memory-safe Rust tool and **breaks the
   Kani losslessness proof** (cannot formally prove through a C parser we didn't
   write). It is more accurate and lower-effort *per language*, but the maintenance
   and supply-chain/safety costs are wrong for this target.
3. **Per-language Rust parser crates.** Rejected: reintroduces a cargo dependency
   tree (supply-chain surface) and has spotty coverage across 56 languages.

## Consequences
**Gains (the moat):**
- **Zero runtime dependencies** — strongest possible supply-chain posture.
- **100% memory-safe Rust**, no FFI.
- **Losslessness is formally provable** (Kani) over our own code.
- **One shared IR** across all languages (a Go caller and a Python callee in the
  same graph) — native parsers give 56 incompatible ASTs instead.
- **Error-tolerant**: extracts from files a strict parser rejects (e.g. files with
  syntax errors).

**Costs (accepted):**
- We own and maintain 56 parsers and must track language syntax drift ourselves.
- Hand-rolled parsers start *less accurate* than the real ones and need fixing.

## The accuracy mechanism
The cost above is bought down by the **ground-truth verification oracle**: run the
real parsers test-only in CI and drive every language to zero unexplained diffs
(fix our bug, or allowlist a genuine parser-vs-parser difference with a reason).
This gives us tree-sitter-grade accuracy **without** tree-sitter's fork-maintenance
hell, its C/FFI surface, or any runtime dependency. No tree-sitter- or
runtime-based tool can claim zero-dep + memory-safe + formally-provable; that claim
is the product.
