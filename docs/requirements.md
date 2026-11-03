# Requirements

Authoritative project requirements come from the architect-provided prompts in
`docs/prompts/`. This document restates those requirements as implementation
constraints for the codebase.

## Source Of Truth

- The architect owns product direction and requirements.
- Codex implements and verifies the code. It must not invent downstream
  artifacts and present them as completed capabilities.
- `docs/prompts/initial-prompt-question-answers.md` is requirement input.
- `docs/prompts/initial-prompt.md` is currently empty and reserved for the
  original prompt text.

## Mission

TrailTracker is a local Rust system that processes inherited codebases and emits an ontology-backed graph that
can support reasoning and eventual isomorphic rebuilds into another language.

The system runs locally, in airgapped environments, including defense hardware.
Supply-chain attacks are treated as a hard design constraint.

## Scope

- First-class Rust.
- First-class C#.
- .NET support includes C# project-system metadata: MSBuild project files,
  solution files, package/assembly references, and related dependency structure.

## Dependency Policy

- Runtime code is std-only by default.
- If a crate has needed behavior, find the relevant behavior and reimplement it
  locally.
- External dependencies are not acceptable in the shipped airgapped runtime.
- Verification tooling may be evaluated separately, but anything shipped inside
  the airgap must satisfy the dependency policy.

## Milestone 1 Acceptance

TrailTracker can analyze the TrailTracker repository itself and emit a graph
containing:

- Files, including extension, path, size, language, and line/source properties.
- Modules.
- Functions.
- Types and type usage.
- Calls as relationships.
- Dependencies as relationships.
- Logical external dependency nodes when dependencies are not held in the
  project, with `external=true` or equivalent.
- Source-location properties such as file, line, column, span, and language.

This acceptance criterion depends on the Rust parser being real. The current
code must not emit fake function/type/call graph facts from partial parsing.

## Grammar Requirement

Full grammar is required. Starting broad preserves future options; filtering and
scope reduction are downstream choices. If TrailTracker fails to capture the
full AST foundation, graph quality will be structurally limited.

Required grammar families:

- Rust Reference grammar.
- C# language specification grammar, including lexical, syntactic, unsafe, and
  preprocessor grammar.
- Cargo/TOML manifest grammar for Rust project metadata.
- MSBuild XML project grammar for .NET project metadata.
- Visual Studio solution-file grammar.

## Ontology Requirement

The canonical graph should be built from an intermediate representation that
recognizes language-specific parts while allowing cross-language reasoning.

The core ontology starts with lambda-calculus-accessible concepts:

- Bindings.
- Abstractions/functions/methods.
- Applications/calls.
- Values/constants/literals.
- Types, type declarations, type parameters, and type usage.
- Scopes/environments.

Practical codebase concepts are also required:

- Files and file extensions.
- Directories and project structure.
- Modules/namespaces.
- Imports/uses/references.
- Packages/crates/assemblies/projects.
- Internal and external dependencies.

## Mindmap Ontology

A second ontology, the mindmap, grows from processed codebases. It classifies
what kind of codebase TrailTracker is working with and supports learning without
assuming LLM availability in the airgapped environment. Traditional ML
techniques may be used if they satisfy the dependency policy.

## Output And Storage

- Graph output is the canonical product artifact.
- Output must be deterministic and linearizable for LLM consumption outside the
  airgap or where LLMs are available.
- JSON/JSONL remain baseline portable formats.
- SQLite with recursive CTEs is a candidate graph query/import target, but not a
  runtime dependency unless reimplemented or otherwise made compliant.
- Speed and low memory overhead matter.

## Eval And Verification

- Use eval loops to test graph quality and protect against regressions.
- A/B test major processing changes.
- Measure speed, memory, and graph quality.
- Use golden fixtures, self-analysis, and corpus tests.
- Formal verification is desired for critical parts where practical.
- Defense/RTS code validation requires traceability, measurements, and
  conservative failure modes.

## Current Implementation Status

Implemented:

- Parser-first CLI gate.
- AST/span structures.
- Grammar source map.
- Partial Rust lexer with explicit `coverage="partial"` output.

Not implemented:

- Full Rust lexer.
- Full Rust parser.
- Rust AST JSON output.
- AST-to-IR lowering.
- Canonical graph output.
- C#/.NET parsers.
- Mindmap ontology.
