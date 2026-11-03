# Architecture

TrailTracker is graph-directed, parser-gated.

The architect's target is the graph: a complete ontology-backed representation
of inherited codebases. The implementation cannot honestly build that graph
until source files have gone through full-grammar parsing, so parser correctness
is the first engineering gate.

## Pipeline

1. **Discover Input**: walk the codebase, preserve file paths, extensions,
   sizes, project manifests, and language candidates.
2. **Select Grammar**: map each source/project file to the full authoritative
   grammar: Rust first, then C#, MSBuild project files, Cargo/TOML manifests,
   and Visual Studio solution files.
3. **Lex Full Fidelity**: produce tokens plus trivia, comments, directives,
   spans, and diagnostics.
4. **Parse Full Grammar**: produce a lossless AST. No canonical code facts are
   emitted from partial parsers.
5. **Resolve Project Semantics**: build module/project structure, imports,
   dependencies, symbol tables, type declarations, type references, and call
   targets where they can be proven. Unresolved external items remain explicit.
6. **Lower To IR/Ontology**: map language-specific ASTs into a common ontology
   rooted in lambda-calculus-accessible parts: bindings, abstractions,
   applications/calls, values, types, modules, files, packages, and effects.
7. **Build Canonical Graph**: emit graph nodes and relationships for files,
   modules, functions, types, calls, dependencies, and external dependencies,
   with source locations and language-specific properties.
8. **Linearize And Store**: produce deterministic graph output that is readable
   by humans and LLMs. JSONL is the baseline stream format; SQLite/recursive CTE
   support remains a research/import target unless implemented internally.
9. **Mindmap Ontology**: extract codebase-level features into a second ontology
   that grows across processed codebases and can support traditional ML in
   airgapped environments.
10. **Eval And Verify**: run golden tests, self-analysis, A/B processing
    changes, performance measurements, and formal verification where practical.

## Non-Negotiables

- The milestone-1 product acceptance is a graph of this repo.
- The Rust AST parser is the first engineering gate toward that milestone.
- Partial parser facts do not become canonical code-entity facts.
- Partial lexer coverage must be reported as partial.
- Every grammar rule should carry source traceability.
- Parser diagnostics are AST/parser facts before they are graph facts.
- Later filtering must never be required to recover source-level information.
- External dependencies or unresolved external items get logical graph nodes,
  not silent omission.
- Runtime behavior must be airgap-safe and std-only; any needed behavior is
  implemented locally.

## Runtime Constraint

The shipped runtime is std-only. If a crate has behavior TrailTracker needs, that
behavior is implemented locally instead of taking the dependency.
