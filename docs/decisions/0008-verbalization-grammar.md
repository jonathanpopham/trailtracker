# 0008 — Verbalization grammar: the retrieval-safe sentence contract

- **Status:** Accepted
- **Date:** 2026-07-08

## Context

The verbalizer epic (E-V) will render the recovered graph as deterministic
human-readable sentences built from vocabulary templates with variable slots —
a pattern with proven prior art in production systems that delivered large
code graphs to LLMs via targeted context. That pattern worked because the
sentences were *machine-grade prose*: uniform, self-contained, and drawn from
a closed vocabulary, so any subset of sentences survived arbitrary context
windowing and the whole output language was enumerable.

This ADR is written **before** the template engine exists, deliberately. The
quality bar must be a contract the engine is built against, not a style guide
negotiated after templates ship. Two consumers drive every rule:

1. **Retrieval.** Sentences will be chunked, embedded, ranked, and windowed
   by machinery that knows nothing about their neighbors. A sentence that
   leans on its neighbor ("it also imports…") silently corrupts whatever
   window it lands in.
2. **Determinism.** The corpus regression gate pins outputs byte-for-byte.
   Prose is only gate-able if the same graph always yields the same
   sentences in the same order, and if the space of possible sentences is
   closed under a registered vocabulary.

## Decision

The unit of the contract is the **sentence**. A verbalized document is a
sequence of sentences: an optional **glossary prelude** (handle definition
lines) followed by body sentences. Every sentence must satisfy rules R1–R9
below. A conformance checker
([`src/verbalize/grammar.rs`](../../src/verbalize/grammar.rs)) enforces each
rule mechanically; V1's template outputs must pass it in CI.

Throughout: **backticks mark code spans.** Anything inside `` `…` `` is a
code identifier, path, or literal, and is exempt from the lexical rules
(R1, R2, R4, R6, R7) — the escape hatch is explicit and visible, never
inferred. Unquoted tokens that are structurally code-shaped (contain `_`,
`/`, `::`, `#`, an internal `.`, mixed case, or letters+digits) are also
treated as identifiers.

### R1 — Standalone sentences: no pronouns, no deixis

Every sentence names its subjects in full (or by glossary handle, R3), every
time. Pronouns (`it`, `its`, `they`, `this`, `these`, `those`, …) and deictic
words that point outside the sentence (`former`, `latter`, `above`, `below`,
`following`, `there`, `previously`, …) are forbidden.

*Rationale:* retrieval windows sentences arbitrarily. A pronoun's referent
lives in a neighboring sentence that may not be in the window; the sentence
then reads as fluent prose while carrying zero (or wrong) information.

- PASS: `D1 imports 12 files from D2.`
- FAIL: `It imports 12 files from the former.` — three dangling references
  in one sentence.
- Not flagged: `src/it/mod.rs`, `` `commit_it` ``, the acronym `IT` — code
  identifiers, paths, code spans, and all-caps acronyms are exempt.

### R2 — One fact per sentence

A sentence states exactly one fact. The conjunction budget is: **at most one
`and`/`or`, and it may only join values, never facts.** Fact-joining words
(`but`, `while`, `however`, `because`, `also`, `then`, …) and semicolons are
forbidden outright. Mechanically, the checker also counts predicates: at most
one verb from the registered verb list may follow a subject (handle, name, or
identifier) in a single sentence.

*Rationale:* one fact per sentence means retrieval rank orders facts, not
paragraphs; a window of k sentences carries exactly k facts; and dropping any
sentence drops exactly one fact.

- PASS: `D1 imports 12 files and 3 types.` — one `and`, joining two values
  of one fact.
- FAIL: `D1 imports 12 files and D2 exports 4 files.` — one `and`, but two
  predicates: two facts smuggled into one sentence.
- FAIL: `D1 imports 12 files; D2 exports 4 files.` — semicolon joins facts.

### R3 — Handle discipline: glossary-introduced, deterministic

Short stable handles exist so R1 (full names) and R8 (length budget) can
coexist. The handle grammar is **one ASCII uppercase letter + 1–4 digits, no
leading zero** (`D1`, `F3`, `C12`). A handle may be used only after a
glossary line introduces it:

```
D1 = the `parse` domain (3,392 nodes)
```

Handle assignment is deterministic: **assignment order = value ranking**
(the largest domain is `D1`, the next `D2`, …), so per prefix the numbering
is dense — `1, 2, 3, …` with no gaps — and the same graph always yields the
same handles.

*Rationale:* a bare `D1` in a retrieved sentence is only self-contained if
the glossary line that defines it is deterministically co-retrievable; a
handle nobody introduced is a pronoun with a serial number.

- PASS: `D1 = the `` `parse` `` domain (3,392 nodes)` … later …
  `D1 contains 3,392 nodes of 7,340 nodes.`
- FAIL: `D9 exports 4 types.` — no glossary line introduces `D9`.
- FAIL: using `D2` in sentence 0 when its glossary line is sentence 3.
- Known collision: metric names shaped like handles (`F1` the score) belong
  to the handle namespace. Templates must write `f1-score` or backtick the
  metric; the checker cannot read minds.

### R4 — Numbers carry denominators or units

Every number is anchored: a unit word after it (`12 files`), a denominator
(`365 of 18,155 nodes`), a metric name before it (`fan-in 365`,
`depth 3`), or a percent sign (`45%`). Justified exceptions: line numbers
and ranges in spans (`line 42`, `lines 481-488`), version strings
(`1.2.3`), and code literals in backticks (`` returns `0` ``).

*Rationale:* a bare number in an isolated sentence is unfalsifiable — `365`
of what, out of how many? Denominators are what let a model reason about
scale without seeing the whole document.

- PASS: `F1 has fan-in 365 of 18,155 nodes.`
- FAIL: `F1 has fan-in 365.` — 365 out of how many?
- PASS: `F1 spans lines 481-488.` — span ranges are self-anchoring.

### R5 — Deterministic ordering

Output order is a function of the graph, never of iteration order:
**domain-major** (all facts about `D1`, then all about `D2`), **define
before reference** (a glossary line precedes every use of its handle; `D2`'s
facts never precede `D1`'s), and **stable tie-breaks** (rank, then
lexicographic name). Mechanically the checker verifies: glossary numbering
is dense and ascending per prefix; glossary lines appear in declaration
order; body sentences that lead with a handle are non-decreasing per prefix.
The body-ordering check takes a declared ordering key
([`OrderingKey`](../../src/verbalize/grammar.rs)); `DomainMajor` is the
default and `None` disables only the body check.

*Rationale:* determinism makes prose gate-able (byte-for-byte goldens) and
diffable (a graph change moves exactly the sentences about the changed
facts). Define-before-reference means any prefix of the document is also a
valid document.

- PASS: `D1 …` sentences, then `D2 …` sentences.
- FAIL: a `D1`-subject sentence appearing after `D2`-subject sentences —
  the domain was revisited, so ordering leaked iteration state.

### R6 — Facts only: no quality adjectives, no hedges, no imperatives

Quality adjectives (`clean`, `elegant`, `robust`, `huge`, …), hedges and
vague quantifiers (`probably`, `roughly`, `several`, `many`, `might`,
`should`, …), and imperative openers (`Note`, `Consider`, `See`, …) are
forbidden. Superlatives over measured values (`largest`, `deepest`) are
facts and stay; vague magnitude words (`large`, `big`) are opinions and go.

*Rationale:* the verbalizer reports a measured graph. Adjectives of quality
are unfalsifiable, hedges convert facts into non-facts, and imperatives
address a reader the sentence cannot assume exists. Every claim must be
checkable against the graph.

- PASS: `D1 is the largest domain: 3,392 nodes of 7,340 nodes.`
- FAIL: `D1 is a huge domain and probably imports too many files.`

### R7 — Vocabulary closure: the output language is enumerable

Every token in a body sentence is one of: a **scaffold word from the
registered vocabulary** (the closed word lists in
[`grammar.rs`](../../src/verbalize/grammar.rs), exposed by
`grammar::vocabulary()`), a **code identifier or path**, a **number**, a
**handle**, or a **capitalized proper name of a code entity**. Nothing else.
Growing the language = a reviewed edit to the vocabulary constants.

*Rationale:* this is the "deterministically mapped vocabulary" property the
prior art proved out: if every non-slot token comes from a registered list,
the entire possible output language is enumerable, testable, and immune to
drift. A template cannot quietly start editorializing, because the words it
would need do not exist.

- PASS: `D1 depends on 3 domains.` — scaffold + handle + anchored number.
- FAIL: `D1 frobnicates the dependency situation.` — `frobnicates` and
  `situation` are not registered; the sentence is outside the language.

### R8 — Length budget

A sentence is at most **160 characters** (`MAX_SENTENCE_CHARS`), counted in
Unicode scalar values. Handles (R3) exist precisely so full-name repetition
(R1) fits the budget.

*Rationale:* embedding quality degrades on long multi-clause strings, and a
sentence pushing past 160 chars almost always contains a second fact (R2)
or an unhandled long name (R3).

- PASS: any sentence in this ADR's examples.
- FAIL: a 200-char sentence chaining a path, three counts, and a clause.

### R9 — Encoding and shape safety

Sentences are single-line, non-empty, valid UTF-8 with: no control
characters (no tabs, no embedded newlines), no zero-width or bidirectional
control codepoints (U+200B–U+200F, U+202A–U+202E, U+2066–U+2069, U+FEFF),
and balanced backticks (an unpaired backtick corrupts code-span parsing for
the rest of the sentence).

*Rationale:* bidi and zero-width codepoints are an injection surface
(sentences quote identifiers from analyzed repos — hostile input); unpaired
backticks silently flip what is and is not exempt from R1–R7.

- PASS: `` F1 calls `render` 3 times of 9 call sites. ``
- FAIL: the same sentence with a U+202E in the identifier, or a lone `` ` ``.

## The checker

`src/verbalize/grammar.rs` (std-only, crate-wide `forbid(unsafe_code)`):

```rust
pub fn check(sentences: &[&str], glossary: &[Handle]) -> Vec<Violation>
pub fn check_with(sentences: &[&str], glossary: &[Handle], ordering: OrderingKey) -> Vec<Violation>
```

- `Handle { handle, expansion }` — the declared glossary, in assignment
  order.
- `Violation { rule: RuleId, sentence, span, message, hint }` — same finding
  discipline as `doctor` and `arch-verify`: which rule fired, where (byte
  span within the sentence; glossary-level findings use
  `GLOSSARY_SENTENCE`), what happened, and how to fix it. `to_json()`
  emits the deterministic JSONL shape.
- The checker is a pure function: same input, same violations, same order
  (sorted by sentence, span, rule, message). Its own determinism is under
  test.

Mechanical approximations are documented in the module: predicate counting
uses subject–verb adjacency; "value vs fact" for `and` is enforced via the
predicate budget; R5 checks the enforceable subset (dense glossary
numbering, declaration-order prelude, non-decreasing leading handles) of
the full ordering principle.

## Consequences

- V1 builds templates **against** this contract: every template's rendered
  output must produce zero violations in tests, and the registered
  vocabulary is the only place new scaffold words can come from.
- The checker is intentionally strict with an explicit escape hatch:
  anything that is code goes in backticks. False positives are resolved by
  quoting, not by loosening lexicons.
- Not in scope here (V1's job): the template registry, slot filling, the
  `verbalize` command, and any renderer. This module stays a leaf:
  `verbalize::grammar` has no dependencies beyond `core::json`.
