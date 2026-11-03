# VIR — the Language Front-End API

This is the precise contract for the **VIR substrate**: the seam where any number
of languages lower into the one shared IR ([the Atlas](./ir-atlas.md)). It is the
linchpin — everything downstream (graph, queries, rebuilds) depends on every
language producing the *same* node/edge vocabulary through the *same* seam.

Read this top-to-bottom once; then the [How to add a language](#how-to-add-a-language)
checklist is the operational recipe.

---

## 1. The front-end trait

A language front end owns exactly one language's path from raw bytes to the shared
IR. The trait lives in
[`src/lang/frontend.rs`](../src/lang/frontend.rs):

```rust
pub trait LanguageFrontEnd {
    fn name(&self) -> &'static str;
    fn extensions(&self) -> &'static [&'static str];
    fn parse(&self, path: &str, source: &str) -> ParseTree;
    fn module_path(&self, rel_path: &str) -> Vec<String> { Vec::new() } // default: flat
    fn lower(&self, input: &LoweredInput, graph: &mut Graph);
}
```

| Method | Responsibility | Contract |
|---|---|---|
| `name` | stable language tag, also the `language` node property (e.g. `"rust"`) | unique across the registry |
| `extensions` | file extensions claimed, **no leading dot** (e.g. `["rs"]`) | disjoint from every other front end¹ |
| `parse` | one file → lossless CST | see [§2 parse contract](#2-the-parse-contract) |
| `module_path` | repo-relative path → scope segments | pure; default is `[]` (single flat scope) |
| `lower` | a batch of parsed files → graph edges/nodes | see [§3 lowering contract](#3-the-lowering-contract) |

¹ One planned amendment: the MATLAB / Objective-C `.m` collision (roadmap
Phase 2) cannot be solved by disjoint extensions and will need a
content-sniffing hook on the trait (e.g. `fn claims(&self, path, source) ->
Confidence`). Until that amendment lands, extension sets stay strictly
disjoint and `.m` remains with one owner.

### Supporting types (same file)

```rust
pub struct SourceFile<'a> {            // one parsed file, ready to lower
    pub rel_path: String,
    pub module_path: Vec<String>,
    pub source: &'a str,               // borrowed from a live ParseTree
    pub root: &'a Node,
}

pub struct LoweredInput<'a> {          // the whole batch for one language
    pub package: &'a str,              // project / package name (manifest-derived)
    pub manifest_deps: &'a [String],   // declared deps; ignore if your lang has none
    pub files: Vec<SourceFile<'a>>,
}
```

### The registry

One central function lists every language, in a fixed order that is part of the
deterministic contract:

```rust
// src/lang/frontend.rs
pub fn front_ends() -> Vec<Box<dyn LanguageFrontEnd>> {
    vec![Box::new(crate::lang::rust::RustFrontEnd)]
}
```

The pipeline ([`src/pipeline/mod.rs`](../src/pipeline/mod.rs)) does the rest:
discovers every file under the root, dispatches each to the **first** front end
whose `extensions()` claim its extension, parses it (isolated with
`catch_unwind`), then calls each front end's `lower` once with the batch it owns
and **merges** every sub-graph into one shared `Graph` via `Graph::merge`. Files
no front end claims are skipped; a parse panic becomes an explicit
`parse_failed` `File` node, never a silent drop.

---

## 2. The parse contract

`parse` must honor the same invariants the property/fuzz harness
([`eval/src/property.rs`](../eval/src/property.rs)) enforces for *all* inputs:

1. **Lossless.** Concatenating every leaf token reproduces the source
   byte-for-byte (`ParseTree::is_lossless() == true`). Token spans are
   contiguous and cover 100% of the bytes.
2. **Trivia retained.** Whitespace and comments are emitted as `trivia` tokens,
   never dropped. Structurally significant whitespace (e.g. Python `NEWLINE`) is
   a *non-trivia* token.
3. **No silent drops.** Anything unclassifiable becomes an `error` token over its
   exact bytes; anything unrecognized at the item level becomes an `ErrorItem`
   node that still holds its tokens, plus a `Diagnostic`.
4. **Depth-guarded.** Mirror `MAX_DEPTH` (256) from the Rust parser: beyond the
   cap, stop recursing and consume the remainder as a flat balanced run, with a
   `depth_limit` diagnostic. A `catch_unwind` cannot catch a stack overflow — the
   guard is the real defense.
5. **Deterministic.** Parsing the same input twice yields identical output.
6. **std-only.** No external crates, ever. Hand-roll the lexer/parser. Study
   [`src/lang/rust/lexer.rs`](../src/lang/rust/lexer.rs) and
   [`src/lang/python/lexer.rs`](../src/lang/python/lexer.rs) as reference lossless
   lexers, and [`src/lang/rust/parser.rs`](../src/lang/rust/parser.rs) as the
   reference CST parser.

The CST shape itself ([`src/core/cst.rs`](../src/core/cst.rs)) is language-neutral:
`Node { kind, span, children }` with `&'static str` kinds. You invent your own
node-kind labels; nothing else needs to know them except your own `lower`.

---

## 3. The lowering contract

`lower` translates *your* CST into the shared ontology
([`src/ir/ontology.rs`](../src/ir/ontology.rs)). Rules:

1. **Emit only ontology kinds.** Use `ontology::node::*` and `ontology::edge::*`
   labels. Every emitted kind must already be documented in the Atlas
   ([`docs/ir-atlas.graph.jsonl`](./ir-atlas.graph.jsonl)) — the conformance test
   `atlas::tests::every_emitted_kind_is_documented_in_the_atlas` fails CI
   otherwise. If you need a kind that does not exist, follow
   [Extending the IR](./ir-atlas.md#extending-the-ir) **in the same PR**.
2. **Map honestly, never force-fit.** A Python `class` and a Rust `struct` are
   both `Type` nodes distinguished by a `type_kind` property and the `language`
   tag — not relabelled to look alike. (See Atlas design principle 2.)
3. **Tag the language.** Put `("language", Json::str(self.name()))` on every
   definition node so the same kind stays honest across languages.
4. **No fabricated targets.** Resolve an edge to a concrete definition only when
   it is unambiguous; preserve ambiguity as a `candidates` set; emit explicit
   `ExternalDependency` / `UnresolvedSymbol` nodes for unresolved references.
   There is no LLM in the airgapped runtime to guess.
5. **Deterministic IDs.** Node ids are structural and human-readable
   (`fn::crate::mod::name#<line>`, `type::…::Name`, `file::path`). Same input →
   same ids → byte-identical graph.
6. **Write into the shared graph.** You are handed `&mut Graph`. You may build a
   self-contained sub-graph and `graph.merge(sub)` (what the Rust front end does,
   because its resolution ladder needs the whole batch at once), or write
   directly. `merge` keeps first-seen nodes/edges, so no front end clobbers
   another and the result stays order-independent for a fixed input set.
7. **Unique ids per distinct definition.** `upsert`/`merge` collapse equal ids
   *silently* — a collision is invisible data loss, not an error. Two
   same-named definitions in different files (or on different lines) must get
   different ids; embed the relative file path and line when the qualified
   path alone can collide (`fn::qual#<rel-path>:<line>`, the pattern the Go
   build-tag-twin bug forced). When unique ids make edges harder to point at,
   the answer is an index + deferred resolution pass — never a looser id.

The relation lattice (`ontology::parent_relation`) is read-side only: it groups
concrete edges under super-relations (`DEPENDS`, `CONTAINMENT`, `SPECIALIZES`)
for coarse queries. Lowerings still emit the **concrete** edge label; they never
emit a super-relation.

---

## 4. How to add a language

Concrete, file-and-line steps. Example: adding a hypothetical `Foo` language with
extension `.foo`.

1. **Create the lexer.**
   `src/lang/foo/lexer.rs` — a lossless lexer satisfying [§2](#2-the-parse-contract).
   Model it on `src/lang/python/lexer.rs` (contiguous spans, trivia tokens,
   `error` fallback). Add `contiguous_coverage_is_lossless`-style tests.

2. **Create the parser.**
   `src/lang/foo/parser.rs` — produces the neutral CST, depth-guarded at
   `MAX_DEPTH`. Model it on `src/lang/rust/parser.rs`. Expose
   `pub fn parse(path: &str, source: &str) -> ParseTree`. Add a
   `parses_and_is_lossless` test and a `pathological_nesting_does_not_overflow`
   test.

3. **Create the module + front end.**
   `src/lang/foo/mod.rs`:
   - `pub mod lexer; pub mod parser;`
   - `pub struct FooFrontEnd;`
   - `impl LanguageFrontEnd for FooFrontEnd { … }` — wire `name → "foo"`,
     `extensions → &["foo"]`, `parse → parser::parse`, `module_path` (override
     only if `.foo` files form a directory/file scope), and `lower`.
   Model it on `src/lang/rust/mod.rs`.

4. **Write the lowering.**
   Put the CST→ontology pass with the front end (e.g. a `lower` helper in
   `src/lang/foo/`), honoring [§3](#3-the-lowering-contract). If you reuse the
   Rust whole-batch shape, build a sub-`Graph` and `graph.merge(sub)`.

5. **Register the module.**
   `src/lang/mod.rs` **line 9** area — add `pub mod foo;` alongside
   `pub mod csharp; pub mod python; pub mod rust;`.

6. **Register the front end (the one-line wire-up).**
   `src/lang/frontend.rs` **line 79** — extend the registry vec:
   ```rust
   pub fn front_ends() -> Vec<Box<dyn LanguageFrontEnd>> {
       vec![
           Box::new(crate::lang::rust::RustFrontEnd),
           Box::new(crate::lang::foo::FooFrontEnd),   // <-- added
       ]
   }
   ```
   This is the *only* edit to shared code. The pipeline now discovers, dispatches,
   parses, and merges `.foo` files automatically — no other front end is touched.

7. **Document any new IR kinds.** If your `lower` emits a kind not already in the
   Atlas, add it to `src/ir/ontology.rs`, `docs/ir-atlas.md` (table + changelog),
   and `docs/ir-atlas.graph.jsonl`, and place it in the lattice via
   `parent_relation` (`src/ir/ontology.rs` line 91). Reuse existing kinds first.

8. **Add a corpus case (optional but recommended).** Drop a small vendored
   project under `eval/corpus/<name>/` and run `regress --update` to bless its
   golden after review. The existing Rust goldens must stay byte-identical.

9. **Verify the full gate:**
   ```
   cargo fmt --all -- --check
   cargo clippy --workspace --all-targets -- -D warnings
   cargo test --workspace
   cargo run --release -p trailtracker-eval --bin regress -- --root .
   ```

10. **Enter external verification.** Add the language to
    [`eval/corpus-manifest.tsv`](../eval/corpus-manifest.tsv) with a real
    corpus repo — Tier B (report-only) at minimum, using the best available
    oracle (`ctags` if nothing canonical exists) — and run the `oracle` bin
    against it locally once to see where you actually stand. A language
    without a manifest row has no external check at all; that is no longer an
    acceptable end state for "added". Promotion to Tier A follows the
    promotion protocol: local 0-diff against the pinned repo *before* the
    manifest flips, CI confirms.

### What you must NOT touch

- Existing `ontology::edge::*` / `node::*` constants or their emitted labels.
- Existing goldens under `eval/golden/*.jsonl` (they gate the Rust front end —
  any change there is a regression unless deliberately blessed).
- Any other language's module. Adding `Foo` is steps 1–6 in `src/lang/foo/` plus
  two one-line registrations.
