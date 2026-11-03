//! AWK front end: lossless lexer + CST parser + lowering, wired to the shared IR
//! through the [`LanguageFrontEnd`] seam.
//!
//! AWK is a small, line-oriented pattern–action language. The lexer stays purely
//! lossless — every byte is covered, newlines are emitted as structural `NEWLINE`
//! tokens, `#` line comments and backslash-newline continuations are trivia, every
//! string/regex/number is a single token, and the `/`-regex-vs-division ambiguity
//! is resolved with the standard previous-token heuristic. The parser recognizes
//! `function name(args) { … }` definitions and `pattern { action }` rules (with
//! brace blocks parsed recursively and depth-guarded), capturing pattern
//! expressions and action bodies as flat token runs.
//!
//! Lowering maps **honestly and sparsely**, because AWK is a small language:
//!   - `function name(args) { … }` → `Function` (with `arity`);
//!   - a `name(…)` user-function call (no space before the paren) → `CALLS`,
//!     resolved against the project's function table, else an explicit
//!     `builtin`/`external`/`ambiguous` `UnresolvedSymbol`.
//!
//! `BEGIN`/`END`/pattern–action blocks are kept losslessly in the CST as rules but
//! are not definitions; their bodies are scanned for calls (attributed to the
//! file, since AWK rules are file-scope).
//!
//! ## Honest punts (deliberately *not* emitted)
//! - **No `Type` / `HAS_METHOD` / `IMPLEMENTS` / `EXTENDS`.** AWK has no
//!   class/struct/interface concept.
//! - **No `Constant`.** AWK globals are implicit — a bare assignment anywhere
//!   creates a dynamically-scoped global; there is no honest top-level declaration
//!   to point at (unlike a shell `NAME=value` line), so none is fabricated.
//! - **No `IMPORTS` / `DEPENDS_ON`.** Standard `awk` has no import system. gawk's
//!   `@include` / `@load` directives are *not* recognized (they would lex as an
//!   `error` token for `@` plus an ident, still losslessly covered) — a future
//!   extension could map `@include` → `IMPORTS`.
//! - **No statement-level structure.** Action bodies are flat token runs inside
//!   brace `Block`s, not parsed statements; call detection reads the raw tokens.
//! - **Built-in vs. user calls** are distinguished, but a built-in used without
//!   parentheses (e.g. bare `length`) is not recorded as a call (only `name(` call
//!   syntax is).
//!
//! ## Activation
//! Per the task's scope constraint, this module edits nothing outside
//! `src/lang/awk/`. To make the pipeline discover `.awk` files it still needs the
//! two standard one-line registrations from `docs/vir.md`: `pub mod awk;` in
//! `src/lang/mod.rs` and `Box::new(crate::lang::awk::AwkFrontEnd)` in the
//! `front_ends()` registry in `src/lang/frontend.rs`.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The AWK language front end. Zero-sized: all state lives in the parse trees and
/// the lowering pass.
pub struct AwkFrontEnd;

impl LanguageFrontEnd for AwkFrontEnd {
    fn name(&self) -> &'static str {
        "awk"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["awk"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once to resolve calls); merge it into the shared graph.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn front_end_identity() {
        let fe = AwkFrontEnd;
        assert_eq!(fe.name(), "awk");
        assert_eq!(fe.extensions(), &["awk"]);
    }

    #[test]
    fn round_trips_a_representative_program() {
        // A shebang, comments, every string/regex/number form, BEGIN/END, a
        // pattern–action rule, a range pattern, and a function with a call.
        let src = "\
#!/usr/bin/awk -f
# field summarizer
BEGIN {
    FS = \",\"
    OFS = \"\\t\"
    total = 0
}

/^#/ { next }                 # skip comment lines

$1 ~ /^[0-9]+(\\.[0-9]+)?$/ {
    total += $1
    seen[$2]++
    x = total / NR            # division, not a regex
}

NR == 1, /END_OF_HEADER/ {    # a range pattern
    print \"header:\", $0
}

function summarize(name,    i, n) {
    n = 0
    for (i in seen)
        n += seen[i]
    printf(\"%s has %d entries\\n\", name, n)
    return n
}

END {
    print \"total =\", total
    summarize(\"report\")
}
";
        let fe = AwkFrontEnd;
        let tree = fe.parse("summary.awk", src);
        assert!(
            tree.is_lossless(),
            "the parsed CST must reconstruct the source byte-for-byte"
        );
        assert_eq!(
            tree.root.error_token_count(),
            0,
            "representative program should lex cleanly with zero error tokens"
        );
    }
}
