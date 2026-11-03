//! Bash / shell front end: lossless lexer + CST parser + lowering, wired to the
//! shared IR through the [`LanguageFrontEnd`] seam.
//!
//! Shell is word-oriented and quote-rich rather than indentation- or
//! brace-structured. The lexer stays purely lossless — every byte is covered,
//! newlines are emitted as structural `NEWLINE` tokens, here-document bodies are
//! captured as covering tokens, and every quoting/expansion form is a single
//! token — and the parser recognizes function definitions, `{ … }` / `( … )`
//! groups, and `if/for/while/until/select/case` compounds, capturing command
//! lines as flat token runs. The lowering maps function definitions → `Function`,
//! top-level assignments → `Constant`, `source`/`.` → `IMPORTS`, and command
//! invocations → `CALLS` resolved against the project's function table. Shell has
//! no class-like constructs, so no `Type`/`HAS_METHOD`/`EXTENDS` are emitted.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Bash/shell language front end. Zero-sized: all state lives in the parse
/// trees and the lowering pass.
pub struct BashFrontEnd;

impl LanguageFrontEnd for BashFrontEnd {
    fn name(&self) -> &'static str {
        "bash"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["sh", "bash", "zsh"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once to resolve calls and includes); merge it into the
        // shared graph the pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn front_end_identity() {
        let fe = BashFrontEnd;
        assert_eq!(fe.name(), "bash");
        assert_eq!(fe.extensions(), &["sh", "bash", "zsh"]);
    }

    #[test]
    fn round_trips_a_representative_script() {
        // Comments, every string form, an expansion, a here-doc, two function
        // forms, an if/else, a for loop, and a `source` include.
        let src = "\
#!/usr/bin/env bash
# deploy helper
set -euo pipefail

APP_NAME=\"my-app\"
readonly VERSION='1.0.0'

log() {
    local level=\"$1\"; shift
    echo \"[$level] $*\" >&2
}

function deploy {
    log info \"deploying ${APP_NAME} v${VERSION}\"
    cat <<-EOF | tee /tmp/manifest
\t  name: ${APP_NAME}
\t  version: ${VERSION}
\tEOF
    if [[ -d ./build ]]; then
        rsync -a ./build/ \"$TARGET\"
    else
        echo \"nothing to deploy\" && exit 1
    fi
}

for env in dev staging prod; do
    deploy \"$env\" || log error \"failed: $env\"
done

source ./lib/common.sh
deploy
";
        let fe = BashFrontEnd;
        let tree = fe.parse("deploy.sh", src);
        assert!(
            tree.is_lossless(),
            "the parsed CST must reconstruct the source byte-for-byte"
        );
        // Lexing classified everything: no bytes fell into `error` tokens.
        assert_eq!(
            tree.root.error_token_count(),
            0,
            "representative script should lex cleanly with zero error tokens"
        );
    }
}
