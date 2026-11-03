//! Tcl / Tk front end: lossless lexer + CST parser + lowering, wired to the
//! shared IR through the [`LanguageFrontEnd`] seam.
//!
//! Tcl is the canonical "everything is a command" language: a script is a list of
//! commands, a command is words separated by whitespace, and structure
//! (`proc`, `namespace eval`, control flow) is just commands whose final argument
//! is a brace-quoted *script body*. The lexer stays purely lossless — every byte
//! is covered, `newline`/`;` are structural separators, and every quoting/
//! substitution form (`{ }`, `[ ]`, `" "`, `$…`) is a single covering token — and
//! the parser descends into the body of body-bearing commands so nested procs and
//! calls become visible. The lowering maps `proc` → `Function`, `namespace eval`
//! → `Module`, `package require` / `source` → `IMPORTS` (+ `ExternalDependency`),
//! top-level `set` → `Constant`, and command invocations → `CALLS` resolved against
//! the project's proc table. Plain Tcl has no class-like constructs, so no
//! `Type`/`HAS_METHOD`/`EXTENDS` are emitted (object systems like TclOO/itcl are a
//! documented punt — see [`lower`]).

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Tcl/Tk language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct TclFrontEnd;

impl LanguageFrontEnd for TclFrontEnd {
    fn name(&self) -> &'static str {
        "tcl"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["tcl", "tk"]
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
        let fe = TclFrontEnd;
        assert_eq!(fe.name(), "tcl");
        assert_eq!(fe.extensions(), &["tcl", "tk"]);
    }

    #[test]
    fn round_trips_a_representative_script() {
        // Comments, every quoting form, a variable + command substitution, two
        // proc forms, a namespace, a package require, a source include, and the
        // common control structures.
        let src = "\
#!/usr/bin/env tclsh
# deploy helper

package require Tk 8.6

set APP_NAME \"my-app\"
set VERSION {1.0.0}

proc log {level msg} {
    puts \"\\[$level\\] $msg\"
}

namespace eval ::deploy {
    variable target /tmp/out
    proc run {env} {
        log info \"deploying ${::APP_NAME} to $env\"
        set files [glob -nocomplain ./build/*]
        if {[llength $files] > 0} {
            foreach f $files {
                puts \"copy $f\"
            }
        } else {
            log error \"nothing to deploy\"
        }
    }
}

while {1} {
    ::deploy::run prod
    break
}

source ./lib/common.tcl
log info done
";
        let fe = TclFrontEnd;
        let tree = fe.parse("deploy.tcl", src);
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

    #[test]
    fn lossless_round_trip_on_edge_cases() {
        // The lossless guarantee must hold for hostile and degenerate inputs too.
        for src in [
            "",
            "\n",
            "   \t  \n",
            "# only a comment",
            "puts foo#bar  ;# trailing\n",
            "set s \"unterminated string\n",
            "proc f {unterminated brace\n",
            "set x [expr {1 + 2}]\n",
            "λ {set ☃ €}\n",
            "proc a {} {proc b {} {proc c {} {puts deep}}}\n",
            "set L {a {b {c {d}}}}\n",
        ] {
            let fe = TclFrontEnd;
            let tree = fe.parse("edge.tcl", src);
            assert!(tree.is_lossless(), "must round-trip byte-for-byte: {src:?}");
        }
    }
}
