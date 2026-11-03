//! F# front end: lossless lexer + CST parser + lowering, wired to the shared IR
//! through the [`LanguageFrontEnd`] seam. Together with the C# and VB.NET front
//! ends this completes TrailTracker's first-class .NET coverage.
//!
//! F# is layout-sensitive (the offside rule), which makes a full grammar
//! expensive; this front end keeps the lexer fully lossless (every byte is a
//! token, trivia and nested `(* *)` block comments preserved, anything
//! unclassifiable is an `error` token) and parses *top-level* structure plus
//! `type` members with a pragmatic, layout-free rule: a declaration head is a
//! token in byte-column 0, an item runs to the next column-0 head (balanced
//! delimiter groups consumed whole), and a `type`'s indented `member` / `inherit`
//! / `interface` lines are recovered by scanning the item's top-level leaves. See
//! [`parser`] for the full rationale and [`lower`] for the honest ontology
//! mapping and the deliberate punts (indented `module X =` bodies, record fields,
//! DU cases, constructors, `USES_TYPE`).

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The F# language front end. Zero-sized: all state lives in the parse trees and
/// the lowering pass.
pub struct FSharpFrontEnd;

impl LanguageFrontEnd for FSharpFrontEnd {
    fn name(&self) -> &'static str {
        "fsharp"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["fs", "fsi", "fsx"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn module_path(&self, rel_path: &str) -> Vec<String> {
        module_path_for(rel_path)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once for the global function/type tables); merge it into
        // the shared graph the pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

/// Map a repo-relative `.fs`/`.fsi`/`.fsx` path to a fallback scope path: the
/// directory segments plus the file name with its extension stripped. This is
/// only a fallback — the lowering prefers the file's own `namespace`/`module`
/// header when present, since the source root that would be trimmed from the
/// front of the path is not known here.
fn module_path_for(rel: &str) -> Vec<String> {
    let mut parts: Vec<String> = rel.split('/').map(|s| s.to_string()).collect();
    if let Some(last) = parts.last_mut() {
        if let Some((head, _ext)) = last.rsplit_once('.') {
            *last = head.to_string();
        }
    }
    parts.retain(|s| !s.is_empty());
    parts
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn front_end_identity() {
        let fe = FSharpFrontEnd;
        assert_eq!(fe.name(), "fsharp");
        assert_eq!(fe.extensions(), &["fs", "fsi", "fsx"]);
    }

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("Program.fs"), vec!["Program"]);
        assert_eq!(
            module_path_for("src/Domain/Order.fs"),
            vec!["src", "Domain", "Order"]
        );
        assert_eq!(module_path_for("Library.fsi"), vec!["Library"]);
    }

    #[test]
    fn parse_round_trips_a_representative_file() {
        // A representative snippet: line + nested block comments, a namespace,
        // opens, a record with a member, a discriminated union, an abstract base
        // class, a derived class with `inherit` and an `interface` impl, a value
        // binding, a recursive function, a verbatim/triple/interpolated string,
        // and an `[<EntryPoint>]` attribute — must reconstruct byte-for-byte.
        let fe = FSharpFrontEnd;
        let src = "\
// A representative F# file.
(* a (* nested *) block comment *)
namespace Acme.Billing

open System
open System.Collections.Generic

/// A money record.
type Money =
    { Amount: decimal
      Currency: string }
    member this.IsZero = this.Amount = 0m

type Invoice =
    | Draft of Money
    | Sent of Money * DateTime

[<AbstractClass>]
type Ledger() =
    abstract member Total : unit -> decimal

type SqlLedger() =
    inherit Ledger()
    interface IDisposable with
        member this.Dispose () = ()
    override this.Total () = 0m

let taxRate : decimal = 0.07m

let verbatim = @\"C:\\temp\\out.txt\"
let triple = \"\"\"line one
line two\"\"\"
let interp = $\"rate = {taxRate}\"

let rec factorial n =
    if n <= 1 then 1 else n * factorial (n - 1)

[<EntryPoint>]
let main argv =
    let f = factorial 5
    printfn \"%d\" f
    0
";
        let tree = fe.parse("Billing.fs", src);
        assert!(tree.is_lossless(), "F# front end must round-trip source");
    }

    #[test]
    fn parse_is_lossless_on_fsx_script() {
        let fe = FSharpFrontEnd;
        let src = "#load \"Setup.fsx\"\nlet x = 1 + 2\nprintfn \"%d\" x\n";
        let tree = fe.parse("script.fsx", src);
        assert!(tree.is_lossless());
    }
}
