//! PowerShell front end: lossless lexer + CST parser + lowering, wired to the
//! shared IR through the [`LanguageFrontEnd`] seam.
//!
//! PowerShell is statement/command-oriented (terminated by newlines or `;`, like
//! Bash) but also carries C#-style `class`/`enum` declarations. The lexer stays
//! purely lossless — every byte is covered, `#` line comments / `<# #>` block
//! comments / backtick line-continuations are retained as trivia, newlines are
//! emitted as structural `NEWLINE` tokens, every string/here-string and `$`
//! variable form is a single covering token, and unclassifiable bytes are
//! preserved as `error` tokens. The lowering maps `function`/`filter` →
//! `Function`, `class`/`enum` → `Type` (with an apt `type_kind`), class methods →
//! `Function` (+ `HAS_METHOD`), base lists → `EXTENDS`/`IMPLEMENTS`, top-level
//! script-scope assignments and class properties → `Constant`, `using` /
//! `Import-Module` → `IMPORTS`, and command / member invocations → `CALLS`,
//! reusing the shared conservative resolution rules. PowerShell is case-
//! insensitive, so keywords are matched case-insensitively throughout.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The PowerShell language front end. Zero-sized: all state lives in the parse
/// trees and the lowering pass.
pub struct PowerShellFrontEnd;

impl LanguageFrontEnd for PowerShellFrontEnd {
    fn name(&self) -> &'static str {
        "powershell"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["ps1", "psm1", "psd1"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    // `module_path` uses the default (flat) implementation: PowerShell scope comes
    // from `using`/`class` declarations in the source, not the file path.

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once to resolve calls and bases); merge it into the shared
        // graph the pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn front_end_identity() {
        let fe = PowerShellFrontEnd;
        assert_eq!(fe.name(), "powershell");
        assert_eq!(fe.extensions(), &["ps1", "psm1", "psd1"]);
    }

    #[test]
    fn round_trips_a_representative_script() {
        // Every comment form, every string form, a here-string, variables in their
        // scope/braced forms, a function with a param block, a class with a base
        // list / property / constructor / method, an enum, a pipeline, and both an
        // `if/else` and a `foreach` compound.
        let src = "\
#requires -Version 5
# deploy helper
<#
    .SYNOPSIS multi-line block comment
#>
using module Pester
using namespace System.Collections

$script:AppName = \"my-app\"
$global:Version = '1.0.0'

function Write-Log {
    param([string]$Level, [string]$Message)
    Write-Host \"[$Level] $Message `n done\" -ForegroundColor Green
}

filter Test-Even {
    if ($_ % 2 -eq 0) { $_ }
}

class Service : System.Object, IDisposable {
    [string]$Name
    static [int]$Count = 0

    Service([string]$name) {
        $this.Name = $name
    }

    [void] Deploy() {
        Write-Log -Level info -Message \"deploying $($this.Name)\"
        $manifest = @\"
name: ${script:AppName}
version: $global:Version
\"@
        if ($this.Name -match '^prod') {
            Get-Item ./build | Copy-Item -Destination \"$env:TARGET\"
        } else {
            Write-Log -Level warn -Message 'nothing to deploy'
        }
    }

    [void] Dispose() { }
}

enum Stage { Dev; Staging; Prod }

$svc = [Service]::new('web')
foreach ($stage in [Stage].GetEnumNames()) {
    $svc.Deploy()
}

Import-Module ./lib/Common.psm1
";
        let fe = PowerShellFrontEnd;
        let tree = fe.parse("deploy.ps1", src);
        assert!(
            tree.is_lossless(),
            "the parsed CST must reconstruct the source byte-for-byte"
        );
        assert_eq!(
            tree.root.error_token_count(),
            0,
            "representative script should lex cleanly with zero error tokens"
        );
    }

    #[test]
    fn handles_all_three_extensions_through_the_seam() {
        let fe = PowerShellFrontEnd;
        for (path, src) in [
            ("a.ps1", "function Get-A { 1 }\n"),
            (
                "b.psm1",
                "function Get-B { 2 }\nExport-ModuleMember -Function Get-B\n",
            ),
            (
                "c.psd1",
                "@{ ModuleVersion = '1.0'; RootModule = 'b.psm1' }\n",
            ),
        ] {
            let tree = fe.parse(path, src);
            assert!(tree.is_lossless(), "must round-trip: {path}");
        }
    }
}
