//! The language front-end abstraction: the seam every language plugs into.
//!
//! A front end owns exactly one language's path from raw bytes to the shared IR:
//! it declares the file extensions it claims, parses a file into the lossless CST
//! ([`crate::core::cst`]), and lowers a batch of those parsed files into the
//! canonical graph ([`crate::graph`]). Everything below the seam — spans, the
//! CST, the ontology, the graph — is language-neutral, so adding a language
//! touches only its own module plus the one-line registry entry in
//! [`front_ends`]. No existing front end is edited to add another.
//!
//! Lowering takes a *batch* (`LoweredInput`), not a single file, because
//! cross-file symbol resolution (e.g. the Rust call-resolution ladder) needs the
//! whole compilation unit in hand. Each front end writes into the shared graph
//! that the pipeline hands it; the pipeline runs the front ends in the fixed
//! registry order, so the merged result is deterministic.

use crate::core::cst::{Node, ParseTree};
use crate::graph::Graph;

/// One parsed source file, ready to lower. Borrows its source text and CST root
/// from a [`ParseTree`] the pipeline keeps alive for the duration of lowering.
///
/// `module_path` is the language's notion of the file's scope path (for Rust, the
/// crate-relative module segments, e.g. `["core", "span"]`); it is derived by the
/// owning front end via [`LanguageFrontEnd::module_path`], so the convention stays
/// with the language that defines it.
pub struct SourceFile<'a> {
    pub rel_path: String,
    pub module_path: Vec<String>,
    pub source: &'a str,
    pub root: &'a Node,
}

/// The batch of one language's files for a single project, plus the project-level
/// facts a lowering may need. `package`/`manifest_deps` come from the project
/// manifest (currently the Cargo reader in the pipeline); front ends for
/// languages without a manifest concept simply ignore them.
pub struct LoweredInput<'a> {
    pub package: &'a str,
    pub manifest_deps: &'a [String],
    pub files: Vec<SourceFile<'a>>,
}

/// A complete language front end. Implementors live under `crate::lang::<lang>`
/// and are listed once in [`front_ends`].
pub trait LanguageFrontEnd {
    /// Stable language tag, also written as the `language` property on emitted
    /// nodes (e.g. `"rust"`). Must be unique across the registry.
    fn name(&self) -> &'static str;

    /// File extensions this front end claims, **without** the leading dot (e.g.
    /// `["rs"]`). The pipeline dispatches a file to the first registered front
    /// end that [`LanguageFrontEnd::claims`] it; the default `claims` matches
    /// against this list.
    fn extensions(&self) -> &'static [&'static str];

    /// Whether this front end claims `rel_path` (repo-relative, `/`-separated).
    /// The default matches the file name's final extension against
    /// [`LanguageFrontEnd::extensions`]. Front ends whose files are not
    /// identified by a simple extension — compound suffixes like
    /// `.flow-meta.xml`, or extension-less names like `Dockerfile` — override
    /// this instead of (or in addition to) listing extensions. Overrides must
    /// stay pure and deterministic: dispatch order is part of the output
    /// contract.
    fn claims(&self, rel_path: &str) -> bool {
        let name = rel_path.rsplit('/').next().unwrap_or(rel_path);
        match name.rsplit_once('.') {
            Some((stem, ext)) if !stem.is_empty() => self.extensions().contains(&ext),
            _ => false,
        }
    }

    /// Parse one file into the lossless CST. Must round-trip the source
    /// byte-for-byte (`ParseTree::is_lossless`) and be depth-guarded against
    /// hostile nesting — the pipeline additionally isolates this call with
    /// `catch_unwind`.
    fn parse(&self, path: &str, source: &str) -> ParseTree;

    /// Derive the file's scope/module path from its repo-relative path. The
    /// default is empty (a flat, single-scope language); languages with a
    /// directory-or-file module convention override it.
    fn module_path(&self, _rel_path: &str) -> Vec<String> {
        Vec::new()
    }

    /// Lower a batch of this language's parsed files into `graph`, emitting only
    /// [`crate::ir::ontology`] kinds. Called once per project with every file the
    /// front end claimed; cross-file resolution may assume the whole batch.
    fn lower(&self, input: &LoweredInput, graph: &mut Graph);

    /// Lower with the opt-in CPG overlay (ADR-0003): the same base facts as
    /// [`LanguageFrontEnd::lower`] plus intra-function `Statement` nodes and
    /// `FLOWS_TO`/`DATA_DEP` edges. The default is the plain lowering — a
    /// front end without a CPG simply contributes its base graph, so the
    /// overlay can be adopted one language at a time without touching the
    /// others.
    fn lower_cpg(&self, input: &LoweredInput, graph: &mut Graph) {
        self.lower(input, graph);
    }
}

/// The central registry: every language TrailTracker can analyze, in a fixed
/// order. Adding a language is a single line here (see `docs/vir.md`). The order
/// is the dispatch + lowering order, so it is part of the deterministic contract.
pub fn front_ends() -> Vec<Box<dyn LanguageFrontEnd>> {
    vec![
        Box::new(crate::lang::rust::RustFrontEnd),
        Box::new(crate::lang::python::PythonFrontEnd),
        Box::new(crate::lang::bash::BashFrontEnd),
        Box::new(crate::lang::c::CFrontEnd),
        Box::new(crate::lang::cpp::CppFrontEnd),
        Box::new(crate::lang::csharp::CSharpFrontEnd),
        Box::new(crate::lang::go::GoFrontEnd),
        Box::new(crate::lang::java::JavaFrontEnd),
        Box::new(crate::lang::javascript::JavaScriptFrontEnd),
        Box::new(crate::lang::kotlin::KotlinFrontEnd),
        Box::new(crate::lang::lua::LuaFrontEnd),
        Box::new(crate::lang::php::PhpFrontEnd),
        Box::new(crate::lang::ruby::RubyFrontEnd),
        Box::new(crate::lang::scala::ScalaFrontEnd),
        Box::new(crate::lang::swift::SwiftFrontEnd),
        Box::new(crate::lang::typescript::TypeScriptFrontEnd),
        Box::new(crate::lang::haskell::HaskellFrontEnd),
        Box::new(crate::lang::dart::DartFrontEnd),
        Box::new(crate::lang::elixir::ElixirFrontEnd),
        Box::new(crate::lang::clojure::ClojureFrontEnd),
        Box::new(crate::lang::julia::JuliaFrontEnd),
        Box::new(crate::lang::elm::ElmFrontEnd),
        Box::new(crate::lang::zig::ZigFrontEnd),
        Box::new(crate::lang::r::RFrontEnd),
        Box::new(crate::lang::perl::PerlFrontEnd),
        Box::new(crate::lang::erlang::ErlangFrontEnd),
        Box::new(crate::lang::groovy::GroovyFrontEnd),
        Box::new(crate::lang::nix::NixFrontEnd),
        Box::new(crate::lang::fortran::FortranFrontEnd),
        Box::new(crate::lang::powershell::PowerShellFrontEnd),
        Box::new(crate::lang::verilog::VerilogFrontEnd),
        Box::new(crate::lang::ada::AdaFrontEnd),
        Box::new(crate::lang::cypher::CypherFrontEnd),
        Box::new(crate::lang::graphql::GraphQlFrontEnd),
        Box::new(crate::lang::objc::ObjcFrontEnd),
        Box::new(crate::lang::solidity::SolidityFrontEnd),
        Box::new(crate::lang::sql::SqlFrontEnd),
        Box::new(crate::lang::asm::AssemblyFrontEnd),
        Box::new(crate::lang::cobol::CobolFrontEnd),
        Box::new(crate::lang::d::DFrontEnd),
        Box::new(crate::lang::fsharp::FSharpFrontEnd),
        Box::new(crate::lang::lisp::LispFrontEnd),
        Box::new(crate::lang::ocaml::OcamlFrontEnd),
        Box::new(crate::lang::pascal::PascalFrontEnd),
        Box::new(crate::lang::prolog::PrologFrontEnd),
        Box::new(crate::lang::visualbasic::VisualBasicFrontEnd),
        Box::new(crate::lang::apl::AplFrontEnd),
        Box::new(crate::lang::awk::AwkFrontEnd),
        Box::new(crate::lang::crystal::CrystalFrontEnd),
        Box::new(crate::lang::forth::ForthFrontEnd),
        Box::new(crate::lang::mojo::MojoFrontEnd),
        Box::new(crate::lang::nim::NimFrontEnd),
        Box::new(crate::lang::smalltalk::SmalltalkFrontEnd),
        Box::new(crate::lang::tcl::TclFrontEnd),
        Box::new(crate::lang::vhdl::VhdlFrontEnd),
        Box::new(crate::lang::wasm::WasmFrontEnd),
        // Compound-suffix front ends (claims overrides) register after all
        // extension-dispatched languages so existing dispatch is untouched.
        Box::new(crate::lang::salesforce::SalesforceFrontEnd),
        // Apex (`.cls`/`.trigger`) — Java-derived, forked front end. Registered
        // near Salesforce so Apex and metadata resolve to the same SObject nodes.
        Box::new(crate::lang::apex::ApexFrontEnd),
    ]
}

/// Index of the first registered front end that claims `extension` (no leading
/// dot), or `None` if no language handles it.
pub fn front_end_for_extension(
    front_ends: &[Box<dyn LanguageFrontEnd>],
    extension: &str,
) -> Option<usize> {
    front_ends
        .iter()
        .position(|fe| fe.extensions().contains(&extension))
}

/// Index of the first registered front end whose [`LanguageFrontEnd::claims`]
/// accepts `rel_path`, or `None`. This is the pipeline's dispatch function;
/// registry order decides ties, so the result is deterministic.
pub fn front_end_for_path(
    front_ends: &[Box<dyn LanguageFrontEnd>],
    rel_path: &str,
) -> Option<usize> {
    front_ends.iter().position(|fe| fe.claims(rel_path))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn registry_has_unique_names_and_extensions() {
        let fes = front_ends();
        assert!(!fes.is_empty(), "registry must list at least one front end");
        let mut names = std::collections::BTreeSet::new();
        let mut exts = std::collections::BTreeSet::new();
        for fe in &fes {
            assert!(
                names.insert(fe.name()),
                "duplicate front-end name {}",
                fe.name()
            );
            for e in fe.extensions() {
                assert!(exts.insert(*e), "extension {e} claimed by two front ends");
            }
        }
    }

    #[test]
    fn default_claims_matches_final_extension_only() {
        let fes = front_ends();
        let rust = &fes[0];
        assert_eq!(rust.name(), "rust");
        assert!(rust.claims("src/main.rs"));
        assert!(rust.claims("main.rs"));
        // Compound suffix: final extension decides under the default.
        assert!(!rust.claims("flows/Intake.flow-meta.xml"));
        // Extension-less and dotfile names are not claimed by default.
        assert!(!rust.claims("Dockerfile"));
        assert!(!rust.claims(".rs"));
        // Dots in directories never fabricate an extension.
        assert!(!rust.claims("dir.rs/README"));
    }

    #[test]
    fn front_end_for_path_dispatches_like_extension_dispatch() {
        let fes = front_ends();
        let by_path = front_end_for_path(&fes, "pkg/lib.rs").expect("rs claimed");
        assert_eq!(fes[by_path].name(), "rust");
        let py = front_end_for_path(&fes, "a/b/c.py").expect("py claimed");
        assert_eq!(fes[py].name(), "python");
        assert_eq!(front_end_for_path(&fes, "notes.txt-unclaimed"), None);
        assert_eq!(front_end_for_path(&fes, "Makefile"), None);
    }

    #[test]
    fn claims_override_supports_compound_suffixes() {
        /// Test-only front end claiming a compound suffix, proving the seam.
        struct MetaXml;
        impl LanguageFrontEnd for MetaXml {
            fn name(&self) -> &'static str {
                "test-meta-xml"
            }
            fn extensions(&self) -> &'static [&'static str] {
                &[]
            }
            fn claims(&self, rel_path: &str) -> bool {
                rel_path.ends_with(".flow-meta.xml") || rel_path.ends_with(".object-meta.xml")
            }
            fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
                crate::lang::rust::RustFrontEnd.parse(path, source)
            }
            fn lower(&self, _input: &LoweredInput, _graph: &mut Graph) {}
        }
        let fes: Vec<Box<dyn LanguageFrontEnd>> = vec![Box::new(MetaXml)];
        assert_eq!(
            front_end_for_path(&fes, "objects/Case.object-meta.xml"),
            Some(0)
        );
        assert_eq!(
            front_end_for_path(&fes, "flows/Intake.flow-meta.xml"),
            Some(0)
        );
        assert_eq!(front_end_for_path(&fes, "plain.xml"), None);
    }

    #[test]
    fn rust_is_dispatched_by_extension() {
        let fes = front_ends();
        let idx = front_end_for_extension(&fes, "rs").expect("rs must be claimed");
        assert_eq!(fes[idx].name(), "rust");
        let py = front_end_for_extension(&fes, "py").expect("py must be claimed");
        assert_eq!(fes[py].name(), "python");
        let pyi = front_end_for_extension(&fes, "pyi").expect("pyi must be claimed");
        assert_eq!(fes[pyi].name(), "python");
        assert_eq!(front_end_for_extension(&fes, "no-such-ext"), None);
    }
}
