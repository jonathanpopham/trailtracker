//! Fortran front end: lossless lexer + CST parser + lowering, wired to the shared
//! IR through the [`LanguageFrontEnd`] seam.
//!
//! Fortran is keyword-block delimited (`program`/`module`/`subroutine`/
//! `function`/`type`/`interface` … `end …`), case-insensitive, and has *no
//! reserved words*, so the parser classifies statements contextually from the
//! lowercased leading tokens of each logical line. Two source forms are
//! supported, both kept fully lossless:
//!
//!   - **free form** (`.f90`/`.f95`/`.f03`): `!` comments, `&` line continuation;
//!   - **fixed form** (`.f`/`.for`): column-1 `C`/`c`/`*` comment lines plus `!`
//!     inline comments, tokenised leniently (the strict column-6 continuation /
//!     column-73 truncation rules are not enforced — every byte still lands in
//!     the tree, so the round-trip holds regardless).
//!
//! The lowering maps `subroutine`/`function`→`Function`,
//! `module`/`program`→`Module`, derived `type`→`Type` (`type_kind` = `type`),
//! `extends(...)`→`EXTENDS`, `parameter` constants→`Constant`,
//! `use`/`include`→`IMPORTS` (+ `ExternalDependency`/`DEPENDS_ON`), `type(T)`/
//! `class(T)` annotations→`USES_TYPE`, and call sites→`CALLS` through a
//! deterministic host-module→global resolution ladder. Because array references
//! and function references share Fortran's `a(i)` syntax, an *implicit* function
//! reference becomes a `CALLS` edge only when it resolves to a project
//! subprogram, while an explicit `call` statement is always emitted — honest
//! about what the source actually states.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Fortran language front end. Zero-sized: all state lives in the parse
/// trees and the lowering pass.
pub struct FortranFrontEnd;

impl LanguageFrontEnd for FortranFrontEnd {
    fn name(&self) -> &'static str {
        "fortran"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["f90", "f95", "f03", "f", "for"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once for the resolution ladder); merge it into the shared
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
        let fe = FortranFrontEnd;
        assert_eq!(fe.name(), "fortran");
        assert_eq!(fe.extensions(), &["f90", "f95", "f03", "f", "for"]);
    }

    #[test]
    fn lossless_round_trip_free_form() {
        // A representative slice of modern free-form Fortran: comments, a module
        // with imports, a derived type with inheritance, a parameter constant,
        // long-form subprograms with type annotations, control flow, an explicit
        // call and a function reference, strings with doubled-quote escapes, and
        // continuation lines.
        let src = "\
! Geometry demo
module geometry
  use iso_fortran_env, only: dp => real64
  implicit none
  private

  real, parameter :: pi = 3.14159265_dp

  type :: shape
     character(len=16) :: name
  end type shape

  type, extends(shape) :: circle
     real :: radius
  end type circle

contains

  pure function area(c) result(a)
     type(circle), intent(in) :: c
     real :: a
     a = pi * c%radius ** 2
  end function area

  subroutine describe(c)
     type(circle), intent(in) :: c
     real :: a
     a = area(c)
     if (a > 10.0) then
        call report(c%name, &
                    a)
     else
        print *, 'small: ''', c%name, ''''
     end if
  end subroutine describe

  subroutine report(label, value)
     character(len=*), intent(in) :: label
     real, intent(in) :: value
     print *, label, value
  end subroutine report
end module geometry
";
        let fe = FortranFrontEnd;
        let tree = fe.parse("geometry.f90", src);
        assert!(
            tree.is_lossless(),
            "the Fortran front end must reconstruct free-form source byte-for-byte"
        );

        // The lowering produces a non-trivial, deterministic graph.
        let file = crate::lang::frontend::SourceFile {
            rel_path: "geometry.f90".to_string(),
            module_path: vec![],
            source: &tree.source,
            root: &tree.root,
        };
        let input = LoweredInput {
            package: "demo",
            manifest_deps: &[],
            files: vec![file],
        };
        let mut g = Graph::new();
        fe.lower(&input, &mut g);
        assert!(g.node_count() > 0);

        let tree2 = fe.parse("geometry.f90", src);
        let file2 = crate::lang::frontend::SourceFile {
            rel_path: "geometry.f90".to_string(),
            module_path: vec![],
            source: &tree2.source,
            root: &tree2.root,
        };
        let input2 = LoweredInput {
            package: "demo",
            manifest_deps: &[],
            files: vec![file2],
        };
        let mut g2 = Graph::new();
        fe.lower(&input2, &mut g2);
        assert_eq!(
            g.to_jsonl(),
            g2.to_jsonl(),
            "lowering must be deterministic across runs"
        );
    }

    #[test]
    fn lossless_round_trip_fixed_form() {
        // Legacy fixed-form: column-1 comment lines (`C`/`*`), a labelled DO loop,
        // a continuation in column 6, and an explicit call.
        let src = "\
C     classic fixed-form program
      program main
      integer i, total
      total = 0
      do 10 i = 1, 10
        total = total +
     &          i
   10 continue
      call show(total)
      end program main
";
        let fe = FortranFrontEnd;
        let tree = fe.parse("legacy.f", src);
        assert!(
            tree.is_lossless(),
            "the Fortran front end must reconstruct fixed-form source byte-for-byte"
        );
        // The program unit is recognised even in fixed form.
        let file = crate::lang::frontend::SourceFile {
            rel_path: "legacy.f".to_string(),
            module_path: vec![],
            source: &tree.source,
            root: &tree.root,
        };
        let input = LoweredInput {
            package: "demo",
            manifest_deps: &[],
            files: vec![file],
        };
        let mut g = Graph::new();
        fe.lower(&input, &mut g);
        assert!(g.count_nodes_of(crate::ir::ontology::node::MODULE) >= 1);
    }
}
