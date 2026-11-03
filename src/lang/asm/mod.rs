//! Assembly front end: one **deliberately coarse, dialect-agnostic** lossless
//! lexer + line-oriented CST parser + lowering, wired to the shared IR through the
//! [`LanguageFrontEnd`] seam.
//!
//! ## Why coarse
//! "Assembly" is not a language but a family: x86 in two incompatible syntaxes
//! (Intel and AT&T), ARM (A32/T32/A64), RISC-V, MIPS, …, each emitted by a
//! different assembler (GAS, NASM, MASM, armasm) with mutually contradictory
//! lexical rules — comment characters, immediate prefixes, label and directive
//! sigils, and number radixes all differ. There is no single correct parse. This
//! front end therefore makes **one** coarse pass tuned for symbol/label/directive/
//! call extraction, and is explicit about what it punts. The only hard guarantee
//! is **losslessness**: every byte is exactly one token, spans are contiguous, the
//! tree reconstructs the source byte-for-byte, trivia is preserved, and anything
//! unclassifiable becomes an `error` token.
//!
//! ## Lossless contract
//! See [`lexer`] and [`parser`]: contiguous spans, newlines as their own trivia
//! kind, a lexer main-loop progress guard, and a parser bracket-nesting depth
//! guard mirroring `MAX_DEPTH`.
//!
//! ## Honest mapping (see [`lower`] for the full list and punts)
//! label `name:` → [`crate::ir::ontology::node::FUNCTION`];
//! `.global`/`global` → `exported`; `.extern`/`include`/`%include`/`#include` →
//! [`crate::ir::ontology::edge::IMPORTS`] (+ `ExternalDependency`);
//! `equ`/`.equ`/`.set`/`=`/`%define`/`#define` → [`crate::ir::ontology::node::CONSTANT`];
//! `call`/`jmp`/`bl`/`b`/`je`/`jal`/… to a label → [`crate::ir::ontology::edge::CALLS`].
//!
//! ## Headline punts
//! - ARM `@`/`!` line comments are not comments (the accept-list is `;`, `#`,
//!   `//`, `/* */`); ARM `#imm` reads as a comment (`#`-comment vs `#`-immediate is
//!   unresolvable coarsely); GAS `;`-as-statement-separator is unsupported.
//! - No register model, no macro expansion, no expression evaluation; sections and
//!   data directives carry no graph node. Everything stays lossless regardless.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The assembly language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct AssemblyFrontEnd;

impl LanguageFrontEnd for AssemblyFrontEnd {
    fn name(&self) -> &'static str {
        "asm"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["asm", "s", "S"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn module_path(&self, rel_path: &str) -> Vec<String> {
        module_path_for(rel_path)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once to resolve calls and exports by name); merge it into
        // the shared graph the pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

/// Map a repo-relative assembly path to its scope segments: the directory
/// components plus the file stem (without the `.asm`/`.s`/`.S` extension). A
/// leading `src/` layout root is stripped if present. Each file is its own leaf
/// scope (assembly has no file→directory module collapse).
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = rel.strip_prefix("src/").unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file
        .strip_suffix(".asm")
        .or_else(|| file.strip_suffix(".S"))
        .or_else(|| file.strip_suffix(".s"))
        .unwrap_or(file);
    let mut module: Vec<String> = parts.iter().map(|s| s.to_string()).collect();
    module.push(stem.to_string());
    module
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn front_end_identity() {
        let fe = AssemblyFrontEnd;
        assert_eq!(fe.name(), "asm");
        assert_eq!(fe.extensions(), &["asm", "s", "S"]);
    }

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("boot.s"), vec!["boot"]);
        assert_eq!(module_path_for("a/b/start.asm"), vec!["a", "b", "start"]);
        assert_eq!(module_path_for("src/arch/entry.S"), vec!["arch", "entry"]);
    }

    /// Lossless round-trip on a representative multi-dialect snippet exercising
    /// every comment form, all string/number shapes, labels (global + NASM-local),
    /// section/directive lines, a constant, externs/includes, and call/branch
    /// instructions in both Intel and AT&T flavors.
    #[test]
    fn parse_round_trips_byte_for_byte() {
        let src = "\
; trailtracker assembly front-end self-test (NASM + GAS + ARM mixed, on purpose)
#include \"macros.inc\"
#define ALIGNMENT 16

    .section .text
    .global _start          // GAS line comment
    .extern printf
    extern  malloc

WIDTH   equ 8
mask:   dd  0xDEADBEEF, 1010b, 0FFh, 777o   /* inline block */

_start:
    mov     eax, WIDTH          ; intel
    movq    %rax, %rbx          # gas
    lea     rdi, [rel mask]
    call    printf@PLT
    call    malloc
    bl      helper
    jmp     .done

helper:
    ldr     r0, =mask
    bx      lr

.done:
    ret
";
        let fe = AssemblyFrontEnd;
        let tree = fe.parse("selftest.asm", src);
        assert!(
            tree.is_lossless(),
            "assembly front end must reconstruct source byte-for-byte"
        );
        let mut rebuilt = String::new();
        tree.root.reconstruct(&tree.source, &mut rebuilt);
        assert_eq!(rebuilt, src);
    }
}
