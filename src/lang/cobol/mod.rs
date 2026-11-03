//! COBOL front end: lossless lexer + CST parser + lowering, wired to the shared
//! IR through the [`LanguageFrontEnd`] seam.
//!
//! COBOL is **case-insensitive** and historically **column-sensitive** (fixed
//! form: cols 1-6 sequence area, col 7 indicator with `*`/`/` comment lines,
//! cols 8-72 code, 73+ ignored). Both source forms are kept fully lossless: the
//! lexer recognises fixed-form column-7 comment lines (over a genuine sequence
//! area) and free-form `*>` inline comments, and tokenises everything else
//! leniently so every byte lands in the tree regardless of column rules. The
//! parser produces a flat, sentence-oriented CST (period-terminated sentences,
//! classified into divisions / sections / paragraphs / data entries) which is
//! robust against the loss of Area-A/Area-B column information in free form.
//!
//! The lowering maps **coarsely but honestly** (see [`lower`] for the full list):
//! `PROGRAM-ID`→`Module`; procedure paragraphs/sections→`Function`;
//! `PERFORM`/`GO TO`→`CALLS` (resolved against the paragraph table);
//! `CALL "x"`→`CALLS`+`ExternalDependency`; `COPY x`→`IMPORTS`+`ExternalDependency`;
//! `01`/`77`/`88`-level items→`Constant`. DML verbs, PIC clauses, and file/screen
//! sections carry no graph fact — they remain in the lossless CST only.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The COBOL language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct CobolFrontEnd;

impl LanguageFrontEnd for CobolFrontEnd {
    fn name(&self) -> &'static str {
        "cobol"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["cob", "cbl", "cpy"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph; merge it
        // into the shared graph the pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn front_end_identity() {
        let fe = CobolFrontEnd;
        assert_eq!(fe.name(), "cobol");
        assert_eq!(fe.extensions(), &["cob", "cbl", "cpy"]);
    }

    #[test]
    fn lossless_round_trip_and_deterministic_lowering() {
        // A representative slice of COBOL: fixed-form sequence numbers and a
        // column-7 comment, an inline `*>` comment, all four divisions, a section,
        // 01/88-level data with a PIC editing period, paragraphs, a PERFORM with
        // THRU, an external CALL, a COPY, a GO TO, and a doubled-quote string.
        let src = "\
000100 IDENTIFICATION DIVISION.
000200 PROGRAM-ID. ACCT-RPT.
000300*    classic fixed-form comment line
000400 ENVIRONMENT DIVISION.
000500 DATA DIVISION.
000600 WORKING-STORAGE SECTION.
000700 COPY ACCTREC.
000800 01 WS-TOTAL   PIC ZZ9.99 VALUE ZERO.
000900 01 WS-NAME    PIC X(20).
001000 88 WS-FINISHED VALUE 'Y'.
001100 PROCEDURE DIVISION.
001200 MAIN-PARA.
001300     DISPLAY \"it''s running\". *> trailing note
001400     PERFORM INIT-PARA THRU INIT-EXIT.
001500     CALL \"POSTGL\" USING WS-TOTAL.
001600     GO TO MAIN-PARA.
001700 INIT-PARA.
001800     MOVE ZERO TO WS-TOTAL.
001900 INIT-EXIT.
002000     EXIT.
";
        let fe = CobolFrontEnd;
        let tree = fe.parse("acct.cob", src);
        assert!(
            tree.is_lossless(),
            "the COBOL front end must reconstruct source byte-for-byte"
        );

        let file = crate::lang::frontend::SourceFile {
            rel_path: "acct.cob".to_string(),
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
        assert!(g.count_nodes_of(crate::ir::ontology::node::MODULE) >= 1);

        let tree2 = fe.parse("acct.cob", src);
        let file2 = crate::lang::frontend::SourceFile {
            rel_path: "acct.cob".to_string(),
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
    fn free_form_round_trips() {
        let src = "\
IDENTIFICATION DIVISION.
PROGRAM-ID. FREE-PROG.
PROCEDURE DIVISION.
MAIN-PARA.
    DISPLAY \"hello\". *> a free-form program
    STOP RUN.
";
        let fe = CobolFrontEnd;
        let tree = fe.parse("free.cbl", src);
        assert!(tree.is_lossless(), "free-form COBOL must round-trip");
    }
}
