//! Verilog / SystemVerilog front end: lossless lexer + CST parser + lowering,
//! wired to the shared IR through the [`LanguageFrontEnd`] seam.
//!
//! Verilog is free-form (whitespace-insensitive) with two line-based exceptions —
//! `//` comments and backtick compiler directives (`` `define ``, `` `include ``).
//! The lexer stays purely lossless: every byte is covered, newlines are emitted as
//! their own trivia kind so the parser can find directive-line boundaries, and an
//! unterminated string/comment is still covered to end of input. Block structure
//! is keyword … end-keyword (`module`…`endmodule`, `function`…`endfunction`,
//! `begin`…`end`, …); the parser collects each definition's `;`-terminated header
//! precisely and recurses into the body as an item list, capturing expression
//! regions as balanced token-tree groups.
//!
//! The lowering maps `module`/`interface`/`program` → `Type` (`type_kind`),
//! `class` → `Type` (+ `EXTENDS`), `package` → `Module`, `function`/`task` →
//! `Function`, `parameter`/`localparam`/`` `define `` → `Constant`,
//! `` `include ``/`import` → `IMPORTS`, and module instantiations + function/task
//! calls → `CALLS`, reusing a conservative name-resolution pass.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Verilog / SystemVerilog language front end. Zero-sized: all state lives in
/// the parse trees and the lowering pass.
pub struct VerilogFrontEnd;

impl LanguageFrontEnd for VerilogFrontEnd {
    fn name(&self) -> &'static str {
        "verilog"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["v", "sv", "vh", "svh"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn module_path(&self, rel_path: &str) -> Vec<String> {
        module_path_for(rel_path)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once to resolve instantiations and calls by name); merge it
        // into the shared graph the pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

/// Map a repo-relative Verilog path to its scope segments: the directory
/// components plus the file stem (without the `.v`/`.sv`/`.vh`/`.svh` extension).
/// A leading `src/` or `rtl/` layout root is stripped if present. Each design file
/// is its own leaf scope (Verilog has no file→directory module collapse).
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = rel
        .strip_prefix("src/")
        .or_else(|| rel.strip_prefix("rtl/"))
        .unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file
        .strip_suffix(".svh")
        .or_else(|| file.strip_suffix(".sv"))
        .or_else(|| file.strip_suffix(".vh"))
        .or_else(|| file.strip_suffix(".v"))
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
        let fe = VerilogFrontEnd;
        assert_eq!(fe.name(), "verilog");
        assert_eq!(fe.extensions(), &["v", "sv", "vh", "svh"]);
    }

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("top.v"), vec!["top"]);
        assert_eq!(module_path_for("a/b/c.sv"), vec!["a", "b", "c"]);
        assert_eq!(module_path_for("rtl/core/alu.v"), vec!["core", "alu"]);
        assert_eq!(module_path_for("src/defs.svh"), vec!["defs"]);
    }

    /// Lossless round-trip on a representative SystemVerilog snippet exercising
    /// comments, all string/number forms, compiler directives (including a
    /// multi-token `` `define ``), attributes, a package, a parameterized module
    /// with an instantiation and a procedural block, a function, and a class with
    /// inheritance.
    #[test]
    fn parse_round_trips_byte_for_byte() {
        let src = "\
// trailtracker Verilog front-end self-test
`include \"defs.vh\"
`define WIDTH 8

package types_pkg;
    typedef enum logic [1:0] { IDLE, BUSY, DONE } state_t;
    localparam int VERSION = 2;
endpackage

(* keep = \"true\" *)
module counter #(parameter int W = `WIDTH) (
    input  logic         clk,
    input  logic         rst_n,
    output logic [W-1:0] q
);
    import types_pkg::*;
    logic [W-1:0] next = 'h0;
    wire enable = 1'b1;

    sub_unit #(.W(W)) u_sub (.clk(clk), .y(next));

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            q <= '0;
        else
            q <= add(q, 8'h01);
        $display(\"q = %0d at %t\", q, $time);
    end

    function automatic logic [W-1:0] add(logic [W-1:0] a, logic [W-1:0] b);
        return a + b;
    endfunction
endmodule

class Packet extends BasePacket;
    int unsigned id;
    function new(int unsigned id_);
        super.new();
        this.id = id_;
    endfunction
endclass
";
        let fe = VerilogFrontEnd;
        let tree = fe.parse("selftest.sv", src);
        assert!(
            tree.is_lossless(),
            "Verilog front end must reconstruct source byte-for-byte"
        );
        // Sanity: the reconstruction equals the input exactly.
        let mut rebuilt = String::new();
        tree.root.reconstruct(&tree.source, &mut rebuilt);
        assert_eq!(rebuilt, src);
    }
}
