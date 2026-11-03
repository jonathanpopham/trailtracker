//! VHDL front end: lossless lexer + CST parser + lowering, wired to the shared
//! IR through the [`LanguageFrontEnd`] seam.
//!
//! VHDL is keyword-block delimited (not whitespace-significant) and
//! case-insensitive: `entity E is … end [entity] [E];`,
//! `architecture A of E is <decls> begin <stmts> end [architecture] [A];`,
//! `package [body] P is … end [package [body]] [P];`,
//! `function F (…) return T is … begin … end [function] [F];`,
//! `procedure P (…) is … end [procedure] [P];`, `component C is … end component;`,
//! `process (…) … begin … end process;`, `type X is …;`, `subtype X is …;`, and
//! the `library`/`use`/`context`/`configuration` clauses; a newline is ordinary
//! trivia. The lexer stays purely lossless (`--` line and `/* */` block comments,
//! `"…"` strings with the doubled-quote escape, bit-string literals `x"FF"` /
//! `8x"0F"` / `sx"FF"`, decimal and based numerals `16#FF#`, the char-literal
//! `'1'` vs attribute-tick `Clk'event` split, extended identifiers `\foo bar\`)
//! with a per-iteration progress guard. The parser captures declarations,
//! signatures and clauses precisely while keeping executable regions as balanced
//! token blocks, depth-guarded against hostile nesting. The lowering maps
//! `entity`/`architecture`→`Type` (`type_kind`), `package`/`package body`→
//! `Module`, `function`/`procedure`→`Function` (+`HAS_METHOD` inside a package),
//! `component`→`Type`, `type`/`subtype`→`Type`, `constant`→`Constant`,
//! `library`/`use`→`IMPORTS` (+`ExternalDependency`), component/entity
//! instantiations→`CALLS`, and `architecture A of E`→`IMPLEMENTS E`. Subprogram
//! `CALLS` are emitted only for `name (…)` references that resolve to a known
//! project subprogram (the call-vs-array-index ambiguity is never guessed — the
//! Ada/Fortran approach).

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The VHDL language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct VhdlFrontEnd;

impl LanguageFrontEnd for VhdlFrontEnd {
    fn name(&self) -> &'static str {
        "vhdl"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["vhd", "vhdl"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn module_path(&self, rel_path: &str) -> Vec<String> {
        module_path_for(rel_path)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once to resolve instantiations, calls, and the
        // architecture→entity links); merge it into the shared graph.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

/// Map a repo-relative VHDL path to its scope segments: the directory components
/// plus the file stem (without the `.vhd`/`.vhdl` extension). A leading `src/`,
/// `rtl/`, or `hdl/` layout root is stripped if present. Each design file is its
/// own leaf scope (VHDL has no file→directory module collapse).
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = rel
        .strip_prefix("src/")
        .or_else(|| rel.strip_prefix("rtl/"))
        .or_else(|| rel.strip_prefix("hdl/"))
        .unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file
        .strip_suffix(".vhdl")
        .or_else(|| file.strip_suffix(".vhd"))
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
        let fe = VhdlFrontEnd;
        assert_eq!(fe.name(), "vhdl");
        assert_eq!(fe.extensions(), &["vhd", "vhdl"]);
    }

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("top.vhd"), vec!["top"]);
        assert_eq!(module_path_for("a/b/c.vhdl"), vec!["a", "b", "c"]);
        assert_eq!(module_path_for("rtl/core/alu.vhd"), vec!["core", "alu"]);
        assert_eq!(module_path_for("hdl/defs.vhd"), vec!["defs"]);
    }

    /// Lossless round-trip on a representative VHDL design exercising both comment
    /// forms, all string/number/bit-string/char forms, an attribute tick, context
    /// clauses, a package + package body with a function, an entity with generics
    /// and ports, an architecture with a component, an instantiation, and a
    /// process with control flow.
    #[test]
    fn parse_round_trips_byte_for_byte() {
        let src = "\
-- trailtracker VHDL front-end self-test
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package types_pkg is
   subtype byte is std_logic_vector(7 downto 0);
   constant VERSION : integer := 2;
   function inc (x : integer) return integer;
end package types_pkg;

package body types_pkg is
   function inc (x : integer) return integer is
   begin
      return x + 1;  /* bump it */
   end function inc;
end package body types_pkg;

entity counter is
   generic (W : integer := 8);
   port (clk : in  std_logic;
         rst : in  std_logic;
         q   : out std_logic_vector(7 downto 0));
end entity counter;

architecture rtl of counter is
   signal next_q : std_logic_vector(7 downto 0) := x\"00\";
   constant ONE  : std_logic := '1';
   component sub is
      port (a : in std_logic; y : out std_logic);
   end component;
begin
   u_sub : sub port map (a => clk, y => next_q(0));

   proc : process (clk, rst)
      variable tmp : integer := 8#17#;
   begin
      if rst = ONE then
         q <= (others => '0');
      elsif clk'event and clk = '1' then
         q <= std_logic_vector(to_unsigned(inc(1), 8));
      end if;
   end process;
end architecture rtl;
";
        let fe = VhdlFrontEnd;
        let tree = fe.parse("counter.vhd", src);
        assert!(
            tree.is_lossless(),
            "the VHDL front end must reconstruct source byte-for-byte"
        );
        let mut rebuilt = String::new();
        tree.root.reconstruct(&tree.source, &mut rebuilt);
        assert_eq!(rebuilt, src);
    }

    #[test]
    fn lowering_is_deterministic_and_non_empty() {
        let src = "\
library ieee;
use ieee.std_logic_1164.all;

entity sub is
   port (a : in std_logic; y : out std_logic);
end entity sub;

architecture rtl of top is
   component sub is
      port (a : in std_logic; y : out std_logic);
   end component;
begin
   u : sub port map (a => clk, y => out_sig);
end architecture rtl;
";
        let fe = VhdlFrontEnd;
        let build = || {
            let tree = fe.parse("design.vhd", src);
            let file = crate::lang::frontend::SourceFile {
                rel_path: "design.vhd".to_string(),
                module_path: module_path_for("design.vhd"),
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
            g.to_jsonl()
        };
        let first = build();
        let second = build();
        assert_eq!(first, second, "lowering must be deterministic across runs");
        assert!(!first.is_empty(), "lowering must produce a non-empty graph");
    }
}
