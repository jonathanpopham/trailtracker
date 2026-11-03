//! Lua front end: lossless lexer + CST parser + lowering, wired to the shared
//! IR through the [`LanguageFrontEnd`] seam.
//!
//! Lua is keyword-block delimited (not whitespace-significant): `do`/`end`,
//! `then`/`end`, `repeat`/`until`, and function bodies bound blocks, and a
//! newline is ordinary trivia. The lexer stays purely lossless (long brackets,
//! both string forms, hex/decimal floats, the full operator set), and the parser
//! captures definitions, control structure, requires and calls precisely while
//! keeping expression bodies as balanced token groups. The lowering maps
//! `function`→`Function`, a dotted/colon function name's table→`Type`
//! (`type_kind: table`) with `HAS_METHOD`, `require`→`IMPORTS`, and top-level
//! bindings→`Constant`, reusing a deterministic scope-resolution ladder for
//! `CALLS`. Lua has no static inheritance or type annotations, so no
//! `EXTENDS`/`IMPLEMENTS`/`USES_TYPE` edges are fabricated.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Lua language front end. Zero-sized: all state lives in the parse trees and
/// the lowering pass.
pub struct LuaFrontEnd;

impl LanguageFrontEnd for LuaFrontEnd {
    fn name(&self) -> &'static str {
        "lua"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["lua"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn module_path(&self, rel_path: &str) -> Vec<String> {
        module_path_for(rel_path)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once for the resolution ladder); merge it into the shared
        // graph the pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

/// Map a repo-relative `.lua` path to a dotted module path. A leading `src/` is
/// stripped if present; an `init.lua` is the package/directory marker and
/// contributes no extra segment (the Lua analogue of `__init__.py` / `mod.rs`),
/// matching `require "a.b"` → `a/b.lua` or `a/b/init.lua`.
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = rel.strip_prefix("src/").unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file.strip_suffix(".lua").unwrap_or(file);
    let mut module: Vec<String> = parts.iter().map(|s| s.to_string()).collect();
    match stem {
        "init" => {} // directory marker: contributes no extra segment
        other => module.push(other.to_string()),
    }
    module
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("foo.lua"), vec!["foo"]);
        assert_eq!(module_path_for("a/b/c.lua"), vec!["a", "b", "c"]);
        assert_eq!(module_path_for("a/b/init.lua"), vec!["a", "b"]);
        assert_eq!(module_path_for("src/pkg/mod.lua"), vec!["pkg", "mod"]);
    }

    #[test]
    fn front_end_identity() {
        let fe = LuaFrontEnd;
        assert_eq!(fe.name(), "lua");
        assert_eq!(fe.extensions(), &["lua"]);
    }

    #[test]
    fn lossless_round_trip_on_representative_snippet() {
        // A representative slice of real Lua: comments, long strings, methods,
        // control flow, table-valued functions, requires, and varargs.
        let src = "\
-- inventory module
local json = require('cjson')
local Item = {}
Item.__index = Item

--[==[
  Long block comment with ]] brackets inside.
]==]

function Item.new(name, qty)
    local self = setmetatable({}, Item)
    self.name = name
    self.qty = qty or 0
    return self
end

function Item:add(n)
    self.qty = self.qty + n
    if self.qty < 0 then
        self.qty = 0
    end
    return self
end

local handlers = {
    encode = function(item)
        return json.encode({ name = item.name, qty = item.qty })
    end,
}

local function sum(...)
    local total = 0
    for _, v in ipairs({ ... }) do
        total = total + v
    end
    return total
end

return Item
";
        let fe = LuaFrontEnd;
        let tree = fe.parse("inventory.lua", src);
        assert!(
            tree.is_lossless(),
            "the Lua front end must reconstruct source byte-for-byte"
        );
        assert_eq!(tree.error_byte_ratio(), 0.0, "no bytes should be errors");

        // And the lowering produces a non-trivial, deterministic graph.
        let file = crate::lang::frontend::SourceFile {
            rel_path: "inventory.lua".to_string(),
            module_path: module_path_for("inventory.lua"),
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
    }
}
