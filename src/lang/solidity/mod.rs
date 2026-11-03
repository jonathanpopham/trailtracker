//! Solidity front end: lossless lexer + CST parser + lowering, wired to the
//! shared IR through the [`LanguageFrontEnd`] seam.
//!
//! Solidity is brace-delimited and C/JS-family, so the parser follows the
//! Rust/Java strategy (precise headers, balanced token-tree bodies) while the
//! lowering follows the Java strategy (an object model with inheritance).
//! Contracts resemble classes: `contract`/`interface`/`library` →`Type`
//! (distinguished by a `type_kind`), `function`/`constructor`/`modifier`/
//! `receive`/`fallback` →`Function` (`HAS_METHOD` from the enclosing contract),
//! state variables / `constant` / `immutable` →`Constant`, `struct`/`enum`/
//! `event`/`error` →`Type`, `is`→`EXTENDS`/`IMPLEMENTS`, and `import`→`IMPORTS`,
//! reusing a deterministic scope-resolution ladder for `CALLS`.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Solidity language front end. Zero-sized: all state lives in the parse
/// trees and the lowering pass.
pub struct SolidityFrontEnd;

impl LanguageFrontEnd for SolidityFrontEnd {
    fn name(&self) -> &'static str {
        "solidity"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["sol"]
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

/// Map a repo-relative `.sol` path to its module path (the directory segments).
/// Solidity has no package/module declaration — imports are path-based — so the
/// directory chain is the most honest scope. Common layout roots (`src/`,
/// `contracts/`) are stripped; the file stem contributes no segment (its
/// top-level contracts are the scopes).
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = ["src/", "contracts/"]
        .iter()
        .find_map(|p| rel.strip_prefix(p))
        .unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    parts.pop(); // the file name itself contributes no module segment
    parts.iter().map(|s| s.to_string()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("contracts/token/ERC20.sol"), vec!["token"]);
        assert_eq!(module_path_for("src/utils/Math.sol"), vec!["utils"]);
        assert_eq!(module_path_for("token/ERC20.sol"), vec!["token"]);
        assert_eq!(module_path_for("Token.sol"), Vec::<String>::new());
        assert_eq!(module_path_for("contracts/Token.sol"), Vec::<String>::new());
    }

    #[test]
    fn front_end_identity() {
        let fe = SolidityFrontEnd;
        assert_eq!(fe.name(), "solidity");
        assert_eq!(fe.extensions(), &["sol"]);
    }

    #[test]
    fn lossless_round_trip() {
        // A representative file exercising NatSpec, pragma, both import forms,
        // inheritance, a constructor, a modifier, events/errors, a struct, an enum,
        // state variables, and receive/fallback.
        let src = "\
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import \"./Ownable.sol\";
import {IERC20 as IToken} from \"@openzeppelin/contracts/token/IERC20.sol\";

/** @title A minimal token. */
interface IThing {
    function ping() external view returns (uint256);
}

abstract contract Base {
    uint256 internal _seed;
    constructor(uint256 seed) { _seed = seed; }
}

contract Token is Base, IThing {
    mapping(address => uint256) public balances;
    uint256 public constant CAP = 1_000_000;
    address immutable owner;

    event Transfer(address indexed from, address indexed to, uint256 amount);
    error InsufficientBalance(uint256 have, uint256 need);

    struct Account { uint256 bal; bool frozen; }
    enum State { Open, Closed }

    modifier onlyOwner() {
        require(msg.sender == owner, \"not owner\");
        _;
    }

    constructor() Base(42) {}

    function ping() external view override returns (uint256) {
        return _seed;
    }

    function transfer(address to, uint256 amount) public onlyOwner {
        if (balances[msg.sender] < amount) {
            revert InsufficientBalance(balances[msg.sender], amount);
        }
        balances[msg.sender] -= amount;
        balances[to] += amount;
        emit Transfer(msg.sender, to, amount);
    }

    receive() external payable {}
    fallback() external {}
}
";
        let tree = parser::parse("Token.sol", src);
        assert!(
            tree.is_lossless(),
            "Solidity front end must reconstruct source byte-for-byte"
        );
        // And the lowering of it stays deterministic.
        let file = crate::lang::frontend::SourceFile {
            rel_path: "contracts/Token.sol".to_string(),
            module_path: SolidityFrontEnd.module_path("contracts/Token.sol"),
            source: &tree.source,
            root: &tree.root,
        };
        let g1 = lower::lower("token", std::slice::from_ref(&file), &[]);
        let g2 = lower::lower("token", std::slice::from_ref(&file), &[]);
        assert_eq!(g1.to_jsonl(), g2.to_jsonl());
    }
}
