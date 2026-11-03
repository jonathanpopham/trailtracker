//! Handle assignment for the verbalizer (ADR-0008 R3/R5): value-ranked,
//! dense, deterministic.
//!
//! Handles exist so full-name repetition (R1) fits the length budget (R8).
//! Assignment order = value ranking: the largest business domain is `D1`,
//! the highest-fan-in hotspot is `F1`, and per prefix the numbering is dense
//! (`1, 2, 3, …`) — exactly what the grammar checker enforces on a declared
//! glossary. The ranking lives in [`crate::verbalize::facts`] (facts arrive
//! pre-ranked); this module only mints the handles and their expansions.

use std::collections::BTreeMap;

use crate::verbalize::facts::{DomainFact, SymbolFact};
use crate::verbalize::grammar::Handle;
use crate::verbalize::templates::{domain_expansion, symbol_expansion};

/// The minted glossary of one verbalized document: declared handles in
/// declaration order plus the lookups the renderer needs.
#[derive(Clone, Debug, Default)]
pub struct Glossary {
    /// Declared handles, in declaration order (`D*` first, then `F*`).
    entries: Vec<Handle>,
    /// Business domain name → its `D` handle.
    domain_handles: BTreeMap<String, String>,
    /// Symbol node id → its `F` handle.
    symbol_handles: BTreeMap<String, String>,
}

impl Glossary {
    /// Mint handles for exactly the entities a document will mention:
    /// `D1..Dn` over `domains` and `F1..Fm` over `symbols`. Both slices
    /// arrive value-ranked from [`crate::verbalize::facts::extract`], so
    /// assignment order = value ranking and numbering is dense per prefix.
    pub fn over(domains: &[DomainFact], symbols: &[SymbolFact]) -> Glossary {
        let mut g = Glossary::default();
        for (i, d) in domains.iter().enumerate() {
            let handle = format!("D{}", i + 1);
            g.entries.push(Handle::new(
                handle.clone(),
                domain_expansion(&d.name, d.files, d.symbols),
            ));
            g.domain_handles.insert(d.name.clone(), handle);
        }
        for (i, s) in symbols.iter().enumerate() {
            g.push_symbol(i, s);
        }
        g
    }

    /// Mint the single-symbol glossary of a `--target` document: the target
    /// is the whole mention set, so it is `F1` by value ranking over that set.
    pub fn for_target(target: &SymbolFact) -> Glossary {
        let mut g = Glossary::default();
        g.push_symbol(0, target);
        g
    }

    fn push_symbol(&mut self, rank: usize, s: &SymbolFact) {
        let handle = format!("F{}", rank + 1);
        self.entries.push(Handle::new(
            handle.clone(),
            symbol_expansion(s.kind, &s.name, &s.path, s.line),
        ));
        self.symbol_handles.insert(s.id.clone(), handle);
    }

    /// The declared handles, in declaration order — the `glossary` argument
    /// of [`crate::verbalize::grammar::check`].
    pub fn handles(&self) -> &[Handle] {
        &self.entries
    }

    /// The in-stream glossary prelude: one `H = expansion` line per handle,
    /// in declaration order.
    pub fn lines(&self) -> Vec<String> {
        self.entries
            .iter()
            .map(|h| format!("{} = {}", h.handle, h.expansion))
            .collect()
    }

    /// The `D` handle of a business domain, if the document mentions one.
    pub fn domain(&self, name: &str) -> Option<&str> {
        self.domain_handles.get(name).map(String::as_str)
    }

    /// The `F` handle of a symbol node id, if the document mentions one.
    pub fn symbol(&self, id: &str) -> Option<&str> {
        self.symbol_handles.get(id).map(String::as_str)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verbalize::facts::Facts;
    use crate::verbalize::grammar;

    fn facts() -> Facts {
        Facts {
            domains: vec![
                DomainFact {
                    name: "parse".into(),
                    files: 34,
                    symbols: 245,
                },
                DomainFact {
                    name: "lang".into(),
                    files: 12,
                    symbols: 96,
                },
            ],
            symbols: vec![SymbolFact {
                id: "fn::render".into(),
                name: "render".into(),
                kind: "Function",
                path: "src/render.rs".into(),
                line: 42,
                domain: "parse".into(),
                layer: "Presentation".into(),
                archetype: "Command",
                fan_in: 9,
                fan_out: 2,
                blast: 20,
                dependents: vec![],
            }],
            ..Facts::default()
        }
    }

    #[test]
    fn handles_are_dense_value_ranked_and_checked() {
        let g = Glossary::over(&facts().domains, &facts().symbols);
        assert_eq!(g.domain("parse"), Some("D1"));
        assert_eq!(g.domain("lang"), Some("D2"));
        assert_eq!(g.symbol("fn::render"), Some("F1"));
        assert_eq!(g.domain("nope"), None);

        // The prelude itself passes the grammar (declared + in-stream).
        let lines = g.lines();
        let doc: Vec<&str> = lines.iter().map(String::as_str).collect();
        let vs = grammar::check(&doc, g.handles());
        assert!(vs.is_empty(), "{vs:#?}");
    }

    #[test]
    fn target_glossary_is_a_single_dense_f_handle() {
        let f = facts();
        let g = Glossary::for_target(&f.symbols[0]);
        assert_eq!(g.symbol("fn::render"), Some("F1"));
        assert_eq!(g.handles().len(), 1);
        let lines = g.lines();
        assert_eq!(
            lines[0],
            "F1 = the function `render` (`src/render.rs`, line 42)"
        );
    }

    #[test]
    fn empty_facts_mint_an_empty_glossary() {
        let g = Glossary::over(&[], &[]);
        assert!(g.handles().is_empty());
        assert!(g.lines().is_empty());
    }
}
