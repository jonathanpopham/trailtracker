//! Metamorphic test harness for the ontology extractors (gs-C1).
//!
//! The extractors (domains / archetypes / layers / hierarchy) have no oracle:
//! nobody can say what the "correct" domain clustering of an arbitrary
//! codebase is. What we *can* state are **metamorphic relations** — how the
//! output must respond to a known transformation of the input. Five relations
//! are encoded here, each scored on fault-sensitivity × independence before
//! implementation:
//!
//! | MR | transformation | relation | catches |
//! |----|----------------|----------|---------|
//! | 1. Permutation / repetition | permute node/edge insertion order; run twice | byte-identical JSONL | any interior `HashMap`/ordering nondeterminism |
//! | 2. Consistent rename | `Order` → `Bestellung` in every symbol name | archetype/layer per symbol unchanged; **domains view byte-identical** (v3 structural clustering + path-derived labels never read symbol names for membership) | vocabulary hard-coding, name-order sensitivity |
//! | 3. Additive stability | add a file inside an existing domain's unit | that domain grows, others byte-equal, top-share stays < 0.5, no new junk domain | threshold fragility, shatter/collapse regressions |
//! | 4. Scope stability (noise) | inject scaffold/docs/generated junk mass (`build/`, `obj/`, `docs/*.md`, `*.Designer.cs`, root strays) | every **src-file domain assignment identical** and the business domain table identical (junk mass is outside the clustering scope); every injected file lands in a named infrastructure group (`kind: "infrastructure"` + `reason`), never ungrouped; existing symbol archetypes and unit layers unchanged | scaffold-filter regressions (Q-DOM-2), the 106-file full-repo regression (junk mass stripping src files of their domain), ungrouped leaks |
//! | 5. Duplication stability | duplicate every module under a new path prefix | domain name set identical, every domain exactly doubled, top-share exactly preserved | shatter on duplicated structure, count instability |
//!
//! Everything is std-only and deterministic: the synthetic fixture is a fixed
//! op-list (permuted by the seeded xorshift [`Rng`] from the property
//! harness), and the corpus checks run [`analyze_dir`] over the vendored
//! `eval/corpus/` fixtures.
//!
//! Note on MR4 scope: the **domains** pass excludes junk from its clustering
//! *scope* (`SCAFFOLD_SEGMENTS`/docs/`brief_generated::is_generated`,
//! Q-DOM-2 + dom3-wire-through) but never from the *view* — excluded files
//! surface in first-class named infrastructure groups (zero ungrouped). The
//! archetypes and layers views deliberately keep scaffold symbols visible,
//! so for those two the honest invariant is *additive-only*: noise may add
//! members, it must never reclassify an existing symbol or flip an existing
//! unit's layer.
//!
//! [`Rng`]: crate::property::Rng
//! [`analyze_dir`]: trailtracker::pipeline::analyze_dir

use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;

use trailtracker::core::json::Json;
use trailtracker::extract::{
    ArchetypeExtractor, DomainExtractor, Extractor, HierarchyExtractor, LayerExtractor,
};
use trailtracker::graph::{Graph, GraphNode};
use trailtracker::ir::ontology::{edge, node as ont};

use crate::property::Rng;

/// One graph-construction operation. A base graph is a *set* of these; the
/// permutation MR applies the same set in different orders and demands a
/// byte-identical result. Ops never conflict (each node id appears once, each
/// edge signature once), so any application order denotes the same graph.
#[derive(Clone, Debug)]
pub enum Op {
    Node {
        id: String,
        kind: &'static str,
        name: String,
        props: Vec<(&'static str, Json)>,
    },
    Edge {
        from: String,
        kind: &'static str,
        to: String,
        props: Vec<(&'static str, Json)>,
    },
}

/// Apply `ops` onto `g` in the order given by `order` (indices into `ops`).
pub fn apply_onto(g: &mut Graph, ops: &[Op], order: &[usize]) {
    for &i in order {
        match &ops[i] {
            Op::Node {
                id,
                kind,
                name,
                props,
            } => g.upsert_node(id.clone(), kind, name.clone(), props.clone()),
            Op::Edge {
                from,
                kind,
                to,
                props,
            } => g.add_edge(from.clone(), kind, to.clone(), props.clone()),
        }
    }
}

/// Build a graph from `ops` applied in the given order.
pub fn build(ops: &[Op], order: &[usize]) -> Graph {
    let mut g = Graph::new();
    apply_onto(&mut g, ops, order);
    g
}

/// The identity order `0..n`.
pub fn identity_order(n: usize) -> Vec<usize> {
    (0..n).collect()
}

/// A deterministic Fisher–Yates permutation of `0..n` from `seed`.
pub fn shuffled_order(n: usize, seed: u64) -> Vec<usize> {
    let mut idx = identity_order(n);
    let mut rng = Rng::new(seed);
    for i in (1..n).rev() {
        let j = (rng.next_u64() % (i as u64 + 1)) as usize;
        idx.swap(i, j);
    }
    idx
}

/// The four ontology extractors under metamorphic test, in registry order.
pub fn ontology_extractors() -> Vec<Box<dyn Extractor>> {
    vec![
        Box::new(DomainExtractor),
        Box::new(ArchetypeExtractor),
        Box::new(LayerExtractor),
        Box::new(HierarchyExtractor),
    ]
}

/// Ops for one source file and its declared symbols.
/// `symbols` entries are `(node kind, name, optional type_kind prop)`.
fn file_ops(prefix: &str, path: &str, symbols: &[(&'static str, &str, Option<&str>)]) -> Vec<Op> {
    let full = format!("{prefix}{path}");
    let file_id = format!("file::{full}");
    let mut ops = vec![Op::Node {
        id: file_id.clone(),
        kind: ont::FILE,
        name: full.rsplit('/').next().unwrap_or(&full).to_string(),
        props: vec![("path", Json::str(full.clone()))],
    }];
    for (i, (kind, name, type_kind)) in symbols.iter().enumerate() {
        let sym_id = sym_id(prefix, path, i);
        let mut props = Vec::new();
        if let Some(tk) = type_kind {
            props.push(("type_kind", Json::str(*tk)));
        }
        ops.push(Op::Node {
            id: sym_id.clone(),
            kind,
            name: name.to_string(),
            props,
        });
        ops.push(Op::Edge {
            from: file_id.clone(),
            kind: edge::DECLARES,
            to: sym_id,
            props: vec![],
        });
    }
    ops
}

/// Positional symbol id: stable under symbol *renames*, unique per file copy.
fn sym_id(prefix: &str, path: &str, i: usize) -> String {
    format!("sym::{prefix}{path}#{i}")
}

/// The synthetic fixture: an eShop-shaped base graph with three bounded
/// contexts (Ordering / Catalog / Basket.API) recoverable from *dependency
/// structure* — each context's projects lean on each other far more than on
/// anything outside (realistic intra-context deps) — plus a concept-free
/// utility coupled into Ordering by a call, pure plumbing that must land in
/// Shared/Platform, and enough archetype variety (Controller / Entity /
/// enum / Command / Handler / Repository / Service / Dto) to make the layers
/// vote non-trivial.
///
/// `prefix` prepends every file path (the duplication MR); `rename` maps
/// every *symbol name* (the rename MR) while ids stay positional and paths
/// stay fixed, so the transformation is exactly "rename the identifier".
pub fn fixture_ops(prefix: &str, rename: &dyn Fn(&str) -> String) -> Vec<Op> {
    type Sym = (&'static str, &'static str, Option<&'static str>);
    // (path, symbols) — symbol counts per context are balanced (9/8/8) so
    // the fixture sits well below the 0.5 top-share collapse threshold and
    // no merged context crosses the anti-collapse cap.
    const FILES: &[(&str, &[Sym])] = &[
        (
            "src/Ordering.API/OrdersController.cs",
            &[
                (ont::TYPE, "OrdersController", None),
                (ont::FUNCTION, "CreateOrder", None),
                (ont::TYPE, "OrderDto", None),
            ],
        ),
        (
            "src/Ordering.Domain/Order.cs",
            &[
                (ont::TYPE, "Order", None),
                (ont::TYPE, "OrderItem", None),
                (ont::TYPE, "OrderStatus", Some("enum")),
            ],
        ),
        (
            "src/Ordering.Application/CreateOrderCommandHandler.cs",
            &[
                (ont::TYPE, "CreateOrderCommand", None),
                (ont::TYPE, "CreateOrderCommandHandler", None),
                (ont::FUNCTION, "HandleCreateOrder", None),
            ],
        ),
        (
            "src/Catalog.API/CatalogController.cs",
            &[
                (ont::TYPE, "CatalogController", None),
                (ont::FUNCTION, "GetCatalogItems", None),
                (ont::TYPE, "CatalogItemDto", None),
                (ont::TYPE, "CatalogBrand", None),
            ],
        ),
        (
            "src/Catalog.Infrastructure/CatalogRepository.cs",
            &[
                (ont::TYPE, "CatalogRepository", None),
                (ont::TYPE, "CatalogItem", None),
                (ont::FUNCTION, "LoadCatalogBrands", None),
                (ont::TYPE, "CatalogType", None),
            ],
        ),
        (
            "src/Basket.API/BasketService.cs",
            &[
                (ont::TYPE, "BasketService", None),
                (ont::TYPE, "BasketItem", None),
                (ont::FUNCTION, "GetBasketAsync", None),
                (ont::FUNCTION, "AddToBasket", None),
            ],
        ),
        (
            "src/Basket.API/BasketRepository.cs",
            &[
                (ont::TYPE, "BasketRepository", None),
                (ont::TYPE, "BasketCheckout", None),
                (ont::FUNCTION, "StoreBasket", None),
                (ont::FUNCTION, "ClearBasket", None),
            ],
        ),
        (
            "src/Common/Guard.cs",
            &[(ont::FUNCTION, "AgainstNull", None)],
        ),
        ("src/Common/Clock.cs", &[(ont::FUNCTION, "GetValue", None)]),
    ];

    let mut ops = Vec::new();
    for (path, symbols) in FILES {
        let renamed: Vec<(&'static str, String, Option<&'static str>)> = symbols
            .iter()
            .map(|(k, n, tk)| (*k, rename(n), *tk))
            .collect();
        let borrowed: Vec<(&'static str, &str, Option<&str>)> = renamed
            .iter()
            .map(|(k, n, tk)| (*k, n.as_str(), *tk))
            .collect();
        ops.extend(file_ops(prefix, path, &borrowed));
    }

    // DDD inheritance: `Order` extends an external `Entity` base — the
    // archetype signal that survives any concept rename.
    ops.push(Op::Edge {
        from: sym_id(prefix, "src/Ordering.Domain/Order.cs", 0),
        kind: edge::EXTENDS,
        to: format!("external::{prefix}Entity"),
        props: vec![("base_name", Json::str("Entity"))],
    });
    // Coupling: CreateOrder calls the concept-free Guard utility.
    ops.push(Op::Edge {
        from: sym_id(prefix, "src/Ordering.API/OrdersController.cs", 1),
        kind: edge::CALLS,
        to: sym_id(prefix, "src/Common/Guard.cs", 0),
        props: vec![],
    });
    // Intra-context structure: each context's API/Application projects lean
    // on their own Domain/Infrastructure project — the dependency mass the
    // structural clustering recovers the bounded contexts from.
    ops.push(Op::Edge {
        from: sym_id(prefix, "src/Ordering.API/OrdersController.cs", 0),
        kind: edge::USES_TYPE,
        to: sym_id(prefix, "src/Ordering.Domain/Order.cs", 0),
        props: vec![],
    });
    ops.push(Op::Edge {
        from: sym_id(prefix, "src/Ordering.API/OrdersController.cs", 1),
        kind: edge::USES_TYPE,
        to: sym_id(prefix, "src/Ordering.Domain/Order.cs", 1),
        props: vec![],
    });
    ops.push(Op::Edge {
        from: sym_id(
            prefix,
            "src/Ordering.Application/CreateOrderCommandHandler.cs",
            1,
        ),
        kind: edge::USES_TYPE,
        to: sym_id(prefix, "src/Ordering.Domain/Order.cs", 0),
        props: vec![],
    });
    ops.push(Op::Edge {
        from: sym_id(prefix, "src/Catalog.API/CatalogController.cs", 1),
        kind: edge::USES_TYPE,
        to: sym_id(prefix, "src/Catalog.Infrastructure/CatalogRepository.cs", 0),
        props: vec![],
    });
    ops.push(Op::Edge {
        from: sym_id(prefix, "src/Catalog.API/CatalogController.cs", 2),
        kind: edge::USES_TYPE,
        to: sym_id(prefix, "src/Catalog.Infrastructure/CatalogRepository.cs", 1),
        props: vec![],
    });
    // Cross-context dependencies (light, never enough to merge contexts):
    // Ordering → Basket and Catalog → Ordering.
    ops.push(Op::Edge {
        from: sym_id(prefix, "src/Ordering.API/OrdersController.cs", 1),
        kind: edge::USES_TYPE,
        to: sym_id(prefix, "src/Basket.API/BasketService.cs", 1),
        props: vec![],
    });
    ops.push(Op::Edge {
        from: sym_id(prefix, "src/Catalog.Infrastructure/CatalogRepository.cs", 1),
        kind: edge::USES_TYPE,
        to: sym_id(prefix, "src/Ordering.Domain/Order.cs", 0),
        props: vec![],
    });
    ops
}

/// MR3's added file: order-dominant vocabulary in an existing Order unit.
pub fn order_export_ops() -> Vec<Op> {
    file_ops(
        "",
        "src/Ordering.API/OrderExport.cs",
        &[
            (ont::TYPE, "OrderExport", None),
            (ont::FUNCTION, "ExportOrder", None),
            (ont::FUNCTION, "SubmitOrder", None),
        ],
    )
}

/// MR5's duplicated module: the two Basket files under a new path prefix —
/// same symbols, new paths — the "copy a module" transformation.
pub fn basket_module_ops(prefix: &str) -> Vec<Op> {
    let mut ops = file_ops(
        prefix,
        "src/Basket.API/BasketService.cs",
        &[
            (ont::TYPE, "BasketService", None),
            (ont::TYPE, "BasketItem", None),
            (ont::FUNCTION, "GetBasketAsync", None),
            (ont::FUNCTION, "AddToBasket", None),
        ],
    );
    ops.extend(file_ops(
        prefix,
        "src/Basket.API/BasketRepository.cs",
        &[
            (ont::TYPE, "BasketRepository", None),
            (ont::TYPE, "BasketCheckout", None),
            (ont::FUNCTION, "StoreBasket", None),
            (ont::FUNCTION, "ClearBasket", None),
        ],
    ));
    ops
}

/// MR4's injected junk mass: scaffold, docs, generated, and repo-root files
/// whose symbols carry existing domain concepts — bait whose mass must never
/// enter the clustering scope (src assignments identical), yet every file of
/// it must land in a named infrastructure group. The expected group is
/// returned beside each path.
pub fn noise_ops() -> Vec<Op> {
    noise_ops_with_groups().0
}

/// [`noise_ops`] plus each injected file's expected `(path, group)` pair.
pub fn noise_ops_with_groups() -> (Vec<Op>, Vec<(&'static str, &'static str)>) {
    let mut ops = file_ops(
        "",
        "build/OrderGen.cs",
        &[
            (ont::TYPE, "OrderScaffold", None),
            (ont::FUNCTION, "GenerateOrder", None),
        ],
    );
    ops.extend(file_ops(
        "",
        "src/App/obj/Debug/TempModel.cs",
        &[
            (ont::TYPE, "BasketTempHolder", None),
            (ont::FUNCTION, "EmitBasket", None),
        ],
    ));
    ops.extend(file_ops(
        "",
        "src/Ordering.API/Orders.Designer.cs",
        &[
            (ont::TYPE, "OrderDesigner", None),
            (ont::FUNCTION, "InitializeComponent", None),
        ],
    ));
    ops.extend(file_ops(
        "",
        "docs/adr/OrderNotes.md",
        &[
            (ont::TYPE, "OrderNotes", None),
            (ont::FUNCTION, "DescribeOrder", None),
        ],
    ));
    ops.extend(file_ops(
        "",
        "Setup.cs",
        &[(ont::FUNCTION, "SetupOrderTooling", None)],
    ));
    let groups = vec![
        ("build/OrderGen.cs", "Build & Tooling"),
        // `obj/` build output is machine-written: `is_generated` claims it
        // before the scaffold-segment rule ever sees it.
        ("src/App/obj/Debug/TempModel.cs", "Generated"),
        ("src/Ordering.API/Orders.Designer.cs", "Generated"),
        ("docs/adr/OrderNotes.md", "Documentation"),
        ("Setup.cs", "Repo root"),
    ];
    (ops, groups)
}

/// String prop of a node, if present.
fn prop_str<'a>(n: &'a GraphNode, key: &str) -> Option<&'a str> {
    match n.props.get(key) {
        Some(Json::Str(s)) => Some(s.as_str()),
        _ => None,
    }
}

/// u64 prop of a node, if present.
fn prop_u64(n: &GraphNode, key: &str) -> Option<u64> {
    match n.props.get(key) {
        Some(Json::U64(v)) => Some(*v),
        _ => None,
    }
}

/// Per-domain metadata read back from a domains view:
/// name → (file_count, symbol_count, unit_count, confidence, label).
pub type DomainTable = BTreeMap<String, (u64, u64, u64, String, String)>;

/// Read the domain summary nodes out of a domains view.
pub fn domain_table(view: &Graph) -> DomainTable {
    view.nodes()
        .filter(|n| n.id.starts_with("domain::"))
        .map(|n| {
            (
                n.name.clone(),
                (
                    prop_u64(n, "file_count").unwrap_or(0),
                    prop_u64(n, "symbol_count").unwrap_or(0),
                    prop_u64(n, "unit_count").unwrap_or(0),
                    prop_str(n, "confidence").unwrap_or("").to_string(),
                    prop_str(n, "label").unwrap_or("").to_string(),
                ),
            )
        })
        .collect()
}

/// Domain name → `kind` prop (`business` / `infrastructure`).
pub fn domain_kinds(view: &Graph) -> BTreeMap<String, String> {
    view.nodes()
        .filter(|n| n.id.starts_with("domain::"))
        .map(|n| {
            (
                n.name.clone(),
                prop_str(n, "kind").unwrap_or("business").to_string(),
            )
        })
        .collect()
}

/// The business-only projection of [`domain_table`]: infrastructure groups
/// (the named homes for scaffold/docs/generated/root junk) excluded. The
/// scope relation (MR4) compares this — junk mass may grow the groups but
/// must never move the business clustering.
pub fn business_domain_table(view: &Graph) -> DomainTable {
    let kinds = domain_kinds(view);
    domain_table(view)
        .into_iter()
        .filter(|(name, _)| kinds.get(name).map(String::as_str) != Some("infrastructure"))
        .collect()
}

/// Member file path → owning domain, from a domains view.
pub fn member_domains(view: &Graph) -> BTreeMap<String, String> {
    view.nodes()
        .filter(|n| n.id.starts_with("unit::"))
        .filter_map(|n| {
            Some((
                prop_str(n, "path")?.to_string(),
                prop_str(n, "domain")?.to_string(),
            ))
        })
        .collect()
}

/// Symbol node id → archetype, from an archetypes view (summary nodes
/// excluded — only classified members).
pub fn archetype_members(view: &Graph) -> BTreeMap<String, String> {
    view.nodes()
        .filter(|n| !n.id.starts_with("archetype::"))
        .filter_map(|n| Some((n.id.clone(), prop_str(n, "archetype")?.to_string())))
        .collect()
}

/// Unit name → layer, from a layers view.
pub fn unit_layers(view: &Graph) -> BTreeMap<String, String> {
    view.nodes()
        .filter(|n| n.id.starts_with("unit::"))
        .filter_map(|n| Some((n.name.clone(), prop_str(n, "layer")?.to_string())))
        .collect()
}

/// Top-share of a domains view as an exact fraction:
/// (largest domain's symbol_count, total symbol_count over all domains).
pub fn top_share(table: &DomainTable) -> (u64, u64) {
    let max = table.values().map(|v| v.1).max().unwrap_or(0);
    let total: u64 = table.values().map(|v| v.1).sum();
    (max, total)
}

/// Byte-identity assert with a first-differing-line diagnosis, so a
/// metamorphic violation reports *where* the outputs diverge, not just that
/// they do.
pub fn assert_byte_identical(label: &str, before: &str, after: &str) {
    if before == after {
        return;
    }
    let mut b = before.lines();
    let mut a = after.lines();
    let mut line = 0usize;
    loop {
        line += 1;
        match (b.next(), a.next()) {
            (Some(x), Some(y)) if x == y => continue,
            (x, y) => panic!(
                "{label}: outputs are not byte-identical (first divergence at line {line})\n  \
                 before: {}\n  after:  {}\n  (before: {} lines / {} bytes, after: {} lines / {} bytes)",
                x.unwrap_or("<end of output>"),
                y.unwrap_or("<end of output>"),
                before.lines().count(),
                before.len(),
                after.lines().count(),
                after.len(),
            ),
        }
    }
}

/// The vendored corpus fixture directories (tests run with `eval/` as CWD),
/// sorted for determinism.
pub fn corpus_dirs() -> Vec<PathBuf> {
    let mut dirs: Vec<PathBuf> = fs::read_dir("corpus")
        .expect("eval/corpus should exist (tests run from the eval crate dir)")
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| {
            p.is_dir()
                && !p
                    .file_name()
                    .is_some_and(|n| n.to_string_lossy().starts_with('.'))
        })
        .collect();
    dirs.sort();
    assert!(!dirs.is_empty(), "corpus discovery found no fixtures");
    dirs
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;
    use trailtracker::pipeline::analyze_dir;

    /// Guard against a vacuous suite: the fixture must actually exercise the
    /// interesting paths (multiple domains, several archetypes, real layers).
    /// A metamorphic relation over a degenerate graph proves nothing.
    #[test]
    fn fixture_is_nonvacuous() {
        let ops = fixture_ops("", &|n| n.to_string());
        let g = build(&ops, &identity_order(ops.len()));
        let domains = domain_table(&DomainExtractor.extract(&g));
        assert_eq!(
            domains.keys().cloned().collect::<Vec<_>>(),
            vec!["Basket.API", "Catalog", "Ordering", "Shared/Platform"],
            "fixture must recover the three bounded contexts + Shared/Platform, got: {domains:#?}"
        );
        let (max, total) = top_share(&domains);
        assert!(
            max * 2 < total,
            "fixture must start below the 0.5 top-share collapse threshold ({max}/{total})"
        );
        let archetypes: BTreeSet<String> = archetype_members(&ArchetypeExtractor.extract(&g))
            .into_values()
            .collect();
        assert!(
            archetypes.len() >= 5,
            "fixture must span several archetypes, got: {archetypes:?}"
        );
        let layers: BTreeSet<String> = unit_layers(&LayerExtractor.extract(&g))
            .into_values()
            .collect();
        assert!(
            layers.contains("Domain") && layers.contains("Presentation"),
            "fixture must place real core layers, got: {layers:?}"
        );
    }

    /// MR1a (equivalence, synthetic): permuting the base graph's node/edge
    /// insertion order — and re-running an extractor on the same graph — must
    /// yield byte-identical JSONL for every ontology view.
    #[test]
    fn mr1_insertion_order_permutation_is_invisible() {
        let ops = fixture_ops("", &|n| n.to_string());
        let baseline = build(&ops, &identity_order(ops.len()));
        let baseline_jsonl = baseline.to_jsonl();
        let base_views: Vec<(String, String)> = ontology_extractors()
            .iter()
            .map(|e| (e.name().to_string(), e.extract(&baseline).to_jsonl()))
            .collect();

        // Re-run on the identical graph: interior nondeterminism check.
        for (name, jsonl) in &base_views {
            let again = trailtracker::extract::extractor_by_name(name)
                .expect("registry name")
                .extract(&baseline)
                .to_jsonl();
            assert_byte_identical(&format!("MR1 {name} re-run on same graph"), jsonl, &again);
        }

        // Permuted insertion orders: same op set ⇒ same graph ⇒ same views.
        for seed in [0xC0FFEE_u64, 0xDEAD_BEEF, 42] {
            let order = shuffled_order(ops.len(), seed);
            assert_ne!(
                order,
                identity_order(ops.len()),
                "seed {seed} produced the identity permutation; pick another seed"
            );
            let permuted = build(&ops, &order);
            assert_byte_identical(
                &format!("MR1 base graph under insertion permutation (seed {seed:#x})"),
                &baseline_jsonl,
                &permuted.to_jsonl(),
            );
            for (name, jsonl) in &base_views {
                let view = trailtracker::extract::extractor_by_name(name)
                    .expect("registry name")
                    .extract(&permuted)
                    .to_jsonl();
                assert_byte_identical(
                    &format!("MR1 {name} view under insertion permutation (seed {seed:#x})"),
                    jsonl,
                    &view,
                );
            }
        }
    }

    /// MR1b (equivalence, corpus): analyzing a real fixture twice and running
    /// every ontology extractor twice must be byte-identical end to end, on
    /// every vendored corpus repo (multiple languages).
    #[test]
    fn mr1_corpus_analysis_and_extraction_are_byte_identical() {
        for dir in corpus_dirs() {
            let label = dir.display().to_string();
            let g1 = analyze_dir(&dir)
                .unwrap_or_else(|e| panic!("analyze_dir({label}) failed: {e}"))
                .graph;
            let g2 = analyze_dir(&dir)
                .unwrap_or_else(|e| panic!("analyze_dir({label}) failed: {e}"))
                .graph;
            assert_byte_identical(
                &format!("MR1 {label} base graph across two analyses"),
                &g1.to_jsonl(),
                &g2.to_jsonl(),
            );
            for e in ontology_extractors() {
                let a = e.extract(&g1).to_jsonl();
                let b = e.extract(&g1).to_jsonl();
                let c = e.extract(&g2).to_jsonl();
                assert_byte_identical(&format!("MR1 {label} {} re-run", e.name()), &a, &b);
                assert_byte_identical(&format!("MR1 {label} {} across analyses", e.name()), &a, &c);
            }
        }
    }

    /// MR2 (equivalence): consistently renaming a symbol identifier
    /// everywhere (`Order` → `Bestellung`) must leave every symbol's
    /// archetype and every unit's layer unchanged — and the **domains view
    /// byte-identical**. Under v3 structural clustering membership follows
    /// dependency structure and labels follow paths, so a symbol vocabulary
    /// change is invisible to the whole view — a strictly stronger relation
    /// than v2's "label tracks the renamed concept" (the lexicon's only
    /// remaining domain roles are conceptless-file detection and label
    /// *tie-breaks*, neither of which a consistent rename may flip here).
    #[test]
    fn mr2_consistent_rename_preserves_structure() {
        let rename = |n: &str| n.replace("Order", "Bestellung");
        let base_ops = fixture_ops("", &|n| n.to_string());
        let renamed_ops = fixture_ops("", &rename);
        let base = build(&base_ops, &identity_order(base_ops.len()));
        let renamed = build(&renamed_ops, &identity_order(renamed_ops.len()));

        // Archetypes: positional ids are rename-stable, so this is a
        // per-symbol equality check.
        let arch_before = archetype_members(&ArchetypeExtractor.extract(&base));
        let arch_after = archetype_members(&ArchetypeExtractor.extract(&renamed));
        assert_eq!(
            arch_before, arch_after,
            "MR2: a consistent concept rename changed some symbol's archetype\n\
             before: {arch_before:#?}\nafter: {arch_after:#?}"
        );

        // Layers: symbol names never appear in the layers view, so the whole
        // view must be byte-identical.
        assert_byte_identical(
            "MR2 layers view under consistent rename",
            &LayerExtractor.extract(&base).to_jsonl(),
            &LayerExtractor.extract(&renamed).to_jsonl(),
        );

        // Domains: the view never contains symbol names — membership is
        // structural, labels are path-derived — so it must not move at all.
        assert_byte_identical(
            "MR2 domains view under consistent rename",
            &DomainExtractor.extract(&base).to_jsonl(),
            &DomainExtractor.extract(&renamed).to_jsonl(),
        );

        // Hierarchy: same shape (node/edge counts, per-level histogram), and
        // every symbol keeps its archetype and its (path-labeled) domain.
        let h_before = HierarchyExtractor.extract(&base);
        let h_after = HierarchyExtractor.extract(&renamed);
        assert_eq!(
            h_before.node_count(),
            h_after.node_count(),
            "MR2 hierarchy node count"
        );
        assert_eq!(
            h_before.edge_count(),
            h_after.edge_count(),
            "MR2 hierarchy edge count"
        );
        let levels = |g: &Graph| -> BTreeMap<String, usize> {
            let mut m = BTreeMap::new();
            for n in g.nodes() {
                if let Some(l) = prop_str(n, "level") {
                    *m.entry(l.to_string()).or_default() += 1;
                }
            }
            m
        };
        assert_eq!(
            levels(&h_before),
            levels(&h_after),
            "MR2 hierarchy level histogram"
        );
        let after_nodes: BTreeMap<&str, &GraphNode> =
            h_after.nodes().map(|n| (n.id.as_str(), n)).collect();
        for n in h_before.nodes() {
            if prop_str(n, "level") != Some("symbol") {
                continue;
            }
            let m = after_nodes
                .get(n.id.as_str())
                .unwrap_or_else(|| panic!("MR2: hierarchy symbol {} vanished under rename", n.id));
            assert_eq!(
                prop_str(n, "archetype"),
                prop_str(m, "archetype"),
                "MR2: hierarchy symbol {} changed archetype under rename",
                n.id
            );
            assert_eq!(
                prop_str(n, "domain"),
                prop_str(m, "domain"),
                "MR2: hierarchy symbol {} changed domain under rename",
                n.id
            );
        }
    }

    /// MR3 (additive): adding one file inside an existing domain's unit
    /// (`Ordering.API`) must strengthen that domain — never collapse the
    /// view, never push top-share past 0.5, never mint a junk (≤3-symbol)
    /// domain, and never disturb the other domains.
    #[test]
    fn mr3_adding_a_file_with_an_existing_concept_is_stable() {
        let mut ops = fixture_ops("", &|n| n.to_string());
        let base = build(&ops, &identity_order(ops.len()));
        ops.extend(order_export_ops());
        let grown = build(&ops, &identity_order(ops.len()));

        let before = domain_table(&DomainExtractor.extract(&base));
        let after = domain_table(&DomainExtractor.extract(&grown));

        assert_eq!(
            before.keys().collect::<Vec<_>>(),
            after.keys().collect::<Vec<_>>(),
            "MR3: adding a file inside Ordering.API changed the domain *set*\n\
             before: {before:#?}\nafter: {after:#?}"
        );
        // The touched domain grows by exactly the added file and its symbols.
        let (bf, bs, ..) = before["Ordering"];
        let (af, asym, ..) = after["Ordering"];
        assert_eq!(
            (af, asym),
            (bf + 1, bs + 3),
            "MR3: Ordering must absorb the added file (files {bf}→{af}, symbols {bs}→{asym})\n\
             before: {before:#?}\nafter: {after:#?}"
        );
        // Every other domain is untouched.
        for (name, info) in &before {
            if name == "Ordering" {
                continue;
            }
            assert_eq!(
                after.get(name),
                Some(info),
                "MR3: unrelated domain {name} shifted when Ordering grew\n\
                 before: {before:#?}\nafter: {after:#?}"
            );
        }
        // No collapse: top-share stays under 0.5.
        let (max, total) = top_share(&after);
        assert!(
            max * 2 < total,
            "MR3: top-share crossed 0.5 after one additive file ({max}/{total})\n\
             after: {after:#?}"
        );
        // No new junk domain (≤3 symbols) appears.
        let junk = |t: &DomainTable| -> BTreeSet<String> {
            t.iter()
                .filter(|(_, v)| v.1 <= 3)
                .map(|(k, _)| k.clone())
                .collect()
        };
        assert_eq!(
            junk(&before),
            junk(&after),
            "MR3: additive change minted a junk domain\n\
             before: {before:#?}\nafter: {after:#?}"
        );
    }

    /// MR4 — the SCOPE relation (synthetic): injecting scaffold/docs/
    /// generated/root junk mass whose symbols carry real domain concepts
    /// must leave every **src-file domain assignment identical** and the
    /// business domain table identical (junk mass is outside the clustering
    /// scope — the 106-file full-repo regression class), while every
    /// injected file lands in its named infrastructure group — never
    /// ungrouped. Archetypes and layers keep scaffold symbols visible by
    /// design, so their invariant is additive-only: no existing symbol
    /// reclassified, no existing unit's layer flipped.
    #[test]
    fn mr4_junk_mass_cannot_move_src_assignments_and_is_always_grouped() {
        let base_ops = fixture_ops("", &|n| n.to_string());
        let base = build(&base_ops, &identity_order(base_ops.len()));
        let (noise, expected_groups) = noise_ops_with_groups();
        let mut noisy_ops = base_ops.clone();
        noisy_ops.extend(noise);
        let noisy = build(&noisy_ops, &identity_order(noisy_ops.len()));

        let dom_before = DomainExtractor.extract(&base);
        let dom_after = DomainExtractor.extract(&noisy);

        // Scope: identical src-file assignments — every file the base view
        // placed keeps exactly its domain under junk injection.
        let members_before = member_domains(&dom_before);
        let members_after = member_domains(&dom_after);
        for (path, domain) in &members_before {
            assert_eq!(
                members_after.get(path),
                Some(domain),
                "MR4 scope: junk mass moved src file {path} out of {domain}"
            );
        }
        // Scope: the business domain table is identical (groups may grow).
        assert_eq!(
            business_domain_table(&dom_before),
            business_domain_table(&dom_after),
            "MR4 scope: junk mass moved the business domain table"
        );

        // Zero ungrouped: every injected file is in its named group.
        for (path, group) in &expected_groups {
            assert_eq!(
                members_after.get(*path).map(String::as_str),
                Some(*group),
                "MR4: injected junk file {path} must land in {group}"
            );
        }
        let kinds = domain_kinds(&dom_after);
        for (_, group) in &expected_groups {
            assert_eq!(
                kinds.get(*group).map(String::as_str),
                Some("infrastructure"),
                "MR4: group {group} must carry kind=infrastructure"
            );
        }

        // Archetypes: noise may only *add* members, never reclassify.
        let arch_before = archetype_members(&ArchetypeExtractor.extract(&base));
        let arch_after = archetype_members(&ArchetypeExtractor.extract(&noisy));
        for (id, arch) in &arch_before {
            assert_eq!(
                arch_after.get(id),
                Some(arch),
                "MR4: noise injection reclassified existing symbol {id}\n\
                 before: {arch_before:#?}\nafter: {arch_after:#?}"
            );
        }

        // Layers: no pre-existing unit changes layer.
        let layers_before = unit_layers(&LayerExtractor.extract(&base));
        let layers_after = unit_layers(&LayerExtractor.extract(&noisy));
        for (unit, layer) in &layers_before {
            assert_eq!(
                layers_after.get(unit),
                Some(layer),
                "MR4: noise injection flipped the layer of existing unit {unit}\n\
                 before: {layers_before:#?}\nafter: {layers_after:#?}"
            );
        }
    }

    /// MR4 — the scope relation over every real corpus graph: repo vs
    /// repo+junk must keep every existing file's domain assignment and the
    /// business domain table identical, place all junk in named groups, and
    /// never reclassify an existing symbol.
    #[test]
    fn mr4_junk_mass_is_scope_stable_on_corpus_graphs() {
        let (noise, expected_groups) = noise_ops_with_groups();
        for dir in corpus_dirs() {
            let label = dir.display().to_string();
            let base = analyze_dir(&dir)
                .unwrap_or_else(|e| panic!("analyze_dir({label}) failed: {e}"))
                .graph;
            let mut noisy = analyze_dir(&dir)
                .unwrap_or_else(|e| panic!("analyze_dir({label}) failed: {e}"))
                .graph;
            apply_onto(&mut noisy, &noise, &identity_order(noise.len()));

            let dom_before = DomainExtractor.extract(&base);
            let dom_after = DomainExtractor.extract(&noisy);
            let members_before = member_domains(&dom_before);
            let members_after = member_domains(&dom_after);
            for (path, domain) in &members_before {
                assert_eq!(
                    members_after.get(path),
                    Some(domain),
                    "MR4 {label}: junk mass moved file {path} out of {domain}"
                );
            }
            assert_eq!(
                business_domain_table(&dom_before),
                business_domain_table(&dom_after),
                "MR4 {label}: junk mass moved the business domain table"
            );
            for (path, group) in &expected_groups {
                assert_eq!(
                    members_after.get(*path).map(String::as_str),
                    Some(*group),
                    "MR4 {label}: injected junk file {path} must land in {group}"
                );
            }
            let arch_before = archetype_members(&ArchetypeExtractor.extract(&base));
            let arch_after = archetype_members(&ArchetypeExtractor.extract(&noisy));
            for (id, arch) in &arch_before {
                assert_eq!(
                    arch_after.get(id),
                    Some(arch),
                    "MR4 {label}: noise injection reclassified existing symbol {id}"
                );
            }
        }
    }

    /// MR5 (multiplicative): duplicating a *module* (the Basket files —
    /// same symbols, new paths) must keep the domain set identical — no
    /// shatter into a near-duplicate `Basket2`, no collapse — with the
    /// duplicated domain exactly doubled and every other domain untouched.
    #[test]
    fn mr5_module_duplication_keeps_domain_count_stable() {
        let mut ops = fixture_ops("", &|n| n.to_string());
        let base = build(&ops, &identity_order(ops.len()));
        ops.extend(basket_module_ops("clone/"));
        let doubled = build(&ops, &identity_order(ops.len()));

        let before = domain_table(&DomainExtractor.extract(&base));
        let after = domain_table(&DomainExtractor.extract(&doubled));

        assert_eq!(
            before.keys().collect::<Vec<_>>(),
            after.keys().collect::<Vec<_>>(),
            "MR5: module duplication changed the domain set (shatter or collapse)\n\
             before: {before:#?}\nafter: {after:#?}"
        );
        let (bf, bs, ..) = before["Basket.API"];
        let (af, asym, ..) = after["Basket.API"];
        assert_eq!(
            (af, asym),
            (bf * 2, bs * 2),
            "MR5: duplicated Basket module did not fold into one exactly-doubled domain\n\
             before: {before:#?}\nafter: {after:#?}"
        );
        for (name, info) in &before {
            if name == "Basket.API" {
                continue;
            }
            assert_eq!(
                after.get(name),
                Some(info),
                "MR5: unrelated domain {name} shifted under Basket duplication\n\
                 before: {before:#?}\nafter: {after:#?}"
            );
        }
        let (max, total) = top_share(&after);
        assert!(
            max * 2 < total,
            "MR5: view collapsed under module duplication ({max}/{total})\nafter: {after:#?}"
        );
    }

    /// MR5 (multiplicative, strict — the 2026-07-06 finding, now closed):
    /// duplicating the *entire codebase* under a new path prefix must keep
    /// the domain SET (and so the count) identical, with every domain
    /// exactly doubled and top-share exactly preserved.
    ///
    /// History: under v2 lexical clustering this test PINNED a real bug the
    /// harness found — the two `Guard.cs` copies (`AgainstNull`) crossed an
    /// absolute `MIN_SEED_FILES = 2` threshold and minted a spurious
    /// `Against` domain (a preposition!). v3 structural clustering holds the
    /// relation by construction: a byte-identical prefix-copy of a unit is
    /// a *mirror unit* that folds into its original before clustering, and
    /// every surviving threshold is a ratio of symbol masses (cap, floor,
    /// shared fold, star weight), so duplicating the whole codebase scales
    /// every mass together and cannot change the community structure.
    #[test]
    fn mr5_whole_codebase_duplication_keeps_domain_set_stable() {
        let mut ops = fixture_ops("", &|n| n.to_string());
        let base = build(&ops, &identity_order(ops.len()));
        ops.extend(fixture_ops("clone/", &|n| n.to_string()));
        let doubled = build(&ops, &identity_order(ops.len()));

        let before = domain_table(&DomainExtractor.extract(&base));
        let after = domain_table(&DomainExtractor.extract(&doubled));

        // STRICT: the domain set is identical — nothing vanishes, nothing
        // is minted (the old bug minted `Against` exactly here).
        assert_eq!(
            before.keys().collect::<Vec<_>>(),
            after.keys().collect::<Vec<_>>(),
            "MR5b: whole-codebase duplication changed the domain set\n\
             before: {before:#?}\nafter: {after:#?}"
        );
        // Every domain doubles exactly — files and symbols — and keeps its
        // label and confidence. (unit_count is exempt: the clone adds one
        // `clone/` top-level unit by construction.)
        for (name, (bf, bs, _bu, bconf, blabel)) in &before {
            let (af, asym, _au, aconf, alabel) = &after[name];
            assert_eq!(
                (*af, *asym),
                (bf * 2, bs * 2),
                "MR5b: domain {name} did not double exactly under duplication\n\
                 before: {before:#?}\nafter: {after:#?}"
            );
            assert_eq!(
                (aconf, alabel),
                (bconf, blabel),
                "MR5b: domain {name} changed confidence/label under duplication\n\
                 before: {before:#?}\nafter: {after:#?}"
            );
        }
        // Top-share exactly preserved (cross-multiplied exact fractions),
        // and still no collapse.
        let (max_b, total_b) = top_share(&before);
        let (max_a, total_a) = top_share(&after);
        assert_eq!(
            max_a * total_b,
            max_b * total_a,
            "MR5b: duplication moved top-share ({max_b}/{total_b} → {max_a}/{total_a})"
        );
        assert!(
            max_a * 2 < total_a,
            "MR5b: view collapsed under duplication ({max_a}/{total_a})"
        );
    }

    /// MR6 (equivalence, incremental cache — gs-N3): the opt-in per-batch
    /// lowering cache must be *invisible*. For every vendored corpus repo:
    /// an uncached analysis, a cold cached run, a warm cached run, a mixed
    /// run (one file touched against a stale cache), and a reverted run must
    /// all produce byte-identical base-graph JSONL and byte-identical
    /// ontology views. The cache trades disk for time, never bytes.
    #[test]
    fn mr6_incremental_cache_is_invisible_cold_warm_and_touched() {
        use trailtracker::pipeline::{analyze_dir_with, AnalyzeOptions};

        /// Base graph + all four ontology views, serialized.
        fn outputs(g: &trailtracker::graph::Graph) -> Vec<(String, String)> {
            let mut out = vec![("graph".to_string(), g.to_jsonl())];
            for e in ontology_extractors() {
                out.push((e.name().to_string(), e.extract(g).to_jsonl()));
            }
            out
        }
        fn assert_all_identical(label: &str, a: &[(String, String)], b: &[(String, String)]) {
            for ((name, x), (_, y)) in a.iter().zip(b) {
                assert_byte_identical(&format!("MR6 {label} [{name}]"), x, y);
            }
        }
        fn copy_tree(src: &PathBuf, dst: &PathBuf) {
            fs::create_dir_all(dst).unwrap();
            for e in fs::read_dir(src).unwrap().flatten() {
                let from = e.path();
                let to = dst.join(e.file_name());
                if from.is_dir() {
                    copy_tree(&from, &to);
                } else {
                    fs::copy(&from, &to).unwrap();
                }
            }
        }
        /// Lexicographically first regular file in the tree — the touch target.
        fn first_file(dir: &PathBuf) -> PathBuf {
            let mut entries: Vec<PathBuf> = fs::read_dir(dir)
                .unwrap()
                .flatten()
                .map(|e| e.path())
                .collect();
            entries.sort();
            for p in entries {
                if p.is_file() {
                    return p;
                }
                if p.is_dir() {
                    return first_file(&p);
                }
            }
            panic!("no file to touch under {}", dir.display());
        }

        for dir in corpus_dirs() {
            let label = dir.display().to_string();
            let tmp = std::env::temp_dir().join(format!(
                "tt-mr6-{}-{}",
                std::process::id(),
                dir.file_name().unwrap().to_string_lossy()
            ));
            let _ = fs::remove_dir_all(&tmp);
            copy_tree(&dir, &tmp);
            let opts = AnalyzeOptions {
                cpg: false,
                cache_dir: Some(tmp.join(".trailtracker-cache")),
                ..Default::default()
            };

            let base = outputs(&analyze_dir(&tmp).unwrap().graph);
            let cold = outputs(&analyze_dir_with(&tmp, &opts).unwrap().graph);
            assert_all_identical(&format!("{label} cold==uncached"), &base, &cold);
            let warm = outputs(&analyze_dir_with(&tmp, &opts).unwrap().graph);
            assert_all_identical(&format!("{label} warm==cold"), &base, &warm);

            // Touch one file (append a newline — every front end is lossless,
            // so this is a real content change) and demand the stale-cache run
            // match a fresh uncached analysis of the modified tree.
            let target = first_file(&tmp);
            let original = fs::read(&target).unwrap();
            let mut touched = original.clone();
            touched.push(b'\n');
            fs::write(&target, &touched).unwrap();
            let mixed = outputs(&analyze_dir_with(&tmp, &opts).unwrap().graph);
            let fresh = outputs(&analyze_dir(&tmp).unwrap().graph);
            assert_all_identical(&format!("{label} mixed==fresh after touch"), &fresh, &mixed);

            // Revert: the rewritten cache must reproduce the original bytes.
            fs::write(&target, &original).unwrap();
            let reverted = outputs(&analyze_dir_with(&tmp, &opts).unwrap().graph);
            assert_all_identical(&format!("{label} reverted==base"), &base, &reverted);

            let _ = fs::remove_dir_all(&tmp);
        }
    }

    /// Harness self-check (the mutation-validation step of the metamorphic
    /// loop, without touching the extractors): the byte-identity detector
    /// must actually fire on a planted single-byte divergence.
    #[test]
    fn harness_detects_a_planted_divergence() {
        let ops = fixture_ops("", &|n| n.to_string());
        let g = build(&ops, &identity_order(ops.len()));
        let good = DomainExtractor.extract(&g).to_jsonl();
        let mutated = good.replacen("Order", "Odrer", 1);
        assert_ne!(good, mutated, "planted mutation must change the output");
        let caught = std::panic::catch_unwind(|| {
            assert_byte_identical("self-check", &good, &mutated);
        })
        .is_err();
        assert!(
            caught,
            "assert_byte_identical failed to detect a planted divergence"
        );
    }
}
