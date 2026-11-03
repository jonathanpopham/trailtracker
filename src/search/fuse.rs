//! Hybrid fusion tier (G1c): reciprocal-rank fusion of the BM25 and hash-
//! embedding tiers, re-ranked by graph-structural proximity.
//!
//! # Pipeline
//!
//! 1. **BM25 ranking** ([`SearchIndex::bm25_search`], top [`TOP_M`]).
//! 2. **Embedding ranking**: the query is hash-embedded ([`embed`]) and
//!    compared by cosine against per-document [`embed_node`] vectors that
//!    [`HybridIndex::build`] precomputed — query time is one embed plus N dot
//!    products. Only strictly-positive similarities rank; a document sharing
//!    zero n-grams with the query is not evidence.
//! 3. **Reciprocal-rank fusion** (Cormack et al.): each document's fused
//!    score is `Σ 1/(k + rank + 1)` over the rankings it appears in, with
//!    `k =` [`RRF_K`] `= 60` and 0-based `rank`. Rank fusion sidesteps the
//!    incomparable score scales of BM25 (unbounded) and cosine (`[-1, 1]`).
//! 4. **Graph-proximity re-rank** — the novel signal. The top
//!    [`ANCHOR_COUNT`] BM25 hits become *anchors*; a breadth-first walk over
//!    DEPENDS-family edges ([`parent_relation`] →
//!    [`relation::DEPENDS`]: CALLS, USES_TYPE, IMPORTS, DEPENDS_ON, FLOWS_TO,
//!    DATA_DEP), in **both directions**, reaches out [`MAX_HOPS`] `= 2` hops.
//!    A fused candidate within reach gains `BETA / (1 + hops)`. Code that is
//!    structurally coupled to what the lexical tier is confident about is
//!    more likely what the user means than an equally-worded but unrelated
//!    symbol. Proximity only *boosts existing candidates* — a node with no
//!    lexical or embedding evidence never appears on proximity alone.
//!
//! # Choice of `BETA`
//!
//! `BETA = 1/(2k) ≈ 0.0083`. Calibration against the RRF score geometry:
//! the largest single-ranking contribution is `1/(k+1) ≈ 0.0164`, and the gap
//! between adjacent ranks near the top is `1/(k+1) − 1/(k+2) ≈ 0.00026`. A
//! full 1-hop boost (`BETA/2 ≈ 0.0042`) is therefore ~16× an adjacent-rank
//! gap — it decisively reorders near-ties — but well under one additional
//! ranking appearance, so a document both tiers agree on can never be
//! displaced by proximity alone. Tests pin both properties.
//!
//! # Determinism
//!
//! Everything is a pure function of (graph, query): both tier rankings break
//! score ties by ascending document index (which is ascending node id by
//! construction), fused scores are accumulated in a fixed order (BM25 list
//! first, then embeddings, then proximity), adjacency lists are sorted and
//! de-duplicated, anchors walk in BM25-rank order, and the final sort is
//! `total_cmp` descending then id ascending. Two runs are byte-identical.
//!
//! [`relation::DEPENDS`]: crate::ir::ontology::relation::DEPENDS

use std::collections::BTreeMap;

use crate::graph::Graph;
use crate::ir::ontology::{parent_relation, relation};

use super::bm25::SearchIndex;
use super::embed::{cosine, embed, embed_node, DIM};

/// RRF smoothing constant. 60 is the standard value from the literature and
/// keeps the top-rank contribution (`1/61`) gentle enough that one tier
/// cannot single-handedly dominate.
const RRF_K: f64 = 60.0;

/// How deep into each tier's ranking fusion looks.
const TOP_M: usize = 100;

/// How many top BM25 hits seed the proximity walk.
const ANCHOR_COUNT: usize = 5;

/// Maximum BFS depth from an anchor.
const MAX_HOPS: u32 = 2;

/// Proximity boost scale; see the module docs for the calibration argument.
const BETA: f64 = 1.0 / (2.0 * RRF_K);

/// One fused, explainable search result.
#[derive(Clone, Debug)]
pub struct SearchResult {
    /// The graph node id (e.g. `fn::crate::parser::parse#7`).
    pub id: String,
    /// The node's display name.
    pub name: String,
    /// The node kind (`Function`, `Type`, `Constant`, `File`, `Module`, …).
    pub kind: &'static str,
    /// The node's `path` property when present; empty otherwise.
    pub path: String,
    /// Fused score; higher is better. Always finite and positive.
    pub score: f64,
    /// The signals that produced this result, human-readable — e.g.
    /// `"bm25 #1"`, `"embed #4"`, `"1 hop from OrderService"`. Ranks are
    /// 1-based. Order is fixed: bm25, embed, then proximity.
    pub why: Vec<String>,
}

/// A prebuilt hybrid index: the BM25 inverted index, one precomputed
/// embedding per document, and the DEPENDS-family adjacency for the
/// proximity walk. Build once, query many times.
pub struct HybridIndex {
    bm25: SearchIndex,
    /// Parallel to the BM25 document table (index = doc index).
    embeddings: Vec<[f32; DIM]>,
    /// Undirected DEPENDS-family adjacency over node ids; each list is
    /// sorted and de-duplicated so the BFS is deterministic.
    adjacency: BTreeMap<String, Vec<String>>,
}

impl HybridIndex {
    /// Build the hybrid index from a base graph. Deterministic: documents
    /// come from [`SearchIndex::build`] (node-id order) and adjacency from
    /// the graph's stably-ordered edge iterator.
    pub fn build(graph: &Graph) -> HybridIndex {
        let bm25 = SearchIndex::build(graph);
        let embeddings = bm25.docs().map(|d| embed_node(d.name, d.path)).collect();

        let mut adjacency: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for edge in graph.edges() {
            if parent_relation(edge.kind) != Some(relation::DEPENDS) {
                continue;
            }
            adjacency
                .entry(edge.from.clone())
                .or_default()
                .push(edge.to.clone());
            adjacency
                .entry(edge.to.clone())
                .or_default()
                .push(edge.from.clone());
        }
        for neighbors in adjacency.values_mut() {
            neighbors.sort();
            neighbors.dedup();
        }

        HybridIndex {
            bm25,
            embeddings,
            adjacency,
        }
    }

    /// Rank `query` against the index: RRF over the BM25 and embedding tiers,
    /// then the graph-proximity boost. Returns at most `limit` results, best
    /// first, each carrying its `why` evidence. An empty (or featureless)
    /// query returns an empty list.
    pub fn search(&self, query: &str, limit: usize) -> Vec<SearchResult> {
        if limit == 0 || self.bm25.is_empty() {
            return Vec::new();
        }

        // Tier 1: BM25. Hits carry ids; map them to doc indices for fusion.
        let bm25_hits = self.bm25.bm25_search(query, TOP_M);
        let doc_of: BTreeMap<&str, u32> = self.bm25.docs().map(|d| (d.id, d.doc)).collect();
        let bm25_ranking: Vec<u32> = bm25_hits.iter().map(|h| doc_of[h.id.as_str()]).collect();

        // Tier 2: embeddings — one query embed, N precomputed cosines. Only
        // positive similarity counts as evidence; ties break by doc index
        // ascending (== node id ascending).
        let q = embed(query);
        let mut sims: Vec<(u32, f32)> = self
            .embeddings
            .iter()
            .enumerate()
            .filter_map(|(i, v)| {
                let s = cosine(&q, v);
                (s > 0.0).then_some((i as u32, s))
            })
            .collect();
        sims.sort_by(|a, b| b.1.total_cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
        sims.truncate(TOP_M);
        let embed_ranking: Vec<u32> = sims.into_iter().map(|(doc, _)| doc).collect();

        // Reciprocal-rank fusion (fixed tier order keeps summation exact).
        let fused = rrf(&[&bm25_ranking, &embed_ranking], RRF_K);

        // Proximity: BFS out from the top BM25 anchors.
        let anchors: Vec<(&str, &str)> = bm25_hits
            .iter()
            .take(ANCHOR_COUNT)
            .map(|h| (h.id.as_str(), h.name.as_str()))
            .collect();
        let reach = self.proximity_reach(&anchors);

        // Assemble, boost, explain.
        let rank_of = |ranking: &[u32], doc: u32| ranking.iter().position(|&d| d == doc);
        let views: Vec<_> = self.bm25.docs().collect();
        let mut results: Vec<SearchResult> = fused
            .into_iter()
            .map(|(doc, mut score)| {
                let view = views[doc as usize];
                let mut why = Vec::new();
                if let Some(r) = rank_of(&bm25_ranking, doc) {
                    why.push(format!("bm25 #{}", r + 1));
                }
                if let Some(r) = rank_of(&embed_ranking, doc) {
                    why.push(format!("embed #{}", r + 1));
                }
                if let Some((hops, anchor)) = reach.get(view.id) {
                    score += BETA / (1.0 + f64::from(*hops));
                    let unit = if *hops == 1 { "hop" } else { "hops" };
                    why.push(format!("{hops} {unit} from {anchor}"));
                }
                SearchResult {
                    id: view.id.to_string(),
                    name: view.name.to_string(),
                    kind: view.kind,
                    path: view.path.to_string(),
                    score,
                    why,
                }
            })
            .collect();

        // Score descending, then node id ascending: fully deterministic.
        results.sort_by(|a, b| b.score.total_cmp(&a.score).then_with(|| a.id.cmp(&b.id)));
        results.truncate(limit);
        results
    }

    /// Multi-anchor bounded BFS over the DEPENDS-family adjacency, both
    /// directions, up to [`MAX_HOPS`]. Returns node id → (hops, anchor name)
    /// for every node reachable in 1..=[`MAX_HOPS`] hops. Anchors themselves
    /// are not self-boosted (hop 0 is skipped), though one anchor may sit
    /// within reach of another. Fewer hops win; on equal hops the
    /// earlier-ranked anchor wins (anchors walk in BM25-rank order and the
    /// map only updates on strictly fewer hops).
    fn proximity_reach(&self, anchors: &[(&str, &str)]) -> BTreeMap<String, (u32, String)> {
        let mut reach: BTreeMap<String, (u32, String)> = BTreeMap::new();
        for &(anchor_id, anchor_name) in anchors {
            let mut visited: Vec<&str> = vec![anchor_id];
            let mut frontier: Vec<&str> = vec![anchor_id];
            for hops in 1..=MAX_HOPS {
                let mut next: Vec<&str> = Vec::new();
                for &id in &frontier {
                    let Some(neighbors) = self.adjacency.get(id) else {
                        continue;
                    };
                    for n in neighbors {
                        if visited.contains(&n.as_str()) {
                            continue;
                        }
                        visited.push(n.as_str());
                        next.push(n.as_str());
                        let better = match reach.get(n.as_str()) {
                            None => true,
                            Some(&(seen, _)) => hops < seen,
                        };
                        if better {
                            reach.insert(n.clone(), (hops, anchor_name.to_string()));
                        }
                    }
                }
                frontier = next;
            }
        }
        reach
    }
}

/// Convenience one-shot: build a [`HybridIndex`] and run one query. For
/// repeated queries over the same graph, build the index once and call
/// [`HybridIndex::search`].
pub fn search(graph: &Graph, query: &str, limit: usize) -> Vec<SearchResult> {
    HybridIndex::build(graph).search(query, limit)
}

/// Reciprocal-rank fusion: `score(doc) = Σ 1/(k + rank + 1)` over every
/// ranking the doc appears in (`rank` 0-based). Rankings are consumed in the
/// given order, so float accumulation order is fixed and the result is
/// deterministic.
fn rrf(rankings: &[&[u32]], k: f64) -> BTreeMap<u32, f64> {
    let mut fused: BTreeMap<u32, f64> = BTreeMap::new();
    for ranking in rankings {
        for (rank, &doc) in ranking.iter().enumerate() {
            *fused.entry(doc).or_insert(0.0) += 1.0 / (k + rank as f64 + 1.0);
        }
    }
    fused
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::json::Json;
    use crate::ir::ontology::{edge, node as ont};
    use std::path::Path;

    /// Insert a Function node with realistic props, as `ir::lower` emits.
    fn add_fn(g: &mut Graph, id: &str, name: &str, qual: &str) {
        g.upsert_node(
            id,
            ont::FUNCTION,
            name,
            vec![
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("rust")),
                ("line", Json::U64(1)),
            ],
        );
    }

    fn render(results: &[SearchResult]) -> String {
        results
            .iter()
            .map(|r| {
                format!(
                    "{}\u{1}{}\u{1}{}\n",
                    r.id,
                    r.score.to_bits(),
                    r.why.join("|")
                )
            })
            .collect()
    }

    #[test]
    fn rrf_hand_example_doc_in_both_lists_beats_doc_in_one() {
        // Ranking A: [1, 2]; ranking B: [2, 3]. Doc 2 appears in both.
        let fused = rrf(&[&[1, 2], &[2, 3]], 60.0);
        assert_eq!(fused[&1], 1.0 / 61.0, "rank 0 in one list");
        assert_eq!(fused[&2], 1.0 / 62.0 + 1.0 / 61.0, "rank 1 + rank 0");
        assert_eq!(fused[&3], 1.0 / 62.0, "rank 1 in one list");
        assert!(
            fused[&2] > fused[&1],
            "both-lists doc must beat either single-list doc"
        );
        assert!(fused[&1] > fused[&3]);
    }

    #[test]
    fn proximity_reorders_a_near_tie_toward_the_anchor() {
        // Two docs with byte-identical searchable content (single-char
        // qualifier segments tokenize away) tie exactly in both tiers; only
        // the node id separates them, so "a" would win. A DEPENDS-family
        // edge from the "order" anchor to the "z" doc must flip that.
        let mut g = Graph::new();
        add_fn(&mut g, "fn::app::order#1", "order", "app::order");
        add_fn(&mut g, "fn::a::order_item#1", "order_item", "a::order_item");
        add_fn(&mut g, "fn::z::order_item#2", "order_item", "z::order_item");
        g.add_edge(
            "fn::app::order#1",
            edge::CALLS,
            "fn::z::order_item#2",
            vec![],
        );

        let results = search(&g, "order item", 10);
        let pos = |id: &str| {
            results
                .iter()
                .position(|r| r.id == id)
                .unwrap_or_else(|| panic!("{id} missing: {results:?}"))
        };
        assert!(
            pos("fn::z::order_item#2") < pos("fn::a::order_item#1"),
            "the doc 1 hop from the anchor must beat its distant twin: {results:?}"
        );
        let boosted = &results[pos("fn::z::order_item#2")];
        assert!(
            boosted.why.iter().any(|w| w == "1 hop from order"),
            "why must name the proximity signal: {:?}",
            boosted.why
        );

        // Sanity: without the edge, the tie breaks by id and "a" wins.
        let mut g2 = Graph::new();
        add_fn(&mut g2, "fn::app::order#1", "order", "app::order");
        add_fn(
            &mut g2,
            "fn::a::order_item#1",
            "order_item",
            "a::order_item",
        );
        add_fn(
            &mut g2,
            "fn::z::order_item#2",
            "order_item",
            "z::order_item",
        );
        let plain = search(&g2, "order item", 10);
        let pos2 = |id: &str| plain.iter().position(|r| r.id == id).unwrap();
        assert!(
            pos2("fn::a::order_item#1") < pos2("fn::z::order_item#2"),
            "control: with no edge the id tie-break holds: {plain:?}"
        );
    }

    #[test]
    fn proximity_cannot_overpower_a_strong_relevance_gap() {
        // "parse" hits both tiers at rank 1. "parsley" shares only a few
        // n-grams (embed tier, no bm25 hit) but sits 1 hop from the anchor.
        // The boost (BETA/2 ≈ 0.0042) must not close a whole-ranking gap
        // (≈ 1/61 ≈ 0.0164).
        let mut g = Graph::new();
        add_fn(&mut g, "fn::app::parse#1", "parse", "app::parse");
        add_fn(&mut g, "fn::app::parsley#2", "parsley", "app::parsley");
        g.add_edge(
            "fn::app::parse#1",
            edge::CALLS,
            "fn::app::parsley#2",
            vec![],
        );

        let results = search(&g, "parse", 10);
        assert_eq!(results[0].id, "fn::app::parse#1", "{results:?}");
        assert_eq!(results.len(), 2, "parsley surfaces via embed: {results:?}");
        assert!(
            results[0].score > results[1].score,
            "the relevance gap must survive the boost: {results:?}"
        );
        assert!(
            results[1].why.iter().any(|w| w == "1 hop from parse"),
            "boosted doc explains its proximity: {:?}",
            results[1].why
        );
    }

    #[test]
    fn typo_query_resolves_via_the_embed_tier() {
        // "Ordring" tokenizes to a term BM25 has never seen; only the
        // n-gram embedding tier can rescue it.
        let mut g = Graph::new();
        g.upsert_node("type::OrderService", ont::TYPE, "OrderService", vec![]);
        g.upsert_node("type::BlobStorage", ont::TYPE, "BlobStorage", vec![]);
        g.upsert_node("type::CacheLayer", ont::TYPE, "CacheLayer", vec![]);

        let results = search(&g, "Ordring", 10);
        assert!(!results.is_empty(), "embed tier must catch the typo");
        assert_eq!(results[0].name, "OrderService", "{results:?}");
        assert_eq!(results[0].why[0], "embed #1", "{results:?}");
        assert!(
            results[0].why.iter().all(|w| !w.starts_with("bm25")),
            "no bm25 evidence exists for a typo-only query: {results:?}"
        );
    }

    #[test]
    fn end_to_end_calc_corpus_search_parse_is_sane_and_explained() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("eval/corpus/calc");
        let analysis = crate::pipeline::analyze_dir(&root).expect("calc corpus analyzes");
        let results = search(&analysis.graph, "parse", 10);
        assert!(!results.is_empty(), "'parse' must hit in the calc corpus");
        assert_eq!(results[0].name, "parse", "top hit is the parser fn");
        assert_eq!(results[0].kind, ont::FUNCTION);
        assert_eq!(results[0].why[0], "bm25 #1", "{:?}", results[0].why);
        for r in &results {
            assert!(!r.why.is_empty(), "every result explains itself: {r:?}");
            assert!(r.score.is_finite() && r.score > 0.0);
        }
    }

    #[test]
    fn search_is_deterministic_across_independent_builds() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("eval/corpus/calc");
        let analysis = crate::pipeline::analyze_dir(&root).expect("calc corpus analyzes");
        let a = render(&search(&analysis.graph, "eval expression", 20));
        let b = render(&search(&analysis.graph, "eval expression", 20));
        assert!(!a.is_empty());
        assert_eq!(a, b, "two runs must be byte-identical");
        // And the prebuilt-index variant agrees with the one-shot.
        let idx = HybridIndex::build(&analysis.graph);
        let c = render(&idx.search("eval expression", 20));
        assert_eq!(a, c, "prebuilt index must match the one-shot path");
    }

    #[test]
    fn empty_query_zero_limit_and_empty_graph_yield_empty() {
        let g = Graph::new();
        assert!(search(&g, "anything", 10).is_empty(), "empty graph");
        let mut g = Graph::new();
        add_fn(&mut g, "fn::app::parse#1", "parse", "app::parse");
        assert!(search(&g, "", 10).is_empty(), "empty query");
        assert!(search(&g, "---///---", 10).is_empty(), "featureless query");
        assert!(search(&g, "parse", 0).is_empty(), "limit 0");
    }
}
