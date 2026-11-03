//! BM25 lexical ranking over the canonical graph (search tier G1a).
//!
//! [`SearchIndex::build`] projects the graph's searchable nodes — [`Function`],
//! [`Type`], [`Constant`], [`File`] and [`Module`]; never `UnresolvedSymbol`
//! or external placeholders — into one document each. Every document is a bag
//! of lowercase subtokens produced by [`crate::extract::lexicon::tokenize`]
//! (the exact tokenizer the Lexicon ontology uses), drawn from weighted
//! fields:
//!
//! | field                      | weight |
//! |----------------------------|--------|
//! | node name                  | 3.0    |
//! | `qualified_name` property  | 2.0    |
//! | `path` property            | 1.5    |
//! | `archetype`/`domain`/`layer` properties | 1.5 each |
//! | node kind                  | 1.0    |
//!
//! A token's per-document term frequency is the **sum of the weights** of the
//! fields it appeared in, and a document's length is its total weighted token
//! mass — so name hits dominate path hits without drowning them.
//!
//! [`SearchIndex::bm25_search`] scores standard BM25 (`k1 = 1.2`, `b = 0.75`,
//! `idf = ln((N − df + 0.5)/(df + 0.5) + 1)`). Multi-token queries sum
//! per-term scores; tokens absent from the index contribute nothing. Ranking
//! is deterministic: score descending, then node id ascending.
//!
//! [`Function`]: crate::ir::ontology::node::FUNCTION
//! [`Type`]: crate::ir::ontology::node::TYPE
//! [`Constant`]: crate::ir::ontology::node::CONSTANT
//! [`File`]: crate::ir::ontology::node::FILE
//! [`Module`]: crate::ir::ontology::node::MODULE

use std::collections::BTreeMap;

use crate::core::json::Json;
use crate::extract::lexicon::tokenize;
use crate::graph::{Graph, GraphNode};
use crate::ir::ontology::node as ont;

/// BM25 term-frequency saturation constant.
const K1: f64 = 1.2;
/// BM25 document-length normalization constant.
const B: f64 = 0.75;

/// Field weight for the node name — the strongest signal.
const WEIGHT_NAME: f64 = 3.0;
/// Field weight for the `qualified_name` property.
const WEIGHT_QUALIFIED: f64 = 2.0;
/// Field weight for the `path` property.
const WEIGHT_PATH: f64 = 1.5;
/// Field weight for the `archetype`, `domain` and `layer` properties.
const WEIGHT_ONTOLOGY: f64 = 1.5;
/// Field weight for the node kind (`Function`, `File`, …).
const WEIGHT_KIND: f64 = 1.0;

/// Node kinds worth searching. `UnresolvedSymbol`, `ExternalDependency` and
/// `Package` stay out: they are resolution artifacts / manifest facts, not
/// code a search should land on.
const INDEXED_KINDS: &[&str] = &[
    ont::CONSTANT,
    ont::FILE,
    ont::FUNCTION,
    ont::MACRO,
    ont::MODULE,
    ont::TYPE,
];

/// One entry in a token's postings list: which document, and the token's
/// field-weighted term frequency inside it. Exposed so the fusion tier (G1c)
/// can inspect per-token evidence without re-tokenizing.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Posting {
    /// Index into the document table; resolve with [`SearchIndex::doc_id`].
    pub doc: u32,
    /// Field-weighted term frequency of the token in this document.
    pub weight: f64,
}

/// A ranked search result.
#[derive(Clone, Debug)]
pub struct ScoredHit {
    /// The graph node id (e.g. `fn::crate::parser::parse#7`).
    pub id: String,
    /// BM25 score; higher is better. Always finite and positive.
    pub score: f64,
    /// The node's display name.
    pub name: String,
    /// The node kind (`Function`, `Type`, `Constant`, `File`, `Module`, …).
    pub kind: &'static str,
    /// The node's `path` property when present (File nodes carry one); empty
    /// otherwise.
    pub path: String,
}

/// A read-only view of one indexed document. The fusion tier (G1c) iterates
/// these at build time to precompute per-document embeddings without
/// re-deriving which nodes are searchable.
#[derive(Clone, Copy, Debug)]
pub struct DocView<'a> {
    /// Document index; matches [`Posting::doc`] and [`SearchIndex::doc_id`].
    pub doc: u32,
    /// The graph node id.
    pub id: &'a str,
    /// The node's display name.
    pub name: &'a str,
    /// The node kind.
    pub kind: &'static str,
    /// The node's `path` property when present; empty otherwise.
    pub path: &'a str,
}

/// Per-document metadata kept alongside the inverted index.
struct DocMeta {
    id: String,
    name: String,
    kind: &'static str,
    path: String,
    /// Total weighted token mass — the BM25 document length.
    len: f64,
}

/// An in-memory BM25 inverted index over a graph's searchable nodes.
///
/// Construction is a pure, deterministic function of the graph: nodes are
/// visited in `BTreeMap` id order, so document indices ascend with node id
/// and postings lists are always identically ordered for the same input.
pub struct SearchIndex {
    docs: Vec<DocMeta>,
    postings: BTreeMap<String, Vec<Posting>>,
    avg_len: f64,
}

impl SearchIndex {
    /// Build the index from a base graph. Only nodes whose kind is in the
    /// searchable set (Function/Type/Constant/File/Module/Macro) become
    /// documents.
    pub fn build(graph: &Graph) -> SearchIndex {
        let mut docs: Vec<DocMeta> = Vec::new();
        let mut postings: BTreeMap<String, Vec<Posting>> = BTreeMap::new();

        for node in graph.nodes() {
            if !INDEXED_KINDS.contains(&node.kind) {
                continue;
            }
            let doc = docs.len() as u32;

            // Weighted term frequencies for this document. BTreeMap keeps the
            // field-merge order-independent and the postings insertion stable.
            let mut tf: BTreeMap<String, f64> = BTreeMap::new();
            add_field(&mut tf, &node.name, WEIGHT_NAME);
            add_prop_field(&mut tf, node, "qualified_name", WEIGHT_QUALIFIED);
            add_prop_field(&mut tf, node, "path", WEIGHT_PATH);
            for key in ["archetype", "domain", "layer"] {
                add_prop_field(&mut tf, node, key, WEIGHT_ONTOLOGY);
            }
            add_field(&mut tf, node.kind, WEIGHT_KIND);

            let len: f64 = tf.values().sum();
            for (token, weight) in tf {
                postings
                    .entry(token)
                    .or_default()
                    .push(Posting { doc, weight });
            }
            docs.push(DocMeta {
                id: node.id.clone(),
                name: node.name.clone(),
                kind: node.kind,
                path: prop_str(node, "path").unwrap_or_default().to_string(),
                len,
            });
        }

        let avg_len = if docs.is_empty() {
            1.0
        } else {
            docs.iter().map(|d| d.len).sum::<f64>() / docs.len() as f64
        };
        SearchIndex {
            docs,
            postings,
            avg_len,
        }
    }

    /// Rank documents against `query` with standard BM25 and return at most
    /// `limit` hits, best first. The query goes through the same
    /// [`tokenize`] as the index; multi-token queries sum per-term scores and
    /// unknown tokens contribute 0. Ties break by node id ascending, so the
    /// ranking is fully deterministic. An empty (or all-stopword) query
    /// returns an empty list.
    pub fn bm25_search(&self, query: &str, limit: usize) -> Vec<ScoredHit> {
        if limit == 0 || self.docs.is_empty() {
            return Vec::new();
        }
        let n = self.docs.len() as f64;
        // Accumulate per-document scores. Query tokens are processed in query
        // order over fixed postings lists, so float summation order — and thus
        // the exact score — is identical across runs.
        let mut scores: BTreeMap<u32, f64> = BTreeMap::new();
        for token in tokenize(query) {
            let Some(plist) = self.postings.get(&token) else {
                continue; // unknown token: contributes 0
            };
            let df = plist.len() as f64;
            let idf = ((n - df + 0.5) / (df + 0.5) + 1.0).ln();
            for p in plist {
                let dl = self.docs[p.doc as usize].len;
                let norm = K1 * (1.0 - B + B * dl / self.avg_len);
                *scores.entry(p.doc).or_insert(0.0) +=
                    idf * (p.weight * (K1 + 1.0)) / (p.weight + norm);
            }
        }

        let mut ranked: Vec<(u32, f64)> = scores.into_iter().collect();
        // Score descending, then id ascending. Document indices ascend with
        // node id by construction, so comparing indices is comparing ids.
        ranked.sort_by(|a, b| b.1.total_cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
        ranked.truncate(limit);
        ranked
            .into_iter()
            .map(|(doc, score)| {
                let d = &self.docs[doc as usize];
                ScoredHit {
                    id: d.id.clone(),
                    score,
                    name: d.name.clone(),
                    kind: d.kind,
                    path: d.path.clone(),
                }
            })
            .collect()
    }

    /// Number of indexed documents.
    pub fn len(&self) -> usize {
        self.docs.len()
    }

    /// True when nothing was worth indexing.
    pub fn is_empty(&self) -> bool {
        self.docs.is_empty()
    }

    /// The postings list for an (already lowercase) index token, or an empty
    /// slice if the token never occurs. Cheap read-only access for the fusion
    /// tier.
    pub fn postings(&self, token: &str) -> &[Posting] {
        self.postings.get(token).map_or(&[], Vec::as_slice)
    }

    /// Resolve a posting's document index back to its graph node id.
    pub fn doc_id(&self, doc: u32) -> Option<&str> {
        self.docs.get(doc as usize).map(|d| d.id.as_str())
    }

    /// Iterate every indexed document in document-index order (which is node
    /// id order by construction). Read-only surface for the fusion tier.
    pub fn docs(&self) -> impl Iterator<Item = DocView<'_>> {
        self.docs.iter().enumerate().map(|(i, d)| DocView {
            doc: i as u32,
            id: &d.id,
            name: &d.name,
            kind: d.kind,
            path: &d.path,
        })
    }
}

/// Tokenize `text` and add `weight` to each resulting token's frequency.
fn add_field(tf: &mut BTreeMap<String, f64>, text: &str, weight: f64) {
    for token in tokenize(text) {
        *tf.entry(token).or_insert(0.0) += weight;
    }
}

/// Add a string property as a weighted field, when present.
fn add_prop_field(tf: &mut BTreeMap<String, f64>, node: &GraphNode, key: &str, weight: f64) {
    if let Some(text) = prop_str(node, key) {
        add_field(tf, text, weight);
    }
}

/// A node's string property, when present and a string.
fn prop_str<'a>(node: &'a GraphNode, key: &str) -> Option<&'a str> {
    match node.props.get(key) {
        Some(Json::Str(s)) => Some(s.as_str()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    /// Insert a Function node with realistic props (qualified name, language,
    /// line) — mirroring what `ir::lower` emits.
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

    /// Insert a File node the way `ir::lower` does: name = path = rel path.
    fn add_file(g: &mut Graph, path: &str) {
        g.upsert_node(
            format!("file::{path}"),
            ont::FILE,
            path,
            vec![("path", Json::str(path)), ("language", Json::str("csharp"))],
        );
    }

    #[test]
    fn exact_name_match_outranks_partial() {
        let mut g = Graph::new();
        add_fn(&mut g, "fn::app::parse#1", "parse", "app::parse");
        add_fn(
            &mut g,
            "fn::app::parse_header#9",
            "parse_header",
            "app::parse_header",
        );
        let idx = SearchIndex::build(&g);
        let hits = idx.bm25_search("parse", 10);
        assert_eq!(hits.len(), 2, "both contain the token");
        assert_eq!(hits[0].name, "parse", "exact name must outrank partial");
        assert_eq!(hits[0].kind, ont::FUNCTION);
        assert!(hits[0].score > hits[1].score);
    }

    #[test]
    fn multi_token_query_ranks_both_token_doc_above_single() {
        let mut g = Graph::new();
        g.upsert_node("type::BasketService", ont::TYPE, "BasketService", vec![]);
        g.upsert_node(
            "type::BasketRepository",
            ont::TYPE,
            "BasketRepository",
            vec![],
        );
        g.upsert_node("type::OrderService", ont::TYPE, "OrderService", vec![]);
        let idx = SearchIndex::build(&g);
        let hits = idx.bm25_search("basket service", 10);
        assert_eq!(
            hits[0].name, "BasketService",
            "doc matching both tokens wins"
        );
        assert_eq!(hits.len(), 3, "single-token matches still surface");
        assert!(hits[0].score > hits[1].score);
    }

    #[test]
    fn path_tokens_are_searchable() {
        let mut g = Graph::new();
        add_file(&mut g, "src/Basket.API/CartStore.cs");
        add_file(&mut g, "src/Ordering.API/OrderStore.cs");
        let idx = SearchIndex::build(&g);
        let hits = idx.bm25_search("basket", 10);
        assert_eq!(hits.len(), 1);
        assert_eq!(hits[0].path, "src/Basket.API/CartStore.cs");
        assert_eq!(hits[0].kind, ont::FILE);
    }

    #[test]
    fn unresolved_and_external_nodes_are_not_indexed() {
        let mut g = Graph::new();
        g.upsert_node("unresolved::mystery", ont::UNRESOLVED, "mystery", vec![]);
        g.upsert_node("extdep::serde", ont::EXTERNAL_DEPENDENCY, "serde", vec![]);
        g.upsert_node("pkg::calc", ont::PACKAGE, "calc", vec![]);
        add_fn(&mut g, "fn::app::mystery#3", "mystery", "app::mystery");
        let idx = SearchIndex::build(&g);
        assert_eq!(idx.len(), 1, "only the Function is a document");
        let hits = idx.bm25_search("mystery", 10);
        assert_eq!(hits.len(), 1);
        assert_eq!(hits[0].kind, ont::FUNCTION);
        assert!(idx.bm25_search("serde", 10).is_empty());
    }

    #[test]
    fn ranking_is_deterministic_across_builds_and_runs() {
        let mut g = Graph::new();
        for (id, name, qual) in [
            ("fn::a::order_total#1", "order_total", "a::order_total"),
            ("fn::b::order_lines#2", "order_lines", "b::order_lines"),
            ("fn::c::total_order#3", "total_order", "c::total_order"),
        ] {
            add_fn(&mut g, id, name, qual);
        }
        add_file(&mut g, "src/Order/Order.cs");
        let render = |hits: Vec<ScoredHit>| {
            hits.iter()
                .map(|h| format!("{}\u{1}{}\n", h.id, h.score))
                .collect::<String>()
        };
        let a = render(SearchIndex::build(&g).bm25_search("order total", 10));
        let b = render(SearchIndex::build(&g).bm25_search("order total", 10));
        assert!(!a.is_empty());
        assert_eq!(a, b, "two independent builds must rank byte-identically");
        let idx = SearchIndex::build(&g);
        assert_eq!(
            render(idx.bm25_search("order total", 10)),
            render(idx.bm25_search("order total", 10)),
        );
    }

    #[test]
    fn empty_and_unknown_queries_yield_empty() {
        let mut g = Graph::new();
        add_fn(&mut g, "fn::app::parse#1", "parse", "app::parse");
        let idx = SearchIndex::build(&g);
        assert!(idx.bm25_search("", 10).is_empty());
        assert!(idx.bm25_search("zzzunknowntoken", 10).is_empty());
        assert!(idx.bm25_search("parse", 0).is_empty(), "limit 0 is empty");
        // A known token alongside unknown ones still ranks — unknowns add 0.
        let mixed = idx.bm25_search("parse zzzunknowntoken", 10);
        assert_eq!(mixed.len(), 1);
        assert_eq!(mixed[0].name, "parse");
    }

    #[test]
    fn unicode_identifiers_do_not_panic() {
        let mut g = Graph::new();
        g.upsert_node("fn::app::café#1", ont::FUNCTION, "café_поиск_圏", vec![]);
        g.upsert_node("type::Ünit", ont::TYPE, "Ünit", vec![]);
        let idx = SearchIndex::build(&g);
        // The tokenizer splits on non-ASCII, so "caf" is the surviving stem.
        let hits = idx.bm25_search("café", 10);
        assert_eq!(hits.len(), 1);
        assert_eq!(hits[0].name, "café_поиск_圏");
        // Pure non-ASCII query tokenizes to nothing: empty, not a panic.
        assert!(idx.bm25_search("поиск", 10).is_empty());
    }

    #[test]
    fn postings_and_doc_id_expose_fusion_surface() {
        let mut g = Graph::new();
        add_fn(&mut g, "fn::app::parse#1", "parse", "app::parse");
        let idx = SearchIndex::build(&g);
        let plist = idx.postings("parse");
        assert_eq!(plist.len(), 1);
        // name (3.0) + qualified_name (2.0) = 5.0 weighted tf.
        assert_eq!(plist[0].weight, WEIGHT_NAME + WEIGHT_QUALIFIED);
        assert_eq!(idx.doc_id(plist[0].doc), Some("fn::app::parse#1"));
        assert!(idx.postings("absent").is_empty());
        assert!(!idx.is_empty());
    }

    #[test]
    fn end_to_end_calc_corpus_search_parse_finds_the_parser_fn() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("eval/corpus/calc");
        let analysis = crate::pipeline::analyze_dir(&root).expect("calc corpus analyzes");
        let idx = SearchIndex::build(&analysis.graph);
        assert!(!idx.is_empty());
        let hits = idx.bm25_search("parse", 10);
        assert!(!hits.is_empty(), "'parse' must hit in the calc corpus");
        assert_eq!(hits[0].name, "parse", "top hit is the parser fn");
        assert_eq!(hits[0].kind, ont::FUNCTION);
        assert!(
            hits[0].id.contains("parser"),
            "top hit lives in the parser module: {}",
            hits[0].id
        );
    }
}
