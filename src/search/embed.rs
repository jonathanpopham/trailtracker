//! Deterministic hash embeddings for hybrid code search (G1b tier).
//!
//! Std-only, zero-dependency character-n-gram feature hashing ("the hashing
//! trick") producing fixed-size vectors comparable via cosine similarity.
//! This is the semantic-ish tier of the hybrid ranker (BM25, hash embeddings,
//! RRF fusion, graph proximity) decided in `docs/plan-remaining.md`
//! (2026-07-06 decision: zero dependencies is absolute; clean-room,
//! algorithms from the literature, no code copied).
//!
//! # Design
//!
//! - **Features**: character n-grams (n = 3 and 4) over lowercased,
//!   boundary-padded tokens. Text is split on non-alphanumeric characters;
//!   each token gets `^` / `$` sentinels so word boundaries are features too
//!   (e.g. `"order"` → `^or`, `ord`, `rde`, `der`, `er$`, `^ord`, ...).
//! - **Signed feature hashing**: each n-gram is FNV-1a-hashed ([`fnv1a_64`],
//!   the crate's existing deterministic hash). The low 8 bits pick one of
//!   [`DIM`] = 256 dimensions; bit 8 (independent of the index bits) picks the
//!   sign. Signed hashing makes collisions cancel in expectation instead of
//!   compounding (Weinberger et al., feature hashing).
//! - **Integer accumulation for bit-exact determinism**: contributions are
//!   accumulated in `i64` counters first, and only converted to `f32` and
//!   L2-normalized at the very end. Integer addition is exact and
//!   order-independent, and the final `f64` sqrt/divide are IEEE-754
//!   correctly-rounded operations, so the same input yields bit-identical
//!   vectors on every platform and in every iteration order. Accumulating in
//!   floating point instead would make results depend on summation order.
//! - **Zero vectors**: input with no n-grams (empty/whitespace/punctuation
//!   only) embeds to the all-zero vector — normalization is skipped, never
//!   producing NaN. Cosine against a zero vector is 0.0 by construction
//!   (dot product of zeros).

use crate::core::span::fnv1a_64;

/// Embedding dimensionality. 256 keeps vectors cache-friendly (1 KiB as f32)
/// while giving 3/4-gram features enough room to avoid heavy collision.
pub const DIM: usize = 256;

/// N-gram sizes extracted from each padded token.
const NGRAM_SIZES: [usize; 2] = [3, 4];

/// Accumulate signed n-gram counts for `text` into `acc`, scaled by `weight`.
///
/// Deterministic: lowercases, splits into alphanumeric tokens, pads each
/// token with `^`/`$`, then hashes every 3- and 4-char-gram into a dimension
/// (low 8 bits of the FNV-1a hash) with a sign (bit 8 of the hash).
fn accumulate(text: &str, weight: i64, acc: &mut [i64; DIM]) {
    let lowered = text.to_lowercase();
    for token in lowered.split(|c: char| !c.is_alphanumeric()) {
        if token.is_empty() {
            continue;
        }
        // Boundary padding: "^token$" so prefixes/suffixes are features.
        let mut padded: Vec<char> = Vec::with_capacity(token.chars().count() + 2);
        padded.push('^');
        padded.extend(token.chars());
        padded.push('$');

        let mut buf = String::new();
        for n in NGRAM_SIZES {
            if padded.len() < n {
                continue;
            }
            for window in padded.windows(n) {
                buf.clear();
                buf.extend(window.iter());
                let hash = fnv1a_64(buf.as_bytes());
                // Low 8 bits -> index (DIM = 256); bit 8 -> sign, so the
                // sign bit is independent of the index bits.
                let index = (hash & 0xFF) as usize;
                let sign: i64 = if (hash >> 8) & 1 == 0 { 1 } else { -1 };
                acc[index] += sign * weight;
            }
        }
    }
}

/// Convert integer counters to an L2-normalized `f32` vector.
///
/// The squared norm is computed exactly in `i128` (integer squares summed),
/// then a single correctly-rounded `f64` sqrt and one divide per component
/// keep the result bit-identical across platforms. An all-zero accumulator
/// yields the all-zero vector (no NaN from dividing by a zero norm).
fn normalize(acc: &[i64; DIM]) -> [f32; DIM] {
    let mut out = [0.0f32; DIM];
    let sum_sq: i128 = acc.iter().map(|&v| (v as i128) * (v as i128)).sum();
    if sum_sq == 0 {
        return out;
    }
    let norm = (sum_sq as f64).sqrt();
    for (o, &v) in out.iter_mut().zip(acc.iter()) {
        *o = ((v as f64) / norm) as f32;
    }
    out
}

/// Embed arbitrary text into a deterministic L2-normalized vector.
///
/// Empty (or feature-less) input returns the all-zero vector.
pub fn embed(text: &str) -> [f32; DIM] {
    let mut acc = [0i64; DIM];
    accumulate(text, 1, &mut acc);
    normalize(&acc)
}

/// Embed a graph node from its name and path.
///
/// Name n-grams are weighted 2x over path n-grams: the symbol name is the
/// strongest relevance signal, but the path still contributes (directory and
/// file tokens carry domain vocabulary). Both accumulate into the same
/// integer vector before the single final normalization.
pub fn embed_node(name: &str, path: &str) -> [f32; DIM] {
    let mut acc = [0i64; DIM];
    accumulate(name, 2, &mut acc);
    accumulate(path, 1, &mut acc);
    normalize(&acc)
}

/// Cosine similarity of two already-L2-normalized vectors: a plain dot
/// product. Zero vectors yield 0.0 (never NaN).
pub fn cosine(a: &[f32; DIM], b: &[f32; DIM]) -> f32 {
    let mut dot = 0.0f64;
    for (&x, &y) in a.iter().zip(b.iter()) {
        dot += (x as f64) * (y as f64);
    }
    dot as f32
}

/// Rank `docs` (id, embedding) against `query` by cosine similarity.
///
/// Deterministic ordering: score descending (compared via `total_cmp`, so no
/// NaN pitfalls), then id ascending as the tie-breaker. Returns at most
/// `limit` results.
pub fn rank(query: &str, docs: &[(String, [f32; DIM])], limit: usize) -> Vec<(String, f32)> {
    let q = embed(query);
    let mut scored: Vec<(String, f32)> = docs
        .iter()
        .map(|(id, vec)| (id.clone(), cosine(&q, vec)))
        .collect();
    scored.sort_by(|a, b| b.1.total_cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    scored.truncate(limit);
    scored
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn morphological_similarity_beats_unrelated() {
        let order = embed("OrderService");
        let orders = embed("OrdersService");
        let blob = embed("BlobStorage");
        let near = cosine(&order, &orders);
        let far = cosine(&order, &blob);
        assert!(
            near > far,
            "OrdersService ({near}) should be closer to OrderService than BlobStorage ({far})"
        );
    }

    #[test]
    fn typo_tolerance_ranks_order_first() {
        let docs = vec![
            (
                "BlobStorage".to_string(),
                embed_node("BlobStorage", "src/storage/blob.rs"),
            ),
            (
                "OrderService".to_string(),
                embed_node("OrderService", "src/orders/service.rs"),
            ),
            (
                "CacheLayer".to_string(),
                embed_node("CacheLayer", "src/cache/layer.rs"),
            ),
        ];
        let ranked = rank("Ordring", &docs, 3);
        assert_eq!(
            ranked[0].0, "OrderService",
            "typo query should still rank the Order symbol first: {ranked:?}"
        );
        assert!(
            ranked[0].1 > ranked[1].1,
            "top hit should strictly outscore the rest"
        );
    }

    #[test]
    fn embeddings_are_bit_identical_across_runs() {
        for text in ["OrderService", "src/graph/mod.rs", "café 日本語", ""] {
            let a = embed(text);
            let b = embed(text);
            for (x, y) in a.iter().zip(b.iter()) {
                assert_eq!(
                    x.to_bits(),
                    y.to_bits(),
                    "non-deterministic embed for {text:?}"
                );
            }
        }
        let n1 = embed_node("Parser", "src/lang/rust.rs");
        let n2 = embed_node("Parser", "src/lang/rust.rs");
        for (x, y) in n1.iter().zip(n2.iter()) {
            assert_eq!(x.to_bits(), y.to_bits());
        }
    }

    #[test]
    fn unicode_input_does_not_panic() {
        for text in [
            "café",
            "日本語のコード",
            "🚀🔥",
            "Ünïcödé_Ident",
            "\u{0301}combining",
        ] {
            let v = embed(text);
            assert!(v.iter().all(|x| x.is_finite()));
        }
    }

    #[test]
    fn empty_input_yields_zero_vector_without_nan() {
        for text in ["", "   ", "---///---"] {
            let v = embed(text);
            assert!(
                v.iter().all(|&x| x == 0.0),
                "expected zero vector for {text:?}"
            );
            assert!(v.iter().all(|x| !x.is_nan()));
            // Cosine involving a zero vector is 0.0, never NaN.
            let other = embed("OrderService");
            assert_eq!(cosine(&v, &other), 0.0);
            assert_eq!(cosine(&v, &v), 0.0);
        }
        let n = embed_node("", "");
        assert!(n.iter().all(|&x| x == 0.0));
    }

    #[test]
    fn normalized_vectors_have_unit_norm() {
        let v = embed("OrderService");
        let norm: f64 = v.iter().map(|&x| (x as f64) * (x as f64)).sum();
        assert!((norm - 1.0).abs() < 1e-6, "norm was {norm}");
    }

    #[test]
    fn rank_breaks_ties_by_id_ascending() {
        // Identical embeddings -> identical scores -> id asc must decide.
        let shared = embed("OrderService");
        let docs = vec![
            ("zeta".to_string(), shared),
            ("alpha".to_string(), shared),
            ("mid".to_string(), shared),
        ];
        let ranked = rank("OrderService", &docs, 3);
        let ids: Vec<&str> = ranked.iter().map(|(id, _)| id.as_str()).collect();
        assert_eq!(ids, ["alpha", "mid", "zeta"]);
        // And limit truncates deterministically.
        let top1 = rank("OrderService", &docs, 1);
        assert_eq!(top1.len(), 1);
        assert_eq!(top1[0].0, "alpha");
    }

    #[test]
    fn name_weighting_outranks_path_only_matches() {
        // Query matches one node's NAME and another node's PATH; the name
        // match (2x weight) must win.
        let name_hit = embed_node("InvoiceParser", "src/misc/util.rs");
        let path_hit = embed_node("Helper", "src/invoice/parser.rs");
        let q = embed("InvoiceParser");
        assert!(cosine(&q, &name_hit) > cosine(&q, &path_hit));
    }
}
