//! Opt-in incremental analysis cache (`--incremental` / `TRAILTRACKER_CACHE`).
//!
//! # What is cached, and why exactly this
//!
//! Lowering is a whole-batch operation by design: every front end receives the
//! complete set of files it claims and performs **cross-file** symbol
//! resolution inside `lower` (see [`crate::lang::frontend::LanguageFrontEnd`]:
//! "cross-file resolution may assume the whole batch"). A single file's
//! "lowered subgraph" therefore does not exist as an isolatable artifact — the
//! edges a file contributes (resolved calls, type uses) depend on what every
//! *other* file in the batch defines. Caching per-file lowering output would be
//! approximate, and approximate is banned: the hard invariant of this cache is
//! that cold, warm, and mixed runs are **byte-identical**.
//!
//! So the cache unit is the narrowest sound one: **one entry per language
//! batch**, keyed by an exact per-file manifest — every claimed readable
//! file's `(rel_path, byte_len, fnv1a_64(content))` — plus the tool version,
//! cache format version, language, package name, and manifest dependencies
//! (everything `lower` can observe). Per-file content hashes decide
//! invalidation; the stored value is the batch's lowered subgraph, serialized
//! with the existing byte-stable graph JSONL machinery, plus the batch's
//! statistics contribution and its parse-panicked file list. Whole-graph
//! passes (cross-provider linking, extractors) always rerun over the merged
//! node/edge set exactly as in a cold run.
//!
//! Soundness of splicing rests on an audited property of every registered
//! front end: `lower` only *writes* into the shared graph (each one lowers a
//! self-contained subgraph and `Graph::merge`s it; none read shared state), so
//! `fe.lower(&input, &mut shared)` is exactly `shared.merge(sub)` where `sub`
//! is `fe.lower` into a fresh graph. The pipeline test
//! `cache_cold_warm_mixed_runs_are_byte_identical` and the corpus golden gate
//! pin this end to end.
//!
//! # Failure posture
//!
//! The cache is an accelerator, never an authority. Any problem — unreadable
//! entry, version mismatch, torn write, malformed JSON, a subgraph containing
//! a value that would not reload as the identical in-memory `Json` variant —
//! degrades to a miss (relower + rewrite) or to not caching at all. Entries
//! are written atomically (temp file + rename). A `.gitignore` containing `*`
//! is dropped inside the cache directory so it never pollutes the analyzed
//! repository.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

use crate::core::json::Json;
use crate::core::span::fnv1a_64;
use crate::graph::Graph;

/// Bump whenever the entry layout or anything feeding the key changes.
const FORMAT: u64 = 1;

/// A language batch's statistics contribution, cached alongside the subgraph
/// so `stats` output is byte-identical between cold and warm runs.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct BatchStats {
    pub files: usize,
    pub lossless_files: usize,
    pub diagnostics: usize,
    pub error_bytes: usize,
    pub total_bytes: usize,
}

/// A cache hit: the batch's lowered subgraph plus everything else the batch
/// contributed to the analysis besides graph content.
pub(crate) struct CachedBatch {
    pub sub: Graph,
    pub stats: BatchStats,
    /// Repo-relative paths whose parse panicked when the entry was built
    /// (deterministic given identical content, so replayable).
    pub panicked: Vec<String>,
}

/// The exact key material of one batch entry, compared as a whole `Json`
/// value. Any difference — one file's content hash, the tool version, the
/// package name — is a miss.
pub(crate) fn batch_key(
    language: &str,
    package: &str,
    manifest_deps: &[String],
    files: &[(String, u64, u64)], // (rel_path, byte_len, fnv1a_64(content))
) -> Json {
    Json::obj([
        ("format", Json::U64(FORMAT)),
        ("tool", Json::str(env!("CARGO_PKG_VERSION"))),
        ("language", Json::str(language)),
        ("package", Json::str(package)),
        (
            "deps",
            Json::Array(manifest_deps.iter().map(Json::str).collect()),
        ),
        (
            "files",
            Json::Array(
                files
                    .iter()
                    .map(|(rel, len, hash)| {
                        Json::Array(vec![
                            Json::str(rel.clone()),
                            Json::U64(*len),
                            Json::str(format!("{hash:016x}")),
                        ])
                    })
                    .collect(),
            ),
        ),
    ])
}

/// One open cache directory, scoped to a single analyzed root (multiple roots
/// can share a `TRAILTRACKER_CACHE_DIR`; each gets its own subdirectory keyed
/// by the canonical root path).
pub(crate) struct Cache {
    entries_dir: PathBuf,
}

impl Cache {
    /// Open (creating if needed) the cache under `dir` for analyses of `root`.
    /// Returns `None` — analysis proceeds uncached — if the directory cannot
    /// be prepared; the reason goes to stderr, never into the output.
    pub(crate) fn open(dir: &Path, root: &Path) -> Option<Cache> {
        let canonical = fs::canonicalize(root).unwrap_or_else(|_| root.to_path_buf());
        let root_tag = format!("{:016x}", fnv1a_64(canonical.to_string_lossy().as_bytes()));
        let entries_dir = dir.join("v1").join(root_tag);
        if let Err(e) = fs::create_dir_all(&entries_dir) {
            eprintln!(
                "trailtracker: cache disabled: cannot create {}: {e}",
                entries_dir.display()
            );
            return None;
        }
        // Keep the cache out of version control, like other tool-managed dirs.
        let gitignore = dir.join(".gitignore");
        if !gitignore.exists() {
            let _ = fs::write(&gitignore, "*\n");
        }
        Some(Cache { entries_dir })
    }

    fn entry_path(&self, language: &str) -> PathBuf {
        self.entries_dir.join(format!("{language}.jsonl"))
    }

    /// Load the entry for `language` if its stored key matches `key` exactly.
    /// Every corruption mode is a miss.
    pub(crate) fn load(&self, language: &str, key: &Json) -> Option<CachedBatch> {
        let text = fs::read_to_string(self.entry_path(language)).ok()?;
        let mut lines = text.lines();
        let meta = parse_json(lines.next()?).ok()?;
        let Json::Object(meta) = meta else {
            return None;
        };
        if meta.get("record").and_then(json_str) != Some("cache-meta") {
            return None;
        }
        if meta.get("key") != Some(key) {
            return None;
        }
        let stats_obj = meta.get("stats")?;
        let stat = |name: &str| -> Option<usize> {
            match stats_obj {
                Json::Object(m) => match m.get(name)? {
                    Json::U64(v) => Some(*v as usize),
                    _ => None,
                },
                _ => None,
            }
        };
        let stats = BatchStats {
            files: stat("files")?,
            lossless_files: stat("lossless_files")?,
            diagnostics: stat("diagnostics")?,
            error_bytes: stat("error_bytes")?,
            total_bytes: stat("total_bytes")?,
        };
        let panicked = match meta.get("panicked")? {
            Json::Array(items) => {
                let mut out = Vec::with_capacity(items.len());
                for item in items {
                    out.push(json_str(item)?.to_string());
                }
                out
            }
            _ => return None,
        };

        let mut sub = Graph::new();
        for line in lines {
            load_record(&mut sub, line)?;
        }
        Some(CachedBatch {
            sub,
            stats,
            panicked,
        })
    }

    /// Store a batch entry: meta line (key + stats + panicked) followed by the
    /// subgraph's canonical JSONL. Refuses (silently — the cache just stays
    /// cold for this batch) when the subgraph contains any value that would
    /// not reload as the identical in-memory `Json` variant, so a warm run can
    /// never diverge from a cold one even in unobservable in-memory state.
    pub(crate) fn store(
        &self,
        language: &str,
        key: &Json,
        sub: &Graph,
        stats: BatchStats,
        panicked: &[String],
    ) {
        if !graph_reloads_exactly(sub) {
            return;
        }
        let meta = Json::obj([
            ("record", Json::str("cache-meta")),
            ("key", key.clone()),
            (
                "stats",
                Json::obj([
                    ("files", Json::U64(stats.files as u64)),
                    ("lossless_files", Json::U64(stats.lossless_files as u64)),
                    ("diagnostics", Json::U64(stats.diagnostics as u64)),
                    ("error_bytes", Json::U64(stats.error_bytes as u64)),
                    ("total_bytes", Json::U64(stats.total_bytes as u64)),
                ]),
            ),
            (
                "panicked",
                Json::Array(panicked.iter().map(Json::str).collect()),
            ),
        ]);
        let mut body = meta.to_line();
        body.push('\n');
        body.push_str(&sub.to_jsonl());
        // Atomic publish: a crash mid-write leaves either the old entry or a
        // stray temp file, never a torn entry that could half-load.
        let path = self.entry_path(language);
        let tmp = path.with_extension("jsonl.tmp");
        if fs::write(&tmp, body).is_ok() && fs::rename(&tmp, &path).is_err() {
            let _ = fs::remove_file(&tmp);
        }
    }

    /// Remove entries for languages that no longer occur in the analyzed
    /// tree (their batch vanished), plus any stray temp files.
    pub(crate) fn prune(&self, active_languages: &BTreeSet<&str>) {
        let Ok(dir) = fs::read_dir(&self.entries_dir) else {
            return;
        };
        for entry in dir.flatten() {
            let name = entry.file_name();
            let name = name.to_string_lossy();
            let stale = match name.strip_suffix(".jsonl") {
                Some(lang) => !active_languages.contains(lang),
                None => name.ends_with(".jsonl.tmp"),
            };
            if stale {
                let _ = fs::remove_file(entry.path());
            }
        }
    }
}

/// Parse one graph JSONL record into `g` via the raw-rebuild constructors.
/// `None` on anything unexpected (the caller treats the whole entry as a miss).
fn load_record(g: &mut Graph, line: &str) -> Option<()> {
    let Json::Object(mut rec) = parse_json(line).ok()? else {
        return None;
    };
    let props = match rec.remove("properties")? {
        Json::Object(m) => m,
        _ => return None,
    };
    let kind = intern(json_str(rec.get("kind")?)?);
    match rec.get("record").and_then(json_str)? {
        "node" => {
            let id = json_str(rec.get("id")?)?.to_string();
            let name = json_str(rec.get("name")?)?.to_string();
            g.insert_node_raw(id, kind, name, props);
        }
        "edge" => {
            let from = json_str(rec.get("from")?)?.to_string();
            let to = json_str(rec.get("to")?)?.to_string();
            g.insert_edge_raw(from, kind, to, props);
        }
        _ => return None,
    }
    Some(())
}

fn json_str(j: &Json) -> Option<&str> {
    match j {
        Json::Str(s) => Some(s.as_str()),
        _ => None,
    }
}

/// Intern a node/edge kind back to `&'static str`. Graph kinds are a small
/// closed vocabulary (the [`crate::ir::ontology`] constants), so the leak is
/// bounded by the number of distinct kind strings ever loaded.
fn intern(s: &str) -> &'static str {
    static KINDS: OnceLock<Mutex<BTreeSet<&'static str>>> = OnceLock::new();
    let set = KINDS.get_or_init(|| Mutex::new(BTreeSet::new()));
    let mut set = set.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    if let Some(k) = set.get(s) {
        return k;
    }
    let leaked: &'static str = Box::leak(s.to_owned().into_boxed_str());
    set.insert(leaked);
    leaked
}

/// True iff every value in the graph round-trips through JSONL to the
/// *identical in-memory `Json` variant*. Byte-identity of serialized output is
/// automatic (same bytes in, same bytes out); this guards the subtler hazard:
/// e.g. `I64(5)` serializes as `5` and would reload as `U64(5)` — identical
/// bytes, different variant — which a downstream `match` could observe.
/// Today's lowerings emit only `Null`/`Bool`/`U64`/`Str`/containers, so this
/// is a tripwire for future emitters, not a working filter.
fn graph_reloads_exactly(g: &Graph) -> bool {
    let vals_ok = |props: &BTreeMap<String, Json>| props.values().all(json_reloads_exactly);
    g.nodes().all(|n| vals_ok(&n.props)) && g.edges().all(|e| vals_ok(&e.props))
}

fn json_reloads_exactly(j: &Json) -> bool {
    match j {
        Json::Null | Json::Bool(_) | Json::U64(_) | Json::Str(_) => true,
        // Non-negative I64 reloads as U64; negative reloads as I64. Exact.
        Json::I64(n) => *n < 0,
        Json::F64(n) => {
            if !n.is_finite() {
                return false; // serializes as null
            }
            let s = format!("{n}");
            // Must keep a float marker (else it reloads as an integer) and
            // must parse back to the same bits (Rust's shortest-roundtrip
            // Display guarantees value equality; -0.0 prints "-0" and is
            // rejected by the marker check).
            s.contains(['.', 'e', 'E'])
                && s.parse::<f64>().is_ok_and(|v| v.to_bits() == n.to_bits())
        }
        Json::Array(items) => items.iter().all(json_reloads_exactly),
        Json::Object(map) => map.values().all(json_reloads_exactly),
    }
}

// ---------------------------------------------------------------------------
// Strict JSON parsing (std-only) — the read half of `core::json`'s writer.
// ---------------------------------------------------------------------------

/// Parse one JSON document (as produced by [`crate::core::json::write_json`]).
/// Strict: trailing garbage, malformed escapes, or invalid numbers are errors.
pub(crate) fn parse_json(text: &str) -> Result<Json, String> {
    let mut p = Parser {
        bytes: text.as_bytes(),
        pos: 0,
    };
    p.skip_ws();
    let value = p.value()?;
    p.skip_ws();
    if p.pos != p.bytes.len() {
        return Err(format!("trailing data at byte {}", p.pos));
    }
    Ok(value)
}

struct Parser<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Parser<'a> {
    fn skip_ws(&mut self) {
        while matches!(self.bytes.get(self.pos), Some(b' ' | b'\t' | b'\n' | b'\r')) {
            self.pos += 1;
        }
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.pos).copied()
    }

    fn expect(&mut self, b: u8) -> Result<(), String> {
        if self.peek() == Some(b) {
            self.pos += 1;
            Ok(())
        } else {
            Err(format!("expected '{}' at byte {}", b as char, self.pos))
        }
    }

    fn value(&mut self) -> Result<Json, String> {
        match self.peek() {
            Some(b'{') => self.object(),
            Some(b'[') => self.array(),
            Some(b'"') => Ok(Json::Str(self.string()?)),
            Some(b't') => self.literal(b"true", Json::Bool(true)),
            Some(b'f') => self.literal(b"false", Json::Bool(false)),
            Some(b'n') => self.literal(b"null", Json::Null),
            Some(c) if c == b'-' || c.is_ascii_digit() => self.number(),
            _ => Err(format!("unexpected byte at {}", self.pos)),
        }
    }

    fn literal(&mut self, word: &[u8], value: Json) -> Result<Json, String> {
        if self.bytes[self.pos..].starts_with(word) {
            self.pos += word.len();
            Ok(value)
        } else {
            Err(format!("bad literal at byte {}", self.pos))
        }
    }

    fn object(&mut self) -> Result<Json, String> {
        self.expect(b'{')?;
        let mut map = BTreeMap::new();
        self.skip_ws();
        if self.peek() == Some(b'}') {
            self.pos += 1;
            return Ok(Json::Object(map));
        }
        loop {
            self.skip_ws();
            let key = self.string()?;
            self.skip_ws();
            self.expect(b':')?;
            self.skip_ws();
            let value = self.value()?;
            map.insert(key, value);
            self.skip_ws();
            match self.peek() {
                Some(b',') => self.pos += 1,
                Some(b'}') => {
                    self.pos += 1;
                    return Ok(Json::Object(map));
                }
                _ => return Err(format!("expected ',' or '}}' at byte {}", self.pos)),
            }
        }
    }

    fn array(&mut self) -> Result<Json, String> {
        self.expect(b'[')?;
        let mut items = Vec::new();
        self.skip_ws();
        if self.peek() == Some(b']') {
            self.pos += 1;
            return Ok(Json::Array(items));
        }
        loop {
            self.skip_ws();
            items.push(self.value()?);
            self.skip_ws();
            match self.peek() {
                Some(b',') => self.pos += 1,
                Some(b']') => {
                    self.pos += 1;
                    return Ok(Json::Array(items));
                }
                _ => return Err(format!("expected ',' or ']' at byte {}", self.pos)),
            }
        }
    }

    fn string(&mut self) -> Result<String, String> {
        self.expect(b'"')?;
        let mut out = String::new();
        loop {
            match self.peek() {
                None => return Err("unterminated string".to_string()),
                Some(b'"') => {
                    self.pos += 1;
                    return Ok(out);
                }
                Some(b'\\') => {
                    self.pos += 1;
                    let esc = self
                        .peek()
                        .ok_or_else(|| "unterminated escape".to_string())?;
                    self.pos += 1;
                    match esc {
                        b'"' => out.push('"'),
                        b'\\' => out.push('\\'),
                        b'/' => out.push('/'),
                        b'n' => out.push('\n'),
                        b'r' => out.push('\r'),
                        b't' => out.push('\t'),
                        b'b' => out.push('\u{08}'),
                        b'f' => out.push('\u{0C}'),
                        b'u' => {
                            let hi = self.hex4()?;
                            let c = if (0xD800..0xDC00).contains(&hi) {
                                // Surrogate pair (our writer never emits these,
                                // but the parser stays a correct JSON reader).
                                if self.peek() != Some(b'\\') {
                                    return Err("lone high surrogate".to_string());
                                }
                                self.pos += 1;
                                self.expect(b'u')?;
                                let lo = self.hex4()?;
                                if !(0xDC00..0xE000).contains(&lo) {
                                    return Err("bad low surrogate".to_string());
                                }
                                let code = 0x10000 + ((hi - 0xD800) << 10) + (lo - 0xDC00);
                                char::from_u32(code)
                                    .ok_or_else(|| "bad surrogate pair".to_string())?
                            } else {
                                char::from_u32(hi)
                                    .ok_or_else(|| "bad unicode escape".to_string())?
                            };
                            out.push(c);
                        }
                        _ => return Err(format!("bad escape at byte {}", self.pos)),
                    }
                }
                Some(_) => {
                    // Consume one UTF-8 scalar: the input is a &str, so byte
                    // boundaries are already valid; find the char at pos.
                    let rest = &self.bytes[self.pos..];
                    let end = self
                        .bytes
                        .iter()
                        .skip(self.pos)
                        .position(|&b| b == b'"' || b == b'\\')
                        .map(|off| self.pos + off)
                        .unwrap_or(self.bytes.len());
                    let chunk = std::str::from_utf8(&rest[..end - self.pos])
                        .map_err(|_| "invalid utf-8 in string".to_string())?;
                    out.push_str(chunk);
                    self.pos = end;
                }
            }
        }
    }

    fn hex4(&mut self) -> Result<u32, String> {
        let end = self.pos + 4;
        if end > self.bytes.len() {
            return Err("truncated unicode escape".to_string());
        }
        let hex = std::str::from_utf8(&self.bytes[self.pos..end])
            .map_err(|_| "bad unicode escape".to_string())?;
        let v = u32::from_str_radix(hex, 16).map_err(|_| "bad unicode escape".to_string())?;
        self.pos = end;
        Ok(v)
    }

    fn number(&mut self) -> Result<Json, String> {
        let start = self.pos;
        let negative = self.peek() == Some(b'-');
        if negative {
            self.pos += 1;
        }
        let mut float = false;
        while let Some(c) = self.peek() {
            match c {
                b'0'..=b'9' => self.pos += 1,
                b'.' | b'e' | b'E' | b'+' | b'-' => {
                    float = true;
                    self.pos += 1;
                }
                _ => break,
            }
        }
        let text = std::str::from_utf8(&self.bytes[start..self.pos])
            .map_err(|_| "bad number".to_string())?;
        if float {
            text.parse::<f64>()
                .map(Json::F64)
                .map_err(|_| format!("bad number '{text}'"))
        } else if negative {
            text.parse::<i64>()
                .map(Json::I64)
                .map_err(|_| format!("bad number '{text}'"))
        } else {
            text.parse::<u64>()
                .map(Json::U64)
                .map_err(|_| format!("bad number '{text}'"))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn roundtrip(j: &Json) -> Json {
        parse_json(&j.to_line()).expect("roundtrip parse")
    }

    #[test]
    fn parser_roundtrips_writer_output() {
        let value = Json::obj([
            ("s", Json::str("a\"\n\t\\b\u{01}λ")),
            ("u", Json::U64(u64::MAX)),
            ("i", Json::I64(-42)),
            ("f", Json::F64(1.5)),
            ("b", Json::Bool(true)),
            ("n", Json::Null),
            (
                "a",
                Json::Array(vec![Json::U64(0), Json::str(""), Json::Bool(false)]),
            ),
            ("o", Json::obj([("k", Json::str("v"))])),
        ]);
        assert_eq!(roundtrip(&value), value);
        // Serialized form is stable through a full round trip too.
        assert_eq!(roundtrip(&value).to_line(), value.to_line());
    }

    #[test]
    fn parser_is_strict() {
        assert!(parse_json("{\"a\":1}garbage").is_err());
        assert!(parse_json("{\"a\":}").is_err());
        assert!(parse_json("[1,]").is_err());
        assert!(parse_json("\"\\q\"").is_err());
        assert!(parse_json("nul").is_err());
        assert!(parse_json("").is_err());
    }

    #[test]
    fn number_variants_map_deterministically() {
        assert_eq!(parse_json("5").unwrap(), Json::U64(5));
        assert_eq!(parse_json("-5").unwrap(), Json::I64(-5));
        assert_eq!(parse_json("5.5").unwrap(), Json::F64(5.5));
        assert_eq!(parse_json("-5.5").unwrap(), Json::F64(-5.5));
        assert_eq!(parse_json("1e3").unwrap(), Json::F64(1000.0));
        assert_eq!(
            parse_json("18446744073709551615").unwrap(),
            Json::U64(u64::MAX)
        );
    }

    #[test]
    fn reload_exactness_guard_rejects_ambiguous_variants() {
        assert!(json_reloads_exactly(&Json::U64(5)));
        assert!(json_reloads_exactly(&Json::I64(-5)));
        assert!(!json_reloads_exactly(&Json::I64(5))); // reloads as U64
        assert!(json_reloads_exactly(&Json::F64(1.5)));
        assert!(!json_reloads_exactly(&Json::F64(5.0))); // prints "5"
        assert!(!json_reloads_exactly(&Json::F64(-0.0))); // prints "-0"
        assert!(!json_reloads_exactly(&Json::F64(f64::NAN))); // prints null
                                                              // Rust Display never uses scientific notation: 1e300 prints as a
                                                              // 301-digit integer, which would not even parse back as u64 — refused.
        assert!(!json_reloads_exactly(&Json::F64(1e300)));
        assert!(!json_reloads_exactly(&Json::Array(vec![Json::I64(1)])));
    }

    #[test]
    fn graph_subgraph_roundtrips_byte_identically() {
        let mut g = Graph::new();
        g.upsert_node(
            "fn::a::b",
            "Function",
            "b",
            vec![
                ("path", Json::str("src/a.rs")),
                ("line", Json::U64(3)),
                ("weird \u{1} name", Json::str("with\nnewline")),
            ],
        );
        g.upsert_node("file::src/a.rs", "File", "a.rs", vec![]);
        g.add_edge(
            "file::src/a.rs",
            "DECLARES",
            "fn::a::b",
            vec![("resolved", Json::Bool(true))],
        );
        g.add_edge("fn::a::b", "CALLS", "ext::c", vec![]);
        let jsonl = g.to_jsonl();

        let mut reloaded = Graph::new();
        for line in jsonl.lines() {
            load_record(&mut reloaded, line).expect("record loads");
        }
        assert_eq!(reloaded.to_jsonl(), jsonl);
        assert_eq!(reloaded.node_count(), g.node_count());
        assert_eq!(reloaded.edge_count(), g.edge_count());
    }

    #[test]
    fn cache_store_load_hit_and_key_mismatch_miss() {
        let tmp =
            std::env::temp_dir().join(format!("tt-cache-test-{}-{}", std::process::id(), line!()));
        let _ = fs::remove_dir_all(&tmp);
        let cache = Cache::open(&tmp, Path::new(".")).expect("open cache");

        let mut sub = Graph::new();
        sub.upsert_node("file::x.rs", "File", "x.rs", vec![]);
        let stats = BatchStats {
            files: 1,
            lossless_files: 1,
            diagnostics: 0,
            error_bytes: 0,
            total_bytes: 10,
        };
        let key = batch_key(
            "rust",
            "pkg",
            &["dep".to_string()],
            &[("x.rs".to_string(), 10, 0xabcd)],
        );
        cache.store("rust", &key, &sub, stats, &["bad.rs".to_string()]);

        let hit = cache.load("rust", &key).expect("hit on identical key");
        assert_eq!(hit.sub.to_jsonl(), sub.to_jsonl());
        assert_eq!(hit.stats, stats);
        assert_eq!(hit.panicked, vec!["bad.rs".to_string()]);

        // One changed content hash is a miss.
        let other = batch_key(
            "rust",
            "pkg",
            &["dep".to_string()],
            &[("x.rs".to_string(), 10, 0xabce)],
        );
        assert!(cache.load("rust", &other).is_none());
        // A corrupt entry is a miss, not an error.
        fs::write(cache.entry_path("rust"), "not json\n").unwrap();
        assert!(cache.load("rust", &key).is_none());

        // Prune removes languages that vanished.
        cache.store("rust", &key, &sub, stats, &[]);
        cache.store("python", &key, &sub, stats, &[]);
        let active: BTreeSet<&str> = ["rust"].into_iter().collect();
        cache.prune(&active);
        assert!(cache.entry_path("rust").exists());
        assert!(!cache.entry_path("python").exists());

        // The cache directory carries a self-ignoring .gitignore.
        assert_eq!(fs::read_to_string(tmp.join(".gitignore")).unwrap(), "*\n");
        let _ = fs::remove_dir_all(&tmp);
    }
}
