//! The `trailtracker.rewrite-proposal/v1` document (ADR-0006).
//!
//! One propose run = one document: the rule identity, the target file and its
//! content fingerprint, the byte-span edits (with full before/after texts and
//! per-edit safety arguments), the recognizer's rejections, and a hash over
//! the whole canonical body. `apply` trusts nothing it cannot re-derive: the
//! hash is recomputed on load, the fingerprint against the file's current
//! bytes, and each edit's `before` against the bytes at its span.
//!
//! Determinism: the document carries **no timestamp** — same binary + same
//! file ⇒ byte-identical proposal, hash included (the dossier precedent:
//! attest content, never a wall clock).

use crate::core::json::{read, Json};
use crate::core::span::{fnv1a_64, ByteSpan};
use crate::rewrite::edit::SpanEdit;

pub const SCHEMA: &str = "trailtracker.rewrite-proposal/v1";

/// One proposed byte-span replacement, with its review payload.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProposedEdit {
    pub span: ByteSpan,
    /// Exact original bytes at `span` (audit + per-span verification).
    pub before: String,
    /// Replacement bytes.
    pub after: String,
    /// One-sentence safety argument.
    pub why_safe: String,
    /// The deterministic CPG evidence consulted (statement ids, edge roles,
    /// def sites) — proposal-scoped ids, self-consistent within the document.
    pub cpg_facts: Vec<String>,
}

/// A near-miss site the recognizer refused, with a machine-readable reason.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rejection {
    pub span: ByteSpan,
    /// snake_case, stable across runs — agents can branch on it.
    pub reason: String,
    /// Human sentence explaining the refusal.
    pub detail: String,
}

/// The full proposal document. `file` is relative to `dir`, so a proposal is
/// portable across checkouts of the same tree.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proposal {
    pub rule_id: String,
    pub rule_version: String,
    pub dir: String,
    pub file: String,
    /// `fnv1a64:<16 hex>` over the target file's exact bytes at propose time.
    pub file_fingerprint: String,
    pub edits: Vec<ProposedEdit>,
    pub rejections: Vec<Rejection>,
}

/// `fnv1a64:<16 hex>` over arbitrary bytes — the change-detection fingerprint
/// (same std-only FNV-1a the dossier and enrich attestations use).
pub fn fingerprint(bytes: &[u8]) -> String {
    format!("fnv1a64:{:016x}", fnv1a_64(bytes))
}

impl Proposal {
    /// The canonical body — every field EXCEPT `proposal_hash`.
    fn body_json(&self) -> Json {
        Json::obj([
            ("schema", Json::str(SCHEMA)),
            (
                "rule",
                Json::obj([
                    ("id", Json::str(self.rule_id.clone())),
                    ("version", Json::str(self.rule_version.clone())),
                ]),
            ),
            ("dir", Json::str(self.dir.clone())),
            ("file", Json::str(self.file.clone())),
            ("file_fingerprint", Json::str(self.file_fingerprint.clone())),
            (
                "edits",
                Json::Array(self.edits.iter().map(edit_json).collect()),
            ),
            (
                "rejections",
                Json::Array(self.rejections.iter().map(rejection_json).collect()),
            ),
        ])
    }

    /// The proposal hash: FNV-1a-64 over the canonical single-line JSON of
    /// the body. Covers every byte of every field — any drift invalidates.
    pub fn hash(&self) -> String {
        fingerprint(self.body_json().to_line().as_bytes())
    }

    /// The complete document (body + `proposal_hash`).
    pub fn to_json(&self) -> Json {
        let Json::Object(mut map) = self.body_json() else {
            unreachable!("body_json builds an object");
        };
        map.insert("proposal_hash".to_string(), Json::str(self.hash()));
        Json::Object(map)
    }

    /// Parse and verify a proposal document. Fail closed: schema mismatch,
    /// missing/odd fields, unknown top-level fields, and a non-verifying
    /// `proposal_hash` are all errors that name the exact problem.
    pub fn parse(text: &str) -> Result<Proposal, String> {
        let read::V::Obj(top) = read::parse(text).map_err(|e| format!("not valid JSON: {e}"))?
        else {
            return Err("the proposal must be a JSON object".to_string());
        };
        const KNOWN: &[&str] = &[
            "schema",
            "rule",
            "dir",
            "file",
            "file_fingerprint",
            "edits",
            "rejections",
            "proposal_hash",
        ];
        for (k, _) in &top {
            if !KNOWN.contains(&k.as_str()) {
                return Err(format!(
                    "unknown field '{k}' (this build understands {SCHEMA})"
                ));
            }
        }
        match get(&top, "schema") {
            Some(read::V::Str(s)) if s == SCHEMA => {}
            Some(read::V::Str(s)) => {
                return Err(format!("unsupported schema '{s}' (expected {SCHEMA})"))
            }
            _ => return Err(format!("missing required field 'schema' ({SCHEMA})")),
        }
        let Some(read::V::Obj(rule)) = get(&top, "rule") else {
            return Err("missing required field 'rule' ({id, version})".to_string());
        };
        let rule_id = req_str(rule, "id", "rule")?;
        let rule_version = req_str(rule, "version", "rule")?;
        let dir = req_str(&top, "dir", "proposal")?;
        let file = req_str(&top, "file", "proposal")?;
        let file_fingerprint = req_str(&top, "file_fingerprint", "proposal")?;

        let Some(read::V::Arr(edit_items)) = get(&top, "edits") else {
            return Err("missing required field 'edits' (an array)".to_string());
        };
        let mut edits = Vec::with_capacity(edit_items.len());
        for (i, item) in edit_items.iter().enumerate() {
            let ctx = format!("edits[{i}]");
            let read::V::Obj(o) = item else {
                return Err(format!("{ctx}: must be an object"));
            };
            edits.push(ProposedEdit {
                span: parse_span(o, &ctx)?,
                before: req_str_allow_empty(o, "before", &ctx)?,
                after: req_str_allow_empty(o, "after", &ctx)?,
                why_safe: req_str(o, "why_safe", &ctx)?,
                cpg_facts: str_array(o, "cpg_facts", &ctx)?,
            });
        }

        let Some(read::V::Arr(rej_items)) = get(&top, "rejections") else {
            return Err("missing required field 'rejections' (an array)".to_string());
        };
        let mut rejections = Vec::with_capacity(rej_items.len());
        for (i, item) in rej_items.iter().enumerate() {
            let ctx = format!("rejections[{i}]");
            let read::V::Obj(o) = item else {
                return Err(format!("{ctx}: must be an object"));
            };
            rejections.push(Rejection {
                span: parse_span(o, &ctx)?,
                reason: req_str(o, "reason", &ctx)?,
                detail: req_str(o, "detail", &ctx)?,
            });
        }

        let proposal = Proposal {
            rule_id,
            rule_version,
            dir,
            file,
            file_fingerprint,
            edits,
            rejections,
        };

        let claimed = req_str(&top, "proposal_hash", "proposal")?;
        let actual = proposal.hash();
        if claimed != actual {
            return Err(format!(
                "proposal_hash does not verify (document says {claimed}, canonical body \
                 hashes to {actual}) — the proposal was modified after propose"
            ));
        }
        Ok(proposal)
    }

    /// The proposal's edits as engine [`SpanEdit`]s.
    pub fn span_edits(&self) -> Vec<SpanEdit> {
        self.edits
            .iter()
            .map(|e| SpanEdit {
                span: e.span,
                replacement: e.after.clone(),
            })
            .collect()
    }
}

fn edit_json(e: &ProposedEdit) -> Json {
    Json::obj([
        ("span", span_json(e.span)),
        ("before", Json::str(e.before.clone())),
        ("after", Json::str(e.after.clone())),
        ("why_safe", Json::str(e.why_safe.clone())),
        (
            "cpg_facts",
            Json::Array(e.cpg_facts.iter().map(|f| Json::str(f.clone())).collect()),
        ),
    ])
}

fn rejection_json(r: &Rejection) -> Json {
    Json::obj([
        ("span", span_json(r.span)),
        ("reason", Json::str(r.reason.clone())),
        ("detail", Json::str(r.detail.clone())),
    ])
}

fn span_json(s: ByteSpan) -> Json {
    Json::obj([
        ("start", Json::U64(s.start as u64)),
        ("end", Json::U64(s.end as u64)),
    ])
}

// --- parse helpers (fail closed, arch.rs style) ------------------------------

fn get<'v>(pairs: &'v [(String, read::V)], key: &str) -> Option<&'v read::V> {
    pairs.iter().find(|(k, _)| k == key).map(|(_, v)| v)
}

fn req_str(pairs: &[(String, read::V)], key: &str, ctx: &str) -> Result<String, String> {
    match get(pairs, key) {
        Some(read::V::Str(s)) if !s.is_empty() => Ok(s.clone()),
        Some(_) => Err(format!("{ctx}: '{key}' must be a non-empty string")),
        None => Err(format!("{ctx}: missing required field '{key}'")),
    }
}

fn req_str_allow_empty(
    pairs: &[(String, read::V)],
    key: &str,
    ctx: &str,
) -> Result<String, String> {
    match get(pairs, key) {
        Some(read::V::Str(s)) => Ok(s.clone()),
        Some(_) => Err(format!("{ctx}: '{key}' must be a string")),
        None => Err(format!("{ctx}: missing required field '{key}'")),
    }
}

fn str_array(pairs: &[(String, read::V)], key: &str, ctx: &str) -> Result<Vec<String>, String> {
    match get(pairs, key) {
        Some(read::V::Arr(items)) => items
            .iter()
            .map(|v| match v {
                read::V::Str(s) => Ok(s.clone()),
                _ => Err(format!("{ctx}: '{key}' items must be strings")),
            })
            .collect(),
        Some(_) => Err(format!("{ctx}: '{key}' must be an array of strings")),
        None => Err(format!("{ctx}: missing required field '{key}'")),
    }
}

fn parse_span(pairs: &[(String, read::V)], ctx: &str) -> Result<ByteSpan, String> {
    let Some(read::V::Obj(o)) = get(pairs, "span") else {
        return Err(format!(
            "{ctx}: missing required field 'span' ({{start, end}})"
        ));
    };
    let num = |key: &str| -> Result<usize, String> {
        match get(o, key) {
            Some(read::V::Num(n)) if *n >= 0.0 && n.fract() == 0.0 => Ok(*n as usize),
            _ => Err(format!(
                "{ctx}: span '{key}' must be a non-negative integer"
            )),
        }
    };
    let (start, end) = (num("start")?, num("end")?);
    if start > end {
        return Err(format!("{ctx}: span start {start} exceeds end {end}"));
    }
    Ok(ByteSpan::new(start, end))
}

// ---------------------------------------------------------------------------
// Unified diff — rendered directly from the edit spans (no LCS heuristics):
// the spans ARE the ground truth of what changed.
// ---------------------------------------------------------------------------

const CONTEXT: usize = 3;

/// A unified diff of `edits` applied to `old`, labeled `a/<path>` /
/// `b/<path>`. Deterministic. `edits` must be valid for `old` (the caller has
/// already run them through the engine's validation).
pub fn unified_diff(path: &str, old: &str, edits: &[SpanEdit]) -> String {
    if edits.is_empty() {
        return String::new();
    }
    let mut sorted: Vec<SpanEdit> = edits.to_vec();
    sorted.sort_by_key(|e| (e.span.start, e.span.end));

    // Line starts (byte offsets), always beginning with 0.
    let mut line_starts: Vec<usize> = vec![0];
    for (i, b) in old.bytes().enumerate() {
        if b == b'\n' {
            line_starts.push(i + 1);
        }
    }
    // A final entry past the end simplifies range math. If the file ends with
    // a newline, the last "line" is empty and unaddressable by edits.
    let line_count = if old.is_empty() || old.ends_with('\n') {
        line_starts.len() - 1
    } else {
        line_starts.len()
    };
    let line_of = |off: usize| -> usize {
        match line_starts.binary_search(&off) {
            Ok(i) => i.min(line_count.saturating_sub(1)),
            Err(i) => (i - 1).min(line_count.saturating_sub(1)),
        }
    };
    let line_start = |l: usize| -> usize { line_starts.get(l).copied().unwrap_or(old.len()) };
    let line_end = |l: usize| -> usize { line_starts.get(l + 1).copied().unwrap_or(old.len()) };

    // Group edits into hunks: an edit joins the previous group when their
    // windows (with context) would overlap or abut.
    struct Group {
        first_line: usize,
        last_line: usize,
        edits: Vec<SpanEdit>,
    }
    let mut groups: Vec<Group> = Vec::new();
    for e in sorted {
        let l0 = line_of(e.span.start as usize);
        let l1 = if e.span.end > e.span.start {
            line_of(e.span.end as usize - 1)
        } else {
            l0
        };
        match groups.last_mut() {
            Some(g) if l0 <= g.last_line + 2 * CONTEXT + 1 => {
                g.last_line = g.last_line.max(l1);
                g.edits.push(e);
            }
            _ => groups.push(Group {
                first_line: l0,
                last_line: l1,
                edits: vec![e],
            }),
        }
    }

    let mut out = String::new();
    out.push_str(&format!("--- a/{path}\n+++ b/{path}\n"));
    let mut new_line_delta: i64 = 0;
    for g in groups {
        let ctx_first = g.first_line.saturating_sub(CONTEXT);
        let ctx_last = (g.last_line + CONTEXT).min(line_count.saturating_sub(1));
        let pre_ctx: Vec<&str> = (ctx_first..g.first_line)
            .map(|l| &old[line_start(l)..line_end(l)])
            .collect();
        let post_ctx: Vec<&str> = (g.last_line + 1..=ctx_last)
            .map(|l| &old[line_start(l)..line_end(l)])
            .collect();

        // Changed window: whole lines first_line..=last_line, old and new.
        let ws = line_start(g.first_line);
        let we = line_end(g.last_line);
        let old_window = &old[ws..we];
        let mut new_window = String::new();
        let mut cursor = ws;
        for e in &g.edits {
            new_window.push_str(&old[cursor..e.span.start as usize]);
            new_window.push_str(&e.replacement);
            cursor = e.span.end as usize;
        }
        new_window.push_str(&old[cursor..we]);

        let old_lines = split_keep_newlines(old_window);
        let new_lines = split_keep_newlines(&new_window);

        let old_start = ctx_first + 1; // 1-based
        let old_count = pre_ctx.len() + old_lines.len() + post_ctx.len();
        let new_start = (old_start as i64 + new_line_delta) as usize;
        let new_count = pre_ctx.len() + new_lines.len() + post_ctx.len();
        out.push_str(&format!(
            "@@ -{old_start},{old_count} +{new_start},{new_count} @@\n"
        ));
        for l in &pre_ctx {
            push_diff_line(&mut out, ' ', l);
        }
        for l in &old_lines {
            push_diff_line(&mut out, '-', l);
        }
        for l in &new_lines {
            push_diff_line(&mut out, '+', l.as_str());
        }
        for l in &post_ctx {
            push_diff_line(&mut out, ' ', l);
        }
        new_line_delta += new_lines.len() as i64 - old_lines.len() as i64;
    }
    out
}

/// Split into lines, each keeping its trailing newline (the last may lack one).
fn split_keep_newlines(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut start = 0;
    for (i, b) in text.bytes().enumerate() {
        if b == b'\n' {
            out.push(text[start..=i].to_string());
            start = i + 1;
        }
    }
    if start < text.len() {
        out.push(text[start..].to_string());
    }
    out
}

/// One diff line; a missing trailing newline gets the standard marker.
fn push_diff_line(out: &mut String, sign: char, line: &str) {
    out.push(sign);
    if let Some(stripped) = line.strip_suffix('\n') {
        out.push_str(stripped);
        out.push('\n');
    } else {
        out.push_str(line);
        out.push_str("\n\\ No newline at end of file\n");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> Proposal {
        Proposal {
            rule_id: "dead-branch-elim".to_string(),
            rule_version: "1".to_string(),
            dir: ".".to_string(),
            file: "src/lib.rs".to_string(),
            file_fingerprint: fingerprint(b"fn main() {}\n"),
            edits: vec![ProposedEdit {
                span: ByteSpan::new(3, 7),
                before: "main".to_string(),
                after: "start".to_string(),
                why_safe: "test fixture".to_string(),
                cpg_facts: vec!["fact one".to_string()],
            }],
            rejections: vec![Rejection {
                span: ByteSpan::new(0, 2),
                reason: "not_recognized".to_string(),
                detail: "fixture rejection".to_string(),
            }],
        }
    }

    #[test]
    fn fingerprint_matches_reference_vectors() {
        assert_eq!(fingerprint(b""), "fnv1a64:cbf29ce484222325");
        assert_eq!(fingerprint(b"a"), "fnv1a64:af63dc4c8601ec8c");
    }

    #[test]
    fn round_trips_through_json() {
        let p = sample();
        let text = p.to_json().to_line();
        let back = Proposal::parse(&text).expect("parse");
        assert_eq!(back, p);
    }

    #[test]
    fn hash_is_deterministic_and_content_bound() {
        let p = sample();
        assert_eq!(p.hash(), p.hash());
        let mut q = p.clone();
        q.edits[0].after = "tampered".to_string();
        assert_ne!(p.hash(), q.hash());
    }

    #[test]
    fn tampered_document_fails_parse() {
        let p = sample();
        let text = p.to_json().to_line();
        let tampered = text.replace("\"after\":\"start\"", "\"after\":\"evil\"");
        assert_ne!(text, tampered, "tamper must hit");
        let err = Proposal::parse(&tampered).unwrap_err();
        assert!(err.contains("proposal_hash does not verify"), "{err}");
    }

    #[test]
    fn unknown_fields_are_rejected() {
        let p = sample();
        let text = p.to_json().to_line();
        let smuggled = text.replacen('{', "{\"skip_checks\":true,", 1);
        let err = Proposal::parse(&smuggled).unwrap_err();
        assert!(err.contains("unknown field"), "{err}");
    }

    #[test]
    fn wrong_schema_is_rejected() {
        let err = Proposal::parse("{\"schema\":\"bogus/v9\"}").unwrap_err();
        assert!(err.contains("unsupported schema"), "{err}");
    }

    #[test]
    fn diff_renders_replacement_with_context() {
        let old = "line one\nline two\nline three\nline four\nline five\n\
                   line six\nline seven\nline eight\n";
        // Replace "three" (bytes 23..28).
        assert_eq!(&old[23..28], "three");
        let edits = vec![SpanEdit {
            span: ByteSpan::new(23, 28),
            replacement: "3".to_string(),
        }];
        let diff = unified_diff("f.txt", old, &edits);
        assert!(diff.starts_with("--- a/f.txt\n+++ b/f.txt\n"), "{diff}");
        // GNU `diff -U3` on the same change emits exactly this hunk header
        // (lines 1..=6: two lines of pre-context exist, three of post).
        assert!(diff.contains("@@ -1,6 +1,6 @@\n"), "{diff}");
        assert!(diff.contains("-line three\n"), "{diff}");
        assert!(diff.contains("+line 3\n"), "{diff}");
        assert!(diff.contains(" line two\n"), "{diff}");
        assert!(diff.contains(" line six\n"), "{diff}");
    }

    #[test]
    fn diff_merges_nearby_edits_into_one_hunk() {
        let old = "a\nb\nc\nd\ne\n";
        let edits = vec![
            SpanEdit {
                span: ByteSpan::new(0, 1),
                replacement: "A".to_string(),
            },
            SpanEdit {
                span: ByteSpan::new(4, 5),
                replacement: "C".to_string(),
            },
        ];
        let diff = unified_diff("f.txt", old, &edits);
        assert_eq!(
            diff.matches("@@").count(),
            2,
            "one hunk (2 markers):\n{diff}"
        );
        assert!(diff.contains("-a\n"), "{diff}");
        assert!(diff.contains("+A\n"), "{diff}");
        assert!(diff.contains("-c\n"), "{diff}");
        assert!(diff.contains("+C\n"), "{diff}");
    }

    #[test]
    fn diff_handles_missing_trailing_newline() {
        let old = "one\ntwo";
        let edits = vec![SpanEdit {
            span: ByteSpan::new(4, 7),
            replacement: "TWO".to_string(),
        }];
        let diff = unified_diff("f.txt", old, &edits);
        assert!(
            diff.contains("-two\n\\ No newline at end of file\n"),
            "{diff}"
        );
        assert!(
            diff.contains("+TWO\n\\ No newline at end of file\n"),
            "{diff}"
        );
    }

    #[test]
    fn diff_is_deterministic() {
        let old = "x\ny\nz\n";
        let edits = vec![SpanEdit {
            span: ByteSpan::new(2, 3),
            replacement: "Y".to_string(),
        }];
        assert_eq!(
            unified_diff("f", old, &edits),
            unified_diff("f", old, &edits)
        );
    }
}
