//! The optional LLM naming pass: **deterministic membership + attested
//! semantics** (`trailtracker enrich-domains`).
//!
//! The domains extractor ([`crate::extract::domains`]) recovers bounded
//! contexts *structurally* — pure, deterministic, airgap-safe — and names them
//! with honest structural labels (`control-plane`, `Ordering`). This module is
//! the explicitly-separate semantic layer on top: it shows an LLM each
//! cluster's **evidence pack** (structural label, member units, top files, top
//! symbols, dominant archetypes, coupling neighbors) and takes back ONLY
//! `{name, description, responsibilities[]}` per cluster. The LLM never sees a
//! choice about membership and its reply cannot alter it: cluster ids, member
//! sets, and every count are computed here, before the call, by the same
//! [`assign_domains`] the airgapped `extract domains` command uses — the six
//! deterministic cluster fields (`domain`, `label`, `unit_count`,
//! `file_count`, `symbol_count`, `confidence`) are byte-identical to the
//! domains-view node properties, and a unit test pins that.
//!
//! # Determinism honesty
//!
//! Enrichment is **NOT byte-stable**: an LLM names the clusters, and the same
//! evidence can be worded differently across runs. It is **ATTESTED** instead:
//! the output carries the backend command, the model id (when the backend
//! reports one), an FNV-1a-64 hash of the exact evidence pack the model saw
//! (`prompt_hash`), and a timestamp. Re-running names the *same* deterministic
//! clusters — the cluster ids and every structural field are byte-stable; only
//! the three semantic fields may vary. Everything else in the trailtracker
//! runtime stays LLM-free; this command is the one surface that requires an
//! external backend, and it fails loudly (exit 4) rather than fake a name.
//!
//! # Backend contract
//!
//! The crate is std-only (no HTTPS), so the LLM is reached by shelling out.
//! `TRAILTRACKER_ENRICH_CMD` names the backend: any command line that accepts
//! the prompt as its **final argument** and prints the model's JSON reply
//! (raw, fenced, or wrapped in a Claude-CLI `{"result": ...}` envelope) on
//! stdout. The default is the Claude Code CLI:
//! `claude -p --output-format json --model haiku`. The prompt always ends
//! with the line `EVIDENCE:` followed by the evidence-pack JSON array, so
//! non-LLM backends (mocks, proxies) can parse it mechanically.

use std::collections::{BTreeMap, BTreeSet};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use crate::core::json::{read as value, Json};
use crate::extract::archetypes;
use crate::extract::domains::{assign_domains, DomainAssignment};
use crate::graph::Graph;
use crate::ir::ontology::{node as ont, parent_relation, relation};

/// Environment variable naming the LLM backend command. See the module docs
/// for the contract; empty/whitespace values fall back to [`DEFAULT_BACKEND`].
pub const ENV_BACKEND: &str = "TRAILTRACKER_ENRICH_CMD";

/// The default backend: the Claude Code CLI in print mode. `--output-format
/// json` wraps the reply in a `{"result": ...}` envelope that
/// [`extract_reply_text`] unwraps (and mines for the model id).
pub const DEFAULT_BACKEND: &str = "claude -p --output-format json --model haiku";

/// Evidence-pack budgets: enough context to name a cluster, small enough to
/// stay cheap on a haiku-class model even at [`MAX_DOMAINS`]-scale repos.
///
/// [`MAX_DOMAINS`]: crate::extract::domains
const MAX_UNITS: usize = 8;
/// See [`MAX_UNITS`].
const MAX_FILES: usize = 10;
/// See [`MAX_UNITS`].
const MAX_SYMBOLS: usize = 15;
/// See [`MAX_UNITS`].
const MAX_ARCHETYPES: usize = 6;
/// See [`MAX_UNITS`].
const MAX_NEIGHBORS: usize = 6;

// ---------------------------------------------------------------------------
// Evidence pack: everything the LLM is allowed to see, per cluster
// ---------------------------------------------------------------------------

/// The deterministic evidence for one cluster — the *entire* input the LLM
/// gets about it. Built purely from the base graph + [`DomainAssignment`];
/// same graph, same evidence, same [`fnv1a64`] hash.
#[derive(Clone, Debug)]
pub struct ClusterEvidence {
    /// `domain::{name}` — the exact node id the domains extractor emits.
    pub cluster_id: String,
    /// The domain display name (the deterministic structural name).
    pub domain: String,
    /// The structural label (same value the domains view carries).
    pub label: String,
    /// Label confidence from the domains view: `high`/`medium`/`low`.
    pub confidence: &'static str,
    /// Distinct units spanned by the member files.
    pub unit_count: u64,
    /// Member file count.
    pub file_count: u64,
    /// Symbols owned by the member files.
    pub symbol_count: u64,
    /// Largest member units: `(unit, file_count, symbol_count)`.
    pub units: Vec<(String, u64, u64)>,
    /// Member file paths with the most symbols.
    pub top_files: Vec<String>,
    /// Most-connected member symbols, as `Name (Kind)` strings.
    pub top_symbols: Vec<String>,
    /// Dominant architectural archetypes: `(archetype, count)`.
    pub archetypes: Vec<(String, u64)>,
    /// Domains this cluster depends on: `(domain, edge_count)`.
    pub depends_on: Vec<(String, u64)>,
    /// Domains that depend on this cluster: `(domain, edge_count)`.
    pub depended_on_by: Vec<(String, u64)>,
}

impl ClusterEvidence {
    /// The evidence as one JSON object (sorted keys, deterministic bytes).
    pub fn to_json(&self) -> Json {
        let pairs = |v: &[(String, u64)]| {
            Json::Array(
                v.iter()
                    .map(|(name, count)| {
                        Json::obj([
                            ("name", Json::str(name.clone())),
                            ("count", Json::U64(*count)),
                        ])
                    })
                    .collect(),
            )
        };
        Json::obj([
            ("cluster_id", Json::str(self.cluster_id.clone())),
            ("structural_label", Json::str(self.label.clone())),
            ("confidence", Json::str(self.confidence)),
            ("unit_count", Json::U64(self.unit_count)),
            ("file_count", Json::U64(self.file_count)),
            ("symbol_count", Json::U64(self.symbol_count)),
            (
                "units",
                Json::Array(
                    self.units
                        .iter()
                        .map(|(unit, files, symbols)| {
                            Json::obj([
                                ("unit", Json::str(unit.clone())),
                                ("files", Json::U64(*files)),
                                ("symbols", Json::U64(*symbols)),
                            ])
                        })
                        .collect(),
                ),
            ),
            (
                "top_files",
                Json::Array(
                    self.top_files
                        .iter()
                        .map(|p| Json::str(p.as_str()))
                        .collect(),
                ),
            ),
            (
                "top_symbols",
                Json::Array(
                    self.top_symbols
                        .iter()
                        .map(|s| Json::str(s.as_str()))
                        .collect(),
                ),
            ),
            ("archetypes", pairs(&self.archetypes)),
            ("depends_on", pairs(&self.depends_on)),
            ("depended_on_by", pairs(&self.depended_on_by)),
        ])
    }
}

/// Build the per-cluster evidence packs from the base graph and the
/// deterministic assignment. Clusters are ordered largest-first
/// (symbol mass desc, then name) so the model reads the spine of the
/// codebase before its satellites; the order is deterministic.
pub fn build_evidence(graph: &Graph, assignment: &DomainAssignment) -> Vec<ClusterEvidence> {
    // Node kinds + degree (edge touches) for symbol salience.
    let kind_of: BTreeMap<&str, &'static str> =
        graph.nodes().map(|n| (n.id.as_str(), n.kind)).collect();
    let mut degree: BTreeMap<&str, u64> = BTreeMap::new();
    for e in graph.edges() {
        *degree.entry(e.from.as_str()).or_default() += 1;
        *degree.entry(e.to.as_str()).or_default() += 1;
    }
    // Direct file → declared-symbol children (containment out of a File).
    let mut file_children: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for e in graph.edges() {
        if parent_relation(e.kind) != Some(relation::CONTAINMENT) {
            continue;
        }
        if kind_of.get(e.from.as_str()).copied() != Some(ont::FILE) {
            continue;
        }
        let child_kind = kind_of.get(e.to.as_str()).copied();
        if matches!(
            child_kind,
            Some(ont::FUNCTION) | Some(ont::TYPE) | Some(ont::CONSTANT) | Some(ont::MACRO)
        ) {
            file_children
                .entry(e.from.as_str())
                .or_default()
                .push(e.to.as_str());
        }
    }
    let node_by_id: BTreeMap<&str, &crate::graph::GraphNode> =
        graph.nodes().map(|n| (n.id.as_str(), n)).collect();

    // Domain → member file ids.
    let mut members: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for (f, d) in &assignment.file_domain {
        members.entry(d.as_str()).or_default().push(f.as_str());
    }

    let mut out: Vec<ClusterEvidence> = Vec::new();
    for (name, info) in &assignment.domains {
        if info.reason.is_some() {
            // Infrastructure groups (Build & Tooling, Documentation,
            // Generated, Repo root) already carry their honest name — the
            // LLM naming pass only upgrades *business* clusters.
            continue;
        }
        let files = members.get(name.as_str()).cloned().unwrap_or_default();

        // Units: per-unit (files, symbols), largest first.
        let mut unit_agg: BTreeMap<&str, (u64, u64)> = BTreeMap::new();
        for f in &files {
            let e = unit_agg
                .entry(assignment.file_unit[*f].as_str())
                .or_default();
            e.0 += 1;
            e.1 += assignment.file_symbols.get(*f).copied().unwrap_or(0);
        }
        let mut units: Vec<(String, u64, u64)> = unit_agg
            .iter()
            .map(|(u, (fc, sc))| (u.to_string(), *fc, *sc))
            .collect();
        units.sort_by(|a, b| b.2.cmp(&a.2).then_with(|| a.0.cmp(&b.0)));
        units.truncate(MAX_UNITS);

        // Top files by owned-symbol count.
        let mut ranked_files: Vec<(&str, u64)> = files
            .iter()
            .map(|f| {
                (
                    assignment.file_path[*f].as_str(),
                    assignment.file_symbols.get(*f).copied().unwrap_or(0),
                )
            })
            .collect();
        ranked_files.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(b.0)));
        let top_files: Vec<String> = ranked_files
            .iter()
            .take(MAX_FILES)
            .map(|(p, _)| (*p).to_string())
            .collect();

        // Top symbols (most-connected first) + archetype tally over the
        // symbols the member files directly declare.
        let mut symbols: Vec<(u64, &str, &'static str)> = Vec::new();
        let mut archetype_tally: BTreeMap<&'static str, u64> = BTreeMap::new();
        for f in &files {
            for child in file_children.get(*f).into_iter().flatten() {
                let Some(node) = node_by_id.get(child) else {
                    continue;
                };
                symbols.push((
                    degree.get(child).copied().unwrap_or(0),
                    node.name.as_str(),
                    node.kind,
                ));
                let archetype = archetypes::classify(node);
                if archetype != archetypes::archetype::UNCLASSIFIED {
                    *archetype_tally.entry(archetype).or_default() += 1;
                }
            }
        }
        symbols.sort_by(|a, b| b.0.cmp(&a.0).then_with(|| a.1.cmp(b.1)));
        let mut seen: BTreeSet<&str> = BTreeSet::new();
        let mut top_symbols: Vec<String> = Vec::new();
        for (_, sym_name, kind) in &symbols {
            if top_symbols.len() == MAX_SYMBOLS {
                break;
            }
            if seen.insert(sym_name) {
                top_symbols.push(format!("{sym_name} ({kind})"));
            }
        }
        let mut archetype_list: Vec<(String, u64)> = archetype_tally
            .iter()
            .map(|(a, c)| ((*a).to_string(), *c))
            .collect();
        archetype_list.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
        archetype_list.truncate(MAX_ARCHETYPES);

        // Coupling neighbors from the counted inter-domain dependencies.
        let neighbor = |outgoing: bool| -> Vec<(String, u64)> {
            let mut v: Vec<(String, u64)> = assignment
                .domain_deps
                .iter()
                .filter_map(|((from, to), count)| {
                    if outgoing && from == name {
                        Some((to.clone(), *count))
                    } else if !outgoing && to == name {
                        Some((from.clone(), *count))
                    } else {
                        None
                    }
                })
                .collect();
            v.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
            v.truncate(MAX_NEIGHBORS);
            v
        };

        out.push(ClusterEvidence {
            cluster_id: format!("domain::{name}"),
            domain: name.clone(),
            label: info.label.clone(),
            confidence: info.confidence,
            unit_count: info.unit_count,
            file_count: info.file_count,
            symbol_count: info.symbol_count,
            units,
            top_files,
            top_symbols,
            archetypes: archetype_list,
            depends_on: neighbor(true),
            depended_on_by: neighbor(false),
        });
    }
    // Largest clusters first; deterministic tie-break on the id.
    out.sort_by(|a, b| {
        b.symbol_count
            .cmp(&a.symbol_count)
            .then_with(|| a.cluster_id.cmp(&b.cluster_id))
    });
    out
}

/// The whole evidence pack as one compact JSON array — the exact string that
/// is hashed ([`fnv1a64`]) and embedded in the prompt.
pub fn evidence_pack(evidence: &[ClusterEvidence]) -> String {
    Json::Array(evidence.iter().map(ClusterEvidence::to_json).collect()).to_line()
}

// ---------------------------------------------------------------------------
// Prompt + attestation hash
// ---------------------------------------------------------------------------

/// FNV-1a 64-bit over the input bytes: tiny, std-only, and stable across
/// platforms — exactly enough to attest *which* evidence a reply named.
pub fn fnv1a64(data: &str) -> u64 {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for byte in data.bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    hash
}

/// The strict naming prompt. Ends with `EVIDENCE:` + the evidence-pack JSON
/// (the documented marker for mechanical backends). The model is told, three
/// different ways, that membership is fixed and only JSON comes back.
pub fn build_prompt(evidence_pack: &str) -> String {
    format!(
        "You are the naming pass over deterministic code clusters.\n\
         \n\
         A structural algorithm has already clustered a codebase into the domains\n\
         listed under EVIDENCE. Cluster membership is FIXED: do not add, remove,\n\
         merge, split, or re-assign anything. Your only job is to give each cluster\n\
         a semantic name and description grounded in its evidence.\n\
         \n\
         Reply with ONLY a JSON array (no prose, no markdown fence) containing one\n\
         object per cluster:\n\
         [{{\"cluster_id\": \"<copied exactly from the evidence>\",\n\
         \x20 \"name\": \"<PascalCase compound, e.g. ControlPlaneAPI, DashboardWebUI>\",\n\
         \x20 \"description\": \"<exactly one sentence: what this cluster does>\",\n\
         \x20 \"responsibilities\": [\"<3-6 short noun phrases>\", \"...\"]}}]\n\
         \n\
         Rules:\n\
         - cover every cluster exactly once; copy each cluster_id verbatim.\n\
         - name: 1-4 concatenated PascalCase words, letters and digits only,\n\
         \x20 unique across clusters.\n\
         - description: one sentence stating what the cluster does and its tech\n\
         \x20 when evident (language, framework).\n\
         - responsibilities: 3-6 noun phrases of 2-4 words each.\n\
         \n\
         EVIDENCE:\n\
         {evidence_pack}"
    )
}

// ---------------------------------------------------------------------------
// Backend invocation
// ---------------------------------------------------------------------------

/// The backend command line: [`ENV_BACKEND`] when set and non-blank,
/// otherwise [`DEFAULT_BACKEND`].
pub fn backend_command() -> String {
    match std::env::var(ENV_BACKEND) {
        Ok(cmd) if !cmd.trim().is_empty() => cmd,
        _ => DEFAULT_BACKEND.to_string(),
    }
}

/// Run the backend: split `cmd` on whitespace, append the prompt as the final
/// argument, capture stdout. Every failure mode gets its own honest message —
/// enrichment never degrades into invented names.
pub fn run_backend(cmd: &str, prompt: &str) -> Result<String, String> {
    let mut parts = cmd.split_whitespace();
    let program = parts
        .next()
        .ok_or_else(|| format!("enrichment backend command is empty ({ENV_BACKEND})"))?;
    let output = Command::new(program)
        .args(parts)
        .arg(prompt)
        .output()
        .map_err(|e| format!("enrichment backend '{program}' failed to start: {e}"))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let snippet: String = stderr.trim().chars().take(300).collect();
        return Err(format!(
            "enrichment backend '{cmd}' exited with {}: {snippet}",
            output.status
        ));
    }
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    if stdout.trim().is_empty() {
        return Err(format!(
            "enrichment backend '{cmd}' returned an empty reply"
        ));
    }
    Ok(stdout)
}

// ---------------------------------------------------------------------------
// Reply parsing (defensive): envelope → text → JSON array → validated namings
// ---------------------------------------------------------------------------

/// One cluster's semantic naming, exactly the three fields the LLM owns.
#[derive(Clone, Debug, PartialEq)]
pub struct ClusterNaming {
    /// Must match a [`ClusterEvidence::cluster_id`] verbatim.
    pub cluster_id: String,
    /// PascalCase name (whitespace/`-`/`_` are stripped as cosmetic noise;
    /// anything else non-alphanumeric is rejected, never repaired).
    pub name: String,
    /// One-sentence description.
    pub description: String,
    /// Short noun phrases; at least one, blanks dropped.
    pub responsibilities: Vec<String>,
}

/// Unwrap a backend stdout into (reply text, model id when reported).
///
/// The Claude CLI's `--output-format json` prints a
/// `{"type":"result","result":"<text>", ..., "modelUsage":{"<model>":{...}}}`
/// envelope; anything that doesn't parse as such an object is treated as the
/// raw reply text itself (covering `TRAILTRACKER_ENRICH_CMD` backends that
/// print the model reply directly).
pub fn extract_reply_text(stdout: &str) -> (String, Option<String>) {
    if let Ok(value::V::Obj(pairs)) = value::parse(stdout.trim()) {
        let get = |key: &str| pairs.iter().find(|(k, _)| k == key).map(|(_, v)| v);
        if let Some(value::V::Str(result)) = get("result") {
            let model = match get("modelUsage") {
                Some(value::V::Obj(usage)) => usage.first().map(|(k, _)| k.clone()),
                _ => match get("model") {
                    Some(value::V::Str(m)) => Some(m.clone()),
                    _ => None,
                },
            };
            return (result.clone(), model);
        }
    }
    (stdout.to_string(), None)
}

/// Parse the model's reply text into namings. Accepts, in order: the raw
/// trimmed text as a JSON array; the contents of the first fenced code block;
/// the first-`[`-to-last-`]` slice (prose-wrapped arrays). Every accepted
/// object must carry the full contract; nothing is invented for it.
pub fn parse_reply(text: &str) -> Result<Vec<ClusterNaming>, String> {
    let mut candidates: Vec<String> = vec![text.trim().to_string()];
    if let Some(fenced) = fenced_block(text) {
        candidates.push(fenced);
    }
    if let (Some(start), Some(end)) = (text.find('['), text.rfind(']')) {
        if start < end {
            candidates.push(text[start..=end].to_string());
        }
    }
    let mut last_err = String::from("reply contained no JSON array");
    for candidate in &candidates {
        match value::parse(candidate) {
            Ok(value::V::Arr(items)) => return namings_from(&items),
            Ok(_) => last_err = "reply JSON is not an array".to_string(),
            Err(e) => last_err = e,
        }
    }
    Err(format!(
        "could not parse the backend reply as a JSON array of cluster namings: {last_err}"
    ))
}

/// The contents of the first ```-fenced block, tolerating a language tag.
fn fenced_block(text: &str) -> Option<String> {
    let open = text.find("```")?;
    let after_tick = &text[open + 3..];
    let body_start = after_tick.find('\n')? + 1;
    let body = &after_tick[body_start..];
    let close = body.find("```")?;
    Some(body[..close].trim().to_string())
}

/// Convert parsed JSON array items into validated [`ClusterNaming`]s.
fn namings_from(items: &[value::V]) -> Result<Vec<ClusterNaming>, String> {
    let mut out = Vec::new();
    for (i, item) in items.iter().enumerate() {
        let value::V::Obj(pairs) = item else {
            return Err(format!("reply item {i} is not an object"));
        };
        let get = |key: &str| pairs.iter().find(|(k, _)| k == key).map(|(_, v)| v);
        let get_str = |key: &str| match get(key) {
            Some(value::V::Str(s)) => Some(s.trim().to_string()),
            _ => None,
        };
        let cluster_id = get_str("cluster_id")
            .filter(|s| !s.is_empty())
            .ok_or_else(|| format!("reply item {i} is missing 'cluster_id'"))?;
        let raw_name = get_str("name")
            .filter(|s| !s.is_empty())
            .ok_or_else(|| format!("reply item {i} ({cluster_id}) is missing 'name'"))?;
        let name = normalize_name(&raw_name).ok_or_else(|| {
            format!("reply item {i} ({cluster_id}) has a non-PascalCase name: '{raw_name}'")
        })?;
        let description = get_str("description")
            .filter(|s| !s.is_empty())
            .ok_or_else(|| format!("reply item {i} ({cluster_id}) is missing 'description'"))?;
        let responsibilities: Vec<String> = match get("responsibilities") {
            Some(value::V::Arr(rs)) => rs
                .iter()
                .filter_map(|r| match r {
                    value::V::Str(s) if !s.trim().is_empty() => Some(s.trim().to_string()),
                    _ => None,
                })
                .collect(),
            _ => Vec::new(),
        };
        if responsibilities.is_empty() {
            return Err(format!(
                "reply item {i} ({cluster_id}) has no usable 'responsibilities'"
            ));
        }
        out.push(ClusterNaming {
            cluster_id,
            name,
            description,
            responsibilities,
        });
    }
    Ok(out)
}

/// Cosmetic-only name normalization: strip whitespace/`-`/`_` (a model that
/// answers "Control Plane API" meant `ControlPlaneAPI`), then require a
/// non-empty, purely alphanumeric result. Anything else is rejected — a bad
/// name is a backend failure, never something to repair into fiction.
fn normalize_name(raw: &str) -> Option<String> {
    let cleaned: String = raw
        .chars()
        .filter(|c| !c.is_whitespace() && *c != '-' && *c != '_')
        .collect();
    (!cleaned.is_empty() && cleaned.chars().all(|c| c.is_ascii_alphanumeric())).then_some(cleaned)
}

/// Check the reply against the evidence: every cluster named exactly once, no
/// unknown ids. Returns namings keyed by cluster id.
pub fn validate(
    namings: Vec<ClusterNaming>,
    evidence: &[ClusterEvidence],
) -> Result<BTreeMap<String, ClusterNaming>, String> {
    let known: BTreeSet<&str> = evidence.iter().map(|e| e.cluster_id.as_str()).collect();
    let mut by_id: BTreeMap<String, ClusterNaming> = BTreeMap::new();
    for naming in namings {
        if !known.contains(naming.cluster_id.as_str()) {
            return Err(format!(
                "backend named unknown cluster '{}' (known: {})",
                naming.cluster_id,
                known.iter().copied().collect::<Vec<_>>().join(", ")
            ));
        }
        let id = naming.cluster_id.clone();
        if by_id.insert(id.clone(), naming).is_some() {
            return Err(format!("backend named cluster '{id}' twice"));
        }
    }
    let missing: Vec<&str> = known
        .iter()
        .copied()
        .filter(|id| !by_id.contains_key(*id))
        .collect();
    if !missing.is_empty() {
        return Err(format!(
            "backend reply did not name every cluster; missing: {}",
            missing.join(", ")
        ));
    }
    Ok(by_id)
}

// ---------------------------------------------------------------------------
// Orchestration + rendering
// ---------------------------------------------------------------------------

/// The attestation block: who named these clusters, from exactly which
/// evidence, when. This is what makes the non-byte-stable output auditable.
#[derive(Clone, Debug)]
pub struct Attestation {
    /// The backend command line that was executed.
    pub backend: String,
    /// The model id the backend reported, or `"unreported"`.
    pub model: String,
    /// `fnv1a64:<16-hex>` over the exact evidence-pack JSON the model saw.
    pub prompt_hash: String,
    /// UTC ISO-8601 wall-clock time of the enrichment run.
    pub timestamp: String,
}

/// A fully enriched cluster: the deterministic evidence plus the attested
/// semantic naming. Membership fields come only from `evidence`.
#[derive(Clone, Debug)]
pub struct EnrichedCluster {
    /// The deterministic side (identical to the domains view).
    pub evidence: ClusterEvidence,
    /// The LLM side (name/description/responsibilities only).
    pub naming: ClusterNaming,
}

/// The result of one enrichment run.
#[derive(Clone, Debug)]
pub struct Enrichment {
    /// Clusters, largest first (the [`build_evidence`] order).
    pub clusters: Vec<EnrichedCluster>,
    /// See [`Attestation`].
    pub attestation: Attestation,
}

/// Run the full pass over an already-analyzed base graph: deterministic
/// clustering → evidence packs → one backend call → validated namings.
/// Errors are complete sentences ready for the CLI's `trailtracker:` line.
pub fn enrich(graph: &Graph) -> Result<Enrichment, String> {
    let assignment = assign_domains(graph);
    let evidence = build_evidence(graph, &assignment);
    if evidence.is_empty() {
        return Err(
            "no domain clusters to enrich (the domains view of this directory is empty)"
                .to_string(),
        );
    }
    let pack = evidence_pack(&evidence);
    let prompt = build_prompt(&pack);
    let backend = backend_command();
    let stdout = run_backend(&backend, &prompt)?;
    let (reply, model) = extract_reply_text(&stdout);
    let namings = parse_reply(&reply)?;
    let mut by_id = validate(namings, &evidence)?;

    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    let attestation = Attestation {
        backend,
        model: model.unwrap_or_else(|| "unreported".to_string()),
        prompt_hash: format!("fnv1a64:{:016x}", fnv1a64(&pack)),
        timestamp: iso8601_utc(now),
    };
    let clusters = evidence
        .into_iter()
        .map(|ev| {
            let naming = by_id
                .remove(&ev.cluster_id)
                .expect("validate() guarantees coverage");
            EnrichedCluster {
                evidence: ev,
                naming,
            }
        })
        .collect();
    Ok(Enrichment {
        clusters,
        attestation,
    })
}

impl Enrichment {
    /// The `trailtracker.enrich/v1` document. Each cluster carries the six
    /// deterministic fields byte-identical to the domains-view node props,
    /// its subdomain (unit) names, and the three attested semantic fields.
    pub fn to_json(&self, dir: &str) -> Json {
        let clusters: Vec<Json> = self
            .clusters
            .iter()
            .map(|c| {
                Json::obj([
                    ("cluster_id", Json::str(c.evidence.cluster_id.clone())),
                    ("domain", Json::str(c.evidence.domain.clone())),
                    ("label", Json::str(c.evidence.label.clone())),
                    ("unit_count", Json::U64(c.evidence.unit_count)),
                    ("file_count", Json::U64(c.evidence.file_count)),
                    ("symbol_count", Json::U64(c.evidence.symbol_count)),
                    ("confidence", Json::str(c.evidence.confidence)),
                    (
                        "subdomains",
                        Json::Array(
                            c.evidence
                                .units
                                .iter()
                                .map(|(u, _, _)| Json::str(u.clone()))
                                .collect(),
                        ),
                    ),
                    ("name", Json::str(c.naming.name.clone())),
                    ("description", Json::str(c.naming.description.clone())),
                    (
                        "responsibilities",
                        Json::Array(
                            c.naming
                                .responsibilities
                                .iter()
                                .map(|r| Json::str(r.clone()))
                                .collect(),
                        ),
                    ),
                ])
            })
            .collect();
        Json::obj([
            ("schema", Json::str("trailtracker.enrich/v1")),
            ("command", Json::str("enrich-domains")),
            ("dir", Json::str(dir)),
            ("clusters", Json::Array(clusters)),
            (
                "attestation",
                Json::obj([
                    ("backend", Json::str(self.attestation.backend.clone())),
                    ("model", Json::str(self.attestation.model.clone())),
                    (
                        "prompt_hash",
                        Json::str(self.attestation.prompt_hash.clone()),
                    ),
                    ("timestamp", Json::str(self.attestation.timestamp.clone())),
                    (
                        "determinism",
                        Json::str(
                            "cluster ids/membership/counts are deterministic (byte-identical \
                             to `extract domains`); name/description/responsibilities are \
                             LLM-attested, not byte-stable",
                        ),
                    ),
                ]),
            ),
        ])
    }

    /// Human table: attested header, then one block per cluster.
    pub fn to_text(&self, dir: &str) -> String {
        use std::fmt::Write as _;
        let mut out = String::new();
        let n = self.clusters.len();
        let noun = if n == 1 { "cluster" } else { "clusters" };
        let _ = writeln!(out, "enriched domains for {dir} — {n} {noun}");
        let _ = writeln!(
            out,
            "backend: {}  model: {}",
            self.attestation.backend, self.attestation.model
        );
        let _ = writeln!(
            out,
            "attested: {}  at {}",
            self.attestation.prompt_hash, self.attestation.timestamp
        );
        let _ = writeln!(
            out,
            "note: membership is deterministic; names are LLM-attested, not byte-stable"
        );
        for c in &self.clusters {
            let _ = writeln!(out);
            let _ = writeln!(
                out,
                "{}  [{}]  units {}  files {}  symbols {}  confidence {}",
                c.naming.name,
                c.evidence.domain,
                c.evidence.unit_count,
                c.evidence.file_count,
                c.evidence.symbol_count,
                c.evidence.confidence
            );
            let _ = writeln!(out, "  {}", c.naming.description);
            for r in &c.naming.responsibilities {
                let _ = writeln!(out, "  - {r}");
            }
        }
        out
    }
}

/// Epoch seconds → `YYYY-MM-DDTHH:MM:SSZ` (proleptic Gregorian, UTC). The
/// civil-from-days algorithm, exact integer arithmetic.
fn iso8601_utc(secs: u64) -> String {
    let days = (secs / 86_400) as i64;
    let rem = secs % 86_400;
    let (hh, mm, ss) = (rem / 3600, (rem % 3600) / 60, rem % 60);
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = yoe + era * 400 + i64::from(m <= 2);
    format!("{y:04}-{m:02}-{d:02}T{hh:02}:{mm:02}:{ss:02}Z")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::extract::domains::DomainExtractor;
    use crate::extract::Extractor;
    use crate::ir::ontology::edge;

    // -- fixtures ----------------------------------------------------------

    fn file(g: &mut Graph, path: &str) -> String {
        let name = path.rsplit('/').next().unwrap().to_string();
        let id = format!("file::{path}");
        g.upsert_node(id.clone(), ont::FILE, name, vec![("path", Json::str(path))]);
        id
    }

    fn sym(g: &mut Graph, file_id: &str, kind: &'static str, name: &str) -> String {
        let id = format!("sym::{file_id}::{name}");
        g.upsert_node(id.clone(), kind, name, vec![]);
        g.add_edge(file_id.to_string(), edge::DECLARES, id.clone(), vec![]);
        id
    }

    /// The same eShop-shaped base graph the domains extractor tests use:
    /// three DDD contexts with real dependency structure.
    fn sample_base() -> Graph {
        let mut g = Graph::new();
        let f = file(&mut g, "src/Ordering.API/OrdersApi.cs");
        let create_order = sym(&mut g, &f, ont::FUNCTION, "CreateOrder");
        let ship_order = sym(&mut g, &f, ont::FUNCTION, "ShipOrder");
        sym(&mut g, &f, ont::TYPE, "OrderStatus");
        let f = file(&mut g, "src/Ordering.Domain/Order.cs");
        let order = sym(&mut g, &f, ont::TYPE, "Order");
        let order_item = sym(&mut g, &f, ont::TYPE, "OrderItem");
        sym(&mut g, &f, ont::TYPE, "OrderBuyer");
        g.add_edge(create_order.clone(), edge::USES_TYPE, order.clone(), vec![]);
        g.add_edge(create_order.clone(), edge::USES_TYPE, order_item, vec![]);
        g.add_edge(ship_order, edge::USES_TYPE, order.clone(), vec![]);

        let f = file(&mut g, "src/Catalog.API/CatalogApi.cs");
        let get_brands = sym(&mut g, &f, ont::FUNCTION, "GetCatalogBrands");
        sym(&mut g, &f, ont::TYPE, "CatalogItemDto");
        let f = file(&mut g, "src/Catalog.Infrastructure/CatalogRepository.cs");
        let repo = sym(&mut g, &f, ont::TYPE, "CatalogRepository");
        let brand = sym(&mut g, &f, ont::TYPE, "CatalogBrand");
        sym(&mut g, &f, ont::TYPE, "CatalogType");
        g.add_edge(get_brands.clone(), edge::USES_TYPE, repo.clone(), vec![]);
        g.add_edge(get_brands, edge::USES_TYPE, brand, vec![]);

        let f = file(&mut g, "src/Basket.API/BasketService.cs");
        let bsvc = sym(&mut g, &f, ont::TYPE, "BasketService");
        let bitem = sym(&mut g, &f, ont::TYPE, "BasketItem");
        let f = file(&mut g, "src/Basket.API/BasketRepository.cs");
        let brepo = sym(&mut g, &f, ont::TYPE, "BasketRepository");
        sym(&mut g, &f, ont::FUNCTION, "GetBasketAsync");
        g.add_edge(bsvc.clone(), edge::USES_TYPE, brepo, vec![]);

        g.add_edge(create_order, edge::USES_TYPE, bitem, vec![]);
        g.add_edge(repo, edge::USES_TYPE, order, vec![]);
        g
    }

    fn sample_evidence() -> Vec<ClusterEvidence> {
        let g = sample_base();
        let assignment = assign_domains(&g);
        build_evidence(&g, &assignment)
    }

    // -- evidence pack -----------------------------------------------------

    #[test]
    fn evidence_matches_the_domains_view_byte_for_byte() {
        let g = sample_base();
        let derived = DomainExtractor.extract(&g);
        let evidence = sample_evidence();
        assert!(!evidence.is_empty(), "sample graph must yield clusters");
        // Every cluster's deterministic fields equal the domains-view node
        // props — the byte-identical claim of the enrich schema.
        for ev in &evidence {
            let node = derived
                .nodes()
                .find(|n| n.id == ev.cluster_id)
                .unwrap_or_else(|| panic!("no domains-view node for {}", ev.cluster_id));
            assert_eq!(
                node.props.get("domain"),
                Some(&Json::str(ev.domain.clone()))
            );
            assert_eq!(node.props.get("label"), Some(&Json::str(ev.label.clone())));
            assert_eq!(
                node.props.get("unit_count"),
                Some(&Json::U64(ev.unit_count))
            );
            assert_eq!(
                node.props.get("file_count"),
                Some(&Json::U64(ev.file_count))
            );
            assert_eq!(
                node.props.get("symbol_count"),
                Some(&Json::U64(ev.symbol_count))
            );
            assert_eq!(
                node.props.get("confidence"),
                Some(&Json::str(ev.confidence))
            );
        }
        // And every domains-view domain node has evidence (full coverage).
        let domain_nodes = derived
            .nodes()
            .filter(|n| n.id.starts_with("domain::"))
            .count();
        assert_eq!(evidence.len(), domain_nodes, "one evidence pack per domain");
    }

    #[test]
    fn evidence_carries_units_files_symbols_and_coupling() {
        let evidence = sample_evidence();
        let ordering = evidence
            .iter()
            .find(|e| e.domain == "Ordering")
            .expect("Ordering cluster");
        assert!(ordering
            .units
            .iter()
            .any(|(u, _, _)| u == "Ordering.API" || u == "Ordering.Domain"));
        assert!(ordering
            .top_files
            .iter()
            .any(|p| p == "src/Ordering.Domain/Order.cs"));
        assert!(ordering
            .top_symbols
            .iter()
            .any(|s| s.starts_with("Order (")));
        // Ordering uses a Basket type: coupling neighbors must reflect it
        // (the Basket domain labels as `Basket.API` in this reduced fixture).
        assert!(
            ordering
                .depends_on
                .iter()
                .any(|(d, _)| d.starts_with("Basket")),
            "Ordering must list the Basket domain as a dependency: {:?}",
            ordering.depends_on
        );
        // And the Basket side must mirror it as an inbound neighbor.
        let basket = evidence
            .iter()
            .find(|e| e.domain.starts_with("Basket"))
            .expect("Basket cluster");
        assert!(
            basket.depended_on_by.iter().any(|(d, _)| d == "Ordering"),
            "Basket must list Ordering as an inbound dependency: {:?}",
            basket.depended_on_by
        );
        // Deterministic: two builds emit identical packs.
        let again = sample_evidence();
        assert_eq!(evidence_pack(&evidence), evidence_pack(&again));
        // Largest cluster first.
        for w in evidence.windows(2) {
            assert!(w[0].symbol_count >= w[1].symbol_count);
        }
    }

    #[test]
    fn prompt_ends_with_the_evidence_marker() {
        let pack = evidence_pack(&sample_evidence());
        let prompt = build_prompt(&pack);
        let marker = format!("EVIDENCE:\n{pack}");
        assert!(
            prompt.ends_with(&marker),
            "prompt must end with EVIDENCE: + pack"
        );
        assert!(prompt.contains("ONLY a JSON array"));
        assert!(prompt.contains("membership is FIXED"));
    }

    // -- attestation hash ---------------------------------------------------

    #[test]
    fn fnv1a64_matches_reference_vectors() {
        assert_eq!(fnv1a64(""), 0xcbf2_9ce4_8422_2325);
        assert_eq!(fnv1a64("a"), 0xaf63_dc4c_8601_ec8c);
        assert_eq!(fnv1a64("foobar"), 0x85944171f73967e8);
    }

    #[test]
    fn iso8601_utc_matches_known_instants() {
        assert_eq!(iso8601_utc(0), "1970-01-01T00:00:00Z");
        assert_eq!(iso8601_utc(1_600_000_000), "2020-09-13T12:26:40Z");
        assert_eq!(iso8601_utc(951_827_696), "2000-02-29T12:34:56Z");
    }

    // -- reply parsing -------------------------------------------------------

    const RAW_REPLY: &str = r#"[{"cluster_id":"domain::Ordering","name":"OrderManagement","description":"Handles orders.","responsibilities":["order lifecycle","shipping"]}]"#;

    #[test]
    fn parse_reply_accepts_raw_fenced_and_prose_wrapped_arrays() {
        let expected = ClusterNaming {
            cluster_id: "domain::Ordering".into(),
            name: "OrderManagement".into(),
            description: "Handles orders.".into(),
            responsibilities: vec!["order lifecycle".into(), "shipping".into()],
        };
        for text in [
            RAW_REPLY.to_string(),
            format!("```json\n{RAW_REPLY}\n```"),
            format!("Here you go:\n\n{RAW_REPLY}\n\nHope that helps!"),
        ] {
            let parsed = parse_reply(&text).unwrap_or_else(|e| panic!("{text}: {e}"));
            assert_eq!(parsed, vec![expected.clone()]);
        }
    }

    #[test]
    fn parse_reply_normalizes_cosmetic_names_but_rejects_garbage() {
        let spaced = RAW_REPLY.replace("OrderManagement", "Order Management");
        assert_eq!(parse_reply(&spaced).unwrap()[0].name, "OrderManagement");
        let hyphened = RAW_REPLY.replace("OrderManagement", "Order-Management");
        assert_eq!(parse_reply(&hyphened).unwrap()[0].name, "OrderManagement");
        let garbage = RAW_REPLY.replace("OrderManagement", "Order/Mgmt!");
        assert!(parse_reply(&garbage).is_err(), "punctuation names rejected");
    }

    #[test]
    fn parse_reply_rejects_incomplete_items() {
        for broken in [
            "not json at all",
            "[]", // parses, but validation must then fail on coverage
            r#"[{"cluster_id":"domain::X","name":"N"}]"#, // no description
            r#"[{"cluster_id":"domain::X","name":"N","description":"d","responsibilities":[]}]"#,
            r#"[{"name":"N","description":"d","responsibilities":["r"]}]"#, // no id
        ] {
            let result = parse_reply(broken);
            if broken == "[]" {
                assert_eq!(result.unwrap(), vec![]);
            } else {
                assert!(result.is_err(), "must reject: {broken}");
            }
        }
    }

    #[test]
    fn extract_reply_text_unwraps_the_claude_envelope() {
        let envelope = format!(
            r#"{{"type":"result","subtype":"success","result":"{}","modelUsage":{{"claude-haiku-4-5":{{"inputTokens":1}}}}}}"#,
            RAW_REPLY.replace('"', "\\\"")
        );
        let (text, model) = extract_reply_text(&envelope);
        assert_eq!(text, RAW_REPLY);
        assert_eq!(model.as_deref(), Some("claude-haiku-4-5"));
        // Raw replies pass through untouched, with no model claim.
        let (text, model) = extract_reply_text(RAW_REPLY);
        assert_eq!(text, RAW_REPLY);
        assert_eq!(model, None);
    }

    // -- validation -----------------------------------------------------------

    #[test]
    fn validate_requires_exact_cluster_coverage() {
        let evidence = sample_evidence();
        let naming_for = |id: &str, name: &str| ClusterNaming {
            cluster_id: id.to_string(),
            name: name.to_string(),
            description: "A cluster.".to_string(),
            responsibilities: vec!["something".to_string()],
        };
        // Full coverage validates.
        let full: Vec<ClusterNaming> = evidence
            .iter()
            .enumerate()
            .map(|(i, e)| naming_for(&e.cluster_id, &format!("Name{i}")))
            .collect();
        let named = validate(full.clone(), &evidence).expect("full coverage is valid");
        assert_eq!(named.len(), evidence.len());
        // Missing one cluster fails.
        let mut missing = full.clone();
        missing.pop();
        let err = validate(missing, &evidence).unwrap_err();
        assert!(err.contains("did not name every cluster"), "{err}");
        // Unknown id fails.
        let mut unknown = full.clone();
        unknown.push(naming_for("domain::NotAThing", "Ghost"));
        let err = validate(unknown, &evidence).unwrap_err();
        assert!(err.contains("unknown cluster"), "{err}");
        // Duplicate fails.
        let mut duplicated = full.clone();
        duplicated.push(full[0].clone());
        let err = validate(duplicated, &evidence).unwrap_err();
        assert!(err.contains("twice"), "{err}");
    }

    // -- end-to-end with a mocked backend (no network) --------------------------

    /// Point [`ENV_BACKEND`] at a tiny python script that parses the evidence
    /// pack out of the prompt and names every cluster mechanically — the whole
    /// enrich() loop runs with zero network and zero LLM.
    #[test]
    fn enrich_names_every_cluster_via_a_mocked_backend() {
        let g = sample_base();
        // The committed CLI-test fixture; unit tests run from the crate root.
        std::env::set_var(ENV_BACKEND, "python3 tests/fixtures/mock_enrich.py");
        let result = enrich(&g);
        std::env::remove_var(ENV_BACKEND);
        let enrichment = result.expect("mocked enrichment must succeed");
        assert_eq!(enrichment.clusters.len(), sample_evidence().len());
        for (i, c) in enrichment.clusters.iter().enumerate() {
            assert_eq!(c.naming.cluster_id, c.evidence.cluster_id);
            assert_eq!(c.naming.name, format!("MockCluster{i}"));
            assert!(!c.naming.responsibilities.is_empty());
        }
        assert!(enrichment.attestation.prompt_hash.starts_with("fnv1a64:"));
        assert_eq!(enrichment.attestation.model, "unreported");
        // The JSON document carries schema, clusters, and attestation.
        let doc = enrichment.to_json(".").to_line();
        assert!(doc.contains("\"schema\":\"trailtracker.enrich/v1\""));
        assert!(doc.contains("\"attestation\""));
        assert!(doc.contains("\"prompt_hash\":\"fnv1a64:"));
        // The human table names every cluster.
        let text = enrichment.to_text(".");
        assert!(text.contains("MockCluster0"));
        assert!(text.contains("not byte-stable"));
    }
}
