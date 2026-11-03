//! Continuous architecture verification (ADR-0005): `trailtracker
//! arch-verify` / `trailtracker arch-init`.
//!
//! The ontology views *recover* architecture; this module turns that report
//! into an enforceable contract. Humans declare the INTENDED architecture in
//! a `.trailtracker-arch.json` spec — domains as repo-relative `pathPrefixes`
//! (the exact shape the eShop ground truth proved out) plus a small rule
//! vocabulary — and [`verify`] checks the ACTUAL code against it:
//!
//! - **`domain-existence`** — the declared domain must be recovered
//!   non-empty (architecture-erosion detection).
//! - **`domain-containment`** — files under the domain's prefixes must still
//!   cluster with that domain (file-migration drift, via [`assign_domains`]).
//! - **`forbidden-dependency`** — no DEPENDS-family edge may point from a
//!   file of domain `from` to a file of domain `to`.
//! - **`forbidden-layer-dependency`** — the layer view's direction semantics,
//!   spec-driven and gating: no dependency mass may flow `from`-layer →
//!   `to`-layer (via [`assign_layers`]).
//!
//! [`verify`] is a pure function of (spec, analyzed graph): deterministic
//! findings with bounded evidence, no I/O. [`init_spec`] bootstraps a spec
//! from the currently recovered architecture (dominant-prefix set-cover per
//! business cluster, observed inter-domain dependencies as an advisory
//! baseline) so a team adopts the gate in one command. Spec parsing fails
//! CLOSED: an unknown rule type, an undeclared domain, an unknown layer, or
//! malformed JSON is an error — the verifier never half-evaluates intent.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::json::{read, Json};
use crate::extract::domains::{assign_domains, DomainAssignment, KIND_BUSINESS};
use crate::extract::layers::{assign_layers, LayerAssignment, LAYER_NAMES};
use crate::graph::Graph;
use crate::ir::ontology::{node as ont, parent_relation, relation};

/// Default spec filename, resolved against the analyzed directory.
pub const SPEC_FILE: &str = ".trailtracker-arch.json";
/// The spec's `format` discriminator (optional in the file, but when present
/// it must match — fail closed on a spec written for a future grammar).
pub const SPEC_FORMAT: &str = "trailtracker.arch-spec/v1";
/// Schema id of the `--json` verification report.
pub const REPORT_FORMAT: &str = "trailtracker.arch-verify/v1";

/// Evidence examples are bounded per finding; counts are always complete.
const MAX_EXAMPLES: usize = 5;
/// `arch-init` prefix derivation: a candidate prefix is *owned* by a cluster
/// when ≥ 4/5 of the analyzable files it matches are cluster members.
const OWN_NUM: u64 = 4;
const OWN_DEN: u64 = 5;
/// `arch-init` prefix derivation: stop once ≥ 4/5 of members are covered.
const COVER_NUM: u64 = 4;
const COVER_DEN: u64 = 5;
/// `arch-init`: readability cap on prefixes per domain.
const MAX_PREFIXES: usize = 20;

/// Finding/rule severity. `error` gates (exit 1); `warn` reports without
/// gating — the adoption ramp for rules a team is not ready to enforce.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Severity {
    Warn,
    Error,
}

impl Severity {
    pub fn as_str(self) -> &'static str {
        match self {
            Severity::Warn => "warn",
            Severity::Error => "error",
        }
    }
}

/// One declared domain: a name plus the repo-relative path prefixes that
/// define membership. Longest matching prefix wins; ties go to declaration
/// order; unmatched files are out of scope.
#[derive(Clone, Debug)]
pub struct SpecDomain {
    pub name: String,
    pub path_prefixes: Vec<String>,
}

/// The rule payload — the v1 vocabulary (ADR-0005).
#[derive(Clone, Debug)]
pub enum RuleKind {
    DomainExistence { domain: String },
    DomainContainment { domain: String },
    ForbiddenDependency { from: String, to: String },
    ForbiddenLayerDependency { from: String, to: String },
}

impl RuleKind {
    /// The stable `type` string used in the spec and in findings.
    pub fn type_name(&self) -> &'static str {
        match self {
            RuleKind::DomainExistence { .. } => "domain-existence",
            RuleKind::DomainContainment { .. } => "domain-containment",
            RuleKind::ForbiddenDependency { .. } => "forbidden-dependency",
            RuleKind::ForbiddenLayerDependency { .. } => "forbidden-layer-dependency",
        }
    }

    /// The derived rule id used when the spec does not name one.
    fn default_id(&self) -> String {
        match self {
            RuleKind::DomainExistence { domain } | RuleKind::DomainContainment { domain } => {
                format!("{}:{domain}", self.type_name())
            }
            RuleKind::ForbiddenDependency { from, to }
            | RuleKind::ForbiddenLayerDependency { from, to } => {
                format!("{}:{from}->{to}", self.type_name())
            }
        }
    }
}

/// One spec rule: id (unique), severity, payload.
#[derive(Clone, Debug)]
pub struct Rule {
    pub id: String,
    pub severity: Severity,
    pub kind: RuleKind,
}

/// The parsed, validated architecture spec.
#[derive(Clone, Debug)]
pub struct ArchSpec {
    pub domains: Vec<SpecDomain>,
    pub rules: Vec<Rule>,
}

/// One verification finding: which rule fired, how hard, and the evidence.
#[derive(Clone, Debug)]
pub struct ArchFinding {
    pub rule_id: String,
    pub rule_type: &'static str,
    pub severity: Severity,
    pub message: String,
    /// Complete count of matching files/edges (never truncated).
    pub count: u64,
    /// Bounded examples (≤ [`MAX_EXAMPLES`]), deterministic order.
    pub examples: Vec<String>,
}

impl ArchFinding {
    pub fn to_json(&self) -> Json {
        Json::obj([
            ("id", Json::str(&self.rule_id)),
            ("type", Json::str(self.rule_type)),
            ("severity", Json::str(self.severity.as_str())),
            ("message", Json::str(&self.message)),
            ("count", Json::U64(self.count)),
            (
                "examples",
                Json::Array(self.examples.iter().map(Json::str).collect()),
            ),
        ])
    }
}

// ---------------------------------------------------------------------------
// Spec parsing (fail closed)
// ---------------------------------------------------------------------------

/// Look up a key in a parsed JSON object (first occurrence wins).
fn get<'v>(pairs: &'v [(String, read::V)], key: &str) -> Option<&'v read::V> {
    pairs.iter().find(|(k, _)| k == key).map(|(_, v)| v)
}

/// A required non-empty string field, with a path-shaped error context.
fn req_str(pairs: &[(String, read::V)], key: &str, ctx: &str) -> Result<String, String> {
    match get(pairs, key) {
        Some(read::V::Str(s)) if !s.trim().is_empty() => Ok(s.trim().to_string()),
        Some(_) => Err(format!("{ctx}: '{key}' must be a non-empty string")),
        None => Err(format!("{ctx}: missing required field '{key}'")),
    }
}

/// Parse and validate a spec document. Every error message names the exact
/// problem; the CLI maps errors to exit 2 with a fix line.
pub fn parse_spec(text: &str) -> Result<ArchSpec, String> {
    let read::V::Obj(top) = read::parse(text).map_err(|e| format!("not valid JSON: {e}"))? else {
        return Err("the spec must be a JSON object".to_string());
    };

    if let Some(v) = get(&top, "format") {
        match v {
            read::V::Str(s) if s == SPEC_FORMAT => {}
            read::V::Str(s) => {
                return Err(format!(
                    "unsupported spec format '{s}' (this build understands {SPEC_FORMAT})"
                ))
            }
            _ => return Err("'format' must be a string".to_string()),
        }
    }

    // Domains.
    let Some(read::V::Arr(domain_items)) = get(&top, "domains") else {
        return Err("missing required field 'domains' (an array of \
                    {name, pathPrefixes[]} objects)"
            .to_string());
    };
    if domain_items.is_empty() {
        return Err("'domains' must declare at least one domain".to_string());
    }
    let mut domains: Vec<SpecDomain> = Vec::new();
    let mut seen_names: BTreeSet<String> = BTreeSet::new();
    for (i, item) in domain_items.iter().enumerate() {
        let read::V::Obj(pairs) = item else {
            return Err(format!("domains[{i}]: not an object"));
        };
        let name = req_str(pairs, "name", &format!("domains[{i}]"))?;
        if !seen_names.insert(name.clone()) {
            return Err(format!("domains[{i}]: duplicate domain name '{name}'"));
        }
        let Some(read::V::Arr(prefix_items)) = get(pairs, "pathPrefixes") else {
            return Err(format!(
                "domains[{i}] ('{name}'): missing required field 'pathPrefixes' \
                 (an array of repo-relative path prefixes)"
            ));
        };
        if prefix_items.is_empty() {
            return Err(format!(
                "domains[{i}] ('{name}'): 'pathPrefixes' must not be empty"
            ));
        }
        let mut path_prefixes = Vec::new();
        for (j, p) in prefix_items.iter().enumerate() {
            match p {
                read::V::Str(s) if !s.trim().is_empty() => path_prefixes.push(s.trim().to_string()),
                _ => {
                    return Err(format!(
                        "domains[{i}] ('{name}'): pathPrefixes[{j}] must be a \
                         non-empty string"
                    ))
                }
            }
        }
        domains.push(SpecDomain {
            name,
            path_prefixes,
        });
    }

    // Rules (optional; a spec may declare structure only).
    let mut rules: Vec<Rule> = Vec::new();
    match get(&top, "rules") {
        None => {}
        Some(read::V::Arr(rule_items)) => {
            let domain_names: BTreeSet<&str> = domains.iter().map(|d| d.name.as_str()).collect();
            let mut seen_ids: BTreeSet<String> = BTreeSet::new();
            for (i, item) in rule_items.iter().enumerate() {
                let read::V::Obj(pairs) = item else {
                    return Err(format!("rules[{i}]: not an object"));
                };
                let ctx = format!("rules[{i}]");
                let rtype = req_str(pairs, "type", &ctx)?;
                let domain_field = |key: &str| -> Result<String, String> {
                    let v = req_str(pairs, key, &ctx)?;
                    if domain_names.contains(v.as_str()) {
                        Ok(v)
                    } else {
                        Err(format!(
                            "{ctx}: '{key}' names undeclared domain '{v}' (declared: {})",
                            domains
                                .iter()
                                .map(|d| d.name.as_str())
                                .collect::<Vec<_>>()
                                .join(", ")
                        ))
                    }
                };
                let layer_field = |key: &str| -> Result<String, String> {
                    let v = req_str(pairs, key, &ctx)?;
                    if LAYER_NAMES.contains(&v.as_str()) {
                        Ok(v)
                    } else {
                        Err(format!(
                            "{ctx}: '{key}' names unknown layer '{v}' (layers: {})",
                            LAYER_NAMES.join(", ")
                        ))
                    }
                };
                let kind = match rtype.as_str() {
                    "domain-existence" => RuleKind::DomainExistence {
                        domain: domain_field("domain")?,
                    },
                    "domain-containment" => RuleKind::DomainContainment {
                        domain: domain_field("domain")?,
                    },
                    "forbidden-dependency" => RuleKind::ForbiddenDependency {
                        from: domain_field("from")?,
                        to: domain_field("to")?,
                    },
                    "forbidden-layer-dependency" => RuleKind::ForbiddenLayerDependency {
                        from: layer_field("from")?,
                        to: layer_field("to")?,
                    },
                    other => {
                        return Err(format!(
                            "{ctx}: unknown rule type '{other}' (known: domain-existence, \
                             domain-containment, forbidden-dependency, \
                             forbidden-layer-dependency)"
                        ))
                    }
                };
                let severity = match get(pairs, "severity") {
                    None => Severity::Error,
                    Some(read::V::Str(s)) if s == "error" => Severity::Error,
                    Some(read::V::Str(s)) if s == "warn" => Severity::Warn,
                    Some(read::V::Str(s)) => {
                        return Err(format!(
                            "{ctx}: unknown severity '{s}' (use 'error' or 'warn')"
                        ))
                    }
                    Some(_) => return Err(format!("{ctx}: 'severity' must be a string")),
                };
                let id = match get(pairs, "id") {
                    None => kind.default_id(),
                    Some(read::V::Str(s)) if !s.trim().is_empty() => s.trim().to_string(),
                    Some(_) => return Err(format!("{ctx}: 'id' must be a non-empty string")),
                };
                if !seen_ids.insert(id.clone()) {
                    return Err(format!("{ctx}: duplicate rule id '{id}'"));
                }
                rules.push(Rule { id, severity, kind });
            }
        }
        Some(_) => return Err("'rules' must be an array".to_string()),
    }

    Ok(ArchSpec { domains, rules })
}

// ---------------------------------------------------------------------------
// Verification (pure)
// ---------------------------------------------------------------------------

/// The declared domain (index into `spec.domains`) owning `path`: longest
/// matching prefix wins, ties go to declaration order, no match is `None`.
fn declared_of(spec: &ArchSpec, path: &str) -> Option<usize> {
    let mut best: Option<(usize, usize)> = None; // (prefix_len, domain_idx)
    for (idx, d) in spec.domains.iter().enumerate() {
        for p in &d.path_prefixes {
            if path.starts_with(p.as_str()) {
                let better = match best {
                    None => true,
                    Some((len, _)) => p.len() > len,
                };
                if better {
                    best = Some((p.len(), idx));
                }
            }
        }
    }
    best.map(|(_, idx)| idx)
}

/// Bounded containment walk to the owning File node — the same walk the
/// domains/layers extractors use (kept structurally identical on purpose).
fn resolve_file<'g>(
    kind_of: &BTreeMap<&'g str, &'static str>,
    parent: &BTreeMap<&'g str, &'g str>,
    mut id: &'g str,
) -> Option<&'g str> {
    for _ in 0..64 {
        if kind_of.get(id).copied() == Some(ont::FILE) {
            return Some(id);
        }
        id = parent.get(id)?;
    }
    None
}

/// Cross-declared-domain dependency mass: `(from_idx, to_idx)` → (total edge
/// count, bounded `fromPath -[KIND]-> toPath` examples). Every DEPENDS-family
/// edge whose endpoints resolve to Files in *different* declared domains
/// contributes.
fn declared_deps(spec: &ArchSpec, graph: &Graph) -> BTreeMap<(usize, usize), (u64, Vec<String>)> {
    let kind_of: BTreeMap<&str, &'static str> =
        graph.nodes().map(|n| (n.id.as_str(), n.kind)).collect();
    let mut parent: BTreeMap<&str, &str> = BTreeMap::new();
    for e in graph.edges() {
        if parent_relation(e.kind) != Some(relation::CONTAINMENT) {
            continue;
        }
        let from_is_file = kind_of.get(e.from.as_str()).copied() == Some(ont::FILE);
        match parent.get(e.to.as_str()) {
            None => {
                parent.insert(e.to.as_str(), e.from.as_str());
            }
            Some(existing) => {
                let existing_is_file = kind_of.get(existing).copied() == Some(ont::FILE);
                if from_is_file && !existing_is_file {
                    parent.insert(e.to.as_str(), e.from.as_str());
                }
            }
        }
    }
    // File id → (path, declared domain index).
    let mut file_decl: BTreeMap<&str, (&str, usize)> = BTreeMap::new();
    for n in graph.nodes().filter(|n| n.kind == ont::FILE) {
        if let Some(Json::Str(path)) = n.props.get("path") {
            if let Some(idx) = declared_of(spec, path) {
                file_decl.insert(n.id.as_str(), (path.as_str(), idx));
            }
        }
    }
    let mut deps: BTreeMap<(usize, usize), (u64, Vec<String>)> = BTreeMap::new();
    for e in graph.edges() {
        if parent_relation(e.kind) != Some(relation::DEPENDS) {
            continue;
        }
        let (Some(from_file), Some(to_file)) = (
            resolve_file(&kind_of, &parent, e.from.as_str()),
            resolve_file(&kind_of, &parent, e.to.as_str()),
        ) else {
            continue;
        };
        let (Some(&(from_path, from_idx)), Some(&(to_path, to_idx))) =
            (file_decl.get(from_file), file_decl.get(to_file))
        else {
            continue;
        };
        if from_idx == to_idx {
            continue;
        }
        let entry = deps.entry((from_idx, to_idx)).or_default();
        entry.0 += 1;
        if entry.1.len() < MAX_EXAMPLES {
            let example = format!("{from_path} -[{}]-> {to_path}", e.kind);
            if !entry.1.contains(&example) {
                entry.1.push(example);
            }
        }
    }
    deps
}

/// Recovered business cluster → the declared domain that *anchors* it (the
/// declared domain owning a strict majority of the cluster's prefix-matched
/// files), or no entry when no majority exists.
fn cluster_anchors(spec: &ArchSpec, assignment: &DomainAssignment) -> BTreeMap<String, usize> {
    let mut per_cluster: BTreeMap<&str, BTreeMap<usize, u64>> = BTreeMap::new();
    for (file, recovered) in &assignment.file_domain {
        let is_business = assignment
            .domains
            .get(recovered)
            .is_some_and(|d| d.kind == KIND_BUSINESS);
        if !is_business {
            continue;
        }
        let Some(path) = assignment.file_path.get(file) else {
            continue;
        };
        if let Some(idx) = declared_of(spec, path) {
            *per_cluster
                .entry(recovered.as_str())
                .or_default()
                .entry(idx)
                .or_default() += 1;
        }
    }
    let mut anchors = BTreeMap::new();
    for (cluster, counts) in per_cluster {
        let total: u64 = counts.values().sum();
        // BTreeMap iteration: first max wins deterministically.
        let (&best_idx, &best_count) = counts
            .iter()
            .max_by(|a, b| a.1.cmp(b.1).then(b.0.cmp(a.0)))
            .expect("counts is non-empty");
        if best_count * 2 > total {
            anchors.insert(cluster.to_string(), best_idx);
        }
    }
    anchors
}

/// Verify the spec against an analyzed graph. Pure and deterministic: same
/// spec + same graph ⇒ the same findings in the same order (spec rule order).
pub fn verify(spec: &ArchSpec, graph: &Graph) -> Vec<ArchFinding> {
    let assignment = assign_domains(graph);
    let layers = assign_layers(graph);
    verify_with(spec, graph, &assignment, &layers)
}

/// [`verify`] with the assignments precomputed (shared by `arch-init`'s
/// self-check and the tests).
fn verify_with(
    spec: &ArchSpec,
    graph: &Graph,
    assignment: &DomainAssignment,
    layers: &LayerAssignment,
) -> Vec<ArchFinding> {
    // Files per declared domain (analyzable files only — the clustered set).
    let mut files_per_decl: BTreeMap<usize, u64> = BTreeMap::new();
    for path in assignment.file_path.values() {
        if let Some(idx) = declared_of(spec, path) {
            *files_per_decl.entry(idx).or_default() += 1;
        }
    }

    // Containment drift: declared domain idx → (count, examples).
    let anchors = cluster_anchors(spec, assignment);
    let mut drift: BTreeMap<usize, (u64, Vec<String>)> = BTreeMap::new();
    for (file, recovered) in &assignment.file_domain {
        let Some(path) = assignment.file_path.get(file) else {
            continue;
        };
        let Some(decl_idx) = declared_of(spec, path) else {
            continue;
        };
        let Some(&anchor_idx) = anchors.get(recovered) else {
            continue; // unanchored cluster (e.g. Shared/Platform): not drift
        };
        if anchor_idx == decl_idx {
            continue;
        }
        let entry = drift.entry(decl_idx).or_default();
        entry.0 += 1;
        if entry.1.len() < MAX_EXAMPLES {
            entry.1.push(format!(
                "{path} — declared '{}', clusters with '{recovered}' (anchored to '{}')",
                spec.domains[decl_idx].name, spec.domains[anchor_idx].name
            ));
        }
    }

    // Cross-declared-domain dependency mass.
    let deps = declared_deps(spec, graph);

    // Layer → layer dependency mass, aggregated from the recovered unit
    // placement (same LayerAssignment the layers view emits).
    let mut layer_deps: BTreeMap<(String, String), (u64, Vec<String>)> = BTreeMap::new();
    for ((from_unit, to_unit), mass) in &layers.unit_deps {
        let (Some(from_layer), Some(to_layer)) = (
            layers.unit_layer.get(from_unit),
            layers.unit_layer.get(to_unit),
        ) else {
            continue;
        };
        let entry = layer_deps
            .entry((from_layer.clone(), to_layer.clone()))
            .or_default();
        entry.0 += mass;
        if entry.1.len() < MAX_EXAMPLES {
            entry
                .1
                .push(format!("{from_unit} -> {to_unit} ({mass} edges)"));
        }
    }

    let idx_of = |name: &str| -> usize {
        spec.domains
            .iter()
            .position(|d| d.name == name)
            .expect("rule domains are validated at parse time")
    };

    let mut findings = Vec::new();
    for rule in &spec.rules {
        let finding = match &rule.kind {
            RuleKind::DomainExistence { domain } => {
                let idx = idx_of(domain);
                let count = files_per_decl.get(&idx).copied().unwrap_or(0);
                (count == 0).then(|| ArchFinding {
                    rule_id: rule.id.clone(),
                    rule_type: rule.kind.type_name(),
                    severity: rule.severity,
                    message: format!(
                        "declared domain '{domain}' was not recovered: no analyzable \
                         file matches its path prefixes"
                    ),
                    count: 0,
                    examples: spec.domains[idx]
                        .path_prefixes
                        .iter()
                        .take(MAX_EXAMPLES)
                        .map(|p| format!("prefix: {p}"))
                        .collect(),
                })
            }
            RuleKind::DomainContainment { domain } => {
                let idx = idx_of(domain);
                drift.get(&idx).map(|(count, examples)| ArchFinding {
                    rule_id: rule.id.clone(),
                    rule_type: rule.kind.type_name(),
                    severity: rule.severity,
                    message: format!(
                        "{count} file(s) declared in '{domain}' cluster with a \
                         different declared domain"
                    ),
                    count: *count,
                    examples: examples.clone(),
                })
            }
            RuleKind::ForbiddenDependency { from, to } => {
                let key = (idx_of(from), idx_of(to));
                deps.get(&key).map(|(count, examples)| ArchFinding {
                    rule_id: rule.id.clone(),
                    rule_type: rule.kind.type_name(),
                    severity: rule.severity,
                    message: format!(
                        "forbidden dependency: '{from}' depends on '{to}' \
                         ({count} edge(s))"
                    ),
                    count: *count,
                    examples: examples.clone(),
                })
            }
            RuleKind::ForbiddenLayerDependency { from, to } => {
                let key = (from.clone(), to.clone());
                layer_deps.get(&key).map(|(count, examples)| ArchFinding {
                    rule_id: rule.id.clone(),
                    rule_type: rule.kind.type_name(),
                    severity: rule.severity,
                    message: format!(
                        "forbidden layer dependency: layer '{from}' depends on \
                         layer '{to}' ({count} cross-unit edge(s))"
                    ),
                    count: *count,
                    examples: examples.clone(),
                })
            }
        };
        if let Some(f) = finding {
            findings.push(f);
        }
    }
    findings
}

/// Does any finding gate (severity `error`)? The CLI's exit-1 predicate.
pub fn gates(findings: &[ArchFinding]) -> bool {
    findings.iter().any(|f| f.severity == Severity::Error)
}

// ---------------------------------------------------------------------------
// arch-init: bootstrap a spec from the recovered architecture
// ---------------------------------------------------------------------------

/// Derive dominant path prefixes for one cluster: greedy set-cover over
/// directory prefixes (deepest-common first by coverage), each candidate
/// *owned* by the cluster (≥ [`OWN_NUM`]/[`OWN_DEN`] of the analyzable files
/// it matches are members), until ≥ [`COVER_NUM`]/[`COVER_DEN`] of members
/// are covered or candidates run out. Falls back to exact member paths when
/// no directory prefix is owned. Mirrors `benchmarks/gt_bootstrap.py`.
fn derive_prefixes(members: &BTreeSet<&str>, universe: &[&str]) -> Vec<String> {
    // Candidate directory prefixes from member paths ("a/b/c.cs" → "a/", "a/b/").
    let mut candidates: BTreeSet<String> = BTreeSet::new();
    for path in members {
        let mut pos = 0;
        for (i, ch) in path.char_indices() {
            if ch == '/' {
                pos = i + 1;
                candidates.insert(path[..pos].to_string());
            }
        }
        let _ = pos;
    }
    // Ownership filter.
    let mut owned: Vec<(String, Vec<&str>)> = Vec::new(); // (prefix, matched members)
    for cand in &candidates {
        let matches_universe = universe.iter().filter(|p| p.starts_with(cand)).count() as u64;
        let matched: Vec<&str> = members
            .iter()
            .filter(|p| p.starts_with(cand))
            .copied()
            .collect();
        if (matched.len() as u64) * OWN_DEN >= matches_universe * OWN_NUM {
            owned.push((cand.clone(), matched));
        }
    }
    // Greedy cover: most new members first; ties → shorter prefix, then lex.
    let mut chosen: Vec<String> = Vec::new();
    let mut covered: BTreeSet<&str> = BTreeSet::new();
    while chosen.len() < MAX_PREFIXES
        && (covered.len() as u64) * COVER_DEN < (members.len() as u64) * COVER_NUM
    {
        let mut best: Option<(usize, &String, &Vec<&str>)> = None;
        for (prefix, matched) in &owned {
            if chosen.contains(prefix) {
                continue;
            }
            let gain = matched.iter().filter(|p| !covered.contains(**p)).count();
            if gain == 0 {
                continue;
            }
            let better = match best {
                None => true,
                Some((bg, bp, _)) => {
                    gain > bg
                        || (gain == bg
                            && (prefix.len() < bp.len()
                                || (prefix.len() == bp.len() && prefix < bp)))
                }
            };
            if better {
                best = Some((gain, prefix, matched));
            }
        }
        let Some((_, prefix, matched)) = best else {
            break;
        };
        chosen.push(prefix.clone());
        covered.extend(matched.iter().copied());
    }
    if chosen.is_empty() {
        // Last resort: exact file paths (a tiny or fully-interleaved cluster).
        return members
            .iter()
            .take(MAX_PREFIXES)
            .map(|p| p.to_string())
            .collect();
    }
    chosen
}

/// JSON-escape a string via the deterministic writer.
fn esc(s: &str) -> String {
    Json::str(s).to_line()
}

/// Bootstrap a spec from the CURRENT recovered architecture. Returns the
/// pretty-printed spec document (human-editable, parseable by [`parse_spec`]).
///
/// - Recovered business clusters become declared domains with derived
///   `pathPrefixes` (dominant-prefix set-cover).
/// - Every domain gets a `domain-existence` rule (severity `error` — it holds
///   by construction today) and a `domain-containment` rule (severity `warn`
///   — the adoption ramp; promote to `error` once the prefixes are
///   hand-tuned).
/// - The current inter-domain dependencies land in an advisory
///   `observedDependencies` baseline (ignored by verify) plus a `notes`
///   scaffold showing how to promote one into a `forbidden-dependency` rule.
pub fn init_spec(graph: &Graph) -> String {
    let assignment = assign_domains(graph);
    let universe: Vec<&str> = assignment.file_path.values().map(String::as_str).collect();

    // Member paths per recovered business cluster, in cluster-name order.
    let mut members: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    for (file, recovered) in &assignment.file_domain {
        let is_business = assignment
            .domains
            .get(recovered)
            .is_some_and(|d| d.kind == KIND_BUSINESS);
        if !is_business {
            continue;
        }
        if let Some(path) = assignment.file_path.get(file) {
            members
                .entry(recovered.as_str())
                .or_default()
                .insert(path.as_str());
        }
    }

    let mut domains: Vec<SpecDomain> = Vec::new();
    for (name, files) in &members {
        let prefixes = derive_prefixes(files, &universe);
        if prefixes.is_empty() {
            continue;
        }
        domains.push(SpecDomain {
            name: name.to_string(),
            path_prefixes: prefixes,
        });
    }

    let rules: Vec<Rule> = domains
        .iter()
        .flat_map(|d| {
            [
                Rule {
                    id: String::new(),
                    severity: Severity::Error,
                    kind: RuleKind::DomainExistence {
                        domain: d.name.clone(),
                    },
                },
                Rule {
                    id: String::new(),
                    severity: Severity::Warn,
                    kind: RuleKind::DomainContainment {
                        domain: d.name.clone(),
                    },
                },
            ]
        })
        .collect();

    // Observed inter-domain dependencies (advisory baseline).
    let spec = ArchSpec { domains, rules };
    let deps = declared_deps(&spec, graph);

    // Render (field order chosen for human reading; parse ignores order).
    let mut out = String::new();
    out.push_str("{\n");
    out.push_str(&format!("  \"format\": {},\n", esc(SPEC_FORMAT)));
    out.push_str(&format!(
        "  \"notes\": {},\n",
        esc(
            "Bootstrapped by `trailtracker arch-init` from the RECOVERED architecture. \
             Edit to declare INTENT: tighten pathPrefixes, promote domain-containment \
             rules from 'warn' to 'error', and forbid unwanted couplings by copying an \
             observedDependencies entry into rules as {\"type\": \"forbidden-dependency\", \
             \"from\": ..., \"to\": ...}. observedDependencies is advisory and ignored \
             by arch-verify."
        )
    ));
    out.push_str("  \"domains\": [\n");
    for (i, d) in spec.domains.iter().enumerate() {
        let prefixes: Vec<String> = d.path_prefixes.iter().map(|p| esc(p)).collect();
        out.push_str(&format!(
            "    {{ \"name\": {}, \"pathPrefixes\": [{}] }}{}\n",
            esc(&d.name),
            prefixes.join(", "),
            if i + 1 < spec.domains.len() { "," } else { "" }
        ));
    }
    out.push_str("  ],\n");
    out.push_str("  \"rules\": [\n");
    for (i, r) in spec.rules.iter().enumerate() {
        let (key, value) = match &r.kind {
            RuleKind::DomainExistence { domain } | RuleKind::DomainContainment { domain } => {
                ("domain", domain.clone())
            }
            _ => unreachable!("init emits only existence/containment rules"),
        };
        out.push_str(&format!(
            "    {{ \"type\": {}, \"{key}\": {}, \"severity\": {} }}{}\n",
            esc(r.kind.type_name()),
            esc(&value),
            esc(r.severity.as_str()),
            if i + 1 < spec.rules.len() { "," } else { "" }
        ));
    }
    out.push_str("  ],\n");
    out.push_str("  \"observedDependencies\": [\n");
    let dep_lines: Vec<String> = deps
        .iter()
        .map(|((from, to), (count, _))| {
            format!(
                "    {{ \"from\": {}, \"to\": {}, \"count\": {count} }}",
                esc(&spec.domains[*from].name),
                esc(&spec.domains[*to].name)
            )
        })
        .collect();
    out.push_str(&dep_lines.join(",\n"));
    if !dep_lines.is_empty() {
        out.push('\n');
    }
    out.push_str("  ]\n");
    out.push_str("}\n");
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::ontology::edge;

    // -- fixtures ------------------------------------------------------------

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

    /// Two clean contexts (ordering, basket) with an ordering→basket call.
    fn sample_graph() -> Graph {
        let mut g = Graph::new();
        let fo = file(&mut g, "src/ordering/orders.rs");
        let place = sym(&mut g, &fo, ont::FUNCTION, "place_order");
        sym(&mut g, &fo, ont::TYPE, "Order");
        let fo2 = file(&mut g, "src/ordering/status.rs");
        let track = sym(&mut g, &fo2, ont::FUNCTION, "track_order");
        sym(&mut g, &fo2, ont::TYPE, "OrderStatus");
        let fb = file(&mut g, "src/basket/basket.rs");
        let checkout = sym(&mut g, &fb, ont::FUNCTION, "checkout");
        sym(&mut g, &fb, ont::TYPE, "Basket");
        let fb2 = file(&mut g, "src/basket/items.rs");
        let add = sym(&mut g, &fb2, ont::FUNCTION, "add_item");
        sym(&mut g, &fb2, ont::TYPE, "BasketItem");
        // Intra-domain cohesion.
        g.add_edge(place.clone(), edge::CALLS, track, vec![]);
        g.add_edge(checkout.clone(), edge::CALLS, add, vec![]);
        // The cross-domain edge a forbidden-dependency rule can bite on.
        g.add_edge(place, edge::CALLS, checkout, vec![]);
        g
    }

    fn spec_text(rules: &str) -> String {
        format!(
            r#"{{
  "format": "trailtracker.arch-spec/v1",
  "domains": [
    {{ "name": "Ordering", "pathPrefixes": ["src/ordering/"] }},
    {{ "name": "Basket", "pathPrefixes": ["src/basket/"] }}
  ],
  "rules": [{rules}]
}}"#
        )
    }

    // -- parsing (fail closed) ------------------------------------------------

    #[test]
    fn parse_rejects_garbage_and_bad_shapes() {
        assert!(parse_spec("not json").is_err());
        assert!(parse_spec("[]").is_err());
        assert!(parse_spec("{}").unwrap_err().contains("domains"));
        assert!(parse_spec(r#"{"domains": []}"#)
            .unwrap_err()
            .contains("at least one"));
        // Wrong format string fails closed.
        let err =
            parse_spec(r#"{"format": "v99", "domains": [{"name": "A", "pathPrefixes": ["a/"]}]}"#)
                .unwrap_err();
        assert!(err.contains("unsupported spec format"), "{err}");
        // Duplicate domain names.
        let err = parse_spec(
            r#"{"domains": [{"name": "A", "pathPrefixes": ["a/"]}, {"name": "A", "pathPrefixes": ["b/"]}]}"#,
        )
        .unwrap_err();
        assert!(err.contains("duplicate domain name"), "{err}");
    }

    #[test]
    fn parse_rejects_unknown_rule_types_and_undeclared_names() {
        let err = parse_spec(&spec_text(
            r#"{ "type": "no-such-rule", "domain": "Ordering" }"#,
        ))
        .unwrap_err();
        assert!(err.contains("unknown rule type"), "{err}");
        let err = parse_spec(&spec_text(
            r#"{ "type": "forbidden-dependency", "from": "Ordering", "to": "Ghost" }"#,
        ))
        .unwrap_err();
        assert!(err.contains("undeclared domain 'Ghost'"), "{err}");
        let err = parse_spec(&spec_text(
            r#"{ "type": "forbidden-layer-dependency", "from": "Domain", "to": "Kernel" }"#,
        ))
        .unwrap_err();
        assert!(err.contains("unknown layer 'Kernel'"), "{err}");
        let err = parse_spec(&spec_text(
            r#"{ "type": "domain-existence", "domain": "Ordering", "severity": "fatal" }"#,
        ))
        .unwrap_err();
        assert!(err.contains("unknown severity"), "{err}");
    }

    #[test]
    fn parse_accepts_a_full_spec_and_derives_ids() {
        let spec = parse_spec(&spec_text(
            r#"{ "type": "forbidden-dependency", "from": "Ordering", "to": "Basket" },
               { "type": "domain-existence", "domain": "Ordering", "severity": "warn" }"#,
        ))
        .expect("valid spec");
        assert_eq!(spec.domains.len(), 2);
        assert_eq!(spec.rules.len(), 2);
        assert_eq!(spec.rules[0].id, "forbidden-dependency:Ordering->Basket");
        assert_eq!(spec.rules[0].severity, Severity::Error);
        assert_eq!(spec.rules[1].severity, Severity::Warn);
    }

    // -- rule evaluation --------------------------------------------------

    #[test]
    fn forbidden_dependency_bites_on_the_actual_edge() {
        let g = sample_graph();
        let spec = parse_spec(&spec_text(
            r#"{ "type": "forbidden-dependency", "from": "Ordering", "to": "Basket" },
               { "type": "forbidden-dependency", "from": "Basket", "to": "Ordering" }"#,
        ))
        .unwrap();
        let findings = verify(&spec, &g);
        // Ordering→Basket fires (the CALLS edge); Basket→Ordering stays clean.
        assert_eq!(findings.len(), 1, "{findings:?}");
        let f = &findings[0];
        assert_eq!(f.rule_id, "forbidden-dependency:Ordering->Basket");
        assert_eq!(f.count, 1);
        assert!(
            f.examples[0].contains("src/ordering/orders.rs")
                && f.examples[0].contains("src/basket/basket.rs"),
            "{:?}",
            f.examples
        );
        assert!(gates(&findings));
    }

    #[test]
    fn domain_existence_bites_on_a_dead_domain() {
        let g = sample_graph();
        let text = r#"{
  "domains": [
    { "name": "Ordering", "pathPrefixes": ["src/ordering/"] },
    { "name": "Shipping", "pathPrefixes": ["src/shipping/"] }
  ],
  "rules": [
    { "type": "domain-existence", "domain": "Ordering" },
    { "type": "domain-existence", "domain": "Shipping" }
  ]
}"#;
        let spec = parse_spec(text).unwrap();
        let findings = verify(&spec, &g);
        assert_eq!(findings.len(), 1, "{findings:?}");
        assert_eq!(findings[0].rule_id, "domain-existence:Shipping");
        assert!(findings[0].message.contains("not recovered"));
    }

    #[test]
    fn forbidden_layer_dependency_bites_on_an_inversion() {
        // Two conventionally named units: the Domain layer calling into the
        // Infrastructure layer — the classic inversion, spec-driven.
        let mut g = Graph::new();
        let fd = file(&mut g, "src/Shop.Domain/order.cs");
        let compute = sym(&mut g, &fd, ont::FUNCTION, "compute_total");
        let fi = file(&mut g, "src/Shop.Infrastructure/repo.cs");
        let persist = sym(&mut g, &fi, ont::FUNCTION, "persist_row");
        g.add_edge(compute, edge::CALLS, persist, vec![]);
        let text = r#"{
  "domains": [ { "name": "Shop", "pathPrefixes": ["src/"] } ],
  "rules": [
    { "type": "forbidden-layer-dependency", "from": "Domain", "to": "Infrastructure" },
    { "type": "forbidden-layer-dependency", "from": "Infrastructure", "to": "Domain" }
  ]
}"#;
        let spec = parse_spec(text).unwrap();
        let findings = verify(&spec, &g);
        assert_eq!(findings.len(), 1, "{findings:?}");
        let f = &findings[0];
        assert_eq!(
            f.rule_id,
            "forbidden-layer-dependency:Domain->Infrastructure"
        );
        assert_eq!(f.count, 1);
        assert!(
            f.examples[0].contains("Shop.Domain") && f.examples[0].contains("Shop.Infrastructure"),
            "{:?}",
            f.examples
        );
    }

    #[test]
    fn domain_containment_bites_when_a_unit_clusters_elsewhere() {
        // Clustering is unit-grained: a whole unit migrates when its only
        // coupling points into another domain. `ordering` is one glue file
        // whose every edge targets basket symbols — the unit clusters WITH
        // basket, while the spec still declares src/ordering/ as Ordering.
        // (`shipping` is an independent cluster so the merge is not global.)
        let mut g = Graph::new();
        let fd = file(&mut g, "src/ordering/basket_glue.rs");
        let glue = sym(&mut g, &fd, ont::FUNCTION, "sync_basket");
        let fb = file(&mut g, "src/basket/basket.rs");
        let checkout = sym(&mut g, &fb, ont::FUNCTION, "checkout");
        let fb2 = file(&mut g, "src/basket/items.rs");
        let add = sym(&mut g, &fb2, ont::FUNCTION, "add_item");
        g.add_edge(glue.clone(), edge::CALLS, checkout.clone(), vec![]);
        g.add_edge(glue, edge::CALLS, add.clone(), vec![]);
        g.add_edge(checkout, edge::CALLS, add, vec![]);
        // Enough independent mass that ordering+basket stays under the
        // anti-collapse cap (a merged community must be < half the repo).
        let fs1 = file(&mut g, "src/shipping/dispatch.rs");
        let dispatch = sym(&mut g, &fs1, ont::FUNCTION, "dispatch_parcel");
        sym(&mut g, &fs1, ont::TYPE, "Parcel");
        sym(&mut g, &fs1, ont::TYPE, "Route");
        let fs2 = file(&mut g, "src/shipping/labels.rs");
        let label = sym(&mut g, &fs2, ont::FUNCTION, "print_label");
        sym(&mut g, &fs2, ont::TYPE, "Label");
        let fs3 = file(&mut g, "src/shipping/carriers.rs");
        let carrier = sym(&mut g, &fs3, ont::FUNCTION, "pick_carrier");
        sym(&mut g, &fs3, ont::TYPE, "Carrier");
        g.add_edge(dispatch.clone(), edge::CALLS, label, vec![]);
        g.add_edge(dispatch, edge::CALLS, carrier, vec![]);

        let assignment = assign_domains(&g);
        let drifted = assignment
            .file_domain
            .get("file::src/ordering/basket_glue.rs")
            .expect("glue file is clustered");
        let basket_cluster = assignment
            .file_domain
            .get("file::src/basket/basket.rs")
            .expect("basket file is clustered");
        // Precondition for the scenario: the ordering unit really migrated.
        assert_eq!(
            drifted, basket_cluster,
            "fixture must cluster the ordering unit with basket: {:?}",
            assignment.file_domain
        );

        let text = r#"{
  "domains": [
    { "name": "Ordering", "pathPrefixes": ["src/ordering/"] },
    { "name": "Basket", "pathPrefixes": ["src/basket/"] },
    { "name": "Shipping", "pathPrefixes": ["src/shipping/"] }
  ],
  "rules": [
    { "type": "domain-containment", "domain": "Ordering" },
    { "type": "domain-containment", "domain": "Shipping" }
  ]
}"#;
        let spec = parse_spec(text).unwrap();
        let findings = verify(&spec, &g);
        assert_eq!(findings.len(), 1, "{findings:?}");
        let f = &findings[0];
        assert_eq!(f.rule_id, "domain-containment:Ordering");
        assert_eq!(f.count, 1);
        assert!(
            f.examples
                .iter()
                .any(|e| e.contains("src/ordering/basket_glue.rs") && e.contains("Basket")),
            "{:?}",
            f.examples
        );
    }

    #[test]
    fn clean_truthful_spec_passes() {
        let g = sample_graph();
        let spec = parse_spec(&spec_text(
            r#"{ "type": "domain-existence", "domain": "Ordering" },
               { "type": "domain-existence", "domain": "Basket" },
               { "type": "domain-containment", "domain": "Ordering" },
               { "type": "domain-containment", "domain": "Basket" },
               { "type": "forbidden-dependency", "from": "Basket", "to": "Ordering" }"#,
        ))
        .unwrap();
        let findings = verify(&spec, &g);
        assert!(findings.is_empty(), "{findings:?}");
    }

    #[test]
    fn warn_severity_reports_without_gating() {
        let g = sample_graph();
        let spec = parse_spec(&spec_text(
            r#"{ "type": "forbidden-dependency", "from": "Ordering", "to": "Basket",
                 "severity": "warn" }"#,
        ))
        .unwrap();
        let findings = verify(&spec, &g);
        assert_eq!(findings.len(), 1);
        assert!(!gates(&findings));
    }

    #[test]
    fn verify_is_deterministic() {
        let g = sample_graph();
        let spec = parse_spec(&spec_text(
            r#"{ "type": "forbidden-dependency", "from": "Ordering", "to": "Basket" }"#,
        ))
        .unwrap();
        let a = format!("{:?}", verify(&spec, &g));
        let b = format!("{:?}", verify(&spec, &g));
        assert_eq!(a, b);
    }

    // -- arch-init ----------------------------------------------------------

    #[test]
    fn init_spec_is_deterministic_parseable_and_verifies_without_gating() {
        let g = sample_graph();
        let a = init_spec(&g);
        let b = init_spec(&g);
        assert_eq!(a, b, "init output must be byte-deterministic");
        let spec = parse_spec(&a).expect("init output must parse");
        assert!(!spec.domains.is_empty());
        assert!(!spec.rules.is_empty());
        // Adopt-in-one-command: a freshly bootstrapped spec never gates.
        let findings = verify(&spec, &g);
        assert!(!gates(&findings), "{findings:?}");
    }
}
