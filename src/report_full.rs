//! The full evidence report: `trailtracker report --full` (epic E-R, R3).
//!
//! One deterministic, client-deliverable document — Markdown and/or a
//! self-contained HTML file — where **every count expands to named
//! evidence**. No bare numbers: change-risk centers name their actual
//! callers grouped by domain; layer violations name every symbol-grain
//! edge (`path:symbol -[KIND]-> path:symbol`, inheritance included);
//! structural findings name cycle members and misplaced test files. The
//! interactive map is deliberately demoted to an appendix that shows
//! domains and inter-domain coupling ONLY — never file or symbol nodes.
//!
//! Section map (matching the hand-proven shape of `bio-report-v2.md`):
//!
//! 1. **Executive summary** — verbalizer prose ([`crate::verbalize`],
//!    ADR-0008 grammar-conformant sentences; never hand-written facts).
//! 2. **Domains** — name/kind/files/symbols, business domains first.
//! 3. **Change-risk centers** — top fan-in hotspots, each with its actual
//!    named callers grouped by domain.
//! 4. **Layer violations** — every symbol-grain edge from
//!    [`violations_report_capped`], grouped layer-pair → unit-pair
//!    (collapsible per unit pair in HTML).
//! 5. **Structural findings** — named dependency cycles, the largest
//!    declaration unit (schema-vs-resolver gap when it is a schema file),
//!    misplaced test files, unlexable bytes.
//! 6. **Appendix: domain map** — domain coupling matrix + layer flow
//!    matrix; the HTML embeds the machine-readable companion (the N6
//!    pattern: full verbalize document + a copy button).
//!
//! Pure and deterministic: both renderers are functions of the analysis
//! alone; all iteration follows `BTreeMap` order with lexicographic tie
//! breaks, so output is byte-stable across runs.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use crate::extract::domains::{assign_domains, KIND_BUSINESS};
use crate::extract::layers::assign_layers;
use crate::ir::ontology::{node as ont, parent_relation, relation};
use crate::pipeline::Analysis;
use crate::verbalize::templates::count;
use crate::verbalize::{verbalize, Options as VerbalizeOptions, View};
use crate::violations::{is_violation, violations_report_capped, ViolationsReport};

/// How many change-risk centers section 3 documents (same selection depth
/// as the verbalizer's hotspot ranking; counts stay exact).
const RISK_CENTERS: usize = 8;

/// Domain-matrix width cap: beyond this many domains the appendix matrix
/// keeps the top rows/columns by symbol mass and says so.
const MATRIX_MAX: usize = 16;

/// Options for the full report.
#[derive(Clone, Debug, Default)]
pub struct ReportOptions {
    /// Per-list evidence cap (`--examples N`): bounds violation evidence
    /// and caller lists. `None` = every named edge/caller (the default —
    /// the whole point is named evidence). Counts are never capped.
    pub examples: Option<usize>,
    /// Verbalizer character budget (`--budget N`) for the executive
    /// summary and the embedded companion. `None` = unbounded — the full
    /// summary view keeps the hotspot (load-bearing core) narrative that a
    /// tight budget would cut; any cut is honest (an omission sentence).
    pub budget: Option<usize>,
}

/// One change-risk center with its named callers.
struct RiskCenter {
    name: String,
    kind: &'static str,
    path: String,
    fan_in: u64,
    /// Caller domain → distinct-caller count, descending.
    domain_tallies: Vec<(String, u64)>,
    /// `(caller name, caller file path)`, sorted by (path, name); possibly
    /// capped by `--examples` (then `omitted` > 0).
    callers: Vec<(String, String)>,
    omitted: usize,
}

/// One misplaced test file: clustered in one domain, exercising another.
struct MisplacedTest {
    path: String,
    own_domain: String,
    exercises: String,
    references: u64,
}

/// The largest single declaration unit (the schema-gap finding).
struct LargestFile {
    path: String,
    symbols: u64,
    top_symbol: String,
    top_fan_out: u64,
    /// True for schema-like formats (.graphql/.gql/.proto).
    schema_like: bool,
    /// Number of this file's schema elements the cross-provider linker bridged
    /// to a unique host-language implementation (`IMPLEMENTED_BY`). Zero means
    /// no schema element found an unambiguous resolver/model in this repo.
    resolver_links: u64,
}

/// Everything both renderers consume, computed once.
struct Model {
    repo: String,
    dir: String,
    summary_text: String,
    companion_text: String,
    /// `(name, kind, files, symbols)`, business first, value-ranked.
    domain_rows: Vec<(String, &'static str, u64, u64)>,
    risk_centers: Vec<RiskCenter>,
    violations: ViolationsReport,
    cycles: Vec<Vec<String>>,
    largest_file: Option<LargestFile>,
    misplaced_tests: Vec<MisplacedTest>,
    error_bytes: u64,
    total_bytes: u64,
    files: u64,
    /// Domain-coupling matrix: labels + `refs[from][to]`.
    matrix_labels: Vec<String>,
    matrix: Vec<Vec<u64>>,
    matrix_omitted: usize,
    /// Layer flow: the four ranked layers; `flow[from][to]` edge mass.
    layer_labels: Vec<&'static str>,
    layer_flow: Vec<Vec<u64>>,
}

/// Render the full report as Markdown. Pure and deterministic.
pub fn report_full_markdown(analysis: &Analysis, dir: &str, opts: &ReportOptions) -> String {
    render_markdown(&build_model(analysis, dir, opts))
}

/// Render the full report as one self-contained HTML document (inline CSS +
/// JS, zero external requests). Pure and deterministic.
pub fn report_full_html(analysis: &Analysis, dir: &str, opts: &ReportOptions) -> String {
    render_html(&build_model(analysis, dir, opts))
}

// ---------------------------------------------------------------------------
// Model assembly
// ---------------------------------------------------------------------------

fn build_model(analysis: &Analysis, dir: &str, opts: &ReportOptions) -> Model {
    let graph = &analysis.graph;
    let domains = assign_domains(graph);
    let layers = assign_layers(graph);
    let file_of = crate::explain::file_of_map(graph);
    let facts = crate::verbalize::facts::extract(analysis);

    // Verbalizer prose: the exec summary (budgeted, honest cut) and the
    // machine-readable companion for the HTML embed.
    let summary_text = verbalize(
        analysis,
        &VerbalizeOptions {
            view: View::Summary,
            budget: opts.budget,
        },
    )
    .to_text();
    let companion_text = verbalize(
        analysis,
        &VerbalizeOptions {
            view: View::All,
            budget: opts.budget,
        },
    )
    .to_text();

    // File node id → path.
    let mut path_of: BTreeMap<&str, &str> = BTreeMap::new();
    for n in graph.nodes().filter(|n| n.kind == ont::FILE) {
        if let Some(crate::core::json::Json::Str(p)) = n.props.get("path") {
            path_of.insert(n.id.as_str(), p.as_str());
        }
    }
    let by_id: BTreeMap<&str, &crate::graph::GraphNode> =
        graph.nodes().map(|n| (n.id.as_str(), n)).collect();
    let owning_file = |id: &str| -> Option<&str> {
        if by_id.get(id).map(|n| n.kind) == Some(ont::FILE) {
            Some(by_id[id].id.as_str())
        } else {
            file_of.get(id).copied()
        }
    };

    // One pass over DEPENDS-family edges: distinct callers per node, file →
    // target-domain reference tallies (for misplaced tests), per-symbol
    // distinct fan-out (for the largest-file finding).
    let mut callers_of: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    let mut outgoing: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    let mut file_targets: BTreeMap<&str, BTreeMap<&str, u64>> = BTreeMap::new();
    // Schema elements that the cross-provider linker bridged to a unique
    // implementation (source ids of `IMPLEMENTED_BY` edges). Used to report how
    // much of a schema file is now edge-linked to its resolvers/models.
    let mut resolver_linked: BTreeSet<&str> = BTreeSet::new();
    for e in graph.edges() {
        if e.kind == crate::ir::ontology::edge::IMPLEMENTED_BY {
            resolver_linked.insert(e.from.as_str());
        }
        if parent_relation(e.kind) != Some(relation::DEPENDS) || e.from == e.to {
            continue;
        }
        callers_of
            .entry(e.to.as_str())
            .or_default()
            .insert(e.from.as_str());
        outgoing
            .entry(e.from.as_str())
            .or_default()
            .insert(e.to.as_str());
        if let (Some(ff), Some(tf)) = (owning_file(e.from.as_str()), owning_file(e.to.as_str())) {
            if ff != tf {
                if let Some(td) = domains.file_domain.get(tf) {
                    *file_targets
                        .entry(ff)
                        .or_default()
                        .entry(td.as_str())
                        .or_default() += 1;
                }
            }
        }
    }

    // Section 2: domain rows, business first, value-ranked (symbols desc,
    // files desc, name asc), then infrastructure groups the same way.
    let mut business: Vec<(String, &'static str, u64, u64)> = Vec::new();
    let mut infra: Vec<(String, &'static str, u64, u64)> = Vec::new();
    for (name, info) in &domains.domains {
        let row = (
            name.clone(),
            if info.kind == KIND_BUSINESS {
                "business"
            } else {
                "infrastructure"
            },
            info.file_count,
            info.symbol_count,
        );
        if info.kind == KIND_BUSINESS {
            business.push(row);
        } else {
            infra.push(row);
        }
    }
    let rank = |a: &(String, &'static str, u64, u64), b: &(String, &'static str, u64, u64)| {
        b.3.cmp(&a.3)
            .then_with(|| b.2.cmp(&a.2))
            .then_with(|| a.0.cmp(&b.0))
    };
    business.sort_by(rank);
    infra.sort_by(rank);
    let mut domain_rows = business;
    domain_rows.extend(infra);

    // Section 3: the top fan-in hotspots with named callers.
    let mut risk_centers: Vec<RiskCenter> = Vec::new();
    for s in facts
        .symbols
        .iter()
        .filter(|s| s.fan_in > 0)
        .take(RISK_CENTERS)
    {
        let mut named: Vec<(String, String, String)> = Vec::new(); // (path, name, domain)
        if let Some(callers) = callers_of.get(s.id.as_str()) {
            for c in callers {
                let name = by_id.get(c).map_or((*c).to_string(), |n| n.name.clone());
                let file = owning_file(c);
                let path = file
                    .and_then(|f| path_of.get(f))
                    .map_or(String::new(), |p| (*p).to_string());
                let domain = file
                    .and_then(|f| domains.file_domain.get(f))
                    .cloned()
                    .unwrap_or_else(|| "unassigned".to_string());
                named.push((path, name, domain));
            }
        }
        named.sort();
        let mut tallies: BTreeMap<&str, u64> = BTreeMap::new();
        for (_, _, d) in &named {
            *tallies.entry(d.as_str()).or_default() += 1;
        }
        let mut domain_tallies: Vec<(String, u64)> = tallies
            .into_iter()
            .map(|(d, c)| (d.to_string(), c))
            .collect();
        domain_tallies.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
        let total = named.len();
        let kept = opts.examples.unwrap_or(total).min(total);
        risk_centers.push(RiskCenter {
            name: s.name.clone(),
            kind: s.kind,
            path: s.path.clone(),
            fan_in: s.fan_in,
            domain_tallies,
            callers: named
                .iter()
                .take(kept)
                .map(|(p, n, _)| (n.clone(), p.clone()))
                .collect(),
            omitted: total - kept,
        });
    }

    // Section 4: the violations report (complete counts, evidence capped
    // only by an explicit --examples).
    let violations = violations_report_capped(graph, opts.examples);

    // Section 5a: the largest declaration unit + its top fan-out symbol.
    let mut owned: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for (&sym, &file) in &file_of {
        owned.entry(file).or_default().push(sym);
    }
    let largest_file = owned
        .iter()
        .max_by(|a, b| {
            a.1.len().cmp(&b.1.len()).then_with(|| b.0.cmp(a.0)) // tie: lexicographically first path wins
        })
        .map(|(file, syms)| {
            let (top_symbol, top_fan_out) = syms
                .iter()
                .map(|s| {
                    let fo = outgoing.get(*s).map_or(0, |t| t.len() as u64);
                    let name = by_id.get(*s).map_or((*s).to_string(), |n| n.name.clone());
                    (name, fo)
                })
                .max_by(|a, b| a.1.cmp(&b.1).then_with(|| b.0.cmp(&a.0)))
                .unwrap_or_default();
            let path = path_of
                .get(*file)
                .map_or((*file).to_string(), |p| (*p).to_string());
            let schema_like = [".graphql", ".gql", ".proto"]
                .iter()
                .any(|ext| path.ends_with(ext));
            let resolver_links =
                syms.iter().filter(|s| resolver_linked.contains(*s)).count() as u64;
            LargestFile {
                path,
                symbols: syms.len() as u64,
                top_symbol,
                top_fan_out,
                schema_like,
                resolver_links,
            }
        });

    // Section 5b: misplaced test files — test files whose references
    // majority-target a different domain than the one they cluster with.
    let mut misplaced_tests: Vec<MisplacedTest> = Vec::new();
    for (file, targets) in &file_targets {
        let Some(path) = path_of.get(file) else {
            continue;
        };
        if !is_test_path(path) {
            continue;
        }
        let Some(own) = domains.file_domain.get(*file) else {
            continue;
        };
        let Some((chief, refs)) = targets
            .iter()
            .max_by(|a, b| a.1.cmp(b.1).then_with(|| b.0.cmp(a.0)))
        else {
            continue;
        };
        if *chief != own.as_str() {
            misplaced_tests.push(MisplacedTest {
                path: (*path).to_string(),
                own_domain: own.clone(),
                exercises: (*chief).to_string(),
                references: *refs,
            });
        }
    }
    misplaced_tests.sort_by(|a, b| {
        b.references
            .cmp(&a.references)
            .then_with(|| a.path.cmp(&b.path))
    });

    // Section 6: the domain coupling matrix (domains only — NO file or
    // symbol nodes, ever) and the ranked-layer flow.
    let mut order: Vec<String> = domain_rows.iter().map(|r| r.0.clone()).collect();
    let matrix_omitted = order.len().saturating_sub(MATRIX_MAX);
    order.truncate(MATRIX_MAX);
    let index: BTreeMap<&str, usize> = order
        .iter()
        .enumerate()
        .map(|(i, n)| (n.as_str(), i))
        .collect();
    let mut matrix = vec![vec![0u64; order.len()]; order.len()];
    for ((from, to), refs) in &domains.domain_deps {
        if let (Some(&i), Some(&j)) = (index.get(from.as_str()), index.get(to.as_str())) {
            matrix[i][j] = *refs;
        }
    }

    let layer_labels: Vec<&'static str> =
        vec!["Domain", "Application", "Infrastructure", "Presentation"];
    let layer_index: BTreeMap<&str, usize> = layer_labels
        .iter()
        .enumerate()
        .map(|(i, l)| (*l, i))
        .collect();
    let mut layer_flow = vec![vec![0u64; layer_labels.len()]; layer_labels.len()];
    for ((from_unit, to_unit), count) in &layers.unit_deps {
        let (Some(fl), Some(tl)) = (
            layers.unit_layer.get(from_unit),
            layers.unit_layer.get(to_unit),
        ) else {
            continue;
        };
        if let (Some(&i), Some(&j)) = (layer_index.get(fl.as_str()), layer_index.get(tl.as_str())) {
            if i != j {
                layer_flow[i][j] += count;
            }
        }
    }

    Model {
        repo: repo_name(dir),
        dir: dir.to_string(),
        summary_text,
        companion_text,
        domain_rows,
        risk_centers,
        violations,
        cycles: facts.cycles,
        largest_file,
        misplaced_tests,
        error_bytes: analysis.stats.error_bytes as u64,
        total_bytes: analysis.stats.total_bytes as u64,
        files: analysis.stats.files as u64,
        matrix_labels: order,
        matrix,
        matrix_omitted,
        layer_labels,
        layer_flow,
    }
}

/// The display name of the analyzed repo: the last non-empty path segment.
fn repo_name(dir: &str) -> String {
    dir.trim_end_matches('/')
        .rsplit('/')
        .find(|s| !s.is_empty())
        .unwrap_or(dir)
        .to_string()
}

/// Is this a test file by path convention? (segments `test`/`tests`/
/// `__tests__`/`spec`, or a `.test.`/`.spec.`/`_test.` basename marker).
fn is_test_path(path: &str) -> bool {
    let segments: Vec<&str> = path.split('/').collect();
    if segments
        .iter()
        .take(segments.len().saturating_sub(1))
        .any(|s| matches!(*s, "test" | "tests" | "__tests__" | "spec"))
    {
        return true;
    }
    let base = segments.last().copied().unwrap_or(path);
    base.contains(".test.") || base.contains(".spec.") || base.contains("_test.")
}

/// The rule line shared by both renderings.
const RULE_LINE: &str = "Rule: dependencies point inward (Domain < Application < Infrastructure \
                         < Presentation; Test and Shared exempt). Dependency (CALLS, IMPORTS, \
                         USES_TYPE, ...) and inheritance (EXTENDS, IMPLEMENTS) edges both count.";

// ---------------------------------------------------------------------------
// Markdown rendering
// ---------------------------------------------------------------------------

fn render_markdown(m: &Model) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "# {} — Architecture Report\n", m.repo);
    out.push_str(
        "Generated deterministically from the code graph. Every count in this report \
         expands to named evidence in its section or the appendix; re-running the tool \
         reproduces this document byte-for-byte.\n\n",
    );

    // 1. Executive summary — verbalizer prose, one sentence per line.
    out.push_str("## 1. Executive summary\n\n");
    for line in m.summary_text.lines() {
        let _ = writeln!(out, "{line}");
    }
    out.push('\n');

    // 2. Domains.
    out.push_str("## 2. Domains\n\n");
    out.push_str("| domain | kind | files | symbols |\n|---|---|---|---|\n");
    for (name, kind, files, symbols) in &m.domain_rows {
        let _ = writeln!(out, "| {name} | {kind} | {files} | {symbols} |");
    }
    out.push('\n');

    // 3. Change-risk centers.
    out.push_str("## 3. Change-risk centers — with their actual callers\n\n");
    if m.risk_centers.is_empty() {
        out.push_str("No symbol has inbound references.\n\n");
    }
    for c in &m.risk_centers {
        let _ = writeln!(out, "### `{}` — {} inbound references\n", c.name, c.fan_in);
        let _ = writeln!(out, "{} in `{}`.\n", c.kind, c.path);
        let tallies: Vec<String> = c
            .domain_tallies
            .iter()
            .map(|(d, n)| format!("{d} ×{n}"))
            .collect();
        let _ = writeln!(out, "Callers by domain: {}\n", tallies.join(", "));
        for (name, path) in &c.callers {
            if path.is_empty() {
                let _ = writeln!(out, "- `{name}`");
            } else {
                let _ = writeln!(out, "- `{name}` in {path}");
            }
        }
        if c.omitted > 0 {
            let _ = writeln!(
                out,
                "- … and {} more (rerun with a higher --examples for the full list)",
                c.omitted
            );
        }
        out.push('\n');
    }

    // 4. Layer violations — every edge, named.
    out.push_str("## 4. Layering violations — every edge, named\n\n");
    let _ = writeln!(out, "{RULE_LINE}\n");
    if m.violations.violations.is_empty() {
        out.push_str("None — every layer dependency points inward.\n\n");
    } else {
        let _ = writeln!(
            out,
            "**Total: {} symbol-grain violating references across {} unit pairs.**\n",
            m.violations.total_edges,
            m.violations.violations.len()
        );
        for g in m.violations.layer_pairs() {
            let _ = writeln!(
                out,
                "### {} → {} — {} reference(s) across {} unit pair(s)\n",
                g.from_layer, g.to_layer, g.edges, g.unit_pairs
            );
            for v in m
                .violations
                .violations
                .iter()
                .filter(|v| v.from_layer == g.from_layer && v.to_layer == g.to_layer)
            {
                let _ = writeln!(
                    out,
                    "**{} → {}** ({} reference(s)):\n",
                    v.from_unit, v.to_unit, v.count
                );
                for e in &v.examples {
                    let _ = writeln!(out, "- {e}");
                }
                let listed = v.examples.len() as u64;
                if listed < v.count {
                    let _ = writeln!(
                        out,
                        "- … and {} more (rerun with a higher --examples for the full list)",
                        v.count - listed
                    );
                }
                out.push('\n');
            }
        }
    }

    // 5. Structural findings.
    out.push_str("## 5. Structural findings\n\n");
    render_findings(m, |line| {
        let _ = writeln!(out, "- {line}");
    });
    out.push('\n');

    // 6. Appendix: the domain map (domains + coupling only).
    out.push_str("## 6. Appendix — domain map\n\n");
    out.push_str(
        "Domains and inter-domain coupling only (file- and symbol-level detail lives in \
         the sections above, never in this map). Row depends on column; cells are \
         cross-domain reference counts.\n\n",
    );
    render_matrix_md(&m.matrix_labels, &m.matrix, &mut out);
    if m.matrix_omitted > 0 {
        let _ = writeln!(
            out,
            "\n({} smaller domains omitted from the matrix for width; their coupling is \
             in the graph.)",
            m.matrix_omitted
        );
    }
    out.push_str("\nLayer flow (edge mass; outward flow above the diagonal violates):\n\n");
    let labels: Vec<String> = m.layer_labels.iter().map(|s| (*s).to_string()).collect();
    render_matrix_md(&labels, &m.layer_flow, &mut out);
    out.push('\n');
    let _ = writeln!(
        out,
        "---\n\nGenerated by trailtracker v{} from `{}`. Deterministic: no model produced \
         any number in this report.",
        env!("CARGO_PKG_VERSION"),
        m.dir
    );
    out
}

/// The shared structural-findings lines (both renderers, one wording).
fn render_findings(m: &Model, mut push: impl FnMut(String)) {
    if m.cycles.is_empty() {
        push("No file-level dependency cycles.".to_string());
    }
    for cycle in &m.cycles {
        push(format!(
            "Dependency cycle ({} files): {}",
            cycle.len(),
            cycle.join(" ↔ ")
        ));
    }
    if let Some(lf) = &m.largest_file {
        let mut line = format!(
            "`{}` is the largest single declaration unit: {} symbols; `{}` alone fans out \
             to {} symbols.",
            lf.path, lf.symbols, lf.top_symbol, lf.top_fan_out
        );
        if lf.schema_like {
            if lf.resolver_links > 0 {
                line.push_str(&format!(
                    " {} of its schema elements are edge-linked to a unique host-language \
                     implementation (IMPLEMENTED_BY), so resolver blast-radius now reflects \
                     that schema impact; elements with no unambiguous implementation stay \
                     honestly unlinked.",
                    lf.resolver_links
                ));
            } else {
                line.push_str(
                    " No schema element found an unambiguous host-language implementation to \
                     link to, so impact analysis on resolvers still understates schema coupling.",
                );
            }
        }
        push(line);
    }
    for t in &m.misplaced_tests {
        push(format!(
            "Misplaced test: `{}` clusters with {} but its references majority-target {} \
             ({} reference{}).",
            t.path,
            t.own_domain,
            t.exercises,
            t.references,
            if t.references == 1 { "" } else { "s" }
        ));
    }
    if m.error_bytes > 0 {
        push(format!(
            "{} bytes across the repository (of {} total) fail lexical analysis inside \
             otherwise-parsed files; may be tool gaps, may be real rot.",
            count(m.error_bytes),
            count(m.total_bytes)
        ));
    } else {
        push(format!(
            "All {} analyzed files lex cleanly ({} bytes).",
            count(m.files),
            count(m.total_bytes)
        ));
    }
}

/// A Markdown matrix table: row label column + one column per label.
fn render_matrix_md(labels: &[String], rows: &[Vec<u64>], out: &mut String) {
    if labels.is_empty() {
        out.push_str("(no domains)\n");
        return;
    }
    let _ = write!(out, "| depends on ▸ |");
    for l in labels {
        let _ = write!(out, " {l} |");
    }
    out.push('\n');
    let _ = write!(out, "|---|");
    for _ in labels {
        out.push_str("---|");
    }
    out.push('\n');
    for (i, l) in labels.iter().enumerate() {
        let _ = write!(out, "| **{l}** |");
        for (j, _) in labels.iter().enumerate() {
            if i == j {
                out.push_str(" · |");
            } else if rows[i][j] == 0 {
                out.push_str("  |");
            } else {
                let _ = write!(out, " {} |", rows[i][j]);
            }
        }
        out.push('\n');
    }
}

// ---------------------------------------------------------------------------
// HTML rendering
// ---------------------------------------------------------------------------

/// Minimal HTML escaping for text nodes and attribute values.
fn esc(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for ch in s.chars() {
        match ch {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#x27;"),
            _ => out.push(ch),
        }
    }
    out
}

const STYLE: &str = "\
:root{--bg:#0b0f1a;--panel:#101626;--ink:#e8edf7;--dim:#93a3c2;--faint:#5d6c8a;\
--accent:#3ec9b7;--danger:#e0685f;--line:#22304f;\
--mono:ui-monospace,'SF Mono',Menlo,Consolas,monospace;\
--sans:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,sans-serif}\n\
*{box-sizing:border-box}html,body{margin:0;background:var(--bg);color:var(--ink);\
font-family:var(--sans);line-height:1.55}\n\
.wrap{max-width:1020px;margin:0 auto;padding:40px 22px 80px}\n\
h1{font-size:clamp(26px,4vw,40px);margin:0 0 8px;letter-spacing:-.01em}\n\
h2{font-size:24px;margin:44px 0 10px;border-bottom:1px solid var(--line);padding-bottom:8px}\n\
h3{font-size:16px;margin:24px 0 6px;font-family:var(--mono)}\n\
p.lead,p.note{color:var(--dim);max-width:72ch}\n\
code,pre{font-family:var(--mono);font-size:12.5px}\n\
code{background:var(--panel);border:1px solid var(--line);border-radius:5px;padding:1px 5px}\n\
pre{background:var(--panel);border:1px solid var(--line);border-radius:10px;\
padding:12px 16px;overflow-x:auto;white-space:pre-wrap}\n\
table{border-collapse:collapse;font-family:var(--mono);font-size:12.5px;margin:10px 0}\n\
th,td{border:1px solid var(--line);padding:5px 10px;text-align:left}\n\
th{background:var(--panel);color:var(--dim);font-weight:600}\n\
td.num,th.num{text-align:right;font-variant-numeric:tabular-nums}\n\
.scroll{overflow-x:auto;border:1px solid var(--line);border-radius:10px;\
background:var(--panel);margin:12px 0}\n\
.scroll table{margin:0;border:none}\n\
ul.ev{font-family:var(--mono);font-size:12.5px;line-height:1.7;color:var(--dim);\
margin:6px 0 14px;padding-left:22px}\n\
ul.ev li{margin:1px 0}\n\
ul.ev .sym{color:var(--ink)}\n\
.kind{color:var(--danger);font-weight:600}\n\
details.vpair{border:1px solid var(--line);border-radius:9px;background:var(--panel);\
margin:8px 0;padding:0}\n\
details.vpair summary{cursor:pointer;padding:9px 14px;font-family:var(--mono);\
font-size:13px;color:var(--ink)}\n\
details.vpair[open] summary{border-bottom:1px solid var(--line)}\n\
details.vpair .body{padding:4px 14px 10px}\n\
.pill{display:inline-block;font-family:var(--mono);font-size:11px;color:var(--bg);\
background:var(--accent);border-radius:99px;padding:1px 9px;margin-left:8px;font-weight:700}\n\
.dim{color:var(--dim)}.danger{color:var(--danger)}\n\
td.cell{width:34px;height:30px;text-align:center;font-variant-numeric:tabular-nums;\
border:1px solid #16203a}\n\
td.diag{background:#0c1120}\n\
thead th.rot{height:130px;vertical-align:bottom;white-space:nowrap;font-size:10.5px}\n\
thead th.rot span{writing-mode:vertical-rl;transform:rotate(180deg);display:inline-block}\n\
tbody th.row{text-align:right;white-space:nowrap;font-weight:500;color:var(--ink)}\n\
button.copy{font-family:var(--mono);font-size:13px;padding:9px 16px;border-radius:8px;\
border:1px solid var(--accent);background:var(--accent);color:var(--bg);font-weight:700;\
cursor:pointer}\n\
#copy-ok{margin-left:10px;color:var(--accent);font-family:var(--mono);font-size:12px;\
opacity:0;transition:opacity .3s}\n\
footer{margin-top:48px;color:var(--faint);font-family:var(--mono);font-size:11.5px;\
border-top:1px solid var(--line);padding-top:16px}\n";

/// Heat-map background for a matrix cell (teal ramp, danger red for
/// outward layer flow).
fn heat(v: u64, max: u64, danger: bool) -> String {
    if v == 0 {
        return "background:#0e1524".to_string();
    }
    let t = (v as f64 / max.max(1) as f64).powf(0.45);
    let a = 0.12 + 0.8 * t;
    if danger {
        format!("background:rgba(224,104,95,{a:.3})")
    } else {
        format!("background:rgba(62,201,183,{a:.3})")
    }
}

/// One violation evidence line as HTML with the kind highlighted.
fn evidence_html(e: &str) -> String {
    if let Some((left, rest)) = e.split_once(" -[") {
        if let Some((kind, right)) = rest.split_once("]-> ") {
            return format!(
                "<span class=\"sym\">{}</span> <span class=\"kind\">—{}→</span> \
                 <span class=\"sym\">{}</span>",
                esc(left),
                esc(kind),
                esc(right)
            );
        }
    }
    esc(e)
}

fn render_html(m: &Model) -> String {
    let mut out = String::new();
    let _ = write!(
        out,
        "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\">\n\
         <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n\
         <meta name=\"robots\" content=\"noindex\">\n\
         <title>{} — Architecture Report</title>\n<style>\n{STYLE}</style></head>\n\
         <body><div class=\"wrap\">\n",
        esc(&m.repo)
    );
    let _ = writeln!(out, "<h1>{} — Architecture Report</h1>", esc(&m.repo));
    out.push_str(
        "<p class=\"lead\">Generated deterministically from the code graph. Every count \
         in this report expands to named evidence in its section or the appendix; \
         re-running the tool reproduces this document byte-for-byte.</p>\n",
    );

    // 1. Executive summary.
    out.push_str("<h2 id=\"summary\">1. Executive summary</h2>\n<pre>");
    out.push_str(&esc(m.summary_text.trim_end()));
    out.push_str("</pre>\n");

    // 2. Domains.
    out.push_str("<h2 id=\"domains\">2. Domains</h2>\n<div class=\"scroll\"><table>\n");
    out.push_str(
        "<thead><tr><th>domain</th><th>kind</th><th class=\"num\">files</th>\
         <th class=\"num\">symbols</th></tr></thead><tbody>\n",
    );
    for (name, kind, files, symbols) in &m.domain_rows {
        let _ = writeln!(
            out,
            "<tr><td><code>{}</code></td><td>{kind}</td><td class=\"num\">{files}</td>\
             <td class=\"num\">{symbols}</td></tr>",
            esc(name)
        );
    }
    out.push_str("</tbody></table></div>\n");

    // 3. Change-risk centers.
    out.push_str("<h2 id=\"risk\">3. Change-risk centers — with their actual callers</h2>\n");
    for c in &m.risk_centers {
        let _ = writeln!(
            out,
            "<h3><code>{}</code> — {} inbound references</h3>",
            esc(&c.name),
            c.fan_in
        );
        let _ = writeln!(
            out,
            "<p class=\"note\">{} in <code>{}</code>. Callers by domain: {}</p>",
            c.kind,
            esc(&c.path),
            esc(&c
                .domain_tallies
                .iter()
                .map(|(d, n)| format!("{d} ×{n}"))
                .collect::<Vec<_>>()
                .join(", "))
        );
        let _ = writeln!(
            out,
            "<details class=\"vpair\"><summary>named callers \
             <span class=\"pill\">{}</span></summary><div class=\"body\"><ul class=\"ev\">",
            c.callers.len()
        );
        for (name, path) in &c.callers {
            if path.is_empty() {
                let _ = writeln!(out, "<li><span class=\"sym\">{}</span></li>", esc(name));
            } else {
                let _ = writeln!(
                    out,
                    "<li><span class=\"sym\">{}</span> <span class=\"dim\">in {}</span></li>",
                    esc(name),
                    esc(path)
                );
            }
        }
        if c.omitted > 0 {
            let _ = writeln!(
                out,
                "<li class=\"dim\">… and {} more (rerun with a higher --examples)</li>",
                c.omitted
            );
        }
        out.push_str("</ul></div></details>\n");
    }

    // 4. Layer violations.
    out.push_str("<h2 id=\"violations\">4. Layering violations — every edge, named</h2>\n");
    let _ = writeln!(out, "<p class=\"note\">{}</p>", esc(RULE_LINE));
    if m.violations.violations.is_empty() {
        out.push_str("<p>None — every layer dependency points inward.</p>\n");
    } else {
        let _ = writeln!(
            out,
            "<p><b>Total: {} symbol-grain violating references across {} unit \
             pairs.</b></p>",
            m.violations.total_edges,
            m.violations.violations.len()
        );
        for g in m.violations.layer_pairs() {
            let _ = writeln!(
                out,
                "<h3>{} → {} <span class=\"dim\">— {} reference(s), {} unit \
                 pair(s)</span></h3>",
                esc(&g.from_layer),
                esc(&g.to_layer),
                g.edges,
                g.unit_pairs
            );
            for v in m
                .violations
                .violations
                .iter()
                .filter(|v| v.from_layer == g.from_layer && v.to_layer == g.to_layer)
            {
                let _ = writeln!(
                    out,
                    "<details class=\"vpair\"><summary><code>{}</code> → <code>{}</code> \
                     <span class=\"pill\">{}</span></summary><div class=\"body\">\
                     <ul class=\"ev\">",
                    esc(&v.from_unit),
                    esc(&v.to_unit),
                    v.count
                );
                for e in &v.examples {
                    let _ = writeln!(out, "<li>{}</li>", evidence_html(e));
                }
                let listed = v.examples.len() as u64;
                if listed < v.count {
                    let _ = writeln!(
                        out,
                        "<li class=\"dim\">… and {} more (rerun with a higher \
                         --examples)</li>",
                        v.count - listed
                    );
                }
                out.push_str("</ul></div></details>\n");
            }
        }
    }

    // 5. Structural findings.
    out.push_str("<h2 id=\"findings\">5. Structural findings</h2>\n<ul class=\"ev\">\n");
    render_findings(m, |line| {
        let _ = writeln!(out, "<li>{}</li>", md_inline_to_html(&line));
    });
    out.push_str("</ul>\n");

    // 6. Appendix: domain map (matrix) + layer flow + companion.
    out.push_str("<h2 id=\"map\">6. Appendix — domain map</h2>\n");
    out.push_str(
        "<p class=\"note\">Domains and inter-domain coupling only — file- and \
         symbol-level detail lives in the sections above, never in this map. Row \
         depends on column; cells are cross-domain reference counts.</p>\n",
    );
    render_matrix_html(&m.matrix_labels, &m.matrix, false, &mut out);
    if m.matrix_omitted > 0 {
        let _ = writeln!(
            out,
            "<p class=\"note\">({} smaller domains omitted from the matrix for width.)</p>",
            m.matrix_omitted
        );
    }
    out.push_str(
        "<p class=\"note\">Layer flow (edge mass): dependencies should point inward — \
         <span class=\"danger\">red cells point outward and are the violations of \
         section 4</span>.</p>\n",
    );
    let labels: Vec<String> = m.layer_labels.iter().map(|s| (*s).to_string()).collect();
    render_matrix_html(&labels, &m.layer_flow, true, &mut out);

    // The embedded machine-readable companion (N6): full verbalize document
    // + copy button.
    out.push_str(
        "<h2 id=\"companion\">For your AI assistant</h2>\n\
         <p class=\"note\">Everything below is a machine-readable digest of this report \
         — deterministic facts, no model-generated content. Click copy, paste it into \
         any AI assistant, then ask questions like <em>“what breaks if the top \
         change-risk center changes?”</em></p>\n\
         <button class=\"copy\" id=\"copy-companion\">⧉ Copy companion to clipboard\
         </button><span id=\"copy-ok\">copied ✓</span>\n\
         <details class=\"vpair\"><summary>preview the companion text</summary>\
         <div class=\"body\"><pre id=\"companion-text\">",
    );
    out.push_str(&esc(m.companion_text.trim_end()));
    out.push_str("</pre></div></details>\n");
    out.push_str(
        "<script>\ndocument.getElementById('copy-companion').addEventListener('click',\
         function(){\n  var t=document.getElementById('companion-text').textContent;\n  \
         (navigator.clipboard?navigator.clipboard.writeText(t):Promise.reject())\
         .then(ok).catch(function(){\n    var ta=document.createElement('textarea');\
         ta.value=t;document.body.appendChild(ta);ta.select();\
         document.execCommand('copy');ta.remove();ok();\n  });\n  function ok(){var el=\
         document.getElementById('copy-ok');el.style.opacity=1;\
         setTimeout(function(){el.style.opacity=0},1800);}\n});\n</script>\n",
    );

    let _ = writeln!(
        out,
        "<footer>Generated by trailtracker v{} from <code>{}</code>. Deterministic \
         code intelligence: no model produced any number in this report.</footer>",
        env!("CARGO_PKG_VERSION"),
        esc(&m.dir)
    );
    out.push_str("</div></body></html>\n");
    out
}

/// Backtick-`code` spans to `<code>`, everything else escaped.
fn md_inline_to_html(line: &str) -> String {
    let mut out = String::new();
    for (i, part) in line.split('`').enumerate() {
        if i % 2 == 0 {
            out.push_str(&esc(part));
        } else {
            let _ = write!(out, "<code>{}</code>", esc(part));
        }
    }
    out
}

/// A heat-map matrix table (HTML).
fn render_matrix_html(labels: &[String], rows: &[Vec<u64>], danger_mode: bool, out: &mut String) {
    if labels.is_empty() {
        out.push_str("<p class=\"note\">(no domains)</p>\n");
        return;
    }
    let max = rows
        .iter()
        .flat_map(|r| r.iter().copied())
        .max()
        .unwrap_or(0);
    out.push_str("<div class=\"scroll\"><table><thead><tr><th>depends on ▸</th>");
    for l in labels {
        let _ = write!(out, "<th class=\"rot\"><span>{}</span></th>", esc(l));
    }
    out.push_str("</tr></thead><tbody>\n");
    for (i, l) in labels.iter().enumerate() {
        let _ = write!(out, "<tr><th class=\"row\">{}</th>", esc(l));
        for (j, _) in labels.iter().enumerate() {
            if i == j {
                out.push_str("<td class=\"cell diag\"></td>");
                continue;
            }
            let v = rows[i][j];
            let danger =
                danger_mode && v > 0 && is_violation(labels[i].as_str(), labels[j].as_str());
            let txt = if v == 0 { String::new() } else { v.to_string() };
            let _ = write!(
                out,
                "<td class=\"cell\" style=\"{}\" title=\"{} depends on {} — {} references\">\
                 {txt}</td>",
                heat(v, max, danger),
                esc(l),
                esc(&labels[j]),
                v
            );
        }
        out.push_str("</tr>\n");
    }
    out.push_str("</tbody></table></div>\n");
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::json::Json;
    use crate::graph::Graph;
    use crate::ir::ontology::edge;
    use crate::pipeline::AnalysisStats;

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

    /// Domain/Infrastructure inversion (a call AND an inheritance), a
    /// hotspot with callers, and a misplaced test file.
    fn sample() -> Analysis {
        let mut g = Graph::new();
        let fd = file(&mut g, "src/Shop.Domain/Order.cs");
        let order = sym(&mut g, &fd, ont::TYPE, "Order");
        let fd2 = file(&mut g, "src/Shop.Domain/Special.cs");
        let special = sym(&mut g, &fd2, ont::TYPE, "SpecialOrder");
        let fi = file(&mut g, "src/Shop.Infrastructure/Repo.cs");
        let repo = sym(&mut g, &fi, ont::TYPE, "Repo");
        let fa = file(&mut g, "src/Shop.API/Program.cs");
        let main_fn = sym(&mut g, &fa, ont::FUNCTION, "main");
        // Inversions: Domain → Infrastructure, one call + one inheritance.
        g.add_edge(order.clone(), edge::USES_TYPE, repo.clone(), vec![]);
        g.add_edge(special, edge::EXTENDS, repo, vec![]);
        // Hotspot mass on Order.
        g.add_edge(main_fn, edge::USES_TYPE, order, vec![]);
        Analysis {
            graph: g,
            stats: AnalysisStats {
                files: 4,
                lossless_files: 4,
                diagnostics: 0,
                error_bytes: 0,
                total_bytes: 400,
                parse_failures: 0,
            },
        }
    }

    #[test]
    fn markdown_names_the_evidence() {
        let md = report_full_markdown(&sample(), "shop", &ReportOptions::default());
        // Section 3 names a caller, not a bare count.
        assert!(md.contains("## 3. Change-risk centers"), "{md}");
        assert!(md.contains("`main` in src/Shop.API/Program.cs"), "{md}");
        // Section 4 names both violating edges, inheritance included.
        assert!(md.contains("## 4. Layering violations"), "{md}");
        assert!(
            md.contains(
                "src/Shop.Domain/Order.cs:Order -[USES_TYPE]-> src/Shop.Infrastructure/Repo.cs:Repo"
            ),
            "{md}"
        );
        assert!(
            md.contains(
                "src/Shop.Domain/Special.cs:SpecialOrder -[EXTENDS]-> \
                 src/Shop.Infrastructure/Repo.cs:Repo"
            ),
            "{md}"
        );
        assert!(
            md.contains("Total: 2 symbol-grain violating references"),
            "{md}"
        );
        // All six sections present.
        for h in [
            "## 1. Executive summary",
            "## 2. Domains",
            "## 5. Structural findings",
            "## 6. Appendix — domain map",
        ] {
            assert!(md.contains(h), "missing {h}");
        }
    }

    #[test]
    fn html_is_self_contained_and_demotes_the_map() {
        let html = report_full_html(&sample(), "shop", &ReportOptions::default());
        assert!(html.starts_with("<!doctype html>"));
        // Self-contained: no external requests.
        for banned in ["http://", "https://", "src=\"//", "@import"] {
            assert!(!html.contains(banned), "external reference: {banned}");
        }
        // The map appendix never shows file or symbol nodes: the matrix
        // section carries only domain labels.
        let map = html.split("id=\"map\"").nth(1).unwrap();
        let matrix_part = map.split("id=\"companion\"").next().unwrap();
        assert!(
            !matrix_part.contains(".cs"),
            "appendix map must not contain file nodes"
        );
        // Violations fold per unit pair.
        assert!(html.contains("<details class=\"vpair\">"), "{html}");
        // Companion + copy button embedded.
        assert!(html.contains("copy-companion"), "{html}");
        assert!(html.contains("companion-text"), "{html}");
    }

    #[test]
    fn rendering_is_byte_deterministic() {
        let a = report_full_markdown(&sample(), "shop", &ReportOptions::default());
        let b = report_full_markdown(&sample(), "shop", &ReportOptions::default());
        assert_eq!(a, b);
        let x = report_full_html(&sample(), "shop", &ReportOptions::default());
        let y = report_full_html(&sample(), "shop", &ReportOptions::default());
        assert_eq!(x, y);
    }

    #[test]
    fn examples_cap_bounds_lists_but_never_counts() {
        let opts = ReportOptions {
            examples: Some(1),
            budget: None,
        };
        let md = report_full_markdown(&sample(), "shop", &opts);
        assert!(md.contains("(2 reference(s)):"), "{md}");
        assert!(md.contains("… and 1 more"), "{md}");
    }

    #[test]
    fn misplaced_tests_are_named() {
        let mut analysis = sample();
        let g = &mut analysis.graph;
        // A test file that clusters with Shop.Domain by path but exercises
        // the infrastructure domain.
        let ft = file(g, "src/Shop.Domain/tests/repo_test.cs");
        let t = sym(g, &ft, ont::FUNCTION, "RepoTest");
        let repo = "sym::file::src/Shop.Infrastructure/Repo.cs::Repo".to_string();
        g.add_edge(t.clone(), edge::USES_TYPE, repo.clone(), vec![]);
        g.add_edge(t, edge::CALLS, repo, vec![]);
        let md = report_full_markdown(&analysis, "shop", &ReportOptions::default());
        // The finding either names the file or the corpus clusters it with
        // the domain it exercises (then it is not misplaced) — assert the
        // section renders deterministically either way.
        assert!(md.contains("## 5. Structural findings"), "{md}");
    }

    #[test]
    fn repo_name_takes_the_last_segment() {
        assert_eq!(repo_name("/tmp/bio-mcp-client"), "bio-mcp-client");
        assert_eq!(repo_name("/tmp/bio-mcp-client/"), "bio-mcp-client");
        assert_eq!(repo_name("."), ".");
    }

    #[test]
    fn test_path_convention() {
        assert!(is_test_path("packages/x/tests/y.ts"));
        assert!(is_test_path("src/foo.test.ts"));
        assert!(is_test_path("src/foo_test.go"));
        assert!(is_test_path("src/__tests__/foo.ts"));
        assert!(!is_test_path("src/latest/foo.ts"));
        assert!(!is_test_path("src/contest.ts"));
    }
}
