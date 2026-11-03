//! The document assembler behind `trailtracker verbalize` (V1, epic E-V).
//!
//! A verbalized document is a glossary prelude (dense, value-ranked handle
//! definitions — ADR-0008 R3/R5) followed by body sentences in domain-major
//! order, rendered exclusively through the versioned template registry.
//! Assembly guarantees, in order:
//!
//! 1. **Grammar conformance** — every sentence comes from
//!    [`crate::verbalize::templates`]; the self-conformance gate runs
//!    [`Document::check`] over real pipeline output in CI.
//! 2. **Deterministic ordering** — facts arrive pre-ranked from
//!    [`crate::verbalize::facts`]; sections group sentences by handle in
//!    assignment order (all `D1` facts before `D2` facts).
//! 3. **Dedup** — an exact duplicate sentence never appears twice (first
//!    occurrence wins), so retrieval never ranks the same fact twice.
//! 4. **Budget honesty** — a `--budget` cut keeps the longest valid prefix
//!    and appends `The budget omits N sentences of M sentences.` — the
//!    nav-pack rule: truncation is never silent.

use std::collections::BTreeSet;

use crate::core::json::Json;
use crate::explain::ExplainError;
use crate::pipeline::Analysis;
use crate::verbalize::facts::{self, Facts};
use crate::verbalize::glossary::Glossary;
use crate::verbalize::grammar::{self, Handle, Violation};
use crate::verbalize::templates as t;

/// Schema id of the `--json` envelope.
pub const REPORT_FORMAT: &str = "trailtracker.verbalize/v1";

/// How many hotspot symbols the `summary` view describes (the full set
/// appears in `hotspots`/`all`).
const SUMMARY_HOTSPOTS: usize = 5;

/// How many dependency sentences each domain contributes in `summary`.
const SUMMARY_DEPS_PER_DOMAIN: usize = 2;

/// How many entry points are named individually (each names the exact total).
const ENTRIES_LISTED: usize = 5;

/// How many flows are described (deepest first).
const FLOWS_LISTED: usize = 3;

/// The selectable document shapes.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum View {
    /// Overview, coverage, domains with top dependencies, groups, the top
    /// hotspots, entry points, flows, and the violation/cycle totals.
    #[default]
    Summary,
    /// Every hotspot symbol in full: identity, fan-in, fan-out, blast
    /// radius, and the top dependents by name.
    Hotspots,
    /// Every hotspot symbol's dependents by name: identity, the exact
    /// dependent count, and the top dependents (relational-lookup view).
    Dependents,
    /// Every layer violation at unit grain, plus every dependency cycle.
    Violations,
    /// Every domain and group with the full dependency map.
    Domains,
    /// Everything above, deduplicated, in one document.
    All,
}

impl View {
    /// Every view name, for CLI validation and did-you-mean suggestions.
    pub const NAMES: &'static [&'static str] = &[
        "summary",
        "hotspots",
        "dependents",
        "violations",
        "domains",
        "all",
    ];

    /// Parse a CLI view name.
    pub fn by_name(name: &str) -> Option<View> {
        match name {
            "summary" => Some(View::Summary),
            "hotspots" => Some(View::Hotspots),
            "dependents" => Some(View::Dependents),
            "violations" => Some(View::Violations),
            "domains" => Some(View::Domains),
            "all" => Some(View::All),
            _ => None,
        }
    }

    /// Stable display name.
    pub fn name(self) -> &'static str {
        match self {
            View::Summary => "summary",
            View::Hotspots => "hotspots",
            View::Dependents => "dependents",
            View::Violations => "violations",
            View::Domains => "domains",
            View::All => "all",
        }
    }
}

/// Assembly options for [`verbalize`].
#[derive(Clone, Debug, Default)]
pub struct Options {
    pub view: View,
    /// Character budget for the whole document (sentences + newlines).
    /// `None` = unbounded. Truncation is honest: an omission sentence
    /// reports exactly how much was cut.
    pub budget: Option<usize>,
}

/// One verbalized document: the declared glossary and the sentence stream
/// (glossary prelude lines first, then body sentences).
#[derive(Clone, Debug, Default)]
pub struct Document {
    /// Declared handles, in declaration order.
    pub glossary: Vec<Handle>,
    /// The sentences, one per line in [`Document::to_text`].
    pub sentences: Vec<String>,
    /// Sentences cut by the budget (0 when unbounded or under budget).
    pub omitted: usize,
    /// Sentence count before the budget cut (excluding the omission line).
    pub total: usize,
}

impl Document {
    /// The plain-text rendering: one sentence per line, newline-terminated.
    pub fn to_text(&self) -> String {
        let mut out = String::new();
        for s in &self.sentences {
            out.push_str(s);
            out.push('\n');
        }
        out
    }

    /// Self-conformance: run the ADR-0008 checker over this document.
    /// The engine polices itself — CI asserts this returns no violations
    /// for real pipeline output.
    pub fn check(&self) -> Vec<Violation> {
        let refs: Vec<&str> = self.sentences.iter().map(String::as_str).collect();
        grammar::check(&refs, &self.glossary)
    }

    /// The deterministic `--json` envelope (schema [`REPORT_FORMAT`]).
    pub fn to_json(&self, dir: &str, view: &str) -> Json {
        Json::obj([
            ("schema", Json::str(REPORT_FORMAT)),
            ("command", Json::str("verbalize")),
            ("dir", Json::str(dir)),
            ("view", Json::str(view)),
            ("template_version", Json::from(t::TEMPLATE_VERSION as u64)),
            (
                "glossary",
                Json::Array(
                    self.glossary
                        .iter()
                        .map(|h| {
                            Json::obj([
                                ("handle", Json::str(&h.handle)),
                                ("expansion", Json::str(&h.expansion)),
                            ])
                        })
                        .collect(),
                ),
            ),
            (
                "sentences",
                Json::Array(self.sentences.iter().map(Json::str).collect()),
            ),
            ("total_sentences", Json::from(self.total)),
            ("omitted", Json::from(self.omitted)),
        ])
    }
}

/// Verbalize one analysis into the chosen view. Pure and deterministic:
/// same analysis, same options, byte-identical document.
pub fn verbalize(analysis: &Analysis, opts: &Options) -> Document {
    let facts = facts::extract(analysis);
    let (glossary, body) = match opts.view {
        View::Summary => {
            let n = facts.symbols.len().min(SUMMARY_HOTSPOTS);
            let g = Glossary::over(&facts.domains, &facts.symbols[..n]);
            let mut body = section_overview(&facts);
            body.extend(section_domains(&facts, &g, Some(SUMMARY_DEPS_PER_DOMAIN)));
            body.extend(section_hotspots(&facts, &g, n, false));
            body.extend(section_entries_and_flows(&facts));
            (g, body)
        }
        View::Hotspots => {
            let g = Glossary::over(&[], &facts.symbols);
            let body = section_hotspots(&facts, &g, facts.symbols.len(), true);
            (g, body)
        }
        View::Dependents => {
            let g = Glossary::over(&[], &facts.symbols);
            let body = section_dependents(&facts, &g);
            (g, body)
        }
        View::Violations => (Glossary::default(), section_violations(&facts)),
        View::Domains => {
            let g = Glossary::over(&facts.domains, &[]);
            let body = section_domains(&facts, &g, None);
            (g, body)
        }
        View::All => {
            let g = Glossary::over(&facts.domains, &facts.symbols);
            let mut body = section_overview(&facts);
            body.extend(section_domains(&facts, &g, None));
            body.extend(section_hotspots(&facts, &g, facts.symbols.len(), true));
            body.extend(section_entries_and_flows(&facts));
            body.extend(section_violations(&facts));
            (g, body)
        }
    };
    assemble(glossary, body, opts.budget)
}

/// Verbalize one explicitly targeted node: identity, fan-in, fan-out, blast
/// radius, the exact dependent count, and the top dependents by name.
/// Target resolution shares `explain`'s exact semantics (id, then
/// file path, then name; ambiguity and not-found carry the same payloads).
pub fn verbalize_target(
    analysis: &Analysis,
    target: &str,
    budget: Option<usize>,
) -> Result<Document, ExplainError> {
    let node = crate::explain::resolve(&analysis.graph, target)?.clone();
    let fact = facts::target_fact(analysis, &node);
    let glossary = Glossary::for_target(&fact);
    let subject = glossary.symbol(&fact.id).unwrap_or("F1").to_string();
    let total_nodes = analysis.graph.node_count() as u64;
    let mut body = vec![
        t::node_identity(&t::NodeIdentity {
            subject: &subject,
            kind: fact.kind,
            name: &fact.name,
            domain: &fact.domain,
            layer: &fact.layer,
            archetype: fact.archetype,
        }),
        t::hotspot_fan_in(&t::Hotspot {
            subject: &subject,
            degree: fact.fan_in,
            total_nodes,
        }),
        t::hotspot_fan_out(&t::Hotspot {
            subject: &subject,
            degree: fact.fan_out,
            total_nodes,
        }),
        t::blast_radius(&t::BlastRadius {
            subject: &subject,
            affected: fact.blast,
            total_nodes,
        }),
    ];
    body.extend(dependents_of(&fact, &subject, total_nodes));
    Ok(assemble(glossary, body, budget))
}

// ---------------------------------------------------------------------------
// Sections
// ---------------------------------------------------------------------------

fn section_overview(facts: &Facts) -> Vec<String> {
    let mut out = vec![
        t::graph_overview(&t::GraphOverview {
            nodes: facts.totals.nodes,
            edges: facts.totals.edges,
        }),
        t::parse_coverage(&t::ParseCoverage {
            parsed: facts
                .totals
                .discovered_files
                .saturating_sub(facts.totals.parse_failures),
            total: facts.totals.discovered_files,
            failures: facts.totals.parse_failures,
        }),
    ];
    if facts.totals.parse_failures > 0 {
        out.push(t::parse_omissions(&t::ParseCoverage {
            parsed: 0,
            total: facts.totals.discovered_files,
            failures: facts.totals.parse_failures,
        }));
    }
    out.push(t::violations_total(&t::ViolationsTotal {
        violations: facts.totals.violation_edges,
    }));
    out.push(t::cycles_total(&t::CyclesTotal {
        cycles: facts.cycles.len() as u64,
    }));
    out
}

/// Domain-major: each domain's summary immediately followed by its outgoing
/// dependencies (capped per domain when `deps_cap` is set), then the
/// infrastructure groups, then group-led dependencies.
fn section_domains(facts: &Facts, glossary: &Glossary, deps_cap: Option<usize>) -> Vec<String> {
    let mut out = Vec::new();
    let subject_of = |name: &str| -> String {
        glossary
            .domain(name)
            .map_or_else(|| t::name_span(name), str::to_string)
    };
    for d in &facts.domains {
        out.push(t::domain_summary(&t::DomainSummary {
            subject: &subject_of(&d.name),
            files: d.files,
            total_files: facts.totals.files,
            symbols: d.symbols,
            total_symbols: facts.totals.symbols,
        }));
        let outgoing = facts.deps.iter().filter(|dep| dep.from == d.name);
        let capped: Vec<_> = match deps_cap {
            Some(cap) => outgoing.take(cap).collect(),
            None => outgoing.collect(),
        };
        for dep in capped {
            out.push(t::dependency(&t::Dependency {
                from: &subject_of(&dep.from),
                to: &subject_of(&dep.to),
                references: dep.references,
                total_references: facts.totals.domain_references,
                chief_unit: dep.chief_unit.as_deref(),
            }));
        }
    }
    for g in &facts.groups {
        out.push(t::infrastructure_group(&t::InfrastructureGroup {
            name: &g.name,
            files: g.files,
            total_files: facts.totals.files,
        }));
    }
    for dep in &facts.deps {
        if facts.groups.iter().any(|g| g.name == dep.from) {
            out.push(t::dependency(&t::Dependency {
                from: &subject_of(&dep.from),
                to: &subject_of(&dep.to),
                references: dep.references,
                total_references: facts.totals.domain_references,
                chief_unit: dep.chief_unit.as_deref(),
            }));
        }
    }
    out
}

/// Handle-major hotspot cards: identity, fan-in, then (in full mode)
/// fan-out, blast radius, the exact dependent count, and the top dependents
/// by name per symbol.
fn section_hotspots(facts: &Facts, glossary: &Glossary, n: usize, full: bool) -> Vec<String> {
    let mut out = Vec::new();
    for s in facts.symbols.iter().take(n) {
        let Some(subject) = glossary.symbol(&s.id) else {
            continue;
        };
        out.push(t::node_identity(&t::NodeIdentity {
            subject,
            kind: s.kind,
            name: &s.name,
            domain: &s.domain,
            layer: &s.layer,
            archetype: s.archetype,
        }));
        out.push(t::hotspot_fan_in(&t::Hotspot {
            subject,
            degree: s.fan_in,
            total_nodes: facts.totals.nodes,
        }));
        if full {
            out.push(t::hotspot_fan_out(&t::Hotspot {
                subject,
                degree: s.fan_out,
                total_nodes: facts.totals.nodes,
            }));
            out.push(t::blast_radius(&t::BlastRadius {
                subject,
                affected: s.blast,
                total_nodes: facts.totals.nodes,
            }));
            out.extend(dependents_of(s, subject, facts.totals.nodes));
        }
    }
    out
}

/// Handle-major dependent cards (the `dependents` view): identity, the
/// exact dependent count, then the top dependents by name — the
/// relational-lookup answer to "what depends on X".
fn section_dependents(facts: &Facts, glossary: &Glossary) -> Vec<String> {
    let mut out = Vec::new();
    for s in &facts.symbols {
        let Some(subject) = glossary.symbol(&s.id) else {
            continue;
        };
        out.push(t::node_identity(&t::NodeIdentity {
            subject,
            kind: s.kind,
            name: &s.name,
            domain: &s.domain,
            layer: &s.layer,
            archetype: s.archetype,
        }));
        out.extend(dependents_of(s, subject, facts.totals.nodes));
    }
    out
}

/// One symbol's dependents block: the exact count (with the graph-wide
/// denominator — honesty about how many stay unnamed), then one sentence per
/// named dependent, in the facts' deterministic order (dependent fan-in
/// desc, id asc).
fn dependents_of(s: &facts::SymbolFact, subject: &str, total_nodes: u64) -> Vec<String> {
    let mut out = vec![t::dependents_total(&t::DependentsTotal {
        subject,
        dependents: s.fan_in,
        total_nodes,
    })];
    for d in &s.dependents {
        out.push(t::dependent_edge(&t::DependentEdge {
            subject,
            kind: d.kind,
            name: &d.name,
            path: &d.path,
        }));
    }
    out
}

fn section_entries_and_flows(facts: &Facts) -> Vec<String> {
    let mut out = Vec::new();
    let total = facts.entries.len() as u64;
    for e in facts.entries.iter().take(ENTRIES_LISTED) {
        out.push(t::entry_point(&t::EntryPoint {
            kind: e.kind,
            name: &e.name,
            path: &e.path,
            total,
        }));
    }
    for f in facts.flows.iter().take(FLOWS_LISTED) {
        out.push(t::flow_step(&t::FlowStep {
            name: &f.name,
            depth: f.depth,
            elements: f.elements,
        }));
    }
    out
}

fn section_violations(facts: &Facts) -> Vec<String> {
    let mut out = vec![t::violations_total(&t::ViolationsTotal {
        violations: facts.totals.violation_edges,
    })];
    for v in &facts.violations {
        out.push(t::layer_violation(&t::LayerViolation {
            from_unit: &v.from_unit,
            from_layer: &v.from_layer,
            to_unit: &v.to_unit,
            to_layer: &v.to_layer,
            violations: v.violations,
            total_violations: facts.totals.violation_edges,
        }));
    }
    out.push(t::cycles_total(&t::CyclesTotal {
        cycles: facts.cycles.len() as u64,
    }));
    for c in &facts.cycles {
        out.push(t::cycle(&t::Cycle { files: c }));
    }
    out
}

// ---------------------------------------------------------------------------
// Assembly: prelude + dedup + budget honesty
// ---------------------------------------------------------------------------

/// Prelude-first assembly with exact-duplicate removal and honest budget
/// truncation. Any prefix of the assembled document is itself a valid
/// document (define-before-reference), which is what makes the budget cut
/// safe. Crate-visible: the navigator's prose format assembles its own body
/// under the same contract.
pub(crate) fn assemble(glossary: Glossary, body: Vec<String>, budget: Option<usize>) -> Document {
    let mut sentences = glossary.lines();
    let mut seen: BTreeSet<String> = sentences.iter().cloned().collect();
    for s in body {
        if seen.insert(s.clone()) {
            sentences.push(s);
        }
    }
    let total = sentences.len();
    let mut omitted = 0usize;
    if let Some(budget) = budget {
        let cost = |s: &str| s.chars().count() + 1;
        let full: usize = sentences.iter().map(|s| cost(s)).sum();
        if full > budget {
            // Longest prefix whose cost plus its omission line fits.
            let mut keep = sentences.len();
            let mut used = full;
            loop {
                let omission = t::budget_omission(&t::BudgetOmission {
                    omitted: (total - keep) as u64,
                    total: total as u64,
                });
                if keep == 0 || used + cost(&omission) <= budget {
                    break;
                }
                keep -= 1;
                used -= cost(&sentences[keep]);
            }
            omitted = total - keep;
            sentences.truncate(keep);
            sentences.push(t::budget_omission(&t::BudgetOmission {
                omitted: omitted as u64,
                total: total as u64,
            }));
        }
    }
    Document {
        glossary: glossary.handles().to_vec(),
        sentences,
        omitted,
        total,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::Graph;
    use crate::ir::ontology::{edge, node as ont};
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

    fn sample() -> Analysis {
        let mut g = Graph::new();
        let fd = file(&mut g, "src/Shop.Domain/Order.cs");
        let order = sym(&mut g, &fd, ont::TYPE, "Order");
        let fi = file(&mut g, "src/Shop.Infrastructure/Repo.cs");
        let repo = sym(&mut g, &fi, ont::TYPE, "Repo");
        let fa = file(&mut g, "src/Shop.API/Program.cs");
        let main_fn = sym(&mut g, &fa, ont::FUNCTION, "main");
        g.add_edge(order.clone(), edge::USES_TYPE, repo.clone(), vec![]);
        g.add_edge(main_fn.clone(), edge::USES_TYPE, order.clone(), vec![]);
        g.add_edge(repo.clone(), edge::USES_TYPE, order, vec![]);
        g.add_edge(repo, edge::USES_TYPE, main_fn, vec![]);
        Analysis {
            graph: g,
            stats: AnalysisStats {
                files: 3,
                lossless_files: 3,
                diagnostics: 0,
                error_bytes: 0,
                total_bytes: 100,
                parse_failures: 1,
            },
        }
    }

    fn all_views() -> Vec<View> {
        vec![
            View::Summary,
            View::Hotspots,
            View::Dependents,
            View::Violations,
            View::Domains,
            View::All,
        ]
    }

    #[test]
    fn every_view_passes_the_grammar_on_a_fixture() {
        let analysis = sample();
        for view in all_views() {
            let doc = verbalize(&analysis, &Options { view, budget: None });
            let vs = doc.check();
            assert!(vs.is_empty(), "view {}: {vs:#?}", view.name());
            assert!(!doc.sentences.is_empty(), "view {}", view.name());
        }
    }

    #[test]
    fn documents_are_byte_deterministic() {
        let analysis = sample();
        for view in all_views() {
            let a = verbalize(&analysis, &Options { view, budget: None });
            let b = verbalize(&sample(), &Options { view, budget: None });
            assert_eq!(a.to_text(), b.to_text(), "view {}", view.name());
        }
    }

    #[test]
    fn budget_truncation_is_honest_and_still_conformant() {
        let analysis = sample();
        let full = verbalize(
            &analysis,
            &Options {
                view: View::All,
                budget: None,
            },
        );
        let budget = full.to_text().len() / 2;
        let cut = verbalize(
            &analysis,
            &Options {
                view: View::All,
                budget: Some(budget),
            },
        );
        assert!(cut.omitted > 0);
        assert_eq!(cut.total, full.sentences.len());
        let last = cut.sentences.last().unwrap();
        assert!(last.starts_with("The budget omits"), "{last}");
        assert!(
            cut.to_text().len() <= budget,
            "{} > {budget}",
            cut.to_text().len()
        );
        let vs = cut.check();
        assert!(vs.is_empty(), "{vs:#?}");
    }

    #[test]
    fn under_budget_documents_are_untouched() {
        let analysis = sample();
        let doc = verbalize(
            &analysis,
            &Options {
                view: View::Summary,
                budget: Some(1_000_000),
            },
        );
        assert_eq!(doc.omitted, 0);
        assert!(!doc
            .sentences
            .iter()
            .any(|s| s.starts_with("The budget omits")));
    }

    #[test]
    fn target_document_describes_one_node() {
        let analysis = sample();
        let doc = verbalize_target(&analysis, "Order", None).unwrap();
        let vs = doc.check();
        assert!(vs.is_empty(), "{vs:#?}");
        assert_eq!(doc.glossary.len(), 1);
        assert_eq!(doc.glossary[0].handle, "F1");
        assert!(doc.sentences.iter().any(|s| s.contains("fan-in")));
        assert!(doc
            .sentences
            .iter()
            .any(|s| s.contains("transitive references")));
    }

    #[test]
    fn dependents_view_names_the_dependents() {
        // Order is depended on by main and Repo; the dependents view must
        // name both, one sentence each, grammar-clean.
        let analysis = sample();
        let doc = verbalize(
            &analysis,
            &Options {
                view: View::Dependents,
                budget: None,
            },
        );
        let vs = doc.check();
        assert!(vs.is_empty(), "{vs:#?}");
        assert!(
            doc.sentences
                .iter()
                .any(|s| s.contains("`main`") && s.contains("depends on")),
            "{}",
            doc.to_text()
        );
        assert!(
            doc.sentences
                .iter()
                .any(|s| s.contains("`Repo`") && s.contains("depends on")),
            "{}",
            doc.to_text()
        );
        assert!(
            doc.sentences.iter().any(|s| s.contains("dependents of")),
            "{}",
            doc.to_text()
        );
    }

    #[test]
    fn target_document_names_the_dependents() {
        let analysis = sample();
        let doc = verbalize_target(&analysis, "Order", None).unwrap();
        let vs = doc.check();
        assert!(vs.is_empty(), "{vs:#?}");
        assert!(
            doc.sentences
                .iter()
                .any(|s| s.contains("`main`") && s.contains("depends on F1")),
            "{}",
            doc.to_text()
        );
        assert!(
            doc.sentences
                .iter()
                .any(|s| s.contains("`Repo`") && s.contains("depends on F1")),
            "{}",
            doc.to_text()
        );
    }

    #[test]
    fn target_resolution_errors_mirror_explain() {
        let analysis = sample();
        assert!(matches!(
            verbalize_target(&analysis, "NoSuchThing", None),
            Err(ExplainError::NotFound { .. })
        ));
    }

    #[test]
    fn duplicate_sentences_are_dropped() {
        // The All view composes sections that each state the violation and
        // cycle totals; dedup must keep exactly one of each.
        let analysis = sample();
        let doc = verbalize(
            &analysis,
            &Options {
                view: View::All,
                budget: None,
            },
        );
        let totals: Vec<&String> = doc
            .sentences
            .iter()
            .filter(|s| s.starts_with("The graph holds"))
            .collect();
        assert_eq!(totals.len(), 1, "{totals:?}");
    }

    #[test]
    fn json_envelope_is_deterministic_and_schemad() {
        let analysis = sample();
        let doc = verbalize(
            &analysis,
            &Options {
                view: View::Summary,
                budget: None,
            },
        );
        let a = doc.to_json("dir", "summary").to_line();
        let b = doc.to_json("dir", "summary").to_line();
        assert_eq!(a, b);
        assert!(a.contains(REPORT_FORMAT), "{a}");
        assert!(a.contains("\"template_version\":3"), "{a}");
    }

    #[test]
    fn view_names_round_trip() {
        for name in View::NAMES {
            assert_eq!(View::by_name(name).unwrap().name(), *name);
        }
        assert!(View::by_name("nope").is_none());
    }
}
