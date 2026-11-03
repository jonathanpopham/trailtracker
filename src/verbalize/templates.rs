//! The versioned template registry (V1, epic E-V): one function per fact
//! family, typed struct in, sentence out.
//!
//! Every template renders a single ADR-0008-conforming sentence from a typed
//! fact — string formatting over arithmetic, no model anywhere. The compiler
//! enforces the slots (a template cannot be called with a missing fact), and
//! [`crate::verbalize::grammar::check`] enforces the output language:
//! standalone sentences (R1), one fact each (R2), glossary-gated handles
//! (R3), anchored numbers (R4), facts only (R6), vocabulary closure (R7),
//! the 160-char budget (R8), and encoding safety (R9).
//!
//! Slot discipline: every free-text slot (names, paths, labels) passes
//! through [`code_span`] — sanitized (backticks, control, bidi and
//! zero-width codepoints removed), truncated deterministically, and wrapped
//! in backticks so the grammar treats it as code, never as prose. Numbers
//! render with thousands separators and always travel with a unit word or a
//! denominator. Templates whose slot count could overflow the R8 budget
//! shrink their spans deterministically ([`shrink_to_fit`]) instead of ever
//! emitting an over-budget sentence.

use crate::verbalize::grammar::MAX_SENTENCE_CHARS;

/// Version of the sentence-template registry. Bump on ANY wording change:
/// goldens pin template output byte-for-byte, so a silent rewording is a
/// regression, not a refactor. v2 added the dependents family
/// ([`dependents_total`], [`dependent_edge`]). v3 added the nav-pack family
/// ([`read_span`], [`domain_nodes`], [`layer_nodes`], [`depends_edge`]).
pub const TEMPLATE_VERSION: u32 = 3;

/// Default per-slot character cap (content chars inside the backticks).
const DEFAULT_SPAN_CAP: usize = 48;

/// Hard floor for a shrunken slot: below this a name is unrecognizable.
const MIN_SPAN_CAP: usize = 8;

/// The six layer names the layers extractor emits. These render as plain
/// capitalized proper names; anything else is backticked as code.
const KNOWN_LAYERS: &[&str] = &[
    "Domain",
    "Application",
    "Infrastructure",
    "Presentation",
    "Test",
    "Shared",
];

// ---------------------------------------------------------------------------
// Slot helpers
// ---------------------------------------------------------------------------

/// Strip everything ADR-0008 R9 forbids inside a sentence — control
/// characters, zero-width and bidirectional controls — and neutralize
/// backticks (a backtick inside a name would silently split the code span).
fn sanitize(raw: &str) -> String {
    raw.chars()
        .filter(|c| !c.is_control() && !is_invisible_or_bidi(*c))
        .map(|c| if c == '`' { '\'' } else { c })
        .collect()
}

/// Mirror of the grammar checker's R9 codepoint classes (kept private there;
/// the checker's own tests pin both sides).
fn is_invisible_or_bidi(c: char) -> bool {
    matches!(
        c,
        '\u{200B}'..='\u{200F}' | '\u{202A}'..='\u{202E}' | '\u{2066}'..='\u{2069}' | '\u{FEFF}'
    )
}

/// Render a free-text slot as a backticked code span: sanitized, truncated
/// to `cap` scalar values (with a deterministic `...` marker when cut), and
/// never empty (`?` stands in for a name that sanitizes away entirely).
fn code_span(raw: &str, cap: usize) -> String {
    let clean = sanitize(raw);
    let total = clean.chars().count();
    let content = if total == 0 {
        "?".to_string()
    } else if total > cap {
        let kept: String = clean.chars().take(cap.saturating_sub(3).max(1)).collect();
        format!("{kept}...")
    } else {
        clean
    };
    format!("`{content}`")
}

/// Format a count with thousands separators (`18155` → `18,155`), matching
/// the number shape the grammar's tokenizer joins into one token. Crate-
/// visible so the full report renders numbers in the same shape.
pub(crate) fn count(n: u64) -> String {
    let digits = n.to_string();
    let mut out = String::with_capacity(digits.len() + digits.len() / 3);
    for (i, c) in digits.chars().enumerate() {
        if i != 0 && (digits.len() - i).is_multiple_of(3) {
            out.push(',');
        }
        out.push(c);
    }
    out
}

/// A layer name slot: the six known layer names are capitalized proper names
/// and render bare; anything else (e.g. `unassigned`) is backticked.
fn layer_display(layer: &str, cap: usize) -> String {
    if KNOWN_LAYERS.contains(&layer) {
        layer.to_string()
    } else {
        code_span(layer, cap)
    }
}

/// Deterministically shrink span caps until the built sentence fits the R8
/// budget. `build` must be monotone in `cap` (smaller cap, shorter output);
/// every [`code_span`] is. Stops at [`MIN_SPAN_CAP`].
fn shrink_to_fit(build: impl Fn(usize) -> String) -> String {
    let mut cap = DEFAULT_SPAN_CAP;
    loop {
        let s = build(cap);
        if s.chars().count() <= MAX_SENTENCE_CHARS || cap <= MIN_SPAN_CAP {
            return s;
        }
        cap = cap.saturating_sub(4).max(MIN_SPAN_CAP);
    }
}

/// Render a cluster name (a domain without a handle, an infrastructure
/// group) as a subject-position code span with a conservative cap, so a
/// two-subject sentence still fits the R8 budget.
pub fn name_span(raw: &str) -> String {
    code_span(raw, 24)
}

/// Map a graph node kind (`Function`, `Type`, …) onto its registered
/// lowercase unit word. Unknown kinds fall back to `node`.
pub fn kind_word(kind: &str) -> &'static str {
    match kind {
        "File" => "file",
        "Module" => "module",
        "Function" => "function",
        "Type" => "type",
        "Constant" => "constant",
        "Package" => "package",
        "Class" => "class",
        "Method" => "method",
        "ExternalDependency" => "dependency",
        "UnresolvedSymbol" => "symbol",
        "Statement" => "statement",
        _ => "node",
    }
}

// ---------------------------------------------------------------------------
// Fact structs + templates
// ---------------------------------------------------------------------------

/// Identity of one node: what it is and how the extractors classify it.
pub struct NodeIdentity<'a> {
    /// Glossary handle for the node (`F1`); introduced by the caller's
    /// glossary before this sentence is emitted.
    pub subject: &'a str,
    /// Graph node kind (`Function`, `File`, …) — mapped via [`kind_word`].
    pub kind: &'a str,
    /// Node display name (free text; sanitized + backticked).
    pub name: &'a str,
    /// Domain label from `assign_domains` (free text; backticked).
    pub domain: &'a str,
    /// Layer name from `assign_layers` (known names render bare).
    pub layer: &'a str,
    /// Archetype from `classify_with` (free text; backticked).
    pub archetype: &'a str,
}

/// `F1 is the function `render`: domain `parse`, layer Presentation,
/// archetype `Command`.`
pub fn node_identity(f: &NodeIdentity) -> String {
    shrink_to_fit(|cap| {
        format!(
            "{} is the {} {}: domain {}, layer {}, archetype {}.",
            f.subject,
            kind_word(f.kind),
            code_span(f.name, cap),
            code_span(f.domain, cap / 2),
            layer_display(f.layer, cap / 2),
            code_span(f.archetype, cap / 2),
        )
    })
}

/// One counted dependency between two clusters (domains or infrastructure
/// groups), with an optional chief contributor.
pub struct Dependency<'a> {
    /// Subject cluster: a glossary handle (`D1`) or a pre-rendered code span.
    pub from: &'a str,
    /// Target cluster: a glossary handle (`D2`) or a pre-rendered code span.
    pub to: &'a str,
    /// Cross-cluster DEPENDS-family edge count for this pair.
    pub references: u64,
    /// Total cross-cluster edge mass in the graph (the denominator).
    pub total_references: u64,
    /// The unit receiving the most of this pair's references, when known.
    pub chief_unit: Option<&'a str>,
}

/// `D1 depends on D2 through 45 references of 320 references, most via the
/// unit `Orders`.` The chief clause is dropped, deterministically, when the
/// sentence cannot fit the R8 budget with it.
pub fn dependency(f: &Dependency) -> String {
    let base = format!(
        "{} depends on {} through {} references of {} references",
        f.from,
        f.to,
        count(f.references),
        count(f.total_references),
    );
    if let Some(unit) = f.chief_unit {
        let with_chief =
            shrink_to_fit(|cap| format!("{base}, most via the unit {}.", code_span(unit, cap)));
        if with_chief.chars().count() <= MAX_SENTENCE_CHARS {
            return with_chief;
        }
    }
    format!("{base}.")
}

/// Fan-in or fan-out of one node, with the graph-wide node denominator.
pub struct Hotspot<'a> {
    /// Glossary handle for the node (`F1`).
    pub subject: &'a str,
    /// Distinct DEPENDS-family neighbors (dependents or dependencies).
    pub degree: u64,
    /// Total nodes in the graph (the denominator).
    pub total_nodes: u64,
}

/// `F1 has fan-in 27 of 7,340 nodes.`
pub fn hotspot_fan_in(f: &Hotspot) -> String {
    format!(
        "{} has fan-in {} of {} nodes.",
        f.subject,
        count(f.degree),
        count(f.total_nodes)
    )
}

/// `F1 has fan-out 12 of 7,340 nodes.`
pub fn hotspot_fan_out(f: &Hotspot) -> String {
    format!(
        "{} has fan-out {} of {} nodes.",
        f.subject,
        count(f.degree),
        count(f.total_nodes)
    )
}

/// The exact dependent count of one node, with the graph-wide denominator.
/// Deliberately restates the fan-in fact in dependents language (fan-in =
/// distinct dependents): retrieval over "dependents" questions matches this
/// sentence lexically where `fan-in` does not.
pub struct DependentsTotal<'a> {
    /// Glossary handle for the depended-on node (`F1`).
    pub subject: &'a str,
    /// Distinct DEPENDS-family dependents (the node's fan-in).
    pub dependents: u64,
    /// Total nodes in the graph (the denominator).
    pub total_nodes: u64,
}

/// `F1 has 118 dependents of 18,165 nodes.`
pub fn dependents_total(f: &DependentsTotal) -> String {
    format!(
        "{} has {} dependents of {} nodes.",
        f.subject,
        count(f.dependents),
        count(f.total_nodes)
    )
}

/// One named dependent of a node: who depends on the subject (R2: one
/// dependent per sentence, never a comma-joined list).
pub struct DependentEdge<'a> {
    /// Glossary handle for the depended-on node (`F1`).
    pub subject: &'a str,
    /// Dependent's graph node kind (`Function`, …) — mapped via [`kind_word`].
    pub kind: &'a str,
    /// Dependent's display name (free text; sanitized + backticked).
    pub name: &'a str,
    /// Dependent's owning file path (backticked); empty when unknown.
    pub path: &'a str,
}

/// `The function `getSchemaHints` in the file `src/hints.ts` depends on F1.`
/// The file clause is dropped when the path is unknown.
pub fn dependent_edge(f: &DependentEdge) -> String {
    shrink_to_fit(|cap| {
        if f.path.is_empty() {
            format!(
                "The {} {} depends on {}.",
                kind_word(f.kind),
                code_span(f.name, cap),
                f.subject,
            )
        } else {
            format!(
                "The {} {} in the file {} depends on {}.",
                kind_word(f.kind),
                code_span(f.name, cap),
                code_span(f.path, cap),
                f.subject,
            )
        }
    })
}

/// Transitive reverse reachability of one node (the `query blast-radius`
/// machinery).
pub struct BlastRadius<'a> {
    /// Glossary handle for the node (`F1`).
    pub subject: &'a str,
    /// Nodes in the transitive reverse-reachability set.
    pub affected: u64,
    /// Total nodes in the graph (the denominator).
    pub total_nodes: u64,
}

/// `213 nodes of 7,340 nodes depend on F1 through transitive references.`
pub fn blast_radius(f: &BlastRadius) -> String {
    format!(
        "{} nodes of {} nodes depend on {} through transitive references.",
        count(f.affected),
        count(f.total_nodes),
        f.subject
    )
}

/// One layer-direction violation at unit grain (the `violations` report row).
pub struct LayerViolation<'a> {
    pub from_unit: &'a str,
    pub from_layer: &'a str,
    pub to_unit: &'a str,
    pub to_layer: &'a str,
    /// Violating edges between the two units.
    pub violations: u64,
    /// Total violating edge mass in the graph (the denominator).
    pub total_violations: u64,
}

/// `The `Ordering.Domain` unit in the Domain layer depends on the
/// `Ordering.Infrastructure` unit in the Infrastructure layer through 2
/// violations of 7 violations.` Falls back to the layer-free variant when
/// the full sentence cannot fit the R8 budget.
pub fn layer_violation(f: &LayerViolation) -> String {
    let full = shrink_to_fit(|cap| {
        format!(
            "The {} unit in the {} layer depends on the {} unit in the {} layer through {} \
             violations of {} violations.",
            code_span(f.from_unit, cap),
            layer_display(f.from_layer, cap / 2),
            code_span(f.to_unit, cap),
            layer_display(f.to_layer, cap / 2),
            count(f.violations),
            count(f.total_violations),
        )
    });
    if full.chars().count() <= MAX_SENTENCE_CHARS {
        return full;
    }
    shrink_to_fit(|cap| {
        format!(
            "The {} unit depends on the {} unit through {} violations of {} violations.",
            code_span(f.from_unit, cap),
            code_span(f.to_unit, cap),
            count(f.violations),
            count(f.total_violations),
        )
    })
}

/// One file-level dependency cycle (a Tarjan SCC of size > 1).
pub struct Cycle<'a> {
    /// Member file paths, sorted (the fact extractor guarantees order).
    pub files: &'a [String],
}

/// How many cycle members are listed by path before the sentence names only
/// the count (long cycles would overflow R8 and read as noise).
const CYCLE_LIST_MAX: usize = 3;

/// `A dependency cycle links 2 files: `src/a.rs`, `src/b.rs`.` — or, past
/// [`CYCLE_LIST_MAX`] members, `A dependency cycle links 12 files.`
pub fn cycle(f: &Cycle) -> String {
    let n = f.files.len() as u64;
    if f.files.len() > CYCLE_LIST_MAX {
        return format!("A dependency cycle links {} files.", count(n));
    }
    let listed = shrink_to_fit(|cap| {
        let spans: Vec<String> = f.files.iter().map(|p| code_span(p, cap)).collect();
        format!(
            "A dependency cycle links {} files: {}.",
            count(n),
            spans.join(", ")
        )
    });
    if listed.chars().count() <= MAX_SENTENCE_CHARS {
        listed
    } else {
        format!("A dependency cycle links {} files.", count(n))
    }
}

/// Size of one recovered domain, with graph-wide denominators.
pub struct DomainSummary<'a> {
    /// Glossary handle for the domain (`D1`).
    pub subject: &'a str,
    pub files: u64,
    pub total_files: u64,
    pub symbols: u64,
    pub total_symbols: u64,
}

/// `D1 contains 34 of 120 files and 245 of 890 symbols.`
pub fn domain_summary(f: &DomainSummary) -> String {
    format!(
        "{} contains {} of {} files and {} of {} symbols.",
        f.subject,
        count(f.files),
        count(f.total_files),
        count(f.symbols),
        count(f.total_symbols),
    )
}

/// Size of one infrastructure group (scaffold/docs/generated/root — the
/// deterministic path classification, not a clustering).
pub struct InfrastructureGroup<'a> {
    /// Group display name (`Build & Tooling`; free text, backticked).
    pub name: &'a str,
    pub files: u64,
    pub total_files: u64,
}

/// `The `Build & Tooling` group holds 12 of 120 files.`
pub fn infrastructure_group(f: &InfrastructureGroup) -> String {
    shrink_to_fit(|cap| {
        format!(
            "The {} group holds {} of {} files.",
            code_span(f.name, cap),
            count(f.files),
            count(f.total_files),
        )
    })
}

/// Shape of one recovered workflow (a `flow` Function node).
pub struct FlowStep<'a> {
    /// Flow display name (free text, backticked).
    pub name: &'a str,
    /// The flow node's `depth` property.
    pub depth: u64,
    /// The flow node's `element_count` property.
    pub elements: u64,
}

/// `The `flow` function `checkout` has depth 12 and 34 nodes.`
pub fn flow_step(f: &FlowStep) -> String {
    shrink_to_fit(|cap| {
        format!(
            "The `flow` function {} has depth {} and {} nodes.",
            code_span(f.name, cap),
            count(f.depth),
            count(f.elements),
        )
    })
}

/// One program entry point (`main`-named Function).
pub struct EntryPoint<'a> {
    /// Graph node kind, mapped via [`kind_word`].
    pub kind: &'a str,
    /// Node display name (free text, backticked).
    pub name: &'a str,
    /// Owning file path (free text, backticked); empty when unknown.
    pub path: &'a str,
    /// Total entry points in the graph (the denominator).
    pub total: u64,
}

/// `The function `main` in the file `src/main.rs` is one entry point of 2
/// entry points.`
pub fn entry_point(f: &EntryPoint) -> String {
    shrink_to_fit(|cap| {
        if f.path.is_empty() {
            format!(
                "The {} {} is one entry point of {} entry points.",
                kind_word(f.kind),
                code_span(f.name, cap),
                count(f.total),
            )
        } else {
            format!(
                "The {} {} in the file {} is one entry point of {} entry points.",
                kind_word(f.kind),
                code_span(f.name, cap),
                code_span(f.path, cap),
                count(f.total),
            )
        }
    })
}

/// Parse coverage of the analysis (from `AnalysisStats`).
pub struct ParseCoverage {
    /// Files that parsed (discovered minus failures).
    pub parsed: u64,
    /// Files discovered for analysis (the denominator).
    pub total: u64,
    /// Files whose parse failed (absent from the graph's content).
    pub failures: u64,
}

/// `The coverage spans 45 files of 47 files.`
pub fn parse_coverage(f: &ParseCoverage) -> String {
    format!(
        "The coverage spans {} files of {} files.",
        count(f.parsed),
        count(f.total)
    )
}

/// `The graph omits 2 files of 47 files.` — emitted only when failures > 0,
/// so omission is never silent (the nav-pack honesty rule).
pub fn parse_omissions(f: &ParseCoverage) -> String {
    format!(
        "The graph omits {} files of {} files.",
        count(f.failures),
        count(f.total)
    )
}

/// Whole-graph size (the overview fact).
pub struct GraphOverview {
    pub nodes: u64,
    pub edges: u64,
}

/// `The graph contains 7,340 nodes and 18,155 edges.`
pub fn graph_overview(f: &GraphOverview) -> String {
    format!(
        "The graph contains {} nodes and {} edges.",
        count(f.nodes),
        count(f.edges)
    )
}

/// Graph-wide violation mass (the summary-view aggregate).
pub struct ViolationsTotal {
    pub violations: u64,
}

/// `The graph holds 7 violations.`
pub fn violations_total(f: &ViolationsTotal) -> String {
    format!("The graph holds {} violations.", count(f.violations))
}

/// Graph-wide cycle count (the summary-view aggregate).
pub struct CyclesTotal {
    pub cycles: u64,
}

/// `The graph contains 3 cycles.`
pub fn cycles_total(f: &CyclesTotal) -> String {
    format!("The graph contains {} cycles.", count(f.cycles))
}

/// Honest truncation marker for a budgeted document.
pub struct BudgetOmission {
    pub omitted: u64,
    pub total: u64,
}

/// `The budget omits 34 sentences of 120 sentences.`
pub fn budget_omission(f: &BudgetOmission) -> String {
    format!(
        "The budget omits {} sentences of {} sentences.",
        count(f.omitted),
        count(f.total)
    )
}

// ---------------------------------------------------------------------------
// The nav-pack family (v3): prose rendering of the navigator's selection
// ---------------------------------------------------------------------------

/// One read-plan span: where a symbol lives, stated as a fact (R6 forbids
/// the imperative "read lines …"; the span fact carries the same
/// information). The subject is the symbol's glossary handle when the
/// document minted one, else its kind+name identity.
pub struct ReadSpan<'a> {
    /// Glossary handle (`F1`) when minted; `None` renders the identity form.
    pub subject: Option<&'a str>,
    /// Graph node kind (`Function`, …) — mapped via [`kind_word`]; used only
    /// in the identity form.
    pub kind: &'a str,
    /// Node display name (free text; sanitized + backticked); identity form.
    pub name: &'a str,
    /// Owning file path (free text; backticked).
    pub path: &'a str,
    /// 1-based start line.
    pub start: u64,
    /// Inclusive end line; `None` means "to the last line of the file".
    pub end: Option<u64>,
}

/// `F1 spans lines 393-825 in the file `src/nav.rs`.` — or, without an end
/// line, `F1 spans line 393 to the last line in the file `src/nav.rs`.`
pub fn read_span(f: &ReadSpan) -> String {
    shrink_to_fit(|cap| {
        let subject = match f.subject {
            Some(h) => h.to_string(),
            None => format!("The {} {}", kind_word(f.kind), code_span(f.name, cap)),
        };
        match f.end {
            Some(end) => format!(
                "{} spans lines {}-{} in the file {}.",
                subject,
                count(f.start),
                count(end),
                code_span(f.path, cap),
            ),
            None => format!(
                "{} spans line {} to the last line in the file {}.",
                subject,
                count(f.start),
                code_span(f.path, cap),
            ),
        }
    })
}

/// Node mass of one domain within a budget-shaped selection (the nav-pack
/// orientation row; the denominator is the selection, not the graph).
pub struct DomainNodes<'a> {
    /// Domain display name (free text; backticked).
    pub name: &'a str,
    /// Selected nodes classified into the domain.
    pub nodes: u64,
    /// Total selected nodes (the denominator).
    pub total_nodes: u64,
}

/// `The `parse` domain holds 12 nodes of 60 nodes.`
pub fn domain_nodes(f: &DomainNodes) -> String {
    shrink_to_fit(|cap| {
        format!(
            "The {} domain holds {} nodes of {} nodes.",
            code_span(f.name, cap),
            count(f.nodes),
            count(f.total_nodes),
        )
    })
}

/// Node mass of one layer within a budget-shaped selection (the nav-pack
/// orientation row; the denominator is the selection, not the graph).
pub struct LayerNodes<'a> {
    /// Layer name from `assign_layers` (known names render bare).
    pub layer: &'a str,
    /// Selected nodes classified into the layer.
    pub nodes: u64,
    /// Total selected nodes (the denominator).
    pub total_nodes: u64,
}

/// `The Presentation layer holds 9 nodes of 60 nodes.`
pub fn layer_nodes(f: &LayerNodes) -> String {
    shrink_to_fit(|cap| {
        format!(
            "The {} layer holds {} nodes of {} nodes.",
            layer_display(f.layer, cap),
            count(f.nodes),
            count(f.total_nodes),
        )
    })
}

/// One endpoint of a [`depends_edge`] sentence: a glossary handle, or a
/// kind+name identity with an optional owning file.
pub struct EdgeEndpoint<'a> {
    /// Glossary handle (`F1`) when minted; `None` renders the identity form.
    pub subject: Option<&'a str>,
    /// Graph node kind (`Function`, …) — mapped via [`kind_word`].
    pub kind: &'a str,
    /// Node display name (free text; sanitized + backticked).
    pub name: &'a str,
    /// Owning file path (backticked); empty drops the file clause.
    pub path: &'a str,
}

impl EdgeEndpoint<'_> {
    /// Render the endpoint: handle, or `the {kind} `{name}`[ in the file
    /// `{path}`]`. `with_path` = false drops the file clause (the R8
    /// fallback).
    fn render(&self, cap: usize, with_path: bool) -> String {
        match self.subject {
            Some(h) => h.to_string(),
            None => {
                let ident = format!("the {} {}", kind_word(self.kind), code_span(self.name, cap));
                if self.path.is_empty() || !with_path {
                    ident
                } else {
                    format!("{ident} in the file {}", code_span(self.path, cap))
                }
            }
        }
    }
}

/// One DEPENDS-family edge between two named nodes (R2: one edge per
/// sentence). `The function `a` in the file `x.rs` depends on the function
/// `b` in the file `y.rs`.` File clauses are dropped, deterministically,
/// when the full sentence cannot fit the R8 budget with them.
pub fn depends_edge(from: &EdgeEndpoint, to: &EdgeEndpoint) -> String {
    let sentence = |with_path: bool| {
        shrink_to_fit(move |cap| {
            let head = from.render(cap, with_path);
            let mut chars = head.chars();
            let capitalized = match chars.next() {
                Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
                None => head.clone(),
            };
            format!("{} depends on {}.", capitalized, to.render(cap, with_path))
        })
    };
    let full = sentence(true);
    if full.chars().count() <= MAX_SENTENCE_CHARS {
        full
    } else {
        sentence(false)
    }
}

// ---------------------------------------------------------------------------
// Glossary expansions (the right-hand side of `D1 = ...` lines)
// ---------------------------------------------------------------------------

/// Expansion for a domain handle: `the `parse` domain (34 files, 245
/// symbols)`. The emitted glossary line (`D1 = <expansion>`) is itself a
/// checked sentence, so the expansion obeys the same grammar.
pub fn domain_expansion(name: &str, files: u64, symbols: u64) -> String {
    shrink_to_fit(|cap| {
        format!(
            "the {} domain ({} files, {} symbols)",
            code_span(name, cap),
            count(files),
            count(symbols),
        )
    })
}

/// Expansion for a symbol handle: `the function `render` (`src/render.rs`,
/// line 42)`. Path and line are omitted when unknown.
pub fn symbol_expansion(kind: &str, name: &str, path: &str, line: u64) -> String {
    shrink_to_fit(|cap| {
        let ident = format!("the {} {}", kind_word(kind), code_span(name, cap));
        if path.is_empty() {
            ident
        } else if line == 0 {
            format!("{ident} ({})", code_span(path, cap))
        } else {
            format!("{ident} ({}, line {})", code_span(path, cap), count(line))
        }
    })
}

// ---------------------------------------------------------------------------
// Tests: every template's output passes the grammar under hostile slots
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verbalize::grammar::{self, Handle, OrderingKey};

    /// Hostile slot values: unicode, quotes, backticks, bidi controls,
    /// 100-char names, banned prose words hiding inside identifiers.
    fn nasty_inputs() -> Vec<String> {
        let mut v: Vec<String> = [
            "render",
            "Order",
            "src/it/handlers_and_hooks.rs",
            "with`backtick",
            "with'quote\"s and spaces",
            "häßlich_ünïcode_gëist",
            "名前_の_関数",
            "\u{202E}bidi\u{200B}attack\u{FEFF}",
            "tab\tname\nnewline",
            "it also probably frobnicates while huge",
            "note; consider: this",
            "",
            "   ",
            "-D1-",
            "D1",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        v.push("x".repeat(100));
        v.push("src/".repeat(30) + "mod.rs");
        // LCG-generated strings over a hostile alphabet (deterministic).
        let alphabet: Vec<char> = "ab`'\"\u{202E}\u{200B}\t\n;.,/:_-XY9 é名".chars().collect();
        let mut seed: u64 = 0x5DEECE66D;
        for _ in 0..64 {
            let len = (seed % 60) as usize + 1;
            let mut s = String::new();
            for _ in 0..len {
                seed = seed
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                s.push(alphabet[(seed >> 33) as usize % alphabet.len()]);
            }
            v.push(s);
        }
        v
    }

    fn counts() -> Vec<u64> {
        vec![0, 1, 2, 9, 42, 999, 18_155, 1_000_000, u64::MAX]
    }

    /// Check one body sentence against the grammar with the standard test
    /// glossary; panic with full context on any violation.
    fn assert_clean(sentence: &str, glossary: &[Handle]) {
        let line0: Vec<String> = glossary
            .iter()
            .map(|h| format!("{} = {}", h.handle, h.expansion))
            .collect();
        let mut doc: Vec<&str> = line0.iter().map(String::as_str).collect();
        doc.push(sentence);
        let vs = grammar::check_with(&doc, glossary, OrderingKey::None);
        assert!(vs.is_empty(), "sentence {sentence:?} violates: {vs:#?}");
    }

    fn std_glossary() -> Vec<Handle> {
        vec![
            Handle::new("D1", domain_expansion("parse", 34, 245)),
            Handle::new("D2", domain_expansion("lang", 12, 96)),
            Handle::new(
                "F1",
                symbol_expansion("Function", "render", "src/render.rs", 42),
            ),
        ]
    }

    #[test]
    fn node_identity_survives_hostile_slots() {
        let g = std_glossary();
        for name in nasty_inputs() {
            for domain in ["parse", "Shared/Platform", "häßlich`dömain", ""] {
                for layer in ["Presentation", "unassigned", "Wëird`Layer"] {
                    let s = node_identity(&NodeIdentity {
                        subject: "F1",
                        kind: "Function",
                        name: &name,
                        domain,
                        layer,
                        archetype: "Command",
                    });
                    assert_clean(&s, &g);
                }
            }
        }
    }

    #[test]
    fn node_identity_maps_unknown_kinds_to_node() {
        let g = std_glossary();
        for kind in ["Function", "File", "Type", "Statement", "Alien`Kind"] {
            let s = node_identity(&NodeIdentity {
                subject: "F1",
                kind,
                name: "thing",
                domain: "parse",
                layer: "Domain",
                archetype: "Unclassified",
            });
            assert_clean(&s, &g);
        }
    }

    #[test]
    fn dependency_with_and_without_chief_unit() {
        let g = std_glossary();
        for refs in counts() {
            for total in counts() {
                for chief in [None, Some("Orders"), Some("x".repeat(100)).as_deref()] {
                    let s = dependency(&Dependency {
                        from: "D1",
                        to: "D2",
                        references: refs,
                        total_references: total,
                        chief_unit: chief,
                    });
                    assert_clean(&s, &g);
                }
            }
        }
    }

    #[test]
    fn dependency_accepts_span_subjects() {
        let g = std_glossary();
        for name in nasty_inputs() {
            let span = code_span(&name, 24);
            let s = dependency(&Dependency {
                from: &span,
                to: "D1",
                references: 3,
                total_references: 10,
                chief_unit: None,
            });
            assert_clean(&s, &g);
        }
    }

    #[test]
    fn hotspots_and_blast_radius_carry_denominators() {
        let g = std_glossary();
        for degree in counts() {
            for total in counts() {
                assert_clean(
                    &hotspot_fan_in(&Hotspot {
                        subject: "F1",
                        degree,
                        total_nodes: total,
                    }),
                    &g,
                );
                assert_clean(
                    &hotspot_fan_out(&Hotspot {
                        subject: "F1",
                        degree,
                        total_nodes: total,
                    }),
                    &g,
                );
                assert_clean(
                    &blast_radius(&BlastRadius {
                        subject: "F1",
                        affected: degree,
                        total_nodes: total,
                    }),
                    &g,
                );
            }
        }
    }

    #[test]
    fn dependents_total_carries_unit_and_denominator() {
        let g = std_glossary();
        for dependents in counts() {
            for total in counts() {
                assert_clean(
                    &dependents_total(&DependentsTotal {
                        subject: "F1",
                        dependents,
                        total_nodes: total,
                    }),
                    &g,
                );
            }
        }
        assert_eq!(
            dependents_total(&DependentsTotal {
                subject: "F1",
                dependents: 118,
                total_nodes: 18_165,
            }),
            "F1 has 118 dependents of 18,165 nodes."
        );
    }

    #[test]
    fn dependent_edge_survives_hostile_slots() {
        let g = std_glossary();
        for name in nasty_inputs() {
            for path in ["src/hints.ts", "", "weird path.rs"] {
                for kind in ["Function", "Type", "File", "Alien`Kind"] {
                    let s = dependent_edge(&DependentEdge {
                        subject: "F1",
                        kind,
                        name: &name,
                        path,
                    });
                    assert_clean(&s, &g);
                }
            }
        }
        assert_eq!(
            dependent_edge(&DependentEdge {
                subject: "F1",
                kind: "Function",
                name: "getSchemaHints",
                path: "src/hints.ts",
            }),
            "The function `getSchemaHints` in the file `src/hints.ts` depends on F1."
        );
        assert_eq!(
            dependent_edge(&DependentEdge {
                subject: "F1",
                kind: "Function",
                name: "getSchemaHints",
                path: "",
            }),
            "The function `getSchemaHints` depends on F1."
        );
    }

    #[test]
    fn layer_violation_survives_hostile_units_and_layers() {
        let g = std_glossary();
        for unit in nasty_inputs() {
            for layer in ["Domain", "Infrastructure", "not`a Layer"] {
                let s = layer_violation(&LayerViolation {
                    from_unit: &unit,
                    from_layer: layer,
                    to_unit: "Ordering.Infrastructure",
                    to_layer: "Presentation",
                    violations: 2,
                    total_violations: u64::MAX,
                });
                assert_clean(&s, &g);
            }
        }
    }

    #[test]
    fn cycle_lists_short_and_counts_long() {
        let g = std_glossary();
        let short: Vec<String> = vec!["src/a.rs".into(), "src/b.rs".into()];
        let s = cycle(&Cycle { files: &short });
        assert!(s.contains("2 files:"), "{s}");
        assert_clean(&s, &g);

        let long: Vec<String> = (0..12).map(|i| format!("src/module_{i}/mod.rs")).collect();
        let s = cycle(&Cycle { files: &long });
        assert_eq!(s, "A dependency cycle links 12 files.");
        assert_clean(&s, &g);

        let hostile: Vec<String> = nasty_inputs().into_iter().take(3).collect();
        assert_clean(&cycle(&Cycle { files: &hostile }), &g);
    }

    #[test]
    fn domain_and_group_and_flow_and_entry_templates_conform() {
        let g = std_glossary();
        for n in counts() {
            assert_clean(
                &domain_summary(&DomainSummary {
                    subject: "D1",
                    files: n,
                    total_files: n.max(1),
                    symbols: n,
                    total_symbols: n.max(1),
                }),
                &g,
            );
        }
        for name in nasty_inputs() {
            assert_clean(
                &infrastructure_group(&InfrastructureGroup {
                    name: &name,
                    files: 12,
                    total_files: 120,
                }),
                &g,
            );
            assert_clean(
                &flow_step(&FlowStep {
                    name: &name,
                    depth: 12,
                    elements: 34,
                }),
                &g,
            );
            assert_clean(
                &entry_point(&EntryPoint {
                    kind: "Function",
                    name: &name,
                    path: "src/main.rs",
                    total: 3,
                }),
                &g,
            );
            assert_clean(
                &entry_point(&EntryPoint {
                    kind: "Function",
                    name: &name,
                    path: "",
                    total: 1,
                }),
                &g,
            );
        }
    }

    #[test]
    fn scalar_templates_conform() {
        let g = std_glossary();
        for n in counts() {
            let f = ParseCoverage {
                parsed: n,
                total: n.max(1),
                failures: n,
            };
            assert_clean(&parse_coverage(&f), &g);
            assert_clean(&parse_omissions(&f), &g);
            assert_clean(&graph_overview(&GraphOverview { nodes: n, edges: n }), &g);
            assert_clean(&violations_total(&ViolationsTotal { violations: n }), &g);
            assert_clean(&cycles_total(&CyclesTotal { cycles: n }), &g);
            assert_clean(
                &budget_omission(&BudgetOmission {
                    omitted: n,
                    total: n.max(1),
                }),
                &g,
            );
        }
    }

    #[test]
    fn glossary_expansions_render_as_checked_lines() {
        for name in nasty_inputs() {
            let d = Handle::new("D1", domain_expansion(&name, 34, 245));
            let line = format!("D1 = {}", d.expansion);
            let vs = grammar::check(&[line.as_str()], std::slice::from_ref(&d));
            assert!(vs.is_empty(), "domain glossary line {line:?}: {vs:#?}");

            for (path, line_no) in [("src/render.rs", 42), ("", 0), ("weird path.rs", 0)] {
                let f = Handle::new("F1", symbol_expansion("Function", &name, path, line_no));
                let line = format!("F1 = {}", f.expansion);
                let vs = grammar::check(&[line.as_str()], std::slice::from_ref(&f));
                assert!(vs.is_empty(), "symbol glossary line {line:?}: {vs:#?}");
            }
        }
    }

    #[test]
    fn spans_are_sanitized_truncated_and_never_empty() {
        assert_eq!(code_span("with`tick", 48), "`with'tick`");
        assert_eq!(code_span("", 48), "`?`");
        assert_eq!(code_span("\u{202E}\u{200B}\t", 48), "`?`");
        let long = code_span(&"x".repeat(100), 10);
        assert_eq!(long, format!("`{}...`", "x".repeat(7)));
        assert!(long.chars().count() <= 12);
    }

    #[test]
    fn counts_carry_thousands_separators() {
        assert_eq!(count(0), "0");
        assert_eq!(count(999), "999");
        assert_eq!(count(1_000), "1,000");
        assert_eq!(count(18_155), "18,155");
        assert_eq!(count(1_234_567), "1,234,567");
        assert_eq!(count(u64::MAX), "18,446,744,073,709,551,615");
    }

    #[test]
    fn templates_are_deterministic() {
        let f = NodeIdentity {
            subject: "F1",
            kind: "Function",
            name: "render",
            domain: "parse",
            layer: "Presentation",
            archetype: "Command",
        };
        assert_eq!(node_identity(&f), node_identity(&f));
        assert_eq!(
            node_identity(&f),
            "F1 is the function `render`: domain `parse`, layer Presentation, \
             archetype `Command`."
        );
    }

    #[test]
    fn read_span_survives_hostile_slots() {
        let g = std_glossary();
        for name in nasty_inputs() {
            for subject in [Some("F1"), None] {
                for end in [None, Some(42), Some(u64::MAX)] {
                    let s = read_span(&ReadSpan {
                        subject,
                        kind: "Function",
                        name: &name,
                        path: &name,
                        start: 7,
                        end,
                    });
                    assert_clean(&s, &g);
                }
            }
        }
    }

    #[test]
    fn read_span_renders_both_shapes() {
        assert_eq!(
            read_span(&ReadSpan {
                subject: Some("F1"),
                kind: "Function",
                name: "render",
                path: "src/nav.rs",
                start: 393,
                end: Some(825),
            }),
            "F1 spans lines 393-825 in the file `src/nav.rs`."
        );
        assert_eq!(
            read_span(&ReadSpan {
                subject: None,
                kind: "File",
                name: "glossary.rs",
                path: "src/verbalize/glossary.rs",
                start: 1,
                end: None,
            }),
            "The file `glossary.rs` spans line 1 to the last line in the file \
             `src/verbalize/glossary.rs`."
        );
    }

    #[test]
    fn cluster_node_rows_survive_hostile_slots() {
        let g = std_glossary();
        for name in nasty_inputs() {
            for nodes in counts() {
                let s = domain_nodes(&DomainNodes {
                    name: &name,
                    nodes,
                    total_nodes: 60,
                });
                assert_clean(&s, &g);
            }
        }
        for layer in ["Presentation", "unassigned", "Wëird`Layer", ""] {
            let s = layer_nodes(&LayerNodes {
                layer,
                nodes: 9,
                total_nodes: 60,
            });
            assert_clean(&s, &g);
        }
    }

    #[test]
    fn depends_edge_survives_hostile_slots_and_drops_paths_to_fit() {
        let g = std_glossary();
        for name in nasty_inputs() {
            let from = EdgeEndpoint {
                subject: None,
                kind: "Function",
                name: &name,
                path: &name,
            };
            let to = EdgeEndpoint {
                subject: Some("F1"),
                kind: "Function",
                name: "render",
                path: "src/render.rs",
            };
            assert_clean(&depends_edge(&from, &to), &g);
            assert_clean(&depends_edge(&to, &from), &g);
        }
        // Two maximal endpoints: the file clauses must drop, and the result
        // must still fit and pass.
        let long_a = "a".repeat(100);
        let long_b = "b".repeat(100);
        let long_path = "src/".repeat(30) + "mod.rs";
        let from = EdgeEndpoint {
            subject: None,
            kind: "Function",
            name: &long_a,
            path: &long_path,
        };
        let to = EdgeEndpoint {
            subject: None,
            kind: "Function",
            name: &long_b,
            path: &long_path,
        };
        let s = depends_edge(&from, &to);
        assert!(s.chars().count() <= MAX_SENTENCE_CHARS, "{s}");
        assert_clean(&s, &g);
    }
}
