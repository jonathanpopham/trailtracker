//! The dossier: TrailTracker's client-ready deliverable — ONE self-contained
//! HTML file that packages everything the engine knows about a repository
//! into a document a stakeholder can open in any browser, on any machine,
//! with the network cable unplugged.
//!
//! Composition (nothing here is re-derived; every section reuses the exact
//! single-source-of-truth pass the CLI already ships):
//!
//! - **Header** — repo name and headline stats straight from the
//!   [`crate::brief::brief_json`] overview (files, lines, nodes, edges,
//!   languages).
//! - **The brief** — the [`crate::brief`] model rendered as clean HTML:
//!   overview, architecture (domains table, largest units, module dependency
//!   map), entry points, hotspots, dependency cycles, and the plain-English
//!   synthesis.
//! - **The interactive code map** — the hierarchy view
//!   ([`crate::extract::HierarchyExtractor`]) serialized as Ontoloom wire JSON
//!   ([`crate::export::ontoloom_wire`]), embedded in a JSON script tag and
//!   driven by an inline adaptation of Ontoloom's code map (same project,
//!   same owner, same design): drill-only navigation (click-to-expand
//!   Domain → Unit → File → Symbol — no bulk expand-to-level buttons), a
//!   deterministic force-directed WEB layout as the default face (dot- and
//!   label-box collision resolution plus zoom-tiered label fading, so label
//!   text never overlaps at any drill depth), a dynamically respaced tidy
//!   TREE as the alternate, search, dependency edges, pan/zoom/fit, and an
//!   inspector panel. Business domains are colored; infrastructure groups
//!   render muted.
//! - **Enriched domains** (`enrich` feature builds ONLY — the section, the
//!   payload, and its renderer do not exist in the default/airgap build) —
//!   when the caller supplies a `trailtracker.enrich/v1` document, its
//!   clusters render as cards (name, description, responsibilities) plus the
//!   attestation block (model, prompt hash).
//! - **Layer violations** — the FULL dependency-direction report from
//!   [`crate::violations`] at unit grain: every violating from-unit → to-unit
//!   pair with edge counts and file-level evidence, grouped by layer pair
//!   (collapsible when a group runs long).
//! - **For your AI assistant** (N6) — the V1 verbalizer's `all` view at a
//!   [`COMPANION_BUDGET`]-char budget: ADR-0008 sentences (glossaried
//!   handles, standalone facts, denominators — the retrieval-safe digest a
//!   model consumes verbatim), embedded once with a one-click copy button
//!   and a collapsible preview. Humans scroll the report; their model gets
//!   fed in one click.
//! - **Footer** — tool version, an attested "generated" line, and the
//!   determinism/airgap statement.
//!
//! Airgap-grade by construction: inline CSS and JS only, no CDNs, no fonts,
//! no images, no fetches — the file makes **zero** network requests. And
//! deterministic: the output is a pure function of the analyzed graph and the
//! optional enrich document. The "generated" line attests a content
//! fingerprint (FNV-1a-64 over the embedded wire JSON), never a wall clock,
//! so two runs over the same tree are byte-identical.

use std::fmt::Write as _;

use crate::core::json::Json;
use crate::doctor::fnv1a64;
use crate::extract::{Extractor, HierarchyExtractor};
use crate::pipeline::Analysis;
use crate::verbalize::{verbalize, Options, View};
use crate::violations::ViolationsReport;

/// The one `Json::Null` the field accessor hands out for missing keys.
static NULL: Json = Json::Null;

/// Character budget for the embedded AI-companion digest: the verbalizer's
/// `all` view fits whole on small and mid-size repos, and past the budget
/// the document ends with the honest omission sentence.
const COMPANION_BUDGET: usize = 30_000;

/// Render the full dossier for an `analysis` of `dir`. `enrich_json`
/// is the verbatim text of a `trailtracker.enrich/v1` document, already
/// validated by the caller (the CLI checks the schema marker before calling).
/// In the default (airgap) build — no `enrich` feature — the argument is
/// ignored: the enriched-domains section, its payload embed, and its
/// renderer are compiled out, and the CLI has no way to produce the value.
pub fn dossier_html(analysis: &Analysis, dir: &str, enrich_json: Option<&str>) -> String {
    #[cfg(not(feature = "enrich"))]
    let _ = enrich_json;
    let graph = &analysis.graph;
    let base = repo_name(dir);
    let brief = crate::brief::brief_json(graph, dir);
    let hierarchy = HierarchyExtractor.extract(graph);
    let wire = crate::export::ontoloom_wire(&hierarchy, &format!("{base} (hierarchy)"));
    let violations = crate::violations::violations_report(graph);
    let companion = verbalize(
        analysis,
        &Options {
            view: View::All,
            budget: Some(COMPANION_BUDGET),
        },
    )
    .to_text();
    let fingerprint = format!("fnv1a64:{:016x}", fnv1a64(wire.as_bytes()));

    let mut out = String::with_capacity(256 * 1024);
    out.push_str("<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n");
    let _ = writeln!(out, "<title>{} — TrailTracker dossier</title>", esc(&base));
    out.push_str("<style>");
    out.push_str(CSS);
    out.push_str(CSS_COMPANION);
    #[cfg(feature = "enrich")]
    out.push_str(CSS_ENRICH);
    out.push_str("</style>\n</head>\n<body>\n");

    header_section(&base, dir, &brief, &mut out);
    out.push_str("<main>\n");
    brief_section(&brief, &mut out);
    map_section(&mut out);
    #[cfg(feature = "enrich")]
    enriched_section(enrich_json.is_some(), &mut out);
    violations_section(&violations, &mut out);
    companion_section(&companion, &mut out);
    out.push_str("</main>\n");
    footer_section(&fingerprint, &mut out);

    // Data payloads: the hierarchy wire JSON (and, in enrich builds, the
    // enrich document) as JSON script tags. `embed_json` escapes any `</` so
    // a payload can never terminate its own script element.
    let _ = writeln!(
        out,
        "<script type=\"application/json\" id=\"tt-graph\">{}</script>",
        embed_json(&wire)
    );
    #[cfg(feature = "enrich")]
    if let Some(enrich) = enrich_json {
        let _ = writeln!(
            out,
            "<script type=\"application/json\" id=\"tt-enrich\">{}</script>",
            embed_json(enrich.trim())
        );
    }
    out.push_str("<script>");
    out.push_str(JS);
    out.push_str(JS_COMPANION);
    #[cfg(feature = "enrich")]
    out.push_str(JS_ENRICH);
    out.push_str("</script>\n</body>\n</html>\n");
    out
}

/// The repo's display name: the last path segment of `dir` (same rule as
/// `export ontoloom`'s graph title).
pub fn repo_name(dir: &str) -> String {
    dir.trim_end_matches(['/', '\\'])
        .rsplit(['/', '\\'])
        .next()
        .filter(|s| !s.is_empty())
        .unwrap_or(dir)
        .to_string()
}

// ---------------------------------------------------------------------------
// Json field accessors (read-only walks over the brief document)
// ---------------------------------------------------------------------------

/// `v[key]`, or `Json::Null` when absent / not an object.
fn field<'a>(v: &'a Json, key: &str) -> &'a Json {
    match v {
        Json::Object(m) => m.get(key).unwrap_or(&NULL),
        _ => &NULL,
    }
}

/// The string inside a `Json::Str`, else `""`.
fn text(v: &Json) -> &str {
    match v {
        Json::Str(s) => s.as_str(),
        _ => "",
    }
}

/// A numeric value as `u64`, else 0.
fn num(v: &Json) -> u64 {
    match v {
        Json::U64(n) => *n,
        Json::I64(n) if *n >= 0 => *n as u64,
        _ => 0,
    }
}

/// The elements of a `Json::Array`, else the empty slice.
fn items(v: &Json) -> &[Json] {
    match v {
        Json::Array(a) => a.as_slice(),
        _ => &[],
    }
}

// ---------------------------------------------------------------------------
// Escaping
// ---------------------------------------------------------------------------

/// HTML-escape text content and attribute values.
fn esc(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            _ => out.push(c),
        }
    }
    out
}

/// Make a JSON document safe inside a `<script type="application/json">`
/// element: `</` becomes `<\/` (a legal JSON string escape), so no payload
/// substring can close the script tag early.
fn embed_json(s: &str) -> String {
    s.replace("</", "<\\/")
}

// ---------------------------------------------------------------------------
// Sections
// ---------------------------------------------------------------------------

fn header_section(base: &str, dir: &str, brief: &Json, out: &mut String) {
    let overview = field(brief, "overview");
    let langs: Vec<String> = items(field(overview, "languages"))
        .iter()
        .map(|l| esc(text(field(l, "language"))))
        .collect();
    out.push_str("<header class=\"hero\">\n");
    let _ = writeln!(out, "<p class=\"kicker\">TrailTracker dossier</p>");
    let _ = writeln!(out, "<h1>{}</h1>", esc(base));
    let _ = writeln!(
        out,
        "<p class=\"sub\">Deterministic code-intelligence report for <code>{}</code></p>",
        esc(dir)
    );
    out.push_str("<div class=\"tiles\">\n");
    for (label, value) in [
        ("files", num(field(overview, "files"))),
        ("lines", num(field(overview, "lines"))),
        ("graph nodes", num(field(overview, "nodes"))),
        ("graph edges", num(field(overview, "edges"))),
    ] {
        let _ = writeln!(
            out,
            "<div class=\"tile\"><b>{value}</b><span>{label}</span></div>"
        );
    }
    let _ = writeln!(
        out,
        "<div class=\"tile\"><b>{}</b><span>language(s)</span></div>",
        langs.len()
    );
    out.push_str("</div>\n");
    if !langs.is_empty() {
        let _ = writeln!(
            out,
            "<p class=\"langs\">{}</p>",
            langs
                .iter()
                .map(|l| format!("<span class=\"chip\">{l}</span>"))
                .collect::<Vec<_>>()
                .join(" ")
        );
    }
    out.push_str("</header>\n");
}

/// One `<tr>` from cell strings already escaped by the caller.
fn tr(cells: &[String], out: &mut String) {
    out.push_str("<tr>");
    for c in cells {
        let _ = write!(out, "<td>{c}</td>");
    }
    out.push_str("</tr>\n");
}

/// `name (kind, file)` label from a brief node descriptor, escaped.
fn descriptor_label(d: &Json) -> String {
    let name = esc(text(field(d, "name")));
    let kind = esc(text(field(d, "kind")));
    let file = esc(text(field(d, "file")));
    if file.is_empty() {
        format!("<code>{name}</code> <span class=\"dim\">({kind})</span>")
    } else {
        format!("<code>{name}</code> <span class=\"dim\">({kind}, {file})</span>")
    }
}

fn brief_section(brief: &Json, out: &mut String) {
    out.push_str("<section id=\"brief\">\n<h2>The brief</h2>\n");

    // Synthesis first: the one paragraph a reader should not scroll past.
    let synthesis = text(field(brief, "synthesis"));
    if !synthesis.is_empty() {
        let _ = writeln!(out, "<p class=\"synthesis\">{}</p>", esc(synthesis));
    }

    // Overview: languages table.
    out.push_str("<h3>Languages</h3>\n");
    let languages = items(field(field(brief, "overview"), "languages"));
    if languages.is_empty() {
        out.push_str("<p class=\"note\">none detected</p>\n");
    } else {
        out.push_str(
            "<table><thead><tr><th>language</th><th>files</th><th>lines</th><th>nodes</th></tr></thead><tbody>\n",
        );
        for l in languages {
            tr(
                &[
                    esc(text(field(l, "language"))),
                    num(field(l, "files")).to_string(),
                    num(field(l, "lines")).to_string(),
                    num(field(l, "nodes")).to_string(),
                ],
                out,
            );
        }
        out.push_str("</tbody></table>\n");
    }

    // Services / projects topology (only when the brief found any).
    let projects = field(brief, "projects");
    if !matches!(projects, Json::Null) {
        let _ = writeln!(
            out,
            "<h3>Services / projects</h3>\n<p>{} project(s) — the solution/service topology:</p>",
            num(field(projects, "count"))
        );
        let _ = writeln!(out, "<pre>{}</pre>", esc(text(field(projects, "topology"))));
    }

    // Architecture.
    let architecture = field(brief, "architecture");
    out.push_str("<h3>Domains (structural clustering)</h3>\n");
    let generated = num(field(architecture, "generated_files_excluded"));
    if generated > 0 {
        let _ = writeln!(
            out,
            "<p class=\"note\">{generated} generated file(s) (migrations, protos, designers) excluded from the signal below.</p>"
        );
    }
    let domains = items(field(architecture, "domains"));
    if domains.is_empty() {
        out.push_str("<p class=\"note\">none — no analyzable code clustered</p>\n");
    } else {
        out.push_str(
            "<table><thead><tr><th>domain</th><th>kind</th><th>files</th><th>symbols</th></tr></thead><tbody>\n",
        );
        for d in domains {
            let kind = text(field(d, "kind"));
            let reason = text(field(d, "reason"));
            let badge = if reason.is_empty() {
                format!("<span class=\"badge biz\">{}</span>", esc(kind))
            } else {
                format!(
                    "<span class=\"badge infra\">{} · {}</span>",
                    esc(kind),
                    esc(reason)
                )
            };
            tr(
                &[
                    format!("<b>{}</b>", esc(text(field(d, "name")))),
                    badge,
                    num(field(d, "files")).to_string(),
                    num(field(d, "symbols")).to_string(),
                ],
                out,
            );
        }
        out.push_str("</tbody></table>\n");
    }

    out.push_str("<h3>Largest units (by contained symbols)</h3>\n");
    let units = items(field(architecture, "largest_units"));
    if units.is_empty() {
        out.push_str("<p class=\"note\">none</p>\n");
    } else {
        out.push_str("<ul class=\"ranked\">\n");
        for u in units {
            let _ = writeln!(
                out,
                "<li>{} — {} symbol(s)</li>",
                descriptor_label(u),
                num(field(u, "symbols"))
            );
        }
        out.push_str("</ul>\n");
    }

    out.push_str("<h3>Module dependency map (cross-file references)</h3>\n");
    let deps = items(field(architecture, "module_dependencies"));
    if deps.is_empty() {
        out.push_str("<p class=\"note\">none — no cross-file dependencies resolved</p>\n");
    } else {
        out.push_str(
            "<table><thead><tr><th>from</th><th>to</th><th>references</th></tr></thead><tbody>\n",
        );
        for d in deps {
            tr(
                &[
                    format!("<code>{}</code>", esc(text(field(d, "from")))),
                    format!("<code>{}</code>", esc(text(field(d, "to")))),
                    num(field(d, "references")).to_string(),
                ],
                out,
            );
        }
        out.push_str("</tbody></table>\n");
        let omitted = num(field(architecture, "module_dependencies_omitted"));
        if omitted > 0 {
            let _ = writeln!(
                out,
                "<p class=\"note\">… and {omitted} more cross-file link(s)</p>"
            );
        }
    }

    // Entry points.
    let entry = field(brief, "entry_points");
    out.push_str("<h3>Entry points</h3>\n<h4>Likely mains</h4>\n");
    let mains = items(field(entry, "mains"));
    if mains.is_empty() {
        out.push_str("<p class=\"note\">none detected — likely a library</p>\n");
    } else {
        out.push_str("<ul class=\"ranked\">\n");
        for m in mains {
            let _ = writeln!(out, "<li>{}</li>", descriptor_label(m));
        }
        out.push_str("</ul>\n");
    }
    out.push_str("<h4>Public API surface (referenced from outside their file)</h4>\n");
    let api = items(field(entry, "public_api"));
    if api.is_empty() {
        out.push_str(
            "<p class=\"note\">none — no symbols are referenced across file boundaries</p>\n",
        );
    } else {
        out.push_str("<ul class=\"ranked\">\n");
        for a in api {
            let _ = writeln!(
                out,
                "<li>{} — {} external reference(s)</li>",
                descriptor_label(a),
                num(field(a, "external_references"))
            );
        }
        out.push_str("</ul>\n");
    }

    // Hotspots.
    let hotspots = field(brief, "hotspots");
    out.push_str("<h3>Hotspots</h3>\n<div class=\"cols\">\n");
    for (key, title) in [
        ("fan_in", "Highest fan-in (change ripples)"),
        ("fan_out", "Highest fan-out (complexity)"),
    ] {
        let _ = writeln!(out, "<div><h4>{title}</h4>");
        let list = items(field(hotspots, key));
        if list.is_empty() {
            out.push_str("<p class=\"note\">none</p>\n");
        } else {
            out.push_str("<ul class=\"ranked\">\n");
            for h in list {
                let _ = writeln!(
                    out,
                    "<li>{} — {}</li>",
                    descriptor_label(h),
                    num(field(h, "count"))
                );
            }
            out.push_str("</ul>\n");
        }
        out.push_str("</div>\n");
    }
    out.push_str("</div>\n");

    // Cycles.
    out.push_str("<h3>Dependency cycles</h3>\n");
    let cycles = items(field(brief, "cycles"));
    if cycles.is_empty() {
        out.push_str("<p class=\"ok\">none — the file dependency graph is acyclic</p>\n");
    } else {
        out.push_str("<ul class=\"ranked\">\n");
        for c in cycles {
            let files: Vec<String> = items(c)
                .iter()
                .map(|f| format!("<code>{}</code>", esc(text(f))))
                .collect();
            let _ = writeln!(
                out,
                "<li class=\"warn\">cycle of {} file(s): {}</li>",
                files.len(),
                files.join(" &harr; ")
            );
        }
        out.push_str("</ul>\n");
    }
    out.push_str("</section>\n");
}

/// The interactive code map: static markup only; the inline script hydrates
/// it from the embedded wire JSON.
fn map_section(out: &mut String) {
    out.push_str(r##"<section id="map">
<h2>Interactive code map</h2>
<p class="note">Click a circle to drill in: Domain &rarr; Unit &rarr; File &rarr; Symbol; click again to fold it away. Colored circles are business domains; muted circles are infrastructure groups (build, docs, generated). Drag to pan, scroll to zoom.</p>
<div class="cm-bar">
<div id="cm-layout" role="group" aria-label="layout">
<button type="button" data-mode="web" aria-pressed="true">Web</button>
<button type="button" data-mode="tree" aria-pressed="false">Tree</button>
</div>
<button type="button" id="cm-deps" aria-pressed="true">Coupling</button>
<button type="button" id="cm-fit">Fit</button>
<span class="cm-searchbox"><input id="cm-search" type="search" placeholder="search files and symbols" aria-label="search the code map"><span id="cm-match-count" hidden></span></span>
<span id="cm-visible" class="dim"></span>
</div>
<div class="cm-body">
<div id="cm-wrap"><svg id="cm-svg" role="tree" aria-label="code map"><g id="cm-viewport"></g></svg></div>
<aside id="cm-detail" class="empty"><div class="empty-hint">click a node to expand it and inspect it here</div></aside>
</div>
<div class="cm-foot">
<div id="cm-stats"></div>
<div class="cm-legend"><span><i class="sw" style="background:#5b8def"></i>domain</span><span><i class="sw" style="background:#6b7793"></i>infrastructure</span><span><i class="sw" style="background:var(--cm-unit)"></i>unit</span><span><i class="sw" style="background:var(--cm-file)"></i>file</span><span><i class="sw" style="background:var(--cm-type)"></i>type</span><span><i class="sw" style="background:var(--cm-func)"></i>function</span><span><i class="sw" style="background:var(--cm-const)"></i>const</span></div>
</div>
</section>
"##);
}

/// Enrich builds only: the enriched-domains section (cards + attestation, or
/// the how-to-generate pointer note). The default/airgap build has neither
/// the section nor any string mentioning the naming pass.
#[cfg(feature = "enrich")]
fn enriched_section(has_enrich: bool, out: &mut String) {
    out.push_str("<section id=\"enriched\">\n<h2>Enriched domains</h2>\n");
    if has_enrich {
        out.push_str(
            "<p class=\"note\">Cluster membership and counts below are deterministic \
             (identical to the structural clustering); names, descriptions, and \
             responsibilities are LLM-attested.</p>\n\
             <div id=\"enrich-cards\" class=\"cards\"></div>\n\
             <div id=\"enrich-attestation\" class=\"attestation\"></div>\n",
        );
    } else {
        out.push_str(
            "<p class=\"note\">No enrichment supplied — the domains above carry structural \
             names only. Run <code>trailtracker enrich-domains DIR --json &gt; enrich.json</code> \
             and rebuild with <code>--enrich enrich.json</code> for semantic names, \
             descriptions, and responsibilities (LLM-attested).</p>\n",
        );
    }
    out.push_str("</section>\n");
}

/// A layer-pair group collapses behind `<details>` above this many rows.
const VIOLATION_GROUP_FOLD: usize = 20;

/// The FULL layer-violations table at unit grain (same data as
/// `trailtracker violations`): grouped by layer pair (worst group first),
/// each group a table of from-unit → to-unit rows ranked worst-first with
/// file-level example evidence. Groups longer than [`VIOLATION_GROUP_FOLD`]
/// rows fold into a `<details>` block so a 100-pair report stays scannable.
fn violations_section(report: &ViolationsReport, out: &mut String) {
    out.push_str("<section id=\"violations\">\n<h2>Layer violations</h2>\n");
    if report.violations.is_empty() {
        out.push_str(
            "<p class=\"ok\">none — every layer dependency points inward \
             (Presentation &rarr; Infrastructure &rarr; Application &rarr; Domain).</p>\n",
        );
        out.push_str("</section>\n");
        return;
    }
    let groups = report.layer_pairs();
    let _ = writeln!(
        out,
        "<p class=\"note\">Dependencies must point inward (Domain &lt; Application &lt; \
         Infrastructure &lt; Presentation; Test and Shared are exempt). Every violating \
         unit pair is listed below, worst first, with file-level evidence — \
         <b>{}</b> violating reference(s) across <b>{}</b> unit pair(s) in <b>{}</b> \
         layer pair(s).</p>",
        report.total_edges,
        report.violations.len(),
        groups.len()
    );
    for g in &groups {
        let rows: Vec<_> = report
            .violations
            .iter()
            .filter(|v| v.from_layer == g.from_layer && v.to_layer == g.to_layer)
            .collect();
        let heading = format!(
            "<b>{}</b> &rarr; <b>{}</b> <span class=\"dim\">— {} reference(s), {} unit \
             pair(s)</span>",
            esc(&g.from_layer),
            esc(&g.to_layer),
            g.edges,
            g.unit_pairs
        );
        let folded = rows.len() > VIOLATION_GROUP_FOLD;
        if folded {
            let _ = writeln!(
                out,
                "<details class=\"vgroup\"><summary>{heading}</summary>"
            );
        } else {
            let _ = writeln!(out, "<h3 class=\"vgroup-h\">{heading}</h3>");
        }
        out.push_str(
            "<table><thead><tr><th>from unit</th><th>to unit</th><th>references</th>\
             <th>example evidence</th></tr></thead><tbody>\n",
        );
        for v in &rows {
            let examples = v
                .examples
                .iter()
                .take(2)
                .map(|e| format!("<code>{}</code>", esc(e)))
                .collect::<Vec<_>>()
                .join("<br>");
            tr(
                &[
                    format!("<code>{}</code>", esc(&v.from_unit)),
                    format!("<code>{}</code>", esc(&v.to_unit)),
                    v.count.to_string(),
                    examples,
                ],
                out,
            );
        }
        out.push_str("</tbody></table>\n");
        if folded {
            out.push_str("</details>\n");
        }
    }
    out.push_str("</section>\n");
}

/// The "For your AI assistant" section (N6): the verbalizer's `all` view —
/// glossaried handles, standalone sentences, denominators — embedded once,
/// with a one-click copy button (clipboard API + `execCommand` fallback,
/// copied-check feedback) and a collapsible preview. The coaching line
/// teaches what to ask.
fn companion_section(companion: &str, out: &mut String) {
    out.push_str("<section id=\"companion\">\n<h2>For your AI assistant</h2>\n");
    out.push_str(
        "<p class=\"note\">Copy the digest below into any AI chat and ask about the \
         codebase — every line is a standalone, quotable fact derived deterministically \
         from the code graph (handles like <code>D1</code>/<code>F1</code> are defined \
         at the top of the digest). Try: <i>&#8220;Where should I start reading?&#8221;</i>, \
         <i>&#8220;What depends on the top hotspot?&#8221;</i>, \
         <i>&#8220;Which units break the layering?&#8221;</i></p>\n",
    );
    out.push_str(
        "<p><button id=\"companion-copy\" type=\"button\">Copy digest</button> \
         <span id=\"companion-status\" class=\"dim\" role=\"status\"></span></p>\n",
    );
    let _ = writeln!(
        out,
        "<details class=\"companion-preview\"><summary>Preview the digest \
         ({} lines)</summary><pre id=\"companion-text\">{}</pre></details>",
        companion.lines().count(),
        esc(companion)
    );
    out.push_str("</section>\n");
}

fn footer_section(fingerprint: &str, out: &mut String) {
    out.push_str("<footer>\n");
    let _ = writeln!(
        out,
        "<p>Generated by trailtracker v{} — analysis fingerprint <code>{}</code> over the embedded hierarchy graph.</p>",
        env!("CARGO_PKG_VERSION"),
        esc(fingerprint)
    );
    out.push_str(
        "<p>Deterministic: identical input trees produce byte-identical dossiers. \
         Airgap-grade: this file is fully self-contained — inline styles and scripts \
         only, no external resources, zero network requests.</p>\n</footer>\n",
    );
}

// ---------------------------------------------------------------------------
// Inline assets
// ---------------------------------------------------------------------------

/// The dossier stylesheet. No external fonts, no images, no imports.
const CSS: &str = r##"
:root{
  --bg:#0e1116; --panel:#141a23; --panel2:#1b2230; --line:#283242;
  --text:#dce3ee; --text-dim:#8b96a8; --text-faint:#5d6879;
  --accent:#5b8def; --ok:#7cc4a4; --warn:#e0b15f; --bad:#e07a7a;
  --cm-unit:#8fa3c0; --cm-file:#c9d4e6; --cm-type:#b98bd9; --cm-func:#7cc4a4; --cm-const:#e0b15f;
}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--text);
  font:15px/1.55 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Helvetica,Arial,sans-serif}
code,pre{font-family:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;font-size:.92em}
main,header.hero,footer{max-width:1180px;margin:0 auto;padding:0 24px}
header.hero{padding-top:44px;padding-bottom:8px}
.kicker{color:var(--accent);text-transform:uppercase;letter-spacing:.14em;font-size:12px;margin:0 0 4px}
h1{margin:0;font-size:34px;letter-spacing:-.02em}
.sub{color:var(--text-dim);margin:6px 0 18px}
.tiles{display:flex;flex-wrap:wrap;gap:12px}
.tile{background:var(--panel);border:1px solid var(--line);border-radius:10px;padding:12px 18px;min-width:110px}
.tile b{display:block;font-size:22px}
.tile span{color:var(--text-dim);font-size:12px}
.langs{margin:14px 0 0}
.chip{display:inline-block;background:var(--panel2);border:1px solid var(--line);border-radius:999px;
  padding:1px 10px;font-size:12px;color:var(--text-dim);margin:2px 2px 2px 0}
section{background:var(--panel);border:1px solid var(--line);border-radius:12px;
  padding:22px 26px;margin:22px 0}
h2{margin:0 0 12px;font-size:22px;border-bottom:2px solid var(--accent);
  padding-bottom:8px;letter-spacing:-.01em}
h3{margin:22px 0 8px;font-size:16px;color:var(--text)}
h4{margin:14px 0 6px;font-size:13px;color:var(--text-dim);text-transform:uppercase;letter-spacing:.06em}
table{border-collapse:collapse;width:100%;margin:6px 0 4px}
th,td{text-align:left;padding:6px 12px 6px 0;border-bottom:1px solid var(--line);vertical-align:top}
th{color:var(--text-dim);font-size:12px;text-transform:uppercase;letter-spacing:.05em;font-weight:600}
tr:last-child td{border-bottom:none}
ul.ranked{margin:6px 0;padding-left:20px}
ul.ranked li{margin:3px 0}
.dim{color:var(--text-dim)}
.note{color:var(--text-dim);font-size:13.5px}
.ok{color:var(--ok)}
.warn{color:var(--warn)}
li.warn{color:var(--warn)}
.synthesis{background:var(--panel2);border-left:3px solid var(--accent);border-radius:0 8px 8px 0;
  padding:12px 16px;font-size:15.5px}
.badge{display:inline-block;border-radius:6px;padding:1px 8px;font-size:12px}
.badge.biz{background:rgba(91,141,239,.15);color:var(--accent)}
.badge.infra{background:rgba(107,119,147,.18);color:var(--text-dim)}
pre{background:var(--panel2);border:1px solid var(--line);border-radius:8px;
  padding:12px;overflow-x:auto;color:var(--text-dim)}
.cols{display:grid;grid-template-columns:repeat(auto-fit,minmax(320px,1fr));gap:0 28px}
footer{color:var(--text-faint);font-size:12.5px;padding-bottom:40px}
footer p{margin:6px 0}
footer code{color:var(--text-dim)}
/* --- code map --- */
.cm-bar{display:flex;flex-wrap:wrap;align-items:center;gap:8px;margin:12px 0}
.cm-bar button{background:var(--panel2);color:var(--text-dim);border:1px solid var(--line);
  border-radius:7px;padding:4px 12px;font-size:13px;cursor:pointer}
.cm-bar button[aria-pressed="true"]{background:var(--accent);border-color:var(--accent);color:#fff}
#cm-layout{display:inline-flex;gap:4px}
.cm-searchbox{position:relative;margin-left:auto}
#cm-search{background:var(--panel2);border:1px solid var(--line);border-radius:7px;
  color:var(--text);padding:4px 10px;font-size:13px;width:220px}
#cm-match-count{position:absolute;right:8px;top:5px;font-size:11px;color:var(--ok)}
#cm-match-count.none{color:var(--bad)}
.cm-body{display:flex;gap:14px;align-items:stretch}
#cm-wrap{flex:1;min-width:0;background:var(--bg);border:1px solid var(--line);border-radius:10px;
  height:560px;cursor:grab;overflow:hidden}
#cm-wrap.grabbing{cursor:grabbing}
#cm-svg{width:100%;height:100%;display:block}
#cm-detail{width:280px;flex:none;background:var(--panel2);border:1px solid var(--line);
  border-radius:10px;padding:14px;overflow-y:auto;max-height:560px;font-size:13px}
#cm-detail.empty{display:flex;align-items:center;justify-content:center;color:var(--text-faint)}
#cm-detail h3{margin:2px 0 4px;font-size:15px}
#cm-detail .kicker{margin:0;font-size:11px}
#cm-detail .path{color:var(--text-dim);word-break:break-all;font-family:ui-monospace,Menlo,monospace;font-size:11.5px}
.metric-row{display:flex;gap:14px;margin:10px 0}
.metric b{display:block;font-size:16px}
.metric span{color:var(--text-dim);font-size:11px}
.kindbar{display:flex;height:8px;border-radius:4px;overflow:hidden;margin:4px 0}
.kindbar i{display:block}
.kindlegend{display:flex;gap:10px;color:var(--text-dim);font-size:11px}
.facts .fact{display:flex;justify-content:space-between;border-bottom:1px solid var(--line);padding:3px 0}
.facts .fact span{color:var(--text-dim)}
.chips{margin:4px 0}
.chip.dep em{color:var(--text-faint);font-style:normal}
.sw{display:inline-block;width:10px;height:10px;border-radius:50%;margin-right:5px;vertical-align:-1px}
.cm-foot{display:flex;flex-wrap:wrap;justify-content:space-between;align-items:center;margin-top:10px;gap:8px}
#cm-stats{display:flex;gap:18px}
#cm-stats .stat b{margin-right:5px}
#cm-stats .stat span{color:var(--text-dim);font-size:12px}
.cm-legend{display:flex;flex-wrap:wrap;gap:12px;color:var(--text-dim);font-size:12px}
.cm-node{cursor:pointer;outline:none}
.cm-node .lbl{fill:var(--text);font-family:ui-monospace,Menlo,monospace}
.cm-node.dim{opacity:.18}
.cm-node.match .dot{stroke-width:2.6}
.cm-node:focus-visible .dot{stroke:#fff}
.cm-node .hit{fill:transparent}
.selring{fill:none;stroke:#fff;stroke-width:1.2;opacity:.7}
.cm-edge{fill:none;stroke:var(--text-faint);stroke-width:1;opacity:.5}
.cm-dep{fill:none;stroke:var(--warn);stroke-width:1.1;stroke-dasharray:5 4;opacity:.75}
.cm-dep-tip{fill:var(--warn)}
.cm-dep-count{fill:var(--warn);font-size:10px;font-family:ui-monospace,Menlo,monospace}
/* web layout: containment fades to faint links; coupling is the loud layer */
.cm-weblink{stroke:var(--line);stroke-width:1;opacity:.8}
.cm-depweb{stroke:var(--warn);opacity:.55}
/* label LOD: below the zoom where a tier's text can resolve it fades out
   instead of smearing (web-drawn nodes only — tree labels are column-guarded) */
.cm-w-sym .lbl,.cm-w-file .lbl,.cm-w-unit .lbl{transition:opacity .15s linear}
#cm-svg[data-z="far"] .cm-w-sym .lbl,#cm-svg[data-z="far"] .cm-w-file .lbl,
#cm-svg[data-z="far"] .cm-w-unit .lbl{opacity:0}
#cm-svg[data-z="mid"] .cm-w-sym .lbl{opacity:0}
#cm-svg[data-z="mid"] .cm-w-file .lbl{opacity:.4}
#cm-svg[data-z="near"] .cm-w-sym .lbl{opacity:.5}
/* violations: layer-pair groups */
.vgroup-h{margin:20px 0 4px}
details.vgroup{margin:16px 0 8px}
details.vgroup summary{cursor:pointer;font-size:16px;margin:2px 0 6px}
details.vgroup summary:hover{color:var(--accent)}
/* --- info cards --- */
.cards{display:grid;grid-template-columns:repeat(auto-fill,minmax(320px,1fr));gap:14px;margin:12px 0}
.card{background:var(--panel2);border:1px solid var(--line);border-radius:10px;padding:14px 16px}
.card header{display:flex;flex-wrap:wrap;align-items:baseline;gap:8px}
.card h3{margin:0;font-size:16px}
.card .counts{color:var(--text-dim);font-size:12.5px;margin:6px 0}
.card ul{margin:6px 0;padding-left:18px}
.card li{margin:2px 0;font-size:13.5px}
@media (max-width:860px){.cm-body{flex-direction:column}#cm-detail{width:auto;max-height:300px}}
@media print{body{background:#fff;color:#111}section{border-color:#ccc}}
"##;

/// Styles for the AI-companion section (always present).
const CSS_COMPANION: &str = r##"
#companion pre{max-height:420px;overflow:auto;background:var(--panel);border:1px solid var(--line);
  border-radius:6px;padding:12px;font-size:12px;line-height:1.55;white-space:pre-wrap}
#companion button{background:var(--accent);color:#fff;border:0;border-radius:6px;
  padding:8px 14px;font-size:14px;cursor:pointer;font:inherit}
#companion button:hover{filter:brightness(1.12)}
#companion .companion-preview summary{cursor:pointer;color:var(--text-dim)}
#companion #companion-status{margin-left:8px}
"##;

/// Enrich builds only: the single enrich-specific style rule (the attestation
/// block under each enriched-domain card). Kept out of the always-emitted
/// [`CSS`] so the default/airgap dossier carries no attestation styling and no
/// string mentioning the naming pass.
#[cfg(feature = "enrich")]
const CSS_ENRICH: &str = r##".attestation{border-top:1px solid var(--line);margin-top:8px;padding-top:10px;
  color:var(--text-dim);font-size:12.5px}
"##;

/// The dossier script: the code-map drill-down (an inline adaptation of
/// Ontoloom's `codemap.js`, tree mode — same project, same owner) plus the
/// enriched-domains renderer. Vanilla JS, no dependencies, no network.
const JS: &str = r##"
"use strict";
(function () {
  var gEl = document.getElementById("tt-graph");
  if (!gEl) return;
  var data = JSON.parse(gEl.textContent);
  var NODES = data.nodes || [];
  var RELS = data.relationships || [];

  var DOMAIN_HUES = ["#5b8def","#7cc4a4","#b98bd9","#e0b15f","#67c0d0","#d97aa6","#8fb069","#d98b6a","#9aa6ff","#c9b458"];
  var INFRA_COLOR = "#6b7793";
  var KIND_COLOR = { T: "var(--cm-type)", F: "var(--cm-func)", C: "var(--cm-const)" };
  var KIND_LABEL = { T: "type", F: "function", C: "const" };
  var KICK = { root: "repository", domain: "domain", unit: "unit", file: "file", sym: "symbol" };
  /* Tree (alternate view): columns are DYNAMIC — sized per render from the
     longest visible label per depth, so gaps grow with the names instead of
     colliding. ROW is the vertical rhythm. */
  var COL = [0, 240, 480, 720, 960];
  var ROW = 22;
  /* Web (default view): a deterministic force layout. Same recipe as
     Ontoloom's codemap (same project, same owner): hash-seeded starts,
     fixed tick budget, grid-bucketed repulsion, containment + coupling
     springs, hub gravity — then a min-separation pass over DOTS and a
     second pass over LABEL BOXES, so no two visible labels overlap at any
     drill depth. No randomness anywhere: same graph, same expansion state,
     same picture. */
  var WEB = {
    cutoff: 240, cutoffBig: 120, repK: 28,
    q: { root: 30, domain: 46, unit: 14, file: 7, sym: 3 },
    rest: [0, 500, 100, 55, 26],
    kc: [0, 0.03, 0.08, 0.1, 0.12],
    depRest: 340, depK: 0.004,
    hubG: 0.05, centerG: 0.008,
    fmax: 40, step: 30,
    ticksFull: 300, ticksBig: 120, ticksIncr: 90, bigN: 1200,
    sepPad: 12, sepPasses: 96, labelPasses: 128, labelPad: 2
  };

  var wrap = document.getElementById("cm-wrap");
  var svg = document.getElementById("cm-svg");
  var vp = document.getElementById("cm-viewport");
  var detail = document.getElementById("cm-detail");
  var statsEl = document.getElementById("cm-stats");
  var visibleEl = document.getElementById("cm-visible");
  var searchInput = document.getElementById("cm-search");
  var matchCountEl = document.getElementById("cm-match-count");
  var EMPTY_DETAIL = '<div class="empty-hint">click a node to expand it and inspect it here</div>';

  var root = null, byId = {}, realById = {}, deps = {};
  var matchSet = null, selectedId = null, showDeps = true;
  var T = { x: 60, y: 40, k: 1 };
  /* Navigation is DRILL-ONLY: expansion happens by clicking nodes; there are
     no bulk expand-to-level buttons. Web is the default face; the tidy tree
     stays as the alternate. */
  var layoutMode = "web";
  var webPos = {};  /* tree id -> {x, y}: settled positions, kept across expands */
  var webSig = "";  /* visible-set signature the sim last ran for */

  function prop(n, key) {
    return n && n.properties && typeof n.properties === "object" ? n.properties[key] : undefined;
  }
  function level(n) { return prop(n, "level"); }
  function esc(s) {
    return String(s).replace(/[<>&]/g, function (c) {
      return { "<": "&lt;", ">": "&gt;", "&": "&amp;" }[c];
    });
  }
  function truncate(s, n) { return s.length > n ? s.slice(0, n - 1) + "…" : s; }

  function symbolKind(n) {
    var k = String(prop(n, "symbol_kind") || "");
    if (/^func/i.test(k)) return "F";
    if (/^const/i.test(k)) return "C";
    if (/^type/i.test(k)) return "T";
    var labels = Array.isArray(n.labels) ? n.labels : [];
    if (labels.indexOf("Function") >= 0) return "F";
    if (labels.indexOf("Constant") >= 0) return "C";
    if (labels.indexOf("Type") >= 0) return "T";
    return "F";
  }

  /* Tree building: Domain -> Unit -> File -> Symbol from CONTAINS edges.
     A file has two CONTAINS parents (domain + unit); the drill path groups
     each domain's files by their unit. */
  function buildTree(name, nodes, rels) {
    realById = {}; deps = {}; byId = {};
    var i, n;
    for (i = 0; i < nodes.length; i++) realById[nodes[i].id] = nodes[i];

    var kidsOf = {}, parentsOf = {};
    for (i = 0; i < rels.length; i++) {
      var r = rels[i];
      if (r.type === "CONTAINS") {
        (kidsOf[r.from] = kidsOf[r.from] || []).push(r.to);
        (parentsOf[r.to] = parentsOf[r.to] || []).push(r.from);
      } else if (r.type === "DEPENDS_ON") {
        (deps[r.from] = deps[r.from] || []).push({ id: r.to, count: prop(r, "count") });
      }
    }
    var unitByName = {};
    for (i = 0; i < nodes.length; i++) {
      n = nodes[i];
      if (level(n) === "unit") unitByName[n.caption || prop(n, "unit") || n.id] = n;
    }

    var seq = 0;
    function tnode(type, label, real, depth, extra) {
      var t = { id: "t" + seq++, type: type, name: label, real: real || null,
                depth: depth, children: [], _collapsed: false };
      if (extra) for (var k in extra) t[k] = extra[k];
      byId[t.id] = t;
      return t;
    }

    root = tnode("root", name || "Code map", null, 0);
    var domTree = {}, hueIdx = 0;
    for (i = 0; i < nodes.length; i++) {
      n = nodes[i];
      if (level(n) !== "domain") continue;
      var infra = prop(n, "kind") === "infrastructure";
      var t = tnode("domain", n.caption || n.id, n, 1, {
        color: infra ? INFRA_COLOR : DOMAIN_HUES[hueIdx++ % DOMAIN_HUES.length],
        infra: infra
      });
      domTree[n.id] = t;
      root.children.push(t);
    }
    var ungrouped = null;
    var unitTree = {};
    for (i = 0; i < nodes.length; i++) {
      var f = nodes[i];
      if (level(f) !== "file") continue;
      var parents = (parentsOf[f.id] || []).map(function (p) { return realById[p]; });
      var domReal = null, unitReal = null, j;
      for (j = 0; j < parents.length; j++) {
        if (parents[j] && level(parents[j]) === "domain") domReal = parents[j];
        if (parents[j] && level(parents[j]) === "unit") unitReal = parents[j];
      }
      var domT = domReal ? domTree[domReal.id] : null;
      if (!domT) {
        if (!ungrouped) {
          ungrouped = tnode("domain", "(ungrouped)", null, 1, { color: INFRA_COLOR, infra: true });
          root.children.push(ungrouped);
        }
        domT = ungrouped;
      }
      if (!unitReal) unitReal = unitByName[prop(f, "unit")] || null;
      var unitName = (unitReal && unitReal.caption) || prop(f, "unit") || "(no unit)";
      var key = domT.id + " " + unitName;
      var unitT = unitTree[key];
      if (!unitT) {
        unitT = tnode("unit", unitName, unitReal, 2);
        unitTree[key] = unitT;
        domT.children.push(unitT);
      }
      var fileT = tnode("file", f.caption || f.id, f, 3, { path: String(prop(f, "path") || "") });
      unitT.children.push(fileT);
      var kids = kidsOf[f.id] || [];
      for (j = 0; j < kids.length; j++) {
        var s = realById[kids[j]];
        if (!s || level(s) !== "symbol") continue;
        fileT.children.push(tnode("sym", s.caption || s.id, s, 4, { kind: symbolKind(s) }));
      }
      fileT.children.sort(function (a, b) {
        return (Number(prop(a.real, "line")) || 0) - (Number(prop(b.real, "line")) || 0) ||
          a.name.localeCompare(b.name);
      });
    }
    for (i = 0; i < root.children.length; i++) {
      var d = root.children[i];
      d.children.sort(function (a, b) { return a.name.localeCompare(b.name); });
      for (var u = 0; u < d.children.length; u++) {
        d.children[u].children.sort(function (a, b) { return a.name.localeCompare(b.name); });
      }
    }
    root.children.sort(function (a, b) {
      return ((a.infra ? 1 : 0) - (b.infra ? 1 : 0)) ||
        (a.infra && b.infra ? a.name.localeCompare(b.name) : 0);
    });
    rollup(root);
  }

  function rollup(n) {
    n.mix = { T: 0, F: 0, C: 0 };
    n.nunits = n.type === "unit" ? 1 : 0;
    n.nfiles = n.type === "file" ? 1 : 0;
    n.nsyms = 0;
    if (n.type === "sym") { n.nsyms = 1; n.mix[n.kind] = 1; return; }
    for (var i = 0; i < n.children.length; i++) {
      var c = n.children[i];
      rollup(c);
      n.nunits += c.nunits; n.nfiles += c.nfiles; n.nsyms += c.nsyms;
      n.mix.T += c.mix.T; n.mix.F += c.mix.F; n.mix.C += c.mix.C;
    }
  }

  function setDepth(d) {
    (function walk(n) {
      if (n.children.length) {
        n._collapsed = n.depth >= d || (n.type === "domain" && n.infra === true);
        n.children.forEach(walk);
      }
    })(root);
  }

  /* Tree columns, resized per render: each gap fits the longest label that
     must live in it (left labels of the deeper column's expanded parents,
     right labels of the shallower column's leaves), so text never reaches
     the neighboring column's nodes. */
  function treeCols() {
    var need = [0, 0, 0, 0, 0];
    (function walk(n) {
      var d = Math.min(n.depth, 4);
      var w = Math.min(n.name.length, 34) * 7 + 80;
      if (w > need[d]) need[d] = w;
      if (!n._collapsed) for (var i = 0; i < n.children.length; i++) walk(n.children[i]);
    })(root);
    var col = [0];
    for (var d = 1; d < 5; d++) {
      col[d] = col[d - 1] + Math.max(220, need[d - 1], need[d]);
    }
    return col;
  }

  var yCursor = 0;
  function layout(n) {
    COL = treeCols();
    yCursor = 0;
    (function place(node) {
      node.x = COL[Math.min(node.depth, COL.length - 1)];
      var kids = node._collapsed || !node.children.length ? [] : node.children;
      if (!kids.length) { node.y = yCursor; yCursor += ROW; }
      else { kids.forEach(place); node.y = (kids[0].y + kids[kids.length - 1].y) / 2; }
    })(n);
  }

  function nodeColor(n) {
    if (n.type === "root") return "var(--accent)";
    if (n.type === "domain") return n.color;
    if (n.type === "unit") return "var(--cm-unit)";
    if (n.type === "file") return "var(--cm-file)";
    return KIND_COLOR[n.kind] || "var(--text-dim)";
  }

  /* One dot radius per node type — shared by both renderers and the web
     collision passes, so "overlap" means the same thing everywhere. */
  function nodeR(n) {
    return n.type === "root" ? 7 : n.type === "domain" ? 6 : n.type === "unit" ? 5 : n.type === "sym" ? 3 : 4;
  }

  function applyT() {
    vp.setAttribute("transform", "translate(" + T.x + "," + T.y + ") scale(" + T.k + ")");
    /* Label LOD (web only, CSS keys on cm-w-* classes): each tier fades out
       below the zoom where its text can actually resolve, instead of piling
       into a smear. Priority: domains always read, units from mid zoom,
       files near, symbols close. */
    if (svg.dataset) {
      svg.dataset.z = T.k < 0.45 ? "far" : T.k < 0.7 ? "mid" : T.k < 1.1 ? "near" : "close";
    }
  }

  /* ==== web layout: a deterministic force sim over the visible slice ==== */

  /* FNV-1a — the deterministic seed for every node's start position. */
  function hash32(s) {
    var h = 0x811c9dc5;
    for (var i = 0; i < s.length; i++) {
      h ^= s.charCodeAt(i);
      h = (h * 0x01000193) >>> 0;
    }
    return h >>> 0;
  }

  /* Round for the SVG string — compact markup, exact determinism. */
  function r2(v) { return Math.round(v * 100) / 100; }

  /* The web label: right of the dot, truncated so dense clusters stay
     legible. Width estimate is shared by the draw and the label-collision
     pass, so "overlap" is judged on exactly what gets painted. */
  function webLabel(n) { return truncate(n.name, 26); }
  function webLabelW(n) {
    var w = webLabel(n).length * 7 + 30;
    /* A collapsed parent paints a `·N` symbol-count suffix — the collision
       pass must budget for the same box the renderer draws. */
    if (n.children.length && n._collapsed && n.nsyms) {
      w += (String(n.nsyms).length + 2) * 7;
    }
    return w;
  }

  /* Visible slice + containment edges + each node's domain-hub index. */
  function collectWeb() {
    var shown = [], edges = [], hubOf = [];
    (function walk(n, parent, hub) {
      var i = shown.length;
      shown.push(n);
      hubOf.push(n.depth === 1 ? i : hub);
      if (parent) edges.push([parent, n]);
      var kids = n._collapsed || !n.children.length ? [] : n.children;
      var myHub = n.depth === 1 ? i : hub;
      for (var k = 0; k < kids.length; k++) walk(kids[k], n, myHub);
    })(root, null, -1);
    return { shown: shown, edges: edges, hubOf: hubOf };
  }

  /* Seed any node that has never been placed: root at the origin, domains
     ringing it, children scattered deterministically beside their parent —
     an expand grows the web outward from where you clicked. */
  function seedWeb(shown, edges) {
    var parentOf = {}, i;
    for (i = 0; i < edges.length; i++) parentOf[edges[i][1].id] = edges[i][0];
    var fresh = 0;
    for (i = 0; i < shown.length; i++) {
      var n = shown[i];
      if (webPos[n.id]) continue;
      fresh++;
      var h = hash32(n.name + " " + n.id);
      var ang = (h % 3600) * (Math.PI / 1800);
      if (n.depth === 0) {
        webPos[n.id] = { x: 0, y: 0 };
      } else if (n.depth === 1) {
        var rad = 320 + ((h >>> 12) % 120);
        webPos[n.id] = { x: Math.cos(ang) * rad, y: Math.sin(ang) * rad };
      } else {
        var par = parentOf[n.id];
        var p = (par && webPos[par.id]) || { x: 0, y: 0 };
        var rr = 18 + ((h >>> 12) % 30);
        webPos[n.id] = { x: p.x + Math.cos(ang) * rr, y: p.y + Math.sin(ang) * rr };
      }
    }
    return fresh;
  }

  /* Springs: containment (short rest — children hug their parent) plus
     DEPENDS_ON (long rest, strength scaled by ln(count)). */
  function buildSprings(shown, edges) {
    var idx = {}, i;
    for (i = 0; i < shown.length; i++) idx[shown[i].id] = i;
    var springs = [];
    for (i = 0; i < edges.length; i++) {
      var d = Math.min(edges[i][1].depth, WEB.rest.length - 1);
      springs.push({ a: idx[edges[i][0].id], b: idx[edges[i][1].id], len: WEB.rest[d], k: WEB.kc[d] });
    }
    var wireToTree = {};
    for (i = 0; i < shown.length; i++) {
      var w = shown[i];
      if (w.real && !(w.real.id in wireToTree)) wireToTree[w.real.id] = w;
    }
    for (var fromWire in deps) {
      var a = wireToTree[fromWire];
      if (!a) continue;
      for (var di = 0; di < deps[fromWire].length; di++) {
        var b = wireToTree[deps[fromWire][di].id];
        if (!b || a === b) continue;
        var k = WEB.depK * (1 + Math.log(1 + (Number(deps[fromWire][di].count) || 1)));
        springs.push({ a: idx[a.id], b: idx[b.id], len: WEB.depRest, k: k });
      }
    }
    return springs;
  }

  /* One force tick over parallel position arrays. Deterministic: fixed
     iteration order, no randomness, pure function of the previous state. */
  function webTick(px, py, qv, springs, hubOf, cutoff, alpha) {
    var n = px.length, i, j;
    var fx = new Float64Array(n);
    var fy = new Float64Array(n);
    var cut2 = cutoff * cutoff;
    /* Repulsion, grid-bucketed: only the 3x3 cell neighborhood is scanned. */
    var grid = {}, cx = new Int32Array(n), cy = new Int32Array(n);
    for (i = 0; i < n; i++) {
      cx[i] = Math.floor(px[i] / cutoff);
      cy[i] = Math.floor(py[i] / cutoff);
      var key = cx[i] + ":" + cy[i];
      (grid[key] = grid[key] || []).push(i);
    }
    for (i = 0; i < n; i++) {
      for (var gx = cx[i] - 1; gx <= cx[i] + 1; gx++) {
        for (var gy = cy[i] - 1; gy <= cy[i] + 1; gy++) {
          var cell = grid[gx + ":" + gy];
          if (!cell) continue;
          for (var ci = 0; ci < cell.length; ci++) {
            j = cell[ci];
            if (j <= i) continue;
            var dx = px[i] - px[j], dy = py[i] - py[j];
            var d2 = dx * dx + dy * dy;
            if (d2 > cut2) continue;
            if (d2 < 1e-4) {
              dx = ((i * 31 + j * 7) % 13 - 6) * 0.17 || 0.61;
              dy = ((i * 17 + j * 11) % 13 - 6) * 0.17 || -0.43;
              d2 = dx * dx + dy * dy;
            }
            var f = WEB.repK * qv[i] * qv[j] / d2;
            if (f > WEB.fmax) f = WEB.fmax;
            var dd = Math.sqrt(d2), ux = dx / dd, uy = dy / dd;
            fx[i] += ux * f; fy[i] += uy * f;
            fx[j] -= ux * f; fy[j] -= uy * f;
          }
        }
      }
    }
    for (i = 0; i < springs.length; i++) {
      var s = springs[i];
      var sdx = px[s.b] - px[s.a], sdy = py[s.b] - py[s.a];
      var sd = Math.sqrt(sdx * sdx + sdy * sdy) || 1;
      var sf = s.k * (sd - s.len);
      if (sf > WEB.fmax) sf = WEB.fmax; else if (sf < -WEB.fmax) sf = -WEB.fmax;
      var sux = sdx / sd, suy = sdy / sd;
      fx[s.a] += sux * sf; fy[s.a] += suy * sf;
      fx[s.b] -= sux * sf; fy[s.b] -= suy * sf;
    }
    /* Gravity: members toward their domain hub; hubs and root centered. */
    for (i = 0; i < n; i++) {
      var h = hubOf[i];
      if (h >= 0 && h !== i) {
        fx[i] += (px[h] - px[i]) * WEB.hubG;
        fy[i] += (py[h] - py[i]) * WEB.hubG;
      } else {
        fx[i] += -px[i] * WEB.centerG;
        fy[i] += -py[i] * WEB.centerG;
      }
    }
    /* Integrate with a displacement clamp; index 0 (the root) never moves. */
    for (i = 1; i < n; i++) {
      var sx = fx[i] * alpha, sy = fy[i] * alpha;
      if (sx > WEB.step) sx = WEB.step; else if (sx < -WEB.step) sx = -WEB.step;
      if (sy > WEB.step) sy = WEB.step; else if (sy < -WEB.step) sy = -WEB.step;
      px[i] += sx; py[i] += sy;
    }
  }

  /* Min-separation over DOTS: overlapping pairs are pushed apart until every
     pair keeps (rA + rB + sepPad) between centers. Fixed pass budget with
     early exit, ascending index order — fully deterministic. */
  function resolveOverlaps(px, py, rv) {
    var n = px.length, i, j;
    var rMax = 0;
    for (i = 0; i < n; i++) if (rv[i] > rMax) rMax = rv[i];
    var cell = rMax * 2 + WEB.sepPad;
    for (var pass = 0; pass < WEB.sepPasses; pass++) {
      var grid = {}, cx = new Int32Array(n), cy = new Int32Array(n);
      for (i = 0; i < n; i++) {
        cx[i] = Math.floor(px[i] / cell);
        cy[i] = Math.floor(py[i] / cell);
        var key = cx[i] + ":" + cy[i];
        (grid[key] = grid[key] || []).push(i);
      }
      var moved = false;
      for (i = 0; i < n; i++) {
        for (var gx = cx[i] - 1; gx <= cx[i] + 1; gx++) {
          for (var gy = cy[i] - 1; gy <= cy[i] + 1; gy++) {
            var b = grid[gx + ":" + gy];
            if (!b) continue;
            for (var bi = 0; bi < b.length; bi++) {
              j = b[bi];
              if (j <= i) continue;
              var minSep = rv[i] + rv[j] + WEB.sepPad;
              var dx = px[j] - px[i], dy = py[j] - py[i];
              var d2 = dx * dx + dy * dy;
              if (d2 >= minSep * minSep) continue;
              if (d2 < 1e-4) {
                dx = ((i * 31 + j * 7) % 13 - 6) * 0.17 || 0.61;
                dy = ((i * 17 + j * 11) % 13 - 6) * 0.17 || -0.43;
                d2 = dx * dx + dy * dy;
              }
              var d = Math.sqrt(d2), ux = dx / d, uy = dy / d;
              var push = minSep - d;
              if (i === 0) { px[j] += ux * push; py[j] += uy * push; }
              else if (j === 0) { px[i] -= ux * push; py[i] -= uy * push; }
              else {
                var hp = push / 2;
                px[i] -= ux * hp; py[i] -= uy * hp;
                px[j] += ux * hp; py[j] += uy * hp;
              }
              moved = true;
            }
          }
        }
      }
      if (!moved) break;
    }
  }

  /* Min-separation over LABEL BOXES (the H10 discipline: no overlapping
     label text at any drill depth). Each node's label is the rectangle the
     renderer will paint — dot offset + estimated text width, 18px tall.
     Intersecting boxes are pushed apart along the axis of least penetration;
     fixed pass budget, early exit, deterministic order. */
  function resolveLabelOverlaps(px, py, rv, lw) {
    var n = px.length, i, j;
    var wMax = 0;
    for (i = 0; i < n; i++) if (lw[i] > wMax) wMax = lw[i];
    var cell = wMax + 24;
    for (var pass = 0; pass < WEB.labelPasses; pass++) {
      /* Bucket by the label-rect CENTER (not the dot): two overlapping
         rects have centers within wMax < cell of each other, so every
         violating pair shares a 3x3 neighborhood. */
      var grid = {}, cx = new Int32Array(n), cy = new Int32Array(n);
      for (i = 0; i < n; i++) {
        cx[i] = Math.floor((px[i] + rv[i] + 5 + lw[i] / 2) / cell);
        cy[i] = Math.floor(py[i] / cell);
        var key = cx[i] + ":" + cy[i];
        (grid[key] = grid[key] || []).push(i);
      }
      var moved = false;
      for (i = 0; i < n; i++) {
        var hwi = lw[i] / 2;
        var cxi = px[i] + rv[i] + 5 + hwi;
        for (var gx = cx[i] - 1; gx <= cx[i] + 1; gx++) {
          for (var gy = cy[i] - 1; gy <= cy[i] + 1; gy++) {
            var b = grid[gx + ":" + gy];
            if (!b) continue;
            for (var bi = 0; bi < b.length; bi++) {
              j = b[bi];
              if (j <= i) continue;
              var hwj = lw[j] / 2;
              var dxc = (px[j] + rv[j] + 5 + hwj) - cxi;
              var dy = py[j] - py[i];
              var penX = hwi + hwj - Math.abs(dxc);
              var penY = 18 - Math.abs(dy);
              if (penX <= 0 || penY <= 0) continue;
              /* Push past zero penetration by labelPad: converging to EXACT
                 touching leaves pairs on the boundary where any neighbor
                 jostle re-breaks them (measured: pure-zero pushes thrash for
                 hundreds of passes; a 2px overshoot terminates in <100). */
              var sy, amt;
              if (penY <= penX) {
                sy = dy > 0 ? 1 : dy < 0 ? -1 : (((i + j) & 1) ? 1 : -1);
                amt = penY + WEB.labelPad;
                if (i === 0) { py[j] += sy * amt; }
                else if (j === 0) { py[i] -= sy * amt; }
                else { py[i] -= sy * amt / 2; py[j] += sy * amt / 2; }
              } else {
                sy = dxc > 0 ? 1 : dxc < 0 ? -1 : (((i + j) & 1) ? 1 : -1);
                amt = penX + WEB.labelPad;
                if (i === 0) { px[j] += sy * amt; }
                else if (j === 0) { px[i] -= sy * amt; }
                else { px[i] -= sy * amt / 2; px[j] += sy * amt / 2; }
              }
              moved = true;
            }
          }
        }
      }
      if (!moved) break;
    }
  }

  /* Gridlock breaker — the GUARANTEE behind the relaxation. Pairwise
     relaxation can deadlock: a label squeezed by neighbors on both sides
     receives net-zero pushes every pass (measured: 29 residual overlaps
     identical at 128 and 4000 passes). This sweep is monotone and therefore
     always terminates overlap-free: walk nodes in y-order and push any node
     whose label still collides with an already-placed one strictly
     downward until it is clear of ALL placed labels. The root (index 0)
     never moves. */
  function resolveLabelGridlock(px, py, rv, lw) {
    var n = px.length, i, j;
    var order = [];
    for (i = 0; i < n; i++) order.push(i);
    /* The immovable root goes FIRST so every other node checks against it;
       otherwise a node processed before the root's y-position could stay
       parked on top of it. */
    order.sort(function (a, b) {
      if (a === 0) return -1;
      if (b === 0) return 1;
      return py[a] - py[b] || px[a] - px[b] || a - b;
    });
    for (var oi = 0; oi < order.length; oi++) {
      j = order[oi];
      if (j === 0) continue;
      var again = true;
      var guard = 0;
      while (again && guard++ < n) {
        again = false;
        var jl = px[j] + rv[j] + 5, jr = jl + lw[j];
        for (var oj = 0; oj < oi; oj++) {
          i = order[oj];
          var il = px[i] + rv[i] + 5, ir = il + lw[i];
          if (jl < ir && il < jr && Math.abs(py[j] - py[i]) < 18) {
            py[j] = py[i] + 18 + WEB.labelPad;
            again = true;
          }
        }
      }
    }
  }

  /* Geometric cooling: alpha at tick t of T total. */
  function webAlpha(t, total) {
    var a0 = 0.6, aMin = 0.05;
    if (total <= 1) return aMin;
    return a0 * Math.pow(aMin / a0, t / (total - 1));
  }

  /* Run the sim for the current visible slice, then persist the settled
     positions. Fixed tick budgets: same graph, same expansion state, same
     picture. Incremental: existing nodes keep their settled positions, new
     children spawn beside their parent, only a short re-settle runs. */
  function runWebSim(shown, edges, hubOf) {
    var n = shown.length, i;
    var fresh = seedWeb(shown, edges);
    var springs = buildSprings(shown, edges);
    var cutoff = n > WEB.bigN ? WEB.cutoffBig : WEB.cutoff;
    var ticks = fresh > n * 0.4 ? (n > WEB.bigN ? WEB.ticksBig : WEB.ticksFull) : WEB.ticksIncr;
    var px = new Float64Array(n), py = new Float64Array(n);
    var qv = new Float64Array(n), rv = new Float64Array(n), lw = new Float64Array(n);
    for (i = 0; i < n; i++) {
      var p = webPos[shown[i].id];
      px[i] = p.x; py[i] = p.y;
      qv[i] = WEB.q[shown[i].type] || WEB.q.sym;
      rv[i] = nodeR(shown[i]);
      lw[i] = webLabelW(shown[i]);
    }
    for (var t = 0; t < ticks; t++) webTick(px, py, qv, springs, hubOf, cutoff, webAlpha(t, ticks));
    resolveOverlaps(px, py, rv);
    resolveLabelOverlaps(px, py, rv, lw);
    resolveLabelGridlock(px, py, rv, lw);
    for (i = 0; i < n; i++) {
      webPos[shown[i].id] = { x: px[i], y: py[i] };
      shown[i].x = px[i]; shown[i].y = py[i];
    }
  }

  /* Web paint. Same classes, data-id, and ARIA as tree mode, so drill,
     keyboard nav, search, selection, and the inspector work unchanged.
     Edges flip roles versus the tree: DEPENDS_ON becomes solid and loud,
     containment fades to faint links. */
  function drawWeb(shown, edges) {
    var s = "", i;
    for (i = 0; i < edges.length; i++) {
      var p = edges[i][0], c = edges[i][1];
      s += '<line class="cm-weblink" x1="' + r2(p.x) + '" y1="' + r2(p.y) + '" x2="' + r2(c.x) + '" y2="' + r2(c.y) + '"/>';
    }
    if (showDeps) {
      var wireToTree = {};
      for (i = 0; i < shown.length; i++) {
        var w = shown[i];
        if (w.real && !(w.real.id in wireToTree)) wireToTree[w.real.id] = w;
      }
      for (var fromWire in deps) {
        var a = wireToTree[fromWire];
        if (!a) continue;
        for (var di = 0; di < deps[fromWire].length; di++) {
          var d = deps[fromWire][di];
          var b = wireToTree[d.id];
          if (!b || a === b) continue;
          var dx = b.x - a.x, dy = b.y - a.y;
          var len = Math.sqrt(dx * dx + dy * dy) || 1;
          var ux = dx / len, uy = dy / len;
          var lwid = Math.min(3, 1 + Math.log(1 + (Number(d.count) || 1)) * 0.35);
          var mx = (a.x + b.x) / 2 - uy * 8;
          var my = (a.y + b.y) / 2 + ux * 8;
          s += '<line class="cm-depweb" x1="' + r2(a.x) + '" y1="' + r2(a.y) + '" x2="' + r2(b.x) + '" y2="' + r2(b.y) + '" stroke-width="' + r2(lwid) + '"/>' +
            '<circle class="cm-dep-tip" cx="' + r2(b.x - ux * 12) + '" cy="' + r2(b.y - uy * 12) + '" r="2"/>' +
            (d.count ? '<text class="cm-dep-count" x="' + r2(mx) + '" y="' + r2(my + 3) + '">' + esc(String(d.count)) + '</text>' : "");
        }
      }
    }
    for (i = 0; i < shown.length; i++) {
      var n = shown[i];
      var hasKids = n.children.length > 0;
      var collapsed = hasKids && n._collapsed;
      var r = nodeR(n);
      var col = nodeColor(n);
      var fill = collapsed ? col : hasKids ? "var(--bg)" : col;
      var cls = ["cm-node", "cm-w-" + n.type];
      if (selectedId === n.id) cls.push("selected");
      if (matchSet) cls.push(matchSet.has(n) ? "match" : "dim");
      var count = collapsed && n.nsyms ? ' <tspan fill="var(--text-faint)">·' + n.nsyms + "</tspan>" : "";
      var lx = r + 7;
      var shownName = webLabel(n);
      var estW = webLabelW(n);
      var aria = ' role="treeitem" tabindex="0" aria-label="' + esc(n.name) + ', ' + KICK[n.type] + '"' +
        (hasKids ? ' aria-expanded="' + (collapsed ? "false" : "true") + '"' : "");
      s += '<g class="' + cls.join(" ") + '" data-id="' + n.id + '"' + aria +
        ' transform="translate(' + r2(n.x) + ',' + r2(n.y) + ')">' +
        (selectedId === n.id ? '<circle class="selring" r="' + (r + 4) + '"/>' : "") +
        '<circle class="dot" r="' + r + '" fill="' + fill + '" stroke="' + col + '" stroke-width="1.6"/>' +
        (collapsed ? '<circle r="' + (r + 3.5) + '" fill="none" stroke="' + col + '" stroke-width="1" opacity=".4"/>' : "") +
        '<text class="lbl" x="' + lx + '" y="3.5" font-size="' + (n.type === "sym" ? 10.5 : 11.5) + '">' +
        esc(shownName) + count + "</text>" +
        '<rect class="hit" x="-' + (r + 4) + '" y="-9" width="' + (lx + estW + r + 4) + '" height="18"/>' +
        "</g>";
    }
    vp.innerHTML = s;
    applyT();
    visibleEl.textContent = shown.length.toLocaleString() + " nodes shown";
  }

  /* Web render: re-simulate only when the visible set actually changed;
     pure repaints (selection, dep toggle, search dimming) reuse the settled
     positions untouched. */
  function renderWeb() {
    var cw = collectWeb();
    var sig = "";
    for (var i = 0; i < cw.shown.length; i++) sig += cw.shown[i].id + ",";
    if (sig !== webSig) {
      webSig = sig;
      runWebSim(cw.shown, cw.edges, cw.hubOf);
    } else {
      for (i = 0; i < cw.shown.length; i++) {
        var p = webPos[cw.shown[i].id];
        if (p) { cw.shown[i].x = p.x; cw.shown[i].y = p.y; }
      }
    }
    drawWeb(cw.shown, cw.edges);
  }

  /* ==== tree layout (the alternate view), dynamically respaced ==== */
  function renderTree() {
    layout(root);
    var shown = [], edges = [];
    (function collect(n) {
      shown.push(n);
      var kids = n._collapsed || !n.children.length ? [] : n.children;
      for (var i = 0; i < kids.length; i++) { edges.push([n, kids[i]]); collect(kids[i]); }
    })(root);

    var s = "", i;
    for (i = 0; i < edges.length; i++) {
      var p = edges[i][0], c = edges[i][1], mx = (p.x + c.x) / 2;
      s += '<path class="cm-edge" d="M' + p.x + ' ' + p.y + 'C' + mx + ' ' + p.y + ' ' + mx + ' ' + c.y + ' ' + c.x + ' ' + c.y + '"/>';
    }
    if (showDeps) {
      var wireToTree = {};
      for (i = 0; i < shown.length; i++) {
        var w = shown[i];
        if (w.real && !(w.real.id in wireToTree)) wireToTree[w.real.id] = w;
      }
      for (var fromWire in deps) {
        var a = wireToTree[fromWire];
        if (!a) continue;
        for (var di = 0; di < deps[fromWire].length; di++) {
          var d = deps[fromWire][di];
          var b = wireToTree[d.id];
          if (!b || a === b) continue;
          var bow = 46 + Math.abs(a.y - b.y) * 0.12;
          var cx = Math.min(a.x, b.x) - bow;
          var midX = (a.x + b.x) / 2 - bow * 0.72;
          var midY = (a.y + b.y) / 2;
          s += '<path class="cm-dep" d="M' + a.x + ' ' + a.y + 'C' + cx + ' ' + a.y + ' ' + cx + ' ' + b.y + ' ' + b.x + ' ' + b.y + '"/>' +
            '<circle class="cm-dep-tip" cx="' + (b.x - 9) + '" cy="' + b.y + '" r="2"/>' +
            (d.count ? '<text class="cm-dep-count" x="' + midX + '" y="' + (midY + 3) + '">' + esc(String(d.count)) + '</text>' : "");
        }
      }
    }
    for (i = 0; i < shown.length; i++) {
      var n = shown[i];
      var hasKids = n.children.length > 0;
      var collapsed = hasKids && n._collapsed;
      var r = nodeR(n);
      var col = nodeColor(n);
      var fill = collapsed ? col : hasKids ? "var(--bg)" : col;
      var cls = ["cm-node"];
      if (selectedId === n.id) cls.push("selected");
      if (matchSet) cls.push(matchSet.has(n) ? "match" : "dim");
      var count = collapsed && n.nsyms ? ' <tspan fill="var(--text-faint)">·' + n.nsyms + "</tspan>" : "";
      var lx = r + 7;
      /* Expanded parents label LEFT (tidy-tree style) so the trace to their
         children never runs through text; leaves and collapsed nodes label
         RIGHT. Both directions truncate to the (dynamic) gap they occupy so
         no label can reach the neighboring column's nodes. */
      var labelLeft = hasKids && !collapsed;
      var colIdx = Math.min(n.depth, COL.length - 1);
      var maxChars = 34;
      if (labelLeft && n.depth > 0) {
        var gapLeft = COL[colIdx] - COL[colIdx - 1];
        maxChars = Math.max(8, Math.min(34, Math.floor((gapLeft - 45) / 7)));
      } else if (!labelLeft && n.depth >= 1 && colIdx < COL.length - 1) {
        var gapRight = COL[colIdx + 1] - COL[colIdx];
        maxChars = Math.max(8, Math.min(34, Math.floor((gapRight - 45) / 7)));
      }
      var shownName = truncate(n.name, maxChars);
      var estW = shownName.length * 7 + 30;
      var aria = ' role="treeitem" tabindex="0" aria-label="' + esc(n.name) + ', ' + KICK[n.type] + '"' +
        (hasKids ? ' aria-expanded="' + (collapsed ? "false" : "true") + '"' : "");
      s += '<g class="' + cls.join(" ") + '" data-id="' + n.id + '"' + aria +
        ' transform="translate(' + n.x + ',' + n.y + ')">' +
        (selectedId === n.id ? '<circle class="selring" r="' + (r + 4) + '"/>' : "") +
        '<circle class="dot" r="' + r + '" fill="' + fill + '" stroke="' + col + '" stroke-width="1.6"/>' +
        (collapsed ? '<circle r="' + (r + 3.5) + '" fill="none" stroke="' + col + '" stroke-width="1" opacity=".4"/>' : "") +
        '<text class="lbl" x="' + (labelLeft ? -lx : lx) + '" y="3.5"' +
        (labelLeft ? ' text-anchor="end"' : "") +
        ' font-size="' + (n.type === "sym" ? 10.5 : 11.5) + '">' + esc(shownName) + count + "</text>" +
        (labelLeft
          ? '<rect class="hit" x="-' + (lx + estW) + '" y="-9" width="' + (lx + estW + r + 4) + '" height="18"/>'
          : '<rect class="hit" x="-' + (r + 4) + '" y="-9" width="' + (lx + estW + r + 4) + '" height="18"/>') +
        "</g>";
    }
    vp.innerHTML = s;
    applyT();
    visibleEl.textContent = shown.length.toLocaleString() + " nodes shown";
  }

  function render() {
    if (!root) return;
    if (layoutMode === "web") renderWeb();
    else renderTree();
  }

  /* Inspector */
  function metric(v, label) {
    return '<div class="metric"><b>' + Number(v).toLocaleString() + "</b><span>" + label + "</span></div>";
  }
  function showDetail(n) {
    selectedId = n.id;
    detail.classList.remove("empty");
    var kick = { root: "repository", domain: "domain", unit: "unit", file: "source file",
                 sym: KIND_LABEL[n.kind] || "symbol" }[n.type];
    var real = n.real;
    var html = '<div class="kicker">' + esc(kick) + "</div><h3>" + esc(n.name) + "</h3>";
    var path = "";
    if (n.type === "file") path = n.path || "";
    else if (n.type === "sym") {
      var file = prop(real, "file"), line = prop(real, "line");
      path = (file || "") + (file && line != null ? ":" + line : "");
    }
    if (path) html += '<div class="path">' + esc(path) + "</div>";
    if (n.type !== "sym") {
      html += '<div class="metric-row">';
      if (n.type === "root" || n.type === "domain") html += metric(n.nunits, "units");
      if (n.type !== "file") html += metric(n.nfiles, "files");
      html += metric(n.nsyms, "symbols") + "</div>";
      var tot = n.mix.T + n.mix.F + n.mix.C;
      if (tot) {
        html += "<h4>symbol kinds</h4><div class=\"kindbar\">" +
          '<i style="flex:' + n.mix.T + ';background:var(--cm-type)"></i>' +
          '<i style="flex:' + n.mix.F + ';background:var(--cm-func)"></i>' +
          '<i style="flex:' + n.mix.C + ';background:var(--cm-const)"></i></div>' +
          '<div class="kindlegend">' +
          '<span><i class="sw" style="background:var(--cm-type)"></i>' + n.mix.T + " type</span>" +
          '<span><i class="sw" style="background:var(--cm-func)"></i>' + n.mix.F + " func</span>" +
          '<span><i class="sw" style="background:var(--cm-const)"></i>' + n.mix.C + " const</span></div>";
      }
    }
    var facts = [], keys = ["archetype", "layer", "domain", "unit", "kind", "reason"];
    if (real) {
      for (var i = 0; i < keys.length; i++) {
        var v = prop(real, keys[i]);
        if (v != null && v !== "") facts.push([keys[i], v]);
      }
    }
    if (facts.length) {
      html += "<h4>facts</h4><div class=\"facts\">" +
        facts.map(function (f) {
          return '<div class="fact"><span>' + esc(f[0]) + "</span><b>" + esc(String(f[1])) + "</b></div>";
        }).join("") + "</div>";
    }
    if (real && deps[real.id] && deps[real.id].length) {
      html += "<h4>depends on</h4><div class=\"chips\">" +
        deps[real.id].map(function (d) {
          var t = realById[d.id];
          var label = (t && t.caption) || d.id;
          var times = d.count != null ? " <em>×" + esc(String(d.count)) + "</em>" : "";
          return '<span class="chip dep">' + esc(label) + times + "</span>";
        }).join("") + "</div>";
    }
    if (n.type === "domain" && n.children.length) {
      html += "<h4>units</h4><div class=\"chips\">" +
        n.children.map(function (u) { return '<span class="chip">' + esc(u.name) + "</span>"; }).join("") +
        "</div>";
    }
    detail.innerHTML = html;
  }

  /* Interactions */
  function collapseSubtree(n) {
    n._collapsed = true;
    for (var i = 0; i < n.children.length; i++) collapseSubtree(n.children[i]);
  }
  function toggleNode(n) {
    if (!n.children.length) return;
    if (n._collapsed) n._collapsed = false;
    else collapseSubtree(n);
  }

  /* Web | Tree — a layout choice, never a bulk expansion. Drilling stays
     click-only in both. */
  document.getElementById("cm-layout").addEventListener("click", function (e) {
    var b = e.target.closest("button");
    if (!b || !root) return;
    var mode = b.dataset.mode === "tree" ? "tree" : "web";
    if (mode === layoutMode) return;
    layoutMode = mode;
    var all = document.querySelectorAll("#cm-layout button");
    for (var i = 0; i < all.length; i++) {
      all[i].setAttribute("aria-pressed", all[i].dataset.mode === mode ? "true" : "false");
    }
    render();
    fit();
  });

  var qt = null;
  searchInput.addEventListener("input", function (e) {
    clearTimeout(qt);
    qt = setTimeout(function () { runSearch(e.target.value.trim().toLowerCase()); }, 160);
  });
  searchInput.addEventListener("keydown", function (e) {
    if (e.key === "Escape" && searchInput.value) {
      e.stopPropagation();
      searchInput.value = "";
      runSearch("");
    }
  });

  function runSearch(q) {
    if (!root) return;
    if (!q) {
      matchSet = null;
      matchCountEl.hidden = true;
      render();
      return;
    }
    matchSet = new Set();
    var hits = 0;
    (function walk(n, anc) {
      var hay = (n.name + " " + (n.path || "")).toLowerCase();
      if (hay.indexOf(q) >= 0) {
        hits++;
        matchSet.add(n);
        for (var i = 0; i < anc.length; i++) { matchSet.add(anc[i]); anc[i]._collapsed = false; }
      }
      var next = anc.concat(n);
      for (var c = 0; c < n.children.length; c++) walk(n.children[c], next);
    })(root, []);
    matchCountEl.hidden = false;
    matchCountEl.textContent = hits === 0 ? "no matches" : hits.toLocaleString() + (hits === 1 ? " match" : " matches");
    matchCountEl.classList.toggle("none", hits === 0);
    render();
    if (hits > 0) fit();
  }

  var drag = null, dragMoved = false, downId = null;
  wrap.addEventListener("pointerdown", function (e) {
    drag = { x: e.clientX, y: e.clientY, tx: T.x, ty: T.y };
    dragMoved = false;
    var g = e.target.closest(".cm-node");
    downId = g ? g.dataset.id : null;
  });
  wrap.addEventListener("pointermove", function (e) {
    if (!drag) return;
    var dx = e.clientX - drag.x, dy = e.clientY - drag.y;
    if (!dragMoved && Math.abs(dx) + Math.abs(dy) > 4) {
      dragMoved = true;
      wrap.classList.add("grabbing");
      try { wrap.setPointerCapture(e.pointerId); } catch (err) {}
    }
    if (dragMoved) { T.x = drag.tx + dx; T.y = drag.ty + dy; applyT(); }
  });
  wrap.addEventListener("pointerup", function (e) {
    var wasClick = drag && !dragMoved && downId;
    drag = null;
    wrap.classList.remove("grabbing");
    try { wrap.releasePointerCapture(e.pointerId); } catch (err) {}
    if (wasClick) {
      var n = byId[downId];
      if (n) { toggleNode(n); showDetail(n); render(); }
    }
    downId = null;
  });
  svg.addEventListener("keydown", function (e) {
    if (e.key !== "Enter" && e.key !== " ") return;
    var g = e.target.closest ? e.target.closest(".cm-node") : null;
    if (!g) return;
    e.preventDefault();
    var n = byId[g.dataset.id];
    if (!n) return;
    toggleNode(n);
    showDetail(n);
    render();
    var again = vp.querySelector('[data-id="' + n.id + '"]');
    if (again) again.focus();
  });
  wrap.addEventListener("wheel", function (e) {
    e.preventDefault();
    var r = svg.getBoundingClientRect();
    var mx = e.clientX - r.left, my = e.clientY - r.top;
    var f = Math.exp(-e.deltaY * 0.0014);
    var nk = Math.min(3, Math.max(0.1, T.k * f));
    T.x = mx - (mx - T.x) * (nk / T.k);
    T.y = my - (my - T.y) * (nk / T.k);
    T.k = nk;
    applyT();
  }, { passive: false });

  function fit() {
    if (!root) return;
    var shown = [];
    (function c(n) {
      shown.push(n);
      var kids = n._collapsed || !n.children.length ? [] : n.children;
      kids.forEach(c);
    })(root);
    if (!shown.length) return;
    var minX = 1 / 0, maxX = -1 / 0, minY = 1 / 0, maxY = -1 / 0;
    for (var i = 0; i < shown.length; i++) {
      var n = shown[i];
      if (n.x < minX) minX = n.x;
      if (n.x > maxX) maxX = n.x;
      if (n.y < minY) minY = n.y;
      if (n.y > maxY) maxY = n.y;
    }
    minX -= 250; maxX += 260; minY -= 30; maxY += 30;
    var r = svg.getBoundingClientRect();
    if (!r.width || !r.height) return;
    var k = Math.min(2, Math.max(0.1, Math.min(r.width / (maxX - minX), r.height / (maxY - minY))));
    T.k = k;
    T.x = (r.width - (maxX + minX) * k) / 2;
    T.y = (r.height - (maxY + minY) * k) / 2;
    applyT();
  }
  document.getElementById("cm-fit").addEventListener("click", fit);

  var depsBtn = document.getElementById("cm-deps");
  depsBtn.addEventListener("click", function () {
    showDeps = !showDeps;
    depsBtn.setAttribute("aria-pressed", showDeps ? "true" : "false");
    render();
  });

  function renderStats(nodes) {
    var c = { domain: 0, unit: 0, file: 0, symbol: 0 };
    for (var i = 0; i < nodes.length; i++) {
      var l = level(nodes[i]);
      if (c[l] !== undefined) c[l]++;
    }
    statsEl.innerHTML = [["domains", c.domain], ["units", c.unit], ["files", c.file], ["symbols", c.symbol]]
      .map(function (p) {
        return '<div class="stat"><b>' + p[1].toLocaleString() + "</b><span>" + p[0] + "</span></div>";
      }).join("");
  }

  /* Boot */
  detail.innerHTML = EMPTY_DETAIL;
  buildTree(data.name, NODES, RELS);
  setDepth(1);
  renderStats(NODES);
  render();
  requestAnimationFrame(fit);
})();
"##;

/// The AI-companion copy button: clipboard API with an `execCommand`
/// fallback, copied-check feedback in the status span. A self-contained
/// IIFE appended after [`JS`]. No network, no external references.
const JS_COMPANION: &str = r##"
(function () {
  "use strict";
  var btn = document.getElementById("companion-copy");
  if (!btn) return;
  var pre = document.getElementById("companion-text");
  var status = document.getElementById("companion-status");
  var timer = null;
  function flash(msg) {
    if (!status) return;
    status.textContent = msg;
    if (timer) clearTimeout(timer);
    timer = setTimeout(function () { status.textContent = ""; }, 2500);
  }
  function fallbackCopy(text) {
    var ta = document.createElement("textarea");
    ta.value = text;
    ta.setAttribute("readonly", "");
    ta.style.position = "fixed";
    ta.style.left = "-9999px";
    document.body.appendChild(ta);
    ta.select();
    var ok = false;
    try { ok = document.execCommand("copy"); } catch (e) { ok = false; }
    document.body.removeChild(ta);
    flash(ok ? "Copied ✓" : "Copy failed — open the preview and copy manually");
  }
  btn.addEventListener("click", function () {
    var text = pre ? pre.textContent : "";
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(text).then(
        function () { flash("Copied ✓"); },
        function () { fallbackCopy(text); }
      );
    } else {
      fallbackCopy(text);
    }
  });
})();
"##;

/// Enrich builds only: the enriched-domains renderer, appended after [`JS`].
/// A self-contained IIFE (its own `esc`), so the default build's script is
/// byte-identical with the whole block absent.
#[cfg(feature = "enrich")]
const JS_ENRICH: &str = r##"
"use strict";
(function () {
  /* Enriched domains: render the embedded trailtracker.enrich/v1 document. */
  var el = document.getElementById("tt-enrich");
  var cards = document.getElementById("enrich-cards");
  var att = document.getElementById("enrich-attestation");
  if (!el || !cards) return;
  function esc(s) {
    return String(s).replace(/[<>&]/g, function (c) {
      return { "<": "&lt;", ">": "&gt;", "&": "&amp;" }[c];
    });
  }
  var doc;
  try { doc = JSON.parse(el.textContent); } catch (err) { return; }
  var clusters = doc.clusters || [];
  var h = "";
  for (var i = 0; i < clusters.length; i++) {
    var c = clusters[i];
    h += '<article class="card"><header><h3>' + esc(c.name || c.label || c.domain || "?") + "</h3>" +
      (c.domain ? '<span class="chip">' + esc(c.domain) + "</span>" : "") +
      (c.confidence ? '<span class="chip">confidence: ' + esc(String(c.confidence)) + "</span>" : "") +
      "</header>" +
      '<p class="counts">' + (c.unit_count || 0) + " unit(s) · " + (c.file_count || 0) +
      " file(s) · " + (c.symbol_count || 0) + " symbol(s)</p>" +
      (c.description ? "<p>" + esc(c.description) + "</p>" : "") +
      (Array.isArray(c.responsibilities) && c.responsibilities.length
        ? "<ul>" + c.responsibilities.map(function (r) { return "<li>" + esc(r) + "</li>"; }).join("") + "</ul>"
        : "") +
      (Array.isArray(c.subdomains) && c.subdomains.length
        ? '<div class="chips">' + c.subdomains.map(function (s) { return '<span class="chip">' + esc(s) + "</span>"; }).join("") + "</div>"
        : "") +
      "</article>";
  }
  cards.innerHTML = h;
  var a = doc.attestation || {};
  if (att) {
    att.innerHTML = "<b>Attested:</b> model <code>" + esc(a.model || "unreported") +
      "</code> · prompt hash <code>" + esc(a.prompt_hash || "?") + "</code>" +
      (a.timestamp ? " · at " + esc(a.timestamp) : "") +
      (a.backend ? "<br>backend: <code>" + esc(a.backend) + "</code>" : "") +
      '<br><span class="dim">Cluster membership and counts are deterministic; names, descriptions, and responsibilities are LLM-attested, not byte-stable.</span>';
  }
})();
"##;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::Graph;
    use crate::ir::ontology::{edge, node as ont};
    use crate::pipeline::AnalysisStats;

    /// Wrap a hand-built test graph in the [`Analysis`] shape `dossier_html`
    /// consumes (zeroed stats: no parse-coverage claims in these fixtures).
    fn analysis_of(graph: Graph) -> Analysis {
        Analysis {
            graph,
            stats: AnalysisStats::default(),
        }
    }

    /// A small eShop-shaped base graph (same shape the hierarchy extractor
    /// tests use): two domains, three units, one cross-domain dependency.
    fn sample_base() -> Graph {
        let mut g = Graph::new();
        let file = |g: &mut Graph, path: &str| {
            let id = format!("base-file::{path}");
            g.upsert_node(
                id.clone(),
                ont::FILE,
                path.rsplit('/').next().unwrap().to_string(),
                vec![
                    ("path", Json::str(path)),
                    ("language", Json::str("csharp")),
                    ("lines", Json::U64(50)),
                ],
            );
            id
        };
        let sym = |g: &mut Graph, file_id: &str, kind: &'static str, name: &str, line: u64| {
            let id = format!("sym::{name}");
            g.upsert_node(id.clone(), kind, name, vec![("line", Json::U64(line))]);
            g.add_edge(file_id.to_string(), edge::DECLARES, id.clone(), vec![]);
            id
        };
        let f = file(&mut g, "src/Ordering.API/OrdersController.cs");
        let controller = sym(&mut g, &f, ont::TYPE, "OrdersController", 12);
        let create = sym(&mut g, &f, ont::FUNCTION, "CreateOrder", 30);
        let f = file(&mut g, "src/Ordering.Domain/Order.cs");
        let order = sym(&mut g, &f, ont::TYPE, "Order", 5);
        let order_item = sym(&mut g, &f, ont::TYPE, "OrderItem", 40);
        sym(&mut g, &f, ont::TYPE, "OrderStatus", 80);
        g.add_edge(controller.clone(), edge::USES_TYPE, order, vec![]);
        g.add_edge(create, edge::USES_TYPE, order_item, vec![]);
        let f = file(&mut g, "src/Basket.API/BasketService.cs");
        let bsvc = sym(&mut g, &f, ont::TYPE, "BasketService", 9);
        let basket_item = sym(&mut g, &f, ont::TYPE, "BasketItem", 55);
        sym(&mut g, &f, ont::TYPE, "BasketRepository", 71);
        let f = file(&mut g, "src/Basket.API/BasketCheckout.cs");
        let checkout = sym(&mut g, &f, ont::TYPE, "BasketCheckout", 7);
        sym(&mut g, &f, ont::FUNCTION, "GetBasketAsync", 21);
        sym(&mut g, &f, ont::FUNCTION, "UpdateBasketAsync", 33);
        g.add_edge(bsvc, edge::USES_TYPE, checkout, vec![]);
        g.add_edge(controller, edge::USES_TYPE, basket_item, vec![]);
        g
    }

    #[test]
    fn dossier_contains_every_section_and_the_embedded_graph() {
        let html = dossier_html(&analysis_of(sample_base()), "eshopish", None);
        for marker in [
            "<!DOCTYPE html>",
            "TrailTracker dossier",
            "<section id=\"brief\">",
            "<section id=\"map\">",
            "<section id=\"violations\">",
            "<footer>",
            "id=\"tt-graph\"",
            "Domains (structural clustering)",
            "Dependency cycles",
            "analysis fingerprint",
        ] {
            assert!(html.contains(marker), "missing `{marker}`");
        }
        // The enriched-domains section exists only in `enrich` feature
        // builds; the default/airgap dossier has no trace of the naming
        // pass — no section, no pointer note, no mention of it at all.
        if cfg!(feature = "enrich") {
            assert!(
                html.contains("<section id=\"enriched\">"),
                "enrich builds render the enriched section"
            );
            assert!(
                html.contains("enrich-domains"),
                "enrich builds keep the pointer note"
            );
        } else {
            assert!(
                !html.contains("<section id=\"enriched\">"),
                "default build must not render the enriched section"
            );
            assert!(
                !html.contains("enrich"),
                "default build must not mention enrichment anywhere"
            );
        }
        // Drill-only navigation: the bulk expand-to-level buttons are gone.
        assert!(
            !html.contains("cm-levels"),
            "level bulk-expand buttons must not exist"
        );
        assert!(
            !html.contains("data-d=\""),
            "level button markup must not exist"
        );
        // The layout toggle exists, web is the pressed default, tree the
        // alternate.
        assert!(html.contains("id=\"cm-layout\""), "layout toggle missing");
        assert!(
            html.contains("data-mode=\"web\" aria-pressed=\"true\""),
            "web must be the default layout"
        );
        assert!(
            html.contains("data-mode=\"tree\" aria-pressed=\"false\""),
            "tree must be the alternate layout"
        );
        // The embedded wire carries the hierarchy view.
        assert!(
            html.contains("\"level\":\"domain\""),
            "no domain nodes embedded"
        );
        assert!(
            html.contains("\"level\":\"symbol\""),
            "no symbol nodes embedded"
        );
        // No enrich document supplied: no enrich payload in any build.
        assert!(
            !html.contains("id=\"tt-enrich\""),
            "enrich payload must be absent"
        );
    }

    #[test]
    fn violations_table_names_unit_pairs_with_evidence() {
        let mut g = sample_base();
        // A deliberate inversion: the Domain entity reaches into the Basket
        // API (Domain → Presentation).
        g.add_edge("sym::Order", edge::USES_TYPE, "sym::BasketService", vec![]);
        let html = dossier_html(&analysis_of(g), "eshopish", None);
        // Grouped by layer pair, with the offending units NAMED, at unit
        // grain, with file-level evidence — not a layer-only summary.
        assert!(
            html.contains("<b>Domain</b> &rarr; <b>Presentation</b>"),
            "layer-pair group header missing"
        );
        assert!(
            html.contains("<code>Ordering.Domain</code>"),
            "from-unit not named"
        );
        assert!(
            html.contains("<code>Basket.API</code>"),
            "to-unit not named"
        );
        assert!(
            html.contains("src/Ordering.Domain/Order.cs"),
            "file-level evidence missing"
        );
        assert!(html.contains("example evidence"), "evidence column missing");
        // A short group renders open (a heading, not a fold).
        assert!(
            html.contains("class=\"vgroup-h\""),
            "short group must not fold"
        );
    }

    #[test]
    fn long_violation_groups_fold_into_details() {
        // 21 Domain units all violating into one API unit: the
        // Domain → Presentation group exceeds the fold threshold (20) and
        // must collapse behind <details>.
        let mut g = Graph::new();
        g.upsert_node(
            "file::api",
            ont::FILE,
            "app.cs",
            vec![("path", Json::str("src/Shell.API/app.cs"))],
        );
        g.upsert_node("sym::app", ont::TYPE, "App", vec![]);
        g.add_edge("file::api", edge::DECLARES, "sym::app", vec![]);
        for i in 0..21 {
            let path = format!("src/Mod{i:02}.Domain/entity.cs");
            let fid = format!("file::{path}");
            let sid = format!("sym::e{i:02}");
            g.upsert_node(
                fid.clone(),
                ont::FILE,
                "entity.cs",
                vec![("path", Json::str(&path))],
            );
            g.upsert_node(sid.clone(), ont::TYPE, format!("Entity{i:02}"), vec![]);
            g.add_edge(fid, edge::DECLARES, sid.clone(), vec![]);
            g.add_edge(sid, edge::USES_TYPE, "sym::app", vec![]);
        }
        let html = dossier_html(&analysis_of(g), "folded", None);
        assert!(
            html.contains("<details class=\"vgroup\"><summary>"),
            "a 21-row group must fold into <details>"
        );
        assert!(
            html.contains("<code>Mod00.Domain</code>"),
            "folded rows still name their units"
        );
    }

    #[test]
    fn dossier_is_deterministic() {
        let a = analysis_of(sample_base());
        assert_eq!(
            dossier_html(&a, "eshopish", None),
            dossier_html(&a, "eshopish", None)
        );
    }

    #[cfg(feature = "enrich")]
    #[test]
    fn dossier_embeds_the_enrich_document_and_drops_the_pointer_note() {
        let enrich = r#"{"schema":"trailtracker.enrich/v1","clusters":[{"cluster_id":"c1","name":"Order Management"}],"attestation":{"model":"haiku","prompt_hash":"fnv1a64:00000000000000ab"}}"#;
        let html = dossier_html(&analysis_of(sample_base()), "eshopish", Some(enrich));
        assert!(html.contains("id=\"tt-enrich\""), "enrich payload missing");
        assert!(html.contains("Order Management"), "cluster name missing");
        assert!(
            html.contains("fnv1a64:00000000000000ab"),
            "prompt hash missing"
        );
        assert!(
            html.contains("id=\"enrich-cards\""),
            "enrich card container missing"
        );
        assert!(
            !html.contains("No enrichment supplied"),
            "pointer note must be replaced by the cards"
        );
    }

    #[test]
    fn dossier_makes_zero_external_references() {
        // In enrich builds, exercise the enrich path too — its attestation
        // markup must be as airgap-clean as everything else.
        let enrich = if cfg!(feature = "enrich") {
            Some(r#"{"schema":"trailtracker.enrich/v1","clusters":[],"attestation":{}}"#)
        } else {
            None
        };
        let html = dossier_html(&analysis_of(sample_base()), "eshopish", enrich);
        for banned in [
            "http:",
            "https:",
            "<link",
            "<img",
            "@import",
            "url(",
            "fetch(",
            "XMLHttpRequest",
            "import(",
            "srcset",
            "integrity=",
            "crossorigin",
        ] {
            assert!(
                !html.contains(banned),
                "airgap violation: found `{banned}` in the dossier"
            );
        }
    }

    #[test]
    fn embedded_json_cannot_close_its_script_tag() {
        assert_eq!(embed_json(r#"{"a":"</script>"}"#), r#"{"a":"<\/script>"}"#);
        // And the wire embed round-trips: unescaping restores the original.
        let wire = r#"{"a":"</x>","b":1}"#;
        assert_eq!(embed_json(wire).replace("<\\/", "</"), wire);
    }

    #[test]
    fn html_escaping_neutralizes_markup_in_names() {
        let mut g = Graph::new();
        g.upsert_node(
            "file::src/evil.rs",
            ont::FILE,
            "<script>alert(1)</script>",
            vec![
                ("path", Json::str("src/evil.rs")),
                ("language", Json::str("rust")),
                ("lines", Json::U64(1)),
            ],
        );
        g.upsert_node("sym::x", ont::FUNCTION, "x", vec![("line", Json::U64(1))]);
        g.add_edge("file::src/evil.rs", edge::DECLARES, "sym::x", vec![]);
        let html = dossier_html(&analysis_of(g), "evil", None);
        // The raw tag never appears outside the JSON payload; inside the
        // payload `</` is escaped, so no `</script>` sequence survives at all
        // except the legitimate closers for our own script elements.
        let closes = html.matches("</script>").count();
        assert_eq!(
            closes, 2,
            "only the graph payload + inline JS closers may exist"
        );
        assert!(
            !html.contains("<script>alert"),
            "unescaped node name leaked"
        );
    }

    #[test]
    fn repo_name_takes_the_last_segment() {
        assert_eq!(repo_name("eval/corpus/calc"), "calc");
        assert_eq!(repo_name("/a/b/eShop/"), "eShop");
        assert_eq!(repo_name("."), ".");
    }
}
