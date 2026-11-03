//! The codebase brief: a language-agnostic, analyst-readable model of an
//! unfamiliar repository — the document you read *first* when handed a codebase
//! you have never seen.
//!
//! Where [`crate::report`] is tuned to the Salesforce-org vocabulary (flows,
//! SObjects, Apex), the brief speaks only the neutral ontology every front end
//! lowers into, so it works on any of the supported languages:
//!
//! - **Overview** — languages present (from node `language` props) with file /
//!   line / node counts, plus total node and edge tallies.
//! - **Architecture** — the domain clustering (the same
//!   [`crate::extract::domains::assign_domains`] single source of truth the
//!   domains/hierarchy views emit: business domains listed, infrastructure
//!   groups summarized), the largest containers ([`Package`] / [`Module`] /
//!   [`File`] nodes ranked by directly contained symbols) and the inter-module
//!   dependency map: which files depend on which, via `DEPENDS`-family edges
//!   ([`crate::ir::ontology::relation::DEPENDS`]) whose endpoints resolve to
//!   *different* files.
//! - **Entry points** — `main`-named functions, and the public API surface:
//!   symbols referenced from outside their own file (high external fan-in).
//! - **Hotspots** — highest fan-in (most depended-upon — change ripples) and
//!   highest fan-out (most outbound complexity) nodes. Fan-in entries whose
//!   references come mostly from *stamped boilerplate* — the same-named caller
//!   declared in many same-named files (one templated file copied per module,
//!   e.g. 106 `get-schema.ts` copies each declaring `registerGetSchema`) — are
//!   annotated with the duplicate-caller count and a de-duplicated "distinct"
//!   figure, so replicated scaffolding cannot masquerade as 106 independent
//!   callers. The raw graph (and the raw count) stays faithful: every edge is
//!   real; the annotation surfaces the duplication instead of hiding it.
//! - **Dependency cycles** — Tarjan SCC over the file-level dependency graph;
//!   any strongly connected component larger than one file is an architectural
//!   smell worth knowing on day one.
//! - **What this repo is** — a one-paragraph plain-English synthesis assembled
//!   from the signals above by a deterministic template. No LLM anywhere.
//!
//! Like every renderer in this crate the brief is a pure, deterministic
//! function of the graph: it walks the `BTreeMap`-ordered node/edge iterators,
//! aggregates into `BTreeMap`s, and breaks every ranking tie by id ascending,
//! so the same graph always produces byte-identical markdown.
//!
//! [`Package`]: crate::ir::ontology::node::PACKAGE
//! [`Module`]: crate::ir::ontology::node::MODULE
//! [`File`]: crate::ir::ontology::node::FILE

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::Path;

use crate::core::json::Json;
use crate::graph::{Graph, GraphNode};
use crate::ir::ontology::{edge, node as ont, parent_relation, relation};

/// How many entries each ranked list (containers, public API, hotspots) shows.
const TOP_N: usize = 10;

/// How many cross-file dependency pairs the module dependency map shows before
/// summarizing the rest (a big repo has thousands; the shape, not the census).
const DEP_MAP_N: usize = 20;

/// Minimum number of distinct caller files sharing one (file basename, caller
/// symbol name) pair before the group is reported as stamped boilerplate.
/// Two same-named files can be coincidence; three or more parallel copies all
/// referencing the same target is a template.
const DUP_CALLER_MIN_FILES: usize = 3;

/// How many duplicate-caller groups the markdown annotation spells out before
/// summarizing the remainder (JSON always carries every qualifying group).
const DUP_GROUPS_SHOWN: usize = 3;

/// One stamped-boilerplate caller group inbound to a single target symbol:
/// the same-named top-level caller declared in many files sharing a basename
/// (a templated file copied once per module). The references are real edges —
/// the group exists so reports can say "N copies of one file", not "N
/// independent callers".
struct DupCallerGroup<'g> {
    /// Caller symbol name (e.g. `registerGetSchema`).
    caller: &'g str,
    /// Shared basename of the caller files (e.g. `get-schema.ts`).
    basename: &'g str,
    /// Distinct caller files in the group.
    files: usize,
    /// Total inbound references the group contributes to the target.
    references: usize,
}

/// Everything the sections need, computed once from the graph.
struct Model<'g> {
    /// id → node, for label lookups.
    by_id: BTreeMap<&'g str, &'g GraphNode>,
    /// Per-language `(files, lines, nodes)` tallies; key `"(unknown)"` collects
    /// nodes with no `language` property that still matter (files only).
    languages: BTreeMap<String, LangStats>,
    /// symbol id → the File node id that (transitively) declares it.
    owner_file: BTreeMap<&'g str, &'g str>,
    /// Cross-file dependency counts: `(from_file, to_file) → refs`.
    file_deps: BTreeMap<(&'g str, &'g str), usize>,
    /// Incoming `DEPENDS`-family edge count per node.
    fan_in: BTreeMap<&'g str, usize>,
    /// Outgoing `DEPENDS`-family edge count per node.
    fan_out: BTreeMap<&'g str, usize>,
    /// Incoming `DEPENDS`-family edges *from a different file*, per symbol.
    external_fan_in: BTreeMap<&'g str, usize>,
    /// target symbol id → its stamped-boilerplate caller groups (same-named
    /// top-level callers in ≥ [`DUP_CALLER_MIN_FILES`] same-named files),
    /// largest first. Used to annotate fan-in / public-API counts.
    dup_callers: BTreeMap<&'g str, Vec<DupCallerGroup<'g>>>,
    /// `main`-named Function node ids.
    mains: Vec<&'g str>,
    /// File-level dependency cycles (each sorted, whole list sorted).
    cycles: Vec<Vec<&'g str>>,
    /// File node ids classified as generated code (EF migrations, protos,
    /// designers). Excluded from architecture signal so hand-written code leads.
    generated: BTreeSet<&'g str>,
    /// Domain clusters from [`crate::extract::domains::assign_domains`] —
    /// the same single source of truth the domains/hierarchy views emit —
    /// largest first. Business domains and infrastructure groups both appear;
    /// `kind`/`reason` tell them apart.
    domains: Vec<DomainRow>,
}

/// One summarized domain cluster for the brief.
struct DomainRow {
    name: String,
    kind: &'static str,
    reason: Option<&'static str>,
    files: u64,
    symbols: u64,
}

#[derive(Default)]
struct LangStats {
    files: usize,
    lines: u64,
    nodes: usize,
}

/// Render the full codebase brief for `dir` as markdown.
pub fn brief(graph: &Graph, dir: &str) -> String {
    let model = Model::build(graph, dir);
    let mut out = String::new();
    let _ = writeln!(out, "# Codebase brief: {dir}\n");

    overview_section(graph, &model, &mut out);
    projects_section(dir, &mut out);
    architecture_section(&model, &mut out);
    entry_points_section(&model, &mut out);
    hotspots_section(&model, &mut out);
    cycles_section(&model, &mut out);
    synthesis_section(graph, &model, &mut out);

    out
}

/// The structured, machine-readable form of [`brief`]: the same deterministic
/// model, emitted as one JSON object (schema `trailtracker.brief/v1`) instead
/// of markdown. Shape:
///
/// ```text
/// {schema, command, dir,
///  overview: {nodes, edges, files, lines, languages: [{language, files, lines, nodes}]},
///  projects: null | {count, topology},
///  architecture: {generated_files_excluded,
///                 domains: [{name, kind, files, symbols, reason?}],
///                 largest_units: [{id, name, kind, symbols}],
///                 module_dependencies: [{from, to, references}],
///                 module_dependencies_omitted},
///  entry_points: {mains: [{id, name, kind, file}],
///                 public_api: [{id, name, kind, file, external_references,
///                               count_distinct?, duplicate_callers?}]},
///  hotspots: {fan_in: [{id, name, kind, file, count,
///                       count_distinct?, duplicate_callers?}],
///             fan_out: [{id, name, kind, file, count}]},
///  cycles: [[file, ...]],
///  synthesis: "plain-English paragraph"}
/// ```
///
/// `count_distinct` / `duplicate_callers` (an array of `{caller,
/// file_basename, files, references}`) appear only when stamped-boilerplate
/// callers inflate the raw count — see the duplicate-caller annotation in the
/// module docs — so output for repos without duplication is byte-identical to
/// before the fields existed.
///
/// Rankings, tie-breaks, and list caps ([`TOP_N`], [`DEP_MAP_N`]) are identical
/// to the markdown sections, so the two views never disagree.
pub fn brief_json(graph: &Graph, dir: &str) -> Json {
    let model = Model::build(graph, dir);

    // Overview.
    let total_files: usize = model.languages.values().map(|s| s.files).sum();
    let total_lines: u64 = model.languages.values().map(|s| s.lines).sum();
    let languages: Vec<Json> = model
        .languages
        .iter()
        .map(|(lang, s)| {
            Json::obj([
                ("language", Json::str(lang.clone())),
                ("files", s.files.into()),
                ("lines", s.lines.into()),
                ("nodes", s.nodes.into()),
            ])
        })
        .collect();
    let overview = Json::obj([
        ("nodes", graph.node_count().into()),
        ("edges", graph.edge_count().into()),
        ("files", total_files.into()),
        ("lines", total_lines.into()),
        ("languages", Json::Array(languages)),
    ]);

    // Services / projects (same source as `projects_section`; null when none).
    let project_graph = crate::brief_projects::analyze(Path::new(dir));
    let projects = if project_graph.projects.is_empty() {
        Json::Null
    } else {
        Json::obj([
            ("count", project_graph.projects.len().into()),
            (
                "topology",
                Json::str(project_graph.topo_summary().trim_end()),
            ),
        ])
    };

    // Architecture: same ranking as `architecture_section`.
    let mut contained: BTreeMap<&str, usize> = BTreeMap::new();
    for (child, file) in &model.owner_file {
        if child != file && !model.is_generated_file(file) {
            *contained.entry(file).or_default() += 1;
        }
    }
    let largest_units: Vec<Json> = rank_desc(&contained)
        .iter()
        .take(TOP_N)
        .map(|(count, id)| node_descriptor(&model, id, vec![("symbols", (*count).into())]))
        .collect();

    let mut deps: Vec<(usize, &(&str, &str))> =
        model.file_deps.iter().map(|(k, v)| (*v, k)).collect();
    deps.sort_by(|a, b| b.0.cmp(&a.0).then_with(|| a.1.cmp(b.1)));
    let module_dependencies: Vec<Json> = deps
        .iter()
        .take(DEP_MAP_N)
        .map(|(count, (from, to))| {
            Json::obj([
                ("from", Json::str(model.file_name(from))),
                ("to", Json::str(model.file_name(to))),
                ("references", (*count).into()),
            ])
        })
        .collect();
    let domains: Vec<Json> = model
        .domains
        .iter()
        .map(|d| {
            let mut pairs = vec![
                ("name", Json::str(d.name.clone())),
                ("kind", Json::str(d.kind)),
                ("files", d.files.into()),
                ("symbols", d.symbols.into()),
            ];
            if let Some(reason) = d.reason {
                pairs.push(("reason", Json::str(reason)));
            }
            Json::obj(pairs)
        })
        .collect();
    let architecture = Json::obj([
        ("generated_files_excluded", model.generated.len().into()),
        ("domains", Json::Array(domains)),
        ("largest_units", Json::Array(largest_units)),
        ("module_dependencies", Json::Array(module_dependencies)),
        (
            "module_dependencies_omitted",
            deps.len().saturating_sub(DEP_MAP_N).into(),
        ),
    ]);

    // Entry points: same filters as `entry_points_section`.
    let mains: Vec<Json> = model
        .mains
        .iter()
        .map(|id| node_descriptor(&model, id, Vec::new()))
        .collect();
    let public_api: Vec<Json> = rank_desc(&model.external_fan_in)
        .into_iter()
        .filter(|(_, id)| is_symbol(&model, id) && !model.owner_is_generated(id))
        .take(TOP_N)
        .map(|(count, id)| {
            let mut extras = vec![("external_references", count.into())];
            extras.extend(dup_json_fields(&model, id, count));
            node_descriptor(&model, id, extras)
        })
        .collect();
    let entry_points = Json::obj([
        ("mains", Json::Array(mains)),
        ("public_api", Json::Array(public_api)),
    ]);

    // Hotspots: same helper as `hotspots_section`. Only fan-in carries the
    // duplicate-caller annotation — the groups describe *inbound* references,
    // which say nothing about a symbol's own fan-out.
    let hotspot_list = |fan: &BTreeMap<&str, usize>, annotate_dups: bool| -> Json {
        Json::Array(
            top_hotspots(&model, fan)
                .iter()
                .map(|(count, id)| {
                    let mut extras = vec![("count", (*count).into())];
                    if annotate_dups {
                        extras.extend(dup_json_fields(&model, id, *count));
                    }
                    node_descriptor(&model, id, extras)
                })
                .collect(),
        )
    };
    let hotspots = Json::obj([
        ("fan_in", hotspot_list(&model.fan_in, true)),
        ("fan_out", hotspot_list(&model.fan_out, false)),
    ]);

    // Cycles: file display names, same order as `cycles_section`.
    let cycles: Vec<Json> = model
        .cycles
        .iter()
        .map(|cycle| {
            Json::Array(
                cycle
                    .iter()
                    .map(|f| Json::str(model.file_name(f)))
                    .collect(),
            )
        })
        .collect();

    // Synthesis: reuse the markdown renderer, minus its section header.
    let mut synthesis_md = String::new();
    synthesis_section(graph, &model, &mut synthesis_md);
    let synthesis = synthesis_md
        .trim_start_matches("## What this repo is")
        .trim()
        .to_string();

    Json::obj([
        ("schema", Json::str("trailtracker.brief/v1")),
        ("command", Json::str("brief")),
        ("dir", Json::str(dir)),
        ("overview", overview),
        ("projects", projects),
        ("architecture", architecture),
        ("entry_points", entry_points),
        ("hotspots", hotspots),
        ("cycles", Json::Array(cycles)),
        ("synthesis", Json::str(synthesis)),
    ])
}

/// JSON descriptor for a node id: `{id, name, kind, file?}` plus any
/// caller-supplied metric pairs. `file` is included for symbols whose owning
/// file is known (and skipped for File nodes, where `name` is already the path).
fn node_descriptor(model: &Model, id: &str, extras: Vec<(&'static str, Json)>) -> Json {
    let mut pairs: Vec<(&'static str, Json)> = vec![("id", Json::str(id))];
    if let Some(n) = model.by_id.get(id) {
        pairs.push(("name", Json::str(display_name(n))));
        pairs.push(("kind", Json::str(n.kind)));
        if n.kind != ont::FILE {
            if let Some(f) = model.owner_file.get(id) {
                pairs.push(("file", Json::str(model.file_name(f))));
            }
        }
    }
    pairs.extend(extras);
    Json::obj(pairs)
}

/// The optional duplicate-caller JSON fields for a reference count: empty for
/// undominated symbols (so existing consumers and goldens see byte-identical
/// output), or `count_distinct` plus a `duplicate_callers` array when stamped
/// boilerplate inflates the raw count.
fn dup_json_fields(model: &Model, id: &str, total: usize) -> Vec<(&'static str, Json)> {
    match model.dup_annotation(id, total) {
        None => Vec::new(),
        Some((distinct, groups)) => {
            let rows: Vec<Json> = groups
                .iter()
                .map(|g| {
                    Json::obj([
                        ("caller", Json::str(g.caller)),
                        ("file_basename", Json::str(g.basename)),
                        ("files", g.files.into()),
                        ("references", g.references.into()),
                    ])
                })
                .collect();
            vec![
                ("count_distinct", distinct.into()),
                ("duplicate_callers", Json::Array(rows)),
            ]
        }
    }
}

impl<'g> Model<'g> {
    fn build(graph: &'g Graph, dir: &str) -> Model<'g> {
        let by_id: BTreeMap<&str, &GraphNode> = graph.nodes().map(|n| (n.id.as_str(), n)).collect();

        // Generated code: classify each File node by path + first-1KB content
        // head (read from disk when available; path-only when not, e.g. in
        // synthetic tests). Deterministic given the same tree + graph.
        let mut generated: BTreeSet<&str> = BTreeSet::new();
        for n in graph.nodes() {
            if n.kind != ont::FILE {
                continue;
            }
            let path = match n.props.get("path") {
                Some(Json::Str(p)) => p.as_str(),
                _ => n.name.as_str(),
            };
            let head = std::fs::read(Path::new(dir).join(path))
                .ok()
                .map(|b| {
                    let end = b.len().min(1024);
                    String::from_utf8_lossy(&b[..end]).into_owned()
                })
                .unwrap_or_default();
            if crate::brief_generated::is_generated(path, &head) {
                generated.insert(n.id.as_str());
            }
        }

        // Languages: files/lines from File nodes, node tallies from any node
        // carrying a `language` property.
        let mut languages: BTreeMap<String, LangStats> = BTreeMap::new();
        for n in graph.nodes() {
            let lang = match n.props.get("language") {
                Some(Json::Str(s)) => s.clone(),
                _ if n.kind == ont::FILE => "(unknown)".to_string(),
                _ => continue,
            };
            let entry = languages.entry(lang).or_default();
            entry.nodes += 1;
            if n.kind == ont::FILE {
                entry.files += 1;
                entry.lines += prop_u64(n.props.get("lines"));
            }
        }

        // Containment parents (child → parent), preferring a File parent so a
        // method reached both by `File DECLARES fn` and `Type HAS_METHOD fn`
        // resolves to its file. First-seen wins among equals (edges iterate in
        // stable signature order), keeping the choice deterministic.
        let mut parent: BTreeMap<&str, &str> = BTreeMap::new();
        for e in graph.edges() {
            if e.kind != edge::CONTAINS && e.kind != edge::DECLARES && e.kind != edge::HAS_METHOD {
                continue;
            }
            let from_is_file = by_id.get(e.from.as_str()).map(|n| n.kind) == Some(ont::FILE);
            match parent.get(e.to.as_str()) {
                None => {
                    parent.insert(e.to.as_str(), e.from.as_str());
                }
                Some(existing) => {
                    let existing_is_file = by_id.get(existing).map(|n| n.kind) == Some(ont::FILE);
                    if from_is_file && !existing_is_file {
                        parent.insert(e.to.as_str(), e.from.as_str());
                    }
                }
            }
        }
        let resolve_file = |mut id: &'g str| -> Option<&'g str> {
            // Bounded walk: containment chains are shallow; the bound only
            // guards against a malformed cyclic containment.
            for _ in 0..64 {
                if by_id.get(id).map(|n| n.kind) == Some(ont::FILE) {
                    return Some(id);
                }
                id = parent.get(id)?;
            }
            None
        };
        let mut owner_file: BTreeMap<&str, &str> = BTreeMap::new();
        for n in graph.nodes() {
            if let Some(f) = resolve_file(n.id.as_str()) {
                owner_file.insert(n.id.as_str(), f);
            }
        }

        // Dependency fan-in/fan-out and the cross-file dependency map.
        // Alongside the raw counts, group cross-file inbound references by
        // (caller file basename, caller symbol name): a same-named top-level
        // caller stamped across many same-named files is one templated file
        // copied per module, and counting each copy as an independent caller
        // manufactures fake hotspots. The raw counts stay untouched (every
        // edge is real); the groups feed the report annotations.
        let mut file_deps: BTreeMap<(&str, &str), usize> = BTreeMap::new();
        let mut fan_in: BTreeMap<&str, usize> = BTreeMap::new();
        let mut fan_out: BTreeMap<&str, usize> = BTreeMap::new();
        let mut external_fan_in: BTreeMap<&str, usize> = BTreeMap::new();
        // target → (basename, caller name) → (distinct caller files, refs).
        type GroupKey<'a> = (&'a str, &'a str);
        let mut caller_groups: BTreeMap<&str, BTreeMap<GroupKey, (BTreeSet<&str>, usize)>> =
            BTreeMap::new();
        for e in graph.edges() {
            if parent_relation(e.kind) != Some(relation::DEPENDS) {
                continue;
            }
            *fan_out.entry(e.from.as_str()).or_default() += 1;
            *fan_in.entry(e.to.as_str()).or_default() += 1;
            let (from_file, to_file) = (
                owner_file.get(e.from.as_str()).copied(),
                owner_file.get(e.to.as_str()).copied(),
            );
            if let (Some(ff), Some(tf)) = (from_file, to_file) {
                if ff != tf {
                    *file_deps.entry((ff, tf)).or_default() += 1;
                    *external_fan_in.entry(e.to.as_str()).or_default() += 1;
                    // Only symbol callers declared directly by their file
                    // qualify for duplicate grouping: boilerplate copies stamp
                    // top-level symbols, while convention-named methods (ten
                    // different `new`s on ten types) hang off distinct types
                    // and must not be mistaken for copies.
                    let caller = by_id.get(e.from.as_str()).copied();
                    let top_level = parent.get(e.from.as_str()).copied() == Some(ff);
                    if let Some(c) = caller {
                        if is_symbol_kind(c.kind) && top_level {
                            let base = by_id.get(ff).map(|f| file_basename(f)).unwrap_or(ff);
                            let (files, refs) = caller_groups
                                .entry(e.to.as_str())
                                .or_default()
                                .entry((base, c.name.as_str()))
                                .or_default();
                            files.insert(ff);
                            *refs += 1;
                        }
                    }
                }
            }
        }
        // Keep only groups spanning enough distinct files to be a template,
        // largest first (files desc, then references desc, then key asc).
        let mut dup_callers: BTreeMap<&str, Vec<DupCallerGroup>> = BTreeMap::new();
        for (target, groups) in caller_groups {
            let mut rows: Vec<DupCallerGroup> = groups
                .into_iter()
                .filter(|(_, (files, _))| files.len() >= DUP_CALLER_MIN_FILES)
                .map(|((basename, caller), (files, references))| DupCallerGroup {
                    caller,
                    basename,
                    files: files.len(),
                    references,
                })
                .collect();
            if rows.is_empty() {
                continue;
            }
            rows.sort_by(|a, b| {
                b.files
                    .cmp(&a.files)
                    .then_with(|| b.references.cmp(&a.references))
                    .then_with(|| (a.basename, a.caller).cmp(&(b.basename, b.caller)))
            });
            dup_callers.insert(target, rows);
        }

        // Likely mains.
        let mains: Vec<&str> = graph
            .nodes()
            .filter(|n| n.kind == ont::FUNCTION && n.name == "main")
            .map(|n| n.id.as_str())
            .collect();

        // Tarjan over the file-level dependency graph.
        let cycles = file_cycles(&file_deps);

        // Domain clusters (the same single-source-of-truth assignment the
        // domains/hierarchy views emit), summarized largest-first.
        let assignment = crate::extract::domains::assign_domains(graph);
        let mut domains: Vec<DomainRow> = assignment
            .domains
            .iter()
            .map(|(name, info)| DomainRow {
                name: name.clone(),
                kind: info.kind,
                reason: info.reason,
                files: info.file_count,
                symbols: info.symbol_count,
            })
            .collect();
        domains.sort_by(|a, b| b.symbols.cmp(&a.symbols).then_with(|| a.name.cmp(&b.name)));

        Model {
            by_id,
            languages,
            owner_file,
            file_deps,
            fan_in,
            fan_out,
            external_fan_in,
            dup_callers,
            mains,
            cycles,
            generated,
            domains,
        }
    }

    /// True if `file_id` is a generated File node.
    fn is_generated_file(&self, file_id: &str) -> bool {
        self.generated.contains(file_id)
    }

    /// True if the symbol `id` lives in a generated file (so it should not
    /// crowd the architecture signal — hotspots, API surface, largest units).
    fn owner_is_generated(&self, id: &str) -> bool {
        if self.generated.contains(id) {
            return true;
        }
        matches!(self.owner_file.get(id), Some(f) if self.generated.contains(f))
    }

    /// Human label for a node id: `path (Kind)` for files, `name (Kind, file)`
    /// for symbols with a known owning file, falling back to the raw id when
    /// the node is unknown.
    fn label(&self, id: &str) -> String {
        match self.by_id.get(id) {
            Some(n) if n.kind == ont::FILE => format!("`{}` ({})", display_name(n), n.kind),
            Some(n) => match self.owner_file.get(id) {
                Some(f) => format!("`{}` ({}, {})", n.name, n.kind, self.file_name(f)),
                None => format!("`{}` ({})", n.name, n.kind),
            },
            None => format!("`{id}`"),
        }
    }

    /// The display name of a file id (its `path` when known).
    fn file_name(&self, id: &str) -> String {
        match self.by_id.get(id) {
            Some(n) => display_name(n),
            None => id.to_string(),
        }
    }

    /// The duplicate-caller annotation for target `id` against a raw reference
    /// count `total`: the de-duplicated ("distinct") count — each stamped
    /// group collapsed to one caller — plus the groups themselves.
    ///
    /// `None` unless the stamped groups explain at least *half* of `total`:
    /// a hotspot is manufactured when duplication is the majority of its
    /// count (bio-mcp-client: 106 of 111), while a handful of same-named
    /// callers under a genuinely diverse hotspot (django: three `test_save`s
    /// in three `tests.py` under a 1910-reference symbol) is convention, not
    /// a template — annotating it would be its own credibility bug. Symbols
    /// below the bar render exactly as before.
    fn dup_annotation(&self, id: &str, total: usize) -> Option<(usize, &[DupCallerGroup<'g>])> {
        let groups = self.dup_callers.get(id)?;
        let stamped: usize = groups.iter().map(|g| g.references).sum();
        if stamped * 2 < total {
            return None;
        }
        let distinct = total.saturating_sub(stamped) + groups.len();
        Some((distinct, groups.as_slice()))
    }

    /// Markdown suffix for a fan-in / external-reference count: `" (D
    /// distinct: R reference(s) from `caller` stamped across N file(s) named
    /// `basename`; …)"`, or empty when no duplicate-caller group qualifies.
    /// At most [`DUP_GROUPS_SHOWN`] groups are spelled out (largest first);
    /// the rest are summarized so one annotation cannot swallow the line.
    fn dup_suffix(&self, id: &str, total: usize) -> String {
        match self.dup_annotation(id, total) {
            None => String::new(),
            Some((distinct, groups)) => {
                let mut parts: Vec<String> = groups
                    .iter()
                    .take(DUP_GROUPS_SHOWN)
                    .map(|g| {
                        format!(
                            "{} reference(s) from `{}` stamped across {} file(s) named `{}`",
                            g.references, g.caller, g.files, g.basename
                        )
                    })
                    .collect();
                if groups.len() > DUP_GROUPS_SHOWN {
                    parts.push(format!(
                        "… and {} more stamped group(s)",
                        groups.len() - DUP_GROUPS_SHOWN
                    ));
                }
                format!(" ({distinct} distinct: {})", parts.join("; "))
            }
        }
    }
}

/// The basename of a file node's display path (`get-schema.ts` for
/// `servers/x/src/tools/get-schema.ts`), tolerant of either separator.
fn file_basename(n: &GraphNode) -> &str {
    let full = match n.props.get("path") {
        Some(Json::Str(p)) if n.kind == ont::FILE => p.as_str(),
        _ => n.name.as_str(),
    };
    full.rsplit(['/', '\\']).next().unwrap_or(full)
}

/// A node's preferred display name: `path` for files when present, else `name`.
fn display_name(n: &GraphNode) -> String {
    match n.props.get("path") {
        Some(Json::Str(p)) if n.kind == ont::FILE => p.clone(),
        _ => n.name.clone(),
    }
}

fn overview_section(graph: &Graph, model: &Model, out: &mut String) {
    out.push_str("## Overview\n\n");
    let total_files: usize = model.languages.values().map(|s| s.files).sum();
    let total_lines: u64 = model.languages.values().map(|s| s.lines).sum();
    let _ = writeln!(
        out,
        "- {} nodes, {} edges — {} file(s), {} line(s)",
        graph.node_count(),
        graph.edge_count(),
        total_files,
        total_lines
    );
    out.push_str("\n### Languages\n\n");
    if model.languages.is_empty() {
        out.push_str("_none detected_\n");
    }
    for (lang, s) in &model.languages {
        let _ = writeln!(
            out,
            "- {lang} — {} file(s), {} line(s), {} node(s)",
            s.files, s.lines, s.nodes
        );
    }
    out.push('\n');
}

/// Service/project topology from `.csproj` files (the .NET solution shape).
/// Emitted only when projects are found, so non-.NET repos are unaffected.
fn projects_section(dir: &str, out: &mut String) {
    let graph = crate::brief_projects::analyze(Path::new(dir));
    if graph.projects.is_empty() {
        return;
    }
    let _ = writeln!(
        out,
        "## Services / projects\n\n{} project(s) — the solution/service topology:\n",
        graph.projects.len()
    );
    out.push_str("```\n");
    out.push_str(graph.topo_summary().trim_end());
    out.push_str("\n```\n\n");
}

fn architecture_section(model: &Model, out: &mut String) {
    out.push_str("## Architecture\n\n");

    if !model.generated.is_empty() {
        let _ = writeln!(
            out,
            "_{} generated file(s) (migrations, protos, designers) excluded from the signal below._\n",
            model.generated.len()
        );
    }

    // Largest containers: Package/Module/File ranked by directly contained
    // symbols (how many nodes resolve their containment parent to them).
    // Generated files are excluded so hand-written code leads.
    let mut contained: BTreeMap<&str, usize> = BTreeMap::new();
    for (child, file) in &model.owner_file {
        if child != file && !model.is_generated_file(file) {
            *contained.entry(file).or_default() += 1;
        }
    }
    // Domains: the structural clustering (bounded contexts), business
    // domains first, infrastructure groups (build/docs/generated/root
    // scaffolding) summarized on one line so they never crowd the signal.
    out.push_str("### Domains (structural clustering)\n\n");
    let business: Vec<&DomainRow> = model
        .domains
        .iter()
        .filter(|d| d.reason.is_none())
        .collect();
    if business.is_empty() {
        out.push_str("_none — no analyzable code clustered_\n");
    }
    for d in business.iter().take(TOP_N) {
        let _ = writeln!(
            out,
            "- {} — {} file(s), {} symbol(s)",
            d.name, d.files, d.symbols
        );
    }
    if business.len() > TOP_N {
        let _ = writeln!(out, "- … and {} more domain(s)", business.len() - TOP_N);
    }
    let infra: Vec<String> = model
        .domains
        .iter()
        .filter(|d| d.reason.is_some())
        .map(|d| format!("{} ({} file(s))", d.name, d.files))
        .collect();
    if !infra.is_empty() {
        let _ = writeln!(out, "\n_infrastructure groups: {}_", infra.join(", "));
    }
    out.push('\n');

    out.push_str("### Largest units (by contained symbols)\n\n");
    let ranked = rank_desc(&contained);
    if ranked.is_empty() {
        out.push_str("_none_\n");
    }
    for (count, id) in ranked.iter().take(TOP_N) {
        let _ = writeln!(out, "- {} — {count} symbol(s)", model.label(id));
    }

    out.push_str("\n### Module dependency map (cross-file references)\n\n");
    if model.file_deps.is_empty() {
        out.push_str("_none — no cross-file dependencies resolved_\n");
    }
    let mut deps: Vec<(usize, &(&str, &str))> =
        model.file_deps.iter().map(|(k, v)| (*v, k)).collect();
    deps.sort_by(|a, b| b.0.cmp(&a.0).then_with(|| a.1.cmp(b.1)));
    for (count, (from, to)) in deps.iter().take(DEP_MAP_N) {
        let _ = writeln!(
            out,
            "- {} -> {} — {count} reference(s)",
            model.file_name(from),
            model.file_name(to)
        );
    }
    if deps.len() > DEP_MAP_N {
        let _ = writeln!(
            out,
            "- … and {} more cross-file link(s)",
            deps.len() - DEP_MAP_N
        );
    }
    out.push('\n');
}

fn entry_points_section(model: &Model, out: &mut String) {
    out.push_str("## Entry points\n\n");

    out.push_str("### Likely mains\n\n");
    if model.mains.is_empty() {
        out.push_str("_none detected — likely a library_\n");
    }
    for id in &model.mains {
        let _ = writeln!(out, "- {}", model.label(id));
    }

    out.push_str("\n### Public API surface (referenced from outside their file)\n\n");
    let api: Vec<(usize, &str)> = rank_desc(&model.external_fan_in)
        .into_iter()
        .filter(|(_, id)| is_symbol(model, id) && !model.owner_is_generated(id))
        .take(TOP_N)
        .collect();
    if api.is_empty() {
        out.push_str("_none — no symbols are referenced across file boundaries_\n");
    }
    for (count, id) in &api {
        let _ = writeln!(
            out,
            "- {} — {count} external reference(s){}",
            model.label(id),
            model.dup_suffix(id, *count)
        );
    }
    out.push('\n');
}

fn hotspots_section(model: &Model, out: &mut String) {
    out.push_str("## Hotspots\n\n");

    out.push_str("### Highest fan-in (most depended upon — change ripples)\n\n");
    let fan_in = top_hotspots(model, &model.fan_in);
    if fan_in.is_empty() {
        out.push_str("_none_\n");
    }
    for (count, id) in &fan_in {
        let _ = writeln!(
            out,
            "- {} — fan-in {count}{}",
            model.label(id),
            model.dup_suffix(id, *count)
        );
    }

    out.push_str("\n### Highest fan-out (depends on the most — complexity)\n\n");
    let fan_out = top_hotspots(model, &model.fan_out);
    if fan_out.is_empty() {
        out.push_str("_none_\n");
    }
    for (count, id) in &fan_out {
        let _ = writeln!(out, "- {} — fan-out {count}", model.label(id));
    }
    out.push('\n');
}

fn cycles_section(model: &Model, out: &mut String) {
    out.push_str("## Dependency cycles\n\n");
    if model.cycles.is_empty() {
        out.push_str("_none — the file dependency graph is acyclic_\n\n");
        return;
    }
    for cycle in &model.cycles {
        let names: Vec<String> = cycle.iter().map(|f| model.file_name(f)).collect();
        let _ = writeln!(
            out,
            "- cycle of {} file(s): {}",
            cycle.len(),
            names.join(" <-> ")
        );
    }
    out.push('\n');
}

fn synthesis_section(graph: &Graph, model: &Model, out: &mut String) {
    out.push_str("## What this repo is\n\n");
    if graph.node_count() == 0 {
        out.push_str("An empty directory as far as TrailTracker can see: no analyzable source files were found.\n");
        return;
    }

    let total_files: usize = model.languages.values().map(|s| s.files).sum();
    let total_lines: u64 = model.languages.values().map(|s| s.lines).sum();
    let lang_count = model.languages.len();
    let primary = model
        .languages
        .iter()
        .max_by(|a, b| a.1.files.cmp(&b.1.files).then_with(|| b.0.cmp(a.0)))
        .map(|(l, _)| l.as_str())
        .unwrap_or("(unknown)");
    let language_phrase = if lang_count > 1 {
        format!("a polyglot codebase (mostly {primary}, {lang_count} languages)")
    } else {
        format!("a {primary} codebase")
    };

    let mut contained: BTreeMap<&str, usize> = BTreeMap::new();
    for (child, file) in &model.owner_file {
        if child != file && !model.is_generated_file(file) {
            *contained.entry(file).or_default() += 1;
        }
    }
    let core_phrase = match rank_desc(&contained).first() {
        Some((count, id)) => format!(
            " Its largest unit is {} with {count} symbol(s).",
            model.label(id)
        ),
        None => String::new(),
    };

    // Domain phrase: the structural clustering's business domains (the
    // infrastructure groups are named scaffolding, not what the repo *is*).
    let business: Vec<&DomainRow> = model
        .domains
        .iter()
        .filter(|d| d.reason.is_none())
        .collect();
    let domain_phrase = match business.len() {
        0 => String::new(),
        1 => format!(" Its code clusters into one domain: {}.", business[0].name),
        n => {
            let top: Vec<&str> = business.iter().take(3).map(|d| d.name.as_str()).collect();
            format!(
                " Its code clusters into {n} domains, led by {}.",
                top.join(", ")
            )
        }
    };

    let entry_phrase = if model.mains.is_empty() {
        match rank_desc(&model.external_fan_in)
            .into_iter()
            .find(|(_, id)| is_symbol(model, id))
        {
            Some((_, id)) => format!(
                " No `main` was detected, so it reads as a library whose public surface is led by {}.",
                model.label(id)
            ),
            None => " No `main` was detected.".to_string(),
        }
    } else {
        let files: Vec<String> = model
            .mains
            .iter()
            .filter_map(|id| model.owner_file.get(id).map(|f| model.file_name(f)))
            .collect();
        if files.is_empty() {
            " Execution enters at a `main` function.".to_string()
        } else {
            format!(" Execution enters at `main` in {}.", files.join(", "))
        }
    };

    let ripple_phrase = match top_hotspots(model, &model.fan_in).first() {
        Some((count, id)) => {
            let dup = match model.dup_annotation(id, *count) {
                Some((distinct, _)) => {
                    format!(", {distinct} distinct once stamped boilerplate copies collapse")
                }
                None => String::new(),
            };
            format!(
                " The most depended-upon symbol is {} (fan-in {count}{dup}) — changes there ripple widest",
                model.label(id)
            )
        }
        None => String::new(),
    };
    let complexity_phrase = match top_hotspots(model, &model.fan_out).first() {
        Some((count, id)) if !ripple_phrase.is_empty() => format!(
            "; {} carries the most outbound complexity (fan-out {count}).",
            model.label(id)
        ),
        Some((count, id)) => format!(
            " {} carries the most outbound complexity (fan-out {count}).",
            model.label(id)
        ),
        None if !ripple_phrase.is_empty() => ".".to_string(),
        None => String::new(),
    };

    let cycle_phrase = if model.cycles.is_empty() {
        " The file dependency graph is acyclic — no dependency cycles."
    } else {
        " Dependency cycles knot the file graph — see the cycles section before refactoring."
    };

    let _ = writeln!(
        out,
        "This repo is {language_phrase}: {total_files} file(s), {total_lines} line(s), \
modeled as {} nodes and {} edges.{core_phrase}{domain_phrase}{entry_phrase}{ripple_phrase}{complexity_phrase}{cycle_phrase}",
        graph.node_count(),
        graph.edge_count()
    );
}

/// True when `id` is a project symbol worth listing as API / hotspot — not an
/// unresolved placeholder, an external dependency, or a scope node.
fn is_symbol(model: &Model, id: &str) -> bool {
    matches!(model.by_id.get(id).map(|n| n.kind), Some(k) if is_symbol_kind(k))
}

/// The node kinds [`is_symbol`] accepts (shared with duplicate-caller
/// grouping, which sees the node itself rather than an id).
fn is_symbol_kind(kind: &str) -> bool {
    matches!(kind, ont::FUNCTION | ont::TYPE | ont::CONSTANT | ont::MACRO)
}

/// Rank a count map descending, ties broken by id ascending.
fn rank_desc<'a>(counts: &BTreeMap<&'a str, usize>) -> Vec<(usize, &'a str)> {
    let mut ranked: Vec<(usize, &str)> = counts.iter().map(|(id, c)| (*c, *id)).collect();
    ranked.sort_by(|a, b| b.0.cmp(&a.0).then_with(|| a.1.cmp(b.1)));
    ranked
}

/// The top hotspot symbols from a fan map: project symbols only (placeholders
/// like `UnresolvedSymbol` / `ExternalDependency` are not actionable).
fn top_hotspots<'a>(model: &Model<'a>, fan: &BTreeMap<&'a str, usize>) -> Vec<(usize, &'a str)> {
    rank_desc(fan)
        .into_iter()
        .filter(|(_, id)| is_symbol(model, id) && !model.owner_is_generated(id))
        .take(TOP_N)
        .collect()
}

/// Strongly connected components (size > 1) of the file dependency graph,
/// via iterative Tarjan. Members and the cycle list are sorted for determinism.
fn file_cycles<'g>(file_deps: &BTreeMap<(&'g str, &'g str), usize>) -> Vec<Vec<&'g str>> {
    // Index the files deterministically (BTreeMap keys are sorted).
    let mut index_of: BTreeMap<&str, usize> = BTreeMap::new();
    for (from, to) in file_deps.keys() {
        let next = index_of.len();
        index_of.entry(from).or_insert(next);
        let next = index_of.len();
        index_of.entry(to).or_insert(next);
    }
    let n = index_of.len();
    let mut files: Vec<&str> = vec![""; n];
    for (f, i) in &index_of {
        files[*i] = f;
    }
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (from, to) in file_deps.keys() {
        adj[index_of[from]].push(index_of[to]);
    }
    for targets in &mut adj {
        targets.sort_unstable();
        targets.dedup();
    }

    // Iterative Tarjan (explicit frame stack; safe on deep graphs).
    const UNVISITED: usize = usize::MAX;
    let mut index = vec![UNVISITED; n];
    let mut low = vec![0usize; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut counter = 0usize;
    let mut sccs: Vec<Vec<usize>> = Vec::new();

    for start in 0..n {
        if index[start] != UNVISITED {
            continue;
        }
        let mut frames: Vec<(usize, usize)> = vec![(start, 0)];
        while let Some(frame) = frames.last_mut() {
            let (v, child) = *frame;
            if child == 0 {
                index[v] = counter;
                low[v] = counter;
                counter += 1;
                stack.push(v);
                on_stack[v] = true;
            }
            if child < adj[v].len() {
                frame.1 += 1;
                let w = adj[v][child];
                if index[w] == UNVISITED {
                    frames.push((w, 0));
                } else if on_stack[w] {
                    low[v] = low[v].min(index[w]);
                }
            } else {
                frames.pop();
                if let Some(&(p, _)) = frames.last() {
                    low[p] = low[p].min(low[v]);
                }
                if low[v] == index[v] {
                    let mut scc = Vec::new();
                    loop {
                        let w = stack.pop().expect("Tarjan stack underflow");
                        on_stack[w] = false;
                        scc.push(w);
                        if w == v {
                            break;
                        }
                    }
                    if scc.len() > 1 {
                        sccs.push(scc);
                    }
                }
            }
        }
    }

    let mut cycles: Vec<Vec<&str>> = sccs
        .into_iter()
        .map(|scc| {
            let mut names: Vec<&str> = scc.into_iter().map(|i| files[i]).collect();
            names.sort_unstable();
            names
        })
        .collect();
    cycles.sort();
    cycles
}

/// A `Json` property rendered as a `u64`, tolerating `U64`/`I64`, else `0`.
fn prop_u64(v: Option<&Json>) -> u64 {
    match v {
        Some(Json::U64(n)) => *n,
        Some(Json::I64(n)) if *n >= 0 => *n as u64,
        _ => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A hand-built two-file "app": `main.rs` declares `main` which calls
    /// `helper` in `util.rs`; when `with_cycle` is set, `util.rs` also calls
    /// back into `main.rs` (a deliberate file-level cycle). `Widget` in
    /// `util.rs` is used from `main.rs`, so it is public API surface.
    fn sample_with(with_cycle: bool) -> Graph {
        let mut g = Graph::new();
        g.upsert_node(
            "file::src/main.rs",
            ont::FILE,
            "main.rs",
            vec![
                ("language", Json::str("rust")),
                ("lines", Json::U64(10)),
                ("path", Json::str("src/main.rs")),
            ],
        );
        g.upsert_node(
            "file::src/util.rs",
            ont::FILE,
            "util.rs",
            vec![
                ("language", Json::str("rust")),
                ("lines", Json::U64(20)),
                ("path", Json::str("src/util.rs")),
            ],
        );
        g.upsert_node(
            "fn::crate::main#1",
            ont::FUNCTION,
            "main",
            vec![("language", Json::str("rust"))],
        );
        g.upsert_node(
            "fn::crate::tick#5",
            ont::FUNCTION,
            "tick",
            vec![("language", Json::str("rust"))],
        );
        g.upsert_node(
            "fn::crate::util::helper#3",
            ont::FUNCTION,
            "helper",
            vec![("language", Json::str("rust"))],
        );
        g.upsert_node(
            "type::crate::util::Widget",
            ont::TYPE,
            "Widget",
            vec![("language", Json::str("rust"))],
        );
        g.add_edge(
            "file::src/main.rs",
            edge::DECLARES,
            "fn::crate::main#1",
            vec![],
        );
        g.add_edge(
            "file::src/main.rs",
            edge::DECLARES,
            "fn::crate::tick#5",
            vec![],
        );
        g.add_edge(
            "file::src/util.rs",
            edge::DECLARES,
            "fn::crate::util::helper#3",
            vec![],
        );
        g.add_edge(
            "file::src/util.rs",
            edge::DECLARES,
            "type::crate::util::Widget",
            vec![],
        );
        // main -> helper (cross-file), main uses Widget (cross-file),
        // helper -> tick (cross-file, closes the file cycle).
        g.add_edge(
            "fn::crate::main#1",
            edge::CALLS,
            "fn::crate::util::helper#3",
            vec![],
        );
        g.add_edge(
            "fn::crate::main#1",
            edge::USES_TYPE,
            "type::crate::util::Widget",
            vec![],
        );
        if with_cycle {
            g.add_edge(
                "fn::crate::util::helper#3",
                edge::CALLS,
                "fn::crate::tick#5",
                vec![],
            );
        }
        g
    }

    fn sample() -> Graph {
        sample_with(true)
    }

    #[test]
    fn brief_has_all_sections() {
        let md = brief(&sample(), "sample");
        for section in [
            "# Codebase brief: sample",
            "## Overview",
            "### Languages",
            "## Architecture",
            "### Largest units",
            "### Module dependency map",
            "## Entry points",
            "### Likely mains",
            "### Public API surface",
            "## Hotspots",
            "### Highest fan-in",
            "### Highest fan-out",
            "## Dependency cycles",
            "## What this repo is",
        ] {
            assert!(md.contains(section), "missing `{section}` in:\n{md}");
        }
    }

    #[test]
    fn brief_finds_main_language_and_api_surface() {
        let md = brief(&sample(), "sample");
        assert!(md.contains("- rust — 2 file(s), 30 line(s)"), "{md}");
        assert!(
            md.contains("`main` (Function, src/main.rs)"),
            "main not attributed to its file:\n{md}"
        );
        // Widget and helper are referenced from outside util.rs.
        assert!(
            md.contains("`Widget` (Type, src/util.rs) — 1 external reference(s)"),
            "{md}"
        );
        assert!(
            md.contains("`helper` (Function, src/util.rs) — 1 external reference(s)"),
            "{md}"
        );
        // Synthesis names the entry point.
        assert!(
            md.contains("Execution enters at `main` in src/main.rs."),
            "{md}"
        );
    }

    #[test]
    fn brief_reports_file_cycle() {
        let md = brief(&sample(), "sample");
        assert!(
            md.contains("- cycle of 2 file(s): src/main.rs <-> src/util.rs"),
            "cycle not reported:\n{md}"
        );
        assert!(md.contains("Dependency cycles knot the file graph"), "{md}");
    }

    #[test]
    fn brief_without_cycle_says_none() {
        let md = brief(&sample_with(false), "sample");
        assert!(
            md.contains("_none — the file dependency graph is acyclic_"),
            "{md}"
        );
        assert!(md.contains("no dependency cycles"), "{md}");
    }

    #[test]
    fn brief_is_deterministic() {
        let g = sample();
        assert_eq!(brief(&g, "sample"), brief(&g, "sample"));
    }

    /// A repo where one shared function is called from `n` copies of the same
    /// boilerplate file: `<dir>/reg.ts` each declaring a top-level `register`
    /// that calls `createHandler` in `lib.ts` (the bio-mcp-client shape, where
    /// 106 `get-schema.ts` copies each declare `registerGetSchema`).
    fn stamped_sample(n: usize) -> Graph {
        let mut g = Graph::new();
        g.upsert_node(
            "file::lib.ts",
            ont::FILE,
            "lib.ts",
            vec![
                ("language", Json::str("typescript")),
                ("lines", Json::U64(10)),
                ("path", Json::str("lib.ts")),
            ],
        );
        g.upsert_node(
            "fn::lib::createHandler",
            ont::FUNCTION,
            "createHandler",
            vec![("language", Json::str("typescript"))],
        );
        g.add_edge(
            "file::lib.ts",
            edge::DECLARES,
            "fn::lib::createHandler",
            vec![],
        );
        for i in 0..n {
            let file_id = format!("file::srv{i}/reg.ts");
            let fn_id = format!("fn::srv{i}::register");
            g.upsert_node(
                &file_id,
                ont::FILE,
                "reg.ts",
                vec![
                    ("language", Json::str("typescript")),
                    ("lines", Json::U64(5)),
                    ("path", Json::str(format!("srv{i}/reg.ts"))),
                ],
            );
            g.upsert_node(
                &fn_id,
                ont::FUNCTION,
                "register",
                vec![("language", Json::str("typescript"))],
            );
            g.add_edge(&file_id, edge::DECLARES, &fn_id, vec![]);
            g.add_edge(&fn_id, edge::CALLS, "fn::lib::createHandler", vec![]);
        }
        g
    }

    #[test]
    fn brief_annotates_stamped_boilerplate_callers() {
        let md = brief(&stamped_sample(3), "stamped");
        // Raw fan-in stays faithful (all 3 edges are real); the annotation
        // surfaces the duplication and the de-duplicated count.
        assert!(
            md.contains(
                "`createHandler` (Function, lib.ts) — fan-in 3 \
(1 distinct: 3 reference(s) from `register` stamped across 3 file(s) named `reg.ts`)"
            ),
            "fan-in annotation missing:\n{md}"
        );
        // The public API surface carries the same annotation.
        assert!(
            md.contains(
                "`createHandler` (Function, lib.ts) — 3 external reference(s) \
(1 distinct: 3 reference(s) from `register` stamped across 3 file(s) named `reg.ts`)"
            ),
            "public API annotation missing:\n{md}"
        );
        // The synthesis paragraph does not repeat the inflated number alone.
        assert!(
            md.contains("(fan-in 3, 1 distinct once stamped boilerplate copies collapse)"),
            "synthesis annotation missing:\n{md}"
        );
    }

    #[test]
    fn brief_json_carries_duplicate_caller_fields() {
        let json = brief_json(&stamped_sample(3), "stamped").to_line();
        assert!(json.contains("\"count_distinct\":1"), "{json}");
        assert!(json.contains("\"duplicate_callers\":["), "{json}");
        assert!(json.contains("\"file_basename\":\"reg.ts\""), "{json}");
        assert!(json.contains("\"caller\":\"register\""), "{json}");
        // Repos without duplication keep the pre-annotation schema exactly.
        let clean = brief_json(&sample(), "sample").to_line();
        assert!(!clean.contains("count_distinct"), "{clean}");
        assert!(!clean.contains("duplicate_callers"), "{clean}");
    }

    #[test]
    fn brief_does_not_flag_two_same_named_files() {
        // Two same-named files can be coincidence, not a template.
        let md = brief(&stamped_sample(2), "pair");
        assert!(
            md.contains("`createHandler` (Function, lib.ts) — fan-in 2\n"),
            "{md}"
        );
        assert!(!md.contains("distinct:"), "{md}");
    }

    #[test]
    fn brief_does_not_flag_minority_duplication() {
        // Three stamped copies under a symbol that is mostly referenced by
        // genuinely distinct callers (4 of 7) stay unannotated: convention
        // noise under a diverse hotspot is not a manufactured hotspot.
        let mut g = stamped_sample(3);
        for i in 0..4 {
            let file_id = format!("file::app{i}/caller{i}.ts");
            let fn_id = format!("fn::app{i}::caller{i}");
            g.upsert_node(
                &file_id,
                ont::FILE,
                format!("caller{i}.ts"),
                vec![
                    ("language", Json::str("typescript")),
                    ("lines", Json::U64(5)),
                    ("path", Json::str(format!("app{i}/caller{i}.ts"))),
                ],
            );
            g.upsert_node(
                &fn_id,
                ont::FUNCTION,
                format!("caller{i}"),
                vec![("language", Json::str("typescript"))],
            );
            g.add_edge(&file_id, edge::DECLARES, &fn_id, vec![]);
            g.add_edge(&fn_id, edge::CALLS, "fn::lib::createHandler", vec![]);
        }
        let md = brief(&g, "minority");
        assert!(
            md.contains("`createHandler` (Function, lib.ts) — fan-in 7\n"),
            "{md}"
        );
        assert!(!md.contains("distinct:"), "{md}");
    }

    #[test]
    fn brief_does_not_flag_convention_named_methods() {
        // Ten types each with a `new` method in files named `mod.rs` are ten
        // different methods, not copies: methods hang off their type (not the
        // file), so the top-level gate must exclude them.
        let mut g = Graph::new();
        g.upsert_node(
            "file::lib.rs",
            ont::FILE,
            "lib.rs",
            vec![
                ("language", Json::str("rust")),
                ("lines", Json::U64(10)),
                ("path", Json::str("lib.rs")),
            ],
        );
        g.upsert_node(
            "fn::lib::shared",
            ont::FUNCTION,
            "shared",
            vec![("language", Json::str("rust"))],
        );
        g.add_edge("file::lib.rs", edge::DECLARES, "fn::lib::shared", vec![]);
        for i in 0..3 {
            let file_id = format!("file::m{i}/mod.rs");
            let ty_id = format!("type::m{i}::Widget{i}");
            let new_id = format!("fn::m{i}::Widget{i}::new");
            g.upsert_node(
                &file_id,
                ont::FILE,
                "mod.rs",
                vec![
                    ("language", Json::str("rust")),
                    ("lines", Json::U64(5)),
                    ("path", Json::str(format!("m{i}/mod.rs"))),
                ],
            );
            g.upsert_node(
                &ty_id,
                ont::TYPE,
                format!("Widget{i}"),
                vec![("language", Json::str("rust"))],
            );
            g.upsert_node(
                &new_id,
                ont::FUNCTION,
                "new",
                vec![("language", Json::str("rust"))],
            );
            g.add_edge(&file_id, edge::DECLARES, &ty_id, vec![]);
            g.add_edge(&ty_id, edge::HAS_METHOD, &new_id, vec![]);
            g.add_edge(&new_id, edge::CALLS, "fn::lib::shared", vec![]);
        }
        let md = brief(&g, "methods");
        assert!(
            md.contains("`shared` (Function, lib.rs) — fan-in 3\n"),
            "{md}"
        );
        assert!(!md.contains("distinct:"), "{md}");
    }

    #[test]
    fn brief_on_empty_graph_is_calm() {
        let md = brief(&Graph::new(), "empty");
        assert!(md.contains("## What this repo is"));
        assert!(md.contains("no analyzable source files"), "{md}");
        assert!(md.contains("_none detected_"), "{md}");
    }
}
