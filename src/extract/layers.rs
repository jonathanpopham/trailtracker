//! The layers extractor: recover the **architectural layer** view from the
//! base graph and flag dependency-direction violations.
//!
//! Clean architecture arranges a codebase as an onion: Domain at the core,
//! Application around it, Infrastructure and Presentation in the outer rings.
//! Dependencies must point **inward** — outer layers may depend on inner ones,
//! never the reverse. This extractor projects exactly that view:
//!
//! - **Unit** — a coarse owner for every node, derived from its owning
//!   [`File`]'s `path`: the top project/namespace segment (e.g.
//!   `src/Ordering.Domain/Order.cs` → unit `Ordering.Domain`). Symbols are
//!   resolved to their file by walking [`CONTAINMENT`] parents (`CONTAINS` /
//!   `DECLARES` / `HAS_METHOD`), the same walk `brief.rs` uses. When one
//!   non-test unit owns a strict majority of the repo's files (the
//!   single-package shape: `django/…`, `alacritty/…`), that unit is refined
//!   one directory level (`django` → `django/db`, `django/views`, …) so the
//!   layer view has structure to work with; multi-project repos are
//!   untouched.
//! - **Layer** — inferred per unit from its **archetype mix** (primary
//!   signal), with the unit-name convention as a secondary hint. Every member
//!   [`Type`]/[`Function`] symbol is classified with the shared
//!   [`archetypes`] rule table (using the declaring file's path for the
//!   location signals), and each archetype votes for a layer:
//!   Controller/Middleware/EntryPoint → Presentation;
//!   Handler/Command/Query/Service/Factory → Application;
//!   Aggregate/Entity/ValueObject/DomainEvent → Domain;
//!   Repository/Migration → Infrastructure; Test/Mock → Test; all other
//!   archetypes abstain. A unit whose classifiable symbols are majority-Test
//!   is a test unit; otherwise the Test vote is dropped (tests living beside
//!   production code — `src/test/java`, `*_test.go`, `mod tests` — must not
//!   swamp the module) and a unique plurality among the core layers wins; on
//!   a tie the name-convention hint decides (case-insensitive substring,
//!   first match wins: `.domain` → Domain; `.application` | `.apis` |
//!   `.appservices` → Application; `.infrastructure` | `.persistence` |
//!   `.data` → Infrastructure; `.api` | `.web` | `.presentation` | `.ui` |
//!   `.mvc` → Presentation; `.tests` | `.test` or a `tests`/`test` suffix →
//!   Test); with no votes the name hint stands alone. A unit with neither
//!   signal falls to the **dependency topology**: a unit many units depend
//!   on while it depends on few is inner (Domain), one that depends on many
//!   while few depend on it is outer (Presentation), anything else is
//!   Shared. This keeps the pass meaningful on codebases that don't use
//!   `.Domain`/`.Infrastructure`/`.API` project naming — or OO role naming
//!   at all — instead of silently mapping everything to Shared.
//! - **Layer dependency graph** — every base-graph [`DEPENDS`]-family or
//!   [`SPECIALIZES`]-family edge (inheritance couples at least as hard as a
//!   call) whose endpoints resolve to *different* units contributes to a
//!   layer → layer `DEPENDS_ON` edge, with a `count`.
//! - **Violations** — the standard clean-arch rule: Domain must depend on
//!   nothing but Domain/Shared; Application may depend on Domain/Shared;
//!   Infrastructure and Presentation may depend inward. Ranks: Domain(1) <
//!   Application(2) < Infrastructure(3) < Presentation(4); an edge from a
//!   more-inner layer to a more-outer one is flagged `violation: true`
//!   (especially Domain → Application/Infrastructure/Presentation and
//!   Application → Presentation). Test and Shared never violate, in either
//!   direction.
//!
//! The derived graph carries one [`Module`] node per layer (tagged
//! `view: "layers"`, with `unit_count`/`symbol_count`), one [`Module`] node
//! per unit (tagged with its `layer`), layer `CONTAINS` unit edges, and the
//! counted layer → layer `DEPENDS_ON` edges. The pass is a pure, deterministic
//! function of the base graph: it walks the `BTreeMap`-ordered node/edge
//! iterators and writes through the sorted, de-duplicating [`Graph`] API, so
//! the output is byte-stable across runs. The base graph is never mutated.
//!
//! [`File`]: crate::ir::ontology::node::FILE
//! [`Type`]: crate::ir::ontology::node::TYPE
//! [`Function`]: crate::ir::ontology::node::FUNCTION
//! [`Module`]: crate::ir::ontology::node::MODULE
//! [`CONTAINMENT`]: crate::ir::ontology::relation::CONTAINMENT
//! [`DEPENDS`]: crate::ir::ontology::relation::DEPENDS
//! [`SPECIALIZES`]: crate::ir::ontology::relation::SPECIALIZES
//! [`archetypes`]: super::archetypes

use std::collections::{BTreeMap, BTreeSet};

use crate::core::json::Json;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont, parent_relation, relation};

use super::archetypes::{archetype, classify_with, SymbolFacts, RULES};
use super::Extractor;

/// Property key marking a node as belonging to the layers view.
const VIEW: &str = "layers";

/// The clean-architecture layers, innermost first.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Layer {
    Domain,
    Application,
    Infrastructure,
    Presentation,
    Test,
    Shared,
}

impl Layer {
    /// Every layer, in the stable declaration (onion) order.
    const ALL: [Layer; 6] = [
        Layer::Domain,
        Layer::Application,
        Layer::Infrastructure,
        Layer::Presentation,
        Layer::Test,
        Layer::Shared,
    ];

    /// The layer named by a [`Layer::name`] string, `None` for anything else.
    fn by_name(name: &str) -> Option<Layer> {
        Layer::ALL.into_iter().find(|l| l.name() == name)
    }

    /// Stable display name (also used in node ids and `layer` props).
    fn name(self) -> &'static str {
        match self {
            Layer::Domain => "Domain",
            Layer::Application => "Application",
            Layer::Infrastructure => "Infrastructure",
            Layer::Presentation => "Presentation",
            Layer::Test => "Test",
            Layer::Shared => "Shared",
        }
    }

    /// Onion rank, innermost = 1. `None` for Test/Shared, which sit outside
    /// the dependency-direction rule entirely.
    fn rank(self) -> Option<u8> {
        match self {
            Layer::Domain => Some(1),
            Layer::Application => Some(2),
            Layer::Infrastructure => Some(3),
            Layer::Presentation => Some(4),
            Layer::Test | Layer::Shared => None,
        }
    }
}

/// The canonical layer names, in onion order — the vocabulary spec-driven
/// rules (`arch-verify`, ADR-0005) validate against. Kept in sync with
/// [`Layer::ALL`] by a unit test.
pub const LAYER_NAMES: [&str; 6] = [
    "Domain",
    "Application",
    "Infrastructure",
    "Presentation",
    "Test",
    "Shared",
];

/// The layer an archetype votes for, or `None` for archetypes that carry no
/// layer information (Interface, Dto, Enum, Configuration, Unclassified, …).
fn layer_of_archetype(arch: &str) -> Option<Layer> {
    match arch {
        archetype::CONTROLLER | archetype::MIDDLEWARE | archetype::ENTRY_POINT => {
            Some(Layer::Presentation)
        }
        archetype::HANDLER
        | archetype::COMMAND
        | archetype::QUERY
        | archetype::SERVICE
        | archetype::FACTORY => Some(Layer::Application),
        archetype::AGGREGATE
        | archetype::ENTITY
        | archetype::VALUE_OBJECT
        | archetype::DOMAIN_EVENT => Some(Layer::Domain),
        archetype::REPOSITORY | archetype::MIGRATION => Some(Layer::Infrastructure),
        archetype::TEST | archetype::MOCK => Some(Layer::Test),
        _ => None,
    }
}

/// Decide a unit's layer from its archetype votes (primary signal) and the
/// name-convention hint (secondary).
///
/// Test votes are special-cased for mixed units (Q-LAY-2): a Maven/Go/Rust
/// module keeps its tests *beside* its production code (`src/test/java`,
/// `*_test.go`, `mod tests`), and because every test symbol votes while only
/// a fraction of production symbols do, the Test vote swamped whole
/// production modules (dubbo: 15/17 units "Test"). So: a unit whose
/// classifiable symbols are majority-Test **is** a test unit; otherwise the
/// Test vote is dropped and the unique plurality among the core layers wins.
/// On a tie the name hint decides (`Shared` when the name says nothing); with
/// no core votes at all the name hint stands. `members` is the unit's
/// [`Type`]/[`Function`] symbol count — the vote-eligible population.
///
/// [`Type`]: crate::ir::ontology::node::TYPE
/// [`Function`]: crate::ir::ontology::node::FUNCTION
fn decide_layer(name_hint: Layer, votes: Option<&BTreeMap<Layer, u64>>, members: u64) -> Layer {
    let Some(votes) = votes.filter(|v| !v.is_empty()) else {
        return name_hint;
    };
    let test = votes.get(&Layer::Test).copied().unwrap_or(0);
    // A unit *named* as a test unit with any test code stays Test — the
    // convention is explicit; entrypoints/enums inside a test harness must
    // not out-vote it.
    if name_hint == Layer::Test && test > 0 {
        return Layer::Test;
    }
    if test * 2 > members {
        return Layer::Test;
    }
    let core: BTreeMap<Layer, u64> = votes
        .iter()
        .filter(|(l, _)| **l != Layer::Test)
        .map(|(l, c)| (*l, *c))
        .collect();
    if core.is_empty() {
        return name_hint;
    }
    let max = core.values().copied().max().unwrap_or(0);
    let mut winners = core.iter().filter(|(_, c)| **c == max).map(|(l, _)| *l);
    let first = winners.next().expect("core votes are non-empty");
    if winners.next().is_none() {
        first
    } else {
        name_hint
    }
}

/// Classify a unit name into a layer by naming convention. Case-insensitive
/// substring match, first match in the fixed convention order wins (so
/// `.apis` → Application is tested before `.api` → Presentation). Used as the
/// secondary hint behind the archetype-mix vote.
fn classify_by_name(unit: &str) -> Layer {
    let u = unit.to_ascii_lowercase();
    if u.contains(".domain") {
        Layer::Domain
    } else if u.contains(".application") || u.contains(".apis") || u.contains(".appservices") {
        Layer::Application
    } else if u.contains(".infrastructure") || u.contains(".persistence") || u.contains(".data") {
        Layer::Infrastructure
    } else if u.contains(".api")
        || u.contains(".web")
        || u.contains(".presentation")
        || u.contains(".ui")
        || u.contains(".mvc")
    {
        Layer::Presentation
    } else if u.contains(".tests")
        || u.contains(".test")
        || u.ends_with("tests")
        || u.ends_with("test")
    {
        Layer::Test
    } else {
        Layer::Shared
    }
}

/// Is a `from`-layer → `to`-layer dependency a direction violation?
/// Violation iff both layers are ranked and the source is more *inner* than
/// the target (dependencies must point inward). Test and Shared are unranked
/// and never violate.
fn is_violation(from: Layer, to: Layer) -> bool {
    match (from.rank(), to.rank()) {
        (Some(f), Some(t)) => f < t,
        _ => false,
    }
}

/// Derive the unit (top project/namespace segment) from a file path:
/// `src/Ordering.Domain/Order.cs` → `Ordering.Domain`. Leading scaffold
/// segments (`src`, `source`, `lib`, `libs`) are skipped; if nothing but
/// scaffold precedes the filename the last scaffold segment is the unit, and
/// a bare filename maps to `(root)`.
fn unit_of_path(path: &str) -> String {
    let mut dirs: Vec<&str> = path.split(['/', '\\']).filter(|s| !s.is_empty()).collect();
    // Drop the filename; only directories name a unit.
    dirs.pop();
    let mut last_scaffold: Option<&str> = None;
    for seg in dirs {
        if is_scaffold_segment(seg) {
            last_scaffold = Some(seg);
        } else {
            return seg.to_string();
        }
    }
    last_scaffold.unwrap_or("(root)").to_string()
}

/// A path segment that scaffolds source trees without naming a unit.
fn is_scaffold_segment(seg: &str) -> bool {
    matches!(
        seg.to_ascii_lowercase().as_str(),
        "src" | "source" | "lib" | "libs"
    )
}

/// Refine a path's unit one directory level below `unit`: the next
/// non-scaffold directory after the unit segment, as `unit/child`
/// (`django/db/models/base.py` → `django/db`;
/// `alacritty/src/renderer/rects.rs` → `alacritty/renderer`). Files directly
/// inside the unit (or with only scaffold below it) keep the plain unit.
fn refine_unit_of_path(path: &str, unit: &str) -> String {
    let mut dirs: Vec<&str> = path.split(['/', '\\']).filter(|s| !s.is_empty()).collect();
    dirs.pop(); // the filename never names a unit
    let mut seen_unit = false;
    for seg in dirs {
        if !seen_unit {
            seen_unit = seg == unit;
            continue;
        }
        if !is_scaffold_segment(seg) {
            return format!("{unit}/{seg}");
        }
    }
    unit.to_string()
}

/// The core unit/layer assignment, exposed so other passes (the hierarchy
/// extractor) consume the *same* placement the layers view emits — one source
/// of truth, never a re-derivation.
#[derive(Clone, Debug, Default)]
pub struct LayerAssignment {
    /// File node id → its unit (top project segment of the file's `path`).
    pub file_unit: BTreeMap<String, String>,
    /// Unit name → assigned layer name (`Domain`, `Application`,
    /// `Infrastructure`, `Presentation`, `Test`, `Shared`).
    pub unit_layer: BTreeMap<String, String>,
    /// Unit name → member file count.
    pub unit_files: BTreeMap<String, u64>,
    /// Unit name → member symbol count (non-File nodes owned by the unit).
    pub unit_symbols: BTreeMap<String, u64>,
    /// Counted inter-unit dependencies: `(from, to)` unit names →
    /// cross-unit [`DEPENDS`]-family + [`SPECIALIZES`]-family edge mass.
    ///
    /// [`DEPENDS`]: crate::ir::ontology::relation::DEPENDS
    /// [`SPECIALIZES`]: crate::ir::ontology::relation::SPECIALIZES
    pub unit_deps: BTreeMap<(String, String), u64>,
}

/// Run the unit derivation + archetype-mix layer inference (see the module
/// doc) over the base graph. This is the single source of truth for
/// file→unit and unit→layer placement; [`LayerExtractor::extract`] and the
/// hierarchy extractor both build their output from it. Pure and
/// deterministic: same graph, same assignment.
pub fn assign_layers(graph: &Graph) -> LayerAssignment {
    // Node kinds by id, for File detection during the containment walk.
    let kind_of: BTreeMap<&str, &'static str> =
        graph.nodes().map(|n| (n.id.as_str(), n.kind)).collect();

    // Containment parents (child → parent), preferring a File parent so a
    // method reached both by `File DECLARES fn` and `Type HAS_METHOD fn`
    // resolves to its file. First-seen wins among equals (edges iterate in
    // stable signature order), keeping the choice deterministic.
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
    // Bounded walk to the owning File: containment chains are shallow;
    // the bound only guards against a malformed cyclic containment.
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

    // File id → unit name (from the File node's `path` prop) and file id
    // → path, for the archetype location signals.
    let mut unit_of_file: BTreeMap<&str, String> = BTreeMap::new();
    let mut path_of_file: BTreeMap<&str, &str> = BTreeMap::new();
    for n in graph.nodes().filter(|n| n.kind == ont::FILE) {
        if let Some(Json::Str(path)) = n.props.get("path") {
            unit_of_file.insert(n.id.as_str(), unit_of_path(path));
            path_of_file.insert(n.id.as_str(), path.as_str());
        }
    }

    // Single-package refinement (Q-LAY-2): repos that keep all production
    // code under one top-level package (`django/…`, `alacritty/…`) collapse
    // into a single unit, making ≥2 core layers structurally impossible.
    // When one non-test unit owns a strict majority of the files, that unit
    // — and only that unit — is refined one directory level (`django` →
    // `django/db`, `django/views`, …; scaffold segments still skipped, files
    // directly inside keep the original unit). Multi-project repos (eShop,
    // jellyfin, hugo, dubbo) have no majority unit and are untouched.
    let dominant: Option<String> = {
        let mut counts: BTreeMap<&str, u64> = BTreeMap::new();
        for unit in unit_of_file.values() {
            if classify_by_name(unit) != Layer::Test {
                *counts.entry(unit.as_str()).or_default() += 1;
            }
        }
        let total: u64 = counts.values().sum();
        counts
            .into_iter()
            .max_by_key(|(_, c)| *c)
            .filter(|(_, c)| c * 2 > total)
            .map(|(u, _)| u.to_string())
    };
    if let Some(dominant) = &dominant {
        for (file, unit) in unit_of_file.iter_mut() {
            if *unit == *dominant {
                if let Some(path) = path_of_file.get(file).copied() {
                    *unit = refine_unit_of_path(path, dominant);
                }
            }
        }
    }

    // Node id → unit name, via the owning file. Also tally per-unit files
    // and symbols (non-File nodes that resolved to a unit), and — the
    // primary layer signal — per-unit archetype layer votes: each member
    // Type/Function symbol is classified against the shared archetype rule
    // table (with its declaring file's path for the location signals) and
    // its archetype votes for a layer via `layer_of_archetype`.
    let mut unit_of: BTreeMap<&str, &str> = BTreeMap::new();
    let mut unit_files: BTreeMap<&str, u64> = BTreeMap::new();
    let mut unit_symbols: BTreeMap<&str, u64> = BTreeMap::new();
    let mut unit_members: BTreeMap<&str, u64> = BTreeMap::new();
    let mut unit_votes: BTreeMap<&str, BTreeMap<Layer, u64>> = BTreeMap::new();
    for n in graph.nodes() {
        let Some(file) = resolve_file(&kind_of, &parent, n.id.as_str()) else {
            continue;
        };
        let Some(unit) = unit_of_file.get(file) else {
            continue;
        };
        unit_of.insert(n.id.as_str(), unit.as_str());
        if n.kind == ont::FILE {
            *unit_files.entry(unit.as_str()).or_default() += 1;
        } else {
            *unit_symbols.entry(unit.as_str()).or_default() += 1;
        }
        if n.kind == ont::TYPE || n.kind == ont::FUNCTION {
            *unit_members.entry(unit.as_str()).or_default() += 1;
            let facts = SymbolFacts::of(n, path_of_file.get(file).copied());
            if let Some(layer) = layer_of_archetype(classify_with(RULES, &facts)) {
                *unit_votes
                    .entry(unit.as_str())
                    .or_default()
                    .entry(layer)
                    .or_default() += 1;
            }
        }
    }

    // Unit → unit dependency counts, from every DEPENDS- or SPECIALIZES-
    // family edge that crosses a unit boundary (cross-unit inheritance is a
    // dependency — the strongest kind; omitting it undercounted the layer
    // flow and the violations report built on it). The topology fallback
    // below deliberately reads only the DEPENDS-family pairs
    // (`depends_pairs`): inheritance mass must not move a unit between
    // layers (a widely-extended test stub would read as "inner"), it only
    // joins the counted flow. Computed before layer assignment: the
    // dependency topology is the last-resort layer signal below.
    let mut unit_deps: BTreeMap<(String, String), u64> = BTreeMap::new();
    let mut depends_pairs: BTreeSet<(&str, &str)> = BTreeSet::new();
    for e in graph.edges() {
        let family = parent_relation(e.kind);
        if !matches!(family, Some(relation::DEPENDS | relation::SPECIALIZES)) {
            continue;
        }
        let (Some(from_unit), Some(to_unit)) =
            (unit_of.get(e.from.as_str()), unit_of.get(e.to.as_str()))
        else {
            continue;
        };
        if from_unit == to_unit {
            continue;
        }
        *unit_deps
            .entry((from_unit.to_string(), to_unit.to_string()))
            .or_default() += 1;
        if family == Some(relation::DEPENDS) {
            depends_pairs.insert((*from_unit, *to_unit));
        }
    }

    // Assign each unit its layer: archetype-mix plurality first, name
    // convention as the tie-breaking hint (see `decide_layer`).
    let all_units: BTreeSet<&str> = unit_files
        .keys()
        .chain(unit_symbols.keys())
        .copied()
        .collect();
    let mut layer_of_unit: BTreeMap<&str, Layer> = all_units
        .iter()
        .map(|unit| {
            (
                *unit,
                decide_layer(
                    classify_by_name(unit),
                    unit_votes.get(unit),
                    unit_members.get(unit).copied().unwrap_or(0),
                ),
            )
        })
        .collect();

    // Dependency-topology fallback (Q-LAY-2): a unit with NO archetype
    // signal at all (no core votes, no name convention — the shape of
    // non-OO code) can still be placed by how it sits in the dependency
    // graph: a unit many units depend on while it depends on few is inner
    // (Domain-ish); a unit that depends on many while few depend on it is
    // outer (Presentation-ish). Fan-in/fan-out count *distinct* counterpart
    // units, so one chatty edge cannot flip a unit. Units with any archetype
    // or name signal are never touched — .NET behavior is unchanged. Only
    // DEPENDS-family pairs feed this signal (see `depends_pairs` above):
    // being widely inherited-from must not reclassify a unit.
    let mut fan_in: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    let mut fan_out: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    for &(from, to) in &depends_pairs {
        fan_out.entry(from).or_default().insert(to);
        fan_in.entry(to).or_default().insert(from);
    }
    for (unit, layer) in layer_of_unit.iter_mut() {
        if *layer != Layer::Shared {
            continue;
        }
        let has_core_votes = unit_votes
            .get(unit)
            .is_some_and(|v| v.keys().any(|l| *l != Layer::Test));
        if has_core_votes {
            continue; // a real tie fell to Shared: respect it
        }
        let fi = fan_in.get(unit).map_or(0, BTreeSet::len);
        let fo = fan_out.get(unit).map_or(0, BTreeSet::len);
        if fi > fo {
            *layer = Layer::Domain;
        } else if fo > fi {
            *layer = Layer::Presentation;
        }
    }

    LayerAssignment {
        file_unit: unit_of_file
            .iter()
            .map(|(f, u)| (f.to_string(), u.clone()))
            .collect(),
        unit_layer: layer_of_unit
            .iter()
            .map(|(u, l)| (u.to_string(), l.name().to_string()))
            .collect(),
        unit_files: unit_files
            .iter()
            .map(|(u, c)| (u.to_string(), *c))
            .collect(),
        unit_symbols: unit_symbols
            .iter()
            .map(|(u, c)| (u.to_string(), *c))
            .collect(),
        unit_deps,
    }
}

/// Recover the architectural-layer view (units, layers, direction violations)
/// from the base graph.
pub struct LayerExtractor;

impl Extractor for LayerExtractor {
    fn name(&self) -> &'static str {
        "layers"
    }

    fn extract(&self, graph: &Graph) -> Graph {
        let assignment = assign_layers(graph);
        let mut out = Graph::new();

        // Per-layer tallies over the assigned units.
        let mut layer_units: BTreeMap<&str, u64> = BTreeMap::new();
        let mut layer_symbols: BTreeMap<&str, u64> = BTreeMap::new();
        for (unit, layer) in &assignment.unit_layer {
            *layer_units.entry(layer.as_str()).or_default() += 1;
            *layer_symbols.entry(layer.as_str()).or_default() +=
                assignment.unit_symbols.get(unit).copied().unwrap_or(0);
        }

        // Layer nodes.
        for (layer, unit_count) in &layer_units {
            let symbol_count = layer_symbols.get(layer).copied().unwrap_or(0);
            out.upsert_node(
                format!("layer::{layer}"),
                ont::MODULE,
                *layer,
                vec![
                    ("view", Json::str(VIEW)),
                    ("layer", Json::str(*layer)),
                    ("unit_count", Json::U64(*unit_count)),
                    ("symbol_count", Json::U64(symbol_count)),
                ],
            );
        }

        // Unit nodes, CONTAINS-linked to their layer.
        for (unit, layer) in &assignment.unit_layer {
            out.upsert_node(
                format!("unit::{unit}"),
                ont::MODULE,
                unit.clone(),
                vec![
                    ("view", Json::str(VIEW)),
                    ("layer", Json::str(layer.clone())),
                    (
                        "file_count",
                        Json::U64(assignment.unit_files.get(unit).copied().unwrap_or(0)),
                    ),
                    (
                        "symbol_count",
                        Json::U64(assignment.unit_symbols.get(unit).copied().unwrap_or(0)),
                    ),
                ],
            );
            out.add_edge(
                format!("layer::{layer}"),
                edge::CONTAINS,
                format!("unit::{unit}"),
                vec![],
            );
        }

        // Layer → layer dependency counts, projected from the inter-unit
        // dependency mass. Every unit in `unit_deps` was placed by
        // `assign_layers`, so the lookup is total.
        let mut layer_deps: BTreeMap<(&str, &str), u64> = BTreeMap::new();
        for ((from_unit, to_unit), count) in &assignment.unit_deps {
            let (Some(from), Some(to)) = (
                assignment.unit_layer.get(from_unit),
                assignment.unit_layer.get(to_unit),
            ) else {
                continue;
            };
            *layer_deps.entry((from.as_str(), to.as_str())).or_default() += count;
        }

        // Layer → layer DEPENDS_ON edges, counted and violation-flagged.
        for ((from, to), count) in &layer_deps {
            let violation = match (Layer::by_name(from), Layer::by_name(to)) {
                (Some(f), Some(t)) => is_violation(f, t),
                _ => false,
            };
            out.add_edge(
                format!("layer::{from}"),
                edge::DEPENDS_ON,
                format!("layer::{to}"),
                vec![
                    ("count", Json::U64(*count)),
                    ("violation", Json::Bool(violation)),
                ],
            );
        }

        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A hand-built base graph shaped like a small eShop-style solution:
    /// files under `src/Ordering.Domain/`, `src/Ordering.Infrastructure/` and
    /// `src/Ordering.API/`, one symbol per file, and cross-unit dependency
    /// edges — one clean (API → Domain) and one deliberate inversion
    /// (Domain → Infrastructure).
    fn sample_base() -> Graph {
        let mut g = Graph::new();

        g.upsert_node(
            "file::src/Ordering.Domain/Order.cs",
            ont::FILE,
            "Order.cs",
            vec![("path", Json::str("src/Ordering.Domain/Order.cs"))],
        );
        g.upsert_node(
            "file::src/Ordering.Infrastructure/OrderRepository.cs",
            ont::FILE,
            "OrderRepository.cs",
            vec![(
                "path",
                Json::str("src/Ordering.Infrastructure/OrderRepository.cs"),
            )],
        );
        g.upsert_node(
            "file::src/Ordering.API/OrdersController.cs",
            ont::FILE,
            "OrdersController.cs",
            vec![("path", Json::str("src/Ordering.API/OrdersController.cs"))],
        );

        g.upsert_node("type::Order", ont::TYPE, "Order", vec![]);
        g.upsert_node(
            "type::OrderRepository",
            ont::TYPE,
            "OrderRepository",
            vec![],
        );
        g.upsert_node("fn::OrdersController.Get", ont::FUNCTION, "Get", vec![]);

        g.add_edge(
            "file::src/Ordering.Domain/Order.cs",
            edge::DECLARES,
            "type::Order",
            vec![],
        );
        g.add_edge(
            "file::src/Ordering.Infrastructure/OrderRepository.cs",
            edge::DECLARES,
            "type::OrderRepository",
            vec![],
        );
        g.add_edge(
            "file::src/Ordering.API/OrdersController.cs",
            edge::DECLARES,
            "fn::OrdersController.Get",
            vec![],
        );

        // Deliberate inversion: the Domain entity reaches out to an
        // Infrastructure type. Must be flagged.
        g.add_edge(
            "type::Order",
            edge::USES_TYPE,
            "type::OrderRepository",
            vec![],
        );
        // Clean inward dependency: the API controller uses the Domain entity.
        g.add_edge(
            "fn::OrdersController.Get",
            edge::USES_TYPE,
            "type::Order",
            vec![],
        );

        g
    }

    #[test]
    fn units_are_assigned_to_layers() {
        let derived = LayerExtractor.extract(&sample_base());

        let layer_of = |unit_id: &str| -> String {
            let n = derived
                .nodes()
                .find(|n| n.id == unit_id)
                .unwrap_or_else(|| panic!("missing unit node {unit_id}"));
            assert_eq!(n.kind, ont::MODULE);
            assert_eq!(n.props.get("view"), Some(&Json::str(VIEW)));
            match n.props.get("layer") {
                Some(Json::Str(s)) => s.clone(),
                other => panic!("unit {unit_id} has no layer prop: {other:?}"),
            }
        };
        assert_eq!(layer_of("unit::Ordering.Domain"), "Domain");
        assert_eq!(layer_of("unit::Ordering.Infrastructure"), "Infrastructure");
        assert_eq!(layer_of("unit::Ordering.API"), "Presentation");

        // Layer nodes exist with tallies.
        let domain = derived
            .nodes()
            .find(|n| n.id == "layer::Domain")
            .expect("layer::Domain");
        assert_eq!(domain.kind, ont::MODULE);
        assert_eq!(domain.props.get("view"), Some(&Json::str(VIEW)));
        assert_eq!(domain.props.get("unit_count"), Some(&Json::U64(1)));
        assert_eq!(domain.props.get("symbol_count"), Some(&Json::U64(1)));
    }

    #[test]
    fn domain_to_infrastructure_is_a_violation() {
        let derived = LayerExtractor.extract(&sample_base());
        let e = derived
            .edges()
            .find(|e| {
                e.kind == edge::DEPENDS_ON
                    && e.from == "layer::Domain"
                    && e.to == "layer::Infrastructure"
            })
            .expect("Domain -> Infrastructure layer edge");
        assert_eq!(e.props.get("violation"), Some(&Json::Bool(true)));
        assert_eq!(e.props.get("count"), Some(&Json::U64(1)));
    }

    #[test]
    fn presentation_to_domain_is_clean() {
        let derived = LayerExtractor.extract(&sample_base());
        let e = derived
            .edges()
            .find(|e| {
                e.kind == edge::DEPENDS_ON
                    && e.from == "layer::Presentation"
                    && e.to == "layer::Domain"
            })
            .expect("Presentation -> Domain layer edge");
        assert_eq!(e.props.get("violation"), Some(&Json::Bool(false)));
        assert_eq!(e.props.get("count"), Some(&Json::U64(1)));
    }

    #[test]
    fn name_classification_follows_convention_order() {
        assert_eq!(classify_by_name("Ordering.Domain"), Layer::Domain);
        assert_eq!(classify_by_name("Ordering.Application"), Layer::Application);
        // `.apis` (Application) is matched before `.api` (Presentation).
        assert_eq!(classify_by_name("Catalog.APIs"), Layer::Application);
        assert_eq!(classify_by_name("Catalog.API"), Layer::Presentation);
        assert_eq!(
            classify_by_name("Ordering.Infrastructure"),
            Layer::Infrastructure
        );
        assert_eq!(
            classify_by_name("Ordering.Persistence"),
            Layer::Infrastructure
        );
        assert_eq!(classify_by_name("Shop.Web"), Layer::Presentation);
        assert_eq!(classify_by_name("Ordering.FunctionalTests"), Layer::Test);
        assert_eq!(classify_by_name("tests"), Layer::Test);
        assert_eq!(classify_by_name("SharedKernel"), Layer::Shared);
        // Case-insensitive.
        assert_eq!(classify_by_name("ordering.domain"), Layer::Domain);
    }

    #[test]
    fn archetype_votes_map_to_layers() {
        assert_eq!(
            layer_of_archetype(archetype::CONTROLLER),
            Some(Layer::Presentation)
        );
        assert_eq!(
            layer_of_archetype(archetype::MIDDLEWARE),
            Some(Layer::Presentation)
        );
        assert_eq!(
            layer_of_archetype(archetype::ENTRY_POINT),
            Some(Layer::Presentation)
        );
        for a in [
            archetype::HANDLER,
            archetype::COMMAND,
            archetype::QUERY,
            archetype::SERVICE,
            archetype::FACTORY,
        ] {
            assert_eq!(layer_of_archetype(a), Some(Layer::Application), "{a}");
        }
        for a in [
            archetype::AGGREGATE,
            archetype::ENTITY,
            archetype::VALUE_OBJECT,
            archetype::DOMAIN_EVENT,
        ] {
            assert_eq!(layer_of_archetype(a), Some(Layer::Domain), "{a}");
        }
        for a in [archetype::REPOSITORY, archetype::MIGRATION] {
            assert_eq!(layer_of_archetype(a), Some(Layer::Infrastructure), "{a}");
        }
        for a in [archetype::TEST, archetype::MOCK] {
            assert_eq!(layer_of_archetype(a), Some(Layer::Test), "{a}");
        }
        // Role-free archetypes abstain.
        for a in [
            archetype::INTERFACE,
            archetype::DTO,
            archetype::ENUM,
            archetype::CONFIGURATION,
            archetype::UNCLASSIFIED,
        ] {
            assert_eq!(layer_of_archetype(a), None, "{a}");
        }
    }

    #[test]
    fn plurality_wins_and_name_hint_breaks_ties() {
        let mut votes = BTreeMap::new();
        votes.insert(Layer::Presentation, 2);
        votes.insert(Layer::Domain, 2);
        // Tie: the name-convention hint decides, Shared when it says nothing.
        assert_eq!(decide_layer(Layer::Domain, Some(&votes), 10), Layer::Domain);
        assert_eq!(decide_layer(Layer::Shared, Some(&votes), 10), Layer::Shared);
        // Unique plurality: the archetype mix overrides the name hint.
        votes.insert(Layer::Presentation, 3);
        assert_eq!(
            decide_layer(Layer::Domain, Some(&votes), 10),
            Layer::Presentation
        );
        // No votes at all: the name-convention result stands.
        assert_eq!(decide_layer(Layer::Test, None, 10), Layer::Test);
        assert_eq!(decide_layer(Layer::Shared, None, 10), Layer::Shared);
    }

    #[test]
    fn test_votes_only_win_units_that_are_mostly_tests() {
        // The dubbo/Maven shape: a production module carrying its tests in
        // `src/test/java`. Every test symbol votes Test, only a fraction of
        // production symbols vote at all — Test must not swamp the module.
        let mut votes = BTreeMap::new();
        votes.insert(Layer::Test, 40);
        votes.insert(Layer::Application, 12);
        // 40 of 200 symbols are tests: a production unit — Application wins.
        assert_eq!(
            decide_layer(Layer::Shared, Some(&votes), 200),
            Layer::Application
        );
        // The same votes in a 60-symbol unit: majority-test — a test unit.
        assert_eq!(decide_layer(Layer::Shared, Some(&votes), 60), Layer::Test);
        // A unit *named* as tests with any test code stays Test even if a
        // harness entrypoint votes elsewhere.
        let mut harness = BTreeMap::new();
        harness.insert(Layer::Test, 3);
        harness.insert(Layer::Presentation, 5);
        assert_eq!(decide_layer(Layer::Test, Some(&harness), 100), Layer::Test);
        // Only Test votes, minority share, no name signal: no core signal —
        // the name hint (here Shared) stands.
        let mut only_tests = BTreeMap::new();
        only_tests.insert(Layer::Test, 5);
        assert_eq!(
            decide_layer(Layer::Shared, Some(&only_tests), 100),
            Layer::Shared
        );
    }

    #[test]
    fn refine_unit_of_path_descends_one_level_skipping_scaffold() {
        assert_eq!(
            refine_unit_of_path("django/db/models/base.py", "django"),
            "django/db"
        );
        assert_eq!(
            refine_unit_of_path("alacritty/src/renderer/rects.rs", "alacritty"),
            "alacritty/renderer"
        );
        // A file directly inside the unit (or with only scaffold below it)
        // keeps the plain unit.
        assert_eq!(
            refine_unit_of_path("django/shortcuts.py", "django"),
            "django"
        );
        assert_eq!(
            refine_unit_of_path("alacritty/src/main.rs", "alacritty"),
            "alacritty"
        );
    }

    /// The single-package + no-OO-naming shape (django/alacritty): all
    /// production code under one top-level dir, no role suffixes anywhere.
    /// The dominant unit must be refined into its child dirs, and vote-less
    /// units must be placed by dependency topology.
    #[test]
    fn single_package_repo_is_refined_and_layered_by_topology() {
        let mut g = Graph::new();
        let mut declare = |path: &str, sym_id: &str, sym_name: &str| {
            let fid = format!("file::{path}");
            g.upsert_node(
                fid.clone(),
                ont::FILE,
                path.rsplit('/').next().unwrap().to_string(),
                vec![("path", Json::str(path))],
            );
            g.upsert_node(sym_id, ont::TYPE, sym_name, vec![]);
            g.add_edge(fid, edge::DECLARES, sym_id, vec![]);
        };
        // One dominant package `pkg/` with three subsystems; names carry no
        // role conventions at all.
        declare("pkg/core/grid.py", "ty::Grid", "Grid");
        declare("pkg/core/cell.py", "ty::Cell", "Cell");
        declare("pkg/render/painter.py", "ty::Painter", "Painter");
        declare("pkg/render/canvas.py", "ty::Canvas", "Canvas");
        declare("pkg/input/keyboard.py", "ty::Keyboard", "Keyboard");
        // Both other subsystems depend on core; core depends on nothing.
        g.add_edge("ty::Painter", edge::USES_TYPE, "ty::Grid", vec![]);
        g.add_edge("ty::Keyboard", edge::USES_TYPE, "ty::Grid", vec![]);
        // render also reaches into input: fan-out 2 > fan-in 0.
        g.add_edge("ty::Painter", edge::USES_TYPE, "ty::Keyboard", vec![]);

        let a = assign_layers(&g);
        // The dominant `pkg` unit was refined into its child dirs.
        assert_eq!(a.file_unit["file::pkg/core/grid.py"], "pkg/core");
        assert_eq!(a.file_unit["file::pkg/render/painter.py"], "pkg/render");
        assert_eq!(a.file_unit["file::pkg/input/keyboard.py"], "pkg/input");
        // core: fan-in 2, fan-out 0 → inner → Domain.
        assert_eq!(a.unit_layer["pkg/core"], "Domain");
        // render: fan-out 2, fan-in 0 → outer → Presentation.
        assert_eq!(a.unit_layer["pkg/render"], "Presentation");
        // input: fan-in 1 == fan-out 1 → no topology verdict → Shared.
        assert_eq!(a.unit_layer["pkg/input"], "Shared");
    }

    /// Archetype and name signals always outrank the topology fallback.
    #[test]
    fn topology_fallback_never_overrides_archetype_or_name_signals() {
        let mut g = Graph::new();
        let mut declare = |path: &str, sym_id: &str, sym_name: &str| {
            let fid = format!("file::{path}");
            g.upsert_node(
                fid.clone(),
                ont::FILE,
                path.rsplit('/').next().unwrap().to_string(),
                vec![("path", Json::str(path))],
            );
            g.upsert_node(sym_id, ont::TYPE, sym_name, vec![]);
            g.add_edge(fid, edge::DECLARES, sym_id, vec![]);
        };
        // `web` has an archetype vote (Controller) but depends on everything
        // — the vote must stand, not the fan-out.
        declare(
            "web/OrdersController.cs",
            "ty::OrdersController",
            "OrdersController",
        );
        declare(
            "store/OrderRepository.cs",
            "ty::OrderRepository",
            "OrderRepository",
        );
        declare("misc/Helpers.cs", "ty::Helpers", "Helpers");
        g.add_edge(
            "ty::OrdersController",
            edge::USES_TYPE,
            "ty::OrderRepository",
            vec![],
        );
        g.add_edge(
            "ty::OrdersController",
            edge::USES_TYPE,
            "ty::Helpers",
            vec![],
        );

        let a = assign_layers(&g);
        assert_eq!(a.unit_layer["web"], "Presentation");
        assert_eq!(a.unit_layer["store"], "Infrastructure");
        // `misc` has no votes and no name signal; fan-in 1 > fan-out 0 →
        // topology places it Domain.
        assert_eq!(a.unit_layer["misc"], "Domain");
    }

    #[test]
    fn unit_derivation_skips_scaffold_segments() {
        assert_eq!(
            unit_of_path("src/Ordering.Domain/Order.cs"),
            "Ordering.Domain"
        );
        assert_eq!(
            unit_of_path("src/Catalog.API/Controllers/CatalogController.cs"),
            "Catalog.API"
        );
        assert_eq!(
            unit_of_path("tests/Ordering.UnitTests/OrderTests.cs"),
            "tests"
        );
        assert_eq!(unit_of_path("src/main.rs"), "src");
        assert_eq!(unit_of_path("Program.cs"), "(root)");
    }

    #[test]
    fn layer_names_match_layer_all() {
        let names: Vec<&str> = Layer::ALL.into_iter().map(Layer::name).collect();
        assert_eq!(names, LAYER_NAMES.to_vec());
    }

    #[test]
    fn direction_rule_matches_clean_architecture() {
        // Domain depends on nothing but Domain/Shared.
        assert!(is_violation(Layer::Domain, Layer::Application));
        assert!(is_violation(Layer::Domain, Layer::Infrastructure));
        assert!(is_violation(Layer::Domain, Layer::Presentation));
        assert!(!is_violation(Layer::Domain, Layer::Domain));
        assert!(!is_violation(Layer::Domain, Layer::Shared));
        // Application may depend on Domain/Shared only.
        assert!(!is_violation(Layer::Application, Layer::Domain));
        assert!(is_violation(Layer::Application, Layer::Infrastructure));
        assert!(is_violation(Layer::Application, Layer::Presentation));
        // Infrastructure and Presentation may depend inward.
        assert!(!is_violation(Layer::Infrastructure, Layer::Domain));
        assert!(!is_violation(Layer::Infrastructure, Layer::Application));
        assert!(!is_violation(Layer::Presentation, Layer::Infrastructure));
        assert!(!is_violation(Layer::Presentation, Layer::Domain));
        // Test and Shared never violate.
        assert!(!is_violation(Layer::Test, Layer::Presentation));
        assert!(!is_violation(Layer::Shared, Layer::Presentation));
        assert!(!is_violation(Layer::Presentation, Layer::Test));
    }

    /// A base graph with NO conventional unit names at all — `web`, `core`,
    /// `store` — the shape that made the name-only pass silently map every
    /// unit to Shared. Layer identity here comes purely from the archetype mix
    /// of each unit's member types.
    fn archetype_base() -> Graph {
        let mut g = Graph::new();

        fn declare(g: &mut Graph, path: &str, sym_id: &str, sym_name: &str) {
            let fid = format!("file::{path}");
            let fname = path.rsplit('/').next().unwrap().to_string();
            g.upsert_node(
                fid.clone(),
                ont::FILE,
                fname,
                vec![("path", Json::str(path))],
            );
            g.upsert_node(sym_id, ont::TYPE, sym_name, vec![]);
            g.add_edge(fid, edge::DECLARES, sym_id, vec![]);
        }

        // web: two controllers → Presentation by archetype plurality.
        declare(
            &mut g,
            "web/OrdersController.cs",
            "ty::OrdersController",
            "OrdersController",
        );
        declare(
            &mut g,
            "web/UsersController.cs",
            "ty::UsersController",
            "UsersController",
        );
        // core: aggregate + entity types → Domain.
        declare(
            &mut g,
            "core/OrderAggregate.cs",
            "ty::OrderAggregate",
            "OrderAggregate",
        );
        declare(
            &mut g,
            "core/CustomerEntity.cs",
            "ty::CustomerEntity",
            "CustomerEntity",
        );
        // store: two repositories → Infrastructure.
        declare(
            &mut g,
            "store/OrderRepository.cs",
            "ty::OrderRepository",
            "OrderRepository",
        );
        declare(
            &mut g,
            "store/CustomerRepository.cs",
            "ty::CustomerRepository",
            "CustomerRepository",
        );

        // Clean inward dependency: web (Presentation) → core (Domain).
        g.add_edge(
            "ty::OrdersController",
            edge::USES_TYPE,
            "ty::OrderAggregate",
            vec![],
        );
        // Deliberate inversion: core (Domain) → store (Infrastructure).
        g.add_edge(
            "ty::OrderAggregate",
            edge::USES_TYPE,
            "ty::OrderRepository",
            vec![],
        );

        g
    }

    #[test]
    fn archetype_mix_assigns_layers_without_naming_conventions() {
        let derived = LayerExtractor.extract(&archetype_base());

        let layer_of = |unit_id: &str| -> String {
            let n = derived
                .nodes()
                .find(|n| n.id == unit_id)
                .unwrap_or_else(|| panic!("missing unit node {unit_id}"));
            match n.props.get("layer") {
                Some(Json::Str(s)) => s.clone(),
                other => panic!("unit {unit_id} has no layer prop: {other:?}"),
            }
        };
        // None of these unit names match any convention; only the archetype
        // mix can place them — the old name-only pass called all three Shared.
        assert_eq!(layer_of("unit::web"), "Presentation");
        assert_eq!(layer_of("unit::core"), "Domain");
        assert_eq!(layer_of("unit::store"), "Infrastructure");

        // The Domain → Infrastructure inversion is flagged…
        let violation = derived
            .edges()
            .find(|e| {
                e.kind == edge::DEPENDS_ON
                    && e.from == "layer::Domain"
                    && e.to == "layer::Infrastructure"
            })
            .expect("Domain -> Infrastructure layer edge");
        assert_eq!(violation.props.get("violation"), Some(&Json::Bool(true)));
        assert_eq!(violation.props.get("count"), Some(&Json::U64(1)));
        // …and the inward Presentation → Domain edge is clean.
        let clean = derived
            .edges()
            .find(|e| {
                e.kind == edge::DEPENDS_ON
                    && e.from == "layer::Presentation"
                    && e.to == "layer::Domain"
            })
            .expect("Presentation -> Domain layer edge");
        assert_eq!(clean.props.get("violation"), Some(&Json::Bool(false)));
    }

    #[test]
    fn name_hint_decides_when_archetype_votes_tie() {
        // One Controller vote vs one Repository vote inside a `.Domain`-named
        // unit: the tie falls to the strong name hint.
        let mut g = Graph::new();
        for (path, id, name) in [
            (
                "src/Billing.Domain/PaymentController.cs",
                "ty::PaymentController",
                "PaymentController",
            ),
            (
                "src/Billing.Domain/PaymentRepository.cs",
                "ty::PaymentRepository",
                "PaymentRepository",
            ),
        ] {
            let fid = format!("file::{path}");
            g.upsert_node(
                fid.clone(),
                ont::FILE,
                path.rsplit('/').next().unwrap().to_string(),
                vec![("path", Json::str(path))],
            );
            g.upsert_node(id, ont::TYPE, name, vec![]);
            g.add_edge(fid, edge::DECLARES, id, vec![]);
        }
        let derived = LayerExtractor.extract(&g);
        let unit = derived
            .nodes()
            .find(|n| n.id == "unit::Billing.Domain")
            .expect("unit node");
        assert_eq!(unit.props.get("layer"), Some(&Json::str("Domain")));
    }

    #[test]
    fn deterministic_across_runs_and_base_untouched() {
        for base in [sample_base(), archetype_base()] {
            let before = base.to_jsonl();
            let a = LayerExtractor.extract(&base).to_jsonl();
            let b = LayerExtractor.extract(&base).to_jsonl();
            assert_eq!(a, b);
            assert!(!a.is_empty());
            assert_eq!(base.to_jsonl(), before, "base graph must not change");
        }
    }
}
