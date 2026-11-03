//! Structure-aware fuzzing of the ontology extractors (gs-C2).
//!
//! The extractors promise two things for *any* base graph, not just graphs a
//! language front end would produce: they never panic, and they are pure —
//! the same input graph always linearizes to byte-identical JSONL. This
//! harness generates random-but-structurally-valid [`Graph`]s straight
//! through the public `upsert_node`/`add_edge` API (the narrowest input
//! boundary the extractors see) and checks three invariants per extractor:
//!
//! 1. **No panic.** Extraction is isolated with `catch_unwind`; a panic is a
//!    reported failure carrying its seed, never a harness crash.
//! 2. **Byte-stable.** Running the same extractor twice on the same graph
//!    must yield byte-identical `to_jsonl` output.
//! 3. **Valid JSONL.** Every emitted line must parse as a standalone JSON
//!    value (validated by the std-only scanner below — the runtime crate has
//!    a JSON writer but deliberately no parser).
//!
//! The generator is structure-aware, not byte-random: node kinds come from
//! the real ontology vocabulary (plus junk), names span PascalCase / snake /
//! unicode / empty / hostile-escape / very long, props cover the keys the
//! extractors actually read (`path`, `language`, `type_kind`, `entrypoint`,
//! `generated`, `level`) plus junk keys and junk value shapes, and edges
//! include self-loops, dangling endpoints, explicit cycles, and dense hubs.
//!
//! Everything is deterministic and hermetic, in the style of
//! [`crate::property`]: a seeded xorshift [`Rng`] drives generation, every
//! failure carries the exact case seed, and `FUZZ_SEED=<seed>` replays a
//! single case. `FUZZ_CASES=<n>` scales the campaign (default keeps the
//! `cargo test` gate fast).
//!
//! [`Graph`]: trailtracker::graph::Graph
//! [`Rng`]: crate::property::Rng

use std::panic::{catch_unwind, AssertUnwindSafe};

use trailtracker::core::json::Json;
use trailtracker::extract::extractors;
use trailtracker::graph::Graph;
use trailtracker::ir::ontology::{edge, node as ont, relation};

use crate::property::Rng;

/// One invariant violation, pinned to the case seed that reproduces it.
#[derive(Debug)]
pub struct Failure {
    pub seed: u64,
    pub extractor: &'static str,
    pub kind: &'static str,
    pub detail: String,
}

impl Failure {
    /// A one-line report with exact repro instructions.
    pub fn report(&self) -> String {
        format!(
            "seed=0x{seed:016x} extractor={ex} kind={kind} — {detail}\n    \
             repro: FUZZ_SEED=0x{seed:x} cargo test -p trailtracker-eval fuzz_seed_replays_clean",
            seed = self.seed,
            ex = self.extractor,
            kind = self.kind,
            detail = self.detail,
        )
    }
}

#[derive(Default)]
pub struct FuzzOutcome {
    pub cases: usize,
    pub failures: Vec<Failure>,
}

impl FuzzOutcome {
    pub fn passed(&self) -> bool {
        self.failures.is_empty()
    }

    pub fn report(&self) -> String {
        self.failures
            .iter()
            .map(Failure::report)
            .collect::<Vec<_>>()
            .join("\n")
    }
}

/// Case count for the gate: `FUZZ_CASES` if set, else `default`.
pub fn cases_from_env(default: usize) -> usize {
    std::env::var("FUZZ_CASES")
        .ok()
        .and_then(|v| v.trim().parse().ok())
        .unwrap_or(default)
}

/// Run `cases` generated graphs derived from `seed` through every registered
/// extractor. Failure collection is capped to keep reports bounded.
pub fn run(seed: u64, cases: usize) -> FuzzOutcome {
    let mut out = FuzzOutcome::default();
    const FAILURE_CAP: usize = 25;
    for i in 0..cases {
        let case_seed = seed ^ (i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15);
        out.cases += 1;
        for f in check_case(case_seed) {
            if out.failures.len() < FAILURE_CAP {
                out.failures.push(f);
            }
        }
    }
    out
}

/// Generate the graph for `case_seed` and check every invariant on every
/// extractor. Public so a single failing seed replays in isolation.
pub fn check_case(case_seed: u64) -> Vec<Failure> {
    let mut rng = Rng::new(case_seed);
    let g = gen_graph(&mut rng);
    let mut failures = Vec::new();

    // The base graph's own serialization must be valid JSONL too — hostile
    // names/props must never break a line.
    if let Some(detail) = first_invalid_line(&g.to_jsonl()) {
        failures.push(Failure {
            seed: case_seed,
            extractor: "base-graph",
            kind: "invalid_jsonl",
            detail,
        });
    }

    for ex in extractors() {
        let name = ex.name();
        // Invariant 1: no panic.
        let first = catch_unwind(AssertUnwindSafe(|| ex.extract(&g).to_jsonl()));
        let jsonl1 = match first {
            Ok(j) => j,
            Err(_) => {
                failures.push(Failure {
                    seed: case_seed,
                    extractor: name,
                    kind: "panic",
                    detail: format!(
                        "extractor panicked on a generated graph ({} nodes, {} edges)",
                        g.node_count(),
                        g.edge_count()
                    ),
                });
                continue;
            }
        };
        // Invariant 2: byte-stable across a second run on the same graph.
        let second = catch_unwind(AssertUnwindSafe(|| ex.extract(&g).to_jsonl()));
        match second {
            Ok(jsonl2) if jsonl1 == jsonl2 => {}
            Ok(jsonl2) => failures.push(Failure {
                seed: case_seed,
                extractor: name,
                kind: "nondeterministic",
                detail: first_divergence(&jsonl1, &jsonl2),
            }),
            Err(_) => failures.push(Failure {
                seed: case_seed,
                extractor: name,
                kind: "panic",
                detail: "second run panicked where the first succeeded".to_string(),
            }),
        }
        // Invariant 3: every output line is standalone valid JSON.
        if let Some(detail) = first_invalid_line(&jsonl1) {
            failures.push(Failure {
                seed: case_seed,
                extractor: name,
                kind: "invalid_jsonl",
                detail,
            });
        }
    }
    failures
}

// ---------------------------------------------------------------------------
// Structure-aware graph generation
// ---------------------------------------------------------------------------

/// Uniform pick in `0..n` (0 when `n == 0`), mirroring the property harness.
fn below(rng: &mut Rng, n: usize) -> usize {
    if n == 0 {
        0
    } else {
        (rng.next_u64() % n as u64) as usize
    }
}

/// Node kinds: the full real ontology vocabulary plus junk kinds that no
/// front end emits — extractors must shrug at both.
const NODE_KINDS: &[&str] = &[
    ont::FILE,
    ont::MODULE,
    ont::FUNCTION,
    ont::TYPE,
    ont::CONSTANT,
    ont::PACKAGE,
    ont::EXTERNAL_DEPENDENCY,
    ont::UNRESOLVED,
    ont::MACRO,
    // Weight the common kinds so most graphs look like real base graphs.
    ont::FILE,
    ont::FUNCTION,
    ont::TYPE,
    ont::FILE,
    ont::FUNCTION,
    ont::TYPE,
    // Junk kinds, including view-level and hostile ones.
    "Domain",
    "Unit",
    "",
    "Weird🦀Kind",
];

/// Edge kinds: every base-graph relationship, the view-level vocabulary
/// (which must be inert in a base graph), and junk.
const EDGE_KINDS: &[&str] = &[
    edge::CONTAINS,
    edge::DECLARES,
    edge::CALLS,
    edge::IMPORTS,
    edge::DEPENDS_ON,
    edge::USES_TYPE,
    edge::IMPLEMENTS,
    edge::HAS_METHOD,
    edge::EXTENDS,
    edge::FLOWS_TO,
    edge::DATA_DEP,
    // Weight the structural pair that most extractors walk.
    edge::DECLARES,
    edge::CONTAINS,
    edge::DECLARES,
    // View-level + junk.
    relation::DEPENDS,
    relation::CONTAINMENT,
    relation::SPECIALIZES,
    "",
    "WEIRD_EDGE",
];

const WORDS: &[&str] = &[
    "Order",
    "Basket",
    "Catalog",
    "Payment",
    "Guard",
    "Against",
    "Create",
    "Get",
    "Controller",
    "Repository",
    "Service",
    "Handler",
    "Command",
    "Dto",
    "Item",
    "Entity",
    "Flow",
    "Trigger",
    "Account",
];

const UNICODE_NAMES: &[&str] = &[
    "Bestellung",
    "注文サービス",
    "🦀Ferris",
    "λcalc",
    "Ünïcödé_Nàme",
    "Schrödinger☃",
    "заказ_обработчик",
];

/// Names whose bytes stress JSON escaping and tokenizers: quotes,
/// backslashes, newlines, tabs, raw control characters.
const HOSTILE_NAMES: &[&str] = &[
    "we\"ird\\na\nme",
    "a\tb\rc",
    "ctrl\u{1}char\u{7f}",
    "\\u0000not-an-escape",
    "{\"json\":\"in-a-name\"}",
];

const PATH_SEGMENTS: &[&str] = &[
    "src",
    "build",
    "obj",
    "Debug",
    "Ordering.API",
    "node_modules",
    ".hidden",
    "",
    ".",
    "..",
    "über raum",
    "a\"b\\c",
    "%2e%2e",
    "with space",
    "force-app",
];

const EXTENSIONS: &[&str] = &[
    ".cs",
    ".rs",
    ".py",
    ".ts",
    ".Designer.cs",
    ".generated.cs",
    ".flow-meta.xml",
    ".object-meta.xml",
    "",
];

fn gen_pascal(rng: &mut Rng) -> String {
    let n = 1 + below(rng, 3);
    let mut s = String::new();
    for _ in 0..n {
        s.push_str(WORDS[below(rng, WORDS.len())]);
    }
    s
}

fn gen_name(rng: &mut Rng) -> String {
    match below(rng, 12) {
        0 => ["", " ", "_", "0"][below(rng, 4)].to_string(),
        1 => UNICODE_NAMES[below(rng, UNICODE_NAMES.len())].to_string(),
        2 => HOSTILE_NAMES[below(rng, HOSTILE_NAMES.len())].to_string(),
        3 => {
            // Very long names: hundreds of bytes, ASCII or multi-byte.
            if below(rng, 2) == 0 {
                gen_pascal(rng).repeat(40)
            } else {
                "🦀".repeat(150)
            }
        }
        4 => format!("{}_impl", gen_pascal(rng).to_lowercase()), // snake-ish
        5 => format!(
            "{}.{}.{}",
            gen_pascal(rng),
            gen_pascal(rng),
            gen_pascal(rng)
        ),
        6 => gen_pascal(rng).to_uppercase(),
        7 => format!("123{}", gen_pascal(rng)),
        _ => gen_pascal(rng),
    }
}

fn gen_path(rng: &mut Rng) -> String {
    let mut s = String::new();
    if below(rng, 5) == 0 {
        s.push('/');
    }
    let segs = 1 + below(rng, 4);
    for i in 0..segs {
        if i > 0 {
            s.push('/');
        }
        s.push_str(PATH_SEGMENTS[below(rng, PATH_SEGMENTS.len())]);
    }
    s.push('/');
    match below(rng, 8) {
        0 => s.push_str(&"Long".repeat(80)),
        1 => s.push_str(UNICODE_NAMES[below(rng, UNICODE_NAMES.len())]),
        _ => s.push_str(&gen_pascal(rng)),
    }
    s.push_str(EXTENSIONS[below(rng, EXTENSIONS.len())]);
    if below(rng, 10) == 0 {
        s.push('/'); // trailing slash: a path that is not file-like
    }
    s
}

/// A random JSON value for junk props, depth-bounded.
fn gen_json_value(rng: &mut Rng, depth: usize) -> Json {
    let top = if depth == 0 { 8 } else { 10 };
    match below(rng, top) {
        0 => Json::Null,
        1 => Json::Bool(below(rng, 2) == 0),
        2 => Json::I64(i64::MIN + below(rng, 3) as i64),
        3 => Json::U64(u64::MAX - below(rng, 3) as u64),
        4 => Json::F64([f64::NAN, f64::INFINITY, -0.0, 1e300, 0.1][below(rng, 5)]),
        5 => Json::str(gen_name(rng)),
        6 => Json::str(HOSTILE_NAMES[below(rng, HOSTILE_NAMES.len())]),
        7 => Json::U64(below(rng, 100_000) as u64),
        8 => Json::Array(
            (0..below(rng, 4))
                .map(|_| gen_json_value(rng, depth - 1))
                .collect(),
        ),
        _ => Json::obj([("k", gen_json_value(rng, depth - 1))]),
    }
}

/// Node props covering every key the extractors read, with both plausible
/// and junk values, plus junk keys (including ones that collide with the
/// JSONL record's own reserved keys).
fn gen_node_props(rng: &mut Rng) -> Vec<(&'static str, Json)> {
    let mut props: Vec<(&'static str, Json)> = Vec::new();
    if below(rng, 3) != 0 {
        props.push(("path", Json::str(gen_path(rng))));
    }
    if below(rng, 3) == 0 {
        const LANGS: &[&str] = &[
            "rust",
            "csharp",
            "python",
            "salesforce-metadata",
            "",
            "🦀",
            "C++",
        ];
        props.push(("language", Json::str(LANGS[below(rng, LANGS.len())])));
    }
    if below(rng, 4) == 0 {
        const TKS: &[&str] = &[
            "enum",
            "interface",
            "trait",
            "flow",
            "class",
            "",
            "ENUM",
            "🦀",
        ];
        props.push(("type_kind", Json::str(TKS[below(rng, TKS.len())])));
    }
    if below(rng, 6) == 0 {
        let v = match below(rng, 3) {
            0 => Json::Bool(true),
            1 => Json::str("yes"), // wrong type: must be tolerated
            _ => Json::U64(1),
        };
        props.push(("entrypoint", v));
    }
    if below(rng, 6) == 0 {
        let key = if below(rng, 2) == 0 {
            "generated"
        } else {
            "is_generated"
        };
        let v = if below(rng, 3) == 0 {
            Json::str("true")
        } else {
            Json::Bool(below(rng, 2) == 0)
        };
        props.push((key, v));
    }
    if below(rng, 8) == 0 {
        const LEVELS: &[&str] = &["file", "symbol", "unit", "domain", ""];
        props.push(("level", Json::str(LEVELS[below(rng, LEVELS.len())])));
    }
    const JUNK_KEYS: &[&str] = &[
        "record",
        "id",
        "kind",
        "name",
        "properties",
        "",
        "💾junk",
        "zzz_junk",
        "line",
        "qualified_name",
        "start",
    ];
    for _ in 0..below(rng, 3) {
        props.push((
            JUNK_KEYS[below(rng, JUNK_KEYS.len())],
            gen_json_value(rng, 2),
        ));
    }
    props
}

fn gen_edge_props(rng: &mut Rng) -> Vec<(&'static str, Json)> {
    let mut props: Vec<(&'static str, Json)> = Vec::new();
    if below(rng, 4) == 0 {
        props.push(("resolved", Json::Bool(below(rng, 2) == 0)));
    }
    if below(rng, 5) == 0 {
        props.push(("base_name", Json::str(gen_name(rng))));
    }
    if below(rng, 6) == 0 {
        props.push(("via", gen_json_value(rng, 1)));
    }
    props
}

fn gen_id(rng: &mut Rng, i: usize) -> String {
    match below(rng, 6) {
        0 => format!("file::{}", gen_path(rng)),
        1 => format!("sym::{}#{}", gen_path(rng), i),
        2 => format!("fn::mod{}::f{i}", below(rng, 9)),
        3 => format!("dup::{}", below(rng, 7)), // deliberate id collisions
        4 => gen_name(rng),                     // arbitrary: empty/unicode/hostile
        _ => format!("n{i}"),
    }
}

/// A dangling-ish endpoint: an id no node carries (with high probability).
fn gen_dangling(rng: &mut Rng) -> String {
    format!("ghost::{}", rng.next_u64() % 1_000)
}

fn pick_endpoint(rng: &mut Rng, ids: &[String], hub: Option<&str>) -> String {
    let r = below(rng, 12);
    if r == 0 || ids.is_empty() {
        return gen_dangling(rng);
    }
    if r <= 3 {
        if let Some(h) = hub {
            return h.to_string(); // dense hub: many edges share one endpoint
        }
    }
    ids[below(rng, ids.len())].clone()
}

/// Build one random-but-structurally-valid graph. Node counts are skewed
/// small (fast cases) with a heavy tail up to ~500 nodes; edges include
/// self-loops, dangling endpoints, dense hubs, and explicit cycles.
pub fn gen_graph(rng: &mut Rng) -> Graph {
    let node_count = if below(rng, 8) == 0 {
        below(rng, 500)
    } else {
        below(rng, 60)
    };
    let mut g = Graph::new();
    let mut ids: Vec<String> = Vec::with_capacity(node_count);
    for i in 0..node_count {
        let id = gen_id(rng, i);
        let kind = NODE_KINDS[below(rng, NODE_KINDS.len())];
        g.upsert_node(id.clone(), kind, gen_name(rng), gen_node_props(rng));
        ids.push(id);
    }

    let n = ids.len();
    let edge_count = if n == 0 {
        below(rng, 4)
    } else {
        below(rng, n * 3 + 4)
    };
    let hub = if n > 0 && below(rng, 3) == 0 {
        Some(ids[below(rng, n)].clone())
    } else {
        None
    };
    for _ in 0..edge_count {
        let kind = EDGE_KINDS[below(rng, EDGE_KINDS.len())];
        let from = pick_endpoint(rng, &ids, hub.as_deref());
        let to = if below(rng, 12) == 0 {
            from.clone() // self-loop
        } else {
            pick_endpoint(rng, &ids, hub.as_deref())
        };
        g.add_edge(from, kind, to, gen_edge_props(rng));
    }
    // Explicit 3-cycle over existing nodes: extractors that walk CONTAINS /
    // CALLS chains must terminate on it.
    if n >= 3 && below(rng, 4) == 0 {
        let kind = [edge::CALLS, edge::CONTAINS, edge::FLOWS_TO][below(rng, 3)];
        let a = ids[below(rng, n)].clone();
        let b = ids[below(rng, n)].clone();
        let c = ids[below(rng, n)].clone();
        g.add_edge(a.clone(), kind, b.clone(), vec![]);
        g.add_edge(b, kind, c.clone(), vec![]);
        g.add_edge(c, kind, a, vec![]);
    }
    g
}

// ---------------------------------------------------------------------------
// JSONL validation (std-only scanner; the runtime crate has no JSON parser)
// ---------------------------------------------------------------------------

/// `Some(diagnosis)` for the first line that is empty or not a single valid
/// JSON value, else `None`. A trailing newline is required after every line.
pub fn first_invalid_line(jsonl: &str) -> Option<String> {
    if !jsonl.is_empty() && !jsonl.ends_with('\n') {
        return Some("output does not end with a newline".to_string());
    }
    for (i, line) in jsonl.lines().enumerate() {
        if !json_line_ok(line) {
            return Some(format!(
                "line {}: not valid JSON: {}",
                i + 1,
                trunc(line, 160)
            ));
        }
    }
    None
}

/// Whether `line` parses as exactly one JSON value with nothing after it.
pub fn json_line_ok(line: &str) -> bool {
    let mut p = Scan {
        b: line.as_bytes(),
        i: 0,
    };
    p.ws();
    if !p.value(0) {
        return false;
    }
    p.ws();
    p.i == p.b.len() && !line.trim().is_empty()
}

struct Scan<'a> {
    b: &'a [u8],
    i: usize,
}

impl Scan<'_> {
    fn peek(&self) -> Option<u8> {
        self.b.get(self.i).copied()
    }
    fn eat(&mut self, c: u8) -> bool {
        if self.peek() == Some(c) {
            self.i += 1;
            true
        } else {
            false
        }
    }
    fn lit(&mut self, s: &[u8]) -> bool {
        if self.b[self.i..].starts_with(s) {
            self.i += s.len();
            true
        } else {
            false
        }
    }
    fn ws(&mut self) {
        while matches!(self.peek(), Some(b' ' | b'\t' | b'\r' | b'\n')) {
            self.i += 1;
        }
    }
    fn value(&mut self, depth: usize) -> bool {
        if depth > 64 {
            return false;
        }
        self.ws();
        match self.peek() {
            Some(b'n') => self.lit(b"null"),
            Some(b't') => self.lit(b"true"),
            Some(b'f') => self.lit(b"false"),
            Some(b'"') => self.string(),
            Some(b'[') => self.array(depth),
            Some(b'{') => self.object(depth),
            Some(c) if c == b'-' || c.is_ascii_digit() => self.number(),
            _ => false,
        }
    }
    fn string(&mut self) -> bool {
        if !self.eat(b'"') {
            return false;
        }
        loop {
            match self.peek() {
                None => return false,
                Some(b'"') => {
                    self.i += 1;
                    return true;
                }
                Some(b'\\') => {
                    self.i += 1;
                    match self.peek() {
                        Some(b'"' | b'\\' | b'/' | b'b' | b'f' | b'n' | b'r' | b't') => self.i += 1,
                        Some(b'u') => {
                            self.i += 1;
                            for _ in 0..4 {
                                match self.peek() {
                                    Some(c) if c.is_ascii_hexdigit() => self.i += 1,
                                    _ => return false,
                                }
                            }
                        }
                        _ => return false,
                    }
                }
                Some(c) if c < 0x20 => return false, // raw control char
                Some(_) => self.i += 1,
            }
        }
    }
    fn digits(&mut self) -> usize {
        let start = self.i;
        while matches!(self.peek(), Some(c) if c.is_ascii_digit()) {
            self.i += 1;
        }
        self.i - start
    }
    fn number(&mut self) -> bool {
        self.eat(b'-');
        match self.peek() {
            Some(b'0') => {
                self.i += 1;
            }
            Some(c) if c.is_ascii_digit() => {
                self.digits();
            }
            _ => return false,
        }
        if self.eat(b'.') && self.digits() == 0 {
            return false;
        }
        if matches!(self.peek(), Some(b'e' | b'E')) {
            self.i += 1;
            if matches!(self.peek(), Some(b'+' | b'-')) {
                self.i += 1;
            }
            if self.digits() == 0 {
                return false;
            }
        }
        true
    }
    fn array(&mut self, depth: usize) -> bool {
        if !self.eat(b'[') {
            return false;
        }
        self.ws();
        if self.eat(b']') {
            return true;
        }
        loop {
            if !self.value(depth + 1) {
                return false;
            }
            self.ws();
            if self.eat(b']') {
                return true;
            }
            if !self.eat(b',') {
                return false;
            }
        }
    }
    fn object(&mut self, depth: usize) -> bool {
        if !self.eat(b'{') {
            return false;
        }
        self.ws();
        if self.eat(b'}') {
            return true;
        }
        loop {
            self.ws();
            if !self.string() {
                return false;
            }
            self.ws();
            if !self.eat(b':') {
                return false;
            }
            if !self.value(depth + 1) {
                return false;
            }
            self.ws();
            if self.eat(b'}') {
                return true;
            }
            if !self.eat(b',') {
                return false;
            }
        }
    }
}

fn trunc(s: &str, max: usize) -> String {
    if s.len() <= max {
        return s.to_string();
    }
    let mut end = max;
    while !s.is_char_boundary(end) {
        end -= 1;
    }
    format!("{}…", &s[..end])
}

fn first_divergence(a: &str, b: &str) -> String {
    for (i, (x, y)) in a.lines().zip(b.lines()).enumerate() {
        if x != y {
            return format!(
                "first divergence at line {}: {} != {}",
                i + 1,
                trunc(x, 120),
                trunc(y, 120)
            );
        }
    }
    format!(
        "outputs diverge in length: {} vs {} bytes",
        a.len(),
        b.len()
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    /// The gate: every generated graph, every extractor, all three
    /// invariants. `FUZZ_CASES` scales the campaign; the default keeps
    /// `cargo test` (and so `scripts/verify.sh`) fast.
    #[test]
    fn fuzz_extractors_never_panic_and_are_byte_stable() {
        let cases = cases_from_env(1_000);
        let out = run(0xFA22_C0DE, cases);
        assert_eq!(out.cases, cases);
        assert!(
            out.passed(),
            "extractor fuzz failures ({} case(s) affected, {} total cases):\n{}",
            out.failures.len(),
            out.cases,
            out.report()
        );
    }

    /// Replay a single case: `FUZZ_SEED=0x... cargo test -p trailtracker-eval
    /// fuzz_seed_replays_clean`. A no-op when the env var is unset.
    #[test]
    fn fuzz_seed_replays_clean() {
        let Ok(raw) = std::env::var("FUZZ_SEED") else {
            return;
        };
        let t = raw.trim();
        let seed = t
            .strip_prefix("0x")
            .or_else(|| t.strip_prefix("0X"))
            .map(|h| u64::from_str_radix(h, 16))
            .unwrap_or_else(|| t.parse())
            .unwrap_or_else(|e| panic!("FUZZ_SEED={raw:?} is not a u64: {e}"));
        let failures = check_case(seed);
        assert!(
            failures.is_empty(),
            "seed 0x{seed:x} still fails:\n{}",
            failures
                .iter()
                .map(Failure::report)
                .collect::<Vec<_>>()
                .join("\n")
        );
    }

    /// Anti-vacuity: the generator must actually cover the structure it
    /// advertises — empty graphs, large graphs, every edge kind, dangling
    /// endpoints, self-loops, unicode/empty/very-long names. Deterministic,
    /// so this is a stable structural floor, not a flaky sample.
    #[test]
    fn generator_covers_the_advertised_structure() {
        let mut saw_empty = false;
        let mut max_nodes = 0usize;
        let mut edge_kinds: BTreeSet<&str> = BTreeSet::new();
        let mut node_kinds: BTreeSet<&str> = BTreeSet::new();
        let mut saw_self_loop = false;
        let mut saw_dangling = false;
        let mut saw_empty_name = false;
        let mut saw_long_name = false;
        let mut saw_non_ascii_name = false;
        for i in 0..400u64 {
            let case_seed = 0xFA22_C0DE ^ i.wrapping_mul(0x9e37_79b9_7f4a_7c15);
            let mut rng = Rng::new(case_seed);
            let g = gen_graph(&mut rng);
            saw_empty |= g.node_count() == 0;
            max_nodes = max_nodes.max(g.node_count());
            for n in g.nodes() {
                node_kinds.insert(n.kind);
                saw_empty_name |= n.name.is_empty();
                saw_long_name |= n.name.len() > 400;
                saw_non_ascii_name |= !n.name.is_ascii();
            }
            for e in g.edges() {
                edge_kinds.insert(e.kind);
                saw_self_loop |= e.from == e.to;
                saw_dangling |= !g.has_node(&e.from) || !g.has_node(&e.to);
            }
        }
        assert!(saw_empty, "no empty graph generated");
        assert!(
            max_nodes > 300,
            "no large graph generated (max {max_nodes})"
        );
        for k in EDGE_KINDS {
            assert!(edge_kinds.contains(k), "edge kind {k:?} never generated");
        }
        for k in [
            ont::FILE,
            ont::FUNCTION,
            ont::TYPE,
            ont::UNRESOLVED,
            ont::PACKAGE,
        ] {
            assert!(node_kinds.contains(k), "node kind {k:?} never generated");
        }
        assert!(saw_self_loop, "no self-loop generated");
        assert!(saw_dangling, "no dangling endpoint generated");
        assert!(saw_empty_name, "no empty name generated");
        assert!(saw_long_name, "no very long name generated");
        assert!(saw_non_ascii_name, "no unicode name generated");
    }

    /// Harness self-check: the JSONL validator must accept real output and
    /// reject planted garbage — otherwise invariant 3 is vacuous.
    #[test]
    fn jsonl_validator_accepts_valid_and_rejects_garbage() {
        for good in [
            "{}",
            "{\"a\":1}",
            "{\"a\":[1,2.5,-3e2,null,true],\"b\":{\"c\":\"d\\n\\u0001\"}}",
            "\"just a string 🦀\"",
            "-0.5",
        ] {
            assert!(json_line_ok(good), "validator rejected valid JSON: {good}");
        }
        for bad in [
            "",
            "   ",
            "{",
            "{\"a\":}",
            "{\"a\":1,}",
            "\"unterminated",
            "\"bad\\x\"",
            "\"raw\u{1}control\"",
            "1.",
            "01",
            "NaN",
            "{} trailing",
        ] {
            assert!(
                !json_line_ok(bad),
                "validator accepted invalid JSON: {bad:?}"
            );
        }
        // End-to-end: a planted invalid line inside otherwise-valid JSONL.
        let mut g = Graph::new();
        g.upsert_node(
            "a",
            ont::FILE,
            "we\"ird\\n🦀",
            vec![("path", Json::str("src/a.rs"))],
        );
        let jsonl = g.to_jsonl();
        assert!(
            first_invalid_line(&jsonl).is_none(),
            "real output must validate"
        );
        let planted = format!("{jsonl}{{broken\n");
        assert!(
            first_invalid_line(&planted).is_some(),
            "validator failed to flag a planted invalid line"
        );
    }
}
