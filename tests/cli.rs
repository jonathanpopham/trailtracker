//! Black-box integration tests for the shipped `trailtracker` CLI.
//!
//! These drive the actual compiled binary (via `CARGO_BIN_EXE_trailtracker`)
//! against a vendored corpus crate, exercising the end-to-end artifact a user
//! runs — not just the library internals.

use std::process::Command;

fn bin() -> Command {
    Command::new(env!("CARGO_BIN_EXE_trailtracker"))
}

const CORPUS: &str = "eval/corpus/calc";

#[test]
fn stats_reports_coverage_and_graph() {
    let out = bin().args(["stats", CORPUS]).output().expect("run stats");
    assert!(out.status.success(), "stats exited non-zero");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("files analyzed"),
        "missing coverage header:\n{stdout}"
    );
    assert!(
        stdout.contains("graph nodes"),
        "missing node stats:\n{stdout}"
    );
    assert!(
        stdout.contains("call resolution"),
        "missing resolution stats:\n{stdout}"
    );
}

#[test]
fn graph_emits_deterministic_jsonl() {
    let run = || {
        let out = bin().args(["graph", CORPUS]).output().expect("run graph");
        assert!(out.status.success(), "graph exited non-zero");
        String::from_utf8(out.stdout).expect("utf8 output")
    };
    let a = run();
    let b = run();
    assert_eq!(a, b, "graph output must be deterministic across runs");

    // Every line is a JSON record with a discriminator, and both kinds appear.
    assert!(!a.trim().is_empty(), "graph output was empty");
    for line in a.lines() {
        assert!(
            line.contains("\"record\""),
            "line missing record field: {line}"
        );
    }
    assert!(a.contains("\"record\":\"node\""), "no node records");
    assert!(a.contains("\"record\":\"edge\""), "no edge records");
    // The corpus deliberately contains a call; a CALLS edge must be present.
    assert!(a.contains("\"CALLS\""), "expected at least one CALLS edge");
}

/// The CPG overlay contract (ADR-0003): `cpg` output is byte-deterministic,
/// a strict superset of `graph` output, and actually carries the overlay
/// (Statement nodes, FLOWS_TO control flow, DATA_DEP def-use).
#[test]
fn cpg_is_a_deterministic_superset_of_graph() {
    let run = |cmd: &str| {
        let out = bin().args([cmd, CORPUS]).output().expect("run");
        assert!(out.status.success(), "{cmd} exited non-zero");
        String::from_utf8(out.stdout).expect("utf8 output")
    };
    let a = run("cpg");
    let b = run("cpg");
    assert_eq!(a, b, "cpg output must be deterministic across runs");

    // Strict superset: every base-graph line appears in the cpg output.
    let base = run("graph");
    let cpg_lines: std::collections::BTreeSet<&str> = a.lines().collect();
    for line in base.lines() {
        assert!(
            cpg_lines.contains(line),
            "base graph line missing from cpg output: {line}"
        );
    }
    assert!(
        a.lines().count() > base.lines().count(),
        "cpg output must add overlay records"
    );

    // The overlay is present.
    assert!(
        a.contains("\"kind\":\"Statement\""),
        "no Statement nodes in cpg output"
    );
    assert!(
        a.contains("\"FLOWS_TO\""),
        "no FLOWS_TO edges in cpg output"
    );
    assert!(
        a.contains("\"DATA_DEP\""),
        "no DATA_DEP edges in cpg output"
    );
    // And the base graph never carries it.
    assert!(
        !base.contains("\"kind\":\"Statement\""),
        "base graph must not contain Statement nodes"
    );
}

/// Golden-shape test for `brief`: every section renders and the calc corpus's
/// key names appear, without pinning exact counts (robust to graph growth).
#[test]
fn brief_renders_codebase_model_for_calc() {
    let run = || {
        let out = bin().args(["brief", CORPUS]).output().expect("run brief");
        assert!(out.status.success(), "brief exited non-zero");
        String::from_utf8(out.stdout).expect("utf8 output")
    };
    let md = run();

    // All sections present.
    for section in [
        "# Codebase brief: eval/corpus/calc",
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

    // Key names from the calc corpus, count-agnostic.
    assert!(
        md.contains("- rust — "),
        "rust language line missing:\n{md}"
    );
    assert!(md.contains("src/ops.rs"), "ops.rs missing:\n{md}");
    assert!(md.contains("src/parser.rs"), "parser.rs missing:\n{md}");
    // lib.rs calls into ops.rs and parser.rs — a cross-file dependency edge.
    assert!(
        md.contains("src/lib.rs -> src/ops.rs"),
        "module dependency map missing lib->ops:\n{md}"
    );
    // Engine methods are the most externally referenced surface.
    assert!(md.contains("Engine"), "Engine hotspot missing:\n{md}");
    // calc is a library: no main.
    assert!(
        md.contains("_none detected — likely a library_"),
        "calc should have no main:\n{md}"
    );
    // Synthesis paragraph is present and non-empty.
    let synthesis = md.split("## What this repo is").nth(1).expect("synthesis");
    assert!(
        synthesis.trim().len() > 50,
        "synthesis too short:\n{synthesis}"
    );

    // Deterministic across runs.
    assert_eq!(md, run(), "brief output must be deterministic");
}

#[test]
fn help_lists_commands() {
    let out = bin().arg("help").output().expect("run help");
    assert!(out.status.success());
    let stdout = String::from_utf8_lossy(&out.stdout);
    for cmd in ["graph", "stats", "parse"] {
        assert!(stdout.contains(cmd), "help missing `{cmd}`");
    }
}

#[test]
fn unknown_command_fails_cleanly() {
    let out = bin().arg("definitely-not-a-command").output().expect("run");
    assert!(
        !out.status.success(),
        "unknown command should exit non-zero"
    );
}

// ---------------------------------------------------------------------------
// `export ontoloom` — the wire document must be exactly what Ontoloom's
// importer (`Graph::from_wire`) accepts: `{name?, nodes:[{id, labels[],
// caption, properties{}, x, y}], relationships:[{id, type, from, to,
// properties{}}]}`, unique node ids, no dangling endpoints.
// ---------------------------------------------------------------------------

/// Minimal test-only JSON parser (the crate's JSON module is deliberately
/// writer-only). Just enough to validate the exported wire document.
mod mini_json {
    #[derive(Debug, PartialEq)]
    pub enum V {
        Null,
        Bool(bool),
        Num(f64),
        Str(String),
        Arr(Vec<V>),
        Obj(Vec<(String, V)>),
    }

    impl V {
        pub fn get(&self, key: &str) -> Option<&V> {
            match self {
                V::Obj(pairs) => pairs.iter().find(|(k, _)| k == key).map(|(_, v)| v),
                _ => None,
            }
        }
        pub fn as_str(&self) -> Option<&str> {
            match self {
                V::Str(s) => Some(s),
                _ => None,
            }
        }
        pub fn as_arr(&self) -> Option<&[V]> {
            match self {
                V::Arr(items) => Some(items),
                _ => None,
            }
        }
    }

    pub fn parse(text: &str) -> Result<V, String> {
        let chars: Vec<char> = text.chars().collect();
        let mut i = 0;
        let v = value(&chars, &mut i)?;
        ws(&chars, &mut i);
        if i != chars.len() {
            return Err(format!("trailing data at char {i}"));
        }
        Ok(v)
    }

    fn ws(c: &[char], i: &mut usize) {
        while *i < c.len() && c[*i].is_whitespace() {
            *i += 1;
        }
    }

    fn value(c: &[char], i: &mut usize) -> Result<V, String> {
        ws(c, i);
        match c.get(*i) {
            Some('{') => {
                *i += 1;
                let mut pairs = Vec::new();
                ws(c, i);
                if c.get(*i) == Some(&'}') {
                    *i += 1;
                    return Ok(V::Obj(pairs));
                }
                loop {
                    ws(c, i);
                    let V::Str(key) = value(c, i)? else {
                        return Err("object key is not a string".into());
                    };
                    ws(c, i);
                    if c.get(*i) != Some(&':') {
                        return Err(format!("expected ':' at char {i}"));
                    }
                    *i += 1;
                    pairs.push((key, value(c, i)?));
                    ws(c, i);
                    match c.get(*i) {
                        Some(',') => *i += 1,
                        Some('}') => {
                            *i += 1;
                            return Ok(V::Obj(pairs));
                        }
                        other => return Err(format!("expected ',' or '}}', got {other:?}")),
                    }
                }
            }
            Some('[') => {
                *i += 1;
                let mut items = Vec::new();
                ws(c, i);
                if c.get(*i) == Some(&']') {
                    *i += 1;
                    return Ok(V::Arr(items));
                }
                loop {
                    items.push(value(c, i)?);
                    ws(c, i);
                    match c.get(*i) {
                        Some(',') => *i += 1,
                        Some(']') => {
                            *i += 1;
                            return Ok(V::Arr(items));
                        }
                        other => return Err(format!("expected ',' or ']', got {other:?}")),
                    }
                }
            }
            Some('"') => {
                *i += 1;
                let mut s = String::new();
                loop {
                    match c.get(*i) {
                        Some('"') => {
                            *i += 1;
                            return Ok(V::Str(s));
                        }
                        Some('\\') => {
                            *i += 1;
                            match c.get(*i) {
                                Some('n') => s.push('\n'),
                                Some('t') => s.push('\t'),
                                Some('r') => s.push('\r'),
                                Some('b') => s.push('\u{08}'),
                                Some('f') => s.push('\u{0C}'),
                                Some('u') => {
                                    let hex: String = c[*i + 1..*i + 5].iter().collect();
                                    let n = u32::from_str_radix(&hex, 16)
                                        .map_err(|e| format!("bad \\u escape: {e}"))?;
                                    s.push(char::from_u32(n).ok_or("bad codepoint")?);
                                    *i += 4;
                                }
                                Some(other) => s.push(*other),
                                None => return Err("unterminated escape".into()),
                            }
                            *i += 1;
                        }
                        Some(ch) => {
                            s.push(*ch);
                            *i += 1;
                        }
                        None => return Err("unterminated string".into()),
                    }
                }
            }
            Some(ch) if *ch == '-' || ch.is_ascii_digit() => {
                let start = *i;
                *i += 1;
                while matches!(c.get(*i), Some(d) if d.is_ascii_digit() || matches!(d, '.' | 'e' | 'E' | '+' | '-'))
                {
                    *i += 1;
                }
                let raw: String = c[start..*i].iter().collect();
                raw.parse::<f64>()
                    .map(V::Num)
                    .map_err(|e| format!("bad number '{raw}': {e}"))
            }
            Some('t') if c[*i..].starts_with(&['t', 'r', 'u', 'e']) => {
                *i += 4;
                Ok(V::Bool(true))
            }
            Some('f') if c[*i..].starts_with(&['f', 'a', 'l', 's', 'e']) => {
                *i += 5;
                Ok(V::Bool(false))
            }
            Some('n') if c[*i..].starts_with(&['n', 'u', 'l', 'l']) => {
                *i += 4;
                Ok(V::Null)
            }
            other => Err(format!("unexpected {other:?} at char {i}")),
        }
    }
}

/// Run `export ontoloom` and validate the document against the exact contract
/// of Ontoloom's `Graph::from_wire`. Returns the parsed document.
fn export_and_validate(args: &[&str]) -> mini_json::V {
    use std::collections::BTreeSet;

    let out = bin().args(args).output().expect("run export");
    assert!(
        out.status.success(),
        "export exited non-zero: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let text = String::from_utf8(out.stdout).expect("utf8 output");
    let doc = mini_json::parse(text.trim_end()).expect("export output must be valid JSON");

    let nodes = doc
        .get("nodes")
        .and_then(|v| v.as_arr())
        .expect("top-level 'nodes' array");
    assert!(!nodes.is_empty(), "nodes must be non-empty");
    let mut ids: BTreeSet<&str> = BTreeSet::new();
    for n in nodes {
        let id = n
            .get("id")
            .and_then(|v| v.as_str())
            .expect("node id string");
        assert!(ids.insert(id), "duplicate node id '{id}'");
        let labels = n
            .get("labels")
            .and_then(|v| v.as_arr())
            .unwrap_or_else(|| panic!("node '{id}' labels array"));
        assert!(
            !labels.is_empty() && labels.iter().all(|l| l.as_str().is_some()),
            "node '{id}' labels must be non-empty strings"
        );
        n.get("caption")
            .and_then(|v| v.as_str())
            .unwrap_or_else(|| panic!("node '{id}' caption string"));
        assert!(
            matches!(n.get("properties"), Some(mini_json::V::Obj(_))),
            "node '{id}' properties object"
        );
        for coord in ["x", "y"] {
            assert!(
                matches!(n.get(coord), Some(mini_json::V::Num(_))),
                "node '{id}' {coord} must be a number"
            );
        }
    }

    let rels = doc
        .get("relationships")
        .and_then(|v| v.as_arr())
        .expect("top-level 'relationships' array");
    assert!(!rels.is_empty(), "relationships must be non-empty");
    let mut rel_ids: BTreeSet<&str> = BTreeSet::new();
    for r in rels {
        let id = r
            .get("id")
            .and_then(|v| v.as_str())
            .expect("relationship id string");
        assert!(rel_ids.insert(id), "duplicate relationship id '{id}'");
        r.get("type")
            .and_then(|v| v.as_str())
            .unwrap_or_else(|| panic!("relationship '{id}' type string"));
        for endpoint in ["from", "to"] {
            let node = r
                .get(endpoint)
                .and_then(|v| v.as_str())
                .unwrap_or_else(|| panic!("relationship '{id}' {endpoint} string"));
            assert!(
                ids.contains(node),
                "relationship '{id}' {endpoint} references missing node '{node}' — Ontoloom would reject this graph"
            );
        }
        assert!(
            matches!(r.get("properties"), Some(mini_json::V::Obj(_))),
            "relationship '{id}' properties object"
        );
    }
    doc
}

#[test]
fn export_ontoloom_hierarchy_round_trips_for_calc() {
    let doc = export_and_validate(&["export", "ontoloom", CORPUS]);
    assert_eq!(
        doc.get("name").and_then(|v| v.as_str()),
        Some("calc (hierarchy)"),
        "graph name should carry the dir + view"
    );

    // The default hierarchy view must carry level labels Ontoloom can pivot on.
    let nodes = doc.get("nodes").and_then(|v| v.as_arr()).unwrap();
    let has_label = |label: &str| {
        nodes.iter().any(|n| {
            n.get("labels")
                .and_then(|v| v.as_arr())
                .is_some_and(|ls| ls.iter().any(|l| l.as_str() == Some(label)))
        })
    };
    assert!(has_label("Unit"), "no Unit-level node in hierarchy export");
    assert!(has_label("File"), "no File node in hierarchy export");
    assert!(
        has_label("Symbol"),
        "no Symbol-level node in hierarchy export"
    );

    // Seed layout: nodes must not all be stacked on one point.
    let positions: std::collections::BTreeSet<String> = nodes
        .iter()
        .map(|n| {
            let num = |k: &str| match n.get(k) {
                Some(mini_json::V::Num(v)) => *v,
                _ => f64::NAN,
            };
            format!("{},{}", num("x"), num("y"))
        })
        .collect();
    assert!(
        positions.len() > 1,
        "all nodes share one position — seed layout missing"
    );

    // Byte-stable across runs.
    let run = || {
        bin()
            .args(["export", "ontoloom", CORPUS])
            .output()
            .expect("run export")
            .stdout
    };
    assert_eq!(run(), run(), "export must be byte-identical across runs");
}

#[test]
fn export_ontoloom_base_graph_view_is_loadable() {
    export_and_validate(&["export", "ontoloom", CORPUS, "--view", "graph"]);
}

/// UBS audit C2: `export` must reject surplus positionals with the standard
/// usage error, exactly like every `split_args` command — a mistyped
/// `export ontoloom . domains` (forgotten `--view`) must never silently
/// export the default view.
#[test]
fn export_rejects_extra_positionals() {
    for args in [
        &["export", "ontoloom", CORPUS, "bogus"][..],
        &["export", "ontoloom", CORPUS, "domains", "another-one"][..],
    ] {
        let out = bin().args(args).output().expect("run export");
        assert_eq!(
            out.status.code(),
            Some(2),
            "{args:?} must exit 2 (usage), stderr: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        let err = String::from_utf8_lossy(&out.stderr);
        assert!(
            err.contains("trailtracker: `export` takes at most 2 positional argument(s)"),
            "standard surplus-positional message missing: {err}"
        );
        assert!(err.contains("fix:"), "fix line missing: {err}");
        assert!(out.stdout.is_empty(), "errors must not pollute stdout");
    }
}

/// UBS audit C1: a consumer that closes stdout early (`| head -n 0`) must see
/// a clean exit 0, never a broken-pipe panic (exit 101). `graph`/`extract`
/// already tolerated this via `write_stdout`; these are the command paths
/// that used to `println!`/`print!` and panic.
#[test]
fn closed_stdout_pipe_is_tolerated_not_a_panic() {
    use std::process::Stdio;
    for args in [
        &["stats", CORPUS][..],
        &["stats", CORPUS, "--json"][..],
        &["report", CORPUS][..],
        &["brief", CORPUS, "--json"][..],
        &["query", "deepest-flows", CORPUS][..],
        &["search", "parse", CORPUS][..],
        &["search", "parse", CORPUS, "--json"][..],
        &["explain", "parse", CORPUS][..],
        &["explain", "parse", CORPUS, "--json"][..],
        &["parse", "eval/corpus/calc/src/lib.rs"][..],
        &["capabilities"][..],
        &["version"][..],
        &["help"][..],
    ] {
        let mut child = bin()
            .args(args)
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .expect("spawn trailtracker");
        // Close the read end before the command writes: every subsequent
        // stdout write hits EPIPE.
        drop(child.stdout.take());
        let status = child.wait().expect("wait for trailtracker");
        assert_eq!(
            status.code(),
            Some(0),
            "{args:?} must exit 0 with a closed stdout pipe (panic = exit 101)"
        );
    }
}

#[test]
fn export_rejects_unknown_format_and_view() {
    let out = bin()
        .args(["export", "graphviz", CORPUS])
        .output()
        .expect("run");
    assert!(!out.status.success(), "unknown format must exit non-zero");
    let out = bin()
        .args(["export", "ontoloom", CORPUS, "--view", "nope"])
        .output()
        .expect("run");
    assert!(!out.status.success(), "unknown view must exit non-zero");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(
        err.contains("hierarchy"),
        "error should list available views: {err}"
    );
}

// ---------------------------------------------------------------------------
// Agent-ergonomics contract (w1/cli-ergonomics): machine-readable help, --json
// modes, exit-code dictionary, and intent inference. Every test here pins a
// surface documented by `trailtracker capabilities`.
// ---------------------------------------------------------------------------

/// Run the binary, asserting success, and return stdout.
fn stdout_of(args: &[&str]) -> String {
    let out = bin().args(args).output().expect("run trailtracker");
    assert!(
        out.status.success(),
        "{args:?} exited non-zero: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).expect("utf8 stdout")
}

#[test]
fn version_prints_semver() {
    for invocation in [&["version"][..], &["--version"][..], &["-V"][..]] {
        let out = stdout_of(invocation);
        assert!(
            out.starts_with("trailtracker ") && out.trim().split('.').count() >= 3,
            "unexpected version output for {invocation:?}: {out}"
        );
    }
}

#[test]
fn capabilities_is_the_machine_contract() {
    let text = stdout_of(&["capabilities"]);
    let doc = mini_json::parse(text.trim_end()).expect("capabilities must be valid JSON");

    assert_eq!(
        doc.get("schema").and_then(|v| v.as_str()),
        Some("trailtracker.capabilities/v1")
    );

    // Every dispatchable command is documented with usage + output shape.
    let commands = doc
        .get("commands")
        .and_then(|v| v.as_arr())
        .expect("commands");
    let names: Vec<&str> = commands
        .iter()
        .filter_map(|c| c.get("name").and_then(|v| v.as_str()))
        .collect();
    for expected in [
        "graph",
        "stats",
        "parse",
        "extract",
        "export",
        "deadcode",
        "query",
        "explain",
        "search",
        "report",
        "brief",
        "rebuild-brief",
        "capabilities",
        "version",
        "help",
    ] {
        assert!(
            names.contains(&expected),
            "command '{expected}' undocumented"
        );
    }
    for c in commands {
        assert!(
            c.get("usage").and_then(|v| v.as_str()).is_some(),
            "usage missing"
        );
        assert!(c.get("output").is_some(), "output shape missing");
    }

    // The extractor list is generated from the registry (no help drift): all 7.
    let extractors = doc
        .get("extractors")
        .and_then(|v| v.as_arr())
        .expect("extractors");
    assert_eq!(extractors.len(), 7, "expected 7 extractors");
    for e in [
        "data-ontology",
        "domains",
        "hierarchy",
        "layers",
        "lexicon",
        "archetypes",
        "workflow-spec",
    ] {
        assert!(
            extractors.iter().any(|x| x.as_str() == Some(e)),
            "extractor '{e}' missing from capabilities"
        );
    }

    // Exit-code dictionary is pinned.
    let codes = doc.get("exit_codes").expect("exit_codes");
    for k in ["0", "1", "2", "3", "4"] {
        assert!(codes.get(k).is_some(), "exit code {k} undocumented");
    }

    // `help --json` returns the identical document.
    assert_eq!(
        text,
        stdout_of(&["help", "--json"]),
        "help --json != capabilities"
    );
    // Deterministic across runs.
    assert_eq!(
        text,
        stdout_of(&["capabilities"]),
        "capabilities not deterministic"
    );
}

#[test]
fn stats_json_matches_schema_and_is_deterministic() {
    let text = stdout_of(&["stats", CORPUS, "--json"]);
    let doc = mini_json::parse(text.trim_end()).expect("stats --json must be valid JSON");
    assert_eq!(
        doc.get("schema").and_then(|v| v.as_str()),
        Some("trailtracker.stats/v1")
    );
    assert_eq!(doc.get("dir").and_then(|v| v.as_str()), Some(CORPUS));
    for key in [
        "files",
        "lossless_files",
        "parse",
        "nodes",
        "edges",
        "calls",
    ] {
        assert!(doc.get(key).is_some(), "stats --json missing '{key}'");
    }
    let nodes = doc.get("nodes").expect("nodes");
    assert!(
        matches!(nodes.get("total"), Some(mini_json::V::Num(n)) if *n > 0.0),
        "nodes.total must be positive"
    );
    assert!(nodes.get("by_kind").is_some(), "nodes.by_kind missing");
    assert_eq!(
        text,
        stdout_of(&["stats", CORPUS, "--json"]),
        "stats --json not deterministic"
    );
    // `--robot` is a synonym.
    assert_eq!(text, stdout_of(&["stats", CORPUS, "--robot"]));
}

#[test]
fn brief_json_matches_schema_and_is_deterministic() {
    let text = stdout_of(&["brief", CORPUS, "--json"]);
    let doc = mini_json::parse(text.trim_end()).expect("brief --json must be valid JSON");
    assert_eq!(
        doc.get("schema").and_then(|v| v.as_str()),
        Some("trailtracker.brief/v1")
    );
    for key in [
        "overview",
        "architecture",
        "entry_points",
        "hotspots",
        "cycles",
        "synthesis",
    ] {
        assert!(doc.get(key).is_some(), "brief --json missing '{key}'");
    }
    let overview = doc.get("overview").expect("overview");
    let langs = overview
        .get("languages")
        .and_then(|v| v.as_arr())
        .expect("languages");
    assert!(
        langs
            .iter()
            .any(|l| l.get("language").and_then(|v| v.as_str()) == Some("rust")),
        "rust language entry missing"
    );
    // The structured brief carries the same signal as the markdown sections.
    let units = doc
        .get("architecture")
        .and_then(|a| a.get("largest_units"))
        .and_then(|v| v.as_arr())
        .expect("largest_units");
    assert!(!units.is_empty(), "largest_units empty");
    let synthesis = doc
        .get("synthesis")
        .and_then(|v| v.as_str())
        .expect("synthesis");
    assert!(synthesis.len() > 50, "synthesis too short: {synthesis}");
    assert!(
        !synthesis.starts_with('#'),
        "synthesis should not carry the markdown header"
    );
    assert_eq!(
        text,
        stdout_of(&["brief", CORPUS, "--json"]),
        "brief --json not deterministic"
    );
}

#[test]
fn report_json_wraps_markdown_envelope() {
    let text = stdout_of(&["report", CORPUS, "--json"]);
    let doc = mini_json::parse(text.trim_end()).expect("report --json must be valid JSON");
    assert_eq!(
        doc.get("schema").and_then(|v| v.as_str()),
        Some("trailtracker.markdown/v1")
    );
    assert_eq!(doc.get("format").and_then(|v| v.as_str()), Some("markdown"));
    let md = doc
        .get("markdown")
        .and_then(|v| v.as_str())
        .expect("markdown");
    // Envelope carries exactly the default output.
    assert_eq!(
        md,
        stdout_of(&["report", CORPUS]),
        "envelope markdown != default output"
    );
}

#[test]
fn json_flag_is_a_noop_on_already_json_commands() {
    // The two hard consumer contracts: default stdout of `graph`/`extract`
    // must not change, and --json/--robot must not change it either.
    assert_eq!(
        stdout_of(&["graph", CORPUS]),
        stdout_of(&["graph", CORPUS, "--json"])
    );
    assert_eq!(
        stdout_of(&["extract", "data-ontology", CORPUS]),
        stdout_of(&["extract", "data-ontology", CORPUS, "--robot"])
    );
}

// ---------------------------------------------------------------------------
// `search` (G2): hybrid search exposed as a CLI command. Human output carries
// rank, 3dp score, name (kind), path, and why-signals; --json emits schema
// trailtracker.search/v1.
// ---------------------------------------------------------------------------

#[test]
fn search_human_output_ranks_and_explains() {
    let out = stdout_of(&["search", "parse", CORPUS]);
    // Header names the query, the dir, and the result count.
    assert!(
        out.starts_with(&format!("search \"parse\" in {CORPUS} — ")),
        "header missing:\n{out}"
    );
    // Rank 1 is the parse function, with a 3dp score and its kind.
    let first = out.lines().nth(1).expect("at least one result line");
    assert!(
        first.trim_start().starts_with("1. "),
        "rank prefix missing: {first}"
    );
    assert!(
        first.contains("parse (Function)"),
        "top hit must be the parse fn with its kind: {first}"
    );
    // Score is exactly 3 decimal places: "1. 0.033  parse ...".
    let score = first
        .trim_start()
        .strip_prefix("1. ")
        .unwrap()
        .split_whitespace()
        .next()
        .unwrap();
    let (int, frac) = score.split_once('.').expect("score has a decimal point");
    assert!(
        int.chars().all(|c| c.is_ascii_digit()) && frac.len() == 3,
        "score not 3dp: {score}"
    );
    // Why-signals are rendered, joined with " · " when multiple.
    assert!(
        out.contains("bm25 #1"),
        "why-signals missing from human output:\n{out}"
    );
    // A File hit carries its path on the result line.
    assert!(
        out.contains("parser.rs (File)  src/parser.rs"),
        "path missing for file hit:\n{out}"
    );
    // Deterministic across runs.
    assert_eq!(out, stdout_of(&["search", "parse", CORPUS]));
}

#[test]
fn search_json_matches_schema() {
    let text = stdout_of(&["search", "parse", CORPUS, "--json"]);
    let doc = mini_json::parse(text.trim_end()).expect("search --json must be valid JSON");
    assert_eq!(
        doc.get("schema").and_then(|v| v.as_str()),
        Some("trailtracker.search/v1")
    );
    assert_eq!(doc.get("query").and_then(|v| v.as_str()), Some("parse"));
    assert_eq!(doc.get("dir").and_then(|v| v.as_str()), Some(CORPUS));
    let results = doc
        .get("results")
        .and_then(|v| v.as_arr())
        .expect("results array");
    assert!(
        matches!(doc.get("total"), Some(mini_json::V::Num(n)) if *n as usize == results.len()),
        "total must equal results length"
    );
    assert!(!results.is_empty(), "'parse' must hit in the calc corpus");
    for (i, r) in results.iter().enumerate() {
        assert!(
            matches!(r.get("rank"), Some(mini_json::V::Num(n)) if *n as usize == i + 1),
            "ranks must be 1-based and ascending"
        );
        for key in ["id", "name", "kind", "path"] {
            assert!(
                r.get(key).and_then(|v| v.as_str()).is_some(),
                "result missing string '{key}'"
            );
        }
        assert!(
            matches!(r.get("score"), Some(mini_json::V::Num(n)) if *n > 0.0),
            "score must be positive"
        );
        let why = r.get("why").and_then(|v| v.as_arr()).expect("why array");
        assert!(
            !why.is_empty() && why.iter().all(|w| w.as_str().is_some()),
            "every result must explain itself"
        );
    }
    let top = &results[0];
    assert_eq!(top.get("name").and_then(|v| v.as_str()), Some("parse"));
    assert_eq!(top.get("kind").and_then(|v| v.as_str()), Some("Function"));
    // Deterministic, and --robot is a synonym.
    assert_eq!(text, stdout_of(&["search", "parse", CORPUS, "--json"]));
    assert_eq!(text, stdout_of(&["search", "parse", CORPUS, "--robot"]));
}

#[test]
fn search_limit_caps_results() {
    let text = stdout_of(&["search", "parse", CORPUS, "--json", "--limit", "1"]);
    let doc = mini_json::parse(text.trim_end()).expect("valid JSON");
    let results = doc.get("results").and_then(|v| v.as_arr()).unwrap();
    assert_eq!(results.len(), 1, "--limit 1 must return exactly one hit");
    // --limit=N spelling is equivalent.
    assert_eq!(
        text,
        stdout_of(&["search", "parse", CORPUS, "--json", "--limit=1"])
    );
}

#[test]
fn search_usage_errors_exit_2_with_fix() {
    // Empty query.
    for args in [
        &["search"][..],
        &["search", "", CORPUS][..],
        &["search", "   ", CORPUS][..],
    ] {
        let out = bin().args(args).output().expect("run search");
        assert_eq!(out.status.code(), Some(2), "{args:?} must exit 2 (usage)");
        let err = String::from_utf8_lossy(&out.stderr);
        assert!(
            err.contains("trailtracker: search requires a non-empty <query>"),
            "message missing for {args:?}: {err}"
        );
        assert!(err.contains("fix:"), "fix line missing: {err}");
        assert!(out.stdout.is_empty(), "errors must not pollute stdout");
    }
    // Bad --limit value.
    let out = bin()
        .args(["search", "parse", CORPUS, "--limit", "lots"])
        .output()
        .expect("run search");
    assert_eq!(out.status.code(), Some(2), "bad --limit must exit 2");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("--limit"), "limit error missing: {err}");
    // Surplus positionals (unquoted multi-word query).
    let out = bin()
        .args(["search", "basket", "repository", CORPUS])
        .output()
        .expect("run search");
    assert_eq!(
        out.status.code(),
        Some(2),
        "surplus positionals must exit 2"
    );
    // Unknown flag gets a did-you-mean.
    let out = bin()
        .args(["search", "parse", CORPUS, "--limt", "5"])
        .output()
        .expect("run search");
    assert_eq!(out.status.code(), Some(2));
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("--limit"), "did-you-mean missing: {err}");
}

#[test]
fn search_missing_dir_exits_3() {
    let out = bin()
        .args(["search", "parse", "/no/such/dir-for-tt-search"])
        .output()
        .expect("run search");
    assert_eq!(out.status.code(), Some(3), "missing dir must exit 3");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("does not exist"), "path error missing: {err}");
}

#[test]
fn search_no_hits_is_success_with_empty_results() {
    // "///" carries no alphanumeric n-grams: neither tier can produce
    // evidence, so the result list is empty — a success, not an error.
    let text = stdout_of(&["search", "///", CORPUS, "--json"]);
    let doc = mini_json::parse(text.trim_end()).expect("valid JSON");
    assert!(
        matches!(doc.get("total"), Some(mini_json::V::Num(n)) if *n == 0.0),
        "featureless query must return total 0, not an error"
    );
    let human = stdout_of(&["search", "///", CORPUS]);
    assert!(
        human.contains("— 0 results"),
        "human output must state 0 results: {human}"
    );
}

// ---------------------------------------------------------------------------
// `explain` (N2): the atomic understanding primitive — one card per file or
// symbol. Text card sections, --json schema trailtracker.explain/v1, and the
// resolution contract (ambiguous name = exit 2, unknown target = exit 3).
// ---------------------------------------------------------------------------

#[test]
fn explain_renders_the_card_for_a_symbol() {
    let out = stdout_of(&["explain", "parse", CORPUS]);
    assert!(
        out.starts_with("explain: parse (Function) — fn::crate::parser::parse#7"),
        "header wrong:\n{out}"
    );
    for section in [
        "  identity",
        "    path        src/parser.rs:7",
        "    qualified   crate::parser::parse",
        "  classification",
        "    domain      ",
        "    layer       ",
        "    archetype   ",
        "  connectivity",
        "    fan-in ",
        "    dependents (",
        "    dependencies (",
        "  blast radius",
        "  neighbors (hybrid search: \"parse\")",
    ] {
        assert!(out.contains(section), "missing `{section}`:\n{out}");
    }
    // The known dependent shows up by name with its id.
    assert!(
        out.contains("evaluate (Function) — fn::crate::evaluate#11"),
        "dependent listing missing:\n{out}"
    );
    // Deterministic across runs.
    assert_eq!(out, stdout_of(&["explain", "parse", CORPUS]));
}

#[test]
fn explain_accepts_a_file_path_and_an_exact_id() {
    let by_path = stdout_of(&["explain", "src/parser.rs", CORPUS]);
    assert!(
        by_path.starts_with("explain: parser.rs (File) — file::src/parser.rs"),
        "file-path target must resolve to the File node:\n{by_path}"
    );
    // Exact id and unique name resolve to the same card.
    assert_eq!(
        stdout_of(&["explain", "fn::crate::parser::parse#7", CORPUS]),
        stdout_of(&["explain", "parse", CORPUS])
    );
}

#[test]
fn explain_json_matches_schema() {
    let text = stdout_of(&["explain", "parse", CORPUS, "--json"]);
    let doc = mini_json::parse(text.trim_end()).expect("explain --json must be valid JSON");
    assert_eq!(
        doc.get("schema").and_then(|v| v.as_str()),
        Some("trailtracker.explain/v1")
    );
    assert_eq!(doc.get("dir").and_then(|v| v.as_str()), Some(CORPUS));
    assert_eq!(doc.get("target").and_then(|v| v.as_str()), Some("parse"));

    let identity = doc.get("identity").expect("identity");
    assert_eq!(
        identity.get("id").and_then(|v| v.as_str()),
        Some("fn::crate::parser::parse#7")
    );
    assert_eq!(
        identity.get("qualified_name").and_then(|v| v.as_str()),
        Some("crate::parser::parse")
    );
    assert_eq!(
        identity.get("path").and_then(|v| v.as_str()),
        Some("src/parser.rs")
    );
    assert!(
        matches!(identity.get("line"), Some(mini_json::V::Num(n)) if *n == 7.0),
        "line must be 7"
    );

    let classification = doc.get("classification").expect("classification");
    for key in ["domain", "layer", "archetype"] {
        assert!(
            classification
                .get(key)
                .and_then(|v| v.as_str())
                .is_some_and(|s| !s.is_empty()),
            "classification.{key} missing"
        );
    }

    let connectivity = doc.get("connectivity").expect("connectivity");
    for key in ["fan_in", "fan_out"] {
        assert!(
            matches!(connectivity.get(key), Some(mini_json::V::Num(n)) if *n >= 0.0),
            "connectivity.{key} missing"
        );
    }
    for key in ["dependents", "dependencies"] {
        let arr = connectivity.get(key).and_then(|v| v.as_arr()).expect(key);
        for r in arr {
            for f in ["id", "name", "kind"] {
                assert!(r.get(f).and_then(|v| v.as_str()).is_some(), "{key}.{f}");
            }
        }
    }

    let blast = doc.get("blast_radius").expect("blast_radius");
    assert!(
        matches!(blast.get("count"), Some(mini_json::V::Num(n)) if *n > 0.0),
        "blast count must be positive for parse"
    );
    assert!(blast.get("examples").and_then(|v| v.as_arr()).is_some());

    let neighbors = doc
        .get("neighbors")
        .and_then(|v| v.as_arr())
        .expect("neighbors");
    for (i, n) in neighbors.iter().enumerate() {
        assert!(
            matches!(n.get("rank"), Some(mini_json::V::Num(r)) if *r as usize == i + 1),
            "neighbor ranks must be 1-based ascending"
        );
        // The target itself never appears among its neighbors.
        assert_ne!(
            n.get("id").and_then(|v| v.as_str()),
            Some("fn::crate::parser::parse#7"),
            "target must not be its own neighbor"
        );
        let why = n.get("why").and_then(|v| v.as_arr()).expect("why array");
        assert!(!why.is_empty(), "every neighbor explains itself");
    }

    // Deterministic, and --robot is a synonym.
    assert_eq!(text, stdout_of(&["explain", "parse", CORPUS, "--json"]));
    assert_eq!(text, stdout_of(&["explain", "parse", CORPUS, "--robot"]));
}

#[test]
fn explain_ambiguous_name_exits_2_with_candidates() {
    // `reset` exists as both crate::reset and crate::ops::reset.
    let out = bin()
        .args(["explain", "reset", CORPUS])
        .output()
        .expect("run explain");
    assert_eq!(out.status.code(), Some(2), "ambiguous target must exit 2");
    assert!(out.stdout.is_empty(), "errors must not pollute stdout");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(
        err.contains("target 'reset' is ambiguous"),
        "ambiguity message missing: {err}"
    );
    for candidate in ["fn::crate::reset#18", "fn::crate::ops::reset#60"] {
        assert!(
            err.contains(candidate),
            "candidate {candidate} missing: {err}"
        );
    }
    assert!(
        err.contains("fix: pass one exact node id"),
        "fix line missing: {err}"
    );
}

#[test]
fn explain_unknown_target_exits_3_with_suggestions() {
    let out = bin()
        .args(["explain", "Parsr", CORPUS])
        .output()
        .expect("run explain");
    assert_eq!(out.status.code(), Some(3), "unknown target must exit 3");
    assert!(out.stdout.is_empty(), "errors must not pollute stdout");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(
        err.contains("no node matching 'Parsr'"),
        "not-found message missing: {err}"
    );
    // The typo still surfaces the parse-family suggestions via the embed tier.
    assert!(err.contains("parse"), "search suggestions missing: {err}");
    assert!(err.contains("fix:"), "fix line missing: {err}");
}

#[test]
fn explain_usage_errors_exit_2() {
    // Missing target.
    let out = bin().args(["explain"]).output().expect("run explain");
    assert_eq!(out.status.code(), Some(2), "missing target must exit 2");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(
        err.contains("explain requires a <target>"),
        "usage message missing: {err}"
    );
    // Surplus positionals.
    let out = bin()
        .args(["explain", "parse", CORPUS, "bogus"])
        .output()
        .expect("run explain");
    assert_eq!(
        out.status.code(),
        Some(2),
        "surplus positionals must exit 2"
    );
    // Missing dir is exit 3 (path not found), not a usage error.
    let out = bin()
        .args(["explain", "parse", "/no/such/dir-for-tt-explain"])
        .output()
        .expect("run explain");
    assert_eq!(out.status.code(), Some(3), "missing dir must exit 3");
}

#[test]
fn exit_codes_follow_the_documented_dictionary() {
    // 2 = usage error.
    let out = bin().arg("definitely-not-a-command").output().expect("run");
    assert_eq!(out.status.code(), Some(2), "unknown command must exit 2");
    let out = bin()
        .args(["extract", "nope", CORPUS])
        .output()
        .expect("run");
    assert_eq!(out.status.code(), Some(2), "unknown extractor must exit 2");
    let out = bin()
        .args(["brief", CORPUS, "--jsno"])
        .output()
        .expect("run");
    assert_eq!(out.status.code(), Some(2), "unknown flag must exit 2");
    // 3 = path not found.
    let out = bin()
        .args(["stats", "/no/such/dir-for-tt"])
        .output()
        .expect("run");
    assert_eq!(out.status.code(), Some(3), "missing dir must exit 3");
    let out = bin()
        .args(["parse", "/no/such/file.rs"])
        .output()
        .expect("run");
    assert_eq!(out.status.code(), Some(3), "missing file must exit 3");
    // 0 = success, even for empty-but-existing analysis targets.
    let out = bin().args(["stats", CORPUS]).output().expect("run");
    assert_eq!(out.status.code(), Some(0));
}

#[test]
fn errors_teach_the_fix_on_stderr() {
    // Unknown command suggests the closest real command.
    let out = bin().args(["grap", CORPUS]).output().expect("run");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(
        err.contains("trailtracker:"),
        "stable error prefix missing: {err}"
    );
    assert!(err.contains("fix:"), "fix line missing: {err}");
    assert!(
        err.contains("`trailtracker graph`"),
        "did-you-mean missing: {err}"
    );
    assert!(out.stdout.is_empty(), "errors must not pollute stdout");

    // Unknown flag suggests --json.
    let out = bin()
        .args(["brief", CORPUS, "--jsno"])
        .output()
        .expect("run");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("--json"), "flag suggestion missing: {err}");

    // Unknown extractor suggests the closest name.
    let out = bin()
        .args(["extract", "domians", CORPUS])
        .output()
        .expect("run");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(
        err.contains("domains"),
        "extractor suggestion missing: {err}"
    );

    // Unknown query kind suggests the closest kind.
    let out = bin()
        .args(["query", "blastradius", "Engine", CORPUS])
        .output()
        .expect("run");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(
        err.contains("blast-radius"),
        "query-kind suggestion missing: {err}"
    );
}

#[test]
fn help_advertises_the_robot_surface() {
    let out = stdout_of(&["help"]);
    for needle in ["--json", "capabilities", "EXIT CODES", "hierarchy"] {
        assert!(out.contains(needle), "help missing '{needle}':\n{out}");
    }
    // Bare invocation prints the same overview and exits 0.
    assert_eq!(out, stdout_of(&[]), "bare invocation should print help");
}

/// The incremental cache is opt-in and invisible: `graph --incremental` is
/// byte-identical to plain `graph` — cold, warm, and after touching a file —
/// and the cache directory materializes (gitignored) next to the analyzed
/// tree.
#[test]
fn graph_incremental_is_byte_identical_and_creates_cache() {
    use std::fs;
    use std::path::Path;

    // Work on a throwaway copy of the corpus so the vendored fixture (and its
    // golden snapshots) are never dirtied.
    fn copy_tree(src: &Path, dst: &Path) {
        fs::create_dir_all(dst).unwrap();
        for e in fs::read_dir(src).unwrap().flatten() {
            let from = e.path();
            let to = dst.join(e.file_name());
            if from.is_dir() {
                copy_tree(&from, &to);
            } else {
                fs::copy(&from, &to).unwrap();
            }
        }
    }
    let tmp = std::env::temp_dir().join(format!("tt-cli-incremental-{}", std::process::id()));
    let _ = fs::remove_dir_all(&tmp);
    copy_tree(Path::new(CORPUS), &tmp);
    let dir = tmp.to_string_lossy().to_string();

    let run = |args: &[&str]| -> String {
        let out = bin().args(args).output().expect("run graph");
        assert!(out.status.success(), "graph exited non-zero");
        String::from_utf8(out.stdout).expect("utf8 output")
    };

    let plain = run(&["graph", &dir]);
    let cold = run(&["graph", &dir, "--incremental"]);
    assert_eq!(cold, plain, "cold cached run differs from uncached run");
    let cache_dir = tmp.join(".trailtracker-cache");
    assert!(cache_dir.is_dir(), "cache directory was not created");
    assert_eq!(
        fs::read_to_string(cache_dir.join(".gitignore")).unwrap(),
        "*\n",
        "cache .gitignore missing"
    );
    let warm = run(&["graph", &dir, "--incremental"]);
    assert_eq!(warm, plain, "warm cached run differs from uncached run");

    // Touch one file: stale cache vs fresh analysis must still agree.
    let lib = tmp.join("src").join("lib.rs");
    let original = fs::read_to_string(&lib).unwrap();
    fs::write(&lib, format!("{original}\n")).unwrap();
    let mixed = run(&["graph", &dir, "--incremental"]);
    let fresh = run(&["graph", &dir]);
    assert_eq!(mixed, fresh, "stale-cache run differs from fresh analysis");

    // The env var is a flagless opt-in with a redirectable location.
    let alt_cache = std::env::temp_dir().join(format!("tt-cli-altcache-{}", std::process::id()));
    let _ = fs::remove_dir_all(&alt_cache);
    let out = bin()
        .args(["graph", &dir])
        .env("TRAILTRACKER_CACHE", "1")
        .env("TRAILTRACKER_CACHE_DIR", &alt_cache)
        .output()
        .expect("run graph with env cache");
    assert!(out.status.success());
    assert_eq!(
        String::from_utf8(out.stdout).unwrap(),
        fresh,
        "env-enabled cached run differs"
    );
    assert!(alt_cache.is_dir(), "TRAILTRACKER_CACHE_DIR not honored");

    let _ = fs::remove_dir_all(&tmp);
    let _ = fs::remove_dir_all(&alt_cache);
}

// ---------------------------------------------------------------------------
// `nav` — the context-efficient codebase navigator (ADR-0004). Black-box
// pins on the CLI surface: schemas, budget honesty, cursor continuation,
// exit codes, and determinism.
// ---------------------------------------------------------------------------

#[test]
fn nav_pack_emits_schema_fits_budget_and_is_deterministic() {
    let args = [
        "nav",
        "pack",
        "parse expression",
        CORPUS,
        "--budget",
        "3000",
        "--json",
    ];
    let a = stdout_of(&args);
    assert!(a.contains("\"schema\":\"trailtracker.nav-pack/v1\""), "{a}");
    for key in [
        "\"budget_chars\":3000",
        "\"used_chars\":",
        "\"estimated_chars\":",
        "\"seeds\":",
        "\"cards\":",
        "\"orientation\":",
        "\"read_plan\":",
        "\"neighborhood\":",
    ] {
        assert!(a.contains(key), "missing {key}:\n{a}");
    }
    assert!(
        a.trim_end().len() <= 3000,
        "output ({} chars) exceeds the 3000-char budget",
        a.trim_end().len()
    );
    assert_eq!(a, stdout_of(&args), "nav pack must be deterministic");
}

#[test]
fn nav_expand_pages_with_a_cursor() {
    let full = stdout_of(&[
        "nav",
        "expand",
        "fn::crate::parser::parse#7",
        CORPUS,
        "--depth",
        "2",
        "--json",
    ]);
    assert!(
        full.contains("\"schema\":\"trailtracker.nav-expand/v1\""),
        "{full}"
    );
    assert!(full.contains("\"truncated\":false"), "{full}");
    // A tight budget must truncate and hand back a cursor.
    let page = stdout_of(&[
        "nav",
        "expand",
        "fn::crate::parser::parse#7",
        CORPUS,
        "--depth",
        "2",
        "--budget",
        "1500",
        "--json",
    ]);
    assert!(
        page.trim_end().len() <= 1500 || page.contains("\"exceeded\":true"),
        "page ({} chars) over budget without saying so",
        page.trim_end().len()
    );
    assert!(page.contains("\"truncated\":true"), "{page}");
    assert!(page.contains("\"next_cursor\":"), "{page}");
}

#[test]
fn nav_error_contract_matches_explain() {
    // Ambiguous name -> exit 2 with candidates.
    let out = bin()
        .args(["nav", "expand", "reset", CORPUS])
        .output()
        .expect("run nav expand");
    assert_eq!(out.status.code(), Some(2), "ambiguous target must exit 2");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("fn::crate::reset#18"), "{stderr}");
    // Unknown target -> exit 3 with suggestions.
    let out = bin()
        .args(["nav", "expand", "NoSuchSymbolAnywhere", CORPUS])
        .output()
        .expect("run nav expand");
    assert_eq!(out.status.code(), Some(3), "unknown target must exit 3");
    // Empty query -> exit 2.
    let out = bin()
        .args(["nav", "pack", "  ", CORPUS])
        .output()
        .expect("run nav pack");
    assert_eq!(out.status.code(), Some(2), "blank query must exit 2");
    // Unknown subcommand -> exit 2 with a hint.
    let out = bin()
        .args(["nav", "pak", CORPUS])
        .output()
        .expect("run nav");
    assert_eq!(out.status.code(), Some(2));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("pack"), "typo hint missing: {stderr}");
    // Bad direction -> exit 2 listing the valid values.
    let out = bin()
        .args(["nav", "expand", "parse", CORPUS, "--direction", "sideways"])
        .output()
        .expect("run nav expand");
    assert_eq!(out.status.code(), Some(2));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("callers"), "{stderr}");
}

#[test]
fn nav_is_documented_in_help_and_capabilities() {
    let help = stdout_of(&["help"]);
    assert!(help.contains("nav pack"), "help missing nav pack:\n{help}");
    assert!(help.contains("nav expand"), "help missing nav expand");
    let caps = stdout_of(&["capabilities"]);
    assert!(
        caps.contains("\"name\":\"nav\""),
        "capabilities missing nav command"
    );
    assert!(
        caps.contains("trailtracker.nav-pack/v1") && caps.contains("trailtracker.nav-expand/v1"),
        "capabilities must document both nav schemas"
    );
}

// ---------------------------------------------------------------------------
// rewrite (ADR-0006): the propose-then-approve contract, end to end
// ---------------------------------------------------------------------------

/// A fresh per-test directory with one rewritable fixture file. Returns
/// (dir, file path).
fn rewrite_fixture(test: &str, source: &str) -> (std::path::PathBuf, std::path::PathBuf) {
    let dir = std::env::temp_dir().join(format!("tt-rewrite-{test}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("fixture.rs");
    std::fs::write(&file, source).unwrap();
    (dir, file)
}

const REWRITE_SRC: &str = "fn doubled(xs: Vec<i32>) -> Vec<i32> {\n    let mut out = Vec::new();\n    for x in xs {\n        out.push(x * 2);\n    }\n    if false {\n        legacy(&out);\n    }\n    out\n}\n\nfn legacy(_: &[i32]) {}\n";

#[test]
fn rewrite_propose_emits_diff_and_never_writes() {
    let (dir, file) = rewrite_fixture("propose-readonly", REWRITE_SRC);
    let out = bin()
        .args([
            "rewrite",
            "propose",
            "loop-to-iterator",
            "fixture.rs",
            dir.to_str().unwrap(),
        ])
        .output()
        .expect("run propose");
    assert_eq!(out.status.code(), Some(0), "{:?}", out);
    let diff = String::from_utf8_lossy(&out.stdout);
    assert!(diff.contains("--- a/fixture.rs"), "{diff}");
    assert!(
        diff.contains("+    let mut out = xs.into_iter().map(|x| x * 2).collect::<Vec<_>>();"),
        "{diff}"
    );
    // Propose NEVER writes source.
    assert_eq!(std::fs::read_to_string(&file).unwrap(), REWRITE_SRC);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn rewrite_proposal_is_deterministic() {
    let (dir, _file) = rewrite_fixture("determinism", REWRITE_SRC);
    let run = || {
        let out = bin()
            .args([
                "rewrite",
                "propose",
                "loop-to-iterator",
                "fixture.rs",
                dir.to_str().unwrap(),
                "--json",
            ])
            .output()
            .expect("run propose --json");
        assert_eq!(out.status.code(), Some(0));
        String::from_utf8(out.stdout).unwrap()
    };
    // No timestamp anywhere (ADR-0006): same binary + same file =>
    // byte-identical proposal, hash included.
    let a = run();
    let b = run();
    assert_eq!(a, b, "proposal must be byte-deterministic");
    assert!(
        a.contains("\"schema\":\"trailtracker.rewrite-proposal/v1\""),
        "{a}"
    );
    assert!(a.contains("\"proposal_hash\":\"fnv1a64:"), "{a}");
    assert!(a.contains("\"why_safe\""), "{a}");
    assert!(a.contains("\"cpg_facts\""), "{a}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn rewrite_apply_round_trip_touches_only_the_spans() {
    let (dir, file) = rewrite_fixture("apply-spans", REWRITE_SRC);
    let proposal = dir.join("p.json");
    let out = bin()
        .args([
            "rewrite",
            "propose",
            "loop-to-iterator",
            "fixture.rs",
            dir.to_str().unwrap(),
            "-o",
            proposal.to_str().unwrap(),
        ])
        .output()
        .expect("run propose -o");
    assert_eq!(out.status.code(), Some(0));

    let out = bin()
        .args(["rewrite", "apply", "--proposal", proposal.to_str().unwrap()])
        .output()
        .expect("run apply");
    assert_eq!(out.status.code(), Some(0), "{:?}", out);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("applied 1 edit(s)"), "{stdout}");

    // Span safety: every byte outside the edited span is byte-identical.
    // The edit replaces lines 2-5 (the let+for pair); everything before the
    // pair and after the loop's closing brace must be untouched.
    let after = std::fs::read_to_string(&file).unwrap();
    let prefix = "fn doubled(xs: Vec<i32>) -> Vec<i32> {\n    ";
    let suffix =
        "\n    if false {\n        legacy(&out);\n    }\n    out\n}\n\nfn legacy(_: &[i32]) {}\n";
    assert!(after.starts_with(prefix), "prefix bytes moved:\n{after}");
    assert!(after.ends_with(suffix), "suffix bytes moved:\n{after}");
    assert_eq!(
        after,
        format!("{prefix}let mut out = xs.into_iter().map(|x| x * 2).collect::<Vec<_>>();{suffix}")
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn rewrite_apply_refuses_tampered_proposal() {
    let (dir, file) = rewrite_fixture("tamper", REWRITE_SRC);
    let proposal = dir.join("p.json");
    let out = bin()
        .args([
            "rewrite",
            "propose",
            "loop-to-iterator",
            "fixture.rs",
            dir.to_str().unwrap(),
            "-o",
            proposal.to_str().unwrap(),
        ])
        .output()
        .expect("run propose -o");
    assert_eq!(out.status.code(), Some(0));

    // Tamper with the replacement text.
    let text = std::fs::read_to_string(&proposal).unwrap();
    let tampered = text.replace("x * 2", "x * 3");
    assert_ne!(text, tampered, "tamper must hit the document");
    std::fs::write(&proposal, tampered).unwrap();

    let out = bin()
        .args(["rewrite", "apply", "--proposal", proposal.to_str().unwrap()])
        .output()
        .expect("run apply");
    assert_eq!(out.status.code(), Some(4), "{:?}", out);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("proposal_hash does not verify"), "{stderr}");
    assert!(
        stderr.contains("re-run `trailtracker rewrite propose`"),
        "{stderr}"
    );
    // And the file is untouched.
    assert_eq!(std::fs::read_to_string(&file).unwrap(), REWRITE_SRC);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn rewrite_apply_refuses_stale_file() {
    let (dir, file) = rewrite_fixture("stale", REWRITE_SRC);
    let proposal = dir.join("p.json");
    let out = bin()
        .args([
            "rewrite",
            "propose",
            "loop-to-iterator",
            "fixture.rs",
            dir.to_str().unwrap(),
            "-o",
            proposal.to_str().unwrap(),
        ])
        .output()
        .expect("run propose -o");
    assert_eq!(out.status.code(), Some(0));

    // The file drifts after the proposal was reviewed.
    std::fs::write(&file, REWRITE_SRC.replace("legacy", "modern")).unwrap();

    let out = bin()
        .args(["rewrite", "apply", "--proposal", proposal.to_str().unwrap()])
        .output()
        .expect("run apply");
    assert_eq!(out.status.code(), Some(4), "{:?}", out);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("changed since the proposal was made"),
        "{stderr}"
    );
    assert!(
        stderr.contains("re-run `trailtracker rewrite propose"),
        "{stderr}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn rewrite_apply_requires_a_proposal_and_propose_has_no_apply_flag() {
    // apply without --proposal: exit 2, and the error names the contract.
    let out = bin()
        .args(["rewrite", "apply"])
        .output()
        .expect("run apply");
    assert_eq!(out.status.code(), Some(2));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("--proposal"), "{stderr}");

    // propose --apply: rejected as an unknown flag (no path skips the
    // two-step; ADR-0006).
    let (dir, file) = rewrite_fixture("no-shortcut", REWRITE_SRC);
    let out = bin()
        .args([
            "rewrite",
            "propose",
            "loop-to-iterator",
            "fixture.rs",
            dir.to_str().unwrap(),
            "--apply",
        ])
        .output()
        .expect("run propose --apply");
    assert_eq!(out.status.code(), Some(2), "{:?}", out);
    assert_eq!(std::fs::read_to_string(&file).unwrap(), REWRITE_SRC);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn rewrite_propose_reports_rejections_without_failing() {
    // A near-miss (accumulator read in body): exit 0, no edits, the rejection
    // reason on stderr, machine-readable document via --json.
    let src = "fn f(xs: Vec<i32>) {\n    let mut out = Vec::new();\n    for x in xs {\n        out.push(out.len());\n    }\n}\n";
    let (dir, _file) = rewrite_fixture("rejections", src);
    let out = bin()
        .args([
            "rewrite",
            "propose",
            "loop-to-iterator",
            "fixture.rs",
            dir.to_str().unwrap(),
            "--json",
        ])
        .output()
        .expect("run propose");
    assert_eq!(out.status.code(), Some(0), "an empty result is an answer");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stdout.contains("\"edits\":[]"), "{stdout}");
    assert!(
        stdout.contains("\"reason\":\"acc_read_in_body\""),
        "{stdout}"
    );
    assert!(stderr.contains("acc_read_in_body"), "{stderr}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn rewrite_extract_function_full_flow() {
    let src = "fn f(x: i32) {\n    let y = x + 1;\n    let z = y * 2;\n    log(y);\n    log(z);\n}\n\nfn log(_: i32) {}\n";
    let (dir, file) = rewrite_fixture("extract", src);
    let proposal = dir.join("p.json");
    let out = bin()
        .args([
            "rewrite",
            "propose",
            "extract-function",
            "fixture.rs",
            dir.to_str().unwrap(),
            "--lines",
            "2-3",
            "--name",
            "compute",
            "-o",
            proposal.to_str().unwrap(),
        ])
        .output()
        .expect("run propose");
    assert_eq!(out.status.code(), Some(0), "{:?}", out);
    let out = bin()
        .args(["rewrite", "apply", "--proposal", proposal.to_str().unwrap()])
        .output()
        .expect("run apply");
    assert_eq!(out.status.code(), Some(0), "{:?}", out);
    let after = std::fs::read_to_string(&file).unwrap();
    assert_eq!(
        after,
        "fn f(x: i32) {\n    let compute = || {\n        let y = x + 1;\n        let z = y * 2;\n        (y, z)\n    };\n    let (y, z) = compute();\n    log(y);\n    log(z);\n}\n\nfn log(_: i32) {}\n"
    );
    // extract-function without --lines is a usage error.
    let out = bin()
        .args([
            "rewrite",
            "propose",
            "extract-function",
            "fixture.rs",
            dir.to_str().unwrap(),
        ])
        .output()
        .expect("run propose without lines");
    assert_eq!(out.status.code(), Some(2), "{:?}", out);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn rewrite_unknown_rule_and_subcommand_get_did_you_mean() {
    let out = bin()
        .args(["rewrite", "proposr"])
        .output()
        .expect("run rewrite typo");
    assert_eq!(out.status.code(), Some(2));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("propose"), "typo hint missing: {stderr}");

    let (dir, _file) = rewrite_fixture("badrule", REWRITE_SRC);
    let out = bin()
        .args([
            "rewrite",
            "propose",
            "loop-to-iter",
            "fixture.rs",
            dir.to_str().unwrap(),
        ])
        .output()
        .expect("run bad rule");
    assert_eq!(out.status.code(), Some(2));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("loop-to-iterator"), "{stderr}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn rewrite_rules_lists_the_vocabulary() {
    let text = stdout_of(&["rewrite", "rules"]);
    for rule in [
        "dead-branch-elim v1",
        "loop-to-iterator v1",
        "extract-function v1",
        "redundant-clone-elim v1",
        "if-let-to-match v1",
        "slice-param v1",
    ] {
        assert!(text.contains(rule), "missing {rule}:\n{text}");
    }
    let json = stdout_of(&["rewrite", "rules", "--json"]);
    assert!(
        json.contains("\"schema\":\"trailtracker.rewrite-rules/v1\""),
        "{json}"
    );
    assert!(json.contains("\"requires_lines\":true"), "{json}");
}

#[test]
fn rewrite_is_documented_in_help_and_capabilities() {
    let help = stdout_of(&["help"]);
    assert!(
        help.contains("rewrite propose"),
        "help missing rewrite:\n{help}"
    );
    assert!(help.contains("rewrite apply"), "{help}");
    assert!(help.contains("rewrite verify"), "{help}");
    let caps = stdout_of(&["capabilities"]);
    assert!(
        caps.contains("\"name\":\"rewrite\""),
        "capabilities missing rewrite"
    );
    assert!(
        caps.contains("trailtracker.rewrite-proposal/v1"),
        "capabilities must document the proposal schema"
    );
    assert!(
        caps.contains("trailtracker.rewrite-cert/v1"),
        "capabilities must document the certificate schema"
    );
    assert!(
        caps.contains("--require-cert"),
        "capabilities must document --require-cert"
    );
}

// ---------------------------------------------------------------------------
// rewrite equivalence certificates (ADR-0007): verify + require-cert
// ---------------------------------------------------------------------------

#[test]
fn rewrite_propose_writes_certificate_beside_proposal() {
    let (dir, file) = rewrite_fixture("cert-beside", REWRITE_SRC);
    let proposal = dir.join("p.json");
    let out = bin()
        .args([
            "rewrite",
            "propose",
            "loop-to-iterator",
            "fixture.rs",
            dir.to_str().unwrap(),
            "-o",
            proposal.to_str().unwrap(),
        ])
        .output()
        .expect("run propose -o");
    assert_eq!(out.status.code(), Some(0), "{:?}", out);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("certificate written to"), "{stderr}");
    let cert_path = dir.join("p.cert.json");
    let cert = std::fs::read_to_string(&cert_path).expect("cert beside proposal");
    assert!(
        cert.contains("\"schema\":\"trailtracker.rewrite-cert/v1\""),
        "{cert}"
    );
    assert!(cert.contains("\"cert_hash\":\"fnv1a64:"), "{cert}");
    assert!(cert.contains("\"assumptions\""), "{cert}");
    assert!(cert.contains("\"checks\""), "{cert}");
    // Propose still never writes source.
    assert_eq!(std::fs::read_to_string(&file).unwrap(), REWRITE_SRC);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn rewrite_verify_recomputes_and_is_deterministic() {
    let (dir, _file) = rewrite_fixture("verify-ok", REWRITE_SRC);
    let proposal = dir.join("p.json");
    let out = bin()
        .args([
            "rewrite",
            "propose",
            "loop-to-iterator",
            "fixture.rs",
            dir.to_str().unwrap(),
            "-o",
            proposal.to_str().unwrap(),
        ])
        .output()
        .expect("run propose -o");
    assert_eq!(out.status.code(), Some(0));

    let run = || {
        let out = bin()
            .args([
                "rewrite",
                "verify",
                "--proposal",
                proposal.to_str().unwrap(),
                "--json",
            ])
            .output()
            .expect("run verify --json");
        assert_eq!(out.status.code(), Some(0), "{:?}", out);
        String::from_utf8(out.stdout).unwrap()
    };
    let a = run();
    let b = run();
    assert_eq!(a, b, "certificate must be byte-deterministic");
    assert!(
        a.contains("\"schema\":\"trailtracker.rewrite-cert/v1\""),
        "{a}"
    );
    assert!(a.contains("\"schema_obligation\""), "{a}");
    assert!(a.contains("k3c_loop_fold_schema"), "{a}");
    // The recomputed certificate byte-matches the one propose wrote.
    let beside = std::fs::read_to_string(dir.join("p.cert.json")).unwrap();
    assert_eq!(
        a.trim(),
        beside.trim(),
        "verify must reproduce propose's certificate"
    );

    // Human mode names the verdict.
    let human = bin()
        .args([
            "rewrite",
            "verify",
            "--proposal",
            proposal.to_str().unwrap(),
        ])
        .output()
        .expect("run verify");
    assert_eq!(human.status.code(), Some(0));
    let text = String::from_utf8_lossy(&human.stdout);
    assert!(text.contains("VERIFIED loop-to-iterator v1"), "{text}");
    assert!(text.contains("unaffected re-verified"), "{text}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn rewrite_verify_refuses_stale_file_with_exit_4() {
    let (dir, file) = rewrite_fixture("verify-stale", REWRITE_SRC);
    let proposal = dir.join("p.json");
    let out = bin()
        .args([
            "rewrite",
            "propose",
            "loop-to-iterator",
            "fixture.rs",
            dir.to_str().unwrap(),
            "-o",
            proposal.to_str().unwrap(),
        ])
        .output()
        .expect("run propose -o");
    assert_eq!(out.status.code(), Some(0));
    // Drift the file under the proposal.
    std::fs::write(&file, REWRITE_SRC.replace("x * 2", "x * 3")).unwrap();
    let out = bin()
        .args([
            "rewrite",
            "verify",
            "--proposal",
            proposal.to_str().unwrap(),
        ])
        .output()
        .expect("run verify");
    assert_eq!(out.status.code(), Some(4), "{:?}", out);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("file_fingerprint_mismatch"), "{stderr}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn rewrite_apply_require_cert_verifies_then_writes() {
    let (dir, file) = rewrite_fixture("require-cert", REWRITE_SRC);
    let proposal = dir.join("p.json");
    let out = bin()
        .args([
            "rewrite",
            "propose",
            "loop-to-iterator",
            "fixture.rs",
            dir.to_str().unwrap(),
            "-o",
            proposal.to_str().unwrap(),
        ])
        .output()
        .expect("run propose -o");
    assert_eq!(out.status.code(), Some(0));
    let out = bin()
        .args([
            "rewrite",
            "apply",
            "--proposal",
            proposal.to_str().unwrap(),
            "--require-cert",
            "--json",
        ])
        .output()
        .expect("run apply --require-cert");
    assert_eq!(out.status.code(), Some(0), "{:?}", out);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("\"cert_hash\":\"fnv1a64:"), "{stdout}");
    assert!(
        std::fs::read_to_string(&file)
            .unwrap()
            .contains(".map(|x| x * 2)"),
        "apply must have written the certified rewrite"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

// The redundant-clone-elim source: a proven last use (`payload` is cloned
// into `owned` and never read again).
const CLONE_SRC: &str = "fn handle(payload: String) {\n    let payload = payload;\n    let owned = payload.clone();\n    store(owned);\n}\n\nfn store(_: String) {}\n";

#[test]
fn rewrite_clone_elim_propose_verify_apply_end_to_end() {
    let (dir, file) = rewrite_fixture("clone-e2e", CLONE_SRC);
    let proposal = dir.join("p.json");

    // 1. propose: emits the diff + a hash-bound proposal + the certificate.
    let out = bin()
        .args([
            "rewrite",
            "propose",
            "redundant-clone-elim",
            "fixture.rs",
            dir.to_str().unwrap(),
            "-o",
            proposal.to_str().unwrap(),
        ])
        .output()
        .expect("run propose");
    assert_eq!(out.status.code(), Some(0), "{:?}", out);
    let diff = String::from_utf8_lossy(&out.stdout);
    assert!(diff.contains("-    let owned = payload.clone();"), "{diff}");
    assert!(diff.contains("+    let owned = payload;"), "{diff}");
    // propose never writes source.
    assert_eq!(std::fs::read_to_string(&file).unwrap(), CLONE_SRC);
    // certificate written beside the proposal, naming the last-use proof.
    let cert = std::fs::read_to_string(dir.join("p.cert.json")).expect("cert beside");
    assert!(
        cert.contains("\"schema\":\"trailtracker.rewrite-cert/v1\""),
        "{cert}"
    );
    assert!(cert.contains("k3c_clone_elim_schema"), "{cert}");

    // 2. verify: the independent checker recomputes and passes.
    let out = bin()
        .args([
            "rewrite",
            "verify",
            "--proposal",
            proposal.to_str().unwrap(),
        ])
        .output()
        .expect("run verify");
    assert_eq!(out.status.code(), Some(0), "{:?}", out);
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(text.contains("VERIFIED redundant-clone-elim v1"), "{text}");

    // 3. apply: the only writing path, certified by default.
    let out = bin()
        .args(["rewrite", "apply", "--proposal", proposal.to_str().unwrap()])
        .output()
        .expect("run apply");
    assert_eq!(out.status.code(), Some(0), "{:?}", out);
    let written = std::fs::read_to_string(&file).unwrap();
    assert!(written.contains("let owned = payload;"), "{written}");
    assert!(!written.contains(".clone()"), "{written}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn rewrite_clone_elim_refuses_when_value_used_later() {
    // THE bite: a clone whose binding IS read after the call. propose refuses
    // the site (it is not the last use), so no proposal is produced and the
    // decoy source is never rewritten.
    let bad = "fn handle(p: String) {\n    let p = p;\n    let owned = p.clone();\n    store(owned);\n    log(&p);\n}\n\nfn store(_: String) {}\nfn log(_: &String) {}\n";
    let (dir, _file) = rewrite_fixture("clone-bite", bad);
    let out = bin()
        .args([
            "rewrite",
            "propose",
            "redundant-clone-elim",
            "fixture.rs",
            dir.to_str().unwrap(),
            "--json",
        ])
        .output()
        .expect("run propose");
    assert_eq!(out.status.code(), Some(0), "{:?}", out);
    let doc = String::from_utf8_lossy(&out.stdout);
    // No edit; the site is reported as a rejection with the exact reason.
    assert!(doc.contains("\"edits\":[]"), "expected no edits:\n{doc}");
    assert!(
        doc.contains("\"reason\":\"cloned_value_read_later\""),
        "{doc}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

// The slice-param source: every use of `items` is slice-safe, so the
// borrowed `Vec` parameter generalizes to a slice.
const SLICE_PARAM_SRC: &str = "fn total(items: &Vec<i32>) -> usize {\n    items.len()\n}\n\nfn caller(xs: Vec<i32>) -> usize {\n    total(&xs)\n}\n";

#[test]
fn rewrite_slice_param_propose_verify_apply_end_to_end() {
    let (dir, file) = rewrite_fixture("slice-param-e2e", SLICE_PARAM_SRC);
    let proposal = dir.join("p.json");

    // 1. propose: emits the diff + a hash-bound proposal + the certificate
    //    (the edit lives in the SIGNATURE — the one rule that rewrites a
    //    span outside every statement).
    let out = bin()
        .args([
            "rewrite",
            "propose",
            "slice-param",
            "fixture.rs",
            dir.to_str().unwrap(),
            "-o",
            proposal.to_str().unwrap(),
        ])
        .output()
        .expect("run propose");
    assert_eq!(out.status.code(), Some(0), "{:?}", out);
    let diff = String::from_utf8_lossy(&out.stdout);
    assert!(
        diff.contains("-fn total(items: &Vec<i32>) -> usize {"),
        "{diff}"
    );
    assert!(
        diff.contains("+fn total(items: &[i32]) -> usize {"),
        "{diff}"
    );
    // propose never writes source.
    assert_eq!(std::fs::read_to_string(&file).unwrap(), SLICE_PARAM_SRC);
    let cert = std::fs::read_to_string(dir.join("p.cert.json")).expect("cert beside");
    assert!(
        cert.contains("\"schema\":\"trailtracker.rewrite-cert/v1\""),
        "{cert}"
    );
    assert!(cert.contains("slice-param"), "{cert}");

    // 2. verify: the independent checker recomputes and passes.
    let out = bin()
        .args([
            "rewrite",
            "verify",
            "--proposal",
            proposal.to_str().unwrap(),
        ])
        .output()
        .expect("run verify");
    assert_eq!(out.status.code(), Some(0), "{:?}", out);
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(text.contains("VERIFIED slice-param v1"), "{text}");

    // 3. apply: the only writing path, certified by default.
    let out = bin()
        .args(["rewrite", "apply", "--proposal", proposal.to_str().unwrap()])
        .output()
        .expect("run apply");
    assert_eq!(out.status.code(), Some(0), "{:?}", out);
    let written = std::fs::read_to_string(&file).unwrap();
    assert!(
        written.contains("fn total(items: &[i32]) -> usize {"),
        "{written}"
    );
    assert!(!written.contains("&Vec<i32>"), "{written}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn rewrite_slice_param_refuses_vec_specific_method() {
    // THE bite: the body calls a Vec-specific method. propose refuses the
    // site with the exact machine-readable reason and writes nothing.
    let bad = "fn f(v: &Vec<i32>) -> usize {\n    v.capacity()\n}\n";
    let (dir, _file) = rewrite_fixture("slice-param-bite", bad);
    let out = bin()
        .args([
            "rewrite",
            "propose",
            "slice-param",
            "fixture.rs",
            dir.to_str().unwrap(),
            "--json",
        ])
        .output()
        .expect("run propose");
    assert_eq!(out.status.code(), Some(0), "{:?}", out);
    let doc = String::from_utf8_lossy(&out.stdout);
    assert!(doc.contains("\"edits\":[]"), "expected no edits:\n{doc}");
    assert!(
        doc.contains("\"reason\":\"param_method_not_slice_compatible\""),
        "{doc}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn rewrite_apply_certifies_by_default_and_rejects_no_cert() {
    // ADR-0007's end state (K3d): apply runs the full equivalence
    // verification WITHOUT --require-cert, and there is no opt-out flag.
    let (dir, file) = rewrite_fixture("cert-default", REWRITE_SRC);
    let proposal = dir.join("p.json");
    let out = bin()
        .args([
            "rewrite",
            "propose",
            "loop-to-iterator",
            "fixture.rs",
            dir.to_str().unwrap(),
            "-o",
            proposal.to_str().unwrap(),
        ])
        .output()
        .expect("run propose -o");
    assert_eq!(out.status.code(), Some(0));

    // A --no-cert escape hatch must not exist.
    let out = bin()
        .args([
            "rewrite",
            "apply",
            "--proposal",
            proposal.to_str().unwrap(),
            "--no-cert",
        ])
        .output()
        .expect("run apply --no-cert");
    assert_eq!(out.status.code(), Some(2), "{:?}", out);
    assert_eq!(
        std::fs::read_to_string(&file).unwrap(),
        REWRITE_SRC,
        "rejected flag must not write"
    );

    // Plain apply certifies: cert_hash is present with no flag at all.
    let out = bin()
        .args([
            "rewrite",
            "apply",
            "--proposal",
            proposal.to_str().unwrap(),
            "--json",
        ])
        .output()
        .expect("run apply");
    assert_eq!(out.status.code(), Some(0), "{:?}", out);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("\"cert_hash\":\"fnv1a64:"), "{stdout}");
    assert!(
        std::fs::read_to_string(&file)
            .unwrap()
            .contains(".map(|x| x * 2)"),
        "apply must have written the certified rewrite"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// deadcode: rooted liveness, evidence, and CLI error contracts
// ---------------------------------------------------------------------------

fn deadcode_fixture(name: &str, source: &str) -> std::path::PathBuf {
    let dir = std::env::temp_dir().join(format!("tt-deadcode-cli-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("app.py"), source).unwrap();
    dir
}

#[test]
fn deadcode_clean_exit_and_json_schema_are_deterministic() {
    let clean = deadcode_fixture("clean", "def main():\n    return 0\n");
    let clean_out = bin()
        .args(["deadcode", clean.to_str().unwrap()])
        .output()
        .expect("run deadcode clean");
    assert_eq!(
        clean_out.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&clean_out.stderr)
    );

    let dirty = deadcode_fixture(
        "json",
        "def main():\n    return 0\n\ndef unused():\n    return 1\n",
    );
    let args = ["deadcode", dirty.to_str().unwrap(), "--json"];
    let first = bin().args(args).output().expect("run deadcode json");
    assert_eq!(first.status.code(), Some(1));
    let text = String::from_utf8(first.stdout).expect("utf8 json");
    assert!(
        text.starts_with("{\"schema\":\"trailtracker.deadcode/v1\",\"command\":\"deadcode\""),
        "schema must be first: {text}"
    );
    let doc = mini_json::parse(text.trim_end()).expect("valid deadcode json");
    assert_eq!(
        doc.get("schema").and_then(|value| value.as_str()),
        Some("trailtracker.deadcode/v1")
    );
    assert!(doc.get("summary").is_some());
    assert!(doc
        .get("findings")
        .and_then(|value| value.as_arr())
        .is_some());
    assert!(doc.get("roots").and_then(|value| value.as_arr()).is_some());
    let second = bin().args(args).output().expect("rerun deadcode json");
    assert_eq!(first.status.code(), second.status.code());
    assert_eq!(text.as_bytes(), second.stdout.as_slice());

    let _ = std::fs::remove_dir_all(clean);
    let _ = std::fs::remove_dir_all(dirty);
}

#[test]
fn deadcode_no_ignore_scans_mentions_in_gitignored_analyzed_files() {
    let dir = deadcode_fixture(
        "no-ignore-mentions",
        "def main():\n    return 0\n\ndef _hook():\n    return 1\n",
    );
    std::fs::create_dir(dir.join(".git")).expect("create git marker");
    std::fs::write(dir.join(".gitignore"), "gen/\n").expect("write gitignore");
    std::fs::create_dir(dir.join("gen")).expect("create ignored directory");
    std::fs::write(dir.join("gen/notes.py"), "NOTE = \"_hook\"\n").expect("write ignored mention");

    let out = bin()
        .args(["deadcode", dir.to_str().unwrap(), "--no-ignore", "--json"])
        .output()
        .expect("run deadcode without ignore filtering");
    assert_eq!(
        out.status.code(),
        Some(1),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let text = String::from_utf8(out.stdout).expect("utf8 deadcode json");
    let doc = mini_json::parse(text.trim_end()).expect("valid deadcode json");
    let hook = doc
        .get("findings")
        .and_then(|value| value.as_arr())
        .and_then(|findings| {
            findings
                .iter()
                .find(|finding| finding.get("name").and_then(|name| name.as_str()) == Some("_hook"))
        })
        .expect("_hook finding");
    assert_eq!(
        hook.get("tier").and_then(|tier| tier.as_str()),
        Some("dead-medium")
    );
    assert!(hook
        .get("evidence")
        .and_then(|evidence| evidence.get("mention_files"))
        .and_then(|files| files.as_arr())
        .is_some_and(|files| {
            files
                .iter()
                .any(|file| file.as_str() == Some("gen/notes.py"))
        }));

    let _ = std::fs::remove_dir_all(dir);
}

#[test]
fn deadcode_calc_corpus_contract_is_pinned_and_deterministic() {
    let args = ["deadcode", CORPUS, "--json"];
    let first = bin().args(args).output().expect("run deadcode on calc");
    assert_eq!(
        first.status.code(),
        Some(1),
        "{}",
        String::from_utf8_lossy(&first.stderr)
    );
    let second = bin().args(args).output().expect("rerun deadcode on calc");
    assert_eq!(second.status.code(), Some(1));
    assert_eq!(first.stdout, second.stdout);

    let text = String::from_utf8(first.stdout).expect("utf8 deadcode json");
    let doc = mini_json::parse(text.trim_end()).expect("valid deadcode json");
    let summary = doc.get("summary").expect("summary");
    assert_eq!(
        summary.get("symbols"),
        Some(&mini_json::V::Num(19.0)),
        "calc symbol count changed"
    );
    assert_eq!(
        summary.get("roots"),
        Some(&mini_json::V::Num(0.0)),
        "calc root count changed"
    );
    let dead = summary.get("dead").expect("dead summary");
    assert_eq!(dead.get("high"), Some(&mini_json::V::Num(1.0)));
    assert_eq!(dead.get("medium"), Some(&mini_json::V::Num(5.0)));
    assert_eq!(dead.get("transitive"), Some(&mini_json::V::Num(13.0)));
    assert_eq!(
        doc.get("findings")
            .and_then(|value| value.as_arr())
            .map(<[_]>::len),
        Some(19)
    );
    assert_eq!(
        doc.get("roots")
            .and_then(|value| value.as_arr())
            .map(<[_]>::len),
        Some(0)
    );
}

#[test]
fn deadcode_pyapp_corpus_contract_pins_tiers_and_schema_line() {
    let args = ["deadcode", "eval/corpus/pyapp", "--json"];
    let out = bin().args(args).output().expect("run deadcode on pyapp");
    assert_eq!(
        out.status.code(),
        Some(1),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );

    let text = String::from_utf8(out.stdout).expect("utf8 deadcode json");
    assert_eq!(text.lines().count(), 1, "--json must emit one schema line");
    assert!(
        text.starts_with("{\"schema\":\"trailtracker.deadcode/v1\",\"command\":\"deadcode\""),
        "schema must be first: {text}"
    );
    let doc = mini_json::parse(text.trim_end()).expect("valid deadcode json");
    let summary = doc.get("summary").expect("summary");
    assert_eq!(summary.get("symbols"), Some(&mini_json::V::Num(16.0)));
    assert_eq!(summary.get("roots"), Some(&mini_json::V::Num(10.0)));
    assert_eq!(
        summary.get("mention_scanned"),
        Some(&mini_json::V::Num(12.0))
    );
    let dead = summary.get("dead").expect("dead summary");
    assert_eq!(dead.get("high"), Some(&mini_json::V::Num(2.0)));
    assert_eq!(dead.get("medium"), Some(&mini_json::V::Num(3.0)));
    assert_eq!(dead.get("transitive"), Some(&mini_json::V::Num(2.0)));
    let findings = doc
        .get("findings")
        .and_then(|value| value.as_arr())
        .expect("findings");
    assert_eq!(findings.len(), 7);
    for live_name in [
        "INTEGRATION_PARSERS",
        "_FORECAST_ENGINE",
        "pytest_configure",
    ] {
        assert!(
            findings.iter().all(
                |finding| finding.get("name").and_then(|name| name.as_str()) != Some(live_name)
            ),
            "{live_name} must be live in the wave-2 corpus"
        );
    }
    let documented = findings
        .iter()
        .find(|finding| finding.get("name").and_then(|name| name.as_str()) == Some("_dead_leaf"))
        .expect("README-mentioned dead symbol");
    assert_eq!(
        documented.get("tier").and_then(|tier| tier.as_str()),
        Some("dead-medium")
    );
    assert!(documented
        .get("evidence")
        .and_then(|evidence| evidence.get("mention_files"))
        .and_then(|files| files.as_arr())
        .is_some_and(|files| files.iter().any(|file| file.as_str() == Some("README.md"))));
}

#[test]
fn deadcode_why_and_unknown_flag_follow_global_errors() {
    let dir = deadcode_fixture(
        "why",
        "def main():\n    helper()\n\ndef helper():\n    return 1\n",
    );
    let live = bin()
        .args(["deadcode", dir.to_str().unwrap(), "--why", "helper"])
        .output()
        .expect("run deadcode why");
    assert_eq!(
        live.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&live.stderr)
    );
    assert!(
        String::from_utf8_lossy(&live.stdout).contains("main-function"),
        "why-live output must name the root reason"
    );

    let unknown = bin()
        .args(["deadcode", dir.to_str().unwrap(), "--why", "NoSuchTarget"])
        .output()
        .expect("run deadcode unknown target");
    assert_eq!(unknown.status.code(), Some(3));
    assert!(String::from_utf8_lossy(&unknown.stderr).contains("NoSuchTarget"));

    let bad_flag = bin()
        .args(["deadcode", dir.to_str().unwrap(), "--limti", "3"])
        .output()
        .expect("run deadcode bad flag");
    assert_eq!(bad_flag.status.code(), Some(2));
    let stderr = String::from_utf8_lossy(&bad_flag.stderr);
    assert!(stderr.contains("unknown flag '--limti'"), "{stderr}");
    assert!(stderr.contains("--limit"), "{stderr}");
    let _ = std::fs::remove_dir_all(dir);
}
