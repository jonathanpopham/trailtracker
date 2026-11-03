//! TrailTracker CLI. Std-only, no argument-parsing crates.
//!
//! Commands:
//!   trailtracker graph [DIR]   Analyze a directory and emit the canonical
//!                              graph as JSONL on stdout (DIR defaults to `.`).
//!   trailtracker stats [DIR]   Print honest coverage statistics for a directory
//!                              (`--json` for a machine-readable object).
//!   trailtracker parse FILE    Emit the lossless CST of one Rust file as JSON.
//!   trailtracker extract NAME [DIR]
//!                              Analyze DIR, apply the named extractor, and emit
//!                              the derived view graph as JSONL.
//!   trailtracker enrich-domains [DIR] [--json]
//!                              `enrich` FEATURE BUILDS ONLY (internal
//!                              tooling, never shipped): the optional LLM
//!                              naming pass over the deterministic domain
//!                              clusters. The default/airgap build contains
//!                              no trace of it — the command is unknown and
//!                              the binary holds zero model-invoking code.
//!   trailtracker export ontoloom [DIR] [--view NAME]
//!                              Analyze DIR, apply the chosen view (default
//!                              `hierarchy`; `graph` = the base graph), and emit
//!                              it as Ontoloom wire JSON.
//!   trailtracker dossier <DIR> [-o out.html]
//!                              The client-ready deliverable: one
//!                              self-contained, airgap-grade HTML report
//!                              (brief + interactive code map + layer
//!                              violations). `--enrich enrich.json` exists
//!                              only in `enrich` feature builds.
//!   trailtracker query KIND [TARGET] [DIR] [--json]
//!                              Ask the graph a question.
//!   trailtracker explain TARGET [DIR] [--json]
//!                              One card that explains a file or symbol:
//!                              identity, domain/layer/archetype, fan-in/out,
//!                              blast radius, and nearest neighbors.
//!   trailtracker search "<query>" [DIR] [--limit N]
//!                              Hybrid code search over the graph: BM25 +
//!                              hash embeddings fused by reciprocal rank,
//!                              re-ranked by graph proximity (`--json` for a
//!                              machine-readable result list).
//!   trailtracker report [DIR]  Markdown org summary (`--json` for an envelope).
//!   trailtracker report --full <DIR> [-o PATH] [--format md|html|both]
//!                              [--examples N] [--budget N]
//!                              The full evidence report: exec summary
//!                              (verbalizer prose), domains, change-risk
//!                              centers with named callers, every layer-
//!                              violating edge at symbol grain (inheritance
//!                              included), structural findings, domains-only
//!                              coupling appendix (MD + self-contained HTML).
//!   trailtracker brief [DIR]   Markdown codebase model (`--json` for a
//!                              structured brief object).
//!   trailtracker rebuild-brief NAME [DIR]
//!                              Markdown rebuild brief for one workflow.
//!   trailtracker arch-verify [DIR] [--spec PATH]
//!                              Verify the ACTUAL code against the INTENDED
//!                              architecture declared in
//!                              `.trailtracker-arch.json` (ADR-0005). Exit 0
//!                              spec holds, 1 error-severity findings (the CI
//!                              gate).
//!   trailtracker arch-init [DIR] [-o PATH]
//!                              Bootstrap an architecture spec from the
//!                              currently recovered domains + dependencies.
//!   trailtracker deadcode [DIR] [--json] [--min-confidence high|medium|low]
//!                              [--limit N] [--why TARGET] [--no-test-roots]
//!                              [--config PATH]
//!                              Rooted liveness analysis with auditable roots,
//!                              tiered dead findings, and per-symbol evidence.
//!                              Exit 0 clean, 1 findings present.
//!   trailtracker violations <DIR> [--examples N] [--json]
//!                              Spec-free full layer-violations report: every
//!                              direction-violating dependency or inheritance
//!                              edge at unit grain (from-unit → to-unit,
//!                              layers, complete edge counts, symbol-grain
//!                              evidence; --examples caps the evidence list),
//!                              ranked worst-first.
//!                              Exit 0 clean, 1 violations present.
//!   trailtracker verbalize <DIR> [--view NAME] [--target ID] [--budget N]
//!                              The graph as retrieval-safe sentences
//!                              (ADR-0008): glossary prelude + one fact per
//!                              sentence, deterministic, budget-honest.
//!   trailtracker doctor [DIR]  Self-diagnose the tool + environment against
//!                              DIR (default `.`): version/build, analysis,
//!                              parse failures, losslessness, extractors,
//!                              determinism. Read-only; exit 0 healthy,
//!                              1 findings. Sub-verbs: `doctor capabilities`,
//!                              `doctor robot-docs`.
//!   trailtracker capabilities  Machine-readable CLI contract (JSON).
//!   trailtracker version       Print the version.
//!   trailtracker help [--json] This overview (`--json` = `capabilities`).
//!
//! Agent contract (stable):
//!   - stdout is data only; stderr is diagnostics only.
//!   - Output is byte-deterministic: same input tree, same bytes.
//!   - Errors are `trailtracker: <what went wrong>` plus an optional
//!     `  fix: <how to fix it>` line, both on stderr.
//!   - Exit codes: 0 success, 2 usage error, 3 path not found/unreadable,
//!     4 analysis failure; `doctor`, `arch-verify`, `violations`, and
//!     `deadcode` add 1 = findings present. Documented in `capabilities`.

// Memory-safe by construction; see src/lib.rs and `[lints.rust]` in Cargo.toml.
#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::io::{self, Write};
use std::path::Path;
use std::process::ExitCode;

use trailtracker::arch;
use trailtracker::core::json::Json;
use trailtracker::doctor::{doctor_capabilities_json, robot_docs, run_doctor, DoctorOptions};
use trailtracker::extract::{extractor_by_name, extractors};
use trailtracker::lang::rust::parser::parse;
use trailtracker::pipeline::{analyze_dir_opts, analyze_dir_with, Analysis, AnalyzeOptions};

/// Exit code for usage errors: bad command, flag, or argument value.
const EXIT_USAGE: u8 = 2;
/// Exit code when an input path does not exist or cannot be read.
const EXIT_NOT_FOUND: u8 = 3;
/// Exit code for analysis failures (internal errors while processing input).
const EXIT_ANALYSIS: u8 = 4;

/// Every dispatchable command name, for `help --json` and typo suggestions.
const COMMAND_NAMES: &[&str] = &[
    "arch-init",
    "arch-verify",
    "graph",
    "cpg",
    "stats",
    "parse",
    "extract",
    #[cfg(feature = "enrich")]
    "enrich-domains",
    "explain",
    "export",
    "dossier",
    "violations",
    "deadcode",
    "verbalize",
    "query",
    "search",
    "nav",
    "report",
    "brief",
    "rebuild-brief",
    "rewrite",
    "doctor",
    "capabilities",
    "version",
    "help",
];

const QUERY_KINDS: &[&str] = &["what-touches", "blast-radius", "uses", "deepest-flows"];

/// A CLI failure: what went wrong, how to fix it, and which exit-code
/// category it belongs to. Rendered on stderr as:
///
/// ```text
/// trailtracker: <message>
///   fix: <fix>
/// ```
struct CliError {
    exit: u8,
    message: String,
    fix: Option<String>,
}

impl CliError {
    fn usage(message: impl Into<String>) -> CliError {
        CliError {
            exit: EXIT_USAGE,
            message: message.into(),
            fix: None,
        }
    }

    fn not_found(message: impl Into<String>) -> CliError {
        CliError {
            exit: EXIT_NOT_FOUND,
            message: message.into(),
            fix: None,
        }
    }

    fn analysis(message: impl Into<String>) -> CliError {
        CliError {
            exit: EXIT_ANALYSIS,
            message: message.into(),
            fix: None,
        }
    }

    fn fix(mut self, fix: impl Into<String>) -> CliError {
        self.fix = Some(fix.into());
        self
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = env::args().skip(1).collect();
    match run(&args) {
        // Data-carrying non-zero exits (doctor findings) have already written
        // their report to stdout; no stderr noise.
        Ok(code) => ExitCode::from(code),
        Err(err) => {
            // Diagnostics tolerate a closed stream too: a dead stderr must
            // never turn a clean error exit into a panic (`eprintln!` would).
            let stderr = io::stderr();
            let mut handle = stderr.lock();
            let _ = writeln!(handle, "trailtracker: {}", err.message);
            if let Some(fix) = &err.fix {
                let _ = writeln!(handle, "  fix: {fix}");
            }
            ExitCode::from(err.exit)
        }
    }
}

/// Successful (`Ok`) command completion with exit code 0. Commands whose
/// success carries a status (doctor) return their code directly.
fn done(result: Result<(), CliError>) -> Result<u8, CliError> {
    result.map(|()| 0)
}

fn run(args: &[String]) -> Result<u8, CliError> {
    let command = args.first().map(String::as_str).unwrap_or("help");
    let rest = args.get(1..).unwrap_or(&[]);
    match command {
        "graph" => done(cmd_graph(rest)),
        "cpg" => done(cmd_cpg(rest)),
        "stats" => done(cmd_stats(rest)),
        "parse" => done(cmd_parse(rest)),
        "extract" => done(cmd_extract(rest)),
        #[cfg(feature = "enrich")]
        "enrich-domains" => done(cmd_enrich_domains(rest)),
        "explain" => done(cmd_explain(rest)),
        "export" => done(cmd_export(rest)),
        "dossier" => done(cmd_dossier(rest)),
        "violations" => cmd_violations(rest),
        "deadcode" => cmd_deadcode(rest),
        "verbalize" => done(cmd_verbalize(rest)),
        "arch-verify" => cmd_arch_verify(rest),
        "arch-init" => done(cmd_arch_init(rest)),
        "query" => done(cmd_query(rest)),
        "search" => done(cmd_search(rest)),
        "nav" => done(cmd_nav(rest)),
        "report" => done(cmd_report(rest)),
        "brief" => done(cmd_brief(rest)),
        "rebuild-brief" => done(cmd_rebuild_brief(rest)),
        "rewrite" => done(cmd_rewrite(rest)),
        "doctor" => cmd_doctor(rest),
        "capabilities" => {
            println_stdout(&capabilities_json().to_line(), "capabilities")?;
            Ok(0)
        }
        "version" | "--version" | "-V" => {
            println_stdout(
                &format!("trailtracker {}", env!("CARGO_PKG_VERSION")),
                "version",
            )?;
            Ok(0)
        }
        "help" | "-h" | "--help" => {
            let parsed = split_args("help", rest)?;
            if parsed.json {
                println_stdout(&capabilities_json().to_line(), "capabilities")?;
            } else {
                write_stdout(help_text().as_bytes(), "help")?;
            }
            Ok(0)
        }
        other => Err(unknown_value_error("command", other, COMMAND_NAMES).fix(
            match closest(other, COMMAND_NAMES) {
                Some(c) => format!(
                    "did you mean `trailtracker {c}`? Run `trailtracker help` for all commands."
                ),
                None => "run `trailtracker help` for the command list, or `trailtracker \
                         capabilities` for the machine-readable contract."
                    .to_string(),
            },
        )),
    }
}

// ---------------------------------------------------------------------------
// Argument handling: flags, typo suggestions, error construction
// ---------------------------------------------------------------------------

/// The parsed arguments of one subcommand invocation.
struct CmdArgs<'a> {
    /// Positional (non-flag) arguments, in order.
    pos: Vec<&'a str>,
    /// `--json` (or its synonym `--robot`) was passed.
    json: bool,
    /// `--incremental` was passed: cache per-language-batch lowered subgraphs
    /// under `<DIR>/.trailtracker-cache` (or `TRAILTRACKER_CACHE_DIR`) and
    /// reuse them for unchanged files. Output is byte-identical to an
    /// uncached run. Also enabled by the `TRAILTRACKER_CACHE` env var.
    incremental: bool,
    /// `--no-ignore` was passed: analyze everything on disk. By default, when
    /// DIR is a git checkout, files matched by its `.gitignore` are excluded
    /// from analysis (untracked build outputs are not source; bead ei8).
    no_ignore: bool,
}

/// Split `rest` into positionals and known flags. Every command accepts
/// `--json`/`--robot` (a no-op on commands whose output is already JSON),
/// `--incremental` and `--no-ignore` (no-ops on commands that do not analyze
/// a directory), and `--help`/`-h`. Unknown flags are a usage error with a
/// did-you-mean hint — never silently ignored.
fn split_args<'a>(cmd: &str, rest: &'a [String]) -> Result<CmdArgs<'a>, CliError> {
    let mut parsed = CmdArgs {
        pos: Vec::new(),
        json: false,
        incremental: false,
        no_ignore: false,
    };
    for arg in rest {
        match arg.as_str() {
            "--json" | "--robot" => parsed.json = true,
            "--incremental" => parsed.incremental = true,
            "--no-ignore" => parsed.no_ignore = true,
            "--help" | "-h" => {
                // Per-command help: redirect to the global overview.
                return Err(CliError::usage(format!(
                    "`trailtracker {cmd}` does not take a --help flag"
                ))
                .fix(
                    "run `trailtracker help` for usage of every command, or `trailtracker \
                     capabilities` for the machine-readable contract.",
                ));
            }
            flag if flag.starts_with('-') => {
                let known = ["--json", "--robot", "--incremental", "--no-ignore"];
                let fix = match closest(flag, &known) {
                    Some(k) => format!("did you mean `{k}`? Run `trailtracker help` for usage."),
                    None => format!(
                        "`trailtracker {cmd}` accepts --json/--robot/--incremental/--no-ignore; \
                         run `trailtracker help` for usage."
                    ),
                };
                return Err(CliError::usage(format!("unknown flag '{flag}' for `{cmd}`")).fix(fix));
            }
            pos => parsed.pos.push(pos),
        }
    }
    Ok(parsed)
}

/// Reject extra positionals so a mistyped invocation never silently degrades.
fn expect_at_most(cmd: &str, usage: &str, parsed: &CmdArgs, max: usize) -> Result<(), CliError> {
    if parsed.pos.len() > max {
        return Err(CliError::usage(format!(
            "`{cmd}` takes at most {max} positional argument(s), got {}: {}",
            parsed.pos.len(),
            parsed.pos.join(" ")
        ))
        .fix(format!("usage: {usage}")));
    }
    Ok(())
}

/// Levenshtein edit distance, for did-you-mean suggestions.
fn levenshtein(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let mut prev: Vec<usize> = (0..=b.len()).collect();
    for (i, ca) in a.iter().enumerate() {
        let mut cur = Vec::with_capacity(b.len() + 1);
        cur.push(i + 1);
        for (j, cb) in b.iter().enumerate() {
            let cost = usize::from(ca != cb);
            cur.push((prev[j] + cost).min(prev[j + 1] + 1).min(cur[j] + 1));
        }
        prev = cur;
    }
    prev[b.len()]
}

/// The closest candidate within a conservative edit distance, or None.
fn closest<'a>(input: &str, candidates: &[&'a str]) -> Option<&'a str> {
    let lowered = input.to_lowercase();
    let (dist, best) = candidates
        .iter()
        .map(|c| (levenshtein(&lowered, &c.to_lowercase()), *c))
        .min()?;
    let max_dist = if input.len() >= 8 { 3 } else { 2 };
    (dist <= max_dist && dist < input.chars().count()).then_some(best)
}

/// "unknown X 'value' (available: a, b, c)" — the standard bad-value error.
fn unknown_value_error(what: &str, value: &str, available: &[&str]) -> CliError {
    CliError::usage(format!(
        "unknown {what} '{value}' (available: {})",
        available.join(", ")
    ))
}

// ---------------------------------------------------------------------------
// Analysis helpers
// ---------------------------------------------------------------------------

/// Analyze `dir`, classifying missing paths (exit 3) apart from analysis
/// failures (exit 4). `incremental` opts into the per-language-batch subgraph
/// cache (also enabled by `TRAILTRACKER_CACHE`); output is byte-identical
/// either way, the cache only trades disk for time. `no_ignore` opts out of
/// the default `.gitignore` filtering (analyze everything on disk).
fn analyze(dir: &str, incremental: bool, no_ignore: bool) -> Result<Analysis, CliError> {
    let path = Path::new(dir);
    if !path.exists() {
        return Err(
            CliError::not_found(format!("path '{dir}' does not exist")).fix(
                "pass an existing directory (paths resolve against the current working \
                 directory).",
            ),
        );
    }
    let opts = AnalyzeOptions {
        cpg: false,
        cache_dir: (incremental || env_cache_enabled()).then(|| {
            env::var_os("TRAILTRACKER_CACHE_DIR")
                .map(std::path::PathBuf::from)
                .unwrap_or_else(|| path.join(".trailtracker-cache"))
        }),
        no_ignore,
    };
    analyze_dir_with(path, &opts)
        .map_err(|e| CliError::analysis(format!("failed to analyze {dir}: {e}")))
}

/// `TRAILTRACKER_CACHE` opts into the incremental cache without the flag
/// (empty, `0`, `false`, and `off` mean off).
fn env_cache_enabled() -> bool {
    match env::var("TRAILTRACKER_CACHE") {
        Ok(v) => !matches!(v.as_str(), "" | "0" | "false" | "off"),
        Err(_) => false,
    }
}

/// Analyze `dir` and return its canonical graph.
fn load_graph(
    dir: &str,
    incremental: bool,
    no_ignore: bool,
) -> Result<trailtracker::graph::Graph, CliError> {
    analyze(dir, incremental, no_ignore).map(|a| a.graph)
}

/// Write `data` to stdout, tolerating a closed pipe (e.g. `| head`).
fn write_stdout(data: &[u8], what: &str) -> Result<(), CliError> {
    let stdout = io::stdout();
    let mut handle = stdout.lock();
    match handle.write_all(data) {
        Ok(()) => Ok(()),
        Err(e) if e.kind() == io::ErrorKind::BrokenPipe => Ok(()),
        Err(e) => Err(CliError::analysis(format!("failed to write {what}: {e}"))),
    }
}

/// `println!` with the [`write_stdout`] EPIPE contract: every stdout line the
/// CLI emits goes through here or `write_stdout`, never through `println!`,
/// which panics when the consumer closes the pipe (UBS audit C1).
fn println_stdout(text: &str, what: &str) -> Result<(), CliError> {
    write_stdout(format!("{text}\n").as_bytes(), what)
}

// ---------------------------------------------------------------------------
// Commands
// ---------------------------------------------------------------------------

fn cmd_graph(rest: &[String]) -> Result<(), CliError> {
    let parsed = split_args("graph", rest)?;
    expect_at_most("graph", "trailtracker graph [DIR] [--json]", &parsed, 1)?;
    // `--json` is accepted as a no-op: the output is already JSONL.
    let dir = parsed.pos.first().copied().unwrap_or(".");
    let analysis = analyze(dir, parsed.incremental, parsed.no_ignore)?;
    write_stdout(analysis.graph.to_jsonl().as_bytes(), "graph")
}

fn cmd_cpg(rest: &[String]) -> Result<(), CliError> {
    let parsed = split_args("cpg", rest)?;
    expect_at_most("cpg", "trailtracker cpg [DIR] [--json]", &parsed, 1)?;
    // `--json` is accepted as a no-op: the output is already JSONL.
    let dir = parsed.pos.first().copied().unwrap_or(".");
    let path = Path::new(dir);
    if !path.exists() {
        return Err(
            CliError::not_found(format!("path '{dir}' does not exist")).fix(
                "pass an existing directory (paths resolve against the current working \
                 directory).",
            ),
        );
    }
    let analysis = analyze_dir_opts(
        path,
        AnalyzeOptions {
            cpg: true,
            no_ignore: parsed.no_ignore,
            ..Default::default()
        },
    )
    .map_err(|e| CliError::analysis(format!("failed to analyze {dir}: {e}")))?;
    write_stdout(analysis.graph.to_jsonl().as_bytes(), "cpg")
}

fn cmd_stats(rest: &[String]) -> Result<(), CliError> {
    let parsed = split_args("stats", rest)?;
    expect_at_most("stats", "trailtracker stats [DIR] [--json]", &parsed, 1)?;
    let dir = parsed.pos.first().copied().unwrap_or(".");
    let analysis = analyze(dir, parsed.incremental, parsed.no_ignore)?;
    if parsed.json {
        return println_stdout(&stats_json(dir, &analysis).to_line(), "stats");
    }
    write_stdout(stats_text(dir, &analysis).as_bytes(), "stats")
}

fn stats_text(dir: &str, analysis: &Analysis) -> String {
    use std::fmt::Write as _;
    let g = &analysis.graph;
    let s = &analysis.stats;
    let mut out = String::new();
    // Writing into a String is infallible; the discarded Results are fmt noise.
    let _ = writeln!(out, "TrailTracker analysis of {dir}");
    let _ = writeln!(out, "  files analyzed      {}", s.files);
    let _ = writeln!(
        out,
        "  lossless files      {} / {}  ({})",
        s.lossless_files,
        s.files,
        if s.files == s.lossless_files {
            "all reconstruct source exactly"
        } else {
            "SOME FILES DID NOT ROUND-TRIP"
        }
    );
    let _ = writeln!(
        out,
        "  parse error bytes   {} / {} ({:.2}%)",
        s.error_bytes,
        s.total_bytes,
        if s.total_bytes == 0 {
            0.0
        } else {
            100.0 * s.error_bytes as f64 / s.total_bytes as f64
        }
    );
    let _ = writeln!(out, "  parser diagnostics  {}", s.diagnostics);
    let _ = writeln!(
        out,
        "  parse failures      {} {}",
        s.parse_failures,
        if s.parse_failures == 0 {
            "(no files crashed analysis)"
        } else {
            "(ISOLATED — see parse_failed nodes)"
        }
    );
    let _ = writeln!(out, "  graph nodes         {}", g.node_count());
    let _ = writeln!(out, "    files             {}", g.count_nodes_of("File"));
    let _ = writeln!(out, "    modules           {}", g.count_nodes_of("Module"));
    let _ = writeln!(
        out,
        "    functions         {}",
        g.count_nodes_of("Function")
    );
    let _ = writeln!(out, "    types             {}", g.count_nodes_of("Type"));
    let _ = writeln!(
        out,
        "    constants         {}",
        g.count_nodes_of("Constant")
    );
    let _ = writeln!(
        out,
        "    external deps     {}",
        g.count_nodes_of("ExternalDependency")
    );
    let _ = writeln!(
        out,
        "    unresolved syms   {}",
        g.count_nodes_of("UnresolvedSymbol")
    );
    let _ = writeln!(out, "  graph edges         {}", g.edge_count());
    let _ = writeln!(
        out,
        "    CONTAINS          {}",
        g.count_edges_of("CONTAINS")
    );
    let _ = writeln!(
        out,
        "    DECLARES          {}",
        g.count_edges_of("DECLARES")
    );
    let _ = writeln!(out, "    CALLS             {}", g.count_edges_of("CALLS"));
    let _ = writeln!(out, "    IMPORTS           {}", g.count_edges_of("IMPORTS"));
    let _ = writeln!(
        out,
        "    DEPENDS_ON        {}",
        g.count_edges_of("DEPENDS_ON")
    );
    let _ = writeln!(
        out,
        "    USES_TYPE         {}",
        g.count_edges_of("USES_TYPE")
    );
    let _ = writeln!(
        out,
        "    HAS_METHOD        {}",
        g.count_edges_of("HAS_METHOD")
    );
    let _ = writeln!(
        out,
        "    IMPLEMENTS        {}",
        g.count_edges_of("IMPLEMENTS")
    );

    let calls = call_provenance(g);
    let _ = writeln!(
        out,
        "  call resolution     resolved {}  ambiguous {}  external {}",
        calls.resolved, calls.ambiguous, calls.external
    );
    for (level, count) in &calls.by_level {
        let _ = writeln!(out, "    {level:<16}  {count}");
    }
    out
}

/// Call-resolution provenance: deterministic, auditable, ambiguity-preserving.
struct CallProvenance {
    by_level: BTreeMap<String, usize>,
    resolved: usize,
    ambiguous: usize,
    external: usize,
}

fn call_provenance(g: &trailtracker::graph::Graph) -> CallProvenance {
    let mut calls = CallProvenance {
        by_level: BTreeMap::new(),
        resolved: 0,
        ambiguous: 0,
        external: 0,
    };
    for e in g.edges().filter(|e| e.kind == "CALLS") {
        if let Some(Json::Str(level)) = e.props.get("resolution") {
            *calls.by_level.entry(level.clone()).or_default() += 1;
        }
        if e.props.get("resolved") == Some(&Json::Bool(true)) {
            calls.resolved += 1;
        }
        if e.props.get("ambiguous") == Some(&Json::Bool(true)) {
            calls.ambiguous += 1;
        }
        if e.props.get("resolution") == Some(&Json::str("external")) {
            calls.external += 1;
        }
    }
    calls
}

/// `stats --json`: the same numbers as the text view, as one stable object.
/// Schema `trailtracker.stats/v1` — see `capabilities`.
fn stats_json(dir: &str, analysis: &Analysis) -> Json {
    let g = &analysis.graph;
    let s = &analysis.stats;

    let mut nodes_by_kind: BTreeMap<String, Json> = BTreeMap::new();
    for n in g.nodes() {
        let entry = nodes_by_kind
            .entry(n.kind.to_string())
            .or_insert(Json::U64(0));
        if let Json::U64(c) = entry {
            *c += 1;
        }
    }
    let mut edges_by_kind: BTreeMap<String, Json> = BTreeMap::new();
    for e in g.edges() {
        let entry = edges_by_kind
            .entry(e.kind.to_string())
            .or_insert(Json::U64(0));
        if let Json::U64(c) = entry {
            *c += 1;
        }
    }

    let calls = call_provenance(g);
    let by_resolution: BTreeMap<String, Json> = calls
        .by_level
        .iter()
        .map(|(k, v)| (k.clone(), Json::U64(*v as u64)))
        .collect();

    Json::obj([
        ("schema", Json::str("trailtracker.stats/v1")),
        ("command", Json::str("stats")),
        ("dir", Json::str(dir)),
        ("files", s.files.into()),
        ("lossless_files", s.lossless_files.into()),
        (
            "parse",
            Json::obj([
                ("error_bytes", s.error_bytes.into()),
                ("total_bytes", s.total_bytes.into()),
                ("diagnostics", s.diagnostics.into()),
                ("failures", s.parse_failures.into()),
            ]),
        ),
        (
            "nodes",
            Json::obj([
                ("total", g.node_count().into()),
                ("by_kind", Json::Object(nodes_by_kind)),
            ]),
        ),
        (
            "edges",
            Json::obj([
                ("total", g.edge_count().into()),
                ("by_kind", Json::Object(edges_by_kind)),
            ]),
        ),
        (
            "calls",
            Json::obj([
                ("resolved", calls.resolved.into()),
                ("ambiguous", calls.ambiguous.into()),
                ("external", calls.external.into()),
                ("by_resolution", Json::Object(by_resolution)),
            ]),
        ),
    ])
}

fn cmd_extract(rest: &[String]) -> Result<(), CliError> {
    let parsed = split_args("extract", rest)?;
    expect_at_most(
        "extract",
        "trailtracker extract NAME [DIR] [--json]",
        &parsed,
        2,
    )?;
    let available: Vec<&str> = extractors().iter().map(|e| e.name()).collect();
    let name = parsed.pos.first().copied().ok_or_else(|| {
        CliError::usage("extract requires an extractor NAME").fix(format!(
            "try `trailtracker extract {} .` — available: {}",
            available.first().copied().unwrap_or("data-ontology"),
            available.join(", ")
        ))
    })?;
    let extractor = extractor_by_name(name).ok_or_else(|| {
        let err = unknown_value_error("extractor", name, &available);
        match closest(name, &available) {
            Some(c) => err.fix(format!("did you mean `trailtracker extract {c}`?")),
            None => err.fix("run `trailtracker capabilities` to list every extractor."),
        }
    })?;
    // `--json` is accepted as a no-op: the output is already JSONL.
    let dir = parsed.pos.get(1).copied().unwrap_or(".");
    let analysis = analyze(dir, parsed.incremental, parsed.no_ignore)?;
    let derived = extractor.extract(&analysis.graph);
    write_stdout(derived.to_jsonl().as_bytes(), "derived graph")
}

/// `enrich-domains [DIR] [--json]` — `enrich` FEATURE BUILDS ONLY (internal
/// tooling; never in the shipped/airgap binary). The optional LLM naming
/// pass over the deterministic domain clusters (see [`trailtracker::enrich`]):
/// membership, counts, and cluster ids are computed locally and are
/// byte-identical to `extract domains`; the LLM contributes ONLY
/// name/description/responsibilities, and the output carries an attestation
/// block (backend, model, evidence-pack FNV-1a-64 hash, timestamp) instead
/// of a byte-stability promise. Backend absent or misbehaving → exit 4 with
/// a fix line; names are never invented locally.
#[cfg(feature = "enrich")]
fn cmd_enrich_domains(rest: &[String]) -> Result<(), CliError> {
    let parsed = split_args("enrich-domains", rest)?;
    expect_at_most(
        "enrich-domains",
        "trailtracker enrich-domains [DIR] [--json]",
        &parsed,
        1,
    )?;
    let dir = parsed.pos.first().copied().unwrap_or(".");
    let graph = load_graph(dir, parsed.incremental, parsed.no_ignore)?;
    let enrichment = trailtracker::enrich::enrich(&graph).map_err(|e| {
        CliError::analysis(e).fix(format!(
            "enrich-domains needs an LLM backend and never falls back to fake names. \
             Install the Claude Code CLI (`npm install -g @anthropic-ai/claude-code`) for \
             the default backend (`{}`), or set {} to any command that accepts the prompt \
             as its final argument and prints the JSON reply on stdout. For the \
             deterministic, airgap-safe view run `trailtracker extract domains {dir}`.",
            trailtracker::enrich::DEFAULT_BACKEND,
            trailtracker::enrich::ENV_BACKEND,
        ))
    })?;
    if parsed.json {
        return println_stdout(&enrichment.to_json(dir).to_line(), "enriched domains");
    }
    write_stdout(enrichment.to_text(dir).as_bytes(), "enriched domains")
}

/// `export ontoloom [DIR] [--view NAME]` — analyze DIR, apply the chosen view
/// (an extractor name, or `graph` for the base graph; default `hierarchy`),
/// and print the result as Ontoloom wire JSON, loadable directly by the
/// Ontoloom editor.
fn cmd_export(rest: &[String]) -> Result<(), CliError> {
    let mut view = String::from("hierarchy");
    let mut incremental = false;
    let mut no_ignore = false;
    let mut pos: Vec<&str> = Vec::new();
    let mut i = 0;
    while i < rest.len() {
        let arg = rest[i].as_str();
        if arg == "--view" {
            i += 1;
            view = rest.get(i).cloned().ok_or_else(|| {
                CliError::usage("--view requires a NAME (an extractor name, or `graph`)")
                    .fix("example: `trailtracker export ontoloom . --view domains`")
            })?;
        } else if let Some(v) = arg.strip_prefix("--view=") {
            view = v.to_string();
        } else if arg == "--json" || arg == "--robot" {
            // No-op: the output is already JSON.
        } else if arg == "--incremental" {
            incremental = true;
        } else if arg == "--no-ignore" {
            no_ignore = true;
        } else if arg.starts_with('-') {
            let known = [
                "--view",
                "--json",
                "--robot",
                "--incremental",
                "--no-ignore",
            ];
            let fix = match closest(arg, &known) {
                Some(k) => format!("did you mean `{k}`?"),
                None => "usage: trailtracker export ontoloom [DIR] [--view NAME]".to_string(),
            };
            return Err(CliError::usage(format!("unknown flag '{arg}' for `export`")).fix(fix));
        } else {
            pos.push(arg);
        }
        i += 1;
    }
    // Same surplus-positional rejection as every `split_args` command: a
    // mistyped invocation (e.g. `export ontoloom . domains` missing `--view`)
    // must fail loudly, not silently drop arguments (UBS audit C2).
    let parsed = CmdArgs {
        pos,
        json: false,
        incremental,
        no_ignore,
    };
    expect_at_most(
        "export",
        "trailtracker export ontoloom [DIR] [--view NAME]",
        &parsed,
        2,
    )?;
    let pos = parsed.pos;
    let format = pos.first().copied().ok_or_else(|| {
        CliError::usage("export requires a FORMAT")
            .fix("try `trailtracker export ontoloom .` (available formats: ontoloom)")
    })?;
    if format != "ontoloom" {
        return Err(unknown_value_error("export format", format, &["ontoloom"])
            .fix("try `trailtracker export ontoloom .`"));
    }
    let dir = pos.get(1).copied().unwrap_or(".");

    let analysis = analyze(dir, parsed.incremental, parsed.no_ignore)?;
    let graph = if view == "graph" {
        analysis.graph
    } else {
        let extractor = extractor_by_name(&view).ok_or_else(|| {
            let mut available: Vec<&str> = vec!["graph"];
            available.extend(extractors().iter().map(|e| e.name()));
            let err = unknown_value_error("view", &view, &available);
            match closest(&view, &available) {
                Some(c) => err.fix(format!("did you mean `--view {c}`?")),
                None => err.fix("run `trailtracker capabilities` to list every view."),
            }
        })?;
        extractor.extract(&analysis.graph)
    };

    // Human title for the Ontoloom graph: the directory's last segment + view.
    let base = dir
        .trim_end_matches(['/', '\\'])
        .rsplit(['/', '\\'])
        .next()
        .filter(|s| !s.is_empty())
        .unwrap_or(dir);
    let wire = trailtracker::export::ontoloom_wire(&graph, &format!("{base} ({view})"));

    write_stdout(format!("{wire}\n").as_bytes(), "export")
}

/// `dossier <DIR> [-o out.html]` — the client-ready deliverable: analyze DIR
/// and write ONE self-contained HTML file (inline CSS + JS, embedded
/// hierarchy graph, zero external requests) containing the brief, the
/// interactive Domain→Unit→File→Symbol code map, and the layer-violations
/// table. In `enrich` feature builds (internal tooling only), `--enrich
/// enrich.json` additionally renders the enriched domain cards with their
/// attestation block; the default/airgap build has no such flag and no such
/// section. Output is byte-deterministic for identical inputs (the
/// "generated" line attests a content fingerprint, never a wall clock).
/// Prints the output path on success. Exit 2 usage, 3 missing DIR (or, with
/// the feature, enrich file), 4 analysis/write failure.
fn cmd_dossier(rest: &[String]) -> Result<(), CliError> {
    #[cfg(feature = "enrich")]
    const USAGE: &str = "trailtracker dossier <DIR> [-o out.html] [--enrich enrich.json]";
    #[cfg(not(feature = "enrich"))]
    const USAGE: &str = "trailtracker dossier <DIR> [-o out.html]";
    let mut out_path: Option<String> = None;
    #[cfg(feature = "enrich")]
    let mut enrich_path: Option<String> = None;
    let mut incremental = false;
    let mut no_ignore = false;
    let mut pos: Vec<&str> = Vec::new();
    let mut i = 0;
    while i < rest.len() {
        let arg = rest[i].as_str();
        if arg == "-o" || arg == "--out" {
            i += 1;
            out_path = Some(rest.get(i).cloned().ok_or_else(|| {
                CliError::usage(format!("{arg} requires a PATH")).fix(format!(
                    "example: `trailtracker dossier . -o dossier.html` — usage: {USAGE}"
                ))
            })?);
        } else if let Some(v) = arg.strip_prefix("--out=") {
            out_path = Some(v.to_string());
        } else if arg == "--enrich" || arg.starts_with("--enrich=") {
            // Only `enrich` feature builds know this flag; the default build
            // rejects it like any other unknown flag.
            #[cfg(feature = "enrich")]
            if let Some(v) = arg.strip_prefix("--enrich=") {
                enrich_path = Some(v.to_string());
            } else {
                i += 1;
                enrich_path = Some(rest.get(i).cloned().ok_or_else(|| {
                    CliError::usage(
                        "--enrich requires a FILE (the output of `enrich-domains --json`)",
                    )
                    .fix(format!(
                        "generate one with `trailtracker enrich-domains DIR --json > enrich.json` \
                         — usage: {USAGE}"
                    ))
                })?);
            }
            #[cfg(not(feature = "enrich"))]
            return Err(
                CliError::usage(format!("unknown flag '{arg}' for `dossier`"))
                    .fix(format!("usage: {USAGE}")),
            );
        } else if arg == "--json" || arg == "--robot" {
            // No-op: the output is an HTML file; the only stdout data is its path.
        } else if arg == "--incremental" {
            incremental = true;
        } else if arg == "--no-ignore" {
            no_ignore = true;
        } else if arg.starts_with('-') {
            let known = [
                "-o",
                "--out",
                #[cfg(feature = "enrich")]
                "--enrich",
                "--json",
                "--robot",
                "--incremental",
                "--no-ignore",
            ];
            let fix = match closest(arg, &known) {
                Some(k) => format!("did you mean `{k}`?"),
                None => format!("usage: {USAGE}"),
            };
            return Err(CliError::usage(format!("unknown flag '{arg}' for `dossier`")).fix(fix));
        } else {
            pos.push(arg);
        }
        i += 1;
    }
    let parsed = CmdArgs {
        pos,
        json: false,
        incremental,
        no_ignore,
    };
    expect_at_most("dossier", USAGE, &parsed, 1)?;
    let dir = parsed.pos.first().copied().ok_or_else(|| {
        CliError::usage("dossier requires a DIR to analyze").fix(format!(
            "example: `trailtracker dossier .` — usage: {USAGE}"
        ))
    })?;

    // Validate the optional enrich document before spending analysis time
    // (enrich feature builds only; the default build always passes None).
    #[cfg(feature = "enrich")]
    let enrich_json = match &enrich_path {
        Some(p) => {
            let text = fs::read_to_string(p).map_err(|e| {
                CliError::not_found(format!("failed to read enrich file {p}: {e}")).fix(
                    "generate one with `trailtracker enrich-domains DIR --json > enrich.json`.",
                )
            })?;
            if !text.contains("\"trailtracker.enrich/v1\"") {
                return Err(CliError::usage(format!(
                    "{p} is not a trailtracker.enrich/v1 document"
                ))
                .fix(
                    "pass the JSON produced by `trailtracker enrich-domains DIR --json` \
                     (its `schema` field must be \"trailtracker.enrich/v1\").",
                ));
            }
            Some(text)
        }
        None => None,
    };
    #[cfg(not(feature = "enrich"))]
    let enrich_json: Option<String> = None;

    let analysis = analyze(dir, parsed.incremental, parsed.no_ignore)?;
    let html = trailtracker::dossier::dossier_html(&analysis, dir, enrich_json.as_deref());
    let out = out_path
        .unwrap_or_else(|| format!("{}-dossier.html", trailtracker::dossier::repo_name(dir)));
    fs::write(&out, html).map_err(|e| {
        CliError::analysis(format!("failed to write {out}: {e}"))
            .fix("pass a writable output path with `-o out.html`.")
    })?;
    println_stdout(&out, "dossier path")
}

/// `arch-verify [DIR] [--spec PATH] [--json]` — continuous architecture
/// verification (ADR-0005): load the human-authored spec (default
/// `<DIR>/.trailtracker-arch.json`), analyze DIR, evaluate the rules, and
/// report findings. Exit 0 when the spec holds (no findings, or warn-only),
/// 1 when at least one `error`-severity finding fired (the CI gate), 2 on a
/// malformed spec or usage error, 3 when DIR or the spec file is missing.
fn cmd_arch_verify(rest: &[String]) -> Result<u8, CliError> {
    const USAGE: &str = "trailtracker arch-verify [DIR] [--spec PATH] [--json]";
    let mut spec_path: Option<String> = None;
    let mut json = false;
    let mut incremental = false;
    let mut no_ignore = false;
    let mut pos: Vec<&str> = Vec::new();
    let mut i = 0;
    while i < rest.len() {
        let arg = rest[i].as_str();
        if arg == "--spec" {
            i += 1;
            spec_path = Some(rest.get(i).cloned().ok_or_else(|| {
                CliError::usage("--spec requires a PATH (the architecture spec file)").fix(format!(
                    "example: `trailtracker arch-verify . --spec arch.json` — usage: {USAGE}"
                ))
            })?);
        } else if let Some(v) = arg.strip_prefix("--spec=") {
            spec_path = Some(v.to_string());
        } else if arg == "--json" || arg == "--robot" {
            json = true;
        } else if arg == "--incremental" {
            incremental = true;
        } else if arg == "--no-ignore" {
            no_ignore = true;
        } else if arg.starts_with('-') {
            let known = [
                "--spec",
                "--json",
                "--robot",
                "--incremental",
                "--no-ignore",
            ];
            let fix = match closest(arg, &known) {
                Some(k) => format!("did you mean `{k}`?"),
                None => format!("usage: {USAGE}"),
            };
            return Err(
                CliError::usage(format!("unknown flag '{arg}' for `arch-verify`")).fix(fix),
            );
        } else {
            pos.push(arg);
        }
        i += 1;
    }
    let parsed = CmdArgs {
        pos,
        json,
        incremental,
        no_ignore,
    };
    expect_at_most("arch-verify", USAGE, &parsed, 1)?;
    let dir = parsed.pos.first().copied().unwrap_or(".");

    // Resolve + read + parse the spec BEFORE spending analysis time.
    let spec_file = match &spec_path {
        Some(p) => p.clone(),
        None => Path::new(dir)
            .join(arch::SPEC_FILE)
            .to_string_lossy()
            .into_owned(),
    };
    let text = fs::read_to_string(&spec_file).map_err(|e| {
        CliError::not_found(format!("failed to read arch spec {spec_file}: {e}")).fix(format!(
            "bootstrap one from the current architecture: `trailtracker arch-init {dir} -o \
             {spec_file}` (or pass --spec PATH)."
        ))
    })?;
    let spec = arch::parse_spec(&text).map_err(|e| {
        CliError::usage(format!("invalid arch spec {spec_file}: {e}")).fix(
            "the spec is {format, domains:[{name, pathPrefixes[]}], rules:[{type, ...}]} — \
             see `trailtracker arch-init` for a valid example, or docs/decisions/0005.",
        )
    })?;

    let graph = load_graph(dir, parsed.incremental, parsed.no_ignore)?;
    let findings = arch::verify(&spec, &graph);
    let gated = arch::gates(&findings);
    let exit = u8::from(gated);
    let status = if findings.is_empty() {
        "clean"
    } else if gated {
        "violated"
    } else {
        "warnings"
    };

    if parsed.json {
        let doc = Json::obj([
            ("format", Json::str(arch::REPORT_FORMAT)),
            ("dir", Json::str(dir)),
            ("spec", Json::str(&spec_file)),
            ("domains", Json::U64(spec.domains.len() as u64)),
            ("rules", Json::U64(spec.rules.len() as u64)),
            (
                "findings",
                Json::Array(findings.iter().map(arch::ArchFinding::to_json).collect()),
            ),
            ("status", Json::str(status)),
            ("exit", Json::U64(u64::from(exit))),
        ]);
        println_stdout(&doc.to_line(), "arch-verify report")?;
        return Ok(exit);
    }

    let mut out = String::new();
    out.push_str(&format!("trailtracker arch-verify: {dir}\n"));
    out.push_str(&format!(
        "spec: {spec_file} — {} domain(s), {} rule(s)\n",
        spec.domains.len(),
        spec.rules.len()
    ));
    if findings.is_empty() {
        out.push_str("findings: none\n");
    } else {
        out.push_str(&format!("findings ({}):\n", findings.len()));
        for f in &findings {
            out.push_str(&format!(
                "  [{}] {}: {}\n",
                f.severity.as_str(),
                f.rule_id,
                f.message
            ));
            for e in &f.examples {
                out.push_str(&format!("        evidence: {e}\n"));
            }
        }
    }
    out.push_str(&format!("status: {status} (exit {exit})\n"));
    write_stdout(out.as_bytes(), "arch-verify report")?;
    Ok(exit)
}

/// `arch-init [DIR] [-o PATH]` — bootstrap an architecture spec from the
/// CURRENT recovered architecture (ADR-0005): recovered business domains
/// become declared domains with derived pathPrefixes, plus existence (error)
/// and containment (warn) rules and the observed inter-domain dependency
/// baseline. Prints the spec to stdout by default (redirect to adopt); `-o`
/// writes a file, refusing to overwrite an existing one.
fn cmd_arch_init(rest: &[String]) -> Result<(), CliError> {
    const USAGE: &str = "trailtracker arch-init [DIR] [-o PATH]";
    let mut out_path: Option<String> = None;
    let mut incremental = false;
    let mut no_ignore = false;
    let mut pos: Vec<&str> = Vec::new();
    let mut i = 0;
    while i < rest.len() {
        let arg = rest[i].as_str();
        if arg == "-o" || arg == "--out" {
            i += 1;
            out_path = Some(rest.get(i).cloned().ok_or_else(|| {
                CliError::usage(format!("{arg} requires a PATH")).fix(format!(
                    "example: `trailtracker arch-init . -o .trailtracker-arch.json` — \
                     usage: {USAGE}"
                ))
            })?);
        } else if let Some(v) = arg.strip_prefix("--out=") {
            out_path = Some(v.to_string());
        } else if arg == "--json" || arg == "--robot" {
            // No-op: the output is already JSON.
        } else if arg == "--incremental" {
            incremental = true;
        } else if arg == "--no-ignore" {
            no_ignore = true;
        } else if arg.starts_with('-') {
            let known = [
                "-o",
                "--out",
                "--json",
                "--robot",
                "--incremental",
                "--no-ignore",
            ];
            let fix = match closest(arg, &known) {
                Some(k) => format!("did you mean `{k}`?"),
                None => format!("usage: {USAGE}"),
            };
            return Err(CliError::usage(format!("unknown flag '{arg}' for `arch-init`")).fix(fix));
        } else {
            pos.push(arg);
        }
        i += 1;
    }
    let parsed = CmdArgs {
        pos,
        json: false,
        incremental,
        no_ignore,
    };
    expect_at_most("arch-init", USAGE, &parsed, 1)?;
    let dir = parsed.pos.first().copied().unwrap_or(".");

    if let Some(out) = &out_path {
        if Path::new(out).exists() {
            return Err(CliError::usage(format!(
                "{out} already exists — arch-init never overwrites a spec"
            ))
            .fix("edit the existing spec, or pass a different -o PATH."));
        }
    }

    let graph = load_graph(dir, parsed.incremental, parsed.no_ignore)?;
    let spec = trailtracker::arch::init_spec(&graph);
    match out_path {
        Some(out) => {
            fs::write(&out, &spec).map_err(|e| {
                CliError::analysis(format!("failed to write {out}: {e}"))
                    .fix("pass a writable output path with `-o PATH`.")
            })?;
            println_stdout(&out, "arch-init path")
        }
        None => write_stdout(spec.as_bytes(), "arch spec"),
    }
}

/// `violations <DIR> [--examples N] [--json]` — the spec-free full
/// layer-violations report: every dependency OR inheritance edge that points
/// outward against the clean-architecture direction rule, at UNIT grain
/// (from-unit → to-unit with layers, complete edge counts, complete
/// symbol-grain evidence — `--examples N` bounds the evidence list, never
/// the counts), ranked worst-first and grouped by layer pair. Needs no arch
/// spec — the layers view's recovered placement is the ground truth. Exit 0
/// clean, 1 violations present (the CI-style findings code, same convention
/// as `arch-verify`/`doctor`).
/// Strip `--examples N` / `--examples=N` from an arg list. `None` = no cap
/// (every named edge — the default: the whole point is named evidence).
fn take_examples_flag(
    rest: &[String],
    usage: &str,
) -> Result<(Option<usize>, Vec<String>), CliError> {
    let parse = |v: &str| -> Result<usize, CliError> {
        v.parse::<usize>().map_err(|_| {
            CliError::usage(format!(
                "--examples expects a non-negative integer, got '{v}'"
            ))
            .fix(format!("usage: {usage}"))
        })
    };
    let mut examples = None;
    let mut kept: Vec<String> = Vec::with_capacity(rest.len());
    let mut i = 0;
    while i < rest.len() {
        let arg = rest[i].as_str();
        if arg == "--examples" {
            let v = rest.get(i + 1).ok_or_else(|| {
                CliError::usage("--examples requires a value").fix(format!("usage: {usage}"))
            })?;
            examples = Some(parse(v)?);
            i += 2;
            continue;
        }
        if let Some(v) = arg.strip_prefix("--examples=") {
            examples = Some(parse(v)?);
            i += 1;
            continue;
        }
        kept.push(rest[i].clone());
        i += 1;
    }
    Ok((examples, kept))
}

fn cmd_violations(rest: &[String]) -> Result<u8, CliError> {
    const USAGE: &str = "trailtracker violations <DIR> [--examples N] [--json]";
    let (examples, rest) = take_examples_flag(rest, USAGE)?;
    let parsed = split_args("violations", &rest)?;
    expect_at_most("violations", USAGE, &parsed, 1)?;
    let dir = parsed.pos.first().copied().ok_or_else(|| {
        CliError::usage("violations requires a DIR to analyze").fix(format!(
            "example: `trailtracker violations .` — usage: {USAGE}"
        ))
    })?;
    let graph = load_graph(dir, parsed.incremental, parsed.no_ignore)?;
    let report = trailtracker::violations::violations_report_capped(&graph, examples);
    if parsed.json {
        println_stdout(&report.to_json(dir).to_line(), "violations report")?;
    } else {
        write_stdout(report.to_text(dir).as_bytes(), "violations report")?;
    }
    Ok(report.exit_code())
}

fn cmd_deadcode(rest: &[String]) -> Result<u8, CliError> {
    use trailtracker::deadcode::ConfigErrorKind;

    let options = trailtracker::deadcode::parse_args(rest).map_err(|error| CliError {
        exit: EXIT_USAGE,
        message: error.message,
        fix: Some(error.fix),
    })?;
    let dir = options.dir.as_str();
    let graph = load_graph(dir, options.incremental, options.no_ignore)?;
    let mut config = trailtracker::deadcode::load_config(Path::new(dir), options.config.as_deref())
        .map_err(|error| {
            let message = format!(
                "deadcode config {}: {}",
                error.path.display(),
                error.message
            );
            match error.kind {
                ConfigErrorKind::Invalid => CliError::usage(message).fix(
                    "valid fields are roots, keep, test_roots, public_api, and mention_exclude; \
                         unknown fields are rejected.",
                ),
                ConfigErrorKind::NotFound | ConfigErrorKind::Read => CliError::not_found(message)
                    .fix("pass a readable config path, or omit --config for defaults."),
            }
        })?;
    if options.no_test_roots {
        config.test_roots = false;
    }
    let report =
        trailtracker::deadcode::analyze_graph(&graph, Path::new(dir), &config, !options.no_ignore)
            .map_err(CliError::analysis)?;
    if let Some(target) = &options.why {
        let output = report
            .why_text(&graph, target)
            .map_err(|error| explain_error(error, dir, "deadcode --why"))?;
        write_stdout(output.as_bytes(), "deadcode why")?;
        return Ok(0);
    }
    if options.json {
        println_stdout(
            &report.to_json_line(dir, options.min_confidence, options.limit),
            "deadcode report",
        )?;
    } else {
        write_stdout(
            report
                .to_text(options.min_confidence, options.limit)
                .as_bytes(),
            "deadcode report",
        )?;
    }
    Ok(report.exit_code(options.min_confidence))
}

/// `verbalize <DIR> [--view NAME] [--target ID] [--budget N] [--json]` —
/// the graph as retrieval-safe sentences (ADR-0008): a glossary prelude of
/// dense value-ranked handles, then one fact per sentence in domain-major
/// order, all drawn from the versioned template registry. `--budget` cuts
/// honestly (an omission sentence reports exactly what was dropped);
/// `--target` renders one node's card (identity, fan-in/out, blast radius)
/// with `explain`'s resolution semantics.
fn cmd_verbalize(rest: &[String]) -> Result<(), CliError> {
    const USAGE: &str = "trailtracker verbalize <DIR> [--view summary|hotspots|dependents|\
                         violations|domains|all] [--target ID] [--budget N] [--json]";
    use trailtracker::verbalize::{verbalize, verbalize_target, Options, View};

    let mut view: Option<String> = None;
    let mut target: Option<String> = None;
    let mut budget: Option<usize> = None;
    let mut json = false;
    let mut incremental = false;
    let mut no_ignore = false;
    let mut pos: Vec<&str> = Vec::new();
    let mut i = 0;
    let value_of = |rest: &[String], i: &mut usize, flag: &str| -> Result<String, CliError> {
        *i += 1;
        rest.get(*i).cloned().ok_or_else(|| {
            CliError::usage(format!("{flag} requires a value")).fix(format!("usage: {USAGE}"))
        })
    };
    while i < rest.len() {
        let arg = rest[i].as_str();
        if arg == "--view" {
            view = Some(value_of(rest, &mut i, "--view")?);
        } else if let Some(v) = arg.strip_prefix("--view=") {
            view = Some(v.to_string());
        } else if arg == "--target" {
            target = Some(value_of(rest, &mut i, "--target")?);
        } else if let Some(v) = arg.strip_prefix("--target=") {
            target = Some(v.to_string());
        } else if arg == "--budget" {
            budget = Some(parse_verbalize_budget(&value_of(
                rest, &mut i, "--budget",
            )?)?);
        } else if let Some(v) = arg.strip_prefix("--budget=") {
            budget = Some(parse_verbalize_budget(v)?);
        } else if arg == "--json" || arg == "--robot" {
            json = true;
        } else if arg == "--incremental" {
            incremental = true;
        } else if arg == "--no-ignore" {
            no_ignore = true;
        } else if arg.starts_with('-') {
            let known = [
                "--view",
                "--target",
                "--budget",
                "--json",
                "--robot",
                "--incremental",
                "--no-ignore",
            ];
            let fix = match closest(arg, &known) {
                Some(k) => format!("did you mean `{k}`?"),
                None => format!("usage: {USAGE}"),
            };
            return Err(CliError::usage(format!("unknown flag '{arg}' for `verbalize`")).fix(fix));
        } else {
            pos.push(arg);
        }
        i += 1;
    }
    let parsed = CmdArgs {
        pos,
        json,
        incremental,
        no_ignore,
    };
    expect_at_most("verbalize", USAGE, &parsed, 1)?;
    let dir = parsed.pos.first().copied().ok_or_else(|| {
        CliError::usage("verbalize requires a DIR to analyze").fix(format!(
            "example: `trailtracker verbalize . --view summary` — usage: {USAGE}"
        ))
    })?;
    if view.is_some() && target.is_some() {
        return Err(
            CliError::usage("--view and --target are mutually exclusive").fix(
                "--target renders one node's card; --view renders a whole-graph document. \
                 Pass one or the other.",
            ),
        );
    }
    let view = match view.as_deref() {
        None => View::default(),
        Some(name) => View::by_name(name).ok_or_else(|| {
            let err = unknown_value_error("view", name, View::NAMES);
            match closest(name, View::NAMES) {
                Some(c) => err.fix(format!("did you mean `--view {c}`?")),
                None => err.fix(format!("usage: {USAGE}")),
            }
        })?,
    };
    let analysis = analyze(dir, parsed.incremental, parsed.no_ignore)?;
    let (doc, view_label) = match target {
        Some(t) => (
            verbalize_target(&analysis, &t, budget)
                .map_err(|e| explain_error(e, dir, "verbalize"))?,
            "target".to_string(),
        ),
        None => (
            verbalize(&analysis, &Options { view, budget }),
            view.name().to_string(),
        ),
    };
    if parsed.json {
        println_stdout(
            &doc.to_json(dir, &view_label).to_line(),
            "verbalize document",
        )
    } else {
        write_stdout(doc.to_text().as_bytes(), "verbalize document")
    }
}

/// Parse the `--budget` character count for `verbalize`.
fn parse_verbalize_budget(raw: &str) -> Result<usize, CliError> {
    raw.parse::<usize>().map_err(|_| {
        CliError::usage(format!("--budget expects a character count, got '{raw}'"))
            .fix("example: `trailtracker verbalize . --budget 8000`")
    })
}

/// `query <kind> <target> [DIR]` and `query deepest-flows [DIR]`. A `--json`
/// flag may appear anywhere and switches the output to a machine object.
fn cmd_query(rest: &[String]) -> Result<(), CliError> {
    let parsed = split_args("query", rest)?;
    let kind = parsed.pos.first().copied().ok_or_else(|| {
        unknown_value_error("query kind", "(none)", QUERY_KINDS)
            .fix("example: `trailtracker query deepest-flows . --json`")
    })?;

    let out = match kind {
        "deepest-flows" => {
            expect_at_most(
                "query deepest-flows",
                "trailtracker query deepest-flows [DIR] [--json]",
                &parsed,
                2,
            )?;
            let dir = parsed.pos.get(1).copied().unwrap_or(".");
            let graph = load_graph(dir, parsed.incremental, parsed.no_ignore)?;
            trailtracker::query::deepest_flows(&graph, parsed.json)
        }
        "what-touches" | "blast-radius" | "uses" => {
            expect_at_most(
                "query",
                "trailtracker query KIND <id-or-name> [DIR] [--json]",
                &parsed,
                3,
            )?;
            let target = parsed.pos.get(1).copied().ok_or_else(|| {
                CliError::usage(format!("query {kind} requires a <id-or-name> target")).fix(
                    "pass a node name or exact node id (find them via `trailtracker graph DIR`).",
                )
            })?;
            let dir = parsed.pos.get(2).copied().unwrap_or(".");
            let graph = load_graph(dir, parsed.incremental, parsed.no_ignore)?;
            let result = match kind {
                "what-touches" => trailtracker::query::what_touches(&graph, target, parsed.json),
                "uses" => trailtracker::query::uses(&graph, target, parsed.json),
                _ => trailtracker::query::blast_radius(&graph, target, parsed.json),
            };
            result.map_err(|e| {
                CliError::usage(e).fix(
                    "targets match node names or exact ids; list candidates with \
                     `trailtracker graph DIR` or orient with `trailtracker brief DIR`.",
                )
            })?
        }
        other => {
            let err = unknown_value_error("query kind", other, QUERY_KINDS);
            return Err(match closest(other, QUERY_KINDS) {
                Some(c) => err.fix(format!("did you mean `trailtracker query {c}`?")),
                None => err.fix("example: `trailtracker query deepest-flows . --json`"),
            });
        }
    };
    write_stdout(out.as_bytes(), "query result")
}

/// `explain <target> [DIR] [--json]` — the atomic understanding primitive:
/// one card that joins identity, classification (domain/layer/archetype),
/// connectivity, blast radius, and nearest neighbors for a file or symbol.
/// Pure composition over existing deterministic passes (see
/// [`trailtracker::explain`]). Targets resolve exact-id → exact-file-path →
/// exact-name; an ambiguous name exits 2 with the candidate list, an unknown
/// target exits 3 with hybrid-search suggestions.
fn cmd_explain(rest: &[String]) -> Result<(), CliError> {
    const USAGE: &str = "trailtracker explain <id-or-path-or-name> [DIR] [--json]";
    let parsed = split_args("explain", rest)?;
    expect_at_most("explain", USAGE, &parsed, 2)?;
    let target = parsed.pos.first().copied().unwrap_or("");
    if target.trim().is_empty() {
        return Err(CliError::usage(
            "explain requires a <target>: a node id, file path, or symbol name",
        )
        .fix(format!(
            "example: `trailtracker explain Engine eval/corpus/calc` — find names with \
             `trailtracker search \"<words>\" DIR`. Usage: {USAGE}"
        )));
    }
    let dir = parsed.pos.get(1).copied().unwrap_or(".");
    let graph = load_graph(dir, parsed.incremental, parsed.no_ignore)?;
    let out = trailtracker::explain::explain(&graph, target, dir, parsed.json)
        .map_err(|e| explain_error(e, dir, "explain"))?;
    write_stdout(out.as_bytes(), "explain card")
}

/// Map an [`ExplainError`](trailtracker::explain::ExplainError) onto the CLI
/// error contract: ambiguity is a usage error (exit 2) carrying the candidate
/// list did-you-mean style; not-found is exit 3 carrying search suggestions.
/// `verb` names the command to retry (`explain`, `nav expand`) in fix lines.
fn explain_error(err: trailtracker::explain::ExplainError, dir: &str, verb: &str) -> CliError {
    /// Candidate lists stay readable: show at most this many, then "+N more".
    const MAX_SHOWN: usize = 8;
    match err {
        trailtracker::explain::ExplainError::Ambiguous { target, candidates } => {
            let mut shown: Vec<String> = candidates
                .iter()
                .take(MAX_SHOWN)
                .map(|c| {
                    if c.location.is_empty() {
                        format!("{} ({})", c.id, c.kind)
                    } else {
                        format!("{} ({}, {})", c.id, c.kind, c.location)
                    }
                })
                .collect();
            if candidates.len() > MAX_SHOWN {
                shown.push(format!("… +{} more", candidates.len() - MAX_SHOWN));
            }
            CliError::usage(format!(
                "target '{target}' is ambiguous: {} nodes match: {}",
                candidates.len(),
                shown.join("; ")
            ))
            .fix(format!(
                "pass one exact node id, e.g. `trailtracker {verb} {} {dir}`.",
                candidates[0].id
            ))
        }
        trailtracker::explain::ExplainError::NotFound {
            target,
            suggestions,
        } => {
            let err = CliError::not_found(format!("no node matching '{target}' in {dir}"));
            if suggestions.is_empty() {
                err.fix(format!(
                    "find targets with `trailtracker search \"{target}\" {dir}` or orient with \
                     `trailtracker brief {dir}`."
                ))
            } else {
                let names: Vec<String> = suggestions
                    .iter()
                    .map(|s| format!("{} ({})", s.name, s.id))
                    .collect();
                err.fix(format!(
                    "closest matches: {} — or search with `trailtracker search \"{target}\" \
                     {dir}`.",
                    names.join("; ")
                ))
            }
        }
    }
}

/// `search "<query>" [DIR] [--limit N]` — hybrid code search over the graph:
/// BM25 and hash-embedding rankings fused by reciprocal rank, then re-ranked
/// by graph-structural proximity to the top lexical anchors. Deterministic,
/// no LLM, no network. `--json` emits schema `trailtracker.search/v1`.
fn cmd_search(rest: &[String]) -> Result<(), CliError> {
    const USAGE: &str = "trailtracker search \"<query>\" [DIR] [--limit N] [--json]";
    let parse_limit = |raw: &str| -> Result<usize, CliError> {
        raw.parse::<usize>().map_err(|_| {
            CliError::usage(format!(
                "--limit must be a non-negative integer, got '{raw}'"
            ))
            .fix(format!("usage: {USAGE}"))
        })
    };

    let mut limit: usize = 20;
    let mut json = false;
    let mut incremental = false;
    let mut no_ignore = false;
    let mut pos: Vec<&str> = Vec::new();
    let mut i = 0;
    while i < rest.len() {
        let arg = rest[i].as_str();
        if arg == "--limit" {
            i += 1;
            let raw = rest.get(i).ok_or_else(|| {
                CliError::usage("--limit requires a number N")
                    .fix("example: `trailtracker search \"basket repository\" . --limit 5`")
            })?;
            limit = parse_limit(raw)?;
        } else if let Some(v) = arg.strip_prefix("--limit=") {
            limit = parse_limit(v)?;
        } else if arg == "--json" || arg == "--robot" {
            json = true;
        } else if arg == "--incremental" {
            incremental = true;
        } else if arg == "--no-ignore" {
            no_ignore = true;
        } else if arg.starts_with('-') {
            let known = [
                "--limit",
                "--json",
                "--robot",
                "--incremental",
                "--no-ignore",
            ];
            let fix = match closest(arg, &known) {
                Some(k) => format!("did you mean `{k}`?"),
                None => format!("usage: {USAGE}"),
            };
            return Err(CliError::usage(format!("unknown flag '{arg}' for `search`")).fix(fix));
        } else {
            pos.push(arg);
        }
        i += 1;
    }
    let parsed = CmdArgs {
        pos,
        json,
        incremental,
        no_ignore,
    };
    expect_at_most("search", USAGE, &parsed, 2)?;
    let query = parsed.pos.first().copied().unwrap_or("");
    if query.trim().is_empty() {
        return Err(
            CliError::usage("search requires a non-empty <query>").fix(format!(
                "pass the words you are looking for, e.g. `trailtracker search \"parse \
             expression\" .` — usage: {USAGE}"
            )),
        );
    }
    let dir = parsed.pos.get(1).copied().unwrap_or(".");
    let graph = load_graph(dir, parsed.incremental, parsed.no_ignore)?;
    let results = trailtracker::search::search(&graph, query, limit);

    if parsed.json {
        return println_stdout(
            &search_json(query, dir, &results).to_line(),
            "search results",
        );
    }
    write_stdout(
        search_text(query, dir, &results).as_bytes(),
        "search results",
    )
}

/// Human rendering of search results: rank, score (3dp), name (kind), path,
/// and the why-signals joined with " · ".
fn search_text(query: &str, dir: &str, results: &[trailtracker::search::SearchResult]) -> String {
    use std::fmt::Write as _;
    let mut out = String::new();
    let noun = if results.len() == 1 {
        "result"
    } else {
        "results"
    };
    let _ = writeln!(
        out,
        "search \"{query}\" in {dir} — {} {noun}",
        results.len()
    );
    for (i, r) in results.iter().enumerate() {
        let _ = write!(out, "{:>3}. {:.3}  {} ({})", i + 1, r.score, r.name, r.kind);
        if !r.path.is_empty() {
            let _ = write!(out, "  {}", r.path);
        }
        let _ = writeln!(out);
        if !r.why.is_empty() {
            let _ = writeln!(out, "           {}", r.why.join(" · "));
        }
    }
    out
}

/// `search --json`: schema `trailtracker.search/v1` — see `capabilities`.
fn search_json(query: &str, dir: &str, results: &[trailtracker::search::SearchResult]) -> Json {
    let items: Vec<Json> = results
        .iter()
        .enumerate()
        .map(|(i, r)| {
            Json::obj([
                ("rank", (i + 1).into()),
                ("id", Json::str(r.id.as_str())),
                ("name", Json::str(r.name.as_str())),
                ("kind", Json::str(r.kind)),
                ("path", Json::str(r.path.as_str())),
                ("score", Json::F64(r.score)),
                (
                    "why",
                    Json::Array(r.why.iter().map(|w| Json::str(w.as_str())).collect()),
                ),
            ])
        })
        .collect();
    Json::obj([
        ("schema", Json::str("trailtracker.search/v1")),
        ("command", Json::str("search")),
        ("query", Json::str(query)),
        ("dir", Json::str(dir)),
        ("total", results.len().into()),
        ("results", Json::Array(items)),
    ])
}

/// `nav <pack|expand>` — the context-efficient codebase navigator
/// (ADR-0004): exact, deterministic, character-budgeted subgraphs for
/// agents. No LLM, no tokenizer — budgets are exact char counts over the
/// JSON serialization.
fn cmd_nav(rest: &[String]) -> Result<(), CliError> {
    const USAGE_PACK: &str = "trailtracker nav pack \"<task query>\" [DIR] [--budget CHARS] \
                              [--format json|text|prose] [--json]";
    const USAGE_EXPAND: &str = "trailtracker nav expand <id-or-path-or-name> [DIR] \
                                [--depth K] [--direction callers|callees|both] \
                                [--budget CHARS] [--cursor N] \
                                [--format json|text|prose] [--json]";
    let sub = rest.first().map(String::as_str).ok_or_else(|| {
        unknown_value_error("nav subcommand", "(none)", &["pack", "expand"])
            .fix(format!("usage: {USAGE_PACK}\n       {USAGE_EXPAND}"))
    })?;
    let rest = rest.get(1..).unwrap_or(&[]);

    // Shared numeric flag parser.
    let parse_num = |flag: &str, raw: &str, usage: &str| -> Result<usize, CliError> {
        raw.parse::<usize>().map_err(|_| {
            CliError::usage(format!(
                "{flag} must be a non-negative integer, got '{raw}'"
            ))
            .fix(format!("usage: {usage}"))
        })
    };

    match sub {
        "pack" => {
            let mut budget = trailtracker::nav::DEFAULT_BUDGET;
            let mut format = trailtracker::nav::PackFormat::Text;
            let mut incremental = false;
            let mut no_ignore = false;
            let mut pos: Vec<&str> = Vec::new();
            let mut i = 0;
            while i < rest.len() {
                let arg = rest[i].as_str();
                if arg == "--budget" {
                    i += 1;
                    let raw = rest.get(i).ok_or_else(|| {
                        CliError::usage(
                            "--budget requires a character count (proxy for the consuming \
                             agent's context window)",
                        )
                        .fix(format!("usage: {USAGE_PACK}"))
                    })?;
                    budget = parse_num("--budget", raw, USAGE_PACK)?;
                } else if let Some(v) = arg.strip_prefix("--budget=") {
                    budget = parse_num("--budget", v, USAGE_PACK)?;
                } else if arg == "--format" || arg.starts_with("--format=") {
                    let raw = match arg.strip_prefix("--format=") {
                        Some(v) => v.to_string(),
                        None => {
                            i += 1;
                            rest.get(i).cloned().ok_or_else(|| {
                                CliError::usage("--format requires a value")
                                    .fix(format!("usage: {USAGE_PACK}"))
                            })?
                        }
                    };
                    format = trailtracker::nav::PackFormat::parse(&raw).ok_or_else(|| {
                        unknown_value_error("format", &raw, trailtracker::nav::PackFormat::NAMES)
                            .fix(format!("usage: {USAGE_PACK}"))
                    })?;
                } else if arg == "--json" || arg == "--robot" {
                    format = trailtracker::nav::PackFormat::Json;
                } else if arg == "--incremental" {
                    incremental = true;
                } else if arg == "--no-ignore" {
                    no_ignore = true;
                } else if arg.starts_with('-') {
                    let known = [
                        "--budget",
                        "--format",
                        "--json",
                        "--robot",
                        "--incremental",
                        "--no-ignore",
                    ];
                    let fix = match closest(arg, &known) {
                        Some(k) => format!("did you mean `{k}`?"),
                        None => format!("usage: {USAGE_PACK}"),
                    };
                    return Err(
                        CliError::usage(format!("unknown flag '{arg}' for `nav pack`")).fix(fix),
                    );
                } else {
                    pos.push(arg);
                }
                i += 1;
            }
            let parsed = CmdArgs {
                pos,
                json: format == trailtracker::nav::PackFormat::Json,
                incremental,
                no_ignore,
            };
            expect_at_most("nav pack", USAGE_PACK, &parsed, 2)?;
            let query = parsed.pos.first().copied().unwrap_or("");
            if query.trim().is_empty() {
                return Err(
                    CliError::usage("nav pack requires a non-empty <task query>").fix(format!(
                        "describe the task, e.g. `trailtracker nav pack \"where is playback \
                         session state managed\" .` — usage: {USAGE_PACK}"
                    )),
                );
            }
            let dir = parsed.pos.get(1).copied().unwrap_or(".");
            let graph = load_graph(dir, parsed.incremental, parsed.no_ignore)?;
            let out = trailtracker::nav::nav_pack(&graph, query, dir, budget, format);
            write_stdout(out.as_bytes(), "nav pack")
        }
        "expand" => {
            let mut budget = trailtracker::nav::DEFAULT_BUDGET;
            let mut depth: usize = trailtracker::nav::DEFAULT_DEPTH as usize;
            let mut cursor: usize = 0;
            let mut direction = trailtracker::nav::Direction::Both;
            let mut format = trailtracker::nav::PackFormat::Text;
            let mut incremental = false;
            let mut no_ignore = false;
            let mut pos: Vec<&str> = Vec::new();
            let mut i = 0;
            while i < rest.len() {
                let arg = rest[i].as_str();
                let mut take_value = |flag: &'static str| -> Result<String, CliError> {
                    i += 1;
                    rest.get(i).cloned().ok_or_else(|| {
                        CliError::usage(format!("{flag} requires a value"))
                            .fix(format!("usage: {USAGE_EXPAND}"))
                    })
                };
                if arg == "--budget" {
                    budget = parse_num("--budget", &take_value("--budget")?, USAGE_EXPAND)?;
                } else if let Some(v) = arg.strip_prefix("--budget=") {
                    budget = parse_num("--budget", v, USAGE_EXPAND)?;
                } else if arg == "--depth" {
                    depth = parse_num("--depth", &take_value("--depth")?, USAGE_EXPAND)?;
                } else if let Some(v) = arg.strip_prefix("--depth=") {
                    depth = parse_num("--depth", v, USAGE_EXPAND)?;
                } else if arg == "--cursor" {
                    cursor = parse_num("--cursor", &take_value("--cursor")?, USAGE_EXPAND)?;
                } else if let Some(v) = arg.strip_prefix("--cursor=") {
                    cursor = parse_num("--cursor", v, USAGE_EXPAND)?;
                } else if arg == "--direction" || arg.starts_with("--direction=") {
                    let raw = match arg.strip_prefix("--direction=") {
                        Some(v) => v.to_string(),
                        None => take_value("--direction")?,
                    };
                    direction = trailtracker::nav::Direction::parse(&raw).ok_or_else(|| {
                        unknown_value_error("direction", &raw, &["callers", "callees", "both"])
                            .fix(format!("usage: {USAGE_EXPAND}"))
                    })?;
                } else if arg == "--format" || arg.starts_with("--format=") {
                    let raw = match arg.strip_prefix("--format=") {
                        Some(v) => v.to_string(),
                        None => take_value("--format")?,
                    };
                    format = trailtracker::nav::PackFormat::parse(&raw).ok_or_else(|| {
                        unknown_value_error("format", &raw, trailtracker::nav::PackFormat::NAMES)
                            .fix(format!("usage: {USAGE_EXPAND}"))
                    })?;
                } else if arg == "--json" || arg == "--robot" {
                    format = trailtracker::nav::PackFormat::Json;
                } else if arg == "--incremental" {
                    incremental = true;
                } else if arg == "--no-ignore" {
                    no_ignore = true;
                } else if arg.starts_with('-') {
                    let known = [
                        "--budget",
                        "--depth",
                        "--direction",
                        "--cursor",
                        "--format",
                        "--json",
                        "--robot",
                        "--incremental",
                        "--no-ignore",
                    ];
                    let fix = match closest(arg, &known) {
                        Some(k) => format!("did you mean `{k}`?"),
                        None => format!("usage: {USAGE_EXPAND}"),
                    };
                    return Err(
                        CliError::usage(format!("unknown flag '{arg}' for `nav expand`")).fix(fix),
                    );
                } else {
                    pos.push(arg);
                }
                i += 1;
            }
            let parsed = CmdArgs {
                pos,
                json: format == trailtracker::nav::PackFormat::Json,
                incremental,
                no_ignore,
            };
            expect_at_most("nav expand", USAGE_EXPAND, &parsed, 2)?;
            let target = parsed.pos.first().copied().unwrap_or("");
            if target.trim().is_empty() {
                return Err(CliError::usage(
                    "nav expand requires a <target>: a node id, file path, or symbol name",
                )
                .fix(format!(
                    "find targets with `trailtracker search \"<words>\" DIR` or `trailtracker \
                     nav pack \"<task>\" DIR`. Usage: {USAGE_EXPAND}"
                )));
            }
            let depth = u32::try_from(depth).map_err(|_| {
                CliError::usage(format!("--depth {depth} is out of range"))
                    .fix("use a small depth (1-8); the neighborhood grows exponentially.")
            })?;
            let dir = parsed.pos.get(1).copied().unwrap_or(".");
            let graph = load_graph(dir, parsed.incremental, parsed.no_ignore)?;
            let out = trailtracker::nav::nav_expand(
                &graph, target, dir, depth, direction, budget, cursor, format,
            )
            .map_err(|e| explain_error(e, dir, "nav expand"))?;
            write_stdout(out.as_bytes(), "nav expand")
        }
        other => {
            let err = unknown_value_error("nav subcommand", other, &["pack", "expand"]);
            Err(match closest(other, &["pack", "expand"]) {
                Some(c) => err.fix(format!("did you mean `trailtracker nav {c}`?")),
                None => err.fix(format!("usage: {USAGE_PACK}")),
            })
        }
    }
}

/// `report [DIR]` — a deterministic markdown org summary. `--json` wraps the
/// markdown in a `trailtracker.markdown/v1` envelope.
///
/// `report --full <DIR> [-o PATH] [--format md|html|both] [--examples N]
/// [--budget N]` — the full evidence report (R3): exec summary (verbalizer
/// prose), domains table, change-risk centers with named callers, every
/// layer-violating edge at symbol grain (inheritance included), structural
/// findings, and a domains-only coupling appendix. `--format both` writes
/// `PATH.md` + `PATH.html` (requires `-o`); without `-o` the chosen format
/// streams to stdout.
fn cmd_report(rest: &[String]) -> Result<(), CliError> {
    if rest.iter().any(|a| a == "--full") {
        return cmd_report_full(rest);
    }
    let parsed = split_args("report", rest)?;
    expect_at_most("report", "trailtracker report [DIR] [--json]", &parsed, 1)?;
    let dir = parsed.pos.first().copied().unwrap_or(".");
    let graph = load_graph(dir, parsed.incremental, parsed.no_ignore)?;
    let md = trailtracker::report::report(&graph);
    if parsed.json {
        return println_stdout(&markdown_envelope("report", dir, &md).to_line(), "report");
    }
    write_stdout(md.as_bytes(), "report")
}

/// The `report --full` surface. Deterministic MD/HTML; file outputs print
/// only the written paths (the dossier convention).
fn cmd_report_full(rest: &[String]) -> Result<(), CliError> {
    const USAGE: &str = "trailtracker report --full <DIR> [-o PATH] [--format md|html|both] \
                         [--examples N] [--budget N] [--json]";
    use trailtracker::report_full::{report_full_html, report_full_markdown, ReportOptions};

    let mut out_path: Option<String> = None;
    let mut format = "md".to_string();
    let mut examples: Option<usize> = None;
    let mut budget: Option<usize> = None;
    let mut json = false;
    let mut incremental = false;
    let mut no_ignore = false;
    let mut pos: Vec<&str> = Vec::new();
    let parse_n = |flag: &str, v: &str| -> Result<usize, CliError> {
        v.parse::<usize>().map_err(|_| {
            CliError::usage(format!("{flag} expects a non-negative integer, got '{v}'"))
                .fix(format!("usage: {USAGE}"))
        })
    };
    let value_of = |rest: &[String], i: &mut usize, flag: &str| -> Result<String, CliError> {
        *i += 1;
        rest.get(*i).cloned().ok_or_else(|| {
            CliError::usage(format!("{flag} requires a value")).fix(format!("usage: {USAGE}"))
        })
    };
    let mut i = 0;
    while i < rest.len() {
        let arg = rest[i].as_str();
        if arg == "--full" {
            // The dispatch marker itself.
        } else if arg == "-o" || arg == "--out" {
            out_path = Some(value_of(rest, &mut i, arg)?);
        } else if let Some(v) = arg.strip_prefix("--out=") {
            out_path = Some(v.to_string());
        } else if arg == "--format" {
            format = value_of(rest, &mut i, "--format")?;
        } else if let Some(v) = arg.strip_prefix("--format=") {
            format = v.to_string();
        } else if arg == "--examples" {
            examples = Some(parse_n(
                "--examples",
                &value_of(rest, &mut i, "--examples")?,
            )?);
        } else if let Some(v) = arg.strip_prefix("--examples=") {
            examples = Some(parse_n("--examples", v)?);
        } else if arg == "--budget" {
            budget = Some(parse_n("--budget", &value_of(rest, &mut i, "--budget")?)?);
        } else if let Some(v) = arg.strip_prefix("--budget=") {
            budget = Some(parse_n("--budget", v)?);
        } else if arg == "--json" || arg == "--robot" {
            json = true;
        } else if arg == "--incremental" {
            incremental = true;
        } else if arg == "--no-ignore" {
            no_ignore = true;
        } else if arg.starts_with('-') {
            let known = [
                "--full",
                "-o",
                "--out",
                "--format",
                "--examples",
                "--budget",
                "--json",
                "--incremental",
                "--no-ignore",
            ];
            let fix = match closest(arg, &known) {
                Some(k) => format!("did you mean `{k}`?"),
                None => format!("usage: {USAGE}"),
            };
            return Err(
                CliError::usage(format!("unknown flag '{arg}' for `report --full`")).fix(fix),
            );
        } else {
            pos.push(arg);
        }
        i += 1;
    }
    if pos.len() > 1 {
        return Err(
            CliError::usage(format!("report --full takes one DIR, got {}", pos.len()))
                .fix(format!("usage: {USAGE}")),
        );
    }
    let dir = pos.first().copied().ok_or_else(|| {
        CliError::usage("report --full requires a DIR to analyze").fix(format!(
            "example: `trailtracker report --full . -o report --format both` — usage: {USAGE}"
        ))
    })?;
    if !matches!(format.as_str(), "md" | "html" | "both") {
        let err = unknown_value_error("--format", &format, &["md", "html", "both"]);
        return Err(match closest(&format, &["md", "html", "both"]) {
            Some(c) => err.fix(format!("did you mean `--format {c}`?")),
            None => err.fix(format!("usage: {USAGE}")),
        });
    }
    if format == "both" && out_path.is_none() {
        return Err(
            CliError::usage("--format both writes two files and needs -o PATH")
                .fix(format!("usage: {USAGE}")),
        );
    }

    let analysis = analyze(dir, incremental, no_ignore)?;
    let opts = ReportOptions { examples, budget };

    // File outputs: `-o report` (or `report.md`/`report.html`) writes the
    // extension-appropriate file(s) and prints only the written paths.
    if let Some(out) = out_path {
        let base = out
            .strip_suffix(".md")
            .or_else(|| out.strip_suffix(".html"))
            .unwrap_or(&out);
        let mut written: Vec<String> = Vec::new();
        if format == "md" || format == "both" {
            let path = format!("{base}.md");
            fs::write(&path, report_full_markdown(&analysis, dir, &opts)).map_err(|e| {
                CliError::analysis(format!("failed to write {path}: {e}"))
                    .fix("pass a writable output path with -o.")
            })?;
            written.push(path);
        }
        if format == "html" || format == "both" {
            let path = format!("{base}.html");
            fs::write(&path, report_full_html(&analysis, dir, &opts)).map_err(|e| {
                CliError::analysis(format!("failed to write {path}: {e}"))
                    .fix("pass a writable output path with -o.")
            })?;
            written.push(path);
        }
        for path in &written {
            println_stdout(path, "report path")?;
        }
        return Ok(());
    }

    // Stream to stdout (single format only; `both` was rejected above).
    let text = if format == "html" {
        report_full_html(&analysis, dir, &opts)
    } else {
        report_full_markdown(&analysis, dir, &opts)
    };
    if json {
        return println_stdout(
            &markdown_envelope("report-full", dir, &text).to_line(),
            "report",
        );
    }
    write_stdout(text.as_bytes(), "report")
}

/// `brief [DIR]` — a deterministic markdown codebase model for an unfamiliar
/// repo: overview, architecture, entry points, hotspots, dependency cycles,
/// and a plain-English synthesis. `--json` emits the structured brief object
/// (schema `trailtracker.brief/v1`).
fn cmd_brief(rest: &[String]) -> Result<(), CliError> {
    let parsed = split_args("brief", rest)?;
    expect_at_most("brief", "trailtracker brief [DIR] [--json]", &parsed, 1)?;
    let dir = parsed.pos.first().copied().unwrap_or(".");
    let graph = load_graph(dir, parsed.incremental, parsed.no_ignore)?;
    if parsed.json {
        return println_stdout(
            &trailtracker::brief::brief_json(&graph, dir).to_line(),
            "brief",
        );
    }
    let md = trailtracker::brief::brief(&graph, dir);
    write_stdout(md.as_bytes(), "brief")
}

/// `rebuild-brief <flow-name-or-id> [DIR]` — a single self-contained markdown
/// document for one workflow: scoped data model, ordered steps with full logic +
/// line cites, inlined called code, and a Medplum target scaffold. `--json`
/// wraps the markdown in a `trailtracker.markdown/v1` envelope.
fn cmd_rebuild_brief(rest: &[String]) -> Result<(), CliError> {
    let parsed = split_args("rebuild-brief", rest)?;
    expect_at_most(
        "rebuild-brief",
        "trailtracker rebuild-brief <flow-name-or-id> [DIR] [--json]",
        &parsed,
        2,
    )?;
    let target = parsed.pos.first().copied().ok_or_else(|| {
        CliError::usage("rebuild-brief requires a <flow-name-or-id>").fix(
            "list flows with `trailtracker extract workflow-spec DIR`, then \
             `trailtracker rebuild-brief <flow> DIR` (e.g. `rebuild-brief DeepIntake \
             eval/corpus/sforg`).",
        )
    })?;
    let dir = parsed.pos.get(1).copied().unwrap_or(".");
    let graph = load_graph(dir, parsed.incremental, parsed.no_ignore)?;
    let md =
        trailtracker::report_brief::rebuild_brief(&graph, Path::new(dir), target).map_err(|e| {
            CliError::usage(e)
                .fix("list available flows with `trailtracker extract workflow-spec DIR`.")
        })?;
    if parsed.json {
        return println_stdout(
            &markdown_envelope("rebuild-brief", dir, &md).to_line(),
            "rebuild brief",
        );
    }
    write_stdout(md.as_bytes(), "rebuild brief")
}

fn cmd_parse(rest: &[String]) -> Result<(), CliError> {
    let parsed = split_args("parse", rest)?;
    expect_at_most("parse", "trailtracker parse FILE", &parsed, 1)?;
    // `--json` is accepted as a no-op: the output is already JSON.
    let file = parsed.pos.first().copied().ok_or_else(|| {
        CliError::usage("parse requires a FILE argument")
            .fix("pass one Rust source file, e.g. `trailtracker parse src/main.rs`.")
    })?;
    let source = fs::read_to_string(file).map_err(|e| {
        CliError::not_found(format!("failed to read {file}: {e}"))
            .fix("pass a readable file path (paths resolve against the current working directory).")
    })?;
    let tree = parse(file, &source);
    if !tree.is_lossless() {
        return Err(CliError::analysis(format!(
            "internal invariant violated: CST for {file} did not reconstruct source"
        )));
    }
    println_stdout(&tree.to_json().to_line(), "CST")
}

// ---------------------------------------------------------------------------
// rewrite (ADR-0006): propose-then-approve span rewrites
// ---------------------------------------------------------------------------

const USAGE_REWRITE: &str = "trailtracker rewrite propose <rule> <FILE> [DIR] [--lines A-B] \
     [--name NAME] [-o proposal.json] [--json] | trailtracker rewrite verify --proposal \
     proposal.json [DIR] [-o cert.json] [--json] | trailtracker rewrite apply --proposal \
     proposal.json [DIR] [--require-cert] [--json] | trailtracker rewrite rules [--json]";

/// `rewrite` — the first code-MODIFYING capability (ADR-0006), governed by the
/// propose-then-approve contract: `propose` analyzes and NEVER writes source;
/// `apply` is the only writing path and refuses tampered (hash) or stale
/// (fingerprint) proposals. No flag combination skips the two-step.
fn cmd_rewrite(rest: &[String]) -> Result<(), CliError> {
    const SUBS: &[&str] = &["propose", "verify", "apply", "rules"];
    match rest.first().map(String::as_str) {
        Some("propose") => cmd_rewrite_propose(&rest[1..]),
        Some("verify") => cmd_rewrite_verify(&rest[1..]),
        Some("apply") => cmd_rewrite_apply(&rest[1..]),
        Some("rules") => cmd_rewrite_rules(&rest[1..]),
        Some(other) => {
            let err = unknown_value_error("rewrite subcommand", other, SUBS);
            Err(match closest(other, SUBS) {
                Some(c) => err.fix(format!("did you mean `trailtracker rewrite {c}`?")),
                None => err.fix(format!("usage: {USAGE_REWRITE}")),
            })
        }
        None => Err(CliError::usage(
            "rewrite requires a subcommand (propose, verify, apply, rules)",
        )
        .fix(format!("usage: {USAGE_REWRITE}"))),
    }
}

/// `rewrite rules [--json]` — the rule vocabulary: ids, versions, and the
/// exact recognized shapes, so agents discover the grammar without trying
/// commands.
fn cmd_rewrite_rules(rest: &[String]) -> Result<(), CliError> {
    let parsed = split_args("rewrite rules", rest)?;
    expect_at_most(
        "rewrite rules",
        "trailtracker rewrite rules [--json]",
        &parsed,
        0,
    )?;
    let rules = trailtracker::rewrite::rules::all_rules();
    if parsed.json {
        let items: Vec<Json> = rules
            .iter()
            .map(|r| {
                Json::obj([
                    ("id", Json::str(r.id())),
                    ("version", Json::str(r.version())),
                    ("summary", Json::str(r.summary())),
                    ("requires_lines", Json::Bool(r.requires_lines())),
                    (
                        "shapes",
                        Json::Array(r.shapes().iter().map(|s| Json::str(*s)).collect()),
                    ),
                ])
            })
            .collect();
        let doc = Json::obj([
            ("schema", Json::str("trailtracker.rewrite-rules/v1")),
            ("rules", Json::Array(items)),
        ]);
        return println_stdout(&doc.to_line(), "rewrite rules");
    }
    let mut out = String::new();
    for r in &rules {
        out.push_str(&format!(
            "{} v{}\n    {}\n",
            r.id(),
            r.version(),
            r.summary()
        ));
        if r.requires_lines() {
            out.push_str("    requires: --lines A-B (1-based, inclusive)\n");
        }
        out.push_str("    shapes:\n");
        for s in r.shapes() {
            out.push_str(&format!("        {s}\n"));
        }
    }
    write_stdout(out.as_bytes(), "rewrite rules")
}

/// `rewrite propose <rule> <FILE> [DIR]` — analyze and emit a unified diff on
/// stdout (the human review surface) plus a `trailtracker.rewrite-proposal/v1`
/// document (`-o` writes it; `--json` puts it on stdout instead of the diff).
/// NEVER writes source; there is no `--apply` flag here and there never will
/// be (ADR-0006).
fn cmd_rewrite_propose(rest: &[String]) -> Result<(), CliError> {
    let mut lines: Option<(usize, usize)> = None;
    let mut name: Option<String> = None;
    let mut out_path: Option<String> = None;
    let mut json = false;
    let mut pos: Vec<&str> = Vec::new();
    let mut i = 0;
    let parse_lines = |raw: &str| -> Result<(usize, usize), CliError> {
        let bad = || {
            CliError::usage(format!("--lines '{raw}' is not A-B (1-based, inclusive)"))
                .fix("example: `--lines 12-20` — usage: trailtracker rewrite propose <rule> <FILE> [DIR] --lines A-B")
        };
        let (a, b) = raw.split_once('-').ok_or_else(bad)?;
        let a: usize = a.trim().parse().map_err(|_| bad())?;
        let b: usize = b.trim().parse().map_err(|_| bad())?;
        if a == 0 || b < a {
            return Err(bad());
        }
        Ok((a, b))
    };
    while i < rest.len() {
        let arg = rest[i].as_str();
        if arg == "--lines" {
            i += 1;
            let raw = rest.get(i).ok_or_else(|| {
                CliError::usage("--lines requires a value A-B")
                    .fix(format!("usage: {USAGE_REWRITE}"))
            })?;
            lines = Some(parse_lines(raw)?);
        } else if let Some(v) = arg.strip_prefix("--lines=") {
            lines = Some(parse_lines(v)?);
        } else if arg == "--name" {
            i += 1;
            name = Some(rest.get(i).cloned().ok_or_else(|| {
                CliError::usage("--name requires a NAME").fix(format!("usage: {USAGE_REWRITE}"))
            })?);
        } else if let Some(v) = arg.strip_prefix("--name=") {
            name = Some(v.to_string());
        } else if arg == "-o" || arg == "--out" {
            i += 1;
            out_path = Some(rest.get(i).cloned().ok_or_else(|| {
                CliError::usage(format!("{arg} requires a PATH"))
                    .fix(format!("usage: {USAGE_REWRITE}"))
            })?);
        } else if let Some(v) = arg.strip_prefix("--out=") {
            out_path = Some(v.to_string());
        } else if arg == "--json" || arg == "--robot" {
            json = true;
        } else if arg.starts_with('-') {
            let known = ["--lines", "--name", "-o", "--out", "--json", "--robot"];
            let fix = match closest(arg, &known) {
                Some(k) => format!("did you mean `{k}`?"),
                None => format!("usage: {USAGE_REWRITE}"),
            };
            return Err(
                CliError::usage(format!("unknown flag '{arg}' for `rewrite propose`")).fix(fix),
            );
        } else {
            pos.push(arg);
        }
        i += 1;
    }
    if pos.len() < 2 {
        return Err(CliError::usage(
            "rewrite propose requires a <rule> and a <FILE> (run `trailtracker rewrite rules` \
             for the rule vocabulary)",
        )
        .fix(format!("usage: {USAGE_REWRITE}")));
    }
    if pos.len() > 3 {
        return Err(CliError::usage(format!(
            "`rewrite propose` takes at most 3 positional arguments, got {}: {}",
            pos.len(),
            pos.join(" ")
        ))
        .fix(format!("usage: {USAGE_REWRITE}")));
    }
    let (rule_id, file, dir) = (pos[0], pos[1], pos.get(2).copied().unwrap_or("."));

    let rule_ids: Vec<&'static str> = trailtracker::rewrite::rules::all_rules()
        .iter()
        .map(|r| r.id())
        .collect();
    let Some(rule) = trailtracker::rewrite::rules::rule_by_id(rule_id) else {
        let err = unknown_value_error("rewrite rule", rule_id, &rule_ids);
        return Err(match closest(rule_id, &rule_ids) {
            Some(c) => err.fix(format!("did you mean `{c}`?")),
            None => err.fix("run `trailtracker rewrite rules` for the rule vocabulary."),
        });
    };

    let (target, source) = read_rewrite_target(dir, file)?;
    let tree = parse(file, &source);
    if !tree.is_lossless() {
        return Err(CliError::analysis(format!(
            "internal invariant violated: CST for {} did not reconstruct source",
            target.display()
        )));
    }
    if !tree.diagnostics.is_empty() {
        return Err(CliError::analysis(format!(
            "{} has {} parse diagnostic(s); refusing to rewrite a file that did not parse \
             cleanly",
            target.display(),
            tree.diagnostics.len()
        ))
        .fix(format!(
            "inspect with `trailtracker parse {}` and fix the parse issues first.",
            target.display()
        )));
    }
    let ctx = trailtracker::rewrite::rules::analyze_file(&tree);
    let opts = trailtracker::rewrite::rules::RuleOptions { lines, name };
    let outcome = rule
        .propose(&ctx, &opts)
        .map_err(|e| CliError::usage(e).fix(format!("usage: {USAGE_REWRITE}")))?;

    let proposal = trailtracker::rewrite::proposal::Proposal {
        rule_id: rule.id().to_string(),
        rule_version: rule.version().to_string(),
        dir: dir.to_string(),
        file: file.to_string(),
        file_fingerprint: trailtracker::rewrite::proposal::fingerprint(source.as_bytes()),
        edits: outcome.edits,
        rejections: outcome.rejections,
    };

    // Diagnostics: every refusal is reported, never silent (stderr).
    {
        let stderr = io::stderr();
        let mut h = stderr.lock();
        for r in &proposal.rejections {
            let _ = writeln!(
                h,
                "rewrite: rejected bytes {}..{}: {} — {}",
                r.span.start, r.span.end, r.reason, r.detail
            );
        }
        if proposal.edits.is_empty() {
            let _ = writeln!(
                h,
                "rewrite: no sites recognized by {} v{} in {} ({} rejection(s))",
                proposal.rule_id,
                proposal.rule_version,
                target.display(),
                proposal.rejections.len()
            );
        }
    }

    // Certification (ADR-0007): every non-empty proposal this binary emits
    // must carry a verifiable equivalence certificate. A proposal we cannot
    // certify is a bug — fail loudly instead of shipping it.
    let cert = if proposal.edits.is_empty() {
        None
    } else {
        let cert = trailtracker::rewrite::cert::certify(&source, &proposal).map_err(|e| {
            CliError::analysis(format!("refusing to emit an uncertifiable proposal — {e}"))
                .fix("this is a rule/verifier disagreement; please report it with the target file.")
        })?;
        Some(cert)
    };

    let doc_line = proposal.to_json().to_line();
    if let Some(out) = &out_path {
        fs::write(out, format!("{doc_line}\n"))
            .map_err(|e| CliError::analysis(format!("failed to write proposal to {out}: {e}")))?;
        let stderr = io::stderr();
        let _ = writeln!(stderr.lock(), "rewrite: proposal written to {out}");
        if let Some(cert) = &cert {
            let cpath = rewrite_cert_path(out);
            let cert_line = cert.to_json().to_line();
            fs::write(&cpath, format!("{cert_line}\n")).map_err(|e| {
                CliError::analysis(format!("failed to write certificate to {cpath}: {e}"))
            })?;
            let _ = writeln!(
                io::stderr().lock(),
                "rewrite: certificate written to {cpath} ({})",
                cert.hash()
            );
        }
    } else if let Some(cert) = &cert {
        let _ = writeln!(
            io::stderr().lock(),
            "rewrite: certified ({} check(s), {})",
            cert.checks.len(),
            cert.hash()
        );
    }
    if json {
        println_stdout(&doc_line, "rewrite proposal")
    } else {
        let diff =
            trailtracker::rewrite::proposal::unified_diff(file, &source, &proposal.span_edits());
        write_stdout(diff.as_bytes(), "rewrite diff")
    }
}

/// The certificate path beside a proposal path: `p.json` → `p.cert.json`.
fn rewrite_cert_path(proposal_path: &str) -> String {
    match proposal_path.strip_suffix(".json") {
        Some(stem) => format!("{stem}.cert.json"),
        None => format!("{proposal_path}.cert.json"),
    }
}

/// `rewrite verify --proposal p.json [DIR] [-o cert.json] [--json]` — the
/// independent checker (ADR-0007): reads ONLY the original file and the
/// proposal, trusts nothing cached (not even a previously written
/// certificate), recomputes the before/after CPGs, verifies the rule's
/// licensed remapping, and replays the licensed emission. Exit 0 = verified;
/// exit 4 names the exact failed check.
fn cmd_rewrite_verify(rest: &[String]) -> Result<(), CliError> {
    let mut proposal_path: Option<String> = None;
    let mut out_path: Option<String> = None;
    let mut json = false;
    let mut pos: Vec<&str> = Vec::new();
    let mut i = 0;
    while i < rest.len() {
        let arg = rest[i].as_str();
        if arg == "--proposal" {
            i += 1;
            proposal_path = Some(rest.get(i).cloned().ok_or_else(|| {
                CliError::usage("--proposal requires a FILE (the output of `rewrite propose -o`)")
                    .fix(format!("usage: {USAGE_REWRITE}"))
            })?);
        } else if let Some(v) = arg.strip_prefix("--proposal=") {
            proposal_path = Some(v.to_string());
        } else if arg == "-o" || arg == "--out" {
            i += 1;
            out_path = Some(rest.get(i).cloned().ok_or_else(|| {
                CliError::usage(format!("{arg} requires a PATH"))
                    .fix(format!("usage: {USAGE_REWRITE}"))
            })?);
        } else if let Some(v) = arg.strip_prefix("--out=") {
            out_path = Some(v.to_string());
        } else if arg == "--json" || arg == "--robot" {
            json = true;
        } else if arg.starts_with('-') {
            let known = ["--proposal", "-o", "--out", "--json", "--robot"];
            let fix = match closest(arg, &known) {
                Some(k) => format!("did you mean `{k}`?"),
                None => format!("usage: {USAGE_REWRITE}"),
            };
            return Err(
                CliError::usage(format!("unknown flag '{arg}' for `rewrite verify`")).fix(fix),
            );
        } else {
            pos.push(arg);
        }
        i += 1;
    }
    let Some(proposal_path) = proposal_path else {
        return Err(
            CliError::usage("rewrite verify requires --proposal FILE").fix(format!(
                "generate one with `trailtracker rewrite propose <rule> <FILE> -o \
                 proposal.json` — usage: {USAGE_REWRITE}"
            )),
        );
    };
    if pos.len() > 1 {
        return Err(CliError::usage(format!(
            "`rewrite verify` takes at most 1 positional argument (DIR), got {}: {}",
            pos.len(),
            pos.join(" ")
        ))
        .fix(format!("usage: {USAGE_REWRITE}")));
    }

    let text = fs::read_to_string(&proposal_path).map_err(|e| {
        CliError::not_found(format!("failed to read proposal {proposal_path}: {e}"))
            .fix("pass the path `rewrite propose -o` wrote.")
    })?;
    let proposal = trailtracker::rewrite::proposal::Proposal::parse(&text).map_err(|e| {
        CliError::analysis(format!("proposal {proposal_path} does not verify: {e}")).fix(
            "re-run `trailtracker rewrite propose` to generate a fresh proposal; \
                 hand-edited or stale proposals are never certified.",
        )
    })?;
    let dir = pos.first().copied().unwrap_or(proposal.dir.as_str());
    let (target, current) = read_rewrite_target(dir, &proposal.file)?;

    let cert = trailtracker::rewrite::cert::certify(&current, &proposal).map_err(|e| {
        CliError::analysis(format!(
            "equivalence verification FAILED for {}: {e}",
            target.display()
        ))
        .fix(format!(
            "the proposal is not a certified-safe application of {} v{}; re-run \
             `trailtracker rewrite propose` and review a fresh proposal.",
            proposal.rule_id, proposal.rule_version
        ))
    })?;

    let cert_line = cert.to_json().to_line();
    if let Some(out) = &out_path {
        fs::write(out, format!("{cert_line}\n")).map_err(|e| {
            CliError::analysis(format!("failed to write certificate to {out}: {e}"))
        })?;
        let _ = writeln!(io::stderr().lock(), "rewrite: certificate written to {out}");
    }
    if json {
        return println_stdout(&cert_line, "rewrite cert");
    }
    let mut out = String::new();
    out.push_str(&format!(
        "VERIFIED {} v{} on {} ({} edit(s))\n",
        cert.rule_id,
        cert.rule_version,
        target.display(),
        proposal.edits.len()
    ));
    out.push_str(&format!(
        "  proposal    {}\n  before      {}\n  after       {}\n  cpg before  {}\n  cpg after   {}\n",
        cert.proposal_hash,
        cert.before_fingerprint,
        cert.after_fingerprint,
        cert.before_cpg_hash,
        cert.after_cpg_hash
    ));
    out.push_str(&format!(
        "  obligation  {} ({})\n",
        cert.obligation_ref, cert.obligation_kani
    ));
    out.push_str(&format!(
        "  functions   {} affected, {} unaffected re-verified\n",
        cert.affected.len(),
        cert.unaffected_verified
    ));
    for c in &cert.checks {
        out.push_str(&format!("  check       {c}\n"));
    }
    out.push_str(&format!(
        "  assumptions {} (see certificate document)\n  cert        {}\n",
        trailtracker::rewrite::cert::ASSUMPTIONS.len(),
        cert.hash()
    ));
    write_stdout(out.as_bytes(), "rewrite verify")
}

/// `rewrite apply --proposal p.json [DIR]` — the ONLY writing path (ADR-0006),
/// and it refuses unless the proposal hash verifies, the target file's current
/// fingerprint matches, and every edit's `before` matches the bytes at its
/// span. Atomic span-only write. No `--force`, no `--skip-verify`. Since K3d
/// the full equivalence verification (ADR-0007) also runs unconditionally:
/// `--require-cert` is the default, kept as an accepted no-op, no opt-out.
fn cmd_rewrite_apply(rest: &[String]) -> Result<(), CliError> {
    let mut proposal_path: Option<String> = None;
    let mut json = false;
    // ADR-0007's stated end state, made real in K3d: apply ALWAYS certifies.
    // `--require-cert` stays accepted (re-asserts the default) so existing
    // scripts keep working; there is deliberately no `--no-cert`.
    let mut require_cert = true;
    let mut pos: Vec<&str> = Vec::new();
    let mut i = 0;
    while i < rest.len() {
        let arg = rest[i].as_str();
        if arg == "--proposal" {
            i += 1;
            proposal_path = Some(rest.get(i).cloned().ok_or_else(|| {
                CliError::usage("--proposal requires a FILE (the output of `rewrite propose -o`)")
                    .fix(format!("usage: {USAGE_REWRITE}"))
            })?);
        } else if let Some(v) = arg.strip_prefix("--proposal=") {
            proposal_path = Some(v.to_string());
        } else if arg == "--require-cert" {
            require_cert = true;
        } else if arg == "--json" || arg == "--robot" {
            json = true;
        } else if arg.starts_with('-') {
            let known = ["--proposal", "--require-cert", "--json", "--robot"];
            let fix = match closest(arg, &known) {
                Some(k) => format!("did you mean `{k}`?"),
                None => format!("usage: {USAGE_REWRITE}"),
            };
            return Err(
                CliError::usage(format!("unknown flag '{arg}' for `rewrite apply`")).fix(fix),
            );
        } else {
            pos.push(arg);
        }
        i += 1;
    }
    let Some(proposal_path) = proposal_path else {
        return Err(CliError::usage(
            "rewrite apply requires --proposal FILE — the reviewed proposal IS the approval \
             token; there is no way to apply without one",
        )
        .fix(format!(
            "generate one with `trailtracker rewrite propose <rule> <FILE> -o proposal.json` \
             — usage: {USAGE_REWRITE}"
        )));
    };
    if pos.len() > 1 {
        return Err(CliError::usage(format!(
            "`rewrite apply` takes at most 1 positional argument (DIR), got {}: {}",
            pos.len(),
            pos.join(" ")
        ))
        .fix(format!("usage: {USAGE_REWRITE}")));
    }

    let text = fs::read_to_string(&proposal_path).map_err(|e| {
        CliError::not_found(format!("failed to read proposal {proposal_path}: {e}"))
            .fix("pass the path `rewrite propose -o` wrote.")
    })?;
    let proposal = trailtracker::rewrite::proposal::Proposal::parse(&text).map_err(|e| {
        CliError::analysis(format!("proposal {proposal_path} does not verify: {e}")).fix(
            "re-run `trailtracker rewrite propose` to generate a fresh proposal; \
                 hand-edited or stale proposals are never applied.",
        )
    })?;
    if proposal.edits.is_empty() {
        return Err(CliError::usage(format!(
            "proposal {proposal_path} contains no edits — there is nothing to approve"
        ))
        .fix(
            "re-run `trailtracker rewrite propose`; a run that recognizes no sites is an \
              answer, not an approvable change.",
        ));
    }

    let dir = pos.first().copied().unwrap_or(proposal.dir.as_str());
    let (target, current) = read_rewrite_target(dir, &proposal.file)?;
    let actual = trailtracker::rewrite::proposal::fingerprint(current.as_bytes());
    if actual != proposal.file_fingerprint {
        return Err(CliError::analysis(format!(
            "{} changed since the proposal was made (file is {actual}, proposal expects {})",
            target.display(),
            proposal.file_fingerprint
        ))
        .fix(format!(
            "re-run `trailtracker rewrite propose {} {} {dir}` and review a fresh proposal.",
            proposal.rule_id, proposal.file
        )));
    }
    // Belt-and-braces under the fingerprint: every `before` must still match.
    for (k, e) in proposal.edits.iter().enumerate() {
        let (s, t) = (e.span.start as usize, e.span.end as usize);
        if t > current.len() || current.get(s..t) != Some(e.before.as_str()) {
            return Err(CliError::analysis(format!(
                "edit {k} of {proposal_path} no longer matches the bytes at {s}..{t} of {}",
                target.display()
            ))
            .fix(format!(
                "re-run `trailtracker rewrite propose {} {} {dir}` and review a fresh proposal.",
                proposal.rule_id, proposal.file
            )));
        }
    }

    // Equivalence verification (ADR-0007): recomputed from the file and the
    // proposal alone, nothing cached; refuse to write when any remapping
    // check fails. Opt-in via --require-cert in K3c; the DEFAULT since K3d
    // (require_cert is initialized true and no flag lowers it).
    let cert = if require_cert {
        Some(
            trailtracker::rewrite::cert::certify(&current, &proposal).map_err(|e| {
                CliError::analysis(format!(
                    "refusing to apply {proposal_path}: equivalence verification FAILED — {e}"
                ))
                .fix(format!(
                    "the proposal is not a certified-safe application of {} v{}; re-run \
                     `trailtracker rewrite propose` and review a fresh proposal.",
                    proposal.rule_id, proposal.rule_version
                ))
            })?,
        )
    } else {
        None
    };

    let edits = proposal.span_edits();
    let rewritten = trailtracker::rewrite::edit::apply_edits(&current, &edits)
        .map_err(|e| CliError::analysis(format!("cannot apply {proposal_path}: {e}")))?;

    // Atomic write: temp file in the target's directory, then rename.
    let tmp = target.with_file_name(format!(
        "{}.tt-rewrite-tmp-{}",
        target
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_else(|| "target".to_string()),
        std::process::id()
    ));
    fs::write(&tmp, rewritten.as_bytes())
        .map_err(|e| CliError::analysis(format!("failed to write {}: {e}", tmp.display())))?;
    fs::rename(&tmp, &target).map_err(|e| {
        let _ = fs::remove_file(&tmp);
        CliError::analysis(format!("failed to replace {}: {e}", target.display()))
    })?;

    if json {
        let mut pairs = vec![
            ("schema", Json::str("trailtracker.rewrite-apply/v1")),
            ("file", Json::str(target.display().to_string())),
            (
                "rule",
                Json::obj([
                    ("id", Json::str(proposal.rule_id.clone())),
                    ("version", Json::str(proposal.rule_version.clone())),
                ]),
            ),
            ("edits_applied", Json::U64(proposal.edits.len() as u64)),
            ("bytes_before", Json::U64(current.len() as u64)),
            ("bytes_after", Json::U64(rewritten.len() as u64)),
            ("proposal_hash", Json::str(proposal.hash())),
        ];
        if let Some(cert) = &cert {
            pairs.push(("cert_hash", Json::str(cert.hash())));
        }
        let doc = Json::obj(pairs);
        println_stdout(&doc.to_line(), "rewrite apply")
    } else {
        let certified = match &cert {
            Some(c) => format!(", certified {}", c.hash()),
            None => String::new(),
        };
        println_stdout(
            &format!(
                "applied {} edit(s) to {} ({} v{}{certified})",
                proposal.edits.len(),
                target.display(),
                proposal.rule_id,
                proposal.rule_version
            ),
            "rewrite apply",
        )
    }
}

/// Resolve and read a rewrite target: `file` relative to `dir` (or absolute).
/// Missing paths are exit 3; non-UTF-8 content is exit 4 (span math is
/// byte+char based and the engine only rewrites source text).
fn read_rewrite_target(dir: &str, file: &str) -> Result<(std::path::PathBuf, String), CliError> {
    let dir_path = Path::new(dir);
    if !dir_path.exists() {
        return Err(
            CliError::not_found(format!("path '{dir}' does not exist")).fix(
                "pass an existing directory (paths resolve against the current working directory).",
            ),
        );
    }
    let target = if Path::new(file).is_absolute() {
        std::path::PathBuf::from(file)
    } else {
        dir_path.join(file)
    };
    if !target.exists() {
        return Err(
            CliError::not_found(format!("file '{}' does not exist", target.display()))
                .fix("pass a source file path relative to DIR (or absolute)."),
        );
    }
    let source = fs::read_to_string(&target)
        .map_err(|e| CliError::analysis(format!("failed to read {}: {e}", target.display())))?;
    Ok((target, source))
}

/// `doctor [DIR]` — self-diagnose the tool + environment (read-only; the only
/// writes are the doctor's own run artifacts under `<DIR>/.doctor/`, and
/// `--no-artifact` disables even those). Sub-verbs: `doctor capabilities`
/// (machine contract) and `doctor robot-docs` (agent handbook). Exit codes:
/// 0 healthy, 1 findings present, 2 usage, 3 DIR missing.
fn cmd_doctor(rest: &[String]) -> Result<u8, CliError> {
    // Reflection sub-verbs take precedence over DIR. (To diagnose a directory
    // literally named `capabilities`, pass `./capabilities`.)
    match rest.first().map(String::as_str) {
        Some("capabilities") => {
            let parsed = split_args("doctor capabilities", rest.get(1..).unwrap_or(&[]))?;
            expect_at_most(
                "doctor capabilities",
                "trailtracker doctor capabilities [--json]",
                &parsed,
                0,
            )?;
            // `--json` is accepted as a no-op: the output is already JSON.
            println_stdout(&doctor_capabilities_json().to_line(), "doctor capabilities")?;
            return Ok(0);
        }
        Some("robot-docs") => {
            let parsed = split_args("doctor robot-docs", rest.get(1..).unwrap_or(&[]))?;
            expect_at_most(
                "doctor robot-docs",
                "trailtracker doctor robot-docs",
                &parsed,
                0,
            )?;
            write_stdout(robot_docs().as_bytes(), "robot docs")?;
            return Ok(0);
        }
        _ => {}
    }

    let mut opts = DoctorOptions {
        quick: false,
        fix: false,
        dry_run: false,
        artifact: true,
    };
    let mut json = false;
    let mut pos: Vec<&str> = Vec::new();
    for arg in rest {
        match arg.as_str() {
            "--json" | "--robot" => json = true,
            "--quick" => opts.quick = true,
            "--fix" => opts.fix = true,
            "--dry-run" => opts.dry_run = true,
            "--no-artifact" => opts.artifact = false,
            flag if flag.starts_with('-') => {
                let known = [
                    "--json",
                    "--robot",
                    "--quick",
                    "--fix",
                    "--dry-run",
                    "--no-artifact",
                ];
                let fix = match closest(flag, &known) {
                    Some(k) => format!("did you mean `{k}`?"),
                    None => "usage: trailtracker doctor [DIR] [--json] [--quick] [--fix] \
                             [--dry-run] [--no-artifact]"
                        .to_string(),
                };
                return Err(
                    CliError::usage(format!("unknown flag '{flag}' for `doctor`")).fix(fix),
                );
            }
            p => pos.push(p),
        }
    }
    if pos.len() > 1 {
        return Err(CliError::usage(format!(
            "`doctor` takes at most 1 positional argument (DIR), got {}: {}",
            pos.len(),
            pos.join(" ")
        ))
        .fix(
            "usage: trailtracker doctor [DIR] [--json] [--quick] [--fix] [--dry-run] \
              [--no-artifact]",
        ));
    }
    if opts.dry_run && !opts.fix {
        return Err(
            CliError::usage("--dry-run only applies together with --fix")
                .fix("run `trailtracker doctor <dir> --fix --dry-run` to preview the fix plan."),
        );
    }
    let dir = pos.first().copied().unwrap_or(".");
    if !Path::new(dir).exists() {
        return Err(
            CliError::not_found(format!("path '{dir}' does not exist")).fix(
                "pass an existing directory (paths resolve against the current working \
                 directory).",
            ),
        );
    }

    let outcome = run_doctor(dir, &opts);
    if json {
        println_stdout(&outcome.report.to_line(), "doctor report")?;
    } else {
        write_stdout(outcome.human.as_bytes(), "doctor report")?;
    }
    Ok(outcome.exit)
}

/// Markdown-in-JSON envelope for commands whose native output is markdown.
fn markdown_envelope(command: &str, dir: &str, markdown: &str) -> Json {
    Json::obj([
        ("schema", Json::str("trailtracker.markdown/v1")),
        ("command", Json::str(command)),
        ("dir", Json::str(dir)),
        ("format", Json::str("markdown")),
        ("markdown", Json::str(markdown)),
    ])
}

// ---------------------------------------------------------------------------
// Self-documentation: help + capabilities
// ---------------------------------------------------------------------------

/// The machine-readable CLI contract (schema `trailtracker.capabilities/v1`):
/// every command with usage, output shape, and flags; every extractor, query
/// kind, and export format; the exit-code dictionary; the error shape; and the
/// IO contract. `trailtracker help --json` returns the same document.
fn capabilities_json() -> Json {
    let extractor_names: Vec<Json> = extractors().iter().map(|e| Json::str(e.name())).collect();
    let mut views: Vec<Json> = vec![Json::str("graph")];
    views.extend(extractors().iter().map(|e| Json::str(e.name())));

    let cmd = |name: &str, usage: &str, summary: &str, output: Json| {
        Json::obj([
            ("name", Json::str(name)),
            ("usage", Json::str(usage)),
            ("summary", Json::str(summary)),
            ("output", output),
        ])
    };
    let out = |format: &str, notes: &str| {
        Json::obj([("format", Json::str(format)), ("notes", Json::str(notes))])
    };

    let commands =
        vec![
        cmd(
            "graph",
            "trailtracker graph [DIR] [--json]",
            "Analyze DIR (default `.`) and emit the canonical code graph.",
            out(
                "jsonl",
                "one {record:\"node\"|\"edge\", ...} object per line; --json is a no-op",
            ),
        ),
        cmd(
            "cpg",
            "trailtracker cpg [DIR] [--json]",
            "The base graph plus the deterministic CPG overlay (ADR-0003): intra-function \
             Statement nodes, FLOWS_TO control-flow edges (sequence, branches, loop \
             back-edges, match arms, early returns) and DATA_DEP def-use edges \
             (conservative may-reach, consumer→producer). Output is a strict superset of \
             `graph`; currently Rust functions only.",
            out(
                "jsonl",
                "same record shape as `graph` plus Statement nodes and \
                 FLOWS_TO/DATA_DEP edges; --json is a no-op",
            ),
        ),
        cmd(
            "stats",
            "trailtracker stats [DIR] [--json]",
            "Coverage + graph statistics; use it to judge how much of the repo was understood.",
            out(
                "text | json",
                "--json emits schema trailtracker.stats/v1: {files, lossless_files, parse{...}, \
                 nodes{total, by_kind}, edges{total, by_kind}, calls{resolved, ambiguous, \
                 external, by_resolution}}",
            ),
        ),
        cmd(
            "parse",
            "trailtracker parse FILE",
            "Emit the lossless CST of one Rust file.",
            out("json", "single-line CST document; --json is a no-op"),
        ),
        cmd(
            "extract",
            "trailtracker extract NAME [DIR] [--json]",
            "Apply a derived-view extractor (see `extractors`) and emit its graph.",
            out("jsonl", "same record shape as `graph`; --json is a no-op"),
        ),
        #[cfg(feature = "enrich")]
        cmd(
            "enrich-domains",
            "trailtracker enrich-domains [DIR] [--json]",
            "ENRICH FEATURE BUILDS ONLY (internal tooling; never in shipped/airgap \
             binaries). Optional LLM naming pass over the deterministic domain clusters \
             — the only command that uses an LLM/network. Cluster ids, membership, and \
             counts are computed locally (byte-identical to `extract domains`); the \
             backend (default `claude -p --output-format json --model haiku`, override \
             with TRAILTRACKER_ENRICH_CMD) returns only \
             name/description/responsibilities per cluster. Output is attested (backend, \
             model, evidence FNV-1a-64 prompt_hash, timestamp), NOT byte-stable. No \
             backend => exit 4; names are never invented.",
            out(
                "text | json",
                "--json emits schema trailtracker.enrich/v1: {dir, clusters:[{cluster_id, \
                 domain, label, unit_count, file_count, symbol_count, confidence, \
                 subdomains[], name, description, responsibilities[]}], \
                 attestation:{backend, model, prompt_hash, timestamp, determinism}}",
            ),
        ),
        cmd(
            "export",
            "trailtracker export ontoloom [DIR] [--view NAME]",
            "Emit a view as Ontoloom wire JSON (see `views`), loadable by the Ontoloom editor.",
            out(
                "json",
                "single {name, nodes, relationships} document with a deterministic seed layout",
            ),
        ),
        #[cfg(feature = "enrich")]
        cmd(
            "dossier",
            "trailtracker dossier <DIR> [-o out.html] [--enrich enrich.json]",
            "The client-ready deliverable: analyze DIR and write ONE self-contained HTML \
             file — inline CSS/JS, embedded hierarchy graph, ZERO external requests \
             (airgap-grade) — containing the codebase brief, the interactive \
             Domain→Unit→File→Symbol code map (drill-only click-to-expand, web/tree \
             layouts, search, dependency edges), the full layer-violations table at \
             unit grain, and, when --enrich supplies a trailtracker.enrich/v1 document, \
             the enriched domain cards with their attestation (model, prompt hash). \
             Byte-deterministic for identical inputs; the generated line attests a \
             content fingerprint, never a wall clock. Default output: \
             <repo-name>-dossier.html in the current directory.",
            out(
                "text",
                "stdout carries only the written file's path; the dossier itself is the \
                 HTML file",
            ),
        ),
        #[cfg(not(feature = "enrich"))]
        cmd(
            "dossier",
            "trailtracker dossier <DIR> [-o out.html]",
            "The client-ready deliverable: analyze DIR and write ONE self-contained HTML \
             file — inline CSS/JS, embedded hierarchy graph, ZERO external requests \
             (airgap-grade) — containing the codebase brief, the interactive \
             Domain→Unit→File→Symbol code map (drill-only click-to-expand, web/tree \
             layouts, search, dependency edges), and the full layer-violations table at \
             unit grain. Byte-deterministic for identical inputs; the generated line \
             attests a content fingerprint, never a wall clock. Default output: \
             <repo-name>-dossier.html in the current directory.",
            out(
                "text",
                "stdout carries only the written file's path; the dossier itself is the \
                 HTML file",
            ),
        ),
        cmd(
            "deadcode",
            "trailtracker deadcode [DIR] [--json] [--min-confidence high|medium|low] \
             [--limit N] [--why TARGET] [--no-test-roots] [--config PATH]",
            "Rooted mark-and-sweep over the merged graph. Auditable roots include main \
             functions, entrypoint facts, main guards, shebangs, tests, decorators, \
             generated files, and config declarations. Findings are ranked as dead-high, \
             dead-medium, or transitively-dead with inbound, ambiguity, textual-mention, \
             and export evidence. --why prints the shortest deterministic root chain or \
             the evidence proving no path. Deterministic, read-only, no graph mutation.",
            Json::obj([
                ("format", Json::str("text | json")),
                (
                    "notes",
                    Json::str(
                        "--json emits schema trailtracker.deadcode/v1: {schema, command, \
                         dir, summary{symbols,roots,dead{high,medium,transitive}}, \
                         findings[{id,path,line,name,kind,tier,reason,evidence{inbound_refs,\
                         ambiguous_candidacies,mention_files,exported}}], roots[{id,reason}]}",
                    ),
                ),
                (
                    "exit_codes",
                    Json::obj([
                        ("0", Json::str("no findings at the selected confidence")),
                        ("1", Json::str("findings present at the selected confidence")),
                        ("2", Json::str("invalid flag, value, or config")),
                        ("3", Json::str("path, config, or --why target not found")),
                        ("4", Json::str("analysis failure")),
                    ]),
                ),
            ]),
        ),
        cmd(
            "violations",
            "trailtracker violations <DIR> [--examples N] [--json]",
            "The spec-free full layer-violations report: every DEPENDS-family \
             (CALLS, IMPORTS, USES_TYPE, ...) or SPECIALIZES-family (EXTENDS, \
             IMPLEMENTS — cross-layer inheritance is a violation too) edge that \
             points outward against the clean-architecture direction rule (Domain < \
             Application < Infrastructure < Presentation; Test/Shared exempt), at \
             UNIT grain — from-unit and to-unit with their layers, complete edge \
             counts, and complete symbol-grain evidence \
             (`path:symbol -[KIND]-> path:symbol`; --examples N bounds the list, \
             never the counts) — ranked worst-first and grouped by layer pair. \
             Unit/layer placement is the layers view's recovered assignment (no \
             arch spec needed; use `arch-verify` for spec-driven gating). \
             Deterministic. Exit 0 clean, 1 violations present.",
            out(
                "text | json",
                "--json emits schema trailtracker.violations/v1: {schema, dir, rule, \
                 total_edges, unit_pairs, layer_pairs:[{from_layer, to_layer, edges, \
                 unit_pairs}], violations:[{from_unit, from_layer, to_unit, to_layer, \
                 count, examples[]}], status: clean|violations, exit}",
            ),
        ),
        cmd(
            "verbalize",
            "trailtracker verbalize <DIR> [--view summary|hotspots|dependents|violations|\
             domains|all] [--target ID] [--budget N] [--json]",
            "The recovered graph as retrieval-safe sentences (ADR-0008): a glossary \
             prelude of dense value-ranked handles (D1 = largest domain, F1 = top \
             hotspot), then one fact per sentence in domain-major order — identity, \
             domain sizes, dependencies with chief target units, fan-in/fan-out and \
             blast radius with denominators, named dependents per hotspot (--view \
             dependents for the relational-lookup document), layer violations, cycles, \
             entry points, \
             flows, parse coverage. Deterministic (byte-identical for the same tree); \
             every sentence passes the grammar conformance checker. --budget N cuts at \
             a character budget and appends an honest omission sentence; --target \
             renders one node's card (resolution: exact id, then file path, then name \
             — ambiguous exits 2 with candidates, unknown exits 3 with suggestions).",
            out(
                "text | json",
                "text: one sentence per line, glossary lines first. --json emits schema \
                 trailtracker.verbalize/v1: {schema, command, dir, view, \
                 template_version, glossary:[{handle, expansion}], sentences[], \
                 total_sentences, omitted}",
            ),
        ),
        cmd(
            "arch-verify",
            "trailtracker arch-verify [DIR] [--spec PATH] [--json]",
            "Continuous architecture verification (ADR-0005): load the human-authored \
             intent spec (default <DIR>/.trailtracker-arch.json — domains as pathPrefixes \
             plus rules: domain-existence, domain-containment, forbidden-dependency, \
             forbidden-layer-dependency), evaluate it against the ACTUAL recovered graph, \
             and report findings with evidence. Deterministic. Exit 0 spec holds (or \
             warn-only), 1 error-severity findings — the CI gate; a malformed spec is \
             exit 2, a missing DIR/spec is exit 3.",
            out(
                "text | json",
                "--json emits schema trailtracker.arch-verify/v1: {format, dir, spec, \
                 domains, rules, findings:[{id, type, severity, message, count, \
                 examples[]}], status: clean|warnings|violated, exit}",
            ),
        ),
        cmd(
            "arch-init",
            "trailtracker arch-init [DIR] [-o PATH]",
            "Bootstrap a .trailtracker-arch.json spec from the CURRENT recovered \
             architecture: business domains with derived pathPrefixes (dominant-prefix \
             set-cover), domain-existence (error) + domain-containment (warn) rules, and \
             the observed inter-domain dependencies as an advisory baseline to promote \
             into forbidden-dependency rules. Prints to stdout (redirect to adopt); -o \
             writes a file and refuses to overwrite.",
            out(
                "json",
                "a trailtracker.arch-spec/v1 document, pretty-printed for hand editing; \
                 with -o, stdout carries only the written file's path",
            ),
        ),
        cmd(
            "query",
            "trailtracker query KIND [TARGET] [DIR] [--json]",
            "Ask the graph a question (see `query_kinds`). TARGET is a node name or exact id.",
            out("text | json", "--json emits one structured object per query"),
        ),
        cmd(
            "explain",
            "trailtracker explain <id-or-path-or-name> [DIR] [--json]",
            "The atomic understanding primitive: one card for a file or symbol — identity \
             (name, kind, path:line, qualified name), classification (domain, layer, \
             archetype), connectivity (fan-in/fan-out with top dependents/dependencies), \
             blast radius (reverse reachability, same machinery as `query blast-radius`), \
             and nearest neighbors (hybrid search, each with why-evidence). Targets resolve \
             exact node id, then exact file path, then exact name; an ambiguous name exits \
             2 with the candidate list, an unknown target exits 3 with search suggestions.",
            out(
                "text | json",
                "--json emits schema trailtracker.explain/v1: {dir, target, identity{id, \
                 name, kind, path, line, qualified_name}, classification{domain, layer, \
                 archetype}, connectivity{fan_in, fan_out, dependents[], dependencies[]}, \
                 blast_radius{count, examples[]}, neighbors:[{rank, id, name, kind, path, \
                 score, why[]}]}",
            ),
        ),
        cmd(
            "search",
            "trailtracker search \"<query>\" [DIR] [--limit N] [--json]",
            "Hybrid code search over the graph: BM25 + hash-embedding rank fusion (RRF), \
             re-ranked by graph proximity to the top lexical anchors. Deterministic, no LLM. \
             Every hit explains itself (`why`: bm25/embed rank, hops from anchor). Default \
             limit 20.",
            out(
                "text | json",
                "--json emits schema trailtracker.search/v1: {query, dir, total, \
                 results:[{rank, id, name, kind, path, score, why[]}]}; ranks are 1-based, \
                 results sorted best-first",
            ),
        ),
        cmd(
            "nav",
            "trailtracker nav pack \"<task query>\" [DIR] [--budget CHARS] \
             [--format json|text|prose] [--json] | \
             trailtracker nav expand <target> [DIR] [--depth K] [--direction \
             callers|callees|both] [--budget CHARS] [--cursor N] \
             [--format json|text|prose] [--json]",
            "The context-efficient codebase navigator (ADR-0004): exact, deterministic, \
             character-budgeted subgraphs for agents working large codebases. `nav pack` \
             turns a task query into one context pack — seeds (hybrid search hits with \
             why-evidence), compact per-seed cards (domain/layer/archetype, fan-in/out, \
             blast-radius count), a domain/layer orientation summary, a ranked read-plan \
             of file:line SPANS (never whole files), and the 2-hop DEPENDS-family \
             neighborhood edge list — the highest-value exact subgraph that fits the \
             budget. `nav expand` grows the exact neighborhood from any node, \
             direction-aware and depth-bounded, with a continuation cursor. --budget is a \
             character budget (proxy for the consuming agent's context window): no LLM, \
             no tokenizer, budgets are exact char counts over the JSON serialization, \
             and every response reports budget_chars/used_chars/estimated_chars plus \
             exact per-section omission counts. Targets resolve like `explain` (exact id \
             -> file path -> name; ambiguous exits 2, unknown exits 3).",
            out(
                "text | json | prose",
                "--json emits schema trailtracker.nav-pack/v1: {query, dir, \
                 budget{budget_chars, used_chars, estimated_chars, truncated, exceeded, \
                 omitted{}}, seeds[], cards[], orientation{domains[], layers[]}, \
                 read_plan:[{path, start_line, end_line?, id, name, kind, why}], \
                 neighborhood{depth, node_count, edge_count_total, edges[]}} — or \
                 trailtracker.nav-expand/v1: {target, identity{}, direction, depth, \
                 budget{...}, total_edges, cursor, returned, truncated, next_cursor, \
                 nodes[], edges:[{from, kind, to, hops}]}. --format prose renders the \
                 same value-ranked selection as deterministic ADR-0008 sentences \
                 (glossary prelude, read-plan spans as facts) with the char budget \
                 honest over the prose — feed it to any model directly",
            ),
        ),
        cmd(
            "report",
            "trailtracker report [DIR] [--json] | trailtracker report --full <DIR> [-o PATH] \
             [--format md|html|both] [--examples N] [--budget N] [--json]",
            "Deterministic markdown org/codebase summary. With --full: the full evidence \
             report — executive summary in verbalizer prose, domains table, change-risk \
             centers with their actual named callers grouped by domain, EVERY \
             layer-violating edge at symbol grain (inheritance included; --examples N \
             caps evidence lists, never counts), structural findings (named cycles, \
             largest declaration unit, misplaced tests, unlexable bytes), and a \
             domains-only coupling appendix. --format both writes PATH.md + PATH.html \
             (self-contained HTML with collapsible evidence and an embedded \
             copy-to-clipboard companion); with -o, stdout carries only the written \
             paths.",
            out(
                "markdown | html | json",
                "--json wraps the markdown in schema trailtracker.markdown/v1",
            ),
        ),
        cmd(
            "brief",
            "trailtracker brief [DIR] [--json]",
            "The best first call on an unfamiliar repo: overview, architecture, entry points, \
             hotspots, cycles, synthesis.",
            out(
                "markdown | json",
                "--json emits schema trailtracker.brief/v1: {overview{languages[]}, \
                 architecture{largest_units[], module_dependencies[]}, entry_points{mains[], \
                 public_api[]}, hotspots{fan_in[], fan_out[]}, cycles[][], synthesis}",
            ),
        ),
        cmd(
            "rebuild-brief",
            "trailtracker rebuild-brief <flow-name-or-id> [DIR] [--json]",
            "Self-contained markdown rebuild brief for one workflow.",
            out(
                "markdown | json",
                "--json wraps the markdown in schema trailtracker.markdown/v1",
            ),
        ),
        cmd(
            "rewrite",
            "trailtracker rewrite propose <rule> <FILE> [DIR] [--lines A-B] [--name NAME] \
             [-o proposal.json] [--json] | trailtracker rewrite verify --proposal \
             proposal.json [DIR] [-o cert.json] [--json] | trailtracker rewrite apply \
             --proposal proposal.json [DIR] [--require-cert] [--json] | trailtracker \
             rewrite rules [--json]",
            "Propose-then-approve span rewrites (ADR-0006) with equivalence certificates \
             (ADR-0007) — the ONLY code-modifying capability, and it never modifies \
             anything in one step. `propose` analyzes and emits a unified diff (stdout) \
             plus a hash-bound trailtracker.rewrite-proposal/v1 document (-o writes it; \
             --json emits it instead of the diff); it NEVER writes source, has no --apply \
             flag, and refuses to emit a non-empty proposal it cannot certify (with -o it \
             writes the trailtracker.rewrite-cert/v1 certificate to <stem>.cert.json). \
             `verify` is the independent checker: from the original file and the proposal \
             alone it recomputes the before/after statement CPGs, verifies the rule's \
             licensed remapping (ADR-0007), replays the licensed emission byte-for-byte, \
             and emits the certificate — exit 0 verified, exit 4 names the exact failed \
             check. `apply` is the only writing path: it refuses unless the proposal hash \
             verifies, the target file's current fingerprint matches, and every edit's \
             `before` text still matches its span; the full equivalence verification \
             then runs BY DEFAULT (K3d) and refuses on any failed check — --require-cert \
             re-asserts that default (kept for compatibility), no opt-out. Writes are \
             atomic and touch only the proposed spans. `rules` lists the rule vocabulary: \
             dead-branch-elim, loop-to-iterator, extract-function, redundant-clone-elim. \
             Recognizers are \
             conservative: near-miss sites are reported as rejections with \
             machine-readable snake_case reasons. Proposals and certificates contain no \
             timestamp: same binary + same file => byte-identical documents, hashes \
             included.",
            out(
                "diff | json",
                "propose: unified diff on stdout (--json: the \
                 trailtracker.rewrite-proposal/v1 document {schema, rule{id,version}, dir, \
                 file, file_fingerprint, edits:[{span{start,end}, before, after, why_safe, \
                 cpg_facts[]}], rejections:[{span, reason, detail}], proposal_hash}); \
                 verify: human summary (--json: trailtracker.rewrite-cert/v1 {schema, \
                 rule, schema_obligation{ref,kani}, proposal_hash, dir, file, \
                 before_fingerprint, after_fingerprint, before_cpg_hash, after_cpg_hash, \
                 functions{affected[],unaffected_verified}, checks[], assumptions[], \
                 cert_hash}); apply: a one-line report (--json: \
                 trailtracker.rewrite-apply/v1, cert_hash always present); rules: \
                 the vocabulary (--json: trailtracker.rewrite-rules/v1)",
            ),
        ),
        cmd(
            "doctor",
            "trailtracker doctor [DIR] [--json] [--quick] [--fix] [--dry-run] [--no-artifact]",
            "Self-diagnose the tool + environment against DIR (default `.`): version/build, \
             analysis, parse failures, losslessness, extractors, determinism. Read-only \
             (advisory fixes only); exit 0 healthy, 1 findings. Sub-verbs: `doctor \
             capabilities` (contract), `doctor robot-docs` (agent handbook).",
            out(
                "text | json",
                "--json emits schema trailtracker.doctor/v1: {status, exit_code, summary, \
                 checks[], findings[], fix, run, artifact}; run artifacts land in \
                 <DIR>/.doctor/runs/<run-id>/ (content-derived run id; byte-deterministic)",
            ),
        ),
        cmd(
            "capabilities",
            "trailtracker capabilities",
            "This machine-readable contract.",
            out("json", "schema trailtracker.capabilities/v1"),
        ),
        cmd(
            "version",
            "trailtracker version",
            "Print `trailtracker <semver>`.",
            out("text", "also available as --version / -V"),
        ),
        cmd(
            "help",
            "trailtracker help [--json]",
            "Human overview; --json returns this capabilities document.",
            out("text | json", "bare `trailtracker` prints the same overview"),
        ),
    ];

    Json::obj([
        ("schema", Json::str("trailtracker.capabilities/v1")),
        ("name", Json::str("trailtracker")),
        ("version", Json::str(env!("CARGO_PKG_VERSION"))),
        #[cfg(not(feature = "enrich"))]
        (
            "description",
            Json::str(
                "Airgap-safe code ontology and graph extractor: deterministic code graphs \
                 and derived ontology views computed locally. This binary contains no \
                 network-capable or model-invoking code paths — no LLM, no network, \
                 nothing that shells out to one.",
            ),
        ),
        #[cfg(feature = "enrich")]
        (
            "description",
            Json::str(
                "Code ontology and graph extractor: deterministic code graphs and derived \
                 ontology views computed locally (no LLM, no network). THIS IS AN `enrich` \
                 FEATURE BUILD (internal tooling, never shipped): it additionally carries \
                 the optional `enrich-domains` command, which shells out to an LLM backend \
                 to *name* the deterministic clusters.",
            ),
        ),
        ("commands", Json::Array(commands)),
        ("extractors", Json::Array(extractor_names)),
        ("views", Json::Array(views)),
        (
            "query_kinds",
            Json::Array(QUERY_KINDS.iter().map(|k| Json::str(*k)).collect()),
        ),
        ("export_formats", Json::Array(vec![Json::str("ontoloom")])),
        (
            "global_flags",
            Json::Array(vec![
                Json::obj([
                    ("flag", Json::str("--json")),
                    (
                        "meaning",
                        Json::str(
                            "machine-readable output; a no-op on commands whose output is \
                             already JSON (graph, extract, export, parse)",
                        ),
                    ),
                ]),
                Json::obj([
                    ("flag", Json::str("--robot")),
                    ("meaning", Json::str("synonym for --json")),
                ]),
                Json::obj([
                    ("flag", Json::str("--incremental")),
                    (
                        "meaning",
                        Json::str(
                            "opt-in incremental analysis: cache per-language-batch lowered \
                             subgraphs under <DIR>/.trailtracker-cache (override with \
                             TRAILTRACKER_CACHE_DIR; TRAILTRACKER_CACHE=1 enables without the \
                             flag) and reuse them for unchanged files. Output is byte-identical \
                             to an uncached run; a no-op on commands that do not analyze a \
                             directory",
                        ),
                    ),
                ]),
                Json::obj([
                    ("flag", Json::str("--no-ignore")),
                    (
                        "meaning",
                        Json::str(
                            "analyze everything on disk. By default, when DIR is a git \
                             checkout (a .git entry exists directly under it), files matched \
                             by its layered .gitignore rules are excluded from the walk — \
                             untracked build outputs (minified bundles, bin/obj, coverage) \
                             are not source and corrupt stats and every derived view. Trees \
                             without .git are never filtered; a no-op on commands that do \
                             not analyze a directory",
                        ),
                    ),
                ]),
            ]),
        ),
        (
            "exit_codes",
            Json::obj([
                ("0", Json::str("success")),
                (
                    "1",
                    Json::str(
                        "doctor/arch-verify/violations/deadcode only: findings present \
                         (unhealthy target or tool, architecture/layer violations, or \
                         dead-code findings)",
                    ),
                ),
                (
                    "2",
                    Json::str("usage error (bad command, flag, or argument)"),
                ),
                ("3", Json::str("path not found or unreadable")),
                ("4", Json::str("analysis failure (internal error)")),
            ]),
        ),
        (
            "error_shape",
            Json::obj([
                ("stream", Json::str("stderr")),
                ("line_1", Json::str("trailtracker: <what went wrong>")),
                ("line_2", Json::str("  fix: <how to fix it> (optional)")),
            ]),
        ),
        (
            "io_contract",
            Json::obj([
                ("stdout", Json::str("data only")),
                ("stderr", Json::str("diagnostics only")),
                #[cfg(not(feature = "enrich"))]
                (
                    "determinism",
                    Json::str("byte-identical output for identical input trees"),
                ),
                #[cfg(feature = "enrich")]
                (
                    "determinism",
                    Json::str(
                        "byte-identical output for identical input trees — except \
                         `enrich-domains`, whose semantic fields are LLM-attested \
                         (prompt_hash + model + timestamp), not byte-stable",
                    ),
                ),
            ]),
        ),
        (
            "recommended_first_calls",
            Json::Array(vec![
                Json::str("trailtracker brief DIR --json"),
                Json::str("trailtracker stats DIR --json"),
                Json::str("trailtracker extract domains DIR"),
                Json::str("trailtracker doctor DIR --json"),
            ]),
        ),
    ])
}

fn help_text() -> String {
    let extractor_names: Vec<&str> = extractors().iter().map(|e| e.name()).collect();
    // `enrich` feature builds (internal tooling) document their extra
    // surface; the default/airgap build's help carries no trace of it.
    #[cfg(feature = "enrich")]
    let enrich_help = "    enrich-domains [DIR] [--json]\n\
                   ENRICH FEATURE BUILDS ONLY (internal tooling; never in\n\
                   shipped/airgap binaries). Optional LLM naming pass: give\n\
                   the deterministic domain clusters semantic names via an\n\
                   external backend (default: the Claude Code CLI; override\n\
                   with TRAILTRACKER_ENRICH_CMD). The only command that uses\n\
                   an LLM/network. Membership and counts stay deterministic\n\
                   (identical to `extract domains`); the semantic fields are\n\
                   attested (backend, model, prompt hash, timestamp), not\n\
                   byte-stable. No backend => exit 4, never invented names\n";
    #[cfg(not(feature = "enrich"))]
    let enrich_help = "";
    #[cfg(feature = "enrich")]
    let dossier_help = "    dossier <DIR> [-o out.html] [--enrich enrich.json]\n\
                   The client-ready deliverable: ONE self-contained HTML file\n\
                   (inline CSS/JS, embedded graph, zero external requests)\n\
                   with the brief, the interactive Domain→Unit→File→Symbol\n\
                   code map, the full layer-violations table, and — with\n\
                   --enrich — the enriched domain cards + attestation.\n\
                   Byte-deterministic; prints the output path (default\n\
                   <repo>-dossier.html)\n";
    #[cfg(not(feature = "enrich"))]
    let dossier_help = "    dossier <DIR> [-o out.html]\n\
                   The client-ready deliverable: ONE self-contained HTML file\n\
                   (inline CSS/JS, embedded graph, zero external requests)\n\
                   with the brief, the interactive Domain→Unit→File→Symbol\n\
                   code map, and the full layer-violations table.\n\
                   Byte-deterministic; prints the output path (default\n\
                   <repo>-dossier.html)\n";
    format!(
        "TrailTracker — airgap-safe code ontology and graph extractor\n\
\n\
USAGE:\n\
    trailtracker <COMMAND> [ARGS] [--json]\n\
\n\
COMMANDS:\n\
    graph [DIR]    Analyze DIR (default `.`) and emit the canonical graph as JSONL\n\
    cpg [DIR]      The canonical graph PLUS the deterministic CPG overlay:\n\
                   intra-function Statement nodes, FLOWS_TO control flow\n\
                   (sequence, branches, loops, match arms, early returns)\n\
                   and DATA_DEP def-use chains. Strict superset of `graph`;\n\
                   Rust functions only for now\n\
    stats [DIR]    Print coverage + graph statistics for DIR (--json for a\n\
                   machine-readable object)\n\
    parse FILE     Emit the lossless CST of one Rust file as JSON\n\
    extract NAME [DIR]\n\
                   Apply a derived-view extractor to DIR (default `.`) and emit\n\
                   its graph as JSONL. Extractors: {extractors}\n\
{enrich_help}\
    export ontoloom [DIR] [--view NAME]\n\
                   Analyze DIR (default `.`), apply the chosen view (an\n\
                   extractor name, or `graph` for the base graph; default\n\
                   `hierarchy`), and emit it as Ontoloom wire JSON — a single\n\
                   {{name, nodes, relationships}} document with a deterministic\n\
                   seed layout, loadable directly by the Ontoloom editor\n\
{dossier_help}\
    query KIND [TARGET] [DIR] [--json]\n\
                   Ask the graph a question. KIND is one of:\n\
                     what-touches <id|name>  incoming edges (what references it)\n\
                     uses <id|name>          outgoing edges (what it references)\n\
                     blast-radius <id|name>  transitive reverse reachability\n\
                     deepest-flows           flows ranked by depth\n\
    explain TARGET [DIR] [--json]\n\
                   One card that explains a file or symbol: identity\n\
                   (path:line, qualified name), classification (domain,\n\
                   layer, archetype), fan-in/fan-out with top dependents and\n\
                   dependencies, blast radius, and nearest neighbors via\n\
                   hybrid search. TARGET is an exact node id, a file path,\n\
                   or a symbol name (ambiguous name => exit 2 with\n\
                   candidates; unknown => exit 3 with suggestions)\n\
    search \"<query>\" [DIR] [--limit N]\n\
                   Hybrid code search over the graph: BM25 + hash-embedding\n\
                   rank fusion, re-ranked by graph proximity. Every hit\n\
                   explains itself (bm25/embed rank, hops from anchor).\n\
                   Default limit 20 (--json for machine-readable results)\n\
    nav pack \"<task query>\" [DIR] [--budget CHARS] [--format json|text|prose]\n\
                   The context navigator: ONE call that turns a task into\n\
                   the highest-value exact subgraph that fits a character\n\
                   budget — seeds (search hits + why), compact cards\n\
                   (domain/layer/archetype, fan-in/out, blast count),\n\
                   orientation, a ranked read-plan of file:line spans, and\n\
                   the 2-hop dependency neighborhood. --budget is a char\n\
                   count (proxy for the agent's context window; no LLM, no\n\
                   tokenizer). Truncation is never silent. --format prose\n\
                   renders the selection as deterministic ADR-0008 sentences\n\
                   for feeding a model directly\n\
    nav expand <target> [DIR] [--depth K] [--direction callers|callees|both]\n\
                   [--budget CHARS] [--cursor N] [--format json|text|prose]\n\
                   Exact neighborhood growth from any node: direction-aware,\n\
                   depth-bounded, budget-truncated with honest markers and a\n\
                   continuation cursor. Target resolves like `explain`\n\
    report [DIR]   Deterministic markdown org/codebase summary (--json wraps it\n\
                   in a JSON envelope)\n\
    brief [DIR]    Deterministic markdown codebase model for an unfamiliar\n\
                   repo: overview (languages), architecture (units + module\n\
                   dependency map), entry points, hotspots (fan-in/fan-out),\n\
                   dependency cycles (Tarjan), and a plain-English synthesis\n\
                   (--json for a structured brief object)\n\
    rebuild-brief <flow-name-or-id> [DIR]\n\
                   Self-contained markdown rebuild brief for one workflow:\n\
                   scoped data model, ordered steps with logic + line cites,\n\
                   inlined called code, and a Medplum target scaffold\n\
    rewrite propose <rule> <FILE> [DIR] [--lines A-B] [--name NAME]\n\
                   [-o proposal.json]\n\
                   Analyze one file with a rewrite rule and emit a unified\n\
                   diff plus a hash-bound rewrite-proposal document (-o\n\
                   writes it; --json prints it instead of the diff). NEVER\n\
                   writes source. Every non-empty proposal is certified\n\
                   (ADR-0007); -o also writes <stem>.cert.json. Near-misses\n\
                   are rejections with machine-readable reasons\n\
    rewrite verify --proposal proposal.json [DIR] [-o cert.json]\n\
                   Independent equivalence check: recompute before/after\n\
                   statement CPGs from the file + proposal alone, verify the\n\
                   rule's licensed remapping, replay the licensed emission,\n\
                   and emit the trailtracker.rewrite-cert/v1 certificate.\n\
                   Exit 0 verified; exit 4 names the exact failed check\n\
    rewrite apply --proposal proposal.json [DIR] [--require-cert]\n\
                   The ONLY writing path: refuses tampered proposals (hash),\n\
                   stale files (fingerprint), and drifted spans; applies\n\
                   atomically, touching only the proposed spans. No --force,\n\
                   no --skip-verify — a failed check means re-propose.\n\
                   Full equivalence verification runs first BY DEFAULT;\n\
                   --require-cert re-asserts the default (no opt-out)\n\
    rewrite rules  List the rewrite rule vocabulary (ids, versions, exact\n\
                   recognized shapes; --json for the machine contract)\n\
    deadcode [DIR] [--json] [--min-confidence high|medium|low]\n\
                   [--limit N] [--why TARGET] [--no-test-roots]\n\
                   [--config PATH]\n\
                   Rooted liveness over the merged graph. Marks forward from\n\
                   explicit, test, decorator, generated, and configured roots;\n\
                   reports dead-high, dead-medium, and transitively-dead symbols\n\
                   with inbound, ambiguity, textual-mention, and export evidence.\n\
                   --why prints the shortest root chain or dead evidence.\n\
                   Exit 0 clean, 1 findings present\n\
    violations <DIR> [--json]\n\
                   Spec-free FULL layer-violations report: every dependency\n\
                   pointing outward against the clean-architecture rule\n\
                   (Domain < Application < Infrastructure < Presentation;\n\
                   Test/Shared exempt) at UNIT grain — from-unit -> to-unit\n\
                   with layers, complete edge counts, and file-level example\n\
                   edges — ranked worst-first, grouped by layer pair. Needs\n\
                   no arch spec. Exit 0 clean, 1 violations present\n\
    verbalize <DIR> [--view NAME] [--target ID] [--budget N]\n\
                   The graph as retrieval-safe sentences (ADR-0008): a\n\
                   glossary prelude of dense value-ranked handles (D1 =\n\
                   largest domain, F1 = top hotspot), then one fact per\n\
                   sentence in domain-major order. Views: summary (default),\n\
                   hotspots, dependents, violations, domains, all. --target\n\
                   renders one node's card, dependents named (explain's\n\
                   resolution semantics). --budget N\n\
                   cuts at a character budget with an honest omission\n\
                   sentence. Deterministic; --json for the machine envelope\n\
    arch-verify [DIR] [--spec PATH]\n\
                   Continuous architecture verification (ADR-0005): check\n\
                   the ACTUAL code against the INTENDED architecture in\n\
                   <DIR>/.trailtracker-arch.json (or --spec PATH). Rules:\n\
                   domain-existence, domain-containment,\n\
                   forbidden-dependency, forbidden-layer-dependency.\n\
                   Exit 0 spec holds, 1 error findings — the CI gate\n\
    arch-init [DIR] [-o PATH]\n\
                   Bootstrap a spec from the CURRENT recovered architecture\n\
                   (domains -> pathPrefixes, existence/containment rules,\n\
                   observed dependency baseline). stdout by default; -o\n\
                   writes a file (never overwrites)\n\
    doctor [DIR]   Self-diagnose the tool + environment against DIR (default\n\
                   `.`): version/build, analysis, parse failures,\n\
                   losslessness, extractors, byte-determinism (run twice,\n\
                   compare). Read-only; advisory fixes only. Exit 0 healthy,\n\
                   1 findings. Flags: --json --quick --fix --dry-run\n\
                   --no-artifact. Sub-verbs: `doctor capabilities`,\n\
                   `doctor robot-docs`\n\
    capabilities   Machine-readable CLI contract as JSON: commands, flags,\n\
                   output schemas, exit codes (same as `help --json`)\n\
    version        Print the version\n\
    help           Show this message (--json for the capabilities document)\n\
\n\
OUTPUT CONTRACT:\n\
    stdout carries data; stderr carries diagnostics. Output is deterministic:\n\
    the same input tree always produces byte-identical bytes.\n\
\n\
INCREMENTAL ANALYSIS (opt-in):\n\
    --incremental (or TRAILTRACKER_CACHE=1) caches per-language-batch lowered\n\
    subgraphs under <DIR>/.trailtracker-cache (gitignored; override the\n\
    location with TRAILTRACKER_CACHE_DIR) keyed by per-file content hashes;\n\
    unchanged batches are reused, changed ones relowered. Output stays\n\
    byte-identical to an uncached run — the cache trades disk for time.\n\
\n\
GITIGNORE (default on, opt out with --no-ignore):\n\
    When DIR is a git checkout (a .git entry exists directly under it), files\n\
    matched by its layered .gitignore rules are excluded from analysis:\n\
    untracked build outputs on disk (minified bundles, bin/obj, coverage) are\n\
    not source and corrupt stats and every derived view. Trees without .git\n\
    are never filtered. --no-ignore analyzes everything on disk.\n\
\n\
EXIT CODES:\n\
    0  success\n\
    1  doctor/arch-verify/violations only: findings present; deadcode also\n\
       returns 1 when findings meet --min-confidence\n\
    2  usage error (bad command, flag, or argument)\n\
    3  path not found or unreadable\n\
    4  analysis failure (internal error)\n",
        extractors = extractor_names.join(", ")
    )
}
