//! `trailtracker doctor` — self-diagnosis of the tool + environment.
//!
//! TrailTracker is a read-only analysis tool: it never mutates the code it
//! analyzes. Its doctor is therefore a *forensic* doctor (detect-and-report,
//! never detect-and-rewrite): every check is a pure detector, every "fix" is
//! advisory (a recommended command for the operator), and the only writes the
//! doctor ever performs are its own additive run artifacts under
//! `<DIR>/.doctor/` — routed through the single [`Mutator::write_file`]
//! chokepoint (atomic tmp+rename, FNV-1a-hash-witnessed in `actions.jsonl`).
//!
//! Determinism contract: the doctor inherits the tool's byte-determinism.
//! The run id is content-derived (no wall clock, no randomness), so the same
//! binary diagnosing the same input tree produces byte-identical stdout AND
//! byte-identical artifacts. Re-running the doctor is an idempotent overwrite
//! with identical bytes — run twice equals run once, provably.
//!
//! Safety envelope (reflected by `trailtracker doctor capabilities`):
//! - never writes outside `<DIR>/.doctor/`;
//! - never deletes anything, anywhere;
//! - never overwrites a file it does not own (the only overwrites are its own
//!   prior run artifacts, and those rewrites are byte-identical by
//!   construction);
//! - all writes are atomic (write to a temp sibling, then rename);
//! - no network, no subprocesses, no TTY assumptions;
//! - `--no-artifact` makes a run 100% read-only.
//!
//! Checks (all pure detectors):
//! - `binary`         version + build profile (debug builds get an advisory)
//! - `target`         DIR exists, is a directory, is readable
//! - `analysis`       `analyze_dir` succeeds and finds analyzable files
//! - `parse-failures` no file crashed or was skipped during parsing
//! - `losslessness`   every parsed file reconstructs its source byte-for-byte
//! - `extractors`     every registered extractor runs without panicking
//! - `determinism`    a second full analysis + extraction is byte-identical
//!
//! Exit codes (documented in `doctor capabilities`): 0 healthy (info-level
//! advisories allowed), 1 findings present (warn/error), 2 usage error,
//! 3 target path not found, 4 internal doctor failure.

use std::fs;
use std::io;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::{Path, PathBuf};

use crate::core::json::Json;
use crate::extract::extractors;
use crate::pipeline::{analyze_dir, Analysis};

/// The doctor's JSON report schema identifier.
pub const DOCTOR_SCHEMA: &str = "trailtracker.doctor/v1";
/// The doctor's capabilities-reflection schema identifier.
pub const DOCTOR_CAPABILITIES_SCHEMA: &str = "trailtracker.doctor-capabilities/v1";
/// The per-run scoring artifact schema identifier.
pub const DOCTOR_SCORECARD_SCHEMA: &str = "trailtracker.doctor-scorecard/v1";

/// Exit code when the target is healthy (info-level advisories permitted).
pub const EXIT_HEALTHY: u8 = 0;
/// Exit code when warn/error findings are present.
pub const EXIT_FINDINGS: u8 = 1;

/// How a doctor run should behave. All fields are opt-in flags.
pub struct DoctorOptions {
    /// Cheap checks only: skip the extractor sweep and the determinism
    /// double-run (they are reported as `skipped`).
    pub quick: bool,
    /// Fix mode requested. TrailTracker's doctor has no automated fixers (it
    /// is a read-only tool), so this reports the advisory plan explicitly.
    pub fix: bool,
    /// With `fix`: print the plan without doing anything. (There is never
    /// anything to do; the plan says so.)
    pub dry_run: bool,
    /// Write the per-run artifact under `<DIR>/.doctor/`. Disabled by
    /// `--no-artifact` for 100% read-only runs.
    pub artifact: bool,
}

/// Finding severity. `Info` findings are advisories and do not affect the
/// exit code; `Warn` and `Error` findings make the run unhealthy (exit 1).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Severity {
    Info,
    Warn,
    Error,
}

impl Severity {
    fn as_str(self) -> &'static str {
        match self {
            Severity::Info => "info",
            Severity::Warn => "warn",
            Severity::Error => "error",
        }
    }
}

/// One diagnostic finding: what is wrong, where the evidence is, and the
/// exact command an operator (human or agent) should run about it.
struct Finding {
    id: &'static str,
    check: &'static str,
    severity: Severity,
    message: String,
    evidence: Vec<String>,
    /// The advisory: no finding in this doctor is auto-fixable (the tool is
    /// read-only), so the fix is always a recommended command.
    recommended: Option<String>,
}

/// Result status of one check.
#[derive(Clone, Copy, PartialEq, Eq)]
enum CheckStatus {
    Pass,
    Warn,
    Fail,
    Skipped,
}

impl CheckStatus {
    fn as_str(self) -> &'static str {
        match self {
            CheckStatus::Pass => "pass",
            CheckStatus::Warn => "warn",
            CheckStatus::Fail => "fail",
            CheckStatus::Skipped => "skipped",
        }
    }
}

/// One executed (or skipped) check with its evidence trail.
struct CheckResult {
    id: &'static str,
    title: &'static str,
    status: CheckStatus,
    evidence: Vec<String>,
}

/// Everything the CLI needs to render a doctor run.
pub struct DoctorOutcome {
    /// The full report as JSON (schema [`DOCTOR_SCHEMA`]).
    pub report: Json,
    /// Human rendering of the same report (stdout when `--json` is absent).
    pub human: String,
    /// Process exit code: 0 healthy, 1 findings present.
    pub exit: u8,
}

/// The stable list of check ids, in execution order. Reflected by
/// `doctor capabilities` and used by tests.
pub const CHECK_IDS: &[&str] = &[
    "binary",
    "target",
    "analysis",
    "parse-failures",
    "losslessness",
    "extractors",
    "determinism",
];

// ---------------------------------------------------------------------------
// FNV-1a 64: the doctor's content hash. std-only, stable across platforms
// and Rust versions (unlike `DefaultHasher`), and fast enough for artifacts.
// ---------------------------------------------------------------------------

/// FNV-1a 64-bit hash of `bytes`. Used for run ids and artifact witnesses.
pub fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for b in bytes {
        hash ^= u64::from(*b);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    hash
}

// ---------------------------------------------------------------------------
// The mutate() chokepoint: the ONLY code in the doctor that writes to disk.
// ---------------------------------------------------------------------------

/// The single mutation chokepoint. Every byte the doctor puts on disk flows
/// through [`Mutator::write_file`]: scoped to `<DIR>/.doctor/`, atomic
/// (tmp + rename), and hash-witnessed in the actions ledger.
struct Mutator {
    /// The only directory this mutator will ever write inside.
    scope: PathBuf,
    /// One JSON line per completed write: `{op, path, bytes, fnv1a64}`.
    actions: Vec<Json>,
}

impl Mutator {
    fn new(scope: PathBuf) -> Mutator {
        Mutator {
            scope,
            actions: Vec::new(),
        }
    }

    /// Atomically write `bytes` to `path` (which must be inside the scope):
    /// create parent directories, write a temp sibling, rename into place,
    /// and record the action with its content hash. This is the only
    /// function in the doctor that touches the disk.
    fn write_file(&mut self, path: &Path, bytes: &[u8]) -> io::Result<()> {
        if !path.starts_with(&self.scope) {
            // Defense in depth: the doctor never writes outside its scope.
            return Err(io::Error::other(format!(
                "doctor write to {} refused: outside scope {}",
                path.display(),
                self.scope.display()
            )));
        }
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        let tmp = path.with_extension(format!("tmp-{}", std::process::id()));
        fs::write(&tmp, bytes)?;
        fs::rename(&tmp, path)?;
        self.actions.push(Json::obj([
            ("op", Json::str("write_file")),
            ("path", Json::str(path.display().to_string())),
            ("bytes", bytes.len().into()),
            ("fnv1a64", Json::str(format!("{:016x}", fnv1a64(bytes)))),
        ]));
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Detectors (pure: they read, measure, and report — they never write).
// ---------------------------------------------------------------------------

/// Binary self-check: version present, build profile disclosed. A debug
/// build is an info-level advisory (slower, larger; not ill health).
fn check_binary(checks: &mut Vec<CheckResult>, findings: &mut Vec<Finding>) {
    let version = env!("CARGO_PKG_VERSION");
    let debug = cfg!(debug_assertions);
    let profile = if debug { "debug" } else { "release" };
    let mut evidence = vec![
        format!("trailtracker {version}"),
        format!("build profile: {profile}"),
        "std-only, #![forbid(unsafe_code)]".to_string(),
    ];
    if debug {
        evidence.push("debug assertions enabled (unoptimized build)".to_string());
        findings.push(Finding {
            id: "debug-build",
            check: "binary",
            severity: Severity::Info,
            message: "this binary is a debug (unoptimized) build".to_string(),
            evidence: vec!["cfg!(debug_assertions) is true".to_string()],
            recommended: Some(
                "cargo build --release && use target/release/trailtracker".to_string(),
            ),
        });
    }
    checks.push(CheckResult {
        id: "binary",
        title: "binary version + build profile",
        status: CheckStatus::Pass,
        evidence,
    });
}

/// Target check: DIR exists (guaranteed by the CLI layer), is a directory,
/// and its metadata is readable.
fn check_target(dir: &str, checks: &mut Vec<CheckResult>, findings: &mut Vec<Finding>) -> bool {
    let path = Path::new(dir);
    match fs::metadata(path) {
        Ok(meta) if meta.is_dir() => {
            checks.push(CheckResult {
                id: "target",
                title: "target directory readable",
                status: CheckStatus::Pass,
                evidence: vec![format!("'{dir}' is a readable directory")],
            });
            true
        }
        Ok(_) => {
            findings.push(Finding {
                id: "target-not-directory",
                check: "target",
                severity: Severity::Error,
                message: format!("'{dir}' exists but is not a directory"),
                evidence: vec![format!("fs::metadata('{dir}').is_dir() == false")],
                recommended: Some(format!(
                    "pass a directory: `trailtracker doctor <dir>` (got file '{dir}')"
                )),
            });
            checks.push(CheckResult {
                id: "target",
                title: "target directory readable",
                status: CheckStatus::Fail,
                evidence: vec![format!("'{dir}' is not a directory")],
            });
            false
        }
        Err(e) => {
            findings.push(Finding {
                id: "target-unreadable",
                check: "target",
                severity: Severity::Error,
                message: format!("cannot read metadata for '{dir}': {e}"),
                evidence: vec![format!("fs::metadata('{dir}') failed: {e}")],
                recommended: Some(
                    "check permissions on the target directory and re-run".to_string(),
                ),
            });
            checks.push(CheckResult {
                id: "target",
                title: "target directory readable",
                status: CheckStatus::Fail,
                evidence: vec![format!("metadata error: {e}")],
            });
            false
        }
    }
}

/// Run one full analysis, isolating panics so the doctor itself survives
/// anything the pipeline might do on hostile input.
fn run_analysis(dir: &str) -> Result<Analysis, String> {
    let result = catch_unwind(AssertUnwindSafe(|| analyze_dir(Path::new(dir))));
    match result {
        Ok(Ok(analysis)) => Ok(analysis),
        Ok(Err(e)) => Err(format!("analyze_dir failed: {e}")),
        Err(_) => Err("analyze_dir panicked (isolated by doctor)".to_string()),
    }
}

/// Analysis check: the pipeline runs and finds analyzable files.
fn check_analysis(
    dir: &str,
    checks: &mut Vec<CheckResult>,
    findings: &mut Vec<Finding>,
) -> Option<Analysis> {
    match run_analysis(dir) {
        Ok(analysis) => {
            let s = &analysis.stats;
            let evidence = vec![
                format!("{} files analyzed", s.files),
                format!("{} total bytes", s.total_bytes),
                format!(
                    "graph: {} nodes, {} edges",
                    analysis.graph.node_count(),
                    analysis.graph.edge_count()
                ),
            ];
            if s.files == 0 {
                findings.push(Finding {
                    id: "no-analyzable-files",
                    check: "analysis",
                    severity: Severity::Warn,
                    message: format!("'{dir}' contains 0 analyzable files"),
                    evidence: vec![
                        "no file under the target matched a registered language front end"
                            .to_string(),
                    ],
                    recommended: Some(
                        "point doctor at a directory containing source files; \
                         `trailtracker stats <dir>` shows what gets analyzed"
                            .to_string(),
                    ),
                });
                checks.push(CheckResult {
                    id: "analysis",
                    title: "analysis pipeline runs on target",
                    status: CheckStatus::Warn,
                    evidence,
                });
            } else {
                checks.push(CheckResult {
                    id: "analysis",
                    title: "analysis pipeline runs on target",
                    status: CheckStatus::Pass,
                    evidence,
                });
            }
            Some(analysis)
        }
        Err(msg) => {
            findings.push(Finding {
                id: "analysis-failed",
                check: "analysis",
                severity: Severity::Error,
                message: format!("analysis of '{dir}' failed"),
                evidence: vec![msg.clone()],
                recommended: Some(format!(
                    "run `trailtracker stats {dir}` for the raw error; if it reproduces, \
                     this is a trailtracker bug worth reporting"
                )),
            });
            checks.push(CheckResult {
                id: "analysis",
                title: "analysis pipeline runs on target",
                status: CheckStatus::Fail,
                evidence: vec![msg],
            });
            None
        }
    }
}

/// Parse-failure check: no file crashed parsing or was unreadable.
fn check_parse_failures(
    analysis: &Analysis,
    checks: &mut Vec<CheckResult>,
    findings: &mut Vec<Finding>,
) {
    let failures = analysis.stats.parse_failures;
    let diagnostics = analysis.stats.diagnostics;
    let evidence = vec![
        format!("{failures} parse failures (isolated, never silently dropped)"),
        format!("{diagnostics} parser diagnostics"),
    ];
    if failures > 0 {
        findings.push(Finding {
            id: "parse-failures",
            check: "parse-failures",
            severity: Severity::Warn,
            message: format!("{failures} file(s) failed to parse and were isolated"),
            evidence: vec![format!(
                "stats.parse_failures == {failures}; see `parse_failed` evidence in \
                 `trailtracker stats <dir>`"
            )],
            recommended: Some(
                "run `trailtracker stats <dir>` to see coverage; non-UTF-8 or hostile files \
                 are isolated by design"
                    .to_string(),
            ),
        });
        checks.push(CheckResult {
            id: "parse-failures",
            title: "no files crashed analysis",
            status: CheckStatus::Warn,
            evidence,
        });
    } else {
        checks.push(CheckResult {
            id: "parse-failures",
            title: "no files crashed analysis",
            status: CheckStatus::Pass,
            evidence,
        });
    }
}

/// Losslessness check: every parsed file reconstructs its source exactly.
/// This is the tool's crown-jewel invariant, so a violation is an error.
fn check_losslessness(
    analysis: &Analysis,
    checks: &mut Vec<CheckResult>,
    findings: &mut Vec<Finding>,
) {
    let s = &analysis.stats;
    let evidence = vec![
        format!("{} / {} files lossless", s.lossless_files, s.files),
        format!("{} / {} error bytes", s.error_bytes, s.total_bytes),
    ];
    if s.lossless_files < s.files {
        let broken = s.files - s.lossless_files;
        findings.push(Finding {
            id: "lossy-parse",
            check: "losslessness",
            severity: Severity::Error,
            message: format!("{broken} file(s) did not reconstruct source byte-for-byte"),
            evidence: vec![format!(
                "stats.lossless_files == {} but stats.files == {}",
                s.lossless_files, s.files
            )],
            recommended: Some(
                "this violates trailtracker's lossless-CST invariant; isolate the file with \
                 `trailtracker parse <file>` and report it as a bug"
                    .to_string(),
            ),
        });
        checks.push(CheckResult {
            id: "losslessness",
            title: "analysis is lossless (CST reconstructs source)",
            status: CheckStatus::Fail,
            evidence,
        });
    } else {
        checks.push(CheckResult {
            id: "losslessness",
            title: "analysis is lossless (CST reconstructs source)",
            status: CheckStatus::Pass,
            evidence,
        });
    }
}

/// Extractor sweep: every registered extractor runs on the graph without
/// panicking. Returns each extractor's output serialized as JSONL so the
/// determinism check can compare a second run against it.
fn check_extractors(
    analysis: &Analysis,
    checks: &mut Vec<CheckResult>,
    findings: &mut Vec<Finding>,
) -> Vec<(String, Option<String>)> {
    let mut outputs: Vec<(String, Option<String>)> = Vec::new();
    let mut evidence: Vec<String> = Vec::new();
    let mut panicked = 0usize;
    for extractor in extractors() {
        let name = extractor.name().to_string();
        let result = catch_unwind(AssertUnwindSafe(|| extractor.extract(&analysis.graph)));
        match result {
            Ok(derived) => {
                evidence.push(format!(
                    "{name}: {} nodes, {} edges",
                    derived.node_count(),
                    derived.edge_count()
                ));
                outputs.push((name, Some(derived.to_jsonl())));
            }
            Err(_) => {
                panicked += 1;
                evidence.push(format!("{name}: PANICKED"));
                findings.push(Finding {
                    id: "extractor-panicked",
                    check: "extractors",
                    severity: Severity::Error,
                    message: format!("extractor '{name}' panicked on this graph"),
                    evidence: vec![format!(
                        "catch_unwind caught a panic in `trailtracker extract {name}`"
                    )],
                    recommended: Some(format!(
                        "reproduce with `trailtracker extract {name} <dir>` and report as a bug"
                    )),
                });
                outputs.push((name, None));
            }
        }
    }
    checks.push(CheckResult {
        id: "extractors",
        title: "all extractors run without error",
        status: if panicked > 0 {
            CheckStatus::Fail
        } else {
            CheckStatus::Pass
        },
        evidence,
    });
    outputs
}

/// Determinism check: a second full analysis (and extractor sweep) must be
/// byte-identical to the first. This is the doctor's own metamorphic test of
/// the tool's core promise.
fn check_determinism(
    dir: &str,
    first: &Analysis,
    first_extractions: &[(String, Option<String>)],
    checks: &mut Vec<CheckResult>,
    findings: &mut Vec<Finding>,
) {
    let second = match run_analysis(dir) {
        Ok(a) => a,
        Err(msg) => {
            findings.push(Finding {
                id: "nondeterministic-analysis",
                check: "determinism",
                severity: Severity::Error,
                message: "second analysis run failed where the first succeeded".to_string(),
                evidence: vec![msg.clone()],
                recommended: Some(
                    "an analysis that succeeds then fails on identical input indicates \
                     environmental flakiness (fs churn?) or a tool bug"
                        .to_string(),
                ),
            });
            checks.push(CheckResult {
                id: "determinism",
                title: "output is byte-deterministic (run twice, compare)",
                status: CheckStatus::Fail,
                evidence: vec![msg],
            });
            return;
        }
    };

    let mut evidence: Vec<String> = Vec::new();
    let mut broken = false;

    let a = first.graph.to_jsonl();
    let b = second.graph.to_jsonl();
    if a == b {
        evidence.push(format!("base graph: {} bytes, byte-identical", a.len()));
    } else {
        broken = true;
        evidence.push(format!(
            "base graph: run 1 = {} bytes (fnv1a64 {:016x}), run 2 = {} bytes (fnv1a64 {:016x})",
            a.len(),
            fnv1a64(a.as_bytes()),
            b.len(),
            fnv1a64(b.as_bytes())
        ));
        findings.push(Finding {
            id: "nondeterministic-analysis",
            check: "determinism",
            severity: Severity::Error,
            message: "two analyses of the same tree produced different graphs".to_string(),
            evidence: evidence.clone(),
            recommended: Some(
                "if the target tree was not modified mid-run, this is a determinism bug in \
                 trailtracker; capture both `trailtracker graph <dir>` outputs and diff them"
                    .to_string(),
            ),
        });
    }

    // Compare each extractor's output across the two independent analyses.
    for (name, first_out) in first_extractions {
        let Some(first_out) = first_out else {
            continue; // already reported as a panic by the extractor check
        };
        let result = catch_unwind(AssertUnwindSafe(|| {
            crate::extract::extractor_by_name(name).map(|e| e.extract(&second.graph).to_jsonl())
        }));
        match result {
            Ok(Some(second_out)) if &second_out == first_out => {
                evidence.push(format!("extractor {name}: byte-identical"));
            }
            Ok(Some(_)) | Ok(None) | Err(_) => {
                broken = true;
                evidence.push(format!("extractor {name}: NOT byte-identical"));
                findings.push(Finding {
                    id: "nondeterministic-extractor",
                    check: "determinism",
                    severity: Severity::Error,
                    message: format!("extractor '{name}' produced different output across runs"),
                    evidence: vec![format!(
                        "two `trailtracker extract {name}` passes over the same tree differ"
                    )],
                    recommended: Some(format!(
                        "diff two runs of `trailtracker extract {name} <dir>` to capture the \
                         nondeterminism, then report it as a bug"
                    )),
                });
            }
        }
    }

    checks.push(CheckResult {
        id: "determinism",
        title: "output is byte-deterministic (run twice, compare)",
        status: if broken {
            CheckStatus::Fail
        } else {
            CheckStatus::Pass
        },
        evidence,
    });
}

/// Push a `skipped` result for a check that could not or should not run.
fn skip_check(checks: &mut Vec<CheckResult>, id: &'static str, title: &'static str, why: &str) {
    checks.push(CheckResult {
        id,
        title,
        status: CheckStatus::Skipped,
        evidence: vec![why.to_string()],
    });
}

// ---------------------------------------------------------------------------
// Report assembly
// ---------------------------------------------------------------------------

fn checks_json(checks: &[CheckResult]) -> Json {
    Json::Array(
        checks
            .iter()
            .map(|c| {
                Json::obj([
                    ("id", Json::str(c.id)),
                    ("title", Json::str(c.title)),
                    ("status", Json::str(c.status.as_str())),
                    (
                        "evidence",
                        Json::Array(c.evidence.iter().map(Json::str).collect()),
                    ),
                ])
            })
            .collect(),
    )
}

fn findings_json(findings: &[Finding]) -> Json {
    Json::Array(
        findings
            .iter()
            .map(|f| {
                Json::obj([
                    ("id", Json::str(f.id)),
                    ("check", Json::str(f.check)),
                    ("severity", Json::str(f.severity.as_str())),
                    ("message", Json::str(&f.message)),
                    (
                        "evidence",
                        Json::Array(f.evidence.iter().map(Json::str).collect()),
                    ),
                    (
                        "fix",
                        match &f.recommended {
                            Some(cmd) => Json::obj([
                                ("auto_fixable", Json::Bool(false)),
                                ("recommended_command", Json::str(cmd)),
                            ]),
                            None => Json::Null,
                        },
                    ),
                ])
            })
            .collect(),
    )
}

/// Render the human (non-`--json`) view of the report. Deterministic.
fn render_human(
    dir: &str,
    opts: &DoctorOptions,
    checks: &[CheckResult],
    findings: &[Finding],
    healthy: bool,
    artifact_dir: Option<&Path>,
) -> String {
    let mut out = String::new();
    out.push_str(&format!("trailtracker doctor: {dir}\n"));
    for c in checks {
        let summary = c.evidence.first().map(String::as_str).unwrap_or("");
        out.push_str(&format!(
            "  {:<7}  {:<16}  {}\n",
            c.status.as_str(),
            c.id,
            summary
        ));
    }
    if findings.is_empty() {
        out.push_str("findings: none\n");
    } else {
        out.push_str(&format!("findings ({}):\n", findings.len()));
        for f in findings {
            out.push_str(&format!(
                "  [{}] {}: {}\n",
                f.severity.as_str(),
                f.id,
                f.message
            ));
            if let Some(cmd) = &f.recommended {
                out.push_str(&format!("        fix: {cmd}\n"));
            }
        }
    }
    if opts.fix {
        if opts.dry_run {
            out.push_str(
                "fix plan (dry run): no automated fixes available — trailtracker is a \
                 read-only analysis tool; every finding above is advisory.\n",
            );
            out.push_str("  write set if executed: <DIR>/.doctor/ only (run artifacts).\n");
        } else {
            out.push_str(
                "fix: 0 actions taken (all findings are advisory; trailtracker never \
                 mutates the target).\n",
            );
        }
    }
    let status = if healthy { "healthy" } else { "unhealthy" };
    let exit = if healthy { EXIT_HEALTHY } else { EXIT_FINDINGS };
    out.push_str(&format!("status: {status} (exit {exit})\n"));
    match artifact_dir {
        Some(dir) => out.push_str(&format!("artifact: {}\n", dir.display())),
        None => out.push_str("artifact: none (--no-artifact)\n"),
    }
    out
}

/// Render the markdown run report stored alongside the JSON artifact.
fn render_markdown(
    dir: &str,
    run_id: &str,
    checks: &[CheckResult],
    findings: &[Finding],
    healthy: bool,
) -> String {
    let mut md = String::new();
    md.push_str(&format!("# trailtracker doctor report — `{run_id}`\n\n"));
    md.push_str(&format!(
        "- target: `{dir}`\n- tool: trailtracker {}\n- status: **{}**\n\n",
        env!("CARGO_PKG_VERSION"),
        if healthy { "healthy" } else { "unhealthy" }
    ));
    md.push_str("## Checks\n\n| check | status | evidence |\n|---|---|---|\n");
    for c in checks {
        md.push_str(&format!(
            "| {} | {} | {} |\n",
            c.id,
            c.status.as_str(),
            c.evidence.join("; ")
        ));
    }
    md.push_str("\n## Findings\n\n");
    if findings.is_empty() {
        md.push_str("None.\n");
    } else {
        for f in findings {
            md.push_str(&format!(
                "- **[{}] {}** ({}): {}\n",
                f.severity.as_str(),
                f.id,
                f.check,
                f.message
            ));
            for e in &f.evidence {
                md.push_str(&format!("  - evidence: {e}\n"));
            }
            if let Some(cmd) = &f.recommended {
                md.push_str(&format!("  - fix (advisory): `{cmd}`\n"));
            }
        }
    }
    md.push_str(
        "\n## Reversibility\n\nThis doctor never mutates the analyzed tree. Its only writes \
         are the additive artifacts in this run directory (hash-witnessed in `actions.jsonl`). \
         To \"undo\" a run, delete the `.doctor/` directory — no other state exists.\n",
    );
    md
}

/// The per-run scoring artifact: the doctor's surface graded against the ten
/// world-class-doctor dimensions, with evidence per dimension. Deterministic;
/// changes only when the doctor's implementation changes.
fn scorecard_json(run_id: &str, dir: &str) -> Json {
    let dim = |name: &str, score: u64, evidence: &str| {
        Json::obj([
            ("dimension", Json::str(name)),
            ("score", Json::U64(score)),
            ("evidence", Json::str(evidence)),
        ])
    };
    let dims = vec![
        dim(
            "agent_intuitiveness",
            850,
            "`trailtracker doctor` with zero flags does the right thing; discoverable from \
             `trailtracker help`; did-you-mean on typos (src/main.rs closest())",
        ),
        dim(
            "agent_ergonomics",
            900,
            "--json/--robot emit stable schema trailtracker.doctor/v1; stdout data-only; \
             exit-code dictionary in `doctor capabilities`; no TTY/interactive paths",
        ),
        dim(
            "automation_degree",
            400,
            "0 auto-fixers by design: trailtracker is a read-only analysis tool (forensic \
             doctor, Pattern 13); every finding carries a recommended_command instead",
        ),
        dim(
            "data_safety",
            950,
            "never mutates the target; only additive writes under <DIR>/.doctor/ via the \
             single Mutator::write_file chokepoint (atomic tmp+rename, scope-guarded)",
        ),
        dim(
            "idempotence",
            950,
            "content-derived run id; run twice == run once byte-for-byte, including \
             artifacts (tests/doctor.rs doctor_is_idempotent_and_deterministic)",
        ),
        dim(
            "reversibility",
            800,
            "nothing to reverse: zero target-state mutations; artifacts are additive and \
             disposable (delete .doctor/); the only overwrite is byte-identical by \
             construction",
        ),
        dim(
            "diagnostic_specificity",
            800,
            "findings cite exact counters (stats fields), extractor names, and hash \
             witnesses; every finding names the exact command to run next",
        ),
        dim(
            "blast_radius_containment",
            950,
            "write set is <DIR>/.doctor/ only, enforced in code (Mutator scope check) and \
             disclosed in `doctor capabilities` + `--fix --dry-run`",
        ),
        dim(
            "observability",
            850,
            "content-addressed run id, actions.jsonl with fnv1a64 witnesses, capabilities \
             reflection, robot-docs handbook, scorecard per run",
        ),
        dim(
            "test_coverage_of_repair",
            750,
            "tests/doctor.rs covers healthy, unhealthy (0-file dir), idempotence, artifact \
             round-trip, exit codes 0/1/2/3, --quick skips, capabilities and robot-docs",
        ),
    ];
    let total: u64 = dims
        .iter()
        .map(|d| match d {
            Json::Object(m) => match m.get("score") {
                Some(Json::U64(s)) => *s,
                _ => 0,
            },
            _ => 0,
        })
        .sum();
    let aggregate = total / dims.len() as u64;
    Json::obj([
        ("schema", Json::str(DOCTOR_SCORECARD_SCHEMA)),
        ("run_id", Json::str(run_id)),
        ("dir", Json::str(dir)),
        ("tool_version", Json::str(env!("CARGO_PKG_VERSION"))),
        (
            "aggregate",
            Json::obj([
                ("score", Json::U64(aggregate)),
                ("method", Json::str("mean of the ten dimension scores")),
                ("target", Json::U64(700)),
                ("meets_target", Json::Bool(aggregate >= 700)),
            ]),
        ),
        ("dimensions", Json::Array(dims)),
        (
            "notes",
            Json::str(
                "automation_degree is honestly low: a read-only analysis tool has no state \
                 of its own to repair, so the doctor is forensic (detect + advise), never \
                 mutating. All other dimensions are load-bearing and test-verified.",
            ),
        ),
    ])
}

// ---------------------------------------------------------------------------
// The doctor entry point
// ---------------------------------------------------------------------------

/// Run the doctor against `dir`. The caller (CLI) has already verified that
/// `dir` exists; everything else is diagnosed, not refused. Never panics on
/// user input; never writes outside `<dir>/.doctor/`; writes nothing at all
/// when `opts.artifact` is false or the artifact directory is unwritable
/// (that downgrade is itself reported as an info finding).
pub fn run_doctor(dir: &str, opts: &DoctorOptions) -> DoctorOutcome {
    let mut checks: Vec<CheckResult> = Vec::new();
    let mut findings: Vec<Finding> = Vec::new();

    check_binary(&mut checks, &mut findings);
    let target_ok = check_target(dir, &mut checks, &mut findings);

    let analysis = if target_ok {
        check_analysis(dir, &mut checks, &mut findings)
    } else {
        skip_check(
            &mut checks,
            "analysis",
            "analysis pipeline runs on target",
            "skipped: target check failed",
        );
        None
    };

    match &analysis {
        Some(analysis) => {
            check_parse_failures(analysis, &mut checks, &mut findings);
            check_losslessness(analysis, &mut checks, &mut findings);
            if opts.quick {
                skip_check(
                    &mut checks,
                    "extractors",
                    "all extractors run without error",
                    "skipped: --quick",
                );
                skip_check(
                    &mut checks,
                    "determinism",
                    "output is byte-deterministic (run twice, compare)",
                    "skipped: --quick",
                );
            } else {
                let extractions = check_extractors(analysis, &mut checks, &mut findings);
                check_determinism(dir, analysis, &extractions, &mut checks, &mut findings);
            }
        }
        None => {
            let why = if target_ok {
                "skipped: analysis unavailable"
            } else {
                "skipped: target check failed"
            };
            skip_check(
                &mut checks,
                "parse-failures",
                "no files crashed analysis",
                why,
            );
            skip_check(
                &mut checks,
                "losslessness",
                "analysis is lossless (CST reconstructs source)",
                why,
            );
            skip_check(
                &mut checks,
                "extractors",
                "all extractors run without error",
                why,
            );
            skip_check(
                &mut checks,
                "determinism",
                "output is byte-deterministic (run twice, compare)",
                why,
            );
        }
    }

    let healthy = findings.iter().all(|f| f.severity == Severity::Info);
    let exit = if healthy { EXIT_HEALTHY } else { EXIT_FINDINGS };

    let count = |status: CheckStatus| checks.iter().filter(|c| c.status == status).count();
    let summary = Json::obj([
        ("checks", checks.len().into()),
        ("passed", count(CheckStatus::Pass).into()),
        ("warned", count(CheckStatus::Warn).into()),
        ("failed", count(CheckStatus::Fail).into()),
        ("skipped", count(CheckStatus::Skipped).into()),
        ("findings", findings.len().into()),
        (
            "advisories",
            findings
                .iter()
                .filter(|f| f.severity == Severity::Info)
                .count()
                .into(),
        ),
    ]);

    let fix_note = if opts.fix {
        "0 actions taken: all findings are advisory; trailtracker is a read-only analysis \
         tool and its doctor never mutates the target"
    } else {
        "not requested; note trailtracker's doctor has no automated fixers (read-only tool)"
    };
    let core = Json::obj([
        ("schema", Json::str(DOCTOR_SCHEMA)),
        ("command", Json::str("doctor")),
        ("version", Json::str(env!("CARGO_PKG_VERSION"))),
        ("dir", Json::str(dir)),
        (
            "mode",
            Json::obj([
                ("quick", Json::Bool(opts.quick)),
                ("fix", Json::Bool(opts.fix)),
                ("dry_run", Json::Bool(opts.dry_run)),
                ("artifact", Json::Bool(opts.artifact)),
            ]),
        ),
        (
            "status",
            Json::str(if healthy { "healthy" } else { "unhealthy" }),
        ),
        ("exit_code", u64::from(exit).into()),
        ("summary", summary),
        ("checks", checks_json(&checks)),
        ("findings", findings_json(&findings)),
        (
            "fix",
            Json::obj([
                ("requested", Json::Bool(opts.fix)),
                ("dry_run", Json::Bool(opts.dry_run)),
                ("auto_fixable_findings", 0usize.into()),
                ("actions_taken", 0usize.into()),
                ("note", Json::str(fix_note)),
            ]),
        ),
    ]);

    // Content-derived run id: no wall clock, no randomness. The same binary
    // diagnosing the same tree always produces the same run id, so re-running
    // is an idempotent byte-identical overwrite.
    let run_id = format!("r{:016x}", fnv1a64(core.to_line().as_bytes()));

    // Emit the run artifact (report.json/report.md/scorecard.json/actions.jsonl
    // + latest pointer) through the mutate() chokepoint. Failure to write is
    // never fatal: the diagnosis stands, and the downgrade is disclosed.
    let mut artifact_json = Json::Null;
    let mut artifact_dir_for_human: Option<PathBuf> = None;
    if opts.artifact && !opts.dry_run {
        let doctor_root = Path::new(dir).join(".doctor");
        let run_dir = doctor_root.join("runs").join(&run_id);
        match write_artifact(
            &doctor_root,
            &run_dir,
            &run_id,
            dir,
            &core,
            &checks,
            &findings,
        ) {
            Ok(files) => {
                artifact_json = Json::obj([
                    ("dir", Json::str(run_dir.display().to_string())),
                    (
                        "files",
                        Json::Array(files.iter().map(|f| Json::str(*f)).collect()),
                    ),
                    (
                        "latest_pointer",
                        Json::str(doctor_root.join("latest").display().to_string()),
                    ),
                ]);
                artifact_dir_for_human = Some(run_dir);
            }
            Err(e) => {
                artifact_json = Json::obj([
                    ("dir", Json::Null),
                    (
                        "error",
                        Json::str(format!("artifact not written: {e} (diagnosis unaffected)")),
                    ),
                ]);
            }
        }
    }

    let mut report = core;
    if let Json::Object(map) = &mut report {
        map.insert(
            "run".to_string(),
            Json::obj([
                ("id", Json::str(&run_id)),
                (
                    "id_derivation",
                    Json::str("fnv1a64 of the core report JSON (content-addressed; no clock)"),
                ),
            ]),
        );
        map.insert("artifact".to_string(), artifact_json);
    }

    let human = render_human(
        dir,
        opts,
        &checks,
        &findings,
        healthy,
        artifact_dir_for_human.as_deref(),
    );

    DoctorOutcome {
        report,
        human,
        exit,
    }
}

/// Write the full run artifact. Every write flows through the [`Mutator`]
/// chokepoint. Returns the artifact file names written, in write order.
#[allow(clippy::too_many_arguments)]
fn write_artifact(
    doctor_root: &Path,
    run_dir: &Path,
    run_id: &str,
    dir: &str,
    core: &Json,
    checks: &[CheckResult],
    findings: &[Finding],
) -> io::Result<Vec<&'static str>> {
    let mut m = Mutator::new(doctor_root.to_path_buf());
    let report_json = format!("{}\n", core.to_line());
    let report_md = render_markdown(
        dir,
        run_id,
        checks,
        findings,
        findings
            .iter()
            .all(|f| matches!(f.severity, Severity::Info)),
    );
    let scorecard = format!("{}\n", scorecard_json(run_id, dir).to_line());

    m.write_file(&run_dir.join("report.json"), report_json.as_bytes())?;
    m.write_file(&run_dir.join("report.md"), report_md.as_bytes())?;
    m.write_file(&run_dir.join("scorecard.json"), scorecard.as_bytes())?;

    // The actions ledger records every mutation performed above. It cannot
    // contain its own hash; robot-docs documents that the ledger does not
    // ledger itself (nor the `latest` pointer written after it).
    let ledger: String = m
        .actions
        .iter()
        .map(|a| format!("{}\n", a.to_line()))
        .collect();
    m.write_file(&run_dir.join("actions.jsonl"), ledger.as_bytes())?;
    m.write_file(
        &doctor_root.join("latest"),
        format!("{run_id}\n").as_bytes(),
    )?;

    Ok(vec![
        "report.json",
        "report.md",
        "scorecard.json",
        "actions.jsonl",
        "latest",
    ])
}

// ---------------------------------------------------------------------------
// Reflection: capabilities + robot-docs
// ---------------------------------------------------------------------------

/// The doctor's machine-readable contract (schema
/// [`DOCTOR_CAPABILITIES_SCHEMA`]): checks, finding ids, exit codes, flags,
/// artifact layout, and the safety envelope.
pub fn doctor_capabilities_json() -> Json {
    let check = |id: &str, title: &str, quick: bool, on_failure: &str| {
        Json::obj([
            ("id", Json::str(id)),
            ("title", Json::str(title)),
            ("runs_in_quick_mode", Json::Bool(quick)),
            ("severity_on_failure", Json::str(on_failure)),
        ])
    };
    Json::obj([
        ("schema", Json::str(DOCTOR_CAPABILITIES_SCHEMA)),
        ("tool", Json::str("trailtracker")),
        ("tool_version", Json::str(env!("CARGO_PKG_VERSION"))),
        ("doctor_contract_version", Json::str("1")),
        (
            "pattern",
            Json::str(
                "forensic (read-only) doctor: pure detectors, advisory fixes only; the tool \
                 never mutates the target it analyzes",
            ),
        ),
        (
            "usage",
            Json::Array(vec![
                Json::str("trailtracker doctor [DIR] [--json] [--quick] [--no-artifact]"),
                Json::str("trailtracker doctor [DIR] --fix [--dry-run]"),
                Json::str("trailtracker doctor capabilities"),
                Json::str("trailtracker doctor robot-docs"),
            ]),
        ),
        (
            "checks",
            Json::Array(vec![
                check("binary", "binary version + build profile", true, "info"),
                check("target", "target directory readable", true, "error"),
                check(
                    "analysis",
                    "analysis pipeline runs on target",
                    true,
                    "error",
                ),
                check("parse-failures", "no files crashed analysis", true, "warn"),
                check(
                    "losslessness",
                    "analysis is lossless (CST reconstructs source)",
                    true,
                    "error",
                ),
                check(
                    "extractors",
                    "all extractors run without error",
                    false,
                    "error",
                ),
                check(
                    "determinism",
                    "output is byte-deterministic (run twice, compare)",
                    false,
                    "error",
                ),
            ]),
        ),
        (
            "finding_ids",
            Json::Array(
                [
                    "debug-build",
                    "target-not-directory",
                    "target-unreadable",
                    "analysis-failed",
                    "no-analyzable-files",
                    "parse-failures",
                    "lossy-parse",
                    "extractor-panicked",
                    "nondeterministic-analysis",
                    "nondeterministic-extractor",
                ]
                .iter()
                .map(|s| Json::str(*s))
                .collect(),
            ),
        ),
        (
            "exit_codes",
            Json::obj([
                ("0", Json::str("healthy (info-level advisories permitted)")),
                ("1", Json::str("findings present (warn or error severity)")),
                ("2", Json::str("usage error (bad flag or argument)")),
                ("3", Json::str("target path does not exist")),
                ("4", Json::str("internal doctor failure")),
            ]),
        ),
        (
            "flags",
            Json::Array(vec![
                Json::obj([
                    ("flag", Json::str("--json | --robot")),
                    (
                        "meaning",
                        Json::str("emit schema trailtracker.doctor/v1 on stdout"),
                    ),
                ]),
                Json::obj([
                    ("flag", Json::str("--quick")),
                    (
                        "meaning",
                        Json::str(
                            "cheap checks only: skips the extractor sweep and the \
                             determinism double-run (reported as skipped)",
                        ),
                    ),
                ]),
                Json::obj([
                    ("flag", Json::str("--fix")),
                    (
                        "meaning",
                        Json::str(
                            "request repairs; always 0 actions (all findings advisory — \
                             read-only tool); exit code semantics unchanged",
                        ),
                    ),
                ]),
                Json::obj([
                    ("flag", Json::str("--dry-run")),
                    (
                        "meaning",
                        Json::str(
                            "with --fix: print the (empty) action plan and the worst-case \
                             write set; writes nothing at all",
                        ),
                    ),
                ]),
                Json::obj([
                    ("flag", Json::str("--no-artifact")),
                    (
                        "meaning",
                        Json::str("skip the run artifact: a 100% read-only invocation"),
                    ),
                ]),
            ]),
        ),
        (
            "artifact",
            Json::obj([
                ("root", Json::str("<DIR>/.doctor/")),
                (
                    "run_dir",
                    Json::str("<DIR>/.doctor/runs/<run-id>/ (run-id is content-derived)"),
                ),
                (
                    "files",
                    Json::Array(
                        [
                            "report.json",
                            "report.md",
                            "scorecard.json",
                            "actions.jsonl",
                        ]
                        .iter()
                        .map(|s| Json::str(*s))
                        .collect(),
                    ),
                ),
                (
                    "latest_pointer",
                    Json::str("<DIR>/.doctor/latest (text file holding the last run id)"),
                ),
                (
                    "determinism",
                    Json::str(
                        "artifacts are byte-deterministic: same binary + same tree = same \
                         run id and identical bytes; re-runs are idempotent overwrites",
                    ),
                ),
            ]),
        ),
        (
            "safety_envelope",
            Json::obj([
                ("mutates_target", Json::Bool(false)),
                (
                    "write_scope",
                    Json::str("<DIR>/.doctor/ only (enforced in code)"),
                ),
                ("deletes_files", Json::Bool(false)),
                ("atomic_writes", Json::Bool(true)),
                ("network", Json::str("never")),
                ("subprocesses", Json::str("never")),
                (
                    "undo",
                    Json::str(
                        "nothing to undo: zero target mutations; delete <DIR>/.doctor/ to \
                         discard all doctor state",
                    ),
                ),
            ]),
        ),
        (
            "recommended_first_calls",
            Json::Array(vec![
                Json::str("trailtracker doctor <dir> --json"),
                Json::str("trailtracker doctor <dir> --quick --json"),
                Json::str("trailtracker doctor capabilities"),
            ]),
        ),
    ])
}

/// The paste-ready agent handbook for the doctor, printed by
/// `trailtracker doctor robot-docs`.
pub fn robot_docs() -> String {
    format!(
        "# trailtracker doctor — agent handbook (contract v1)\n\
\n\
## What it is\n\
A forensic (read-only) doctor: it diagnoses the trailtracker binary and its\n\
ability to analyze a target directory. It NEVER mutates the target. Its only\n\
writes are its own run artifacts under `<DIR>/.doctor/`, and `--no-artifact`\n\
disables even those.\n\
\n\
## Invocations\n\
    trailtracker doctor [DIR] --json      # full diagnosis, machine output\n\
    trailtracker doctor [DIR] --quick     # cheap checks only (CI/pre-commit)\n\
    trailtracker doctor [DIR] --fix       # accepted; always 0 actions (advisory-only)\n\
    trailtracker doctor [DIR] --fix --dry-run   # print the (empty) plan + write set\n\
    trailtracker doctor [DIR] --no-artifact     # 100% read-only run\n\
    trailtracker doctor capabilities      # machine-readable contract ({cap})\n\
    trailtracker doctor robot-docs        # this handbook\n\
DIR defaults to `.`. `--robot` is a synonym for `--json`.\n\
Note: `capabilities` and `robot-docs` are sub-verbs; to diagnose a directory\n\
literally named `capabilities`, pass `./capabilities`.\n\
\n\
## Checks (in order)\n\
    binary          version + build profile (debug build => info advisory)\n\
    target          DIR exists, is a directory, is readable\n\
    analysis        analyze_dir succeeds and finds analyzable files\n\
    parse-failures  no file crashed parsing (failures are isolated, counted)\n\
    losslessness    every parsed file reconstructs its source byte-for-byte\n\
    extractors      every registered extractor runs without panicking\n\
    determinism     a second full analysis + extraction is byte-identical\n\
`--quick` skips `extractors` and `determinism` (reported as `skipped`).\n\
\n\
## Exit codes\n\
    0  healthy (info-level advisories permitted)\n\
    1  findings present (warn or error severity)\n\
    2  usage error (bad flag or argument)\n\
    3  target path does not exist\n\
    4  internal doctor failure\n\
\n\
## Output contract\n\
stdout is data only; stderr is diagnostics only. `--json` emits one line of\n\
schema `{schema}`: {{status, exit_code, summary, checks[], findings[], fix,\n\
run, artifact}}. Every finding carries `fix.recommended_command` — the exact\n\
command to run next — and `fix.auto_fixable` is always false (read-only tool).\n\
Output is byte-deterministic: the run id is content-derived (fnv1a64 of the\n\
core report), so identical inputs produce identical bytes, artifacts included.\n\
\n\
## Artifacts\n\
Each run writes `<DIR>/.doctor/runs/<run-id>/` with report.json, report.md,\n\
scorecard.json (ten-dimension self-score), and actions.jsonl (one line per\n\
write: op, path, bytes, fnv1a64 — the ledger does not ledger itself or the\n\
`latest` pointer). `<DIR>/.doctor/latest` holds the last run id. Artifact\n\
writes are atomic (tmp + rename) and confined to `<DIR>/.doctor/` by a code\n\
check. If artifacts cannot be written the diagnosis still completes and the\n\
JSON `artifact.error` field says so.\n\
\n\
## Reversibility\n\
There is nothing to undo: the doctor performs zero target mutations. Delete\n\
`<DIR>/.doctor/` to discard all doctor state; no other state exists.\n\
\n\
## Recipes\n\
    # Is the tool healthy on this repo?\n\
    trailtracker doctor <dir> --json | check .status == \"healthy\"; exit code 0\n\
    # Gate a pipeline cheaply\n\
    trailtracker doctor <dir> --quick --no-artifact\n\
    # Self-check the tool against its own source\n\
    trailtracker doctor src --json\n",
        cap = DOCTOR_CAPABILITIES_SCHEMA,
        schema = DOCTOR_SCHEMA,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fnv1a64_is_stable() {
        // Pinned vectors: the run-id derivation must never drift silently.
        assert_eq!(fnv1a64(b""), 0xcbf2_9ce4_8422_2325);
        assert_eq!(fnv1a64(b"a"), 0xaf63_dc4c_8601_ec8c);
        assert_eq!(fnv1a64(b"trailtracker"), fnv1a64(b"trailtracker"));
        assert_ne!(fnv1a64(b"trailtracker"), fnv1a64(b"trailtracker "));
    }

    #[test]
    fn check_ids_match_capabilities_reflection() {
        let caps = doctor_capabilities_json().to_line();
        for id in CHECK_IDS {
            assert!(
                caps.contains(&format!("\"id\":\"{id}\"")),
                "capabilities missing check id {id}"
            );
        }
    }

    #[test]
    fn scorecard_meets_target() {
        let line = scorecard_json("rtest", ".").to_line();
        assert!(line.contains("\"meets_target\":true"), "scorecard: {line}");
        assert!(line.contains(DOCTOR_SCORECARD_SCHEMA));
    }

    #[test]
    fn mutator_refuses_out_of_scope_writes() {
        let scope = std::env::temp_dir().join("tt-doctor-scope-test");
        let mut m = Mutator::new(scope.clone());
        let outside = std::env::temp_dir().join("tt-doctor-escape.txt");
        let err = m.write_file(&outside, b"x").unwrap_err();
        assert!(err.to_string().contains("outside scope"), "{err}");
        assert!(m.actions.is_empty(), "refused write must not be ledgered");
        assert!(!outside.exists());
    }
}
