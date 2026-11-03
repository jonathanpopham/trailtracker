//! Black-box integration tests for `trailtracker doctor`.
//!
//! These drive the compiled binary against the vendored corpus and against
//! purpose-built temp directories, asserting the doctor's contract: exit-code
//! dictionary, stable `--json` schema, idempotent byte-deterministic output
//! (artifacts included), the mutate()-chokepoint artifact ledger, and the
//! reflection sub-verbs (`capabilities`, `robot-docs`).

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn bin() -> Command {
    Command::new(env!("CARGO_BIN_EXE_trailtracker"))
}

fn run(args: &[&str]) -> Output {
    bin().args(args).output().expect("run trailtracker")
}

fn stdout(out: &Output) -> String {
    String::from_utf8(out.stdout.clone()).expect("utf8 stdout")
}

const CORPUS: &str = "eval/corpus/calc";

/// A unique temp directory that cleans itself up (tests must not litter).
struct TempDir(PathBuf);

impl TempDir {
    fn new(tag: &str) -> TempDir {
        let dir = std::env::temp_dir().join(format!("tt-doctor-test-{tag}-{}", std::process::id()));
        // Stale leftovers from a killed prior run: rebuild from scratch.
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).expect("create temp dir");
        TempDir(dir)
    }

    fn path(&self) -> &Path {
        &self.0
    }

    fn as_str(&self) -> &str {
        self.0.to_str().expect("utf8 temp path")
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

// ---------------------------------------------------------------------------
// Healthy path
// ---------------------------------------------------------------------------

#[test]
fn doctor_reports_healthy_corpus_with_exit_0() {
    let out = run(&["doctor", CORPUS, "--no-artifact"]);
    assert_eq!(out.status.code(), Some(0), "healthy corpus must exit 0");
    let text = stdout(&out);
    assert!(text.contains("status: healthy"), "not healthy:\n{text}");
    // Every check appears in the human rendering.
    for id in [
        "binary",
        "target",
        "analysis",
        "parse-failures",
        "losslessness",
        "extractors",
        "determinism",
    ] {
        assert!(text.contains(id), "missing check {id}:\n{text}");
    }
    assert!(
        out.stderr.is_empty(),
        "healthy run must not write to stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn doctor_json_emits_stable_schema() {
    let out = run(&["doctor", CORPUS, "--no-artifact", "--json"]);
    assert_eq!(out.status.code(), Some(0));
    let json = stdout(&out);
    assert!(
        json.starts_with('{') && json.trim_end().ends_with('}'),
        "stdout must be one JSON object:\n{json}"
    );
    for field in [
        "\"schema\":\"trailtracker.doctor/v1\"",
        "\"status\":\"healthy\"",
        "\"exit_code\":0",
        "\"checks\":[",
        "\"findings\":[",
        "\"summary\":{",
        "\"run\":{",
        "\"artifact\":null",
        "\"fix\":{",
    ] {
        assert!(json.contains(field), "missing {field}:\n{json}");
    }
    // The test harness runs a debug binary: the debug-build advisory must be
    // present (proving detection) yet must NOT flip health (info severity).
    assert!(json.contains("\"id\":\"debug-build\""), "advisory missing");
    assert!(json.contains("\"severity\":\"info\""));
    assert!(
        json.contains("\"recommended_command\":\"cargo build --release"),
        "advisory must name the exact fix command"
    );
}

#[test]
fn doctor_robot_flag_is_json_synonym() {
    let a = run(&["doctor", CORPUS, "--no-artifact", "--json"]);
    let b = run(&["doctor", CORPUS, "--no-artifact", "--robot"]);
    assert_eq!(stdout(&a), stdout(&b), "--robot must equal --json");
}

// ---------------------------------------------------------------------------
// Idempotence + determinism (the doctor's own crown jewel)
// ---------------------------------------------------------------------------

#[test]
fn doctor_is_idempotent_and_deterministic() {
    let tmp = TempDir::new("idem");
    fs::write(tmp.path().join("lib.rs"), "pub fn answer() -> u32 { 42 }\n").expect("write fixture");

    let first = run(&["doctor", tmp.as_str(), "--json"]);
    assert_eq!(first.status.code(), Some(0));
    let report_path = || {
        let json = stdout(&first);
        let key = "\"dir\":\"";
        // artifact.dir is the only path-valued "dir" besides the target; find
        // the one under .doctor.
        json.match_indices(key)
            .map(|(i, _)| {
                let rest = &json[i + key.len()..];
                rest[..rest.find('"').unwrap()].to_string()
            })
            .find(|p| p.contains(".doctor"))
            .expect("artifact dir in report")
    };
    let run_dir = PathBuf::from(report_path());
    for f in [
        "report.json",
        "report.md",
        "scorecard.json",
        "actions.jsonl",
    ] {
        assert!(run_dir.join(f).exists(), "artifact file {f} missing");
    }
    let report1 = fs::read(run_dir.join("report.json")).expect("read report");

    // Second run: byte-identical stdout AND byte-identical artifact (the
    // content-derived run id makes the rewrite an idempotent overwrite).
    let second = run(&["doctor", tmp.as_str(), "--json"]);
    assert_eq!(second.status.code(), Some(0));
    assert_eq!(
        stdout(&first),
        stdout(&second),
        "doctor stdout must be byte-deterministic"
    );
    let report2 = fs::read(run_dir.join("report.json")).expect("read report again");
    assert_eq!(
        report1, report2,
        "artifact must be byte-identical on re-run"
    );

    // Exactly one run directory: no accumulation from identical re-runs.
    let runs: Vec<_> = fs::read_dir(tmp.path().join(".doctor/runs"))
        .expect("runs dir")
        .collect();
    assert_eq!(
        runs.len(),
        1,
        "identical re-runs must not mint new run dirs"
    );

    // The latest pointer holds the run id.
    let latest = fs::read_to_string(tmp.path().join(".doctor/latest")).expect("latest");
    assert_eq!(
        latest.trim(),
        run_dir.file_name().unwrap().to_str().unwrap(),
        "latest pointer must hold the run id"
    );
}

#[test]
fn doctor_artifact_ledger_witnesses_every_write() {
    let tmp = TempDir::new("ledger");
    fs::write(tmp.path().join("lib.rs"), "pub fn f() {}\n").expect("write fixture");
    let out = run(&["doctor", tmp.as_str()]);
    assert_eq!(out.status.code(), Some(0));

    let runs_root = tmp.path().join(".doctor/runs");
    let run_dir = fs::read_dir(&runs_root)
        .expect("runs dir")
        .next()
        .expect("one run")
        .expect("entry")
        .path();
    let ledger = fs::read_to_string(run_dir.join("actions.jsonl")).expect("ledger");
    // One line per pre-ledger artifact write, each with op/path/bytes/hash.
    let lines: Vec<&str> = ledger.lines().collect();
    assert_eq!(lines.len(), 3, "ledger must witness the 3 prior writes");
    for (line, file) in lines
        .iter()
        .zip(["report.json", "report.md", "scorecard.json"])
    {
        assert!(line.contains("\"op\":\"write_file\""), "bad ledger: {line}");
        assert!(line.contains(file), "ledger order wrong: {line}");
        assert!(line.contains("\"fnv1a64\":\""), "missing hash: {line}");
    }

    // The doctor writes ONLY inside .doctor: the target dir gains exactly the
    // fixture file + .doctor.
    let entries: Vec<String> = fs::read_dir(tmp.path())
        .expect("target dir")
        .map(|e| e.expect("entry").file_name().to_string_lossy().into_owned())
        .collect();
    let mut sorted = entries.clone();
    sorted.sort();
    assert_eq!(sorted, vec![".doctor", "lib.rs"], "write scope violated");
}

#[test]
fn doctor_scorecard_meets_rubric_target() {
    let tmp = TempDir::new("score");
    fs::write(tmp.path().join("lib.rs"), "pub fn f() {}\n").expect("write fixture");
    let out = run(&["doctor", tmp.as_str()]);
    assert_eq!(out.status.code(), Some(0));
    let runs_root = tmp.path().join(".doctor/runs");
    let run_dir = fs::read_dir(&runs_root)
        .expect("runs dir")
        .next()
        .expect("one run")
        .expect("entry")
        .path();
    let scorecard = fs::read_to_string(run_dir.join("scorecard.json")).expect("scorecard");
    assert!(scorecard.contains("\"schema\":\"trailtracker.doctor-scorecard/v1\""));
    assert!(
        scorecard.contains("\"meets_target\":true"),
        "aggregate rubric score must be >= 700:\n{scorecard}"
    );
    // All ten dimensions present with evidence.
    for dim in [
        "agent_intuitiveness",
        "agent_ergonomics",
        "automation_degree",
        "data_safety",
        "idempotence",
        "reversibility",
        "diagnostic_specificity",
        "blast_radius_containment",
        "observability",
        "test_coverage_of_repair",
    ] {
        assert!(scorecard.contains(dim), "missing dimension {dim}");
    }
}

#[test]
fn doctor_no_artifact_writes_nothing() {
    let tmp = TempDir::new("noart");
    fs::write(tmp.path().join("lib.rs"), "pub fn f() {}\n").expect("write fixture");
    let out = run(&["doctor", tmp.as_str(), "--no-artifact"]);
    assert_eq!(out.status.code(), Some(0));
    assert!(
        !tmp.path().join(".doctor").exists(),
        "--no-artifact must be 100% read-only"
    );
}

#[test]
fn doctor_fix_dry_run_writes_nothing_and_prints_plan() {
    let tmp = TempDir::new("dryrun");
    fs::write(tmp.path().join("lib.rs"), "pub fn f() {}\n").expect("write fixture");
    let out = run(&["doctor", tmp.as_str(), "--fix", "--dry-run"]);
    assert_eq!(out.status.code(), Some(0));
    let text = stdout(&out);
    assert!(text.contains("fix plan (dry run)"), "plan missing:\n{text}");
    assert!(
        text.contains(".doctor/ only"),
        "plan must disclose the worst-case write set:\n{text}"
    );
    assert!(
        !tmp.path().join(".doctor").exists(),
        "--dry-run must write nothing at all"
    );
}

// ---------------------------------------------------------------------------
// Unhealthy + error paths (exit-code dictionary)
// ---------------------------------------------------------------------------

#[test]
fn doctor_flags_empty_dir_as_unhealthy_exit_1() {
    let tmp = TempDir::new("empty");
    let out = run(&["doctor", tmp.as_str(), "--no-artifact", "--json"]);
    assert_eq!(out.status.code(), Some(1), "0 analyzable files must exit 1");
    let json = stdout(&out);
    assert!(json.contains("\"status\":\"unhealthy\""));
    assert!(json.contains("\"id\":\"no-analyzable-files\""));
    assert!(json.contains("\"severity\":\"warn\""));
    assert!(json.contains("\"exit_code\":1"));
}

#[test]
fn doctor_missing_dir_exits_3_like_every_other_command() {
    let out = run(&["doctor", "/nonexistent-tt-doctor-target"]);
    assert_eq!(out.status.code(), Some(3));
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("does not exist"), "stderr: {err}");
    assert!(err.contains("fix:"), "error must carry a fix line: {err}");
}

#[test]
fn doctor_usage_errors_exit_2() {
    let out = run(&["doctor", ".", "--bogus"]);
    assert_eq!(out.status.code(), Some(2), "unknown flag must exit 2");
    assert!(String::from_utf8_lossy(&out.stderr).contains("unknown flag"));

    let out = run(&["doctor", ".", "--dry-run"]);
    assert_eq!(out.status.code(), Some(2), "--dry-run without --fix");
    assert!(String::from_utf8_lossy(&out.stderr).contains("--fix"));

    let out = run(&["doctor", "a", "b"]);
    assert_eq!(out.status.code(), Some(2), "two positionals must exit 2");
}

// ---------------------------------------------------------------------------
// Quick mode
// ---------------------------------------------------------------------------

#[test]
fn doctor_quick_skips_expensive_checks() {
    let out = run(&["doctor", CORPUS, "--quick", "--no-artifact", "--json"]);
    assert_eq!(out.status.code(), Some(0));
    let json = stdout(&out);
    // extractors + determinism are reported, but skipped.
    let skipped = json.matches("\"status\":\"skipped\"").count();
    assert_eq!(skipped, 2, "quick mode must skip exactly 2 checks:\n{json}");
    assert!(json.contains("skipped: --quick"));
}

// ---------------------------------------------------------------------------
// Reflection: capabilities + robot-docs + top-level integration
// ---------------------------------------------------------------------------

#[test]
fn doctor_capabilities_reflects_the_contract() {
    let out = run(&["doctor", "capabilities"]);
    assert_eq!(out.status.code(), Some(0));
    let json = stdout(&out);
    assert!(json.contains("\"schema\":\"trailtracker.doctor-capabilities/v1\""));
    for id in [
        "binary",
        "target",
        "analysis",
        "parse-failures",
        "losslessness",
        "extractors",
        "determinism",
    ] {
        assert!(json.contains(&format!("\"id\":\"{id}\"")), "missing {id}");
    }
    // Exit-code dictionary and safety envelope are reflected.
    assert!(json.contains("\"exit_codes\""));
    assert!(json.contains("\"safety_envelope\""));
    assert!(json.contains("\"mutates_target\":false"));
    // `--json` is accepted as a no-op.
    let with_flag = run(&["doctor", "capabilities", "--json"]);
    assert_eq!(stdout(&with_flag), json);
}

#[test]
fn doctor_robot_docs_prints_the_agent_handbook() {
    let out = run(&["doctor", "robot-docs"]);
    assert_eq!(out.status.code(), Some(0));
    let docs = stdout(&out);
    for section in [
        "agent handbook",
        "## Invocations",
        "## Checks (in order)",
        "## Exit codes",
        "## Output contract",
        "## Artifacts",
        "## Reversibility",
    ] {
        assert!(docs.contains(section), "robot-docs missing {section}");
    }
    assert!(docs.contains("trailtracker.doctor/v1"));
}

#[test]
fn doctor_is_discoverable_from_help_and_capabilities() {
    let help = stdout(&run(&["help"]));
    assert!(help.contains("doctor [DIR]"), "help missing doctor");
    assert!(
        help.contains("1  doctor/arch-verify/violations only: findings present"),
        "help missing doctor exit code"
    );
    let caps = stdout(&run(&["capabilities"]));
    assert!(
        caps.contains("\"name\":\"doctor\""),
        "capabilities missing doctor"
    );
    assert!(caps.contains("trailtracker.doctor/v1"));

    // Typo redirection reaches doctor too.
    let out = run(&["docter"]);
    assert_eq!(out.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("trailtracker doctor"),
        "did-you-mean must suggest doctor"
    );
}
