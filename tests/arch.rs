//! Black-box integration tests for `trailtracker arch-verify` / `arch-init`
//! (ADR-0005): the exit-code contract (0 spec holds / 1 error findings /
//! 2 malformed spec / 3 missing paths), the `--json` report schema, evidence
//! in findings, byte-determinism, and the adopt-in-one-command bootstrap.

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

fn stderr(out: &Output) -> String {
    String::from_utf8(out.stderr.clone()).expect("utf8 stderr")
}

/// The corpus fixture with a real cross-domain dependency: its `flows`
/// cluster depends on its `classes` cluster (a Flow calling an Apex action).
const CORPUS: &str = "eval/corpus/sflinked";

/// A unique temp directory that cleans itself up (tests must not litter).
struct TempDir(PathBuf);

impl TempDir {
    fn new(tag: &str) -> TempDir {
        let dir = std::env::temp_dir().join(format!("tt-arch-test-{tag}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).expect("create temp dir");
        TempDir(dir)
    }

    fn path(&self) -> &Path {
        &self.0
    }

    /// Write `text` as a spec file inside the dir and return its path.
    fn write_spec(&self, name: &str, text: &str) -> String {
        let p = self.0.join(name);
        fs::write(&p, text).expect("write spec");
        p.to_str().expect("utf8 path").to_string()
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// A truthful spec for the sflinked corpus: both recovered domains declared,
/// with the dependency direction that does NOT exist forbidden.
const TRUTHFUL_SPEC: &str = r#"{
  "format": "trailtracker.arch-spec/v1",
  "domains": [
    { "name": "Classes", "pathPrefixes": ["force-app/main/default/classes/"] },
    { "name": "Flows", "pathPrefixes": ["force-app/main/default/flows/"] }
  ],
  "rules": [
    { "type": "domain-existence", "domain": "Classes" },
    { "type": "domain-existence", "domain": "Flows" },
    { "type": "forbidden-dependency", "from": "Classes", "to": "Flows" }
  ]
}"#;

/// The same spec with the rule flipped onto the dependency that DOES exist
/// (flows -> classes), so verification must gate.
const VIOLATED_SPEC: &str = r#"{
  "format": "trailtracker.arch-spec/v1",
  "domains": [
    { "name": "Classes", "pathPrefixes": ["force-app/main/default/classes/"] },
    { "name": "Flows", "pathPrefixes": ["force-app/main/default/flows/"] }
  ],
  "rules": [
    { "type": "forbidden-dependency", "from": "Flows", "to": "Classes" }
  ]
}"#;

// ---------------------------------------------------------------------------
// Exit-code contract
// ---------------------------------------------------------------------------

#[test]
fn clean_spec_exits_0_with_no_findings() {
    let tmp = TempDir::new("clean");
    let spec = tmp.write_spec("arch.json", TRUTHFUL_SPEC);
    let out = run(&["arch-verify", CORPUS, "--spec", &spec]);
    assert_eq!(out.status.code(), Some(0), "stderr: {}", stderr(&out));
    let text = stdout(&out);
    assert!(text.contains("findings: none"), "{text}");
    assert!(text.contains("status: clean (exit 0)"), "{text}");
    assert!(out.stderr.is_empty(), "clean run must not touch stderr");
}

#[test]
fn violated_spec_exits_1_with_evidence() {
    let tmp = TempDir::new("violated");
    let spec = tmp.write_spec("arch.json", VIOLATED_SPEC);
    let out = run(&["arch-verify", CORPUS, "--spec", &spec]);
    assert_eq!(out.status.code(), Some(1), "must gate on the real edge");
    let text = stdout(&out);
    assert!(
        text.contains("[error] forbidden-dependency:Flows->Classes"),
        "{text}"
    );
    // Evidence names actual files on both sides of the edge.
    assert!(text.contains("evidence:"), "{text}");
    assert!(
        text.contains("force-app/main/default/flows/") && text.contains("classes/"),
        "{text}"
    );
    assert!(text.contains("status: violated (exit 1)"), "{text}");
}

#[test]
fn garbage_spec_exits_2_with_fix_line() {
    let tmp = TempDir::new("garbage");
    let spec = tmp.write_spec("arch.json", "not json at all {{{");
    let out = run(&["arch-verify", CORPUS, "--spec", &spec]);
    assert_eq!(out.status.code(), Some(2));
    assert!(
        out.stdout.is_empty(),
        "usage errors write no data to stdout"
    );
    let err = stderr(&out);
    assert!(err.starts_with("trailtracker: invalid arch spec"), "{err}");
    assert!(err.contains("  fix: "), "missing fix line: {err}");
}

#[test]
fn unknown_rule_type_exits_2_and_names_the_vocabulary() {
    let tmp = TempDir::new("unknown-rule");
    let spec = tmp.write_spec(
        "arch.json",
        r#"{"domains": [{"name": "A", "pathPrefixes": ["a/"]}],
            "rules": [{"type": "no-cycles"}]}"#,
    );
    let out = run(&["arch-verify", CORPUS, "--spec", &spec]);
    assert_eq!(out.status.code(), Some(2));
    let err = stderr(&out);
    assert!(err.contains("unknown rule type 'no-cycles'"), "{err}");
    assert!(err.contains("forbidden-dependency"), "{err}");
}

#[test]
fn missing_spec_exits_3_and_recommends_arch_init() {
    let out = run(&["arch-verify", CORPUS]);
    assert_eq!(out.status.code(), Some(3), "no default spec in the corpus");
    let err = stderr(&out);
    assert!(err.contains("failed to read arch spec"), "{err}");
    assert!(
        err.contains("arch-init"),
        "fix must point at arch-init: {err}"
    );
}

#[test]
fn missing_dir_exits_3() {
    let tmp = TempDir::new("missing-dir");
    let spec = tmp.write_spec("arch.json", TRUTHFUL_SPEC);
    let out = run(&["arch-verify", "/no/such/dir-tt-arch", "--spec", &spec]);
    assert_eq!(out.status.code(), Some(3));
}

#[test]
fn unknown_flag_exits_2_with_hint() {
    let out = run(&["arch-verify", CORPUS, "--sepc", "x.json"]);
    assert_eq!(out.status.code(), Some(2));
    assert!(stderr(&out).contains("--spec"), "{}", stderr(&out));
}

// ---------------------------------------------------------------------------
// Severity semantics
// ---------------------------------------------------------------------------

#[test]
fn warn_severity_reports_but_does_not_gate() {
    let tmp = TempDir::new("warn");
    let spec = tmp.write_spec(
        "arch.json",
        &VIOLATED_SPEC.replace(
            r#""to": "Classes" }"#,
            r#""to": "Classes", "severity": "warn" }"#,
        ),
    );
    let out = run(&["arch-verify", CORPUS, "--spec", &spec]);
    assert_eq!(out.status.code(), Some(0), "warn findings must not gate");
    let text = stdout(&out);
    assert!(
        text.contains("[warn] forbidden-dependency:Flows->Classes"),
        "{text}"
    );
    assert!(text.contains("status: warnings (exit 0)"), "{text}");
}

// ---------------------------------------------------------------------------
// --json report schema
// ---------------------------------------------------------------------------

#[test]
fn json_report_carries_schema_findings_and_exit() {
    let tmp = TempDir::new("json");
    let spec = tmp.write_spec("arch.json", VIOLATED_SPEC);
    let out = run(&["arch-verify", CORPUS, "--spec", &spec, "--json"]);
    assert_eq!(out.status.code(), Some(1));
    let text = stdout(&out);
    assert!(
        text.contains("\"format\":\"trailtracker.arch-verify/v1\""),
        "{text}"
    );
    for key in [
        "\"dir\":",
        "\"spec\":",
        "\"domains\":2",
        "\"rules\":1",
        "\"findings\":",
        "\"id\":\"forbidden-dependency:Flows->Classes\"",
        "\"type\":\"forbidden-dependency\"",
        "\"severity\":\"error\"",
        "\"count\":",
        "\"examples\":",
        "\"status\":\"violated\"",
        "\"exit\":1",
    ] {
        assert!(text.contains(key), "missing {key} in:\n{text}");
    }
}

// ---------------------------------------------------------------------------
// Determinism
// ---------------------------------------------------------------------------

#[test]
fn verify_output_is_byte_deterministic() {
    let tmp = TempDir::new("determinism");
    let spec = tmp.write_spec("arch.json", VIOLATED_SPEC);
    let once = run(&["arch-verify", CORPUS, "--spec", &spec, "--json"]);
    let twice = run(&["arch-verify", CORPUS, "--spec", &spec, "--json"]);
    assert_eq!(stdout(&once), stdout(&twice));
    assert_eq!(once.status.code(), twice.status.code());
}

// ---------------------------------------------------------------------------
// arch-init: the adopt-in-one-command path
// ---------------------------------------------------------------------------

#[test]
fn arch_init_bootstraps_a_spec_that_verifies_without_gating() {
    let tmp = TempDir::new("init");
    let spec_path = tmp.path().join("arch.json");
    let spec_str = spec_path.to_str().unwrap();
    let out = run(&["arch-init", CORPUS, "-o", spec_str]);
    assert_eq!(out.status.code(), Some(0), "stderr: {}", stderr(&out));
    // stdout carries only the written path.
    assert_eq!(stdout(&out).trim(), spec_str);
    let text = fs::read_to_string(&spec_path).expect("spec written");
    assert!(
        text.contains("\"format\": \"trailtracker.arch-spec/v1\""),
        "{text}"
    );
    assert!(text.contains("domain-existence"), "{text}");
    assert!(text.contains("domain-containment"), "{text}");
    assert!(text.contains("observedDependencies"), "{text}");

    // The bootstrapped spec immediately verifies without gating.
    let verify = run(&["arch-verify", CORPUS, "--spec", spec_str]);
    assert_eq!(
        verify.status.code(),
        Some(0),
        "fresh init must not gate:\n{}",
        stdout(&verify)
    );
}

#[test]
fn arch_init_stdout_is_byte_deterministic() {
    let once = run(&["arch-init", CORPUS]);
    let twice = run(&["arch-init", CORPUS]);
    assert_eq!(once.status.code(), Some(0));
    assert_eq!(stdout(&once), stdout(&twice));
}

#[test]
fn arch_init_refuses_to_overwrite() {
    let tmp = TempDir::new("no-overwrite");
    let spec = tmp.write_spec("arch.json", "{}");
    let out = run(&["arch-init", CORPUS, "-o", &spec]);
    assert_eq!(out.status.code(), Some(2));
    assert!(
        stderr(&out).contains("never overwrites"),
        "{}",
        stderr(&out)
    );
}

// ---------------------------------------------------------------------------
// Default spec discovery (<DIR>/.trailtracker-arch.json)
// ---------------------------------------------------------------------------

#[test]
fn default_spec_is_discovered_in_the_analyzed_dir() {
    // Copy the corpus into a temp dir so the fixture itself stays pristine.
    let tmp = TempDir::new("default-spec");
    let dir = tmp.path().join("repo");
    copy_tree(Path::new(CORPUS), &dir);
    fs::write(dir.join(".trailtracker-arch.json"), VIOLATED_SPEC).unwrap();
    let out = run(&["arch-verify", dir.to_str().unwrap()]);
    assert_eq!(out.status.code(), Some(1), "{}", stderr(&out));
    assert!(stdout(&out).contains("forbidden-dependency:Flows->Classes"));
}

fn copy_tree(from: &Path, to: &Path) {
    fs::create_dir_all(to).unwrap();
    for entry in fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let target = to.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            copy_tree(&entry.path(), &target);
        } else {
            fs::copy(entry.path(), &target).unwrap();
        }
    }
}

// ---------------------------------------------------------------------------
// Discoverability
// ---------------------------------------------------------------------------

#[test]
fn arch_commands_are_discoverable_from_help_and_capabilities() {
    let help = stdout(&run(&["help"]));
    assert!(
        help.contains("arch-verify [DIR]"),
        "help missing arch-verify"
    );
    assert!(help.contains("arch-init [DIR]"), "help missing arch-init");
    let caps = stdout(&run(&["capabilities"]));
    assert!(
        caps.contains("\"name\":\"arch-verify\""),
        "capabilities missing arch-verify"
    );
    assert!(
        caps.contains("\"name\":\"arch-init\""),
        "capabilities missing arch-init"
    );
    assert!(
        caps.contains("trailtracker.arch-verify/v1"),
        "missing report schema id"
    );
}
