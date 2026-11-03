//! Black-box tests for `trailtracker enrich-domains` — the optional LLM
//! naming pass. `enrich` FEATURE BUILDS ONLY: the command (and this whole
//! test file) does not exist in the default/airgap build. No test here
//! touches the network or a real LLM: the backend is either a committed
//! python mock (`tests/fixtures/mock_enrich.py`, driven through the
//! documented `TRAILTRACKER_ENRICH_CMD` override) or deliberately broken to
//! pin the actionable exit-4 error path.
#![cfg(feature = "enrich")]

use std::process::Command;

fn bin() -> Command {
    Command::new(env!("CARGO_BIN_EXE_trailtracker"))
}

const CORPUS: &str = "eval/corpus/calc";
/// The offline mock backend (integration tests run from the crate root).
const MOCK_BACKEND: &str = "python3 tests/fixtures/mock_enrich.py";

/// Extract the value of a `"key":"value"` pair from one-line JSON output.
/// (String-level on purpose: these are black-box shape checks; the full JSON
/// contract is exercised by the unit tests in `src/enrich.rs`.)
fn json_str_field<'a>(doc: &'a str, key: &str) -> Option<&'a str> {
    let marker = format!("\"{key}\":\"");
    let start = doc.find(&marker)? + marker.len();
    let end = doc[start..].find('"')? + start;
    Some(&doc[start..end])
}

#[test]
fn enrich_domains_with_mocked_backend_emits_the_enrich_schema() {
    let out = bin()
        .args(["enrich-domains", CORPUS, "--json"])
        .env("TRAILTRACKER_ENRICH_CMD", MOCK_BACKEND)
        .output()
        .expect("run enrich-domains");
    assert!(
        out.status.success(),
        "enrich-domains failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let doc = String::from_utf8(out.stdout).expect("utf8 stdout");
    assert!(
        doc.contains("\"schema\":\"trailtracker.enrich/v1\""),
        "{doc}"
    );
    assert!(doc.contains("\"command\":\"enrich-domains\""), "{doc}");
    // Clusters are named by the mock and carry the deterministic ids.
    assert!(doc.contains("\"cluster_id\":\"domain::"), "{doc}");
    assert!(doc.contains("\"name\":\"MockCluster0\""), "{doc}");
    assert!(doc.contains("\"responsibilities\":["), "{doc}");
    // Attestation block: backend, model, prompt hash, timestamp, honesty note.
    assert!(doc.contains("\"attestation\""), "{doc}");
    assert_eq!(
        json_str_field(&doc, "backend"),
        Some(MOCK_BACKEND),
        "attestation must record the actual backend"
    );
    assert!(doc.contains("\"prompt_hash\":\"fnv1a64:"), "{doc}");
    assert!(doc.contains("\"timestamp\":\""), "{doc}");
    assert!(doc.contains("not byte-stable"), "{doc}");
}

/// The deterministic side of the attestation: two runs over the same tree see
/// the same evidence, so the prompt hash (and every cluster id) is identical
/// even though the semantic fields carry no byte-stability promise.
#[test]
fn enrich_domains_prompt_hash_is_stable_across_runs() {
    let run = || {
        let out = bin()
            .args(["enrich-domains", CORPUS, "--json"])
            .env("TRAILTRACKER_ENRICH_CMD", MOCK_BACKEND)
            .output()
            .expect("run enrich-domains");
        assert!(out.status.success());
        String::from_utf8(out.stdout).expect("utf8 stdout")
    };
    let (a, b) = (run(), run());
    let hash = |doc: &str| json_str_field(doc, "prompt_hash").map(str::to_string);
    assert!(hash(&a).is_some(), "prompt_hash missing: {a}");
    assert_eq!(
        hash(&a),
        hash(&b),
        "same tree must attest the same evidence"
    );
}

/// The cluster ids the enrichment names must be exactly the domain node ids
/// the airgapped `extract domains` emits — deterministic membership.
#[test]
fn enrich_domains_names_exactly_the_extract_domains_clusters() {
    let extract = bin()
        .args(["extract", "domains", CORPUS])
        .output()
        .expect("run extract domains");
    assert!(extract.status.success());
    let jsonl = String::from_utf8(extract.stdout).expect("utf8");
    let domain_ids: Vec<&str> = jsonl
        .lines()
        .filter(|l| l.contains("\"record\":\"node\"") && l.contains("\"id\":\"domain::"))
        .filter_map(|l| json_str_field(l, "id"))
        .collect();
    assert!(!domain_ids.is_empty(), "calc corpus must yield domains");

    let out = bin()
        .args(["enrich-domains", CORPUS, "--json"])
        .env("TRAILTRACKER_ENRICH_CMD", MOCK_BACKEND)
        .output()
        .expect("run enrich-domains");
    assert!(out.status.success());
    let doc = String::from_utf8(out.stdout).expect("utf8");
    for id in &domain_ids {
        assert!(
            doc.contains(&format!("\"cluster_id\":\"{id}\"")),
            "cluster {id} missing from enrichment:\n{doc}"
        );
    }
    let named = doc.matches("\"cluster_id\":\"domain::").count();
    assert_eq!(
        named,
        domain_ids.len(),
        "enrichment must name every cluster exactly once"
    );
}

#[test]
fn enrich_domains_human_output_shows_names_and_attestation() {
    let out = bin()
        .args(["enrich-domains", CORPUS])
        .env("TRAILTRACKER_ENRICH_CMD", MOCK_BACKEND)
        .output()
        .expect("run enrich-domains");
    assert!(out.status.success());
    let text = String::from_utf8(out.stdout).expect("utf8 stdout");
    assert!(
        text.starts_with("enriched domains for eval/corpus/calc"),
        "{text}"
    );
    assert!(text.contains("MockCluster0"), "{text}");
    assert!(text.contains("fnv1a64:"), "{text}");
    assert!(
        text.contains("not byte-stable"),
        "determinism honesty note missing:\n{text}"
    );
}

/// Backend absent: the actionable E1-style failure — exit 4, `trailtracker:`
/// message, `fix:` line teaching both the install and the override, clean
/// stdout, and NEVER a locally invented name.
#[test]
fn enrich_domains_without_backend_fails_actionably_with_exit_4() {
    let out = bin()
        .args(["enrich-domains", CORPUS])
        .env("TRAILTRACKER_ENRICH_CMD", "/nonexistent/tt-enrich-backend")
        .output()
        .expect("run enrich-domains");
    assert_eq!(out.status.code(), Some(4), "missing backend must exit 4");
    assert!(out.stdout.is_empty(), "errors must not pollute stdout");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("trailtracker:"), "error prefix missing: {err}");
    assert!(err.contains("failed to start"), "cause missing: {err}");
    assert!(err.contains("fix:"), "fix line missing: {err}");
    assert!(
        err.contains("TRAILTRACKER_ENRICH_CMD"),
        "fix must teach the override: {err}"
    );
    assert!(
        err.contains("extract domains"),
        "fix must point at the airgap-safe alternative: {err}"
    );
}

/// Backend runs but replies with nothing: still exit 4, still honest.
#[test]
fn enrich_domains_with_empty_reply_fails_with_exit_4() {
    let out = bin()
        .args(["enrich-domains", CORPUS])
        .env("TRAILTRACKER_ENRICH_CMD", "true")
        .output()
        .expect("run enrich-domains");
    assert_eq!(out.status.code(), Some(4), "empty reply must exit 4");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("empty reply"), "cause missing: {err}");
    assert!(err.contains("fix:"), "fix line missing: {err}");
}

#[test]
fn enrich_domains_usage_and_missing_dir_follow_the_exit_dictionary() {
    // Surplus positionals: exit 2 before any backend is touched.
    let out = bin()
        .args(["enrich-domains", CORPUS, "extra"])
        .env("TRAILTRACKER_ENRICH_CMD", "/nonexistent/never-invoked")
        .output()
        .expect("run enrich-domains");
    assert_eq!(
        out.status.code(),
        Some(2),
        "surplus positionals must exit 2"
    );
    // Missing dir: exit 3 before any backend is touched.
    let out = bin()
        .args(["enrich-domains", "/no/such/dir-for-tt-enrich"])
        .env("TRAILTRACKER_ENRICH_CMD", "/nonexistent/never-invoked")
        .output()
        .expect("run enrich-domains");
    assert_eq!(out.status.code(), Some(3), "missing dir must exit 3");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("does not exist"), "path error missing: {err}");
}

#[test]
fn enrich_domains_is_discoverable_from_help_and_capabilities() {
    let help = bin().arg("help").output().expect("run help");
    let help = String::from_utf8_lossy(&help.stdout).to_string();
    assert!(
        help.contains("enrich-domains"),
        "help missing enrich-domains"
    );
    assert!(
        help.contains("TRAILTRACKER_ENRICH_CMD"),
        "help must document the backend override"
    );
    let caps = bin()
        .arg("capabilities")
        .output()
        .expect("run capabilities");
    let caps = String::from_utf8_lossy(&caps.stdout).to_string();
    assert!(
        caps.contains("\"name\":\"enrich-domains\""),
        "capabilities missing enrich-domains"
    );
    assert!(
        caps.contains("trailtracker.enrich/v1"),
        "capabilities missing the enrich schema"
    );
}
