//! Black-box integration tests for `trailtracker dossier` — the client-ready
//! single-file HTML deliverable. These drive the compiled binary against the
//! vendored calc corpus and pin the contract:
//!
//! - every section renders (brief, code map, enriched domains, layer
//!   violations, footer),
//! - the embedded graph payload is byte-identical to the proven
//!   `export ontoloom --view hierarchy` wire document,
//! - the file is airgap-grade: zero external references of any kind,
//! - two runs over the same tree produce byte-identical files,
//! - `--enrich` embeds the supplied document and renders its attestation,
//! - every error path exits with the documented code.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

fn bin() -> Command {
    Command::new(env!("CARGO_BIN_EXE_trailtracker"))
}

const CORPUS: &str = "eval/corpus/calc";

/// A per-test output path in the OS temp dir (unique per test name + pid so
/// parallel test runs never collide).
fn out_file(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "tt-dossier-test-{name}-{}.html",
        std::process::id()
    ))
}

/// Run `dossier CORPUS -o <path>`, assert success + path echo, return the HTML.
fn generate(name: &str, extra: &[&str]) -> String {
    let path = out_file(name);
    let path_str = path.to_str().expect("utf8 temp path");
    let mut args = vec!["dossier", CORPUS, "-o", path_str];
    args.extend_from_slice(extra);
    let out = bin().args(&args).output().expect("run dossier");
    assert!(
        out.status.success(),
        "dossier exited non-zero: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert_eq!(
        stdout.trim_end(),
        path_str,
        "stdout must carry exactly the output path"
    );
    let html = fs::read_to_string(&path).expect("read generated dossier");
    let _ = fs::remove_file(&path);
    html
}

#[test]
fn dossier_renders_every_section() {
    let html = generate("sections", &[]);
    for marker in [
        "<!DOCTYPE html>",
        "TrailTracker dossier",
        "<section id=\"brief\">",
        "Domains (structural clustering)",
        "Module dependency map",
        "Entry points",
        "Hotspots",
        "Dependency cycles",
        "<section id=\"map\">",
        "id=\"cm-layout\"",
        "id=\"cm-search\"",
        "<section id=\"violations\">",
        "<section id=\"companion\">",
        "For your AI assistant",
        "id=\"companion-copy\"",
        "id=\"companion-text\"",
        "<footer>",
        "analysis fingerprint",
        "id=\"tt-graph\"",
    ] {
        assert!(html.contains(marker), "missing `{marker}` in dossier");
    }
    // Drill-only navigation (H10): no bulk expand-to-level buttons anywhere.
    assert!(
        !html.contains("cm-levels"),
        "level bulk-expand buttons must not exist"
    );
    // Web is the default layout face; tree the alternate.
    assert!(
        html.contains("data-mode=\"web\" aria-pressed=\"true\""),
        "web must be the default layout"
    );
    // The enriched-domains section exists only in `enrich` feature builds;
    // the default/airgap dossier carries no trace of the naming pass.
    if cfg!(feature = "enrich") {
        assert!(
            html.contains("<section id=\"enriched\">"),
            "enrich builds must render the enriched section"
        );
        assert!(
            html.contains("enrich-domains"),
            "missing the run-enrich-domains pointer note"
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
    assert!(
        !html.contains("id=\"tt-enrich\""),
        "enrich payload must be absent without --enrich"
    );
    // The version in the footer matches the binary's.
    assert!(
        html.contains(&format!("trailtracker v{}", env!("CARGO_PKG_VERSION"))),
        "footer must attest the tool version"
    );
}

#[test]
fn embedded_graph_equals_the_hierarchy_export() {
    let html = generate("embed", &[]);
    let start_tag = "<script type=\"application/json\" id=\"tt-graph\">";
    let start = html.find(start_tag).expect("graph payload tag") + start_tag.len();
    let end = start + html[start..].find("</script>").expect("payload closer");
    // Undo the script-safety escape (`</` was embedded as `<\/`).
    let embedded = html[start..end].replace("<\\/", "</");

    let out = bin()
        .args(["export", "ontoloom", CORPUS, "--view", "hierarchy"])
        .output()
        .expect("run export");
    assert!(out.status.success(), "export exited non-zero");
    let wire = String::from_utf8(out.stdout).expect("utf8 wire");
    assert_eq!(
        embedded,
        wire.trim_end(),
        "embedded graph must be byte-identical to the proven wire export"
    );
}

/// The embedded AI-companion digest is exactly the verbalizer's `all` view
/// at the dossier's budget — one source of truth, no drift between the copy
/// button's payload and what `trailtracker verbalize` prints.
#[test]
fn companion_digest_equals_the_verbalize_all_view() {
    let html = generate("companion", &[]);
    let start_tag = "<pre id=\"companion-text\">";
    let start = html.find(start_tag).expect("companion pre") + start_tag.len();
    let end = start + html[start..].find("</pre>").expect("companion closer");
    let embedded = html[start..end]
        .replace("&lt;", "<")
        .replace("&gt;", ">")
        .replace("&quot;", "\"")
        .replace("&amp;", "&");

    let out = bin()
        .args(["verbalize", CORPUS, "--view", "all", "--budget", "30000"])
        .output()
        .expect("run verbalize");
    assert!(out.status.success(), "verbalize exited non-zero");
    let digest = String::from_utf8(out.stdout).expect("utf8 digest");
    assert_eq!(
        embedded, digest,
        "companion must be byte-identical to `verbalize --view all --budget 30000`"
    );
}

#[test]
fn dossier_is_byte_deterministic() {
    let a = generate("det-a", &[]);
    let b = generate("det-b", &[]);
    assert_eq!(a, b, "two runs over the same tree must be byte-identical");
}

#[test]
fn dossier_makes_zero_external_references() {
    let html = generate("airgap", &[]);
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
        "<iframe",
    ] {
        assert!(
            !html.contains(banned),
            "airgap violation: `{banned}` found in the dossier"
        );
    }
}

#[cfg(feature = "enrich")]
#[test]
fn enrich_document_is_embedded_and_attested() {
    let fixture = std::env::temp_dir().join(format!(
        "tt-dossier-test-enrich-{}.json",
        std::process::id()
    ));
    fs::write(
        &fixture,
        r#"{"schema":"trailtracker.enrich/v1","command":"enrich-domains","dir":"eval/corpus/calc","clusters":[{"cluster_id":"c1","domain":"calc","label":"calc","unit_count":1,"file_count":2,"symbol_count":9,"confidence":"high","subdomains":["calc"],"name":"Expression Calculator","description":"Parses and evaluates arithmetic expressions.","responsibilities":["tokenize input","evaluate expressions"]}],"attestation":{"backend":"mock","model":"haiku","prompt_hash":"fnv1a64:00000000000000ab","timestamp":"2026-01-01T00:00:00Z"}}"#,
    )
    .expect("write enrich fixture");

    let html = generate(
        "enrich",
        &["--enrich", fixture.to_str().expect("utf8 fixture path")],
    );
    let _ = fs::remove_file(&fixture);

    assert!(html.contains("id=\"tt-enrich\""), "enrich payload missing");
    assert!(
        html.contains("Expression Calculator"),
        "cluster name missing from the embedded document"
    );
    assert!(
        html.contains("fnv1a64:00000000000000ab"),
        "attestation prompt hash missing"
    );
    assert!(
        html.contains("id=\"enrich-cards\""),
        "enrich card container missing"
    );
    assert!(
        !html.contains("No enrichment supplied"),
        "pointer note must give way to the cards"
    );
}

// ---------------------------------------------------------------------------
// Error paths — every failure exits with the documented code and a fix line.
// ---------------------------------------------------------------------------

/// The default/airgap build has no --enrich flag at all: it must be rejected
/// like any other unknown flag, not silently ignored.
#[cfg(not(feature = "enrich"))]
#[test]
fn enrich_flag_is_unknown_in_the_default_build() {
    let out = bin()
        .args(["dossier", CORPUS, "--enrich", "x.json"])
        .output()
        .expect("run");
    assert_eq!(out.status.code(), Some(2), "--enrich must be unknown");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("unknown flag"), "unhelpful error: {err}");
}

#[test]
fn missing_dir_exits_3() {
    let out = bin()
        .args(["dossier", "does/not/exist"])
        .output()
        .expect("run");
    assert_eq!(out.status.code(), Some(3), "missing DIR must exit 3");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("does not exist"), "unhelpful error: {err}");
}

#[test]
fn missing_dir_argument_exits_2() {
    let out = bin().args(["dossier"]).output().expect("run");
    assert_eq!(out.status.code(), Some(2), "no DIR must exit 2");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("requires a DIR"), "unhelpful error: {err}");
}

#[test]
fn surplus_positionals_exit_2() {
    let out = bin()
        .args(["dossier", CORPUS, "extra"])
        .output()
        .expect("run");
    assert_eq!(out.status.code(), Some(2), "surplus positional must exit 2");
}

#[test]
fn unknown_flag_exits_2() {
    let out = bin()
        .args(["dossier", CORPUS, "--nope"])
        .output()
        .expect("run");
    assert_eq!(out.status.code(), Some(2), "unknown flag must exit 2");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("unknown flag"), "unhelpful error: {err}");
}

#[test]
fn dangling_output_flag_exits_2() {
    let out = bin().args(["dossier", CORPUS, "-o"]).output().expect("run");
    assert_eq!(out.status.code(), Some(2), "-o without PATH must exit 2");
}

#[cfg(feature = "enrich")]
#[test]
fn missing_enrich_file_exits_3() {
    let out = bin()
        .args(["dossier", CORPUS, "--enrich", "no/such/enrich.json"])
        .output()
        .expect("run");
    assert_eq!(
        out.status.code(),
        Some(3),
        "missing enrich file must exit 3"
    );
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(
        err.contains("enrich-domains"),
        "fix line should say how to generate one: {err}"
    );
}

#[cfg(feature = "enrich")]
#[test]
fn wrong_schema_enrich_file_exits_2() {
    let fixture = std::env::temp_dir().join(format!(
        "tt-dossier-test-badenrich-{}.json",
        std::process::id()
    ));
    fs::write(&fixture, r#"{"schema":"something/else"}"#).expect("write fixture");
    let out = bin()
        .args([
            "dossier",
            CORPUS,
            "--enrich",
            fixture.to_str().expect("utf8 path"),
        ])
        .output()
        .expect("run");
    let _ = fs::remove_file(&fixture);
    assert_eq!(
        out.status.code(),
        Some(2),
        "non-enrich/v1 document must exit 2"
    );
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(
        err.contains("trailtracker.enrich/v1"),
        "error should name the expected schema: {err}"
    );
}

#[test]
fn dossier_is_documented_in_capabilities_and_help() {
    let out = bin().args(["capabilities"]).output().expect("run");
    assert!(out.status.success());
    let caps = String::from_utf8_lossy(&out.stdout).into_owned();
    let want_usage = if cfg!(feature = "enrich") {
        "trailtracker dossier <DIR> [-o out.html] [--enrich enrich.json]"
    } else {
        "trailtracker dossier <DIR> [-o out.html]"
    };
    assert!(
        caps.contains(want_usage),
        "capabilities must document the dossier usage"
    );
    if !cfg!(feature = "enrich") {
        assert!(
            !caps.contains("enrich"),
            "default capabilities must not mention enrichment"
        );
    }
    let out = bin().args(["help"]).output().expect("run");
    assert!(out.status.success());
    let help = String::from_utf8_lossy(&out.stdout).into_owned();
    assert!(
        help.contains("dossier <DIR>"),
        "help must list the dossier command"
    );
}
