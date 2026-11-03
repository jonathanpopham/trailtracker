//! `verify` — the CI/build verification gate.
//!
//! Runs the eval pipeline (self-analysis regression + property/fuzz harness),
//! hash-attests the built CLI binary, and emits a deterministic JSON report that
//! can be archived and reviewed against its SHA-256. Exits non-zero if any gate
//! fails, so CI blocks on it.
//!
//! Usage:
//!   verify [--root DIR] [--binary PATH] [--out FILE] [--cases N] [--seed HEX]

#![forbid(unsafe_code)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use trailtracker_eval::property;
use trailtracker_eval::regression;
use trailtracker_eval::report;
use trailtracker_eval::sha256::sha256_hex;

fn main() -> ExitCode {
    let args = Args::parse(std::env::args().skip(1));

    eprintln!(
        "trailtracker verify: running self-analysis regression on {}",
        args.root.display()
    );
    let reg = match regression::run(&args.root) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("verify: analysis failed: {e}");
            return ExitCode::FAILURE;
        }
    };

    eprintln!(
        "trailtracker verify: running {} property cases (seed {:#x})",
        args.cases, args.seed
    );
    let corpus = collect_corpus(&args.root);
    let prop = property::run(args.seed, args.cases, &corpus);

    let binary_sha = args.binary.as_ref().and_then(|p| match fs::read(p) {
        Ok(bytes) => Some(sha256_hex(&bytes)),
        Err(_) => {
            eprintln!(
                "verify: note: binary {} not found; skipping hash",
                p.display()
            );
            None
        }
    });

    let json = report::build(
        &reg,
        &prop,
        binary_sha.as_deref(),
        env!("CARGO_PKG_VERSION"),
    );
    let body = json.to_line();
    let report_sha = sha256_hex(body.as_bytes());

    if let Some(out) = &args.out {
        if let Err(e) = fs::write(out, format!("{body}\n")) {
            eprintln!("verify: failed to write {}: {e}", out.display());
            return ExitCode::FAILURE;
        }
        eprintln!("trailtracker verify: report written to {}", out.display());
    }

    // Human-readable summary to stderr; machine attestation to stdout.
    eprintln!("--- verification summary ---");
    eprintln!(
        "  regression: {}  ({} files, {} nodes, {} edges, deterministic={})",
        pass_str(reg.passed()),
        reg.files,
        reg.nodes,
        reg.edges,
        reg.deterministic
    );
    for v in &reg.violations {
        eprintln!("    violation: {v}");
    }
    eprintln!(
        "  property:   {}  ({} cases, {} failures)",
        pass_str(prop.passed()),
        prop.cases,
        prop.failures.len()
    );
    for f in prop.failures.iter().take(5) {
        eprintln!("    failure [{}] seed={:#x}: {}", f.kind, f.seed, f.sample);
    }
    if let Some(h) = &binary_sha {
        eprintln!("  binary sha256: {h}");
    }
    eprintln!("  report sha256: {report_sha}");

    let pass = report::overall_pass(&reg, &prop);
    eprintln!("  overall: {}", pass_str(pass));
    // stdout: a single attestation line, easy to capture/compare in CI.
    println!("report_sha256={report_sha} overall_pass={pass}");

    if pass {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

fn pass_str(b: bool) -> &'static str {
    if b {
        "PASS"
    } else {
        "FAIL"
    }
}

/// Collect `.rs` sources under the repo as mutation fuel for the fuzzer.
fn collect_corpus(root: &Path) -> Vec<String> {
    let mut out = Vec::new();
    for sub in ["src", "eval/src"] {
        collect_rs(&root.join(sub), &mut out);
    }
    out
}

fn collect_rs(dir: &Path, out: &mut Vec<String>) {
    let entries = match fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_rs(&path, out);
        } else if path.extension().map(|e| e == "rs").unwrap_or(false) {
            if let Ok(s) = fs::read_to_string(&path) {
                out.push(s);
            }
        }
    }
}

struct Args {
    root: PathBuf,
    binary: Option<PathBuf>,
    out: Option<PathBuf>,
    cases: usize,
    seed: u64,
}

impl Args {
    fn parse(mut it: impl Iterator<Item = String>) -> Args {
        let mut args = Args {
            root: PathBuf::from("."),
            binary: None,
            out: None,
            cases: 5000,
            seed: 0xC0FFEE,
        };
        while let Some(flag) = it.next() {
            match flag.as_str() {
                "--root" => {
                    if let Some(v) = it.next() {
                        args.root = PathBuf::from(v);
                    }
                }
                "--binary" => args.binary = it.next().map(PathBuf::from),
                "--out" => args.out = it.next().map(PathBuf::from),
                "--cases" => {
                    if let Some(v) = it.next() {
                        if let Ok(n) = v.parse() {
                            args.cases = n;
                        }
                    }
                }
                "--seed" => {
                    if let Some(v) = it.next() {
                        let v = v.trim_start_matches("0x");
                        if let Ok(n) = u64::from_str_radix(v, 16) {
                            args.seed = n;
                        }
                    }
                }
                _ => {}
            }
        }
        args
    }
}
