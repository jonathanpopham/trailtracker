//! `regress` — golden-snapshot regression over a fixed corpus of known codebases.
//!
//! Loops every vendored crate under the corpus directory, analyzes it, and diffs
//! the canonical graph against its committed golden. Exits non-zero if any case
//! regressed, is missing a golden, or failed to analyze — so it can gate a PR.
//!
//! Usage:
//!   regress [--root DIR] [--corpus DIR] [--golden DIR] [--update]
//!
//!   --root    repo root; corpus/golden default to <root>/eval/{corpus,golden}
//!   --corpus  override corpus directory
//!   --golden  override golden directory
//!   --update  (re)write goldens from current output instead of failing

#![forbid(unsafe_code)]

use std::path::PathBuf;
use std::process::ExitCode;

use trailtracker_eval::golden::{self, CaseStatus};

fn main() -> ExitCode {
    let args = Args::parse(std::env::args().skip(1));

    eprintln!(
        "trailtracker regress: corpus={} golden={}{}",
        args.corpus.display(),
        args.golden.display(),
        if args.update { "  (UPDATE MODE)" } else { "" }
    );

    let outcomes = match golden::run_all(&args.corpus, &args.golden, args.update) {
        Ok(o) => o,
        Err(e) => {
            eprintln!(
                "regress: failed to read corpus {}: {e}",
                args.corpus.display()
            );
            return ExitCode::FAILURE;
        }
    };

    if outcomes.is_empty() {
        eprintln!(
            "regress: no corpus crates found under {}",
            args.corpus.display()
        );
        return ExitCode::FAILURE;
    }

    let mut failed = 0usize;
    for o in &outcomes {
        eprintln!(
            "  [{:>9}] {:<16} nodes={} edges={}",
            o.status.label(),
            o.name,
            o.nodes,
            o.edges
        );
        match &o.status {
            CaseStatus::Diff { added, removed } => {
                failed += 1;
                eprintln!(
                    "      +{} added / -{} removed lines",
                    added.len(),
                    removed.len()
                );
                for line in removed.iter().take(5) {
                    eprintln!("      - {}", truncate(line));
                }
                for line in added.iter().take(5) {
                    eprintln!("      + {}", truncate(line));
                }
                if added.len() + removed.len() > 10 {
                    eprintln!("      … run `regress --update` to bless after review");
                }
            }
            CaseStatus::Missing => {
                failed += 1;
                eprintln!("      no committed golden — run `regress --update` to create it");
            }
            CaseStatus::AnalysisError(msg) => {
                failed += 1;
                eprintln!("      analysis error: {msg}");
            }
            CaseStatus::Pass | CaseStatus::Written => {}
        }
    }

    let total = outcomes.len();
    eprintln!(
        "trailtracker regress: {}/{} cases ok{}",
        total - failed,
        total,
        if args.update {
            " (goldens written)"
        } else {
            ""
        }
    );
    // Machine-readable summary line for CI capture.
    println!("regress_total={total} regress_failed={failed}");

    if failed == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

fn truncate(s: &str) -> String {
    const MAX: usize = 160;
    if s.len() <= MAX {
        s.to_string()
    } else {
        format!("{}…", &s[..MAX])
    }
}

struct Args {
    corpus: PathBuf,
    golden: PathBuf,
    update: bool,
}

impl Args {
    fn parse(mut it: impl Iterator<Item = String>) -> Args {
        let mut root = PathBuf::from(".");
        let mut corpus: Option<PathBuf> = None;
        let mut golden: Option<PathBuf> = None;
        let mut update = false;
        while let Some(flag) = it.next() {
            match flag.as_str() {
                "--root" => {
                    if let Some(v) = it.next() {
                        root = PathBuf::from(v);
                    }
                }
                "--corpus" => corpus = it.next().map(PathBuf::from),
                "--golden" => golden = it.next().map(PathBuf::from),
                "--update" => update = true,
                _ => {}
            }
        }
        Args {
            corpus: corpus.unwrap_or_else(|| root.join("eval/corpus")),
            golden: golden.unwrap_or_else(|| root.join("eval/golden")),
            update,
        }
    }
}
