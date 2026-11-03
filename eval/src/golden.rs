//! Golden-snapshot regression against a fixed corpus of *known codebases*.
//!
//! Each subdirectory of the corpus directory is a self-contained Rust crate
//! (vendored, no network). We run the full pipeline on it, serialize the
//! canonical graph to JSONL, and compare it byte-for-byte against a committed
//! golden file. Because TrailTracker guarantees deterministic output, any diff
//! is a *real semantic change* in the analyzer — precisely the regression signal
//! a PR gate should block on.
//!
//! `--update` blesses the current output as the new golden; review the diff in
//! the PR before doing so.

use std::fs;
use std::path::{Path, PathBuf};

use trailtracker::pipeline::analyze_dir;

/// One known codebase and the golden it is checked against.
pub struct CorpusCase {
    pub name: String,
    pub repo: PathBuf,
    pub golden: PathBuf,
}

/// Result of checking a single corpus case.
pub struct CaseOutcome {
    pub name: String,
    pub nodes: usize,
    pub edges: usize,
    pub status: CaseStatus,
}

pub enum CaseStatus {
    /// Output matched the committed golden exactly.
    Pass,
    /// Golden was absent; either a new case, or `--update` just wrote it.
    Written,
    Missing,
    /// The analyzer errored on this repo.
    AnalysisError(String),
    /// Output diverged from the golden.
    Diff {
        added: Vec<String>,
        removed: Vec<String>,
    },
}

impl CaseStatus {
    pub fn passed(&self) -> bool {
        matches!(self, CaseStatus::Pass | CaseStatus::Written)
    }
    pub fn label(&self) -> &'static str {
        match self {
            CaseStatus::Pass => "PASS",
            CaseStatus::Written => "WROTE",
            CaseStatus::Missing => "NO-GOLDEN",
            CaseStatus::AnalysisError(_) => "ERROR",
            CaseStatus::Diff { .. } => "REGRESSED",
        }
    }
}

/// Discover every corpus case: any non-hidden subdirectory of `corpus_dir`.
/// The corpus is curated by hand, so presence is the only criterion — cases
/// are no longer necessarily Rust crates (e.g. `sforg` is a Salesforce SFDX
/// metadata tree). Goldens live at `golden_dir/<name>.jsonl`. Returned sorted
/// by name for deterministic order.
pub fn discover(corpus_dir: &Path, golden_dir: &Path) -> std::io::Result<Vec<CorpusCase>> {
    let mut cases = Vec::new();
    let entries = fs::read_dir(corpus_dir)?;
    for entry in entries.flatten() {
        let repo = entry.path();
        if !repo.is_dir() {
            continue;
        }
        if entry.file_name().to_string_lossy().starts_with('.') {
            continue;
        }
        let name = repo
            .file_name()
            .map(|s| s.to_string_lossy().to_string())
            .unwrap_or_default();
        let golden = golden_dir.join(format!("{name}.jsonl"));
        cases.push(CorpusCase { name, repo, golden });
    }
    cases.sort_by(|a, b| a.name.cmp(&b.name));
    Ok(cases)
}

/// Run one case. When `update` is set, a missing or diverging golden is
/// (over)written instead of being reported as a failure.
pub fn run_case(case: &CorpusCase, update: bool) -> CaseOutcome {
    let analysis = match analyze_dir(&case.repo) {
        Ok(a) => a,
        Err(e) => {
            return CaseOutcome {
                name: case.name.clone(),
                nodes: 0,
                edges: 0,
                status: CaseStatus::AnalysisError(e.to_string()),
            };
        }
    };
    let nodes = analysis.graph.node_count();
    let edges = analysis.graph.edge_count();
    let actual = analysis.graph.to_jsonl();

    let golden = fs::read_to_string(&case.golden).ok();

    let status = match golden {
        None => {
            if update {
                write_golden(&case.golden, &actual);
                CaseStatus::Written
            } else {
                CaseStatus::Missing
            }
        }
        Some(expected) => {
            if expected == actual {
                CaseStatus::Pass
            } else if update {
                write_golden(&case.golden, &actual);
                CaseStatus::Written
            } else {
                let (added, removed) = diff_lines(&expected, &actual);
                CaseStatus::Diff { added, removed }
            }
        }
    };

    CaseOutcome {
        name: case.name.clone(),
        nodes,
        edges,
        status,
    }
}

/// Run the whole corpus loop. Returns one outcome per case.
pub fn run_all(
    corpus_dir: &Path,
    golden_dir: &Path,
    update: bool,
) -> std::io::Result<Vec<CaseOutcome>> {
    if update {
        let _ = fs::create_dir_all(golden_dir);
    }
    let cases = discover(corpus_dir, golden_dir)?;
    Ok(cases.iter().map(|c| run_case(c, update)).collect())
}

fn write_golden(path: &Path, body: &str) {
    if let Some(parent) = path.parent() {
        let _ = fs::create_dir_all(parent);
    }
    let _ = fs::write(path, body);
}

/// Line-level diff: lines present only in `actual` (added) and only in
/// `expected` (removed). Order-preserving against the source they came from.
fn diff_lines(expected: &str, actual: &str) -> (Vec<String>, Vec<String>) {
    let exp: Vec<&str> = expected.lines().collect();
    let act: Vec<&str> = actual.lines().collect();
    let exp_set: std::collections::HashSet<&str> = exp.iter().copied().collect();
    let act_set: std::collections::HashSet<&str> = act.iter().copied().collect();

    let added: Vec<String> = act
        .iter()
        .filter(|l| !exp_set.contains(**l))
        .map(|l| l.to_string())
        .collect();
    let removed: Vec<String> = exp
        .iter()
        .filter(|l| !act_set.contains(**l))
        .map(|l| l.to_string())
        .collect();
    (added, removed)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn diff_detects_added_and_removed() {
        let (added, removed) = diff_lines("a\nb\nc\n", "a\nc\nd\n");
        assert_eq!(added, vec!["d".to_string()]);
        assert_eq!(removed, vec!["b".to_string()]);
    }

    #[test]
    fn identical_output_has_no_diff() {
        let (added, removed) = diff_lines("x\ny\n", "x\ny\n");
        assert!(added.is_empty() && removed.is_empty());
    }

    #[test]
    fn corpus_is_discoverable_and_nonempty() {
        // Tests run with the eval crate dir as CWD.
        let cases =
            discover(Path::new("corpus"), Path::new("golden")).expect("corpus dir should exist");
        assert!(!cases.is_empty(), "expected at least one vendored corpus");
        // Every case must carry *some* analyzable source — a crate manifest,
        // a `src/`, or (since TT-60) a non-crate fixture tree like the
        // Salesforce `sforg` metadata org. Presence + a golden is the contract.
        for c in &cases {
            let has_content = c.repo.join("Cargo.toml").exists()
                || c.repo.join("src").exists()
                || std::fs::read_dir(&c.repo)
                    .map(|mut d| d.next().is_some())
                    .unwrap_or(false);
            assert!(has_content, "{} is empty", c.name);
        }
    }

    #[test]
    fn corpus_matches_committed_goldens() {
        // The committed goldens must match current analyzer output exactly.
        // If this fails after an intentional change, run `regress --update`.
        let outcomes = run_all(Path::new("corpus"), Path::new("golden"), false)
            .expect("corpus run should not error");
        let regressions: Vec<&CaseOutcome> =
            outcomes.iter().filter(|o| !o.status.passed()).collect();
        assert!(
            regressions.is_empty(),
            "corpus regressions: {:?}",
            regressions
                .iter()
                .map(|o| format!("{} -> {}", o.name, o.status.label()))
                .collect::<Vec<_>>()
        );
    }
}
