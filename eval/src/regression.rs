//! Self-analysis regression: run TrailTracker on a real repository (its own
//! workspace) and assert the invariants that must always hold, plus determinism.
//!
//! We assert *invariants and lower bounds*, not exact counts — counts drift as
//! the codebase grows, but losslessness, crash-freedom, and determinism must
//! never regress.

use std::path::Path;

use trailtracker::pipeline::{analyze_dir, Analysis};

pub struct RegressionResult {
    pub files: usize,
    pub lossless_files: usize,
    pub parse_failures: usize,
    pub error_bytes: usize,
    pub nodes: usize,
    pub edges: usize,
    pub deterministic: bool,
    pub violations: Vec<String>,
}

impl RegressionResult {
    pub fn passed(&self) -> bool {
        self.violations.is_empty()
    }
}

/// Analyze `root` twice and check invariants + determinism.
pub fn run(root: &Path) -> std::io::Result<RegressionResult> {
    let a: Analysis = analyze_dir(root)?;
    let b: Analysis = analyze_dir(root)?;

    let jsonl_a = a.graph.to_jsonl();
    let jsonl_b = b.graph.to_jsonl();
    let deterministic = jsonl_a == jsonl_b;

    let mut violations = Vec::new();
    if a.stats.lossless_files != a.stats.files {
        violations.push(format!(
            "lossless regression: {}/{} files reconstructed source",
            a.stats.lossless_files, a.stats.files
        ));
    }
    if a.stats.parse_failures != 0 {
        violations.push(format!(
            "{} file(s) failed to parse",
            a.stats.parse_failures
        ));
    }
    if a.stats.error_bytes != 0 {
        violations.push(format!("{} parser error byte(s)", a.stats.error_bytes));
    }
    if !deterministic {
        violations.push("non-deterministic graph output across two runs".to_string());
    }
    if a.stats.files == 0 {
        violations.push("no files analyzed (corpus missing?)".to_string());
    }
    if a.graph.node_count() < 50 {
        violations.push(format!(
            "implausibly small graph: {} nodes",
            a.graph.node_count()
        ));
    }

    Ok(RegressionResult {
        files: a.stats.files,
        lossless_files: a.stats.lossless_files,
        parse_failures: a.stats.parse_failures,
        error_bytes: a.stats.error_bytes,
        nodes: a.graph.node_count(),
        edges: a.graph.edge_count(),
        deterministic,
        violations,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn self_analysis_invariants_hold() {
        // Tests run with the crate dir as CWD; the workspace root is one up.
        let root = Path::new("..");
        let result = run(root).expect("analysis should not error");
        assert!(result.passed(), "violations: {:?}", result.violations);
        assert!(result.deterministic);
    }
}
