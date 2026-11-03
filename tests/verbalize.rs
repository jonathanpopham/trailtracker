//! Self-conformance gate for the verbalizer (V1, epic E-V): the engine
//! polices itself.
//!
//! Runs the FULL pipeline (discover → parse → lower → graph) over real
//! eval-corpus fixtures and asserts three properties on the rendered
//! documents:
//!
//! 1. **Grammar conformance** — `grammar::check` returns ZERO violations for
//!    every view on real output, not just on unit fixtures. A template edit
//!    that drifts outside ADR-0008 fails here before any golden moves.
//! 2. **Byte determinism** — two independent analyses render byte-identical
//!    documents (the corpus regression discipline applied to prose).
//! 3. **Golden stability** — the `all` view is pinned byte-for-byte under
//!    `tests/golden_verbalize/`. Re-bless after an INTENTIONAL change with
//!    `UPDATE_GOLDENS=1 cargo test --test verbalize`, then review the diff
//!    before committing (same contract as `benchmarks/golden_check.sh`;
//!    this golden lives in the Rust test so `cargo test` — and therefore
//!    `verify.sh` — gates it with no extra CI step).

#![forbid(unsafe_code)]

use std::fs;
use std::path::{Path, PathBuf};

use trailtracker::pipeline::analyze_dir;
use trailtracker::verbalize::{verbalize, verbalize_target, Options, View};

/// The self-contained corpus fixtures the gate runs over: `calc` (Rust,
/// external deps, no violations) and `sforg` (Salesforce org: Apex +
/// metadata XML — the multi-frontend shape).
const FIXTURES: &[&str] = &["eval/corpus/calc", "eval/corpus/sforg"];

fn all_views() -> Vec<View> {
    vec![
        View::Summary,
        View::Hotspots,
        View::Dependents,
        View::Violations,
        View::Domains,
        View::All,
    ]
}

fn golden_path(fixture: &str) -> PathBuf {
    let name = fixture.rsplit('/').next().unwrap();
    Path::new("tests/golden_verbalize").join(format!("{name}__all.txt"))
}

/// The corpus fixtures, plus an optional real repo: set `VERBALIZE_EXTRA_DIR`
/// to point the conformance gate at any checkout (e.g. a client codebase)
/// without touching the pinned goldens.
fn conformance_fixtures() -> Vec<String> {
    let mut dirs: Vec<String> = FIXTURES.iter().map(|f| (*f).to_string()).collect();
    if let Ok(extra) = std::env::var("VERBALIZE_EXTRA_DIR") {
        if !extra.is_empty() {
            dirs.push(extra);
        }
    }
    dirs
}

#[test]
fn real_pipeline_output_produces_zero_grammar_violations() {
    for fixture in conformance_fixtures() {
        let analysis = analyze_dir(Path::new(&fixture)).expect("analyze fixture");
        for view in all_views() {
            let doc = verbalize(&analysis, &Options { view, budget: None });
            assert!(
                !doc.sentences.is_empty(),
                "{fixture} {}: empty document",
                view.name()
            );
            let violations = doc.check();
            assert!(
                violations.is_empty(),
                "{fixture} {} violates ADR-0008:\n{:#?}\n--- document ---\n{}",
                view.name(),
                violations,
                doc.to_text()
            );
        }
    }
}

#[test]
fn budgeted_documents_stay_conformant_and_honest() {
    for fixture in FIXTURES {
        let analysis = analyze_dir(Path::new(fixture)).expect("analyze fixture");
        let full = verbalize(
            &analysis,
            &Options {
                view: View::All,
                budget: None,
            },
        );
        for budget in [200, 400, full.to_text().len() / 2] {
            let doc = verbalize(
                &analysis,
                &Options {
                    view: View::All,
                    budget: Some(budget),
                },
            );
            let violations = doc.check();
            assert!(
                violations.is_empty(),
                "{fixture} budget {budget}: {violations:#?}"
            );
            if doc.omitted > 0 {
                let last = doc.sentences.last().unwrap();
                assert!(
                    last.starts_with("The budget omits"),
                    "{fixture} budget {budget}: no omission sentence: {last}"
                );
            }
        }
    }
}

#[test]
fn documents_are_byte_deterministic_across_analyses() {
    for fixture in FIXTURES {
        let first = analyze_dir(Path::new(fixture)).expect("analyze fixture");
        let second = analyze_dir(Path::new(fixture)).expect("analyze fixture");
        for view in all_views() {
            let a = verbalize(&first, &Options { view, budget: None });
            let b = verbalize(&second, &Options { view, budget: None });
            assert_eq!(
                a.to_text(),
                b.to_text(),
                "{fixture} {}: two runs differ",
                view.name()
            );
        }
    }
}

#[test]
fn target_documents_conform_on_real_output() {
    let analysis = analyze_dir(Path::new("eval/corpus/calc")).expect("analyze calc");
    let doc = verbalize_target(&analysis, "Engine", None).expect("resolve Engine");
    let violations = doc.check();
    assert!(violations.is_empty(), "{violations:#?}");
    assert_eq!(doc.glossary.len(), 1);
    assert_eq!(doc.glossary[0].handle, "F1");
    // The target card names its dependents (the relational-lookup fix).
    assert!(
        doc.sentences.iter().any(|s| s.contains("dependents of")),
        "{}",
        doc.to_text()
    );
    assert!(
        doc.sentences.iter().any(|s| s.contains("depends on F1")),
        "{}",
        doc.to_text()
    );
}

#[test]
fn all_view_matches_the_golden() {
    for fixture in FIXTURES {
        let analysis = analyze_dir(Path::new(fixture)).expect("analyze fixture");
        let doc = verbalize(
            &analysis,
            &Options {
                view: View::All,
                budget: None,
            },
        );
        let text = doc.to_text();
        let path = golden_path(fixture);
        if std::env::var_os("UPDATE_GOLDENS").is_some() {
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(&path, &text).unwrap();
            continue;
        }
        let golden = fs::read_to_string(&path).unwrap_or_else(|e| {
            panic!(
                "missing golden {} ({e}); bless with UPDATE_GOLDENS=1 cargo test --test verbalize",
                path.display()
            )
        });
        assert_eq!(
            text,
            golden,
            "{fixture}: verbalize output drifted from {}. If the change is intentional, \
             re-bless with UPDATE_GOLDENS=1 cargo test --test verbalize and review the diff.",
            path.display()
        );
    }
}
