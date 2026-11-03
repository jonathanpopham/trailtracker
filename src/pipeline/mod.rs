//! The end-to-end pipeline: discover sources of *every* supported language under
//! a directory, parse each to a lossless CST via its [`LanguageFrontEnd`], and
//! lower them all into one canonical graph.
//!
//! Language dispatch is data-driven: each file's extension selects a front end
//! from the central registry ([`crate::lang::frontend::front_ends`]); files no
//! front end claims are skipped. Each front end lowers the batch of files it owns
//! into the single shared graph, so a polyglot repository produces one merged
//! graph. Cross-language symbol resolution stays per-language for now.
//!
//! The Cargo manifest reader here is a deliberately small, std-only scan — just
//! enough to recover the package name and dependency names. It is not a full TOML
//! parser (that is a separate grammar on the roadmap), and it does not pretend to
//! be: anything it cannot read is simply absent, never fabricated. Languages
//! without a manifest concept simply ignore these fields.

use std::collections::BTreeSet;
use std::fs;
use std::io;
use std::panic::AssertUnwindSafe;
use std::path::{Path, PathBuf};

use crate::core::cst::ParseTree;
use crate::core::span::fnv1a_64;
use crate::graph::Graph;
use crate::lang::frontend::{
    front_end_for_path, front_ends, LanguageFrontEnd, LoweredInput, SourceFile,
};

mod cache;
mod ignore;
mod linker;

#[derive(Clone, Copy, Debug, Default)]
pub struct AnalysisStats {
    pub files: usize,
    pub lossless_files: usize,
    pub diagnostics: usize,
    pub error_bytes: usize,
    pub total_bytes: usize,
    /// Files whose parse panicked and were isolated (should be 0).
    pub parse_failures: usize,
}

pub struct Analysis {
    pub graph: Graph,
    pub stats: AnalysisStats,
}

/// One parsed file of the batch currently being lowered. Trees are held here
/// so the borrowed [`SourceFile`] lowering inputs stay valid.
struct ParsedFile {
    rel: String,
    module_path: Vec<String>,
    tree: ParseTree,
}

/// One readable claimed source file, before parsing. Contents are read exactly
/// once and feed both parsing and (when caching) the per-file content hashes.
struct RawFile {
    fe_idx: usize,
    rel: String,
    source: String,
}

/// Knobs for [`analyze_dir_with`]. The default is a plain, uncached analysis —
/// byte-identical to what [`analyze_dir`] has always produced.
#[derive(Default)]
pub struct AnalyzeOptions {
    /// When set, per-language-batch lowered subgraphs are cached under this
    /// directory (opt-in `--incremental` / `TRAILTRACKER_CACHE`): unchanged
    /// batches are spliced from cache, changed ones are relowered and
    /// rewritten. Output is byte-identical either way — the cache is an
    /// accelerator, never an authority (see [`cache`] for the design and why
    /// the sound unit is the language batch, not the single file).
    pub cache_dir: Option<PathBuf>,
    /// Emit the CPG overlay (ADR-0003): intra-function `Statement` nodes plus
    /// `FLOWS_TO`/`DATA_DEP` edges, for front ends that implement it. The base
    /// graph lines are byte-identical either way — the overlay only adds.
    /// The overlay is never cached: `cpg` forces a full uncached lowering so
    /// cache entries stay base-graph-only (soundness over speed).
    pub cpg: bool,
    /// Analyze everything on disk, ignoring `.gitignore` (`--no-ignore`).
    /// By default, when the analyzed root is a git checkout (a `.git` entry
    /// exists directly under it), files matched by the repo's layered
    /// `.gitignore` rules are excluded from the walk: untracked build outputs
    /// (minified bundles, `bin`/`obj`, coverage dumps) are not source and
    /// silently corrupt stats and every derived view (bead ei8, the
    /// `docs-site/out` incident). Trees without a `.git` entry are never
    /// filtered, so fixtures and exported sources are unaffected. See
    /// [`ignore`] for the exact supported pattern subset.
    pub no_ignore: bool,
}

/// Analyze every supported source file under `root` and return the canonical
/// graph plus honest coverage statistics. Files are dispatched to the front end
/// whose extensions match; everything is merged into one graph.
pub fn analyze_dir(root: &Path) -> io::Result<Analysis> {
    analyze_dir_with(root, &AnalyzeOptions::default())
}

/// [`analyze_dir_with`] taking options by value — convenience for callers that
/// build options inline (the `cpg` command, tests).
pub fn analyze_dir_opts(root: &Path, opts: AnalyzeOptions) -> io::Result<Analysis> {
    analyze_dir_with(root, &opts)
}

/// [`analyze_dir`] with options (incremental cache, CPG overlay). Invariant:
/// for any input tree, the base result is byte-identical with a cold cache, a
/// warm cache, a stale cache, or no cache at all; `cpg` adds overlay lines and
/// disables the cache for that run.
pub fn analyze_dir_with(root: &Path, opts: &AnalyzeOptions) -> io::Result<Analysis> {
    let timing = std::env::var_os("TRAILTRACKER_TIMING").is_some();
    let t0 = std::time::Instant::now();
    let front_ends = front_ends();
    let (package, deps) = read_manifest(root);

    let mut src_files: Vec<PathBuf> = Vec::new();
    collect_source_files(root, &front_ends, &mut src_files, !opts.no_ignore)?;
    src_files.sort();
    if timing {
        eprintln!(
            "timing: discover {} files in {:?}",
            src_files.len(),
            t0.elapsed()
        );
    }

    // Read every claimed file once, in deterministic (sorted-path) order.
    // Files we cannot read as UTF-8 (binaries mislabelled with a source
    // extension, latin-1, etc.) are recorded as failures rather than aborting
    // the whole repo — surfaced, never silently dropped.
    let t_read = std::time::Instant::now();
    let mut raw: Vec<RawFile> = Vec::new();
    let mut failed: Vec<(usize, String)> = Vec::new();
    for path in &src_files {
        let rel = rel_path(root, path);
        let Some(fe_idx) = file_front_end(&front_ends, &rel) else {
            continue; // no front end claims this extension
        };
        match fs::read_to_string(path) {
            Ok(source) => raw.push(RawFile {
                fe_idx,
                rel,
                source,
            }),
            Err(_) => failed.push((fe_idx, rel)),
        }
    }
    if timing {
        eprintln!("timing: read {:?}", t_read.elapsed());
    }

    // The CPG overlay is never cached: entries must stay base-graph-only, so
    // `cpg` forces a full uncached lowering (soundness over speed).
    let cache = if opts.cpg {
        None
    } else {
        opts.cache_dir
            .as_deref()
            .and_then(|dir| cache::Cache::open(dir, root))
    };

    let mut stats = AnalysisStats {
        files: 0,
        lossless_files: 0,
        diagnostics: 0,
        error_bytes: 0,
        total_bytes: 0,
        parse_failures: 0,
    };

    // Parse and lower per language batch, in registry order so the merge is
    // deterministic. Each parse is isolated with `catch_unwind`: a single
    // hostile or malformed file cannot abort a whole-repo analysis; failures
    // are recorded explicitly, never silently dropped (conservative failure
    // mode for defense use). Every front end lowers a self-contained subgraph
    // which is then merged — audited invariant: no registered `lower` reads
    // the shared graph (each already builds a fresh subgraph and merges it),
    // so capturing the subgraph here is byte-equivalent to lowering into the
    // shared graph directly (pinned end-to-end by the golden regression gate
    // and `cache_cold_warm_mixed_runs_are_byte_identical`). With a cache, an
    // unchanged batch's subgraph is spliced from disk instead.
    let mut graph = Graph::new();
    let mut active_languages: BTreeSet<&str> = BTreeSet::new();
    for (fe_idx, fe) in front_ends.iter().enumerate() {
        let batch: Vec<&RawFile> = raw.iter().filter(|r| r.fe_idx == fe_idx).collect();
        if batch.is_empty() {
            continue;
        }
        active_languages.insert(fe.name());
        let t_batch = std::time::Instant::now();

        // The batch key: everything `lower` can observe, with one
        // (rel_path, byte_len, fnv1a_64(content)) row per file.
        let key = cache.as_ref().map(|_| {
            let manifest: Vec<(String, u64, u64)> = batch
                .iter()
                .map(|r| {
                    (
                        r.rel.clone(),
                        r.source.len() as u64,
                        fnv1a_64(r.source.as_bytes()),
                    )
                })
                .collect();
            cache::batch_key(fe.name(), &package, &deps, &manifest)
        });

        if let (Some(c), Some(key)) = (cache.as_ref(), key.as_ref()) {
            if let Some(hit) = c.load(fe.name(), key) {
                stats.files += hit.stats.files;
                stats.lossless_files += hit.stats.lossless_files;
                stats.diagnostics += hit.stats.diagnostics;
                stats.error_bytes += hit.stats.error_bytes;
                stats.total_bytes += hit.stats.total_bytes;
                for rel in hit.panicked {
                    failed.push((fe_idx, rel));
                }
                graph.merge(hit.sub);
                if timing {
                    eprintln!(
                        "timing: {} batch ({} files) cache hit {:?}",
                        fe.name(),
                        batch.len(),
                        t_batch.elapsed()
                    );
                }
                continue;
            }
        }

        // Cold path: parse the batch, lower it into a fresh subgraph, splice,
        // and (when caching) store the entry.
        let mut parsed: Vec<ParsedFile> = Vec::new();
        let mut panicked: Vec<String> = Vec::new();
        for r in &batch {
            let module_path = fe.module_path(&r.rel);
            let result = std::panic::catch_unwind(AssertUnwindSafe(|| fe.parse(&r.rel, &r.source)));
            match result {
                Ok(tree) => parsed.push(ParsedFile {
                    rel: r.rel.clone(),
                    module_path,
                    tree,
                }),
                Err(_) => panicked.push(r.rel.clone()),
            }
        }

        let mut bstats = cache::BatchStats {
            files: parsed.len(),
            ..Default::default()
        };
        for p in &parsed {
            let t = &p.tree;
            if t.is_lossless() {
                bstats.lossless_files += 1;
            }
            bstats.diagnostics += t.diagnostics.len();
            bstats.error_bytes += (t.error_byte_ratio() * t.source.len() as f64).round() as usize;
            bstats.total_bytes += t.source.len();
        }

        let files: Vec<SourceFile> = parsed
            .iter()
            .map(|p| SourceFile {
                rel_path: p.rel.clone(),
                module_path: p.module_path.clone(),
                source: &p.tree.source,
                root: &p.tree.root,
            })
            .collect();
        let input = LoweredInput {
            package: &package,
            manifest_deps: &deps,
            files,
        };
        let mut sub = Graph::new();
        if opts.cpg {
            fe.lower_cpg(&input, &mut sub);
        } else {
            fe.lower(&input, &mut sub);
        }
        if let (Some(c), Some(key)) = (cache.as_ref(), key.as_ref()) {
            c.store(fe.name(), key, &sub, bstats, &panicked);
        }
        graph.merge(sub);

        stats.files += bstats.files;
        stats.lossless_files += bstats.lossless_files;
        stats.diagnostics += bstats.diagnostics;
        stats.error_bytes += bstats.error_bytes;
        stats.total_bytes += bstats.total_bytes;
        for rel in panicked {
            failed.push((fe_idx, rel));
        }
        if timing {
            eprintln!(
                "timing: {} batch ({} files) parse+lower {:?}",
                fe.name(),
                batch.len(),
                t_batch.elapsed()
            );
        }
    }
    if let Some(c) = &cache {
        c.prune(&active_languages);
    }
    stats.parse_failures = failed.len();

    // Surface parse failures as explicit File nodes so they are never invisible,
    // tagged with the language of the front end that owns the file.
    for (fe_idx, rel) in &failed {
        let id = format!("file::{rel}");
        graph.upsert_node(
            id,
            "File",
            rel.rsplit('/').next().unwrap_or(rel).to_string(),
            vec![
                ("path", crate::core::json::Json::str(rel.clone())),
                (
                    "language",
                    crate::core::json::Json::str(front_ends[*fe_idx].name()),
                ),
                ("parse_failed", crate::core::json::Json::Bool(true)),
            ],
        );
    }

    let t_link = std::time::Instant::now();
    // Cross-provider linking (TT-62): every front end has now lowered into the
    // single merged graph, so unresolved references one provider could only name
    // (a Flow's `actionCalls`) can be resolved against another provider's real
    // definitions (an Apex `@InvocableMethod`). Additive + deterministic.
    linker::link_cross_provider(&mut graph);
    if timing {
        eprintln!(
            "timing: link {:?}; total {:?}",
            t_link.elapsed(),
            t0.elapsed()
        );
    }

    Ok(Analysis { graph, stats })
}

/// Front end index for a file: the first registered front end that claims the
/// repo-relative path (extension match by default; compound suffixes and
/// extension-less names via `claims` overrides).
fn file_front_end(front_ends: &[Box<dyn LanguageFrontEnd>], rel: &str) -> Option<usize> {
    front_end_for_path(front_ends, rel)
}

/// Recursively collect files claimed by any front end, skipping build output
/// and VCS directories. When `respect_gitignore` is set and `root` is a git
/// checkout (`.git` exists directly under it — a directory for clones, a file
/// for worktrees/submodules), entries matched by the repo's layered
/// `.gitignore` rules are excluded too: build artifacts on disk are not
/// source (bead ei8). Trees without `.git` are never filtered.
fn collect_source_files(
    root: &Path,
    front_ends: &[Box<dyn LanguageFrontEnd>],
    out: &mut Vec<PathBuf>,
    respect_gitignore: bool,
) -> io::Result<()> {
    let mut ignores =
        (respect_gitignore && root.join(".git").exists()).then(ignore::IgnoreStack::new);
    let mut rel: Vec<String> = Vec::new();
    walk_collect(root, Some(front_ends), out, &mut ignores, &mut rel)
}

/// Collect every regular file using the pipeline's deterministic tree walk and
/// layered gitignore filtering, without restricting paths to registered source
/// front ends. Callers sort the result before reading, as the analysis pipeline
/// does for source files.
pub(crate) fn collect_repository_files(
    root: &Path,
    out: &mut Vec<PathBuf>,
    respect_gitignore: bool,
) -> io::Result<()> {
    let mut ignores =
        (respect_gitignore && root.join(".git").exists()).then(ignore::IgnoreStack::new);
    let mut rel = Vec::new();
    walk_collect(root, None, out, &mut ignores, &mut rel)
}

/// Match a repository-relative path with the documented std-only gitignore glob
/// subset (`*`, `?`, `**`, slash anchoring).
pub(crate) fn path_matches_glob(pattern: &str, path: &str) -> bool {
    ignore::path_matches(pattern, path)
}

fn walk_collect(
    dir: &Path,
    front_ends: Option<&[Box<dyn LanguageFrontEnd>]>,
    out: &mut Vec<PathBuf>,
    ignores: &mut Option<ignore::IgnoreStack>,
    rel: &mut Vec<String>,
) -> io::Result<()> {
    let pushed = match ignores {
        Some(stack) => stack.push_dir(dir, rel.len()),
        None => false,
    };
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        let file_type = entry.file_type()?;
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if file_type.is_dir() {
            if matches!(name.as_ref(), "target" | ".git" | "node_modules") || name.starts_with('.')
            {
                continue;
            }
            rel.push(name.into_owned());
            if !is_ignored(ignores, rel, true) {
                walk_collect(&path, front_ends, out, ignores, rel)?;
            }
            rel.pop();
        } else if file_type.is_file() {
            let claimed = match front_ends {
                Some(front_ends) => front_end_for_path(front_ends, name.as_ref()).is_some(),
                None => true,
            };
            if claimed {
                rel.push(name.into_owned());
                if !is_ignored(ignores, rel, false) {
                    out.push(path);
                }
                rel.pop();
            }
        }
    }
    if pushed {
        if let Some(stack) = ignores {
            stack.pop_dir();
        }
    }
    Ok(())
}

/// Test `rel` against the gitignore stack (no stack: nothing is ignored).
fn is_ignored(ignores: &Option<ignore::IgnoreStack>, rel: &[String], is_dir: bool) -> bool {
    match ignores {
        Some(stack) => {
            let segs: Vec<&str> = rel.iter().map(String::as_str).collect();
            stack.is_ignored(&segs, is_dir)
        }
        None => false,
    }
}

fn rel_path(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/")
}

/// Minimal manifest read: package name and dependency names. Returns a default
/// package name derived from the directory when no manifest is found.
fn read_manifest(root: &Path) -> (String, Vec<String>) {
    let default_name = root
        .file_name()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "crate".to_string());

    let manifest = root.join("Cargo.toml");
    let text = match fs::read_to_string(&manifest) {
        Ok(t) => t,
        Err(_) => return (default_name, Vec::new()),
    };

    let mut name = default_name;
    let mut deps = Vec::new();
    let mut section = "";
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if line.starts_with('[') && line.ends_with(']') {
            section = match line {
                "[package]" => "package",
                "[dependencies]" | "[dev-dependencies]" | "[build-dependencies]" => "dependencies",
                _ => "other",
            };
            continue;
        }
        match section {
            "package" => {
                if let Some(v) = kv(line, "name") {
                    name = v;
                }
            }
            "dependencies" => {
                if let Some((key, _)) = line.split_once('=') {
                    let dep = key.trim().trim_matches('"').to_string();
                    if !dep.is_empty() && !deps.contains(&dep) {
                        deps.push(dep);
                    }
                }
            }
            _ => {}
        }
    }
    (name, deps)
}

fn kv(line: &str, key: &str) -> Option<String> {
    let (k, v) = line.split_once('=')?;
    if k.trim() != key {
        return None;
    }
    Some(v.trim().trim_matches('"').to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    /// A small polyglot fixture with a cross-file Rust call (exercising the
    /// batch-wide resolution ladder) plus a Python file, so the cache handles
    /// two independent language batches.
    fn write_fixture(root: &Path) {
        fs::create_dir_all(root.join("src")).unwrap();
        fs::create_dir_all(root.join("tools")).unwrap();
        fs::write(
            root.join("Cargo.toml"),
            "[package]\nname = \"fixture\"\n\n[dependencies]\nserde = \"1\"\n",
        )
        .unwrap();
        fs::write(
            root.join("src/lib.rs"),
            "mod util;\n\npub fn top() {\n    util::helper();\n}\n",
        )
        .unwrap();
        fs::write(root.join("src/util.rs"), "pub fn helper() {}\n").unwrap();
        fs::write(
            root.join("tools/script.py"),
            "def py_fn():\n    return 1\n\npy_fn()\n",
        )
        .unwrap();
    }

    fn temp_root(tag: &str) -> PathBuf {
        let dir =
            std::env::temp_dir().join(format!("tt-pipeline-cache-{}-{tag}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    fn stats_tuple(s: &AnalysisStats) -> (usize, usize, usize, usize, usize, usize) {
        (
            s.files,
            s.lossless_files,
            s.diagnostics,
            s.error_bytes,
            s.total_bytes,
            s.parse_failures,
        )
    }

    /// THE invariant of the incremental cache: for the same tree, an uncached
    /// run, a cold cached run, a warm cached run, a mixed run (one file
    /// changed against a stale cache), and a reverted run are all
    /// byte-identical — graph and statistics.
    #[test]
    fn cache_cold_warm_mixed_runs_are_byte_identical() {
        let root = temp_root("invariant");
        write_fixture(&root);
        let cache_dir = root.join(".trailtracker-cache");
        let opts = AnalyzeOptions {
            cpg: false,
            cache_dir: Some(cache_dir.clone()),
            ..Default::default()
        };

        let base = analyze_dir(&root).unwrap();
        let base_jsonl = base.graph.to_jsonl();
        // The fixture must exercise cross-file resolution or the test is weak.
        assert!(
            base_jsonl.contains("\"CALLS\""),
            "fixture lost its cross-file call:\n{base_jsonl}"
        );

        let cold = analyze_dir_with(&root, &opts).unwrap();
        assert_eq!(cold.graph.to_jsonl(), base_jsonl, "cold != uncached");
        assert_eq!(stats_tuple(&cold.stats), stats_tuple(&base.stats));
        // Entries were written for both language batches, and the cache
        // ignores itself in version control.
        let entries: Vec<String> = walk_files(&cache_dir);
        assert!(
            entries.iter().any(|p| p.ends_with("rust.jsonl")),
            "no rust entry in {entries:?}"
        );
        assert!(
            entries.iter().any(|p| p.ends_with("python.jsonl")),
            "no python entry in {entries:?}"
        );
        assert_eq!(
            fs::read_to_string(cache_dir.join(".gitignore")).unwrap(),
            "*\n"
        );

        let warm = analyze_dir_with(&root, &opts).unwrap();
        assert_eq!(warm.graph.to_jsonl(), base_jsonl, "warm != cold");
        assert_eq!(stats_tuple(&warm.stats), stats_tuple(&base.stats));

        // Touch one Rust file: the rust batch is stale, python still cached.
        let util = root.join("src/util.rs");
        let original = fs::read_to_string(&util).unwrap();
        fs::write(&util, "pub fn helper() {}\npub fn extra() {}\n").unwrap();
        let mixed = analyze_dir_with(&root, &opts).unwrap();
        let fresh = analyze_dir(&root).unwrap();
        assert_eq!(
            mixed.graph.to_jsonl(),
            fresh.graph.to_jsonl(),
            "mixed run against a stale cache diverged from a fresh analysis"
        );
        assert_eq!(stats_tuple(&mixed.stats), stats_tuple(&fresh.stats));

        // Revert: the (rewritten) cache must reproduce the original bytes.
        fs::write(&util, original).unwrap();
        let reverted = analyze_dir_with(&root, &opts).unwrap();
        assert_eq!(reverted.graph.to_jsonl(), base_jsonl, "revert != original");

        // Delete the Python file: its batch vanishes and its entry is pruned.
        fs::remove_file(root.join("tools/script.py")).unwrap();
        let pruned = analyze_dir_with(&root, &opts).unwrap();
        let expect = analyze_dir(&root).unwrap();
        assert_eq!(pruned.graph.to_jsonl(), expect.graph.to_jsonl());
        let entries: Vec<String> = walk_files(&cache_dir);
        assert!(
            !entries.iter().any(|p| p.ends_with("python.jsonl")),
            "stale python entry survived pruning: {entries:?}"
        );

        let _ = fs::remove_dir_all(&root);
    }

    /// A corrupt or torn cache entry is a miss (relower + rewrite), never an
    /// error and never wrong output.
    #[test]
    fn corrupt_cache_entries_degrade_to_recomputation() {
        let root = temp_root("corrupt");
        write_fixture(&root);
        let cache_dir = root.join(".trailtracker-cache");
        let opts = AnalyzeOptions {
            cpg: false,
            cache_dir: Some(cache_dir.clone()),
            ..Default::default()
        };
        let base = analyze_dir(&root).unwrap().graph.to_jsonl();
        analyze_dir_with(&root, &opts).unwrap();

        for entry in walk_files(&cache_dir) {
            if entry.ends_with("rust.jsonl") {
                // Truncate mid-line: a torn write must not half-load.
                let text = fs::read_to_string(&entry).unwrap();
                fs::write(&entry, &text[..text.len() / 2]).unwrap();
            }
        }
        let after = analyze_dir_with(&root, &opts).unwrap();
        assert_eq!(after.graph.to_jsonl(), base, "corrupt entry changed output");
        // And the entry was healed for the next run.
        let healed = analyze_dir_with(&root, &opts).unwrap();
        assert_eq!(healed.graph.to_jsonl(), base);
        let _ = fs::remove_dir_all(&root);
    }

    /// The cache key includes the manifest: editing Cargo.toml (package name or
    /// dependency set feeds every batch's `LoweredInput`) must invalidate.
    #[test]
    fn manifest_changes_invalidate_the_cache() {
        let root = temp_root("manifest");
        write_fixture(&root);
        let opts = AnalyzeOptions {
            cpg: false,
            cache_dir: Some(root.join(".trailtracker-cache")),
            ..Default::default()
        };
        analyze_dir_with(&root, &opts).unwrap();
        fs::write(
            root.join("Cargo.toml"),
            "[package]\nname = \"renamed\"\n\n[dependencies]\nserde = \"1\"\n",
        )
        .unwrap();
        let mixed = analyze_dir_with(&root, &opts).unwrap();
        let fresh = analyze_dir(&root).unwrap();
        assert_eq!(mixed.graph.to_jsonl(), fresh.graph.to_jsonl());
        assert!(
            mixed.graph.to_jsonl().contains("renamed"),
            "stale package name served from cache"
        );
        let _ = fs::remove_dir_all(&root);
    }

    /// Regression for bead ei8 (the `docs-site/out` incident): a gitignored
    /// build-output directory containing a file that parses with error bytes
    /// must be excluded from analysis by default — untracked artifacts on
    /// disk corrupted self-analysis stats and would corrupt any client-repo
    /// domain/dossier counts. `no_ignore` restores the analyze-everything
    /// walk, and trees without a `.git` entry are never filtered.
    #[test]
    fn gitignored_build_outputs_are_excluded_by_default() {
        let root = temp_root("gitignore-ei8");
        write_fixture(&root);
        // Minified-bundle stand-in: garbage a JS parse cannot fully consume,
        // so its inclusion is visible as error_bytes — exactly the byte that
        // failed the regression gate in the incident.
        fs::create_dir_all(root.join("out")).unwrap();
        fs::write(
            root.join("out/app.min.js"),
            "!function(){for(;;)break a;}();#%@ )]}'\n",
        )
        .unwrap();
        fs::write(root.join(".gitignore"), "out/\n").unwrap();

        // No .git entry: the tree is not a checkout, .gitignore is inert and
        // everything on disk is analyzed (fixtures/exports stay unfiltered).
        let plain = analyze_dir(&root).unwrap();
        assert!(
            plain.graph.to_jsonl().contains("out/app.min.js"),
            "without .git the artifact must still be analyzed"
        );
        assert!(plain.stats.error_bytes > 0, "fixture lost its error bytes");

        // A git checkout: the ignored build output is excluded by default...
        fs::create_dir_all(root.join(".git")).unwrap();
        let filtered = analyze_dir(&root).unwrap();
        assert!(
            !filtered.graph.to_jsonl().contains("out/app.min.js"),
            "gitignored build output leaked into analysis:\n{}",
            filtered.graph.to_jsonl()
        );
        assert_eq!(filtered.stats.error_bytes, 0, "artifact error bytes leaked");
        assert_eq!(filtered.stats.files, plain.stats.files - 1);

        // ...and `no_ignore` deliberately brings it back (analyze everything).
        let everything = analyze_dir_opts(
            &root,
            AnalyzeOptions {
                no_ignore: true,
                ..Default::default()
            },
        )
        .unwrap();
        assert!(everything.graph.to_jsonl().contains("out/app.min.js"));
        assert_eq!(everything.stats.files, plain.stats.files);
        assert!(everything.stats.error_bytes > 0);

        // Layering: a nested .gitignore filters beneath its own directory.
        fs::create_dir_all(root.join("tools/gen")).unwrap();
        fs::write(root.join("tools/.gitignore"), "gen/\n").unwrap();
        fs::write(root.join("tools/gen/junk.py"), "def gen():\n    pass\n").unwrap();
        let nested = analyze_dir(&root).unwrap();
        assert!(
            !nested.graph.to_jsonl().contains("tools/gen/junk.py"),
            "nested .gitignore was not respected"
        );

        let _ = fs::remove_dir_all(&root);
    }

    fn walk_files(dir: &Path) -> Vec<String> {
        let mut out = Vec::new();
        let Ok(rd) = fs::read_dir(dir) else {
            return out;
        };
        for e in rd.flatten() {
            let p = e.path();
            if p.is_dir() {
                out.extend(walk_files(&p));
            } else {
                out.push(p.to_string_lossy().to_string());
            }
        }
        out
    }

    #[test]
    fn dispatches_files_by_extension() {
        let fes = front_ends();
        assert_eq!(
            file_front_end(&fes, "src/core/span.rs").map(|i| fes[i].name()),
            Some("rust")
        );
        // Unknown and extensionless files are claimed by no front end.
        assert_eq!(file_front_end(&fes, "README.md"), None);
        assert_eq!(file_front_end(&fes, "Makefile"), None);
    }
}
