//! IR Atlas conformance: keep the living model honest.
//!
//! The Atlas (`docs/ir-atlas.md` + `docs/ir-atlas.graph.jsonl`) is the source of
//! truth for the shared IR. This guard asserts that every node/edge kind the
//! analyzer *actually emits* over the corpus is documented in the Atlas graph as
//! an `irnode::`/`iredge::` entry. A new kind shipped without an Atlas entry
//! fails CI — so the model can never silently drift from the code.

use std::collections::HashSet;
use std::path::Path;

use trailtracker::pipeline::analyze_dir;

/// Collect the distinct node and edge kinds emitted when analyzing `root`.
pub fn emitted_kinds(root: &Path) -> std::io::Result<(HashSet<String>, HashSet<String>)> {
    let analysis = analyze_dir(root)?;
    let mut node_kinds = HashSet::new();
    let mut edge_kinds = HashSet::new();
    for line in analysis.graph.to_jsonl().lines() {
        // The runtime writer emits compact records; pull the kind cheaply without
        // a JSON parser (the eval crate is std-only too).
        if let Some(kind) = field(line, "\"kind\":\"") {
            if line.contains("\"record\":\"node\"") {
                node_kinds.insert(kind);
            } else if line.contains("\"record\":\"edge\"") {
                edge_kinds.insert(kind);
            }
        }
    }
    Ok((node_kinds, edge_kinds))
}

fn field(line: &str, key: &str) -> Option<String> {
    let start = line.find(key)? + key.len();
    let rest = &line[start..];
    let end = rest.find('"')?;
    Some(rest[..end].to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn every_emitted_kind_is_documented_in_the_atlas() {
        // Tests run with the eval crate dir as CWD.
        let atlas = fs::read_to_string("../docs/ir-atlas.graph.jsonl")
            .expect("ir-atlas.graph.jsonl should exist");
        let (nodes, edges) =
            emitted_kinds(Path::new("corpus/calc")).expect("analysis should not error");

        let mut undocumented = Vec::new();
        for k in &nodes {
            if !atlas.contains(&format!("\"irnode::{k}\"")) {
                undocumented.push(format!("node kind `{k}` (add irnode::{k} to the Atlas)"));
            }
        }
        for k in &edges {
            if !atlas.contains(&format!("\"iredge::{k}\"")) {
                undocumented.push(format!("edge kind `{k}` (add iredge::{k} to the Atlas)"));
            }
        }
        assert!(
            undocumented.is_empty(),
            "IR Atlas is out of date — undocumented kinds emitted by the analyzer:\n  {}",
            undocumented.join("\n  ")
        );
    }
}
