//! Rooted dead-code analysis over TrailTracker's merged graph.
//!
//! The engine is read-side only. It materializes graph indexes once, marks
//! liveness from auditable roots, and classifies every unreachable source
//! symbol from deterministic evidence.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use crate::brief_generated;
use crate::core::json::{read, Json};
use crate::explain::{file_of_map, resolve, ExplainError};
use crate::graph::{Graph, GraphNode};
use crate::ir::ontology::{edge, node as ont, parent_relation, relation};

pub const REPORT_FORMAT: &str = "trailtracker.deadcode/v1";

/// Textual-mention files above 4 MiB are not read; the report always discloses
/// how many files this fixed bound excluded.
const MENTION_FILE_SIZE_CAP_BYTES: u64 = 4 * 1024 * 1024;
const MENTION_BINARY_PROBE_BYTES: usize = 4096;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Tier {
    High,
    Medium,
    Transitive,
}

impl Tier {
    fn as_str(self) -> &'static str {
        match self {
            Tier::High => "dead-high",
            Tier::Medium => "dead-medium",
            Tier::Transitive => "transitively-dead",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MinConfidence {
    High,
    Medium,
    Low,
}

impl MinConfidence {
    pub fn parse(value: &str) -> Option<MinConfidence> {
        match value {
            "high" => Some(MinConfidence::High),
            "medium" => Some(MinConfidence::Medium),
            "low" => Some(MinConfidence::Low),
            _ => None,
        }
    }

    fn includes(self, tier: Tier) -> bool {
        match self {
            MinConfidence::High => tier == Tier::High,
            MinConfidence::Medium => matches!(tier, Tier::High | Tier::Medium),
            MinConfidence::Low => true,
        }
    }
}

#[derive(Clone, Debug)]
pub struct DeadcodeConfig {
    pub roots: Vec<String>,
    pub keep: Vec<String>,
    pub test_roots: bool,
    pub public_api: Vec<String>,
    pub mention_exclude: Vec<String>,
}

impl Default for DeadcodeConfig {
    fn default() -> Self {
        Self {
            roots: Vec::new(),
            keep: Vec::new(),
            test_roots: true,
            public_api: Vec::new(),
            mention_exclude: Vec::new(),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConfigErrorKind {
    NotFound,
    Invalid,
    Read,
}

#[derive(Clone, Debug)]
pub struct ConfigError {
    pub kind: ConfigErrorKind,
    pub path: PathBuf,
    pub message: String,
}

fn config_value<'a>(pairs: &'a [(String, read::V)], key: &str) -> Option<&'a read::V> {
    pairs
        .iter()
        .find(|(name, _)| name == key)
        .map(|(_, value)| value)
}

fn config_strings(pairs: &[(String, read::V)], key: &str) -> Result<Vec<String>, String> {
    let Some(value) = config_value(pairs, key) else {
        return Ok(Vec::new());
    };
    let read::V::Arr(items) = value else {
        return Err(format!("field '{key}' must be an array of strings"));
    };
    let mut values = Vec::with_capacity(items.len());
    for (index, item) in items.iter().enumerate() {
        match item {
            read::V::Str(value) if !value.trim().is_empty() => {
                values.push(value.trim().to_string());
            }
            _ => {
                return Err(format!(
                    "field '{key}' item {index} must be a non-empty string"
                ))
            }
        }
    }
    Ok(values)
}

pub fn parse_config(text: &str) -> Result<DeadcodeConfig, String> {
    let read::V::Obj(pairs) =
        read::parse(text).map_err(|error| format!("not valid JSON: {error}"))?
    else {
        return Err("the config must be a JSON object".to_string());
    };
    const FIELDS: &[&str] = &[
        "roots",
        "keep",
        "test_roots",
        "public_api",
        "mention_exclude",
    ];
    for (field, _) in &pairs {
        if !FIELDS.contains(&field.as_str()) {
            return Err(format!("unknown field '{field}'"));
        }
    }
    let test_roots = match config_value(&pairs, "test_roots") {
        None => true,
        Some(read::V::Bool(value)) => *value,
        Some(_) => return Err("field 'test_roots' must be a boolean".to_string()),
    };
    Ok(DeadcodeConfig {
        roots: config_strings(&pairs, "roots")?,
        keep: config_strings(&pairs, "keep")?,
        test_roots,
        public_api: config_strings(&pairs, "public_api")?,
        mention_exclude: config_strings(&pairs, "mention_exclude")?,
    })
}

pub fn load_config(dir: &Path, explicit: Option<&Path>) -> Result<DeadcodeConfig, ConfigError> {
    let path = explicit
        .map(Path::to_path_buf)
        .unwrap_or_else(|| dir.join(".trailtracker-deadcode.json"));
    if !path.exists() {
        if explicit.is_none() {
            return Ok(DeadcodeConfig::default());
        }
        return Err(ConfigError {
            kind: ConfigErrorKind::NotFound,
            message: "config file does not exist".to_string(),
            path,
        });
    }
    let text = fs::read_to_string(&path).map_err(|error| ConfigError {
        kind: ConfigErrorKind::Read,
        message: error.to_string(),
        path: path.clone(),
    })?;
    parse_config(&text).map_err(|message| ConfigError {
        kind: ConfigErrorKind::Invalid,
        message,
        path,
    })
}

#[derive(Clone, Debug)]
pub struct ArgError {
    pub message: String,
    pub fix: String,
}

#[derive(Clone, Debug)]
pub struct CommandOptions {
    pub dir: String,
    pub json: bool,
    pub min_confidence: MinConfidence,
    pub limit: Option<usize>,
    pub why: Option<String>,
    pub no_test_roots: bool,
    pub config: Option<PathBuf>,
    pub incremental: bool,
    pub no_ignore: bool,
}

fn edit_distance(left: &str, right: &str) -> usize {
    let right_chars: Vec<char> = right.chars().collect();
    let mut previous: Vec<usize> = (0..=right_chars.len()).collect();
    for (left_index, left_char) in left.chars().enumerate() {
        let mut current = Vec::with_capacity(right_chars.len() + 1);
        current.push(left_index + 1);
        for (right_index, right_char) in right_chars.iter().enumerate() {
            let cost = usize::from(left_char != *right_char);
            current.push(
                (previous[right_index] + cost)
                    .min(previous[right_index + 1] + 1)
                    .min(current[right_index] + 1),
            );
        }
        previous = current;
    }
    previous[right_chars.len()]
}

fn closest_flag(input: &str) -> Option<&'static str> {
    const FLAGS: &[&str] = &[
        "--json",
        "--robot",
        "--min-confidence",
        "--limit",
        "--why",
        "--no-test-roots",
        "--config",
        "--incremental",
        "--no-ignore",
    ];
    let (distance, candidate) = FLAGS
        .iter()
        .map(|candidate| (edit_distance(input, candidate), *candidate))
        .min()?;
    (distance <= 3).then_some(candidate)
}

fn arg_error(message: impl Into<String>) -> ArgError {
    ArgError {
        message: message.into(),
        fix: "usage: trailtracker deadcode [DIR] [--json] [--min-confidence high|medium|low] \
              [--limit N] [--why TARGET] [--no-test-roots] [--config PATH]"
            .to_string(),
    }
}

pub fn parse_args(args: &[String]) -> Result<CommandOptions, ArgError> {
    let mut options = CommandOptions {
        dir: ".".to_string(),
        json: false,
        min_confidence: MinConfidence::Low,
        limit: None,
        why: None,
        no_test_roots: false,
        config: None,
        incremental: false,
        no_ignore: false,
    };
    let mut positionals = Vec::new();
    let mut index = 0;
    while index < args.len() {
        let argument = args[index].as_str();
        let value_after = |flag: &str, index: &mut usize| -> Result<&str, ArgError> {
            *index += 1;
            args.get(*index)
                .map(String::as_str)
                .ok_or_else(|| arg_error(format!("{flag} requires a value")))
        };
        match argument {
            "--json" | "--robot" => options.json = true,
            "--no-test-roots" => options.no_test_roots = true,
            "--incremental" => options.incremental = true,
            "--no-ignore" => options.no_ignore = true,
            "--min-confidence" => {
                let value = value_after(argument, &mut index)?;
                options.min_confidence = MinConfidence::parse(value).ok_or_else(|| {
                    arg_error(format!(
                        "unknown minimum confidence '{value}' (available: high, medium, low)"
                    ))
                })?;
            }
            "--limit" => {
                let value = value_after(argument, &mut index)?;
                options.limit = Some(value.parse::<usize>().map_err(|_| {
                    arg_error(format!(
                        "--limit expects a non-negative integer, got '{value}'"
                    ))
                })?);
            }
            "--why" => options.why = Some(value_after(argument, &mut index)?.to_string()),
            "--config" => {
                options.config = Some(PathBuf::from(value_after(argument, &mut index)?));
            }
            "--help" | "-h" => {
                return Err(ArgError {
                    message: "`trailtracker deadcode` does not take a --help flag".to_string(),
                    fix: "run `trailtracker help` for command usage".to_string(),
                });
            }
            _ if argument.starts_with("--min-confidence=") => {
                let value = argument.trim_start_matches("--min-confidence=");
                options.min_confidence = MinConfidence::parse(value).ok_or_else(|| {
                    arg_error(format!(
                        "unknown minimum confidence '{value}' (available: high, medium, low)"
                    ))
                })?;
            }
            _ if argument.starts_with("--limit=") => {
                let value = argument.trim_start_matches("--limit=");
                options.limit = Some(value.parse::<usize>().map_err(|_| {
                    arg_error(format!(
                        "--limit expects a non-negative integer, got '{value}'"
                    ))
                })?);
            }
            _ if argument.starts_with("--why=") => {
                options.why = Some(argument.trim_start_matches("--why=").to_string());
            }
            _ if argument.starts_with("--config=") => {
                options.config = Some(PathBuf::from(argument.trim_start_matches("--config=")));
            }
            _ if argument.starts_with('-') => {
                let fix = closest_flag(argument)
                    .map(|flag| format!("did you mean `{flag}`?"))
                    .unwrap_or_else(|| arg_error("").fix);
                return Err(ArgError {
                    message: format!("unknown flag '{argument}' for `deadcode`"),
                    fix,
                });
            }
            _ => positionals.push(argument),
        }
        index += 1;
    }
    if positionals.len() > 1 {
        return Err(arg_error(format!(
            "`deadcode` takes at most one DIR, got: {}",
            positionals.join(" ")
        )));
    }
    if let Some(dir) = positionals.first() {
        options.dir = (*dir).to_string();
    }
    if options
        .why
        .as_ref()
        .is_some_and(|target| target.trim().is_empty())
    {
        return Err(arg_error("--why requires a non-empty target"));
    }
    Ok(options)
}

#[derive(Clone, Debug)]
pub struct Evidence {
    pub inbound_refs: usize,
    pub ambiguous_candidacies: usize,
    pub mention_files: Vec<String>,
    pub exported: bool,
}

#[derive(Clone, Debug)]
pub struct Finding {
    pub id: String,
    pub path: String,
    pub line: u64,
    pub name: String,
    pub kind: &'static str,
    pub tier: Tier,
    pub reason: String,
    pub evidence: Evidence,
}

#[derive(Clone, Debug)]
pub struct Root {
    pub id: String,
    pub reason: String,
}

#[derive(Clone, Debug)]
struct ParentStep {
    parent: String,
    edge: String,
}

#[derive(Clone, Debug)]
pub struct DeadcodeReport {
    pub symbols: usize,
    pub findings: Vec<Finding>,
    pub roots: Vec<Root>,
    pub mention_scanned: usize,
    pub mention_excluded: usize,
    pub mention_skipped_binary: usize,
    pub mention_skipped_large: usize,
    live: BTreeSet<String>,
    parents: BTreeMap<String, ParentStep>,
}

struct Fabric<'g> {
    by_id: BTreeMap<&'g str, &'g GraphNode>,
    out: BTreeMap<&'g str, Vec<(&'static str, &'g str)>>,
    inc: BTreeMap<&'g str, Vec<(&'static str, &'g str)>>,
    candidates: BTreeMap<&'g str, Vec<&'g str>>,
    candidate_counts: BTreeMap<&'g str, usize>,
    unresolved_callees: BTreeSet<&'g str>,
    methods: BTreeMap<&'g str, Vec<&'g str>>,
    method_ids: BTreeSet<&'g str>,
    specializes: BTreeMap<&'g str, Vec<(&'static str, &'g str)>>,
    file_modules: BTreeMap<&'g str, Vec<&'g str>>,
    module_files: BTreeMap<&'g str, Vec<&'g str>>,
}

impl<'g> Fabric<'g> {
    fn build(graph: &'g Graph) -> Fabric<'g> {
        let by_id: BTreeMap<&str, &GraphNode> =
            graph.nodes().map(|node| (node.id.as_str(), node)).collect();
        let mut out: BTreeMap<&str, Vec<(&'static str, &str)>> = BTreeMap::new();
        let mut inc: BTreeMap<&str, Vec<(&'static str, &str)>> = BTreeMap::new();
        let mut candidates: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        let mut unresolved_callees = BTreeSet::new();
        let mut methods: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        let mut method_ids = BTreeSet::new();
        let mut specializes: BTreeMap<&str, Vec<(&'static str, &str)>> = BTreeMap::new();
        let mut file_modules: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        let mut module_files: BTreeMap<&str, Vec<&str>> = BTreeMap::new();

        for node in graph.nodes().filter(|node| node.kind == ont::UNRESOLVED) {
            append_candidates(
                &mut candidates,
                node.id.as_str(),
                node.props.get("candidates"),
            );
        }
        for graph_edge in graph.edges() {
            if parent_relation(graph_edge.kind) == Some(relation::DEPENDS) {
                out.entry(graph_edge.from.as_str())
                    .or_default()
                    .push((graph_edge.kind, graph_edge.to.as_str()));
                inc.entry(graph_edge.to.as_str())
                    .or_default()
                    .push((graph_edge.kind, graph_edge.from.as_str()));
                if graph_edge.kind == edge::CALLS {
                    append_candidates(
                        &mut candidates,
                        graph_edge.to.as_str(),
                        graph_edge.props.get("candidates"),
                    );
                    if by_id
                        .get(graph_edge.to.as_str())
                        .is_some_and(|node| node.kind == ont::UNRESOLVED)
                    {
                        if let Some(Json::Str(callee)) = graph_edge.props.get("callee") {
                            unresolved_callees.insert(callee.as_str());
                        }
                    }
                }
            }
            if graph_edge.kind == edge::HAS_METHOD {
                methods
                    .entry(graph_edge.from.as_str())
                    .or_default()
                    .push(graph_edge.to.as_str());
                method_ids.insert(graph_edge.to.as_str());
            }
            if matches!(graph_edge.kind, edge::EXTENDS | edge::IMPLEMENTS) {
                specializes
                    .entry(graph_edge.from.as_str())
                    .or_default()
                    .push((graph_edge.kind, graph_edge.to.as_str()));
            }
            if graph_edge.kind == edge::CONTAINS {
                let from_kind = by_id.get(graph_edge.from.as_str()).map(|node| node.kind);
                let to_kind = by_id.get(graph_edge.to.as_str()).map(|node| node.kind);
                match (from_kind, to_kind) {
                    (Some(ont::MODULE), Some(ont::FILE)) => {
                        file_modules
                            .entry(graph_edge.to.as_str())
                            .or_default()
                            .push(graph_edge.from.as_str());
                        module_files
                            .entry(graph_edge.from.as_str())
                            .or_default()
                            .push(graph_edge.to.as_str());
                    }
                    (Some(ont::FILE), Some(ont::MODULE)) => {
                        file_modules
                            .entry(graph_edge.from.as_str())
                            .or_default()
                            .push(graph_edge.to.as_str());
                    }
                    _ => {}
                }
            }
        }
        for values in out.values_mut() {
            sort_edges(values);
        }
        for values in inc.values_mut() {
            sort_edges(values);
        }
        for values in candidates.values_mut() {
            values.sort_unstable();
            values.dedup();
        }
        for values in methods.values_mut() {
            values.sort_unstable();
            values.dedup();
        }
        for values in specializes.values_mut() {
            sort_edges(values);
        }
        for values in file_modules.values_mut() {
            values.sort_unstable();
            values.dedup();
        }
        for values in module_files.values_mut() {
            values.sort_unstable();
            values.dedup();
        }
        let mut candidate_counts = BTreeMap::new();
        for values in candidates.values() {
            for candidate in values {
                *candidate_counts.entry(*candidate).or_insert(0) += 1;
            }
        }
        Fabric {
            by_id,
            out,
            inc,
            candidates,
            candidate_counts,
            unresolved_callees,
            methods,
            method_ids,
            specializes,
            file_modules,
            module_files,
        }
    }
}

fn append_candidates<'g>(
    candidates: &mut BTreeMap<&'g str, Vec<&'g str>>,
    unresolved: &'g str,
    value: Option<&'g Json>,
) {
    if let Some(Json::Array(ids)) = value {
        candidates
            .entry(unresolved)
            .or_default()
            .extend(ids.iter().filter_map(|id| match id {
                Json::Str(id) => Some(id.as_str()),
                _ => None,
            }));
    }
}

fn sort_edges(values: &mut Vec<(&'static str, &str)>) {
    values.sort_unstable_by(|left, right| left.1.cmp(right.1).then_with(|| left.0.cmp(right.0)));
    values.dedup();
}

struct SourceIndex {
    bytes: BTreeMap<String, Vec<u8>>,
    counts: BTreeMap<String, BTreeMap<String, usize>>,
    scanned: usize,
    excluded: usize,
    skipped_binary: usize,
    skipped_large: usize,
}

impl SourceIndex {
    fn build(
        graph: &Graph,
        dir: &Path,
        mention_exclude: &[String],
        respect_gitignore: bool,
    ) -> Result<SourceIndex, String> {
        let mut bytes = BTreeMap::new();
        for file in graph.nodes().filter(|node| node.kind == ont::FILE) {
            let path = prop_str(file, "path");
            if path.is_empty() {
                continue;
            }
            let source = fs::read(dir.join(path))
                .map_err(|error| format!("failed to read analyzed file {path}: {error}"))?;
            bytes.insert(path.to_string(), source);
        }

        let mut files = Vec::new();
        crate::pipeline::collect_repository_files(dir, &mut files, respect_gitignore)
            .map_err(|error| format!("failed to walk files for textual mentions: {error}"))?;
        files.sort();
        let mut counts: BTreeMap<String, BTreeMap<String, usize>> = BTreeMap::new();
        let mut scanned = 0;
        let mut excluded = 0;
        let mut skipped_binary = 0;
        let mut skipped_large = 0;
        for full_path in files {
            let path = full_path
                .strip_prefix(dir)
                .unwrap_or(&full_path)
                .to_string_lossy()
                .replace('\\', "/");
            if mention_exclude
                .iter()
                .any(|pattern| crate::pipeline::path_matches_glob(pattern, &path))
            {
                excluded += 1;
                continue;
            }
            let metadata = fs::metadata(&full_path)
                .map_err(|error| format!("failed to inspect mention file {path}: {error}"))?;
            if metadata.len() > MENTION_FILE_SIZE_CAP_BYTES {
                skipped_large += 1;
                continue;
            }
            let source_from_disk;
            let source = match bytes.get(&path) {
                Some(source) => source.as_slice(),
                None => {
                    source_from_disk = fs::read(&full_path)
                        .map_err(|error| format!("failed to read mention file {path}: {error}"))?;
                    source_from_disk.as_slice()
                }
            };
            if source[..source.len().min(MENTION_BINARY_PROBE_BYTES)].contains(&0) {
                skipped_binary += 1;
                continue;
            }
            for token in identifier_tokens(source) {
                *counts
                    .entry(token.to_string())
                    .or_default()
                    .entry(path.clone())
                    .or_insert(0) += 1;
            }
            scanned += 1;
        }
        Ok(SourceIndex {
            bytes,
            counts,
            scanned,
            excluded,
            skipped_binary,
            skipped_large,
        })
    }

    fn mention_files(&self, node: &GraphNode, path: &str) -> Vec<String> {
        let Some(by_file) = self.counts.get(node.name.as_str()) else {
            return Vec::new();
        };
        let definition_count = self.definition_count(node, path);
        by_file
            .iter()
            .filter(|(file, count)| file.as_str() != path || **count > definition_count)
            .map(|(file, _)| file.clone())
            .collect()
    }

    fn definition_count(&self, node: &GraphNode, path: &str) -> usize {
        let Some(source) = self.bytes.get(path) else {
            return 1;
        };
        let start = prop_usize(node, "span_start");
        let end = prop_usize(node, "span_end");
        if let (Some(start), Some(end)) = (start, end) {
            if start < end && end <= source.len() {
                return identifier_tokens(&source[start..end])
                    .filter(|token| *token == node.name)
                    .count();
            }
        }
        1
    }
}

fn identifier_tokens(source: &[u8]) -> impl Iterator<Item = &str> {
    struct Tokens<'a> {
        source: &'a [u8],
        offset: usize,
    }
    impl<'a> Iterator for Tokens<'a> {
        type Item = &'a str;

        fn next(&mut self) -> Option<&'a str> {
            while self.offset < self.source.len() {
                let start = self.offset;
                let valid_start =
                    self.source[start].is_ascii_alphabetic() || self.source[start] == b'_';
                if self.source[start].is_ascii_alphanumeric() || self.source[start] == b'_' {
                    self.offset += 1;
                    while self.offset < self.source.len()
                        && (self.source[self.offset].is_ascii_alphanumeric()
                            || self.source[self.offset] == b'_')
                    {
                        self.offset += 1;
                    }
                    if valid_start {
                        return std::str::from_utf8(&self.source[start..self.offset]).ok();
                    }
                } else {
                    self.offset += 1;
                }
            }
            None
        }
    }
    Tokens { source, offset: 0 }
}

fn is_symbol(node: &GraphNode) -> bool {
    matches!(node.kind, ont::FUNCTION | ont::TYPE | ont::CONSTANT)
}

fn prop_bool(node: &GraphNode, key: &str) -> bool {
    node.props.get(key) == Some(&Json::Bool(true))
}

fn prop_str<'a>(node: &'a GraphNode, key: &str) -> &'a str {
    match node.props.get(key) {
        Some(Json::Str(value)) => value,
        _ => "",
    }
}

fn prop_u64(node: &GraphNode, key: &str) -> u64 {
    match node.props.get(key) {
        Some(Json::U64(value)) => *value,
        Some(Json::I64(value)) if *value >= 0 => *value as u64,
        _ => 0,
    }
}

fn prop_usize(node: &GraphNode, key: &str) -> Option<usize> {
    match node.props.get(key) {
        Some(Json::U64(value)) => usize::try_from(*value).ok(),
        Some(Json::I64(value)) if *value >= 0 => usize::try_from(*value).ok(),
        _ => None,
    }
}

fn effective_path<'g>(
    node: &'g GraphNode,
    file_of: &BTreeMap<&'g str, &'g str>,
    by_id: &BTreeMap<&'g str, &'g GraphNode>,
) -> &'g str {
    let own = prop_str(node, "path");
    if !own.is_empty() {
        return own;
    }
    file_of
        .get(node.id.as_str())
        .and_then(|file| by_id.get(file))
        .map_or("", |file| prop_str(file, "path"))
}

fn is_test_path(path: &str) -> bool {
    let normalized = path.replace('\\', "/");
    let surrounded = format!("/{}/", normalized.trim_matches('/'));
    let basename = normalized.rsplit('/').next().unwrap_or("");
    let stem = basename.rsplit_once('.').map_or(basename, |(stem, _)| stem);
    surrounded.contains("/tests/")
        || surrounded.contains("/test/")
        || normalized.contains("__tests__")
        || matches!(basename, "tests.py" | "conftest.py")
        || ((basename.starts_with("test_") || basename.starts_with("tests_"))
            && basename.ends_with(".py"))
        || stem.ends_with("_test")
        || basename.contains(".test.")
        || basename.contains(".spec.")
}

fn insert_root<'g>(roots: &mut BTreeMap<&'g str, &'static str>, id: &'g str, reason: &'static str) {
    roots.entry(id).or_insert(reason);
}

fn root_file<'g>(
    roots: &mut BTreeMap<&'g str, &'static str>,
    file: &'g str,
    reason: &'static str,
    modules: &BTreeMap<&'g str, Vec<&'g str>>,
    symbols: &BTreeMap<&'g str, Vec<&'g str>>,
    include_symbols: bool,
) {
    insert_root(roots, file, reason);
    if let Some(ids) = modules.get(file) {
        for id in ids {
            insert_root(roots, id, reason);
        }
    }
    if include_symbols {
        if let Some(ids) = symbols.get(file) {
            for id in ids {
                insert_root(roots, id, reason);
            }
        }
    }
}

fn is_constructor(node: &GraphNode, owner: &GraphNode) -> bool {
    prop_bool(node, "is_constructor")
        || matches!(node.name.as_str(), "__init__" | "__new__" | "constructor")
        || node.name == owner.name
}

fn is_python_module_protocol_symbol(
    node: &GraphNode,
    file_of: &BTreeMap<&str, &str>,
    file_modules: &BTreeMap<&str, Vec<&str>>,
) -> bool {
    if !matches!(node.kind, ont::FUNCTION | ont::CONSTANT)
        || prop_str(node, "language") != "python"
        || !node.name.starts_with("__")
        || !node.name.ends_with("__")
    {
        return false;
    }
    if node.kind == ont::CONSTANT {
        return file_of
            .get(node.id.as_str())
            .and_then(|file| file_modules.get(file))
            .is_some_and(|modules| !modules.is_empty());
    }
    let qualified = prop_str(node, "qualified_name");
    if qualified == node.name {
        return true;
    }
    let Some(module_join) = qualified
        .strip_suffix(node.name.as_str())
        .and_then(|prefix| prefix.strip_suffix('.'))
    else {
        return false;
    };
    file_of
        .get(node.id.as_str())
        .and_then(|file| file_modules.get(file))
        .is_some_and(|modules| {
            modules
                .iter()
                .any(|module| module.strip_prefix("mod::") == Some(module_join))
        })
}

pub fn analyze_graph(
    graph: &Graph,
    dir: &Path,
    config: &DeadcodeConfig,
    respect_gitignore: bool,
) -> Result<DeadcodeReport, String> {
    let fabric = Fabric::build(graph);
    let file_of = file_of_map(graph);
    let sources = SourceIndex::build(graph, dir, &config.mention_exclude, respect_gitignore)?;

    let mut file_symbols: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for (id, file) in &file_of {
        if fabric.by_id.get(id).is_some_and(|node| is_symbol(node)) {
            file_symbols.entry(*file).or_default().push(*id);
        }
    }
    for ids in file_symbols.values_mut() {
        ids.sort_unstable();
        ids.dedup();
    }

    let mut root_reasons: BTreeMap<&str, &'static str> = BTreeMap::new();
    for node in graph.nodes() {
        if node.kind == ont::FUNCTION && node.name == "main" {
            insert_root(&mut root_reasons, node.id.as_str(), "main-function");
        }
    }
    for node in graph
        .nodes()
        .filter(|node| is_python_module_protocol_symbol(node, &file_of, &fabric.file_modules))
    {
        insert_root(&mut root_reasons, node.id.as_str(), "module-protocol");
    }
    for node in graph.nodes().filter(|node| prop_bool(node, "entrypoint")) {
        insert_root(&mut root_reasons, node.id.as_str(), "entrypoint-prop");
        if node.kind == ont::FILE {
            root_file(
                &mut root_reasons,
                node.id.as_str(),
                "entrypoint-prop",
                &fabric.file_modules,
                &file_symbols,
                false,
            );
        }
    }
    for file in graph.nodes().filter(|node| node.kind == ont::FILE) {
        if prop_bool(file, "main_guard") {
            root_file(
                &mut root_reasons,
                file.id.as_str(),
                "main-guard",
                &fabric.file_modules,
                &file_symbols,
                false,
            );
        }
        if prop_bool(file, "shebang") {
            root_file(
                &mut root_reasons,
                file.id.as_str(),
                "shebang",
                &fabric.file_modules,
                &file_symbols,
                false,
            );
        }
        let path = prop_str(file, "path");
        if config.test_roots && is_test_path(path) {
            // Test runners invoke tests and fixtures dynamically, so no CALLS edge
            // connects the runner to those symbols. Root them with the test File to
            // avoid treating discoverable tests and helpers as production dead code.
            root_file(
                &mut root_reasons,
                file.id.as_str(),
                "test-root",
                &fabric.file_modules,
                &file_symbols,
                true,
            );
        }
        if let Some(source) = sources.bytes.get(path) {
            let head = String::from_utf8_lossy(&source[..source.len().min(1024)]);
            if brief_generated::is_generated(path, &head) {
                if let Some(symbols) = file_symbols.get(file.id.as_str()) {
                    for symbol in symbols {
                        insert_root(&mut root_reasons, symbol, "generated");
                    }
                }
            }
        }
    }
    for node in graph
        .nodes()
        .filter(|node| is_symbol(node) && node.props.contains_key("decorators"))
    {
        insert_root(&mut root_reasons, node.id.as_str(), "decorated");
    }

    for selector in &config.roots {
        add_config_selector(
            selector,
            "config-root",
            false,
            graph,
            &fabric,
            &file_of,
            &fabric.file_modules,
            &file_symbols,
            &mut root_reasons,
        );
    }
    for selector in &config.keep {
        add_config_selector(
            selector,
            "config-keep",
            true,
            graph,
            &fabric,
            &file_of,
            &fabric.file_modules,
            &file_symbols,
            &mut root_reasons,
        );
    }
    for node in graph.nodes().filter(|node| {
        is_symbol(node)
            && prop_bool(node, "exported")
            && config
                .public_api
                .iter()
                .any(|prefix| effective_path(node, &file_of, &fabric.by_id).starts_with(prefix))
    }) {
        insert_root(&mut root_reasons, node.id.as_str(), "public-api");
    }

    let mut live: BTreeSet<&str> = root_reasons.keys().copied().collect();
    let mut parents: BTreeMap<&str, (&str, &'static str)> = BTreeMap::new();
    let mut frontier: Vec<&str> = live.iter().copied().collect();
    while !frontier.is_empty() {
        let mut claims: BTreeMap<&str, (&str, &'static str)> = BTreeMap::new();
        for id in frontier {
            let mut transitions: Vec<(&str, &'static str)> = Vec::new();
            if let Some(edges) = fabric.out.get(id) {
                for (kind, target) in edges {
                    transitions.push((target, kind));
                    if *kind == edge::CALLS {
                        if let Some(candidates) = fabric.candidates.get(target) {
                            transitions.extend(
                                candidates
                                    .iter()
                                    .map(|candidate| (*candidate, "CALLS[candidate]")),
                            );
                        }
                    }
                    if *kind == edge::IMPORTS {
                        match fabric.by_id.get(target).map(|node| node.kind) {
                            Some(ont::MODULE) => {
                                if let Some(files) = fabric.module_files.get(target) {
                                    transitions.extend(
                                        files.iter().map(|file| (*file, "IMPORTS[file-frontier]")),
                                    );
                                }
                            }
                            Some(ont::FILE) => {
                                if let Some(modules) = fabric.file_modules.get(target) {
                                    transitions.extend(
                                        modules
                                            .iter()
                                            .map(|module| (*module, "IMPORTS[module-frontier]")),
                                    );
                                }
                            }
                            _ => {
                                if let Some(file) = file_of.get(target) {
                                    transitions.push((*file, "IMPORTS[file-frontier]"));
                                }
                            }
                        }
                    }
                }
            }
            if let Some(node) = fabric.by_id.get(id) {
                if node.kind == ont::TYPE {
                    if let Some(methods) = fabric.methods.get(id) {
                        for method in methods {
                            if let Some(method_node) = fabric.by_id.get(method) {
                                if method_node.name.starts_with("__")
                                    || is_constructor(method_node, node)
                                {
                                    transitions.push((method, edge::HAS_METHOD));
                                }
                            }
                        }
                    }
                }
            }
            if let Some(bases) = fabric.specializes.get(id) {
                transitions.extend(bases.iter().map(|(kind, target)| (*target, *kind)));
            }
            // M2: keep overriding methods when a live base contract requires them.
            transitions.sort_unstable_by(|left, right| {
                left.0.cmp(right.0).then_with(|| left.1.cmp(right.1))
            });
            transitions.dedup();
            for (target, kind) in transitions {
                if live.contains(target) {
                    continue;
                }
                claims
                    .entry(target)
                    .and_modify(|current| {
                        if (id, kind) < *current {
                            *current = (id, kind);
                        }
                    })
                    .or_insert((id, kind));
            }
        }
        let mut next = Vec::with_capacity(claims.len());
        for (target, (parent, kind)) in claims {
            live.insert(target);
            parents.insert(target, (parent, kind));
            next.push(target);
        }
        frontier = next;
    }

    let dead_ids: BTreeSet<&str> = graph
        .nodes()
        .filter(|node| is_symbol(node) && !live.contains(node.id.as_str()))
        .map(|node| node.id.as_str())
        .collect();
    let symbols = graph.nodes().filter(|node| is_symbol(node)).count();
    let mut findings = Vec::with_capacity(dead_ids.len());
    for id in &dead_ids {
        let node = fabric.by_id[id];
        let inbound = fabric.inc.get(id).map(Vec::as_slice).unwrap_or(&[]);
        let inbound_refs = inbound.len();
        let ambiguous_candidacies = fabric.candidate_counts.get(id).copied().unwrap_or(0);
        let path = effective_path(node, &file_of, &fabric.by_id);
        let mention_files = sources.mention_files(node, path);
        let exported = prop_bool(node, "exported");
        let type_with_methods = node.kind == ont::TYPE && fabric.methods.contains_key(id);
        let dynamic_dispatch = type_with_methods || fabric.method_ids.contains(id);
        let unresolved_same_name = fabric.unresolved_callees.contains(node.name.as_str());
        let transitive =
            inbound_refs > 0 && inbound.iter().all(|(_, source)| dead_ids.contains(source));
        let tier = if transitive {
            Tier::Transitive
        } else if inbound_refs == 0
            && ambiguous_candidacies == 0
            && mention_files.is_empty()
            && !dynamic_dispatch
            && !exported
            && !unresolved_same_name
        {
            Tier::High
        } else {
            Tier::Medium
        };
        let reason = finding_reason(
            tier,
            ambiguous_candidacies,
            &mention_files,
            exported,
            dynamic_dispatch,
            unresolved_same_name,
        );
        findings.push(Finding {
            id: node.id.clone(),
            path: path.to_string(),
            line: prop_u64(node, "line"),
            name: node.name.clone(),
            kind: node.kind,
            tier,
            reason: reason.to_string(),
            evidence: Evidence {
                inbound_refs,
                ambiguous_candidacies,
                mention_files,
                exported,
            },
        });
    }
    findings.sort_by(|left, right| {
        left.tier
            .cmp(&right.tier)
            .then_with(|| left.path.cmp(&right.path))
            .then_with(|| left.line.cmp(&right.line))
            .then_with(|| left.id.cmp(&right.id))
    });
    let roots = root_reasons
        .into_iter()
        .map(|(id, reason)| Root {
            id: id.to_string(),
            reason: reason.to_string(),
        })
        .collect();
    let parents = parents
        .into_iter()
        .map(|(child, (parent, kind))| {
            (
                child.to_string(),
                ParentStep {
                    parent: parent.to_string(),
                    edge: kind.to_string(),
                },
            )
        })
        .collect();
    Ok(DeadcodeReport {
        symbols,
        findings,
        roots,
        live: live.into_iter().map(str::to_string).collect(),
        parents,
        mention_scanned: sources.scanned,
        mention_excluded: sources.excluded,
        mention_skipped_binary: sources.skipped_binary,
        mention_skipped_large: sources.skipped_large,
    })
}

#[allow(clippy::too_many_arguments)]
fn add_config_selector<'g>(
    selector: &str,
    reason: &'static str,
    symbols_only: bool,
    graph: &'g Graph,
    fabric: &Fabric<'g>,
    file_of: &BTreeMap<&'g str, &'g str>,
    file_modules: &BTreeMap<&'g str, Vec<&'g str>>,
    file_symbols: &BTreeMap<&'g str, Vec<&'g str>>,
    roots: &mut BTreeMap<&'g str, &'static str>,
) {
    let matches: Vec<&GraphNode> = if symbols_only {
        graph
            .nodes()
            .filter(|node| {
                is_symbol(node)
                    && (node.name == selector
                        || effective_path(node, file_of, &fabric.by_id).starts_with(selector))
            })
            .collect()
    } else if let Some(node) = fabric.by_id.get(selector) {
        vec![*node]
    } else {
        let by_name: Vec<&GraphNode> = graph.nodes().filter(|node| node.name == selector).collect();
        if by_name.is_empty() {
            graph
                .nodes()
                .filter(|node| effective_path(node, file_of, &fabric.by_id).starts_with(selector))
                .collect()
        } else {
            by_name
        }
    };
    for node in matches {
        insert_root(roots, node.id.as_str(), reason);
        if node.kind == ont::FILE {
            root_file(
                roots,
                node.id.as_str(),
                reason,
                file_modules,
                file_symbols,
                false,
            );
        }
    }
}

fn finding_reason(
    tier: Tier,
    ambiguous_candidacies: usize,
    mention_files: &[String],
    exported: bool,
    dynamic_dispatch: bool,
    unresolved_same_name: bool,
) -> &'static str {
    if tier == Tier::Transitive {
        "referenced only by dead code"
    } else if !mention_files.is_empty() {
        "textual mentions outside the definition"
    } else if ambiguous_candidacies > 0 {
        "ambiguous call candidacy"
    } else if exported {
        "exported symbol outside configured public API"
    } else if dynamic_dispatch {
        "dynamic-dispatch risk"
    } else if unresolved_same_name {
        "unresolved same-name call exists"
    } else if tier == Tier::High {
        "no inbound references, candidacies, or textual mentions in files scanned for mentions"
    } else {
        "unreachable with non-high-confidence evidence"
    }
}

impl DeadcodeReport {
    fn counts(&self) -> (usize, usize, usize) {
        let high = self
            .findings
            .iter()
            .filter(|finding| finding.tier == Tier::High)
            .count();
        let medium = self
            .findings
            .iter()
            .filter(|finding| finding.tier == Tier::Medium)
            .count();
        let transitive = self
            .findings
            .iter()
            .filter(|finding| finding.tier == Tier::Transitive)
            .count();
        (high, medium, transitive)
    }

    fn selected(&self, min_confidence: MinConfidence, limit: Option<usize>) -> Vec<&Finding> {
        let mut selected = Vec::new();
        for tier in [Tier::High, Tier::Medium, Tier::Transitive] {
            if !min_confidence.includes(tier) {
                continue;
            }
            selected.extend(
                self.findings
                    .iter()
                    .filter(|finding| finding.tier == tier)
                    .take(limit.unwrap_or(usize::MAX)),
            );
        }
        selected
    }

    pub fn exit_code(&self, min_confidence: MinConfidence) -> u8 {
        u8::from(
            self.findings
                .iter()
                .any(|finding| min_confidence.includes(finding.tier)),
        )
    }

    pub fn to_text(&self, min_confidence: MinConfidence, limit: Option<usize>) -> String {
        let (high, medium, transitive) = self.counts();
        let mut output = String::new();
        let _ = writeln!(
            output,
            "trailtracker deadcode: analyzed {} symbols, {} roots, {} dead: {} high / {} medium / {} transitive",
            self.symbols,
            self.roots.len(),
            self.findings.len(),
            high,
            medium,
            transitive
        );
        let _ = writeln!(
            output,
            "mention scan: {} files scanned, {} excluded, {} binary skipped, {} over {}-byte cap skipped",
            self.mention_scanned,
            self.mention_excluded,
            self.mention_skipped_binary,
            self.mention_skipped_large,
            MENTION_FILE_SIZE_CAP_BYTES
        );
        for tier in [Tier::High, Tier::Medium, Tier::Transitive] {
            if !min_confidence.includes(tier) {
                continue;
            }
            let tier_findings: Vec<&Finding> = self
                .findings
                .iter()
                .filter(|finding| finding.tier == tier)
                .collect();
            let _ = writeln!(output, "\n{} ({}):", tier.as_str(), tier_findings.len());
            let shown = limit.unwrap_or(usize::MAX).min(tier_findings.len());
            for finding in tier_findings.iter().take(shown) {
                let location = if finding.line == 0 {
                    finding.path.clone()
                } else {
                    format!("{}:{}", finding.path, finding.line)
                };
                let _ = writeln!(
                    output,
                    "  {location} {} ({}) — {}",
                    finding.name, finding.kind, finding.reason
                );
            }
            if shown < tier_findings.len() {
                let _ = writeln!(
                    output,
                    "  …and {} more (use --limit)",
                    tier_findings.len() - shown
                );
            }
        }
        let mut by_reason: BTreeMap<&str, usize> = BTreeMap::new();
        for root in &self.roots {
            *by_reason.entry(root.reason.as_str()).or_insert(0) += 1;
        }
        let _ = writeln!(output, "\nroots ({}):", self.roots.len());
        for (reason, count) in by_reason {
            let _ = writeln!(output, "  {reason}: {count}");
        }
        for root in self.roots.iter().take(10) {
            let _ = writeln!(output, "  {} — {}", root.id, root.reason);
        }
        if self.roots.len() > 10 {
            let _ = writeln!(output, "  …and {} more roots", self.roots.len() - 10);
        }
        output
    }

    pub fn to_json_line(
        &self,
        dir: &str,
        min_confidence: MinConfidence,
        limit: Option<usize>,
    ) -> String {
        let (high, medium, transitive) = self.counts();
        let summary = Json::obj([
            ("symbols", Json::U64(self.symbols as u64)),
            ("roots", Json::U64(self.roots.len() as u64)),
            ("mention_scanned", Json::U64(self.mention_scanned as u64)),
            ("mention_excluded", Json::U64(self.mention_excluded as u64)),
            (
                "mention_skipped_binary",
                Json::U64(self.mention_skipped_binary as u64),
            ),
            (
                "mention_skipped_large",
                Json::U64(self.mention_skipped_large as u64),
            ),
            (
                "mention_file_size_cap_bytes",
                Json::U64(MENTION_FILE_SIZE_CAP_BYTES),
            ),
            (
                "dead",
                Json::obj([
                    ("high", Json::U64(high as u64)),
                    ("medium", Json::U64(medium as u64)),
                    ("transitive", Json::U64(transitive as u64)),
                ]),
            ),
        ]);
        let findings = Json::Array(
            self.selected(min_confidence, limit)
                .into_iter()
                .map(|finding| {
                    Json::obj([
                        ("id", Json::str(&finding.id)),
                        ("path", Json::str(&finding.path)),
                        ("line", Json::U64(finding.line)),
                        ("name", Json::str(&finding.name)),
                        ("kind", Json::str(finding.kind)),
                        ("tier", Json::str(finding.tier.as_str())),
                        ("reason", Json::str(&finding.reason)),
                        (
                            "evidence",
                            Json::obj([
                                (
                                    "inbound_refs",
                                    Json::U64(finding.evidence.inbound_refs as u64),
                                ),
                                (
                                    "ambiguous_candidacies",
                                    Json::U64(finding.evidence.ambiguous_candidacies as u64),
                                ),
                                (
                                    "mention_files",
                                    Json::Array(
                                        finding
                                            .evidence
                                            .mention_files
                                            .iter()
                                            .map(Json::str)
                                            .collect(),
                                    ),
                                ),
                                ("exported", Json::Bool(finding.evidence.exported)),
                            ]),
                        ),
                    ])
                })
                .collect(),
        );
        let roots = Json::Array(
            self.roots
                .iter()
                .map(|root| {
                    Json::obj([
                        ("id", Json::str(&root.id)),
                        ("reason", Json::str(&root.reason)),
                    ])
                })
                .collect(),
        );
        // Json::Object sorts keys. Assemble only the top-level envelope so the
        // required schema/command/dir prefix stays first; every value still
        // uses the repository's deterministic Json::to_line writer.
        format!(
            "{{\"schema\":{},\"command\":{},\"dir\":{},\"summary\":{},\"findings\":{},\"roots\":{}}}",
            Json::str(REPORT_FORMAT).to_line(),
            Json::str("deadcode").to_line(),
            Json::str(dir).to_line(),
            summary.to_line(),
            findings.to_line(),
            roots.to_line()
        )
    }

    pub fn why_text(&self, graph: &Graph, target: &str) -> Result<String, ExplainError> {
        let node = resolve(graph, target)?;
        if self.live.contains(node.id.as_str()) {
            let mut chain: Vec<(String, String, String)> = Vec::new();
            let mut current = node.id.clone();
            while let Some(step) = self.parents.get(&current) {
                chain.push((step.parent.clone(), step.edge.clone(), current.clone()));
                current.clone_from(&step.parent);
            }
            chain.reverse();
            let reason = self
                .roots
                .iter()
                .find(|root| root.id == current)
                .map_or("root", |root| root.reason.as_str());
            let mut output = format!(
                "live: {} ({})\nroot: {} — {}\nchain:\n  {} — {}\n",
                node.name, node.id, current, reason, current, reason
            );
            for (_, kind, child) in chain {
                let _ = writeln!(output, "  -[{kind}]-> {child}");
            }
            return Ok(output);
        }
        let finding = self.findings.iter().find(|finding| finding.id == node.id);
        let mut output = match finding {
            Some(finding) => format!(
                "dead: {} ({}) — {}\nno root-to-target path exists\n",
                finding.name,
                finding.id,
                finding.tier.as_str()
            ),
            None => format!(
                "dead: {} ({}) — non-symbol\nno root-to-target path exists\n",
                node.name, node.id
            ),
        };
        if let Some(finding) = finding {
            let _ = writeln!(
                output,
                "evidence: inbound_refs={}, ambiguous_candidacies={}, exported={}",
                finding.evidence.inbound_refs,
                finding.evidence.ambiguous_candidacies,
                finding.evidence.exported
            );
            let _ = writeln!(
                output,
                "mention_scan: scanned={}, excluded={}, binary_skipped={}, over_{}_bytes_skipped={}",
                self.mention_scanned,
                self.mention_excluded,
                self.mention_skipped_binary,
                MENTION_FILE_SIZE_CAP_BYTES,
                self.mention_skipped_large
            );
            let shown = finding.evidence.mention_files.len().min(5);
            let _ = writeln!(
                output,
                "mention_files: {}",
                finding.evidence.mention_files[..shown].join(", ")
            );
            if shown < finding.evidence.mention_files.len() {
                let _ = writeln!(
                    output,
                    "…and {} more mention files",
                    finding.evidence.mention_files.len() - shown
                );
            }
        }
        Ok(output)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::path::{Path, PathBuf};

    use crate::pipeline::analyze_dir;

    struct Fixture(PathBuf);

    impl Fixture {
        fn new(name: &str, files: &[(&str, &str)]) -> Fixture {
            let root = std::env::temp_dir().join(format!(
                "trailtracker-deadcode-{name}-{}",
                std::process::id()
            ));
            let _ = fs::remove_dir_all(&root);
            fs::create_dir_all(&root).expect("create fixture root");
            for (path, source) in files {
                let full = root.join(path);
                if let Some(parent) = full.parent() {
                    fs::create_dir_all(parent).expect("create fixture parent");
                }
                fs::write(full, source).expect("write fixture source");
            }
            Fixture(root)
        }

        fn path(&self) -> &Path {
            &self.0
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn dead_function_is_high_but_called_function_is_live() {
        let fixture = Fixture::new(
            "basic",
            &[(
                "app.py",
                "def main():\n    live()\n\ndef live():\n    return 1\n\ndef _dead():\n    return 2\n\ndef dead_pub():\n    return 3\n",
            )],
        );
        let graph = analyze_dir(fixture.path()).expect("analyze fixture").graph;
        let report = analyze_graph(&graph, fixture.path(), &DeadcodeConfig::default(), true)
            .expect("analyze dead code");

        let dead_private = report
            .findings
            .iter()
            .find(|finding| finding.name == "_dead")
            .expect("private dead function must be reported");
        assert_eq!(dead_private.tier, Tier::High);

        let dead_public = report
            .findings
            .iter()
            .find(|finding| finding.name == "dead_pub")
            .expect("public dead function must be reported");
        assert_eq!(dead_public.tier, Tier::Medium);
        assert!(dead_public.evidence.exported);
        assert!(
            report.findings.iter().all(|finding| finding.name != "live"),
            "called function must be live"
        );
    }

    #[test]
    fn same_module_constant_read_is_live_with_inbound_reference() {
        let fixture = Fixture::new(
            "constant-read",
            &[(
                "forecast_helpers.py",
                "_FORECAST_ENGINE = object()\n\ndef main():\n    return _FORECAST_ENGINE\n",
            )],
        );
        let graph = analyze_dir(fixture.path()).expect("analyze fixture").graph;
        let constant = graph
            .nodes()
            .find(|node| node.kind == ont::CONSTANT && node.name == "_FORECAST_ENGINE")
            .expect("module constant");
        let inbound_refs = graph
            .edges()
            .filter(|edge| edge.kind == edge::READS && edge.to == constant.id)
            .count();
        assert!(inbound_refs > 0);
        let report = analyze_graph(&graph, fixture.path(), &DeadcodeConfig::default(), true)
            .expect("analyze dead code");
        assert!(
            report
                .findings
                .iter()
                .all(|finding| finding.id != constant.id),
            "the main function's READS edge must keep the constant live"
        );
    }

    #[test]
    fn live_ambiguous_call_keeps_every_candidate_live() {
        let fixture = Fixture::new(
            "ambiguous",
            &[(
                "app.py",
                "class A:\n    def ping(self):\n        return 1\n\nclass B:\n    def ping(self):\n        return 2\n\ndef main():\n    value.ping()\n",
            )],
        );
        let mut graph = analyze_dir(fixture.path()).expect("analyze fixture").graph;
        let main_id = graph
            .nodes()
            .find(|node| node.kind == ont::FUNCTION && node.name == "main")
            .expect("main node")
            .id
            .clone();
        let candidates: Vec<Json> = graph
            .nodes()
            .filter(|node| node.kind == ont::FUNCTION && node.name == "ping")
            .map(|node| Json::str(node.id.clone()))
            .collect();
        assert_eq!(candidates.len(), 2, "fixture must expose two candidates");
        graph.upsert_node(
            "unresolved::fixture::ping",
            ont::UNRESOLVED,
            "ping",
            vec![("candidates", Json::Array(candidates))],
        );
        graph.add_edge(
            main_id,
            crate::ir::ontology::edge::CALLS,
            "unresolved::fixture::ping",
            vec![("callee", Json::str("ping"))],
        );
        let report = analyze_graph(&graph, fixture.path(), &DeadcodeConfig::default(), true)
            .expect("analyze dead code");
        assert!(
            report.findings.iter().all(|finding| finding.name != "ping"),
            "all candidates of a live ambiguous call must be live"
        );
    }

    #[test]
    fn mutually_recursive_dead_cluster_is_transitive() {
        let fixture = Fixture::new(
            "cluster",
            &[(
                "app.py",
                "def main():\n    return 0\n\ndef a():\n    b()\n\ndef b():\n    a()\n",
            )],
        );
        let graph = analyze_dir(fixture.path()).expect("analyze fixture").graph;
        let report = analyze_graph(&graph, fixture.path(), &DeadcodeConfig::default(), true)
            .expect("analyze dead code");
        for name in ["a", "b"] {
            let finding = report
                .findings
                .iter()
                .find(|finding| finding.name == name)
                .expect("cluster member must be reported");
            assert_eq!(finding.tier, Tier::Transitive);
        }
    }

    #[test]
    fn main_guard_roots_module_level_callees_when_fact_exists() {
        let fixture = Fixture::new(
            "main-guard",
            &[(
                "app.py",
                "def launch():\n    return 1\n\nif __name__ == \"__main__\":\n    launch()\n",
            )],
        );
        let graph = analyze_dir(fixture.path()).expect("analyze fixture").graph;
        if !graph
            .nodes()
            .any(|node| node.kind == ont::FILE && prop_bool(node, "main_guard"))
        {
            eprintln!("skipping main-guard assertion: frontend emitted no main_guard fact");
            return;
        }
        let report = analyze_graph(&graph, fixture.path(), &DeadcodeConfig::default(), true)
            .expect("analyze dead code");
        assert!(
            report
                .findings
                .iter()
                .all(|finding| finding.name != "launch"),
            "main guard must keep its module-level callee live"
        );
    }

    #[test]
    fn bash_textual_mention_demotes_python_symbol() {
        let fixture = Fixture::new(
            "mention",
            &[
                (
                    "app.py",
                    "def main():\n    return 0\n\ndef cross_language_hook():\n    return 1\n",
                ),
                ("scripts/use.sh", "echo cross_language_hook\n"),
            ],
        );
        let graph = analyze_dir(fixture.path()).expect("analyze fixture").graph;
        let report = analyze_graph(&graph, fixture.path(), &DeadcodeConfig::default(), true)
            .expect("analyze dead code");
        let finding = report
            .findings
            .iter()
            .find(|finding| finding.name == "cross_language_hook")
            .expect("unused function must be reported");
        assert_eq!(finding.tier, Tier::Medium);
        assert_eq!(finding.evidence.mention_files, vec!["scripts/use.sh"]);
    }

    #[test]
    fn readme_only_mention_demotes_symbol_and_names_readme() {
        let fixture = Fixture::new(
            "readme-mention",
            &[
                (
                    "app.py",
                    "def main():\n    return 0\n\ndef _documented_hook():\n    return 1\n",
                ),
                ("README.md", "Call `_documented_hook` during deployment.\n"),
            ],
        );
        let graph = analyze_dir(fixture.path()).expect("analyze fixture").graph;
        let report = analyze_graph(&graph, fixture.path(), &DeadcodeConfig::default(), true)
            .expect("analyze dead code");
        let finding = report
            .findings
            .iter()
            .find(|finding| finding.name == "_documented_hook")
            .expect("unused function");
        assert_eq!(finding.tier, Tier::Medium);
        assert_eq!(finding.evidence.mention_files, vec!["README.md"]);
    }

    #[test]
    fn mention_exclude_restores_high_tier_and_reports_exclusion() {
        let fixture = Fixture::new(
            "excluded-readme-mention",
            &[
                (
                    "app.py",
                    "def main():\n    return 0\n\ndef _documented_hook():\n    return 1\n",
                ),
                ("README.md", "Call `_documented_hook` during deployment.\n"),
            ],
        );
        let graph = analyze_dir(fixture.path()).expect("analyze fixture").graph;
        let config =
            parse_config(r#"{"mention_exclude":["README.md"]}"#).expect("valid mention config");
        let report =
            analyze_graph(&graph, fixture.path(), &config, true).expect("analyze dead code");
        let finding = report
            .findings
            .iter()
            .find(|finding| finding.name == "_documented_hook")
            .expect("unused function");
        assert_eq!(finding.tier, Tier::High);
        assert!(finding.evidence.mention_files.is_empty());
        assert_eq!(
            finding.reason,
            "no inbound references, candidacies, or textual mentions in files scanned for mentions"
        );
        assert!(
            report
                .to_json_line("fixture", MinConfidence::Low, None)
                .contains("\"mention_excluded\":1"),
            "summary must disclose excluded mention files"
        );
    }

    #[test]
    fn oversized_file_is_skipped_and_disclosed() {
        let fixture = Fixture::new(
            "oversized-mention",
            &[(
                "app.py",
                "def main():\n    return 0\n\ndef _large_hook():\n    return 1\n",
            )],
        );
        let mut oversized = vec![b'x'; MENTION_FILE_SIZE_CAP_BYTES as usize + 1];
        oversized[..11].copy_from_slice(b"_large_hook");
        fs::write(fixture.path().join("large.txt"), oversized).expect("write oversized fixture");
        let graph = analyze_dir(fixture.path()).expect("analyze fixture").graph;
        let report = analyze_graph(&graph, fixture.path(), &DeadcodeConfig::default(), true)
            .expect("analyze dead code");
        let finding = report
            .findings
            .iter()
            .find(|finding| finding.name == "_large_hook")
            .expect("unused function");
        assert_eq!(finding.tier, Tier::High);
        assert_eq!(report.mention_skipped_large, 1);
    }

    #[test]
    fn binary_file_is_skipped_without_creating_a_mention() {
        let fixture = Fixture::new(
            "binary-mention",
            &[(
                "app.py",
                "def main():\n    return 0\n\ndef _binary_hook():\n    return 1\n",
            )],
        );
        fs::write(
            fixture.path().join("artifact.bin"),
            b"_binary_hook\0payload",
        )
        .expect("write binary fixture");
        let graph = analyze_dir(fixture.path()).expect("analyze fixture").graph;
        let report = analyze_graph(&graph, fixture.path(), &DeadcodeConfig::default(), true)
            .expect("analyze dead code");
        let finding = report
            .findings
            .iter()
            .find(|finding| finding.name == "_binary_hook")
            .expect("unused function");
        assert_eq!(finding.tier, Tier::High);
        assert!(finding.evidence.mention_files.is_empty());
        assert!(report
            .to_json_line("fixture", MinConfidence::Low, None)
            .contains("\"mention_skipped_binary\":1"));
    }

    #[test]
    fn config_keep_makes_symbol_live_with_auditable_reason() {
        let fixture = Fixture::new(
            "keep",
            &[(
                "app.py",
                "def main():\n    return 0\n\ndef plugin_hook():\n    return 1\n",
            )],
        );
        let graph = analyze_dir(fixture.path()).expect("analyze fixture").graph;
        let config = DeadcodeConfig {
            keep: vec!["plugin_hook".to_string()],
            ..DeadcodeConfig::default()
        };
        let report =
            analyze_graph(&graph, fixture.path(), &config, true).expect("analyze dead code");
        assert!(report
            .findings
            .iter()
            .all(|finding| finding.name != "plugin_hook"));
        assert!(report.roots.iter().any(|root| {
            graph
                .nodes()
                .any(|node| node.id == root.id && node.name == "plugin_hook")
                && root.reason == "config-keep"
        }));
    }

    #[test]
    fn decorated_symbol_is_a_root() {
        let fixture = Fixture::new(
            "decorated",
            &[(
                "app.py",
                "def register(fn):\n    return fn\n\n@register\ndef handler():\n    return 1\n\ndef main():\n    return 0\n",
            )],
        );
        let graph = analyze_dir(fixture.path()).expect("analyze fixture").graph;
        assert!(
            graph
                .nodes()
                .any(|node| node.name == "handler" && node.props.contains_key("decorators")),
            "fixture must expose the decorators fact"
        );
        let report = analyze_graph(&graph, fixture.path(), &DeadcodeConfig::default(), true)
            .expect("analyze dead code");
        assert!(
            report
                .findings
                .iter()
                .all(|finding| finding.name != "handler"),
            "decorated symbol must be live"
        );
    }

    #[test]
    fn pytest_conventional_root_files_are_recognized_without_substrings() {
        for path in [
            "tests.py",
            "pkg/tests.py",
            "conftest.py",
            "pkg/conftest.py",
            "tests_4_9a_integration.py",
            "pkg/tests_feature.py",
        ] {
            assert!(is_test_path(path), "{path} must be a test root");
        }
        for path in ["contest.py", "protests.py", "mytests.py"] {
            assert!(!is_test_path(path), "{path} must not be a test root");
        }
    }

    #[test]
    fn module_protocol_dunder_is_an_auditable_root() {
        let fixture = Fixture::new(
            "module-protocol",
            &[(
                "lazy.py",
                "def __getattr__(name):\n    raise AttributeError(name)\n",
            )],
        );
        let graph = analyze_dir(fixture.path()).expect("analyze fixture").graph;
        let protocol = graph
            .nodes()
            .find(|node| node.kind == ont::FUNCTION && node.name == "__getattr__")
            .expect("module protocol function");
        let report = analyze_graph(&graph, fixture.path(), &DeadcodeConfig::default(), true)
            .expect("analyze dead code");
        assert!(
            report
                .findings
                .iter()
                .all(|finding| finding.id != protocol.id),
            "runtime-invoked module protocol must not be reported"
        );
        assert!(report
            .roots
            .iter()
            .any(|root| { root.id == protocol.id && root.reason == "module-protocol" }));
    }

    #[test]
    fn module_protocol_dunder_constant_is_an_auditable_root() {
        let fixture = Fixture::new(
            "module-protocol-constant",
            &[(
                "lazy.py",
                "def load_attribute(name):\n    raise AttributeError(name)\n\n__getattr__ = load_attribute\n",
            )],
        );
        let graph = analyze_dir(fixture.path()).expect("analyze fixture").graph;
        let protocol = graph
            .nodes()
            .find(|node| node.kind == ont::CONSTANT && node.name == "__getattr__")
            .expect("module protocol constant");
        let report = analyze_graph(&graph, fixture.path(), &DeadcodeConfig::default(), true)
            .expect("analyze dead code");
        assert!(
            report
                .findings
                .iter()
                .all(|finding| finding.id != protocol.id),
            "runtime-invoked module protocol binding must not be reported"
        );
        assert!(report
            .roots
            .iter()
            .any(|root| { root.id == protocol.id && root.reason == "module-protocol" }));
    }

    #[test]
    fn unittest_methods_are_rooted_only_in_test_files() {
        let fixture = Fixture::new(
            "unittest-methods",
            &[
                (
                    "tests/test_feature.py",
                    "class FeatureTests:\n    def test_runner_invoked(self):\n        pass\n",
                ),
                (
                    "feature.py",
                    "class Feature:\n    def test_not_runner_invoked(self):\n        pass\n",
                ),
            ],
        );
        let graph = analyze_dir(fixture.path()).expect("analyze fixture").graph;
        let report = analyze_graph(&graph, fixture.path(), &DeadcodeConfig::default(), true)
            .expect("analyze dead code");
        assert!(report
            .findings
            .iter()
            .all(|finding| finding.name != "test_runner_invoked"));
        assert!(report.roots.iter().any(|root| {
            graph.nodes().any(|node| {
                node.id == root.id
                    && node.name == "test_runner_invoked"
                    && root.reason == "test-root"
            })
        }));
        assert!(report
            .findings
            .iter()
            .any(|finding| finding.name == "test_not_runner_invoked"));
    }

    #[test]
    fn generated_file_symbols_are_never_findings() {
        let fixture = Fixture::new(
            "generated",
            &[(
                "generated/messages_pb2.py",
                "# @generated by protoc\n\ndef generated_helper():\n    return 1\n",
            )],
        );
        let graph = analyze_dir(fixture.path()).expect("analyze fixture").graph;
        let report = analyze_graph(&graph, fixture.path(), &DeadcodeConfig::default(), true)
            .expect("analyze dead code");
        assert!(
            report
                .findings
                .iter()
                .all(|finding| finding.name != "generated_helper"),
            "generated symbols must be rooted"
        );
    }

    #[test]
    fn full_json_output_is_byte_identical() {
        let fixture = Fixture::new(
            "determinism",
            &[(
                "app.py",
                "def main():\n    live()\n\ndef live():\n    return 1\n\ndef dead():\n    return 2\n",
            )],
        );
        let first_graph = analyze_dir(fixture.path()).expect("first analysis").graph;
        let first = analyze_graph(
            &first_graph,
            fixture.path(),
            &DeadcodeConfig::default(),
            true,
        )
        .expect("first deadcode analysis")
        .to_json_line("fixture", MinConfidence::Low, None);
        let second_graph = analyze_dir(fixture.path()).expect("second analysis").graph;
        let second = analyze_graph(
            &second_graph,
            fixture.path(),
            &DeadcodeConfig::default(),
            true,
        )
        .expect("second deadcode analysis")
        .to_json_line("fixture", MinConfidence::Low, None);
        assert_eq!(first, second);
    }

    fn fixture_node_id(graph: &Graph, kind: &str, name: &str) -> String {
        graph
            .nodes()
            .find(|node| node.kind == kind && node.name == name)
            .unwrap_or_else(|| panic!("missing {kind} node named {name}"))
            .id
            .clone()
    }

    fn fixture_file_id(graph: &Graph, path: &str) -> String {
        graph
            .nodes()
            .find(|node| node.kind == ont::FILE && prop_str(node, "path") == path)
            .unwrap_or_else(|| panic!("missing file node for {path}"))
            .id
            .clone()
    }

    #[test]
    fn imported_module_keeps_its_contained_file_frontier_live() {
        let fixture = Fixture::new(
            "imported-module-frontier",
            &[
                ("entry.py", "def entry():\n    return 0\n"),
                ("imported.py", "def top_level_callee():\n    return 1\n"),
            ],
        );
        let mut graph = analyze_dir(fixture.path()).expect("analyze fixture").graph;
        let entry_file = fixture_file_id(&graph, "entry.py");
        let imported_file = fixture_file_id(&graph, "imported.py");
        let callee = fixture_node_id(&graph, ont::FUNCTION, "top_level_callee");
        let module = "mod::fixture::imported";

        graph.upsert_node(
            entry_file.clone(),
            ont::FILE,
            "entry.py",
            vec![("entrypoint", Json::Bool(true))],
        );
        graph.upsert_node(module, ont::MODULE, "imported", vec![]);
        graph.add_edge(module, edge::CONTAINS, imported_file, vec![]);
        graph.add_edge(entry_file, edge::IMPORTS, module, vec![]);
        graph.add_edge(
            fixture_file_id(&graph, "imported.py"),
            edge::CALLS,
            callee.clone(),
            vec![],
        );

        let report = analyze_graph(&graph, fixture.path(), &DeadcodeConfig::default(), true)
            .expect("analyze dead code");
        assert!(
            report.findings.iter().all(|finding| finding.id != callee),
            "an imported Module must activate its directly contained File frontier"
        );
    }

    #[test]
    fn main_guard_file_roots_its_containing_module_frontier() {
        let fixture = Fixture::new(
            "main-guard-module-frontier",
            &[("app.py", "def module_level_callee():\n    return 1\n")],
        );
        let mut graph = analyze_dir(fixture.path()).expect("analyze fixture").graph;
        let file = fixture_file_id(&graph, "app.py");
        let callee = fixture_node_id(&graph, ont::FUNCTION, "module_level_callee");
        let module = "mod::fixture::app";

        graph.upsert_node(
            file.clone(),
            ont::FILE,
            "app.py",
            vec![("main_guard", Json::Bool(true))],
        );
        graph.upsert_node(module, ont::MODULE, "app", vec![]);
        graph.add_edge(module, edge::CONTAINS, file, vec![]);
        graph.add_edge(module, edge::CALLS, callee.clone(), vec![]);

        let report = analyze_graph(&graph, fixture.path(), &DeadcodeConfig::default(), true)
            .expect("analyze dead code");
        assert!(
            report.findings.iter().all(|finding| finding.id != callee),
            "a main-guard File must root its directly containing Module"
        );
    }

    #[test]
    fn imported_inline_module_does_not_root_sibling_modules() {
        let fixture = Fixture::new(
            "inline-module-frontier",
            &[
                ("entry.rs", "pub fn entry() {}\n"),
                (
                    "host.rs",
                    "pub fn imported_live() {}\npub fn sibling_dead() {}\n",
                ),
            ],
        );
        let mut graph = analyze_dir(fixture.path()).expect("analyze fixture").graph;
        let entry_file = fixture_file_id(&graph, "entry.rs");
        let host_file = fixture_file_id(&graph, "host.rs");
        let imported_live = fixture_node_id(&graph, ont::FUNCTION, "imported_live");
        let sibling_dead = fixture_node_id(&graph, ont::FUNCTION, "sibling_dead");
        let imported_module = "mod::fixture::host::imported";
        let sibling_module = "mod::fixture::host::sibling";

        graph.upsert_node(
            entry_file.clone(),
            ont::FILE,
            "entry.rs",
            vec![("entrypoint", Json::Bool(true))],
        );
        graph.upsert_node(imported_module, ont::MODULE, "imported", vec![]);
        graph.upsert_node(sibling_module, ont::MODULE, "sibling", vec![]);
        graph.add_edge(host_file.clone(), edge::CONTAINS, imported_module, vec![]);
        graph.add_edge(host_file, edge::CONTAINS, sibling_module, vec![]);
        graph.add_edge(entry_file, edge::IMPORTS, imported_module, vec![]);
        graph.add_edge(imported_module, edge::CALLS, imported_live.clone(), vec![]);
        graph.add_edge(sibling_module, edge::CALLS, sibling_dead.clone(), vec![]);

        let report = analyze_graph(&graph, fixture.path(), &DeadcodeConfig::default(), true)
            .expect("analyze dead code");
        assert!(
            report
                .findings
                .iter()
                .all(|finding| finding.id != imported_live),
            "the imported inline Module must propagate its own dependencies"
        );
        assert!(
            report
                .findings
                .iter()
                .any(|finding| finding.id == sibling_dead),
            "importing one inline Module must not root a sibling in the same File"
        );
    }

    #[test]
    fn why_parent_ties_choose_the_ascending_parent_id() {
        let fixture = Fixture::new("why-parent-tie", &[("empty.py", "# fixture\n")]);
        let mut graph = analyze_dir(fixture.path()).expect("analyze fixture").graph;
        for (id, name) in [
            ("fn::root-a", "main"),
            ("fn::root-b", "main"),
            ("fn::z-parent", "z_parent"),
            ("fn::a-parent", "a_parent"),
            ("fn::target", "target"),
        ] {
            graph.upsert_node(id, ont::FUNCTION, name, vec![]);
        }
        graph.add_edge("fn::root-a", edge::CALLS, "fn::z-parent", vec![]);
        graph.add_edge("fn::root-b", edge::CALLS, "fn::a-parent", vec![]);
        graph.add_edge("fn::z-parent", edge::CALLS, "fn::target", vec![]);
        graph.add_edge("fn::a-parent", edge::CALLS, "fn::target", vec![]);

        let report = analyze_graph(&graph, fixture.path(), &DeadcodeConfig::default(), true)
            .expect("analyze dead code");
        assert_eq!(
            report.parents["fn::target"].parent, "fn::a-parent",
            "equal-length why paths must choose the ascending parent id"
        );
    }

    #[test]
    fn config_rejects_unknown_fields_by_name() {
        let error = parse_config(r#"{"roots":[],"framework_magic":true}"#)
            .expect_err("unknown config fields must fail closed");
        assert!(error.contains("framework_magic"), "{error}");
    }
}
