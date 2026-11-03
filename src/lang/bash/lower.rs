//! Lower the Bash CST into the canonical graph.
//!
//! This mirrors the Rust and Python lowerings — same conservative principles,
//! same shared ontology — adapted to shell's surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to a
//!    concrete project function only when the name yields exactly one definition;
//!    several definitions become an ambiguous edge carrying the full `candidates`
//!    set; an unknown command (a shell builtin or an external program) resolves to
//!    an explicit `UnresolvedSymbol`. There is no LLM in the airgap to guess.
//! 2. **Everything comes from real tokens.** Calls, assignments, and `source`
//!    includes are read off the lossless tree, never invented.
//!
//! Honest mappings (see the IR Atlas):
//!   - a function definition (`f() { … }` or `function f { … }`) → `Function`;
//!   - a top-level assignment (`NAME=value`, `export NAME=…`) → `Constant`;
//!   - `source FILE` / `. FILE` → `IMPORTS` (to the project file when resolvable,
//!     otherwise an `ExternalDependency` + `DEPENDS_ON`);
//!   - a command invocation → `CALLS` (to a project function, else an
//!     `UnresolvedSymbol` standing for the builtin/external command).
//!
//! Shell has no class/struct/interface constructs, so this front end emits **no**
//! `Type`, `HAS_METHOD`, `IMPLEMENTS`, or `EXTENDS` nodes/edges — forcing a `Type`
//! onto a shell function would be dishonest (Atlas design principle 2). Functions
//! are file-global in shell; nested definitions are still reachable globally, so
//! every function is indexed by its simple name for call resolution.

use std::collections::BTreeMap;

use crate::core::cst::Node;
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::bash::lexer::{is_keyword, kind as tk};
use crate::lang::bash::parser::node as cst;
use crate::lang::frontend::SourceFile;

/// Lower a whole project's worth of shell files into a graph. `manifest_deps` is
/// unused for shell (there is no manifest concept); dependencies are discovered
/// from `source`/`.` includes and unresolved command invocations instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        fn_by_name: BTreeMap::new(),
        file_id_by_rel: BTreeMap::new(),
        files_by_base: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id.clone(),
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("shell"))],
    );

    // Pre-index files so `source` includes can resolve to a concrete project file.
    for f in files {
        let id = file_id(&f.rel_path);
        let norm = f.rel_path.trim_start_matches("./").to_string();
        lo.file_id_by_rel.insert(norm, id.clone());
        lo.files_by_base
            .entry(file_name(&f.rel_path))
            .or_default()
            .push(id);
    }

    // Pass A: file nodes + every function definition (so a call to a function
    // defined later in the project still resolves).
    for f in files {
        let li = LineIndex::new(f.source);
        let fid = file_id(&f.rel_path);
        lo.g.upsert_node(
            fid.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("bash")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(pkg_id.clone(), edge::CONTAINS, fid.clone(), vec![]);
        lo.collect_functions(f.root, &fid, &f.rel_path, f.source, &li);
    }

    // Pass B: assignments (Constants), includes (IMPORTS), and call sites (CALLS)
    // resolved against the now-complete function table.
    for f in files {
        let li = LineIndex::new(f.source);
        let fid = file_id(&f.rel_path);
        lo.walk_commands(f.root, None, &fid, &f.rel_path, f.source, &li);
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    /// Simple function name → all function node ids (global level).
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// Normalized rel-path → file node id (for `source` resolution).
    file_id_by_rel: BTreeMap<String, String>,
    /// File basename → file node ids (for `source` basename resolution).
    files_by_base: BTreeMap<String, Vec<String>>,
}

impl Lowerer {
    fn pkg_id(&self) -> String {
        format!("pkg::{}", self.package)
    }

    // --- pass A: function definitions ---------------------------------------

    /// Walk the tree creating a `Function` node for every definition (top-level or
    /// nested), recording it in the global name index and a `DECLARES` edge from
    /// the file.
    fn collect_functions(
        &mut self,
        node: &Node,
        file_id: &str,
        rel_path: &str,
        src: &str,
        li: &LineIndex,
    ) {
        for child in node.child_nodes() {
            if child.kind == cst::FUNCTION {
                self.declare_function(child, file_id, rel_path, src, li);
            }
            // Recurse: nested functions live anywhere (group/compound/function body).
            self.collect_functions(child, file_id, rel_path, src, li);
        }
    }

    fn declare_function(
        &mut self,
        item: &Node,
        file_id: &str,
        rel_path: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let name = match name_text(item, src) {
            Some(n) => n.to_string(),
            None => return,
        };
        let line = li.line_col(name_span_start(item)).line;
        let id = fn_id(rel_path, &name, line);
        let has_body = item.child(cst::GROUP).is_some()
            || item.child(cst::COMPOUND).is_some()
            || item.child(cst::COMMAND).is_some();
        self.g.upsert_node(
            id.clone(),
            ont::FUNCTION,
            name.clone(),
            vec![
                ("qualified_name", Json::str(name.clone())),
                ("language", Json::str("bash")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
                ("has_body", Json::Bool(has_body)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.fn_by_name.entry(name).or_default().push(id);
    }

    // --- pass B: assignments, includes, calls -------------------------------

    /// Walk statements, tracking the enclosing function (`owner`). Commands are
    /// analyzed for facts; descending into a function switches the owner so its
    /// call sites are attributed to it, while groups/compounds keep the current
    /// owner (shell groups are not separate scopes).
    fn walk_commands(
        &mut self,
        node: &Node,
        owner: Option<&str>,
        file_id: &str,
        rel_path: &str,
        src: &str,
        li: &LineIndex,
    ) {
        for child in node.child_nodes() {
            match child.kind {
                cst::FUNCTION => {
                    let name = name_text(child, src).unwrap_or("");
                    let line = li.line_col(name_span_start(child)).line;
                    let fid = fn_id(rel_path, name, line);
                    self.walk_commands(child, Some(&fid), file_id, rel_path, src, li);
                }
                cst::COMMAND => {
                    self.process_command(child, owner, file_id, rel_path, src, li);
                }
                _ => {
                    self.walk_commands(child, owner, file_id, rel_path, src, li);
                }
            }
        }
    }

    fn process_command(
        &mut self,
        node: &Node,
        owner: Option<&str>,
        file_id: &str,
        rel_path: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let caller = owner.unwrap_or(file_id).to_string();
        let top_level = owner.is_none();
        let toks = command_tokens(node, src);
        for seg in split_pipelines(&toks) {
            self.process_segment(seg, &caller, top_level, file_id, rel_path, li);
        }
    }

    /// Analyze one pipeline segment: leading `NAME=value` assignments, then the
    /// command word (an include, or a call).
    fn process_segment(
        &mut self,
        seg: &[TokInfo<'_>],
        caller: &str,
        top_level: bool,
        file_id: &str,
        rel_path: &str,
        li: &LineIndex,
    ) {
        let mut i = 0;
        let mut decl_only = false;
        let export_command = seg.first().is_some_and(|t| t.text == "export");
        let mut exported = export_command;
        if let Some(t0) = seg.first() {
            if matches!(
                t0.text,
                "export" | "declare" | "readonly" | "local" | "typeset"
            ) {
                decl_only = true;
                i = 1;
            }
        }
        while i < seg.len() && seg[i].text.starts_with('-') {
            if export_command && seg[i].text != "-x" {
                exported = false;
            }
            i += 1;
        }

        // Leading assignment prefixes (`A=1 B=2 cmd …` or `export A=1`).
        while i + 1 < seg.len()
            && seg[i].kind == tk::WORD
            && is_name(seg[i].text)
            && seg[i + 1].text == "="
            && seg[i].end == seg[i + 1].start
        {
            if top_level {
                let line = li.line_col(seg[i].start).line;
                self.emit_constant(seg[i].text, file_id, rel_path, line, exported);
            }
            // Skip the (contiguous) value tokens of this assignment.
            let mut j = i + 2;
            let mut last_end = seg[i + 1].end;
            while j < seg.len() && seg[j].start == last_end {
                last_end = seg[j].end;
                j += 1;
            }
            i = j;
        }

        if exported && top_level {
            for item in &seg[i..] {
                if item.kind == tk::WORD && is_name(item.text) {
                    let line = li.line_col(item.start).line;
                    self.emit_constant(item.text, file_id, rel_path, line, true);
                }
            }
        }

        if decl_only {
            return; // `export`/`declare`/… is a builtin, not a call we record.
        }
        let cmd = match seg.get(i) {
            Some(t) if t.kind == tk::WORD => t,
            _ => return,
        };
        if cmd.text == "source" || cmd.text == "." {
            if let Some(arg) = seg.get(i + 1) {
                self.emit_include(file_id, arg.text);
            }
            return;
        }
        if is_keyword(cmd.text) {
            return;
        }
        self.emit_call(caller, cmd.text);
    }

    fn emit_constant(
        &mut self,
        name: &str,
        file_id: &str,
        rel_path: &str,
        line: u32,
        exported: bool,
    ) {
        let id = format!("const::{rel_path}:{name}");
        let mut props = vec![
            ("binding", Json::str("shell_var")),
            ("language", Json::str("bash")),
            ("line", Json::U64(line as u64)),
        ];
        if exported {
            props.push(("exported", Json::Bool(true)));
        }
        self.g
            .upsert_node(id.clone(), ont::CONSTANT, name.to_string(), props);
        self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
    }

    /// Resolve a command word to a project function or an explicit external/
    /// unresolved command node, then emit the `CALLS` edge.
    fn emit_call(&mut self, caller: &str, name: &str) {
        let candidates = self.fn_by_name.get(name).cloned().unwrap_or_default();
        let mut props = vec![("callee", Json::str(name.to_string()))];
        match candidates.len() {
            1 => {
                props.push(("resolved", Json::Bool(true)));
                props.push(("resolution", Json::str("project")));
                props.push(("candidate_count", Json::U64(1)));
                self.g
                    .add_edge(caller, edge::CALLS, candidates[0].clone(), props);
            }
            0 => {
                let target = unresolved_id(name);
                self.ensure_unresolved(&target, name);
                props.push(("resolved", Json::Bool(false)));
                props.push(("resolution", Json::str("external")));
                props.push(("candidate_count", Json::U64(0)));
                self.g.add_edge(caller, edge::CALLS, target, props);
            }
            n => {
                let target = unresolved_id(name);
                self.ensure_unresolved(&target, name);
                props.push(("resolved", Json::Bool(false)));
                props.push(("resolution", Json::str("ambiguous")));
                props.push(("ambiguous", Json::Bool(true)));
                props.push(("candidate_count", Json::U64(n as u64)));
                props.push((
                    "candidates",
                    Json::Array(candidates.into_iter().map(Json::Str).collect()),
                ));
                self.g.add_edge(caller, edge::CALLS, target, props);
            }
        }
    }

    fn ensure_unresolved(&mut self, id: &str, name: &str) {
        if !self.g.has_node(id) {
            self.g.upsert_node(
                id.to_string(),
                ont::UNRESOLVED,
                name.to_string(),
                vec![
                    ("unresolved", Json::Bool(true)),
                    ("role", Json::str("command")),
                ],
            );
        }
    }

    /// `source FILE` / `. FILE`: an `IMPORTS` edge to the project file when the
    /// path resolves, else an `ExternalDependency` (+ `DEPENDS_ON`).
    fn emit_include(&mut self, file_id: &str, arg_text: &str) {
        let cleaned = strip_quotes(arg_text);
        let dynamic = cleaned.is_empty() || cleaned.contains('$') || cleaned.contains('`');
        if !dynamic {
            let norm = cleaned.trim_start_matches("./");
            if let Some(target) = self.file_id_by_rel.get(norm).cloned() {
                self.g.add_edge(
                    file_id,
                    edge::IMPORTS,
                    target,
                    vec![
                        ("path", Json::str(cleaned.to_string())),
                        ("external", Json::Bool(false)),
                    ],
                );
                return;
            }
            if let Some(ids) = self.files_by_base.get(&file_name(cleaned)) {
                if ids.len() == 1 {
                    let target = ids[0].clone();
                    self.g.add_edge(
                        file_id,
                        edge::IMPORTS,
                        target,
                        vec![
                            ("path", Json::str(cleaned.to_string())),
                            ("external", Json::Bool(false)),
                        ],
                    );
                    return;
                }
            }
        }
        let base = if cleaned.is_empty() {
            "include".to_string()
        } else {
            file_name(cleaned)
        };
        let dep_id = ext_id(&base);
        self.g.upsert_node(
            dep_id.clone(),
            ont::EXTERNAL_DEPENDENCY,
            base,
            vec![
                ("external", Json::Bool(true)),
                ("source", Json::str("source")),
            ],
        );
        self.g.add_edge(
            file_id,
            edge::IMPORTS,
            dep_id.clone(),
            vec![
                ("path", Json::str(arg_text.to_string())),
                ("external", Json::Bool(true)),
            ],
        );
        let pkg = self.pkg_id();
        self.g.add_edge(pkg, edge::DEPENDS_ON, dep_id, vec![]);
    }
}

// --- pure helpers -----------------------------------------------------------

/// A flat token (text + kind + byte span) used by the small token-list helpers.
#[derive(Clone, Copy)]
struct TokInfo<'a> {
    text: &'a str,
    kind: &'static str,
    start: u32,
    end: u32,
}

/// Direct, non-trivia child tokens of a `Command` node, in source order.
fn command_tokens<'a>(node: &'a Node, src: &'a str) -> Vec<TokInfo<'a>> {
    node.tokens()
        .filter(|t| t.kind != tk::NEWLINE)
        .map(|t| TokInfo {
            text: t.span.text(src),
            kind: t.kind,
            start: t.span.start,
            end: t.span.end,
        })
        .collect()
}

/// Split a command's tokens into pipeline segments on the connectors
/// `|`, `||`, `&&`, `|&`. Each segment has its own command word.
fn split_pipelines<'a, 'b>(toks: &'b [TokInfo<'a>]) -> Vec<&'b [TokInfo<'a>]> {
    let mut out = Vec::new();
    let mut start = 0;
    for (idx, t) in toks.iter().enumerate() {
        if matches!(t.text, "|" | "||" | "&&" | "|&") {
            if idx > start {
                out.push(&toks[start..idx]);
            }
            start = idx + 1;
        }
    }
    if start < toks.len() {
        out.push(&toks[start..]);
    }
    out
}

/// True if `s` is a valid shell variable name (`[A-Za-z_][A-Za-z0-9_]*`).
fn is_name(s: &str) -> bool {
    let mut chars = s.chars();
    match chars.next() {
        Some(c) if c == '_' || c.is_ascii_alphabetic() => {}
        _ => return false,
    }
    chars.all(|c| c == '_' || c.is_ascii_alphanumeric())
}

fn strip_quotes(s: &str) -> &str {
    let b = s.as_bytes();
    if b.len() >= 2 && (b[0] == b'\'' || b[0] == b'"') && b[b.len() - 1] == b[0] {
        &s[1..s.len() - 1]
    } else {
        s
    }
}

fn fn_id(rel_path: &str, name: &str, line: u32) -> String {
    format!("fn::{rel_path}:{name}#{line}")
}

fn file_id(rel: &str) -> String {
    format!("file::{rel}")
}

fn ext_id(name: &str) -> String {
    format!("ext::{name}")
}

fn unresolved_id(name: &str) -> String {
    format!("unresolved::{name}")
}

fn file_name(rel: &str) -> String {
    rel.rsplit('/').next().unwrap_or(rel).to_string()
}

fn extension(rel: &str) -> String {
    match rel.rsplit_once('.') {
        Some((_, ext)) => ext.to_string(),
        None => String::new(),
    }
}

fn line_count(src: &str) -> usize {
    if src.is_empty() {
        0
    } else {
        src.matches('\n').count() + 1
    }
}

fn name_text<'a>(item: &'a Node, src: &'a str) -> Option<&'a str> {
    let nm = item.child(cst::NAME)?;
    nm.tokens().next().map(|t| t.span.text(src))
}

fn name_span_start(item: &Node) -> u32 {
    item.child(cst::NAME)
        .map(|n| n.span.start)
        .unwrap_or(item.span.start)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::bash::parser::parse;
    use std::collections::BTreeSet;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("script.sh", src);
        let file = SourceFile {
            rel_path: "script.sh".to_string(),
            module_path: vec![],
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    fn call_edges(g: &Graph) -> Vec<&crate::graph::GraphEdge> {
        g.edges().filter(|e| e.kind == edge::CALLS).collect()
    }

    #[test]
    fn emits_function_and_file_nodes() {
        let g = graph_for("f() {\n  echo hi\n}\nfunction g {\n  echo bye\n}\n");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "f + g");
        assert_eq!(g.count_nodes_of(ont::FILE), 1);
        assert_eq!(g.count_nodes_of(ont::PACKAGE), 1);
        // No class-like constructs in shell.
        assert_eq!(g.count_nodes_of(ont::TYPE), 0);
    }

    #[test]
    fn function_node_has_bash_language_tag() {
        let g = graph_for("f() {\n  echo hi\n}\n");
        let f = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION)
            .expect("a function");
        assert_eq!(f.props.get("language"), Some(&Json::str("bash")));
    }

    #[test]
    fn resolves_call_to_project_function() {
        let g = graph_for("greet() {\n  echo hi\n}\nrun() {\n  greet\n}\n");
        let calls = call_edges(&g);
        let to_greet = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("greet")))
            .expect("a call to greet");
        assert!(to_greet.to.starts_with("fn::script.sh:greet"));
        assert_eq!(to_greet.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(
            to_greet.props.get("resolution"),
            Some(&Json::str("project"))
        );
    }

    #[test]
    fn unknown_command_is_external() {
        let g = graph_for("run() {\n  notacmd\n}\n");
        let calls = call_edges(&g);
        let ext = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("notacmd")))
            .expect("a call to notacmd");
        assert_eq!(ext.props.get("resolution"), Some(&Json::str("external")));
        assert!(g.has_node("unresolved::notacmd"));
    }

    #[test]
    fn top_level_assignment_is_constant() {
        let g = graph_for("NAME=value\nf() {\n  local x=1\n}\n");
        // NAME is a top-level Constant; the function-local x is not.
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 1);
        let c = g
            .nodes()
            .find(|n| n.kind == ont::CONSTANT)
            .expect("a constant");
        assert_eq!(c.name, "NAME");
    }

    #[test]
    fn export_assignment_is_constant() {
        let g = graph_for("export PATH=/usr/bin\n");
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 1);
        let c = g.nodes().find(|n| n.kind == ont::CONSTANT).unwrap();
        assert_eq!(c.name, "PATH");
    }

    #[test]
    fn export_marks_constant_as_exported() {
        let assigned = graph_for("export ASSIGNED=value\n");
        let assigned = assigned
            .nodes()
            .find(|n| n.kind == ont::CONSTANT)
            .expect("exported assignment constant");
        assert_eq!(assigned.props.get("exported"), Some(&Json::Bool(true)));

        let bare = graph_for("export BARE\n");
        let bare = bare
            .nodes()
            .find(|n| n.kind == ont::CONSTANT)
            .expect("bare export constant");
        assert_eq!(bare.props.get("exported"), Some(&Json::Bool(true)));
    }

    #[test]
    fn export_query_and_unexport_flags_do_not_mark_constants_exported() {
        for src in ["export -p NAME\n", "export -- NAME\n", "export -n NAME\n"] {
            let exported = graph_for(src)
                .nodes()
                .find(|node| node.kind == ont::CONSTANT && node.name == "NAME")
                .and_then(|node| node.props.get("exported"))
                .cloned();
            assert_eq!(exported, None, "{src:?}");
        }
    }

    #[test]
    fn export_x_marks_remaining_name_exported() {
        let g = graph_for("export -x NAME\n");
        let name = g
            .nodes()
            .find(|node| node.kind == ont::CONSTANT && node.name == "NAME")
            .expect("exported name");
        assert_eq!(name.props.get("exported"), Some(&Json::Bool(true)));
    }

    #[test]
    fn plain_assignment_is_not_exported() {
        let g = graph_for("PLAIN=value\n");
        let constant = g
            .nodes()
            .find(|n| n.kind == ont::CONSTANT)
            .expect("plain assignment constant");
        assert_eq!(constant.props.get("exported"), None);
    }

    #[test]
    fn source_unknown_is_external_dependency() {
        let g = graph_for("source ./lib.sh\n");
        assert!(g.has_node("ext::lib.sh"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::IMPORTS && e.to == "ext::lib.sh"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::lib.sh"));
    }

    #[test]
    fn pipeline_segments_each_yield_a_call() {
        let g = graph_for("run() {\n  alpha | beta\n}\n");
        let callees: BTreeSet<String> = call_edges(&g)
            .iter()
            .filter_map(|e| e.props.get("callee"))
            .filter_map(|j| match j {
                Json::Str(s) => Some(s.clone()),
                _ => None,
            })
            .collect();
        assert!(callees.contains("alpha"), "first pipeline command");
        assert!(callees.contains("beta"), "second pipeline command");
    }

    #[test]
    fn output_is_deterministic() {
        let src = "A=1\nf() {\n  g\n}\nfunction g {\n  echo hi\n}\nsource ./lib.sh\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
