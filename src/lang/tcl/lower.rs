//! Lower the Tcl CST into the canonical graph.
//!
//! This mirrors the Rust, Python, and Bash lowerings — same conservative
//! principles, same shared ontology — adapted to Tcl's surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to a
//!    concrete project proc only when the name yields exactly one definition;
//!    several definitions become an ambiguous edge carrying the full `candidates`
//!    set; an unknown command (a Tcl builtin or an external program) resolves to
//!    an explicit `UnresolvedSymbol`. There is no LLM in the airgap to guess.
//! 2. **Everything comes from real tokens.** Procs, namespaces, calls, includes,
//!    and assignments are read off the lossless tree, never invented.
//!
//! Honest mappings (see the IR Atlas):
//!   - `proc name args body` → `Function` (qualified by its enclosing namespace);
//!   - `namespace eval NS body` → `Module` (a scope), `CONTAINS` from its file;
//!   - `package require PKG` → `IMPORTS` to an `ExternalDependency` (+ `DEPENDS_ON`);
//!   - `source FILE` → `IMPORTS` (to the project file when resolvable, else an
//!     `ExternalDependency` + `DEPENDS_ON`);
//!   - a top-level `set NAME value` → `Constant`;
//!   - any other command word → `CALLS` (to a project proc, else an
//!     `UnresolvedSymbol` standing for the builtin/external command).
//!
//! Tcl has no class/struct/interface constructs at the language level, so this
//! front end emits **no** `Type`, `HAS_METHOD`, `IMPLEMENTS`, or `EXTENDS`
//! nodes/edges — forcing a `Type` onto a Tcl namespace or proc would be dishonest
//! (Atlas design principle 2). Procs are resolvable both by their simple name and
//! by their namespace-qualified name.
//!
//! Honest punts:
//!   - Calls inside `[ … ]` command substitutions are not extracted (the bracket
//!     stays a single token; only command-position words become `CALLS`).
//!   - Object systems layered on Tcl (`itcl`, TclOO `oo::class`, `snit`) are not
//!     modelled as `Type`s; their `method`/`oo::define` bodies are still descended
//!     into for nested procs/calls by the parser, but methods are not `Function`s.
//!   - Only the *final* brace body of a control command is descended into, so a
//!     proc defined inside an `if`'s *then* branch (when an `else` brace follows)
//!     is not seen.

use std::collections::BTreeMap;

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::tcl::lexer::{is_keyword, kind as tk};
use crate::lang::tcl::parser::node as cst;

/// Lower a whole project's worth of Tcl files into a graph. `manifest_deps` is
/// unused for Tcl (there is no manifest concept); dependencies are discovered from
/// `package require` / `source` and unresolved command invocations instead.
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
        vec![("ecosystem", Json::str("tcl"))],
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

    // Pass A: file nodes, namespace Modules, and every proc definition (so a call
    // to a proc defined later in the project still resolves).
    for f in files {
        let li = LineIndex::new(f.source);
        let fid = file_id(&f.rel_path);
        lo.g.upsert_node(
            fid.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("tcl")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(pkg_id.clone(), edge::CONTAINS, fid.clone(), vec![]);
        lo.collect_defs(f.root, &fid, &f.rel_path, f.source, &li, "");
    }

    // Pass B: assignments (Constants), includes (IMPORTS), and call sites (CALLS)
    // resolved against the now-complete proc table.
    for f in files {
        let li = LineIndex::new(f.source);
        let fid = file_id(&f.rel_path);
        lo.walk_commands(f.root, None, &fid, &f.rel_path, f.source, &li, "");
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    /// Resolution name (simple or qualified) → all matching proc node ids.
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

    // --- pass A: namespaces + proc definitions ------------------------------

    fn collect_defs(
        &mut self,
        node: &Node,
        file_id: &str,
        rel_path: &str,
        src: &str,
        li: &LineIndex,
        ns: &str,
    ) {
        for child in node.child_nodes() {
            if child.kind == cst::COMMAND {
                self.collect_command_defs(child, file_id, rel_path, src, li, ns);
            } else {
                // Plain Script wrapper (e.g. an expanded body): recurse, same ns.
                self.collect_defs(child, file_id, rel_path, src, li, ns);
            }
        }
    }

    fn collect_command_defs(
        &mut self,
        cmd: &Node,
        file_id: &str,
        rel_path: &str,
        src: &str,
        li: &LineIndex,
        ns: &str,
    ) {
        let words = command_words(cmd, src);
        let first = words.first().map(|w| w.text.as_str());
        match first {
            Some("proc") => {
                if let Some(name_w) = words.get(1) {
                    self.declare_proc(&name_w.text, name_w.start, rel_path, file_id, ns, li);
                }
                // Nested procs live in this proc's body, in the same namespace.
                for s in cmd.child_nodes() {
                    self.collect_defs(s, file_id, rel_path, src, li, ns);
                }
            }
            Some("namespace") if words.get(1).map(|w| w.text.as_str()) == Some("eval") => {
                let new_ns = match words.get(2) {
                    Some(w) => {
                        let q = qualify(ns, &w.text);
                        self.declare_module(&q, w.start, rel_path, file_id, li);
                        q
                    }
                    None => ns.to_string(),
                };
                for s in cmd.child_nodes() {
                    self.collect_defs(s, file_id, rel_path, src, li, &new_ns);
                }
            }
            _ => {
                // Other body-bearing commands (while/for/catch/…) may still hold
                // nested procs; descend with the same namespace.
                for s in cmd.child_nodes() {
                    self.collect_defs(s, file_id, rel_path, src, li, ns);
                }
            }
        }
    }

    fn declare_proc(
        &mut self,
        name: &str,
        name_start: u32,
        rel_path: &str,
        file_id: &str,
        ns: &str,
        li: &LineIndex,
    ) {
        let qualified = qualify(ns, name);
        let simple = simple_name(&qualified);
        let line = li.line_col(name_start).line;
        let id = fn_id(rel_path, &qualified, line);
        self.g.upsert_node(
            id.clone(),
            ont::FUNCTION,
            simple.clone(),
            vec![
                ("qualified_name", Json::str(qualified.clone())),
                ("language", Json::str("tcl")),
                ("namespace", Json::str(ns.to_string())),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        // Index for resolution under both the qualified and the simple name.
        self.fn_by_name
            .entry(qualified.clone())
            .or_default()
            .push(id.clone());
        if simple != qualified {
            self.fn_by_name.entry(simple).or_default().push(id);
        }
    }

    fn declare_module(
        &mut self,
        qualified: &str,
        name_start: u32,
        rel_path: &str,
        file_id: &str,
        li: &LineIndex,
    ) {
        let line = li.line_col(name_start).line;
        let id = module_id(rel_path, qualified);
        self.g.upsert_node(
            id.clone(),
            ont::MODULE,
            qualified.to_string(),
            vec![
                ("qualified_name", Json::str(qualified.to_string())),
                ("language", Json::str("tcl")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::CONTAINS, id, vec![]);
    }

    // --- pass B: assignments, includes, calls -------------------------------

    #[allow(clippy::too_many_arguments)]
    fn walk_commands(
        &mut self,
        node: &Node,
        owner: Option<&str>,
        file_id: &str,
        rel_path: &str,
        src: &str,
        li: &LineIndex,
        ns: &str,
    ) {
        for child in node.child_nodes() {
            if child.kind == cst::COMMAND {
                self.process_command(child, owner, file_id, rel_path, src, li, ns);
            } else {
                self.walk_commands(child, owner, file_id, rel_path, src, li, ns);
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn process_command(
        &mut self,
        cmd: &Node,
        owner: Option<&str>,
        file_id: &str,
        rel_path: &str,
        src: &str,
        li: &LineIndex,
        ns: &str,
    ) {
        let words = command_words(cmd, src);
        let caller = owner.unwrap_or(file_id).to_string();
        let top_level = owner.is_none();
        let first = words.first();

        // Default body owner/namespace; overridden for proc/namespace below.
        let mut body_owner = owner.map(|s| s.to_string());
        let mut body_ns = ns.to_string();

        match first.map(|w| w.text.as_str()) {
            Some("proc") => {
                if let Some(name_w) = words.get(1) {
                    let qualified = qualify(ns, &name_w.text);
                    let line = li.line_col(name_w.start).line;
                    body_owner = Some(fn_id(rel_path, &qualified, line));
                }
            }
            Some("namespace") if words.get(1).map(|w| w.text.as_str()) == Some("eval") => {
                if let Some(name_w) = words.get(2) {
                    body_ns = qualify(ns, &name_w.text);
                }
            }
            Some("package") if words.get(1).map(|w| w.text.as_str()) == Some("require") => {
                if let Some(pkg_w) = words.get(2) {
                    self.emit_require(file_id, &pkg_w.text);
                }
            }
            Some("source") => {
                if let Some(arg) = words.get(1) {
                    self.emit_include(file_id, &arg.text);
                }
            }
            Some("set") => {
                if top_level {
                    if let Some(name_w) = words.get(1) {
                        if is_name(&name_w.text) {
                            let line = li.line_col(name_w.start).line;
                            self.emit_constant(&name_w.text, file_id, rel_path, line);
                        }
                    }
                }
            }
            Some(w) if is_keyword(w) => { /* control word: not a call */ }
            Some(_) => {
                if let Some(fw) = first {
                    // Only a literal bareword is a resolvable command name; a
                    // dynamic word (`$cmd …`, `[x] …`) is left alone.
                    if fw.first_kind == tk::WORD {
                        self.emit_call(&caller, &fw.text, ns);
                    }
                }
            }
            None => {}
        }

        // Descend into any body scripts this command holds.
        for s in cmd.child_nodes() {
            self.walk_commands(
                s,
                body_owner.as_deref(),
                file_id,
                rel_path,
                src,
                li,
                &body_ns,
            );
        }
    }

    fn emit_constant(&mut self, name: &str, file_id: &str, rel_path: &str, line: u32) {
        let id = format!("const::{rel_path}:{name}");
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            name.to_string(),
            vec![
                ("binding", Json::str("tcl_var")),
                ("language", Json::str("tcl")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
    }

    /// Resolve a command word to a project proc or an explicit external/unresolved
    /// command node, then emit the `CALLS` edge. A simple name is first resolved
    /// within the current namespace, then globally.
    fn emit_call(&mut self, caller: &str, name: &str, ns: &str) {
        let key = name.trim_start_matches("::").to_string();
        // Prefer a namespace-local match for a simple (unqualified) name.
        let candidates = if !key.contains("::") && !ns.is_empty() {
            let local = qualify(ns, &key);
            match self.fn_by_name.get(&local) {
                Some(v) => v.clone(),
                None => self.fn_by_name.get(&key).cloned().unwrap_or_default(),
            }
        } else {
            self.fn_by_name.get(&key).cloned().unwrap_or_default()
        };

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
                let target = unresolved_id(&key);
                self.ensure_unresolved(&target, name);
                props.push(("resolved", Json::Bool(false)));
                props.push(("resolution", Json::str("external")));
                props.push(("candidate_count", Json::U64(0)));
                self.g.add_edge(caller, edge::CALLS, target, props);
            }
            n => {
                let target = unresolved_id(&key);
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

    /// `package require PKG`: an `ExternalDependency` (+ `IMPORTS` / `DEPENDS_ON`).
    fn emit_require(&mut self, file_id: &str, pkg_text: &str) {
        let name = strip_quotes(pkg_text);
        if name.is_empty() {
            return;
        }
        let dep_id = ext_id(name);
        self.g.upsert_node(
            dep_id.clone(),
            ont::EXTERNAL_DEPENDENCY,
            name.to_string(),
            vec![
                ("external", Json::Bool(true)),
                ("ecosystem", Json::str("tcl")),
                ("source", Json::str("package require")),
            ],
        );
        self.g.add_edge(
            file_id,
            edge::IMPORTS,
            dep_id.clone(),
            vec![
                ("path", Json::str(name.to_string())),
                ("external", Json::Bool(true)),
            ],
        );
        let pkg = self.pkg_id();
        self.g.add_edge(pkg, edge::DEPENDS_ON, dep_id, vec![]);
    }

    /// `source FILE`: an `IMPORTS` edge to the project file when the path resolves,
    /// else an `ExternalDependency` (+ `DEPENDS_ON`).
    fn emit_include(&mut self, file_id: &str, arg_text: &str) {
        let cleaned = strip_quotes(arg_text);
        let dynamic = cleaned.is_empty()
            || cleaned.contains('$')
            || cleaned.contains('[')
            || cleaned.contains('{');
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

/// One command word: its full reconstructed text plus the kind and byte offset of
/// its leading token (enough to tell a literal command name from a dynamic one).
struct Word {
    text: String,
    first_kind: &'static str,
    start: u32,
}

/// Split a `Command` node's direct children into words. Words are runs of adjacent
/// significant tokens; trivia, `newline`/`;`, and child nodes (an expanded body)
/// end the current word.
fn command_words(node: &Node, src: &str) -> Vec<Word> {
    let mut out = Vec::new();
    let mut cur: Option<Word> = None;
    for ch in &node.children {
        match ch {
            Child::Token(t) => {
                if t.trivia || t.kind == tk::NEWLINE || t.kind == tk::SEMICOLON {
                    if let Some(w) = cur.take() {
                        out.push(w);
                    }
                } else {
                    let txt = t.span.text(src);
                    match &mut cur {
                        Some(w) => w.text.push_str(txt),
                        None => {
                            cur = Some(Word {
                                text: txt.to_string(),
                                first_kind: t.kind,
                                start: t.span.start,
                            })
                        }
                    }
                }
            }
            Child::Node(_) => {
                if let Some(w) = cur.take() {
                    out.push(w);
                }
            }
        }
    }
    if let Some(w) = cur.take() {
        out.push(w);
    }
    out
}

/// Combine a namespace prefix and a (possibly qualified) name into a single
/// fully-qualified name, normalizing leading `::` away.
fn qualify(ns: &str, name: &str) -> String {
    if let Some(stripped) = name.strip_prefix("::") {
        return stripped.to_string(); // absolute name
    }
    if ns.is_empty() {
        name.to_string()
    } else {
        format!("{ns}::{name}")
    }
}

/// The final `::`-delimited segment of a qualified name.
fn simple_name(qualified: &str) -> String {
    qualified
        .rsplit("::")
        .next()
        .unwrap_or(qualified)
        .to_string()
}

/// True if `s` is a plain Tcl variable name we record as a `Constant` (no array
/// index, no substitution). `::` is allowed for qualified globals.
fn is_name(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }
    let core = s.trim_start_matches("::");
    if core.is_empty() {
        return false;
    }
    core.chars()
        .all(|c| c == '_' || c == ':' || c.is_alphanumeric())
}

fn strip_quotes(s: &str) -> &str {
    let b = s.as_bytes();
    if b.len() >= 2 && (b[0] == b'"' || b[0] == b'{') {
        let close = if b[0] == b'{' { b'}' } else { b'"' };
        if b[b.len() - 1] == close {
            return &s[1..s.len() - 1];
        }
    }
    s
}

fn fn_id(rel_path: &str, qualified: &str, line: u32) -> String {
    format!("fn::{rel_path}:{qualified}#{line}")
}

fn module_id(rel_path: &str, qualified: &str) -> String {
    format!("module::{rel_path}:{qualified}")
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::tcl::parser::parse;
    use std::collections::BTreeSet;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("script.tcl", src);
        let file = SourceFile {
            rel_path: "script.tcl".to_string(),
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
    fn emits_proc_and_file_nodes() {
        let g = graph_for("proc f {} { puts hi }\nproc g {} { puts bye }\n");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "f + g");
        assert_eq!(g.count_nodes_of(ont::FILE), 1);
        assert_eq!(g.count_nodes_of(ont::PACKAGE), 1);
        // No class-like constructs in plain Tcl.
        assert_eq!(g.count_nodes_of(ont::TYPE), 0);
    }

    #[test]
    fn proc_node_has_tcl_language_tag() {
        let g = graph_for("proc f {} { puts hi }\n");
        let f = g.nodes().find(|n| n.kind == ont::FUNCTION).expect("a proc");
        assert_eq!(f.props.get("language"), Some(&Json::str("tcl")));
    }

    #[test]
    fn resolves_call_to_project_proc() {
        let g = graph_for("proc greet {} { puts hi }\nproc run {} { greet }\n");
        let calls = call_edges(&g);
        let to_greet = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("greet")))
            .expect("a call to greet");
        assert!(to_greet.to.starts_with("fn::script.tcl:greet"));
        assert_eq!(to_greet.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(
            to_greet.props.get("resolution"),
            Some(&Json::str("project"))
        );
    }

    #[test]
    fn unknown_command_is_external() {
        let g = graph_for("proc run {} { notacmd }\n");
        let calls = call_edges(&g);
        let ext = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("notacmd")))
            .expect("a call to notacmd");
        assert_eq!(ext.props.get("resolution"), Some(&Json::str("external")));
        assert!(g.has_node("unresolved::notacmd"));
    }

    #[test]
    fn namespace_eval_is_module() {
        let g = graph_for("namespace eval ::app {\n  proc tick {} { incr ::app::count }\n}\n");
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "::app is a Module");
        let m = g.nodes().find(|n| n.kind == ont::MODULE).unwrap();
        assert_eq!(m.name, "app");
        // The proc inside is qualified by its namespace.
        let proc = g.nodes().find(|n| n.kind == ont::FUNCTION).expect("a proc");
        assert_eq!(
            proc.props.get("qualified_name"),
            Some(&Json::str("app::tick"))
        );
    }

    #[test]
    fn top_level_set_is_constant() {
        let g = graph_for("set NAME value\nproc f {} { set local 1 }\n");
        // NAME is a top-level Constant; the proc-local `set local` is not.
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 1);
        let c = g
            .nodes()
            .find(|n| n.kind == ont::CONSTANT)
            .expect("a constant");
        assert_eq!(c.name, "NAME");
    }

    #[test]
    fn package_require_is_external_dependency() {
        let g = graph_for("package require Tk 8.6\n");
        assert!(g.has_node("ext::Tk"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::IMPORTS && e.to == "ext::Tk"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::Tk"));
    }

    #[test]
    fn source_unknown_is_external_dependency() {
        let g = graph_for("source ./lib.tcl\n");
        assert!(g.has_node("ext::lib.tcl"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::IMPORTS && e.to == "ext::lib.tcl"));
    }

    #[test]
    fn nested_proc_in_body_is_found() {
        let g = graph_for("proc outer {} {\n  proc inner {} { puts hi }\n}\n");
        let names: BTreeSet<String> = g
            .nodes()
            .filter(|n| n.kind == ont::FUNCTION)
            .map(|n| n.name.clone())
            .collect();
        assert!(names.contains("outer"));
        assert!(names.contains("inner"));
    }

    #[test]
    fn output_is_deterministic() {
        let src = "set A 1\nproc f {} { g }\nnamespace eval ns { proc g {} { puts hi } }\nsource ./lib.tcl\npackage require Tk\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
