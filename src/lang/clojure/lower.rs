//! Lower the Clojure CST into the canonical graph.
//!
//! Conservative, honest mappings (see the IR Atlas). A *form* is a list whose
//! first symbol names the operator:
//!
//!   - `(ns my.app …)`                         → `Module` (the file's namespace)
//!   - `(defn  name …)` / `(defn- name …)`     → `Function`
//!   - `(defmacro name …)`                      → `Function` (`def_form: defmacro`)
//!   - `(def name …)` / `(defonce name …)`      → `Constant`
//!   - `(defrecord|deftype|defprotocol name …)` → `Type` (`type_kind` records which)
//!   - `(:require …)`/`(:use …)`/`(:import …)` inside `ns`, and top-level
//!     `(require …)`/`(use …)`/`(import …)`     → `IMPORTS` (+ `ExternalDependency`
//!     / `DEPENDS_ON` for namespaces the project does not own)
//!   - the first symbol of any other list, inside a function body, that resolves
//!     to a project-defined function → `CALLS`
//!
//! Principles carried over from the Rust/Python lowerings:
//!   1. **No fabricated targets.** A `CALLS` edge is emitted only when the head
//!      symbol resolves to a project function. A unique match → a resolved edge; a
//!      name shared by several defs → an ambiguous edge carrying the full
//!      `candidates` set; an unknown head (a special form, a macro, a host-interop
//!      call, or a function from a dependency we cannot see in the airgap) → *no
//!      edge*. We prefer fewer, correct edges over guesses.
//!   2. **Everything comes from real tokens.** Names, namespaces, and call heads
//!      are read off the lossless tree, never invented.
//!
//! Honest coverage gaps (documented, not hidden): calls are resolved by simple
//! name only (Clojure has no static type inference here), so a cross-namespace
//! `other.ns/f` resolves to any project `f`; top-level (non-function) call sites
//! are not attributed (there is no enclosing `Function` to own the edge); a form
//! marked for `#_` discard is still treated as live (the discard is lexer trivia).

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::clojure::lexer::kind as tk;
use crate::lang::clojure::lexer::{is_close_delim, is_open_delim};
use crate::lang::clojure::parser::node as cst;
use crate::lang::frontend::SourceFile;

/// Lower a whole project's worth of Clojure files into a graph. `manifest_deps` is
/// unused (the pipeline's manifest reader is Cargo-only); dependencies are
/// discovered from `:require`/`:use`/`:import` instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    // Determine each file's namespace (from its `ns` form, else its module path).
    let file_ns: Vec<String> = files
        .iter()
        .map(|f| ns_of_file(f.root, f.source).unwrap_or_else(|| f.module_path.join(".")))
        .collect();

    // Project-local namespaces and their root segments. A required namespace that
    // is one of these is intra-project, not an external dependency.
    let mut local_ns: BTreeSet<String> = BTreeSet::new();
    let mut local_roots: BTreeSet<String> = BTreeSet::new();
    local_roots.insert(package.to_string());
    for ns in &file_ns {
        if ns.is_empty() {
            continue;
        }
        local_ns.insert(ns.clone());
        if let Some(root) = ns.split('.').next() {
            local_roots.insert(root.to_string());
        }
    }
    for f in files {
        for seg in &f.module_path {
            local_roots.insert(seg.clone());
        }
    }

    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        local_ns,
        local_roots,
        fn_by_name: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("clojure"))],
    );

    // Pass B: create definition nodes + structural edges, build the symbol table.
    let mut pend: Vec<PendingFn> = Vec::new();
    for (idx, f) in files.iter().enumerate() {
        let ns = &file_ns[idx];
        let li = LineIndex::new(f.source);
        let leaf = lo.ensure_modules(ns);
        let file_id = format!("file::{}", f.rel_path);
        lo.g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("clojure")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(leaf, edge::CONTAINS, file_id.clone(), vec![]);
        lo.walk_top(f.root, &file_id, ns, f.source, &li, &mut pend);
    }

    // Pass C: resolve calls against the now-complete symbol table.
    for pf in &pend {
        let mut calls = Vec::new();
        for child in pf.node.child_nodes() {
            scan_calls(child, pf.src, &mut calls);
        }
        for name in &calls {
            lo.emit_call(&pf.id, name);
        }
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    local_ns: BTreeSet<String>,
    local_roots: BTreeSet<String>,
    /// Simple (unqualified) function name → all defining node ids.
    fn_by_name: BTreeMap<String, Vec<String>>,
}

/// A function whose body is scanned for call sites in pass C.
struct PendingFn<'a> {
    id: String,
    node: &'a Node,
    src: &'a str,
}

impl Lowerer {
    fn pkg_id(&self) -> String {
        format!("pkg::{}", self.package)
    }

    /// Ensure the `Package → mod::a → mod::a.b …` chain exists for a dotted
    /// namespace and return the leaf module id (or the package id for an empty ns).
    fn ensure_modules(&mut self, ns: &str) -> String {
        let pkg = self.pkg_id();
        if ns.is_empty() {
            return pkg;
        }
        let mut parent = pkg;
        let mut acc: Vec<&str> = Vec::new();
        for seg in ns.split('.') {
            acc.push(seg);
            let id = format!("mod::{}", acc.join("."));
            self.g.upsert_node(
                id.clone(),
                ont::MODULE,
                seg.to_string(),
                vec![("language", Json::str("clojure"))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    /// Walk the top-level forms of a file, creating definition nodes and import
    /// edges and queuing functions for call scanning.
    fn walk_top<'a>(
        &mut self,
        root: &'a Node,
        file_id: &str,
        ns: &str,
        src: &'a str,
        li: &LineIndex,
        pend: &mut Vec<PendingFn<'a>>,
    ) {
        for list in root.children_of(cst::LIST) {
            let fs = forms(list, src);
            let head = match op_symbol(&fs) {
                Some(h) => h,
                None => continue, // not an operator-headed list
            };
            match head {
                "ns" => self.handle_ns(&fs, file_id, src),
                "defn" | "defn-" | "defmacro" => {
                    self.handle_fn(list, &fs, file_id, ns, src, li, head, pend)
                }
                "def" | "defonce" => self.handle_def(&fs, file_id, ns, li, head),
                "defrecord" | "deftype" | "defprotocol" | "definterface" => {
                    self.handle_type(&fs, file_id, ns, li, head)
                }
                "require" | "use" | "import" => self.handle_import_call(&fs, file_id, src, head),
                _ => {}
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_fn<'a>(
        &mut self,
        list: &'a Node,
        fs: &[El<'a>],
        file_id: &str,
        ns: &str,
        src: &'a str,
        li: &LineIndex,
        head: &str,
        pend: &mut Vec<PendingFn<'a>>,
    ) {
        let (name, start) = match name_after_head(fs) {
            Some(n) => n,
            None => return,
        };
        let line = li.line_col(start).line;
        let qual = qual_name(ns, name);
        let id = format!("fn::{qual}#{line}");
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("clojure")),
            ("def_form", Json::str(head.to_string())),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(list.span.start as u64)),
            ("span_end", Json::U64(list.span.end as u64)),
        ];
        if head == "defn-" {
            props.push(("private", Json::Bool(true)));
        }
        if head == "defmacro" {
            props.push(("is_macro", Json::Bool(true)));
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, name.to_string(), props);
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.fn_by_name
            .entry(name.to_string())
            .or_default()
            .push(id.clone());
        pend.push(PendingFn {
            id,
            node: list,
            src,
        });
    }

    fn handle_def(&mut self, fs: &[El<'_>], file_id: &str, ns: &str, li: &LineIndex, head: &str) {
        let (name, start) = match name_after_head(fs) {
            Some(n) => n,
            None => return,
        };
        let line = li.line_col(start).line;
        let qual = qual_name(ns, name);
        let id = format!("const::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            name.to_string(),
            vec![
                ("qualified_name", Json::str(qual)),
                ("binding", Json::str(head.to_string())),
                ("language", Json::str("clojure")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
    }

    fn handle_type(&mut self, fs: &[El<'_>], file_id: &str, ns: &str, li: &LineIndex, head: &str) {
        let (name, start) = match name_after_head(fs) {
            Some(n) => n,
            None => return,
        };
        let line = li.line_col(start).line;
        let qual = qual_name(ns, name);
        let id = format!("type::{qual}");
        let type_kind = match head {
            "defrecord" => "record",
            "deftype" => "type",
            "defprotocol" => "protocol",
            _ => "interface",
        };
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.to_string(),
            vec![
                ("type_kind", Json::str(type_kind)),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("clojure")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
    }

    /// `(ns name (:require …) (:use …) (:import …))` — pull import edges from the
    /// reference clauses.
    fn handle_ns(&mut self, fs: &[El<'_>], file_id: &str, src: &str) {
        for el in fs {
            if let El::Grp(g) = el {
                if g.kind != cst::LIST {
                    continue;
                }
                let inner = forms(g, src);
                // The leading element of a `(:require …)` clause is a keyword.
                if let Some(El::Tok { kind, text, .. }) = inner.first() {
                    if *kind == tk::KEYWORD {
                        match *text {
                            ":require" | ":use" => self.handle_libspecs(&inner[1..], file_id, src),
                            ":import" => self.handle_imports(&inner[1..], file_id, src),
                            _ => {}
                        }
                    }
                }
            }
        }
    }

    /// Top-level `(require '[a :as b] …)` / `(use …)` / `(import …)`.
    fn handle_import_call(&mut self, fs: &[El<'_>], file_id: &str, src: &str, head: &str) {
        let rest = if fs.is_empty() { &[][..] } else { &fs[1..] };
        if head == "import" {
            self.handle_imports(rest, file_id, src);
        } else {
            self.handle_libspecs(rest, file_id, src);
        }
    }

    /// Each libspec names a namespace: a vector/list `[ns …]` (first symbol) or a
    /// bare symbol `ns`.
    fn handle_libspecs(&mut self, specs: &[El<'_>], file_id: &str, src: &str) {
        for el in specs {
            let ns = match el {
                El::Grp(g) => first_symbol(&forms(g, src)).map(|s| s.to_string()),
                El::Tok { kind, text, .. } if *kind == tk::SYMBOL => Some(text.to_string()),
                _ => None,
            };
            if let Some(ns) = ns {
                self.emit_import(file_id, &ns);
            }
        }
    }

    /// `:import` clauses: `(java.util Date List)` (package + classes) or a bare
    /// fully-qualified `java.util.Date`. We record the package/namespace as the
    /// imported path.
    fn handle_imports(&mut self, specs: &[El<'_>], file_id: &str, src: &str) {
        for el in specs {
            match el {
                El::Grp(g) => {
                    if let Some(pkg) = first_symbol(&forms(g, src)) {
                        self.emit_import(file_id, pkg);
                    }
                }
                El::Tok { kind, text, .. } if *kind == tk::SYMBOL => {
                    self.emit_import(file_id, text);
                }
                _ => {}
            }
        }
    }

    /// Emit one `IMPORTS` edge for a referenced namespace/package, plus the
    /// `ExternalDependency`/`DEPENDS_ON` pair when its root is not project-local.
    fn emit_import(&mut self, file_id: &str, ns: &str) {
        if ns.is_empty() {
            return;
        }
        let root = ns.split('.').next().unwrap_or(ns).to_string();
        let internal = self.local_ns.contains(ns) || self.local_roots.contains(&root);
        if internal {
            let mod_id = format!("mod::{ns}");
            self.g.upsert_node(
                mod_id.clone(),
                ont::MODULE,
                ns.to_string(),
                vec![("language", Json::str("clojure"))],
            );
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                mod_id,
                vec![
                    ("path", Json::str(ns.to_string())),
                    ("external", Json::Bool(false)),
                ],
            );
        } else {
            let dep_id = format!("ext::{root}");
            self.g.upsert_node(
                dep_id.clone(),
                ont::EXTERNAL_DEPENDENCY,
                root,
                vec![
                    ("external", Json::Bool(true)),
                    ("source", Json::str("require")),
                ],
            );
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                dep_id.clone(),
                vec![
                    ("path", Json::str(ns.to_string())),
                    ("external", Json::Bool(true)),
                ],
            );
            self.g
                .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
        }
    }

    /// Emit a `CALLS` edge for a head symbol, but only when it resolves to a
    /// project function. Unique → resolved edge; several same-named defs →
    /// ambiguous edge with candidates; unknown → no edge (honest gap).
    fn emit_call(&mut self, caller_id: &str, raw_name: &str) {
        let name = simple_name(raw_name);
        let ids = match self.fn_by_name.get(name) {
            Some(ids) if !ids.is_empty() => ids.clone(),
            _ => return,
        };
        if ids.len() == 1 {
            self.g.add_edge(
                caller_id,
                edge::CALLS,
                ids[0].clone(),
                vec![
                    ("callee", Json::str(name.to_string())),
                    ("resolved", Json::Bool(true)),
                    ("candidate_count", Json::U64(1)),
                ],
            );
        } else {
            let target = format!("unresolved::{name}");
            if !self.g.has_node(&target) {
                self.g.upsert_node(
                    target.clone(),
                    ont::UNRESOLVED,
                    name.to_string(),
                    vec![
                        ("unresolved", Json::Bool(true)),
                        ("role", Json::str("call")),
                    ],
                );
            }
            self.g.add_edge(
                caller_id,
                edge::CALLS,
                target,
                vec![
                    ("callee", Json::str(name.to_string())),
                    ("resolved", Json::Bool(false)),
                    ("ambiguous", Json::Bool(true)),
                    ("candidate_count", Json::U64(ids.len() as u64)),
                    (
                        "candidates",
                        Json::Array(ids.into_iter().map(Json::Str).collect()),
                    ),
                ],
            );
        }
    }
}

// --- element model over the lossless tree -----------------------------------

/// A significant child of a form: a flat token or a nested delimiter group.
/// Trivia, delimiter tokens, and reader-macro tokens are filtered out.
enum El<'a> {
    Tok {
        kind: &'static str,
        text: &'a str,
        start: u32,
    },
    Grp(&'a Node),
}

/// True for the structural/reader tokens that are not themselves *forms*: the
/// delimiter tokens and the reader macros (`'`, `` ` ``, `~`, `~@`, `#`, `@`, `^`).
fn is_structural(kind: &str) -> bool {
    is_open_delim(kind) || is_close_delim(kind) || kind == tk::READER
}

/// The significant elements of a node: non-trivia tokens that are not structural,
/// plus child group nodes, in source order.
fn forms<'a>(node: &'a Node, src: &'a str) -> Vec<El<'a>> {
    let mut v = Vec::new();
    for c in &node.children {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) if is_structural(t.kind) => {}
            Child::Token(t) => v.push(El::Tok {
                kind: t.kind,
                text: t.span.text(src),
                start: t.span.start,
            }),
            Child::Node(n) => v.push(El::Grp(n)),
        }
    }
    v
}

/// The operator symbol of a list: its *first* element, only if that element is a
/// bare symbol. `None` if the list leads with a group, keyword, or other atom.
fn op_symbol<'a>(fs: &[El<'a>]) -> Option<&'a str> {
    match fs.first() {
        Some(El::Tok { kind, text, .. }) if *kind == tk::SYMBOL => Some(*text),
        _ => None,
    }
}

/// The first symbol token anywhere in `fs` (used to read a namespace out of a
/// libspec vector or import group).
fn first_symbol<'a>(fs: &[El<'a>]) -> Option<&'a str> {
    fs.iter().find_map(|e| match e {
        El::Tok { kind, text, .. } if *kind == tk::SYMBOL => Some(*text),
        _ => None,
    })
}

/// The defined name: the first symbol *after* the head operator, skipping metadata
/// keywords/maps (`^:private`, `^{…}`). Returns the name text and its byte offset.
fn name_after_head<'a>(fs: &[El<'a>]) -> Option<(&'a str, u32)> {
    fs.iter().skip(1).find_map(|e| match e {
        El::Tok { kind, text, start } if *kind == tk::SYMBOL => Some((*text, *start)),
        _ => None,
    })
}

// --- call detection over the lossless token tree ----------------------------

/// Collect candidate call names: the head symbol of every list reachable from
/// `node` (recursively, through vectors and maps too). The enclosing definition's
/// own head is *not* visited because callers pass the def list's children, not the
/// def list itself.
fn scan_calls(node: &Node, src: &str, out: &mut Vec<String>) {
    if node.kind == cst::LIST {
        let fs = forms(node, src);
        if let Some(head) = op_symbol(&fs) {
            out.push(head.to_string());
        }
    }
    for child in node.child_nodes() {
        scan_calls(child, src, out);
    }
}

// --- pure helpers -----------------------------------------------------------

/// `ns/name` — the qualified name and basis for node ids. A file with no namespace
/// yields a bare name.
fn qual_name(ns: &str, name: &str) -> String {
    if ns.is_empty() {
        name.to_string()
    } else {
        format!("{ns}/{name}")
    }
}

/// The unqualified portion of a possibly namespace-qualified symbol (`str/join` →
/// `join`); falls back to the raw text for oddities like the bare `/` symbol.
fn simple_name(raw: &str) -> &str {
    match raw.rsplit('/').next() {
        Some(s) if !s.is_empty() => s,
        _ => raw,
    }
}

/// The namespace declared by a file's `ns` form, if any.
fn ns_of_file(root: &Node, src: &str) -> Option<String> {
    for list in root.children_of(cst::LIST) {
        let fs = forms(list, src);
        if op_symbol(&fs) == Some("ns") {
            return name_after_head(&fs).map(|(n, _)| n.to_string());
        }
    }
    None
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
    use crate::lang::clojure::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("core.clj", src);
        let file = SourceFile {
            rel_path: "core.clj".to_string(),
            module_path: vec!["core".to_string()],
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    fn call_edges(g: &Graph) -> Vec<&crate::graph::GraphEdge> {
        g.edges().filter(|e| e.kind == edge::CALLS).collect()
    }

    #[test]
    fn emits_function_and_module_nodes() {
        let g = graph_for("(ns my.app)\n(defn f [] 1)\n(defn- g [] 2)\n");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "f + g");
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "ns my.app");
        let priv_fn = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "g")
            .expect("g");
        assert_eq!(priv_fn.props.get("private"), Some(&Json::Bool(true)));
    }

    #[test]
    fn def_is_constant_defmacro_is_function() {
        let g = graph_for("(def answer 42)\n(defmacro m [] nil)\n");
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 1);
        let mac = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "m")
            .expect("m");
        assert_eq!(mac.props.get("is_macro"), Some(&Json::Bool(true)));
        assert_eq!(mac.props.get("def_form"), Some(&Json::str("defmacro")));
    }

    #[test]
    fn defrecord_is_a_type() {
        let g = graph_for("(defrecord Point [x y])\n");
        let ty = g.nodes().find(|n| n.kind == ont::TYPE).expect("a Type");
        assert_eq!(ty.name, "Point");
        assert_eq!(ty.props.get("type_kind"), Some(&Json::str("record")));
        assert_eq!(ty.props.get("language"), Some(&Json::str("clojure")));
    }

    #[test]
    fn metadata_before_name_is_skipped() {
        let g = graph_for("(def ^:private x 1)\n");
        let c = g.nodes().find(|n| n.kind == ont::CONSTANT).expect("const");
        assert_eq!(c.name, "x");
    }

    #[test]
    fn require_internal_and_external() {
        let g = graph_for(
            "(ns demo.core\n  (:require [demo.util :as u]\n            [clojure.string :as s]))\n",
        );
        // demo.* is project-local; clojure.* is external.
        assert!(g.has_node("ext::clojure"), "clojure is external");
        assert!(
            g.edges()
                .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::clojure"),
            "DEPENDS_ON external"
        );
        assert!(
            g.edges().any(|e| e.kind == edge::IMPORTS),
            "an IMPORTS edge exists"
        );
    }

    #[test]
    fn resolves_unique_local_call() {
        let g = graph_for("(defn helper [] 1)\n(defn run [] (helper))\n");
        let calls = call_edges(&g);
        let helper = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("helper")))
            .expect("a call to helper");
        assert!(helper.to.starts_with("fn::"));
        assert_eq!(helper.props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn unknown_and_special_forms_are_not_calls() {
        // `println` is unknown (a dependency fn), `let`/`if` are special forms;
        // none should produce an edge — we prefer fewer, correct edges.
        let g = graph_for("(defn run [] (let [x 1] (if x (println x))))\n");
        assert_eq!(call_edges(&g).len(), 0, "no fabricated call edges");
    }

    #[test]
    fn output_is_deterministic() {
        let src =
            "(ns demo.core (:require [clojure.string :as s]))\n(defn a [] (b))\n(defn b [] 1)\n";
        let x = graph_for(src).to_jsonl();
        let y = graph_for(src).to_jsonl();
        assert_eq!(x, y, "graph output must be byte-identical across runs");
    }
}
