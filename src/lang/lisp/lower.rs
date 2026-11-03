//! Lower the Lisp CST into the canonical graph.
//!
//! Conservative, honest mappings (see the IR Atlas). A *form* is a list whose
//! first symbol names the operator. The mapping inspects that head symbol:
//!
//!   - `(defun|defmethod|defmacro|defgeneric|defsubst NAME …)` and the `cl-`
//!     prefixed variants                          → `Function`
//!   - Scheme `(define (NAME …) …)`               → `Function`
//!   - Scheme `(define NAME (lambda …))`          → `Function`
//!   - `(defclass|defstruct|deftype NAME …)` and `(define-record-type NAME …)`,
//!     plus `cl-defstruct`                         → `Type`
//!   - `(defvar|defparameter|defconstant|defconst|defcustom NAME …)`             → `Constant`
//!   - `(define NAME <non-lambda>)`               → `Constant`
//!   - `(require|use-package|load|import …)`      → `IMPORTS` (+ `ExternalDependency`
//!     / `DEPENDS_ON` for paths the project does not own)
//!   - the head symbol of any other list inside a function body that resolves to a
//!     project-defined function → `CALLS`
//!
//! Principles carried over from the Rust/Python/Clojure lowerings:
//!   1. **No fabricated targets.** A `CALLS` edge is emitted only when the head
//!      symbol resolves to a project function. A unique match → a resolved edge; a
//!      name shared by several defs → an ambiguous edge carrying the full
//!      `candidates` set; an unknown head (a special form, a macro, a host call, or
//!      a dependency function we cannot see in the airgap) → *no edge*. We prefer
//!      fewer, correct edges over guesses.
//!   2. **Everything comes from real tokens.** Names, paths, and call heads are
//!      read off the lossless tree, never invented.
//!
//! Honest coverage gaps (documented, not hidden):
//!   - Calls resolve by simple (package-stripped) name only — Lisp has no static
//!     type inference here — so `pkg:f` resolves to any project `f`.
//!   - Top-level (non-function) call sites are not attributed (no enclosing
//!     `Function` owns the edge).
//!   - A definition's own lambda-list is skipped when scanning for calls (so
//!     `(defun f (x) …)` does not call `x`), but a *nested* `let`/`flet` binding
//!     list could still surface a spurious call if a local name collides with a
//!     top-level function — rare, and only ever an edge to a real project def.
//!   - `defpackage`/`in-package` (CL packages), Scheme libraries, and Elisp
//!     `provide`/feature scoping are not modelled; scope is directory-derived from
//!     the file's module path. `define-syntax` macros are not specially handled.
//!   - A `#;` datum-comment marker is lexer trivia, so the datum it would discard
//!     is still treated as live.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::lisp::lexer::kind as tk;
use crate::lang::lisp::lexer::{is_close_delim, is_open_delim};
use crate::lang::lisp::parser::node as cst;

/// Lower a whole project's worth of Lisp files into a graph. `manifest_deps` is
/// unused (the pipeline's manifest reader is Cargo-only); dependencies are
/// discovered from `require`/`use-package`/`load`/`import` instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    // Each file's scope is its directory-derived module path (Lisp has no portable
    // filename→namespace convention; packages/libraries are a documented punt).
    let file_ns: Vec<String> = files.iter().map(|f| f.module_path.join(".")).collect();

    // Project-local scopes and their root segments. An imported path whose root is
    // one of these is treated as intra-project, not an external dependency.
    let mut local_ns: BTreeSet<String> = BTreeSet::new();
    let mut local_roots: BTreeSet<String> = BTreeSet::new();
    local_roots.insert(package.to_string());
    for (idx, ns) in file_ns.iter().enumerate() {
        if !ns.is_empty() {
            local_ns.insert(ns.clone());
            if let Some(root) = ns.split('.').next() {
                local_roots.insert(root.to_string());
            }
        }
        for seg in &files[idx].module_path {
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
        vec![("ecosystem", Json::str("lisp"))],
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
                ("language", Json::str("lisp")),
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
        scan_body(pf.node, pf.src, pf.skip_groups, &mut calls);
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

/// A function whose body is scanned for call sites in pass C. `skip_groups` is the
/// number of leading child *groups* (the lambda-list / signature) to skip so a
/// definition does not appear to call its own parameters.
struct PendingFn<'a> {
    id: String,
    node: &'a Node,
    src: &'a str,
    skip_groups: usize,
}

impl Lowerer {
    fn pkg_id(&self) -> String {
        format!("pkg::{}", self.package)
    }

    /// Ensure the `Package → mod::a → mod::a.b …` chain exists for a dotted scope
    /// and return the leaf module id (or the package id for an empty scope).
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
                vec![("language", Json::str("lisp"))],
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
                "defun" | "defmethod" | "defgeneric" | "defmacro" | "defsubst" | "cl-defun"
                | "cl-defmethod" | "cl-defgeneric" | "cl-defmacro" | "cl-defsubst" => {
                    self.handle_named_fn(list, &fs, file_id, ns, src, li, head, pend)
                }
                "define" => self.handle_define(list, &fs, file_id, ns, src, li, pend),
                "defclass" | "defstruct" | "deftype" | "cl-defstruct" | "define-record-type" => {
                    self.handle_type(&fs, file_id, ns, li, head)
                }
                "defvar" | "defparameter" | "defconstant" | "defconst" | "defcustom"
                | "defvar-local" => self.handle_def(&fs, file_id, ns, li, head),
                "require" | "use-package" | "load" | "import" => {
                    self.handle_import(&fs, file_id, src, head)
                }
                _ => {}
            }
        }
    }

    /// `(defun NAME (lambda-list) body…)` and friends. The name is the first symbol
    /// after the head; the lambda-list is the first child group, which is skipped
    /// when scanning the body for calls.
    #[allow(clippy::too_many_arguments)]
    fn handle_named_fn<'a>(
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
        let is_macro = head == "defmacro" || head == "cl-defmacro";
        self.emit_fn(
            list, name, start, ns, file_id, src, li, head, is_macro, 1, pend,
        );
    }

    /// Scheme `define`. `(define (f x) …)` and `(define f (lambda …))` are
    /// functions; `(define x <non-lambda>)` is a constant.
    #[allow(clippy::too_many_arguments)]
    fn handle_define<'a>(
        &mut self,
        list: &'a Node,
        fs: &[El<'a>],
        file_id: &str,
        ns: &str,
        src: &'a str,
        li: &LineIndex,
        pend: &mut Vec<PendingFn<'a>>,
    ) {
        match fs.get(1) {
            // (define (f args) body…) — name is the head of the signature group;
            // skip that one group when scanning the body for calls.
            Some(El::Grp(g)) => {
                if let Some((name, start)) = first_symbol_pos(&forms(g, src)) {
                    self.emit_fn(
                        list, name, start, ns, file_id, src, li, "define", false, 1, pend,
                    );
                }
            }
            // (define name value)
            Some(El::Tok { kind, text, start }) if *kind == tk::SYMBOL => {
                let value_is_lambda = matches!(
                    fs.get(2),
                    Some(El::Grp(g)) if op_symbol(&forms(g, src)) == Some("lambda")
                        || op_symbol(&forms(g, src)) == Some("λ")
                );
                if value_is_lambda {
                    // Scan into the lambda (skip_groups=0): its own arglist heads are
                    // parameters, which resolution filters out.
                    self.emit_fn(
                        list, text, *start, ns, file_id, src, li, "define", false, 0, pend,
                    );
                } else {
                    self.emit_constant(text, *start, ns, file_id, li, "define");
                }
            }
            _ => {}
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_fn<'a>(
        &mut self,
        list: &'a Node,
        name: &str,
        start: u32,
        ns: &str,
        file_id: &str,
        src: &'a str,
        li: &LineIndex,
        head: &str,
        is_macro: bool,
        skip_groups: usize,
        pend: &mut Vec<PendingFn<'a>>,
    ) {
        let line = li.line_col(start).line;
        let qual = qual_name(ns, name);
        let id = format!("fn::{qual}#{line}");
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("lisp")),
            ("def_form", Json::str(head.to_string())),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(list.span.start as u64)),
            ("span_end", Json::U64(list.span.end as u64)),
        ];
        if is_macro {
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
            skip_groups,
        });
    }

    fn handle_def(&mut self, fs: &[El<'_>], file_id: &str, ns: &str, li: &LineIndex, head: &str) {
        let (name, start) = match name_after_head(fs) {
            Some(n) => n,
            None => return,
        };
        self.emit_constant(name, start, ns, file_id, li, head);
    }

    fn emit_constant(
        &mut self,
        name: &str,
        start: u32,
        ns: &str,
        file_id: &str,
        li: &LineIndex,
        head: &str,
    ) {
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
                ("language", Json::str("lisp")),
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
            "defclass" => "class",
            "defstruct" | "cl-defstruct" => "struct",
            "deftype" => "type",
            "define-record-type" => "record",
            _ => "type",
        };
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.to_string(),
            vec![
                ("type_kind", Json::str(type_kind)),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("lisp")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
    }

    /// `(require 'feature)` / `(use-package foo)` / `(load "file")` /
    /// `(import (scheme base))` — pull import edges from the referenced names.
    fn handle_import(&mut self, fs: &[El<'_>], file_id: &str, src: &str, head: &str) {
        for el in fs.iter().skip(1) {
            let name = match el {
                El::Tok { kind, text, .. } if *kind == tk::SYMBOL => Some((*text).to_string()),
                El::Tok { kind, text, .. } if *kind == tk::KEYWORD => {
                    Some(text.trim_start_matches(':').to_string())
                }
                El::Tok { kind, text, .. } if *kind == tk::STRING => {
                    Some(text.trim_matches('"').to_string())
                }
                El::Grp(g) => first_symbol(&forms(g, src)).map(|s| s.to_string()),
                _ => None,
            };
            if let Some(name) = name {
                self.emit_import(file_id, &name, head);
            }
        }
    }

    /// Emit one `IMPORTS` edge for a referenced path, plus the
    /// `ExternalDependency`/`DEPENDS_ON` pair when its root is not project-local.
    fn emit_import(&mut self, file_id: &str, path: &str, source: &str) {
        if path.is_empty() {
            return;
        }
        // Split on `.` (Scheme-ish), `/` (paths), and `:` (CL package qualifier).
        let root = path
            .split(['.', '/', ':'])
            .find(|s| !s.is_empty())
            .unwrap_or(path)
            .to_string();
        let internal = self.local_ns.contains(path) || self.local_roots.contains(&root);
        if internal {
            let mod_id = format!("mod::{path}");
            self.g.upsert_node(
                mod_id.clone(),
                ont::MODULE,
                path.to_string(),
                vec![("language", Json::str("lisp"))],
            );
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                mod_id,
                vec![
                    ("path", Json::str(path.to_string())),
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
                    ("source", Json::str(source.to_string())),
                ],
            );
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                dep_id.clone(),
                vec![
                    ("path", Json::str(path.to_string())),
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
/// delimiter tokens and the reader macros (`'`, `` ` ``, `,`, `,@`, `#`, `#'`).
fn is_structural(kind: &str) -> bool {
    is_open_delim(kind) || is_close_delim(kind) || kind == tk::READER
}

/// The significant elements of a node: non-trivia tokens that are not structural,
/// plus child group nodes, in source order. Borrows text from `src`.
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

/// The first symbol token anywhere in `fs`.
fn first_symbol<'a>(fs: &[El<'a>]) -> Option<&'a str> {
    fs.iter().find_map(|e| match e {
        El::Tok { kind, text, .. } if *kind == tk::SYMBOL => Some(*text),
        _ => None,
    })
}

/// The first symbol token and its byte offset.
fn first_symbol_pos<'a>(fs: &[El<'a>]) -> Option<(&'a str, u32)> {
    fs.iter().find_map(|e| match e {
        El::Tok { kind, text, start } if *kind == tk::SYMBOL => Some((*text, *start)),
        _ => None,
    })
}

/// The defined name: the first symbol *after* the head operator, skipping any
/// intervening keyword qualifiers (`defmethod foo :around`). Returns the name text
/// and its byte offset.
fn name_after_head<'a>(fs: &[El<'a>]) -> Option<(&'a str, u32)> {
    fs.iter().skip(1).find_map(|e| match e {
        El::Tok { kind, text, start } if *kind == tk::SYMBOL => Some((*text, *start)),
        _ => None,
    })
}

// --- call detection over the lossless token tree ----------------------------

/// Collect call names from a definition's body: the head symbol of every list,
/// skipping the first `skip_groups` child groups of the definition list (its
/// lambda-list / signature, whose head would otherwise look like a call).
fn scan_body(def_list: &Node, src: &str, skip_groups: usize, out: &mut Vec<String>) {
    let mut skipped = 0usize;
    for child in def_list.child_nodes() {
        if skipped < skip_groups {
            skipped += 1;
            continue; // the lambda-list / signature group
        }
        scan_calls(child, src, out);
    }
}

/// Collect candidate call names: the head symbol of every list reachable from
/// `node` (recursively, through bracketed and brace groups too).
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

/// `ns.name` — the qualified name and basis for node ids. A file with no scope
/// yields a bare name.
fn qual_name(ns: &str, name: &str) -> String {
    if ns.is_empty() {
        name.to_string()
    } else {
        format!("{ns}.{name}")
    }
}

/// The unqualified portion of a possibly package-qualified symbol (`cl:remove` →
/// `remove`, `pkg::sym` → `sym`); falls back to the raw text otherwise.
fn simple_name(raw: &str) -> &str {
    match raw.rsplit(':').next() {
        Some(s) if !s.is_empty() => s,
        _ => raw,
    }
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
    use crate::lang::lisp::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("core.lisp", src);
        let file = SourceFile {
            rel_path: "core.lisp".to_string(),
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
    fn defun_and_defmacro_are_functions() {
        let g = graph_for("(defun f (x) x)\n(defmacro m (x) x)\n");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "f + m");
        let mac = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "m")
            .expect("m");
        assert_eq!(mac.props.get("is_macro"), Some(&Json::Bool(true)));
        assert_eq!(mac.props.get("def_form"), Some(&Json::str("defmacro")));
    }

    #[test]
    fn defvar_is_constant() {
        let g = graph_for("(defvar *answer* 42)\n(defparameter *x* 1)\n");
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 2);
    }

    #[test]
    fn defclass_and_defstruct_are_types() {
        let g = graph_for("(defclass point () ())\n(defstruct rect w h)\n");
        let class = g
            .nodes()
            .find(|n| n.kind == ont::TYPE && n.name == "point")
            .expect("point");
        assert_eq!(class.props.get("type_kind"), Some(&Json::str("class")));
        let st = g
            .nodes()
            .find(|n| n.kind == ont::TYPE && n.name == "rect")
            .expect("rect");
        assert_eq!(st.props.get("type_kind"), Some(&Json::str("struct")));
    }

    #[test]
    fn scheme_define_function_and_constant() {
        let g = graph_for("(define (square x) (* x x))\n(define pi 3.14)\n");
        assert!(
            g.nodes()
                .any(|n| n.kind == ont::FUNCTION && n.name == "square"),
            "square is a function"
        );
        assert!(
            g.nodes().any(|n| n.kind == ont::CONSTANT && n.name == "pi"),
            "pi is a constant"
        );
    }

    #[test]
    fn scheme_define_lambda_is_function() {
        let g = graph_for("(define cube (lambda (x) (* x x x)))\n");
        assert!(
            g.nodes()
                .any(|n| n.kind == ont::FUNCTION && n.name == "cube"),
            "cube bound to a lambda is a function"
        );
    }

    #[test]
    fn define_record_type_is_a_type() {
        let g = graph_for("(define-record-type point (make-point x y) point? (x px) (y py))\n");
        let ty = g
            .nodes()
            .find(|n| n.kind == ont::TYPE && n.name == "point")
            .expect("a Type");
        assert_eq!(ty.props.get("type_kind"), Some(&Json::str("record")));
    }

    #[test]
    fn require_and_use_package_are_imports() {
        let g = graph_for("(require 'cl-lib)\n(use-package 'dash)\n");
        assert!(g.has_node("ext::cl-lib"), "cl-lib external dep");
        assert!(
            g.edges().any(|e| e.kind == edge::IMPORTS),
            "an IMPORTS edge exists"
        );
        assert!(
            g.edges()
                .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::cl-lib"),
            "DEPENDS_ON external"
        );
    }

    #[test]
    fn resolves_unique_local_call() {
        let g = graph_for("(defun helper () 1)\n(defun run () (helper))\n");
        let calls = call_edges(&g);
        let helper = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("helper")))
            .expect("a call to helper");
        assert!(helper.to.starts_with("fn::"));
        assert_eq!(helper.props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn parameters_are_not_self_calls() {
        // `x` is the parameter; the body calls nothing project-local. The
        // lambda-list must not be scanned as a call to a same-named def.
        let g = graph_for("(defun x () 1)\n(defun f (x) (+ x 1))\n");
        // No CALLS edge to `x` from `f` despite the arglist mentioning `x`.
        assert!(
            !call_edges(&g)
                .iter()
                .any(|e| e.props.get("callee") == Some(&Json::str("x"))),
            "the lambda-list parameter must not be treated as a call"
        );
    }

    #[test]
    fn unknown_and_special_forms_are_not_calls() {
        // `format`/`+` are unknown (host/dep), `let`/`if` are special forms;
        // none should produce an edge — we prefer fewer, correct edges.
        let g = graph_for("(defun run () (let ((x 1)) (if x (format nil \"~a\" x))))\n");
        assert_eq!(call_edges(&g).len(), 0, "no fabricated call edges");
    }

    #[test]
    fn output_is_deterministic() {
        let src = "(require 'dash)\n(defun a () (b))\n(defun b () 1)\n";
        let x = graph_for(src).to_jsonl();
        let y = graph_for(src).to_jsonl();
        assert_eq!(x, y, "graph output must be byte-identical across runs");
    }
}
