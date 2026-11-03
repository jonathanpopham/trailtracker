//! Lower the C# CST into the canonical graph.
//!
//! This mirrors the Rust and Python lowerings ([`crate::ir::lower`],
//! [`crate::lang::python::lower`]) — same conservative principles, same shared
//! ontology — adapted to C#'s surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to
//!    a concrete project definition only when a scope level yields exactly one
//!    candidate; several candidates become an ambiguous edge carrying the full
//!    `candidates` set; none resolves to an explicit `UnresolvedSymbol`.
//! 2. **Everything comes from real tokens.** Calls, base lists, usings, and type
//!    uses are read off the lossless tree, never guessed.
//!
//! Honest mappings (see the IR Atlas):
//!   `class`/`struct`/`interface`/`enum`/`record`/`delegate` → `Type` with an apt
//!   `type_kind`; method/constructor → `Function` (a method gets `HAS_METHOD`
//!   from its enclosing type); `namespace` → `Module`; `using` → `IMPORTS` (plus
//!   `ExternalDependency`/`DEPENDS_ON` for non-project roots); base list →
//!   `IMPLEMENTS` for interfaces and `EXTENDS` for base classes.
//!
//! Mapping caveat (honest): C# fields and properties have no dedicated IR node
//! kind, so they lower to `Constant` with a `binding` property (`const`, `field`,
//! `event`, `property`). This is the closest existing kind ("a value binding");
//! a dedicated `Field`/`Property` kind would be a more faithful IR extension. We
//! do not fabricate an edge kind for it.
//!
//! **Entry points.** A classic `static Main` method is marked with
//! `entrypoint=true`, and modern top-level statements (C# 9 top-level programs,
//! including minimal-API hosting: `var builder = WebApplication.CreateBuilder(args);
//! … app.Run();`) are detected per file. Either way the file gains a synthetic
//! `main`-named `Function` marker (`synthetic=true`, `entrypoint_kind`), mirroring
//! the compiler-generated `<Main>$`, so downstream consumers that look for a
//! `main` function (e.g. the architecture brief) see the executable. The marker is
//! kept out of the call-resolution symbol tables — it is never a fabricated call
//! target — and for top-level statements the real statements are scanned as its
//! body, so its outgoing `CALLS` edges come from real tokens.
//!
//! Resolution uses a deterministic **scope ladder** (most specific first): for a
//! `this`/`base` method call, the enclosing type's methods; for a bare call, the
//! enclosing type's methods then any project function of that name; for any other
//! receiver, project methods of that name (ambiguity preserved). Generic-argument
//! call sites (`Foo<T>(x)`) are not matched, staying conservative rather than
//! guessing across the C# `<` ambiguity.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::csharp::lexer::{is_keyword, kind as tk};
use crate::lang::csharp::parser::node as cst;
use crate::lang::frontend::SourceFile;

const LANG: &str = "csharp";

/// Lower a whole project's worth of C# files into a graph. `manifest_deps` is
/// unused for C# (the pipeline's manifest reader is Cargo-only); dependencies are
/// discovered from `using` directives instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], manifest_deps: &[String]) -> Graph {
    lower_impl(package, files, manifest_deps, false)
}

/// [`lower`] plus the opt-in CPG overlay (ADR-0003): after the base facts are
/// emitted, each method body additionally yields `Statement` nodes and
/// intra-method `FLOWS_TO`/`DATA_DEP` edges. The base sub-graph is
/// byte-identical to [`lower`]'s — the overlay is strictly additive.
pub fn lower_with_cpg(package: &str, files: &[SourceFile<'_>], manifest_deps: &[String]) -> Graph {
    lower_impl(package, files, manifest_deps, true)
}

fn lower_impl(
    package: &str,
    files: &[SourceFile<'_>],
    _manifest_deps: &[String],
    cpg: bool,
) -> Graph {
    // Project-local namespace roots: the package plus the first segment of every
    // declared namespace. A `using` whose first segment is one of these is an
    // intra-project import, not an external dependency. Conservative: prefer
    // under-reporting externals to fabricating one for a namespace we own.
    let mut local_roots: BTreeSet<String> = BTreeSet::new();
    local_roots.insert(package.to_string());
    for f in files {
        collect_namespace_roots(f.root, f.source, &mut local_roots);
    }

    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        local_roots,
        fn_by_name: BTreeMap::new(),
        method_by_name: BTreeMap::new(),
        method_by_type: BTreeMap::new(),
        type_by_name: BTreeMap::new(),
        type_kind_by_id: BTreeMap::new(),
        static_main_by_file: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("dotnet"))],
    );

    // Pass B: create definition nodes + structural edges, build symbol tables.
    // Inheritance and call/type resolution are deferred to pass C so a base type
    // or callee defined later in the project still resolves.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_extends: Vec<PendingExtends> = Vec::new();
    let mut pend_type_uses: Vec<(String, &Node, &str)> = Vec::new();
    for f in files {
        let li = LineIndex::new(f.source);
        let file_id = format!("file::{}", f.rel_path);
        lo.g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str(LANG)),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(lo.pkg_id(), edge::CONTAINS, file_id.clone(), vec![]);
        lo.walk_items(
            f.root,
            &file_id,
            "",
            None,
            &[],
            None,
            f.source,
            &li,
            &mut pend_fns,
            &mut pend_extends,
            &mut pend_type_uses,
        );

        // Entry points. Modern .NET has no `static Main` in source: `Program.cs`
        // holds top-level statements (the compiler synthesizes `<Main>$`). Detect
        // both shapes and emit a `main`-named marker so the executable is visible.
        let top_stmts = top_level_statements(f.root, f.source);
        if !top_stmts.is_empty() {
            let first = top_stmts[0];
            let last = top_stmts[top_stmts.len() - 1];
            let line = li.line_col(first.span.start).line;
            let id = lo.emit_entry_main(
                &file_id,
                &f.rel_path,
                "top_level_statements",
                line,
                (first.span.start, last.span.end),
                None,
            );
            // The statements are the entry point's body: scan them for calls in
            // pass C, exactly like a method block.
            for stmt in top_stmts {
                pend_fns.push(PendingFn {
                    id: id.clone(),
                    source: f.source,
                    block: Some(stmt),
                    header: None,
                    owner_type: None,
                });
            }
        } else if let Some(m) = lo.static_main_by_file.get(&file_id).cloned() {
            lo.emit_entry_main(
                &file_id,
                &f.rel_path,
                "static_main",
                m.line,
                (m.span_start, m.span_end),
                Some(m.fn_id),
            );
        }
    }

    // Pass C: resolve calls (scope ladder), type usages, and inheritance against
    // the now-complete symbol tables.
    for pf in &pend_fns {
        if let Some(block) = pf.block {
            let mut calls = Vec::new();
            scan_calls(block, pf.source, &mut calls);
            for call in &calls {
                let res = lo.resolve(call, pf.owner_type.as_deref());
                lo.emit_call(&pf.id, call, res);
            }
        }
        if cpg {
            // Only real method bodies (`Block` nodes, incl. `=> expr` bodies)
            // get an overlay. Top-level-statement entry markers share one fn
            // id across several `Statement` blocks — their statement numbering
            // would collide, so they are excluded (documented in ADR-0003).
            if let Some(block) = pf.block {
                if block.kind == cst::BLOCK {
                    crate::lang::csharp::cpg::emit_method_cpg(
                        &mut lo.g, &pf.id, block, pf.header, pf.source,
                    );
                }
            }
        }
    }
    for entry in &pend_type_uses {
        lo.emit_type_uses(&entry.0, entry.1, entry.2);
    }
    for pe in &pend_extends {
        lo.emit_extends(pe);
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    local_roots: BTreeSet<String>,
    /// Simple name → all function node ids (project-wide).
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// Simple name → method node ids only (global method-call level).
    method_by_name: BTreeMap<String, Vec<String>>,
    /// (type_name, method_name) → method ids (receiver level).
    method_by_type: BTreeMap<(String, String), Vec<String>>,
    /// Simple name → type node ids.
    type_by_name: BTreeMap<String, Vec<String>>,
    /// Type node id → its `type_kind` (for base-edge classification).
    type_kind_by_id: BTreeMap<String, &'static str>,
    /// File id → the first `static Main` method seen in that file (classic
    /// entry point), used to emit the file's entry marker after its walk.
    static_main_by_file: BTreeMap<String, StaticMain>,
}

/// A classic `static Main` method observed while walking a file.
#[derive(Clone)]
struct StaticMain {
    fn_id: String,
    line: u32,
    span_start: u32,
    span_end: u32,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    block: Option<&'a Node>,
    /// The member's `Header` node (parameter list), for the CPG overlay.
    header: Option<&'a Node>,
    owner_type: Option<String>,
}

/// A deferred base-type link, resolved into `EXTENDS`/`IMPLEMENTS` in pass C.
struct PendingExtends {
    type_id: String,
    base_name: String,
}

/// The enclosing type while walking, for methods (`HAS_METHOD`, receiver scope).
struct Owner {
    name: String,
    id: String,
}

/// A detected call site over the lossless tree.
struct Call {
    /// The called name (final attribute or bare name).
    name: String,
    /// True for `recv.name(...)` member calls.
    method: bool,
    /// Immediate receiver identifier for member calls (`this`, `base`, a var).
    receiver: Option<String>,
}

enum Outcome {
    One(String),
    Many(Vec<String>),
    None,
}

struct Resolution {
    outcome: Outcome,
    level: &'static str,
}

impl Lowerer {
    fn pkg_id(&self) -> String {
        format!("pkg::{}", self.package)
    }

    /// Ensure the `Package → mod::A → mod::A.B …` chain exists for a dotted
    /// namespace and return the leaf module id (or the package id for the empty,
    /// global namespace).
    fn ensure_module(&mut self, ns_join: &str) -> String {
        let pkg = self.pkg_id();
        if ns_join.is_empty() {
            return pkg;
        }
        let mut parent = pkg;
        let mut acc: Vec<&str> = Vec::new();
        for seg in ns_join.split('.') {
            acc.push(seg);
            let id = format!("mod::{}", acc.join("."));
            self.g.upsert_node(
                id.clone(),
                ont::MODULE,
                seg.to_string(),
                vec![("language", Json::str(LANG))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    /// Walk a container of items (a `SourceFile`, a namespace `ItemBlock`, or a
    /// type `ItemBlock`), creating definition nodes and recursing.
    #[allow(clippy::too_many_arguments)]
    fn walk_items<'a>(
        &mut self,
        container: &'a Node,
        file_id: &str,
        ns_join: &str,
        module_id: Option<&str>,
        scope: &[String],
        owner: Option<&Owner>,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_extends: &mut Vec<PendingExtends>,
        pend_type_uses: &mut Vec<(String, &'a Node, &'a str)>,
    ) {
        for item in container.child_nodes() {
            match item.kind {
                cst::NAMESPACE => self.handle_namespace(
                    item,
                    file_id,
                    ns_join,
                    src,
                    li,
                    pend_fns,
                    pend_extends,
                    pend_type_uses,
                ),
                cst::CLASS
                | cst::STRUCT
                | cst::INTERFACE
                | cst::ENUM
                | cst::RECORD
                | cst::DELEGATE => self.handle_type(
                    item,
                    file_id,
                    ns_join,
                    module_id,
                    scope,
                    src,
                    li,
                    pend_fns,
                    pend_extends,
                    pend_type_uses,
                ),
                cst::METHOD => self.handle_method(
                    item,
                    file_id,
                    ns_join,
                    scope,
                    owner,
                    src,
                    li,
                    pend_fns,
                    pend_type_uses,
                ),
                cst::FIELD | cst::PROPERTY => {
                    self.handle_field(item, file_id, ns_join, scope, src, li, pend_type_uses)
                }
                cst::USING => self.handle_using(item, file_id, src),
                _ => {}
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_namespace<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        ns_join: &str,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_extends: &mut Vec<PendingExtends>,
        pend_type_uses: &mut Vec<(String, &'a Node, &'a str)>,
    ) {
        let name = node_name(item, src).unwrap_or_default();
        let new_ns = join_ns(ns_join, &name);
        let module_id = self.ensure_module(&new_ns);
        if let Some(block) = item.child(cst::ITEM_BLOCK) {
            self.walk_items(
                block,
                file_id,
                &new_ns,
                Some(&module_id),
                &[],
                None,
                src,
                li,
                pend_fns,
                pend_extends,
                pend_type_uses,
            );
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_type<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        ns_join: &str,
        module_id: Option<&str>,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_extends: &mut Vec<PendingExtends>,
        pend_type_uses: &mut Vec<(String, &'a Node, &'a str)>,
    ) {
        // The delegate's name lives in its header (it has no leading-keyword
        // `Name` node); every other type kind has an explicit `Name`.
        let name = match item.kind {
            cst::DELEGATE => item
                .child(cst::HEADER)
                .and_then(|h| member_name(h, src))
                .unwrap_or_else(|| "<anonymous>".to_string()),
            _ => node_name(item, src).unwrap_or_else(|| "<anonymous>".to_string()),
        };
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(ns_join, scope, &name);
        let id = format!("type::{qual}");
        let type_kind = match item.kind {
            cst::CLASS => "class",
            cst::STRUCT => "struct",
            cst::INTERFACE => "interface",
            cst::ENUM => "enum",
            cst::RECORD => "record",
            cst::DELEGATE => "delegate",
            _ => "type",
        };
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str(type_kind)),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str(LANG)),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        if let Some(m) = module_id {
            self.g.add_edge(m, edge::CONTAINS, id.clone(), vec![]);
        }
        self.type_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());
        self.type_kind_by_id.insert(id.clone(), type_kind);

        // Base list (defer EXTENDS/IMPLEMENTS resolution to pass C). Interfaces,
        // classes, structs, and records may all carry one.
        if let Some(header) = item.child(cst::HEADER) {
            for base in base_names(header, src) {
                pend_extends.push(PendingExtends {
                    type_id: id.clone(),
                    base_name: base,
                });
            }
            // Base types and (for delegates) the signature contribute type uses.
            pend_type_uses.push((id.clone(), header, src));
        }

        if let Some(block) = item.child(cst::ITEM_BLOCK) {
            let owner = Owner {
                name: name.clone(),
                id: id.clone(),
            };
            let mut child_scope = scope.to_vec();
            child_scope.push(name);
            self.walk_items(
                block,
                file_id,
                ns_join,
                module_id,
                &child_scope,
                Some(&owner),
                src,
                li,
                pend_fns,
                pend_extends,
                pend_type_uses,
            );
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_method<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        ns_join: &str,
        scope: &[String],
        owner: Option<&Owner>,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_type_uses: &mut Vec<(String, &'a Node, &'a str)>,
    ) {
        let header = item.child(cst::HEADER);
        let name = header
            .and_then(|h| member_name(h, src))
            .unwrap_or_else(|| "<anonymous>".to_string());
        let line = li.line_col(item.span.start).line;
        let qual = qual_name(ns_join, scope, &name);
        let id = format!("fn::{qual}#{line}");
        let block = item.child(cst::BLOCK);
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str(LANG)),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            ("has_body", Json::Bool(block.is_some())),
        ];
        if has_modifier(item, src, "async") {
            props.push(("is_async", Json::Bool(true)));
        }
        let is_static = has_modifier(item, src, "static");
        if is_static {
            props.push(("is_static", Json::Bool(true)));
        }
        // Classic entry point: `static … Main(…)`. Marked here; the file's
        // synthetic `main` marker is emitted once the file walk completes.
        let is_entry_main = is_static && name == "Main";
        if is_entry_main {
            props.push(("entrypoint", Json::Bool(true)));
        }
        if let Some(o) = owner {
            props.push(("receiver_type", Json::str(o.name.clone())));
            props.push(("is_method", Json::Bool(true)));
            if o.name == name {
                props.push(("is_constructor", Json::Bool(true)));
            }
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, name.clone(), props);
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);

        if is_entry_main {
            self.static_main_by_file
                .entry(file_id.to_string())
                .or_insert(StaticMain {
                    fn_id: id.clone(),
                    line,
                    span_start: item.span.start,
                    span_end: item.span.end,
                });
        }

        self.fn_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());
        if let Some(o) = owner {
            self.method_by_name
                .entry(name.clone())
                .or_default()
                .push(id.clone());
            self.method_by_type
                .entry((o.name.clone(), name.clone()))
                .or_default()
                .push(id.clone());
            self.g
                .add_edge(o.id.clone(), edge::HAS_METHOD, id.clone(), vec![]);
        }

        if let Some(h) = header {
            pend_type_uses.push((id.clone(), h, src));
        }
        pend_fns.push(PendingFn {
            id,
            source: src,
            block,
            header,
            owner_type: owner.map(|o| o.name.clone()),
        });
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_field<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        ns_join: &str,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_type_uses: &mut Vec<(String, &'a Node, &'a str)>,
    ) {
        let header = match item.child(cst::HEADER) {
            Some(h) => h,
            None => return,
        };
        let name = match member_name(header, src) {
            Some(n) => n,
            None => return,
        };
        let line = li.line_col(item.span.start).line;
        let qual = qual_name(ns_join, scope, &name);
        let id = format!("const::{qual}");
        let binding = if item.kind == cst::PROPERTY {
            "property"
        } else if has_modifier(item, src, "const") {
            "const"
        } else if header_has_keyword(header, src, "event") {
            "event"
        } else {
            "field"
        };
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            name,
            vec![
                ("binding", Json::str(binding)),
                ("language", Json::str(LANG)),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        pend_type_uses.push((id, header, src));
    }

    /// `using A.B.C;` / `using static A.B;` / `using X = A.B;` — each names a
    /// namespace (or type). Internal namespaces become `IMPORTS` to the module;
    /// external roots become an `ExternalDependency` plus a `DEPENDS_ON` edge.
    fn handle_using(&mut self, item: &Node, file_id: &str, src: &str) {
        let header = match item.child(cst::HEADER) {
            Some(h) => h,
            None => return,
        };
        let toks = top_level_tokens(header, src);
        // `using X = A.B;` — drop the alias and the `=`.
        let body: Vec<Tok> = match toks.iter().position(|t| t.text == "=") {
            Some(p) => toks[p + 1..].to_vec(),
            None => toks,
        };
        let segs: Vec<String> = body
            .iter()
            .filter(|t| t.kind == tk::IDENT && !is_keyword(t.text))
            .map(|t| t.text.to_string())
            .collect();
        if segs.is_empty() {
            return;
        }
        let path_text = segs.join(".");
        self.emit_import_edge(file_id, &segs, &path_text);
    }

    fn emit_import_edge(&mut self, file_id: &str, segs: &[String], path_text: &str) {
        let root = segs[0].clone();
        if self.local_roots.contains(&root) {
            let mod_id = self.ensure_module(&root);
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                mod_id,
                vec![
                    ("path", Json::str(path_text.to_string())),
                    ("external", Json::Bool(false)),
                ],
            );
        } else {
            let dep_id = ext_id(&root);
            self.g.upsert_node(
                dep_id.clone(),
                ont::EXTERNAL_DEPENDENCY,
                root,
                vec![
                    ("external", Json::Bool(true)),
                    ("source", Json::str("using")),
                ],
            );
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                dep_id.clone(),
                vec![
                    ("path", Json::str(path_text.to_string())),
                    ("external", Json::Bool(true)),
                ],
            );
            self.g
                .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
        }
    }

    /// Emit the synthetic `main`-named `Function` marker for an entry-point
    /// file. For top-level statements this mirrors the compiler-generated
    /// `<Main>$`; for a classic `static Main` it aliases the real method
    /// (`alias_of`). The marker is deliberately *not* registered in the
    /// call-resolution symbol tables: it may gain outgoing `CALLS` edges from
    /// real statements, but never becomes a fabricated call target.
    fn emit_entry_main(
        &mut self,
        file_id: &str,
        rel_path: &str,
        kind: &'static str,
        line: u32,
        span: (u32, u32),
        alias_of: Option<String>,
    ) -> String {
        let id = format!("fn::{rel_path}::main");
        let mut props = vec![
            ("entrypoint", Json::Bool(true)),
            ("entrypoint_kind", Json::str(kind)),
            ("synthetic", Json::Bool(true)),
            ("language", Json::str(LANG)),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(span.0 as u64)),
            ("span_end", Json::U64(span.1 as u64)),
        ];
        if let Some(target) = alias_of {
            props.push(("alias_of", Json::str(target)));
        }
        self.g.upsert_node(id.clone(), ont::FUNCTION, "main", props);
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        id
    }

    // --- resolution ---------------------------------------------------------

    fn resolve(&self, call: &Call, owner_type: Option<&str>) -> Resolution {
        if call.method {
            // `this.M()` / `base.M()` → enclosing type's methods.
            if matches!(call.receiver.as_deref(), Some("this") | Some("base")) {
                if let Some(owner) = owner_type {
                    let c = self.methods_of(owner, &call.name);
                    if !c.is_empty() {
                        return mk(c, "receiver");
                    }
                }
            }
            // Other receivers have an unknown static type (no inference): fall back
            // to a global match among *methods* only, preserving ambiguity.
            let c = self.global_methods(&call.name);
            return if c.is_empty() {
                external()
            } else {
                mk(c, "global_method")
            };
        }

        // Bare call: an implicit-`this` method of the enclosing type first.
        if let Some(owner) = owner_type {
            let c = self.methods_of(owner, &call.name);
            if !c.is_empty() {
                return mk(c, "implicit_this");
            }
        }
        // Then any project function of that name (covers constructors via `new`).
        let c = self.global_fns(&call.name);
        if c.is_empty() {
            external()
        } else {
            mk(c, "global")
        }
    }

    fn emit_call(&mut self, caller_id: &str, call: &Call, res: Resolution) {
        let mut props = vec![
            ("callee", Json::str(call.name.clone())),
            ("method", Json::Bool(call.method)),
            ("resolution", Json::str(res.level)),
        ];
        match res.outcome {
            Outcome::One(id) => {
                props.push(("resolved", Json::Bool(true)));
                props.push(("candidate_count", Json::U64(1)));
                self.g.add_edge(caller_id, edge::CALLS, id, props);
            }
            Outcome::Many(ids) => {
                let target = unresolved_id(&call.name);
                self.ensure_unresolved(&target, &call.name, "call");
                props.push(("resolved", Json::Bool(false)));
                props.push(("ambiguous", Json::Bool(true)));
                props.push(("candidate_count", Json::U64(ids.len() as u64)));
                props.push((
                    "candidates",
                    Json::Array(ids.into_iter().map(Json::Str).collect()),
                ));
                self.g.add_edge(caller_id, edge::CALLS, target, props);
            }
            Outcome::None => {
                let target = unresolved_id(&call.name);
                self.ensure_unresolved(&target, &call.name, "call");
                props.push(("resolved", Json::Bool(false)));
                props.push(("candidate_count", Json::U64(0)));
                self.g.add_edge(caller_id, edge::CALLS, target, props);
            }
        }
    }

    /// Resolve a deferred base-type link. An interface base (resolved as such, or
    /// matching the `IPascal` naming convention when external) becomes
    /// `IMPLEMENTS`; a class/struct/record base becomes `EXTENDS`. The target is a
    /// concrete project type when unique, else an explicit `UnresolvedSymbol` (a
    /// framework/third-party base we cannot see in an airgap).
    fn emit_extends(&mut self, pe: &PendingExtends) {
        let (target, is_interface, heuristic) = match self.unique_type(&pe.base_name) {
            Some(id) => {
                let kind = self.type_kind_by_id.get(&id).copied().unwrap_or("class");
                (id, kind == "interface", false)
            }
            None => {
                let id = unresolved_id(&pe.base_name);
                self.ensure_unresolved(&id, &pe.base_name, "base_type");
                (id, looks_like_interface(&pe.base_name), true)
            }
        };
        let edge_kind = if is_interface {
            edge::IMPLEMENTS
        } else {
            edge::EXTENDS
        };
        let mut props = vec![("base_name", Json::str(pe.base_name.clone()))];
        if heuristic {
            props.push(("inference", Json::str("naming_convention")));
        }
        self.g
            .add_edge(pe.type_id.clone(), edge_kind, target, props);
    }

    fn ensure_unresolved(&mut self, id: &str, name: &str, role: &'static str) {
        if !self.g.has_node(id) {
            self.g.upsert_node(
                id.to_string(),
                ont::UNRESOLVED,
                name.to_string(),
                vec![("unresolved", Json::Bool(true)), ("role", Json::str(role))],
            );
        }
    }

    /// Add `USES_TYPE` edges for identifiers in `region` (a signature/base list)
    /// that name a unique project type.
    fn emit_type_uses(&mut self, from_id: &str, region: &Node, src: &str) {
        let mut seen: Vec<String> = Vec::new();
        for n in region.walk() {
            for t in n.tokens() {
                if t.kind != tk::IDENT {
                    continue;
                }
                let name = t.span.text(src);
                if is_keyword(name) {
                    continue;
                }
                if let Some(type_id) = self.unique_type(name) {
                    if type_id != from_id && !seen.contains(&type_id) {
                        seen.push(type_id.clone());
                        self.g.add_edge(
                            from_id,
                            edge::USES_TYPE,
                            type_id,
                            vec![("type_name", Json::str(name.to_string()))],
                        );
                    }
                }
            }
        }
    }

    fn methods_of(&self, type_name: &str, method: &str) -> Vec<String> {
        self.method_by_type
            .get(&(type_name.to_string(), method.to_string()))
            .cloned()
            .unwrap_or_default()
    }

    fn global_fns(&self, name: &str) -> Vec<String> {
        self.fn_by_name.get(name).cloned().unwrap_or_default()
    }

    fn global_methods(&self, name: &str) -> Vec<String> {
        self.method_by_name.get(name).cloned().unwrap_or_default()
    }

    fn unique_type(&self, name: &str) -> Option<String> {
        match self.type_by_name.get(name) {
            Some(ids) if ids.len() == 1 => Some(ids[0].clone()),
            _ => None,
        }
    }
}

fn mk(ids: Vec<String>, level: &'static str) -> Resolution {
    let outcome = if ids.len() == 1 {
        Outcome::One(ids[0].clone())
    } else {
        Outcome::Many(ids)
    };
    Resolution { outcome, level }
}

fn external() -> Resolution {
    Resolution {
        outcome: Outcome::None,
        level: "external",
    }
}

// --- entry-point detection ----------------------------------------------------

/// Canonical .NET hosting idioms, matched against the space-joined significant
/// tokens of a top-level statement. Any one of these is a strong signal that
/// the file is a program entry point (minimal-API / generic-host startup).
const ENTRY_SIGNALS: &[&str] = &[
    "WebApplication . CreateBuilder",
    "app . Run (",
    "app . RunAsync (",
    "Host . CreateDefaultBuilder",
    "CreateHostBuilder",
    "builder . Build ( )",
];

/// Keywords that can open a real executable statement at file scope. `var` and
/// `await` are matched by text so this holds whether or not the lexer treats
/// them as keywords (both are contextual in C#).
const STMT_KEYWORDS: &[&str] = &[
    "await",
    "var",
    "if",
    "for",
    "foreach",
    "while",
    "do",
    "switch",
    "try",
    "return",
    "throw",
    "lock",
    "checked",
    "unchecked",
];

/// The direct `Statement` children of a file root that look like real
/// top-level statements (C# 9 top-level programs). Statements nested inside a
/// namespace or type are never top-level statements, so only the root's direct
/// children are considered.
fn top_level_statements<'a>(root: &'a Node, src: &str) -> Vec<&'a Node> {
    root.child_nodes()
        .filter(|n| n.kind == cst::STATEMENT && statement_is_executable(n, src))
        .collect()
}

/// Heuristic: does a file-scope `Statement` node hold executable top-level
/// code rather than stray/erroneous tokens? True when it opens like a statement
/// (a non-keyword identifier such as `app`/`Console`, or a statement keyword
/// such as `await`/`var`), or when it carries one of the canonical hosting
/// idioms ([`ENTRY_SIGNALS`]). Attribute-only items, stray closers, and other
/// recovery artifacts fail both tests.
fn statement_is_executable(stmt: &Node, src: &str) -> bool {
    // Opening shape: the first significant child decides.
    for ch in &stmt.children {
        match ch {
            Child::Token(t) if t.trivia => continue,
            Child::Token(t) => {
                let text = t.span.text(src);
                if (t.kind == tk::IDENT && !is_keyword(text)) || STMT_KEYWORDS.contains(&text) {
                    return true;
                }
                break;
            }
            Child::Node(_) => break,
        }
    }
    // Fallback: a strong hosting signal anywhere among the real tokens.
    let mut toks: Vec<&str> = Vec::new();
    collect_significant_texts(stmt, src, &mut toks);
    let joined = toks.join(" ");
    ENTRY_SIGNALS.iter().any(|sig| joined.contains(sig))
}

/// Append every significant (non-trivia) token text under `node`, in source
/// order, descending into nested groups.
fn collect_significant_texts<'a>(node: &'a Node, src: &'a str, out: &mut Vec<&'a str>) {
    for ch in &node.children {
        match ch {
            Child::Token(t) if !t.trivia => out.push(t.span.text(src)),
            Child::Token(_) => {}
            Child::Node(n) => collect_significant_texts(n, src, out),
        }
    }
}

// --- pure helpers -----------------------------------------------------------

/// Join a parent namespace and a child namespace name (`""`, `"A.B"` → `"A.B"`).
fn join_ns(parent: &str, child: &str) -> String {
    match (parent.is_empty(), child.is_empty()) {
        (_, true) => parent.to_string(),
        (true, false) => child.to_string(),
        (false, false) => format!("{parent}.{child}"),
    }
}

/// `namespace.scope….name` — the dotted qualified name and the basis for ids.
fn qual_name(ns_join: &str, scope: &[String], name: &str) -> String {
    let mut parts: Vec<String> = Vec::new();
    if !ns_join.is_empty() {
        parts.push(ns_join.to_string());
    }
    parts.extend(scope.iter().cloned());
    parts.push(name.to_string());
    parts.join(".")
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

/// Interface naming convention: `I` followed by an uppercase letter (`IFoo`,
/// `IDisposable`) — used only to classify an *external* base whose definition is
/// not in the project (the target is still an explicit `UnresolvedSymbol`).
fn looks_like_interface(name: &str) -> bool {
    let bytes = name.as_bytes();
    bytes.len() >= 2 && bytes[0] == b'I' && bytes[1].is_ascii_uppercase()
}

/// Name from a `Name` child node: the joined non-trivia token texts (a single
/// identifier for a type, a dotted path for a namespace).
fn node_name(item: &Node, src: &str) -> Option<String> {
    let nm = item.child(cst::NAME)?;
    let mut s = String::new();
    for t in nm.tokens() {
        s.push_str(t.span.text(src));
    }
    if s.is_empty() {
        None
    } else {
        Some(s)
    }
}

fn name_span_start(item: &Node) -> u32 {
    item.child(cst::NAME)
        .map(|n| n.span.start)
        .unwrap_or(item.span.start)
}

/// The member name from a header: the last non-keyword identifier at angle-bracket
/// depth 0 that appears before the parameter-list `Paren` (or before the end, for
/// a field/property). Skips generic parameters (`Foo<T>` → `Foo`) and return-type
/// identifiers, and works for explicit interface members (`IFoo.Bar` → `Bar`).
fn member_name(header: &Node, src: &str) -> Option<String> {
    let children = &header.children;
    // Index of the parameter-list paren (the last direct Paren child).
    let mut end = children.len();
    for (i, ch) in children.iter().enumerate() {
        if let Child::Node(n) = ch {
            if n.kind == cst::PAREN {
                end = i;
            }
        }
    }
    let mut depth: i32 = 0;
    let mut name: Option<String> = None;
    for ch in &children[..end] {
        if let Child::Token(t) = ch {
            if t.trivia {
                continue;
            }
            let text = t.span.text(src);
            for c in text.chars() {
                match c {
                    '<' => depth += 1,
                    '>' => depth -= 1,
                    _ => {}
                }
            }
            if depth < 0 {
                depth = 0;
            }
            if depth == 0 && t.kind == tk::IDENT && !is_keyword(text) {
                name = Some(text.to_string());
            }
        }
    }
    name
}

/// Base-type simple names from a type header's base list (the part after the first
/// top-level `:`, up to a `where` constraint clause). Generic arguments are
/// ignored (`List<T>` → `List`); each comma-separated base yields its last
/// non-keyword identifier at angle-depth 0.
fn base_names(header: &Node, src: &str) -> Vec<String> {
    let toks = top_level_tokens(header, src);
    // Find the base-list colon: the first depth-0 `:` reached before any `where`.
    let mut depth: i32 = 0;
    let mut start: Option<usize> = None;
    for (i, t) in toks.iter().enumerate() {
        adjust_angle(&mut depth, t.text);
        if depth == 0 && t.text == "where" {
            return Vec::new();
        }
        if depth == 0 && t.text == ":" {
            start = Some(i + 1);
            break;
        }
    }
    let start = match start {
        Some(s) => s,
        None => return Vec::new(),
    };

    let mut bases = Vec::new();
    let mut clause_last: Option<String> = None;
    depth = 0;
    for t in &toks[start..] {
        adjust_angle(&mut depth, t.text);
        if depth == 0 && t.text == "where" {
            break;
        }
        if depth == 0 && t.text == "," {
            if let Some(b) = clause_last.take() {
                bases.push(b);
            }
            continue;
        }
        if depth == 0 && t.kind == tk::IDENT && !is_keyword(t.text) {
            clause_last = Some(t.text.to_string());
        }
    }
    if let Some(b) = clause_last.take() {
        bases.push(b);
    }
    bases
}

fn adjust_angle(depth: &mut i32, text: &str) {
    for c in text.chars() {
        match c {
            '<' => *depth += 1,
            '>' => *depth -= 1,
            _ => {}
        }
    }
    if *depth < 0 {
        *depth = 0;
    }
}

/// True if `item` carries a leading modifier token with the given text.
fn has_modifier(item: &Node, src: &str, kw: &str) -> bool {
    item.tokens().any(|t| t.span.text(src) == kw)
}

/// True if a header carries the given keyword among its direct, top-level tokens.
fn header_has_keyword(header: &Node, src: &str, kw: &str) -> bool {
    header.tokens().any(|t| t.span.text(src) == kw)
}

/// A flat token (text + kind), used by the small token-list helpers.
#[derive(Clone, Copy)]
struct Tok<'a> {
    text: &'a str,
    kind: &'static str,
}

/// Direct, non-trivia child tokens of `node` in source order (does not descend
/// into child nodes such as balanced groups).
fn top_level_tokens<'a>(node: &'a Node, src: &'a str) -> Vec<Tok<'a>> {
    node.tokens()
        .map(|t| Tok {
            text: t.span.text(src),
            kind: t.kind,
        })
        .collect()
}

/// Collect the first segment of every declared namespace into `roots` (a pre-pass
/// so a `using` can be classified internal/external regardless of declaration
/// order across files).
fn collect_namespace_roots(node: &Node, src: &str, roots: &mut BTreeSet<String>) {
    for n in node.walk() {
        if n.kind == cst::NAMESPACE {
            if let Some(name) = node_name(n, src) {
                if let Some(first) = name.split('.').next() {
                    if !first.is_empty() {
                        roots.insert(first.to_string());
                    }
                }
            }
        }
    }
}

// --- call detection over the lossless token tree ----------------------------

enum El<'a> {
    Tok { text: &'a str, ident: bool },
    Grp(&'a Node),
}

fn tok_text<'a>(e: &El<'a>) -> Option<&'a str> {
    match e {
        El::Tok { text, .. } => Some(text),
        El::Grp(_) => None,
    }
}

fn is_ident_el(e: &El) -> bool {
    matches!(e, El::Tok { ident: true, .. })
}

fn grp<'a>(e: &El<'a>) -> Option<&'a Node> {
    match e {
        El::Grp(n) => Some(n),
        El::Tok { .. } => None,
    }
}

fn significant_children<'a>(node: &'a Node, src: &'a str) -> Vec<El<'a>> {
    let mut v = Vec::new();
    for c in &node.children {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => v.push(El::Tok {
                text: t.span.text(src),
                ident: t.kind == tk::IDENT,
            }),
            Child::Node(n) => v.push(El::Grp(n)),
        }
    }
    v
}

/// Detect `name(...)` and `recv.name(...)` call sites over the real token tree,
/// recursing into nested groups. Keywords (`new`, `if`, `typeof`, …) are excluded
/// as callee names — `new Foo(...)` is captured as a call to the constructor
/// `Foo`, since `new` is skipped and `Foo` is the adjacent identifier.
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        // Member call: `.` name `(...)`.
        if tok_text(&els[i]) == Some(".") {
            if i + 2 < n && is_ident_el(&els[i + 1]) {
                if let Some(g) = grp(&els[i + 2]) {
                    if g.kind == cst::PAREN {
                        let callee = tok_text(&els[i + 1]).unwrap_or("");
                        if !is_keyword(callee) {
                            let receiver = if i > 0 {
                                match &els[i - 1] {
                                    El::Tok { text, ident: true } => Some(text.to_string()),
                                    _ => None,
                                }
                            } else {
                                None
                            };
                            out.push(Call {
                                name: callee.to_string(),
                                method: true,
                                receiver,
                            });
                            i += 3;
                            continue;
                        }
                    }
                }
            }
            i += 1;
            continue;
        }
        // Bare call: name `(...)`, not preceded by `.` and not a keyword.
        if is_ident_el(&els[i]) {
            let prev = if i > 0 { tok_text(&els[i - 1]) } else { None };
            let text = tok_text(&els[i]).unwrap_or("");
            if prev != Some(".") && !is_keyword(text) && i + 1 < n {
                if let Some(g) = grp(&els[i + 1]) {
                    if g.kind == cst::PAREN {
                        out.push(Call {
                            name: text.to_string(),
                            method: false,
                            receiver: None,
                        });
                    }
                }
            }
        }
        i += 1;
    }
    // Recurse into nested groups (parameter lists, blocks, expressions).
    for e in &els {
        if let Some(g) = grp(e) {
            scan_calls(g, src, out);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::csharp::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("Sample.cs", src);
        let file = SourceFile {
            rel_path: "Sample.cs".to_string(),
            module_path: vec![],
            source: &tree.source,
            root: &tree.root,
        };
        lower("Demo", std::slice::from_ref(&file), &[])
    }

    fn call_edges(g: &Graph) -> Vec<&crate::graph::GraphEdge> {
        g.edges().filter(|e| e.kind == edge::CALLS).collect()
    }

    #[test]
    fn emits_type_function_module_nodes() {
        let g = graph_for("namespace App { class C { void M() {} int F; } }");
        assert_eq!(g.count_nodes_of(ont::TYPE), 1, "class C is a Type");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 1, "method M");
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "namespace App");
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 1, "field F");
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD));
    }

    #[test]
    fn type_kinds_are_honest() {
        let g = graph_for(
            "namespace N { class C {} struct S {} interface I {} enum E { A } record R(int X); }",
        );
        let kinds: BTreeSet<String> = g
            .nodes()
            .filter(|n| n.kind == ont::TYPE)
            .filter_map(|n| n.props.get("type_kind"))
            .filter_map(|j| match j {
                Json::Str(s) => Some(s.clone()),
                _ => None,
            })
            .collect();
        for k in ["class", "struct", "interface", "enum", "record"] {
            assert!(kinds.contains(k), "missing type_kind {k}: {kinds:?}");
        }
    }

    #[test]
    fn resolves_unique_method_call_via_implicit_this() {
        let g = graph_for("class C { void Run() { Helper(); } void Helper() {} }");
        let calls = call_edges(&g);
        let h = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("Helper")))
            .expect("a call to Helper");
        assert_eq!(h.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(h.props.get("resolution"), Some(&Json::str("implicit_this")));
        assert!(h.to.starts_with("fn::C.Helper") || h.to.contains(".Helper"));
    }

    #[test]
    fn this_call_resolves_via_receiver() {
        let g = graph_for("class P { void A() { this.B(); } void B() {} }");
        let recv = call_edges(&g)
            .into_iter()
            .find(|e| e.props.get("resolution") == Some(&Json::str("receiver")));
        assert!(recv.is_some(), "this.B() should resolve via receiver scope");
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for("class C { void Run() { Mystery(); } }");
        let calls = call_edges(&g);
        let m = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("Mystery")))
            .expect("call to Mystery");
        assert_eq!(m.props.get("resolution"), Some(&Json::str("external")));
        assert!(g.has_node("unresolved::Mystery"));
    }

    #[test]
    fn new_expression_is_a_constructor_call() {
        let g = graph_for(
            "class Widget { public Widget() {} } class C { void M() { var w = new Widget(); } }",
        );
        let calls = call_edges(&g);
        let ctor = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("Widget")));
        assert!(
            ctor.is_some(),
            "new Widget() should be a CALLS edge to the ctor"
        );
    }

    #[test]
    fn external_using_creates_dependency() {
        let g = graph_for("using System;\nusing System.Text;\nclass C {}");
        assert!(g.has_node("ext::System"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::System"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn internal_using_is_not_external() {
        let g = graph_for("using App.Core;\nnamespace App.Core { class C {} }");
        // `App` is a declared namespace root → internal import, no ExternalDependency.
        assert!(!g.has_node("ext::App"), "App should be internal");
        assert!(g.edges().any(
            |e| e.kind == edge::IMPORTS && e.props.get("external") == Some(&Json::Bool(false))
        ));
    }

    #[test]
    fn class_inheritance_emits_extends() {
        let g = graph_for("class Base {} class Derived : Base {}");
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an EXTENDS edge");
        assert!(ext.from.contains("Derived"));
        assert!(ext.to.contains("Base"));
    }

    #[test]
    fn interface_base_emits_implements() {
        let g = graph_for("interface IFoo {} class C : IFoo {}");
        let imp = g
            .edges()
            .find(|e| e.kind == edge::IMPLEMENTS)
            .expect("an IMPLEMENTS edge");
        assert!(imp.to.contains("IFoo"));
    }

    #[test]
    fn external_interface_base_uses_naming_convention() {
        let g = graph_for("class C : IDisposable {}");
        let imp = g
            .edges()
            .find(|e| e.kind == edge::IMPLEMENTS && e.to == "unresolved::IDisposable")
            .expect("heuristic IMPLEMENTS to unresolved interface");
        assert_eq!(
            imp.props.get("inference"),
            Some(&Json::str("naming_convention"))
        );
    }

    #[test]
    fn field_is_constant_property_is_property() {
        let g = graph_for("class C { const int K = 1; int P { get; set; } }");
        let consts: Vec<&crate::graph::GraphNode> =
            g.nodes().filter(|n| n.kind == ont::CONSTANT).collect();
        assert_eq!(consts.len(), 2);
        let k = consts.iter().find(|n| n.name == "K").unwrap();
        assert_eq!(k.props.get("binding"), Some(&Json::str("const")));
        let p = consts.iter().find(|n| n.name == "P").unwrap();
        assert_eq!(p.props.get("binding"), Some(&Json::str("property")));
    }

    #[test]
    fn type_use_in_signature() {
        let g = graph_for("class Widget {} class C { void Build(Widget w) {} }");
        assert!(
            g.edges()
                .any(|e| e.kind == edge::USES_TYPE && e.to.contains("Widget")),
            "parameter type should create USES_TYPE"
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src = "namespace N { class C : B { void M() { f(); g(); } void f() {} } }";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }

    #[test]
    fn top_level_statements_emit_entry_main() {
        // Modern minimal-API Program.cs: no `Main` anywhere in source.
        let src = "using Microsoft.AspNetCore.Builder;\n\n\
                   var builder = WebApplication.CreateBuilder(args);\n\
                   builder.Services.AddControllers();\n\
                   var app = builder.Build();\n\
                   app.MapGet(\"/\", () => \"ok\");\n\
                   app.Run();\n";
        let g = graph_for(src);
        let main = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "main")
            .expect("top-level statements should produce a synthetic main");
        assert_eq!(main.props.get("entrypoint"), Some(&Json::Bool(true)));
        assert_eq!(
            main.props.get("entrypoint_kind"),
            Some(&Json::str("top_level_statements"))
        );
        assert_eq!(main.props.get("synthetic"), Some(&Json::Bool(true)));
        assert!(
            g.edges()
                .any(|e| e.kind == edge::DECLARES && e.to == main.id),
            "the file should declare the entry marker"
        );
        // The statements are its body: real CALLS edges come off the marker.
        assert!(
            g.edges().any(|e| e.kind == edge::CALLS
                && e.from == main.id
                && e.props.get("callee") == Some(&Json::str("Run"))),
            "app.Run() should be a CALLS edge from the synthetic main"
        );
    }

    #[test]
    fn async_top_level_statements_are_an_entry_point() {
        let src = "var host = Host.CreateDefaultBuilder(args).Build();\n\
                   await host.RunAsync();\n";
        let g = graph_for(src);
        let main = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "main")
            .expect("await-led top-level statements should produce a synthetic main");
        assert_eq!(main.props.get("entrypoint"), Some(&Json::Bool(true)));
    }

    #[test]
    fn classic_static_main_is_an_entry_point() {
        let g = graph_for(
            "class Program { static void Main(string[] args) { Console.WriteLine(\"hi\"); } }",
        );
        let main_method = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "Main")
            .expect("the Main method node");
        assert_eq!(main_method.props.get("entrypoint"), Some(&Json::Bool(true)));
        let marker = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "main")
            .expect("classic static Main should also produce the main marker");
        assert_eq!(
            marker.props.get("entrypoint_kind"),
            Some(&Json::str("static_main"))
        );
        assert_eq!(
            marker.props.get("alias_of"),
            Some(&Json::str(main_method.id.clone())),
            "the marker should alias the real Main method"
        );
    }

    #[test]
    fn library_file_is_not_an_entry_point() {
        let src = "using System;\n\
                   namespace Lib {\n\
                     public class Greeter {\n\
                       public string Greet(string name) => $\"hi {name}\";\n\
                       static string Format(string s) { return s; }\n\
                     }\n\
                   }\n";
        let g = graph_for(src);
        assert!(
            !g.nodes().any(|n| n.name == "main"),
            "a plain library file must not gain a main marker"
        );
        assert!(
            !g.nodes().any(|n| n.props.contains_key("entrypoint")),
            "no node in a library file should be marked entrypoint"
        );
    }

    #[test]
    fn stray_top_level_tokens_are_not_an_entry_point() {
        // Assembly attribute + stray closer: recovery artifacts, not statements.
        for src in ["[assembly: InternalsVisibleTo(\"X\")]", "}", ";"] {
            let g = graph_for(src);
            assert!(
                !g.nodes().any(|n| n.name == "main"),
                "stray input {src:?} must not be an entry point"
            );
        }
    }

    #[test]
    fn instance_main_is_not_an_entry_point() {
        // `Main` without `static` is just a method, not the program entry.
        let g = graph_for("class C { void Main() {} }");
        assert!(!g.nodes().any(|n| n.name == "main"));
        assert!(!g.nodes().any(|n| n.props.contains_key("entrypoint")));
    }
}
