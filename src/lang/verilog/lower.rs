//! Lower the Verilog / SystemVerilog CST into the canonical graph.
//!
//! This mirrors the Rust and Lua lowerings — the same conservative principles and
//! the same shared ontology — adapted to hardware-description surface. The honest
//! mapping is:
//!
//!   - `module` / `interface` / `program` → [`Type`] (`type_kind: module` /
//!     `interface` / `program`). A hardware module is a *definition* with ports
//!     and instances; modelling it as a `Type` keeps it a first-class declared
//!     node that instantiations can resolve to, exactly as a class does.
//!   - `class` → [`Type`] (`type_kind: class`), with `extends Base` lowered to an
//!     `EXTENDS` edge (inheritance, not interface-conformance).
//!   - `package` → [`Module`] (a pure namespace scope).
//!   - `function` / `task` → [`Function`] (a `task` carries `returns: void`); a
//!     function/task declared inside a `class` is additionally `HAS_METHOD` of the
//!     class and flagged `is_method`.
//!   - `parameter` / `localparam` / `` `define `` → [`Constant`].
//!   - `` `include "file" `` → [`IMPORTS`] (+ [`ExternalDependency`] + `DEPENDS_ON`),
//!     and `import pkg::*` → [`IMPORTS`] (internal to a local package, else an
//!     external dependency).
//!   - module **instantiation** `Foo u1 (...)` → [`CALLS`] to the `Foo` module
//!     type; a bare `name(...)` → [`CALLS`] to a function/task; a `$system` task →
//!     [`CALLS`] to an explicit [`UnresolvedSymbol`] (a builtin with no project
//!     definition). Dotted method calls (`obj.m()`) are intentionally *not*
//!     emitted: there is no receiver-type inference here, so emitting them would
//!     fabricate targets the source does not pin down (airgap "no fabricated
//!     targets" rule).
//!
//! What has no honest home: net/variable declarations (`wire`/`logic`), procedural
//! blocks (`always`/`initial`), and `assign` statements are structure, not
//! definitions or edges, so they are walked for the calls they contain but emit no
//! node of their own. Everything comes from real tokens on the lossless tree;
//! nothing is guessed.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::verilog::lexer::{is_keyword, kind as tk};
use crate::lang::verilog::parser::node as cst;

/// Lower a whole project's worth of Verilog/SystemVerilog files into a graph.
/// `manifest_deps` is unused (Verilog has no manifest the pipeline reads);
/// dependencies are discovered from `` `include ``/`import` instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    let mut local_roots: BTreeSet<String> = BTreeSet::new();
    local_roots.insert(package.to_string());
    for f in files {
        for seg in &f.module_path {
            local_roots.insert(seg.clone());
        }
    }

    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        local_roots,
        local_packages: BTreeSet::new(),
        fn_by_name: BTreeMap::new(),
        module_by_name: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("verilog"))],
    );

    // Pass B: create definition nodes + structural edges and build symbol tables.
    let mut pend: Vec<PendingScope> = Vec::new();
    for f in files {
        let li = LineIndex::new(f.source);
        let module_join = mod_join(&f.module_path);
        let leaf = lo.ensure_modules(&f.module_path);
        let file_id = format!("file::{}", f.rel_path);
        lo.g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("verilog")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(leaf, edge::CONTAINS, file_id.clone(), vec![]);

        lo.walk(
            f.root,
            &file_id,
            &file_id,
            &module_join,
            &[],
            None,
            f.source,
            &li,
            &mut pend,
        );
    }

    // Pass C: resolve calls and instantiations against the complete tables.
    for ps in &pend {
        let mut calls = Vec::new();
        let mut insts = Vec::new();
        scan_refs(ps.body, ps.scan_insts, ps.source, &mut calls, &mut insts);
        for call in &calls {
            lo.emit_call(&ps.id, call);
        }
        for inst in &insts {
            lo.emit_inst(&ps.id, inst);
        }
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    local_roots: BTreeSet<String>,
    local_packages: BTreeSet<String>,
    /// Simple name → function/task node ids.
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// Simple name → module/interface/program type ids (instantiation targets).
    module_by_name: BTreeMap<String, Vec<String>>,
}

struct PendingScope<'a> {
    id: String,
    source: &'a str,
    body: &'a Node,
    /// Modules scan for instantiations; function/task bodies do not.
    scan_insts: bool,
}

/// A detected reference site over the lossless token tree.
struct Ref {
    name: String,
    /// True for a `$system` task/function (a builtin, never project-local).
    system: bool,
}

struct Inst {
    /// The instantiated module type name.
    module: String,
}

impl Lowerer {
    fn pkg_id(&self) -> String {
        format!("pkg::{}", self.package)
    }

    /// Ensure the `Package → mod::a → mod::a.b …` chain exists and return the leaf
    /// module id (or the package id for a root file with no module segments).
    fn ensure_modules(&mut self, path: &[String]) -> String {
        let pkg = self.pkg_id();
        if path.is_empty() {
            return pkg;
        }
        let mut parent = pkg;
        let mut acc: Vec<String> = Vec::new();
        for seg in path {
            acc.push(seg.clone());
            let id = format!("mod::{}", acc.join("."));
            self.g.upsert_node(
                id.clone(),
                ont::MODULE,
                seg.clone(),
                vec![("language", Json::str("verilog"))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    /// Walk an item container, creating definition nodes and recursing. `owner`
    /// carries the enclosing class (type id, name) so methods get `HAS_METHOD`.
    #[allow(clippy::too_many_arguments)]
    fn walk<'a>(
        &mut self,
        container: &'a Node,
        file_id: &str,
        container_id: &str,
        module_join: &str,
        scope: &[String],
        owner: Option<&(String, String)>,
        src: &'a str,
        li: &LineIndex,
        pend: &mut Vec<PendingScope<'a>>,
    ) {
        for item in container.child_nodes() {
            match item.kind {
                cst::MODULE | cst::INTERFACE | cst::PROGRAM => {
                    self.handle_module_like(
                        item,
                        file_id,
                        container_id,
                        module_join,
                        scope,
                        src,
                        li,
                        pend,
                    );
                }
                cst::PACKAGE => {
                    self.handle_package(item, container_id, module_join, scope, src, li, pend);
                }
                cst::CLASS => {
                    self.handle_class(
                        item,
                        file_id,
                        container_id,
                        module_join,
                        scope,
                        src,
                        li,
                        pend,
                    );
                }
                cst::FUNCTION | cst::TASK => {
                    self.handle_fn(item, container_id, module_join, scope, owner, src, li, pend);
                }
                cst::PARAM_DECL => {
                    self.handle_param(item, container_id, module_join, scope, src, li)
                }
                cst::IMPORT_DECL => self.handle_import(item, file_id, src),
                cst::DIRECTIVE => {
                    self.handle_directive(item, file_id, container_id, module_join, scope, src, li)
                }
                // Not new naming scopes, but may hold nested definitions.
                cst::GENERATE
                | cst::BEGIN_BLOCK
                | cst::CASE
                | cst::BLOCK_CONSTRUCT
                | cst::ITEM_BLOCK => {
                    self.walk(
                        item,
                        file_id,
                        container_id,
                        module_join,
                        scope,
                        owner,
                        src,
                        li,
                        pend,
                    );
                }
                _ => {}
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_module_like<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        container_id: &str,
        module_join: &str,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend: &mut Vec<PendingScope<'a>>,
    ) {
        let name = simple_name(item, src).unwrap_or_else(|| "<anonymous>".to_string());
        let line = li.line_col(name_start(item)).line;
        let type_kind = match item.kind {
            cst::INTERFACE => "interface",
            cst::PROGRAM => "program",
            _ => "module",
        };
        let qual = qual_name(module_join, scope, &name);
        let id = format!("type::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str(type_kind)),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("verilog")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
            ],
        );
        self.g
            .add_edge(container_id, edge::DECLARES, id.clone(), vec![]);
        self.module_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());

        if let Some(body) = item.child(cst::ITEM_BLOCK) {
            pend.push(PendingScope {
                id: id.clone(),
                source: src,
                body,
                scan_insts: true,
            });
            let mut child_scope = scope.to_vec();
            child_scope.push(name);
            self.walk(
                body,
                file_id,
                &id,
                module_join,
                &child_scope,
                None,
                src,
                li,
                pend,
            );
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_package<'a>(
        &mut self,
        item: &'a Node,
        container_id: &str,
        module_join: &str,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend: &mut Vec<PendingScope<'a>>,
    ) {
        let name = simple_name(item, src).unwrap_or_else(|| "<anonymous>".to_string());
        let qual = qual_name(module_join, scope, &name);
        let id = format!("mod::pkg::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::MODULE,
            name.clone(),
            vec![
                ("module_kind", Json::str("package")),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("verilog")),
            ],
        );
        self.g
            .add_edge(container_id, edge::CONTAINS, id.clone(), vec![]);
        self.local_packages.insert(name.clone());

        if let Some(body) = item.child(cst::ITEM_BLOCK) {
            let mut child_scope = scope.to_vec();
            child_scope.push(name);
            self.walk(
                body,
                container_id,
                &id,
                module_join,
                &child_scope,
                None,
                src,
                li,
                pend,
            );
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_class<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        container_id: &str,
        module_join: &str,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend: &mut Vec<PendingScope<'a>>,
    ) {
        let name = simple_name(item, src).unwrap_or_else(|| "<anonymous>".to_string());
        let line = li.line_col(name_start(item)).line;
        let qual = qual_name(module_join, scope, &name);
        let id = format!("type::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str("class")),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("verilog")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
            ],
        );
        self.g
            .add_edge(container_id, edge::DECLARES, id.clone(), vec![]);
        self.module_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());

        // `extends Base` → EXTENDS edge to the base class (resolved later only if
        // unique; here we record an unresolved base if absent, never fabricated).
        if let Some(base) = class_base(item, src) {
            let target = format!("unresolved::{base}");
            if !self.g.has_node(&target) {
                self.g.upsert_node(
                    target.clone(),
                    ont::UNRESOLVED,
                    base.clone(),
                    vec![
                        ("unresolved", Json::Bool(true)),
                        ("role", Json::str("base_class")),
                    ],
                );
            }
            self.g.add_edge(
                id.clone(),
                edge::EXTENDS,
                target,
                vec![("base_name", Json::str(base))],
            );
        }

        let owner = (id.clone(), name.clone());
        if let Some(body) = item.child(cst::ITEM_BLOCK) {
            let mut child_scope = scope.to_vec();
            child_scope.push(name);
            self.walk(
                body,
                file_id,
                &id,
                module_join,
                &child_scope,
                Some(&owner),
                src,
                li,
                pend,
            );
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_fn<'a>(
        &mut self,
        item: &'a Node,
        container_id: &str,
        module_join: &str,
        scope: &[String],
        owner: Option<&(String, String)>,
        src: &'a str,
        li: &LineIndex,
        pend: &mut Vec<PendingScope<'a>>,
    ) {
        let name = fn_name(item, src).unwrap_or_else(|| "<anonymous>".to_string());
        let line = li.line_col(name_start(item)).line;
        let qual = qual_name(module_join, scope, &name);
        let id = format!("fn::{qual}#{line}");
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("verilog")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            (
                "has_body",
                Json::Bool(item.child(cst::ITEM_BLOCK).is_some()),
            ),
        ];
        if item.kind == cst::TASK {
            props.push(("subroutine", Json::str("task")));
            props.push(("returns", Json::str("void")));
        } else {
            props.push(("subroutine", Json::str("function")));
        }
        if let Some((_, owner_name)) = owner {
            props.push(("receiver_type", Json::str(owner_name.clone())));
            props.push(("is_method", Json::Bool(true)));
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, name.clone(), props);
        self.g
            .add_edge(container_id, edge::DECLARES, id.clone(), vec![]);
        self.fn_by_name.entry(name).or_default().push(id.clone());

        if let Some((owner_id, _)) = owner {
            self.g
                .add_edge(owner_id.clone(), edge::HAS_METHOD, id.clone(), vec![]);
        }

        if let Some(body) = item.child(cst::ITEM_BLOCK) {
            pend.push(PendingScope {
                id,
                source: src,
                body,
                scan_insts: false,
            });
        }
    }

    fn handle_param(
        &mut self,
        item: &Node,
        container_id: &str,
        module_join: &str,
        scope: &[String],
        src: &str,
        li: &LineIndex,
    ) {
        // `parameter [type] NAME = expr` — the binding name is the identifier
        // immediately preceding the first top-level `=`, or the last identifier.
        let name = match param_name(item, src) {
            Some(n) => n,
            None => return,
        };
        let line = li.line_col(item.span.start).line;
        let kind = item
            .tokens()
            .find(|t| matches!(t.span.text(src), "parameter" | "localparam"))
            .map(|t| t.span.text(src))
            .unwrap_or("parameter");
        let qual = qual_name(module_join, scope, &name);
        let id = format!("const::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            name,
            vec![
                ("binding", Json::str(kind)),
                ("language", Json::str("verilog")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(container_id, edge::DECLARES, id, vec![]);
    }

    fn handle_import(&mut self, item: &Node, file_id: &str, src: &str) {
        // `import pkg::*;` / `import pkg::name;` — the package is the first ident.
        let pkg = item
            .tokens()
            .map(|t| t.span.text(src))
            .find(|txt| !is_keyword(txt) && is_word(txt));
        let pkg = match pkg {
            Some(p) => p.to_string(),
            None => return,
        };
        if self.local_packages.contains(&pkg) || self.local_roots.contains(&pkg) {
            let id = format!("mod::{pkg}");
            self.g.upsert_node(
                id.clone(),
                ont::MODULE,
                pkg,
                vec![("language", Json::str("verilog"))],
            );
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                id,
                vec![("external", Json::Bool(false))],
            );
        } else {
            self.emit_external_import(file_id, &pkg, "import");
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_directive(
        &mut self,
        item: &Node,
        file_id: &str,
        container_id: &str,
        module_join: &str,
        scope: &[String],
        src: &str,
        li: &LineIndex,
    ) {
        let dir = match item.tokens().next() {
            Some(t) if t.kind == tk::DIRECTIVE => t.span.text(src),
            _ => return,
        };
        match dir {
            "`define" => {
                // `` `define NAME body `` — NAME is the first ident after the
                // directive token.
                if let Some(name) = item
                    .tokens()
                    .map(|t| t.span.text(src))
                    .find(|txt| is_word(txt))
                {
                    let line = li.line_col(item.span.start).line;
                    let qual = qual_name(module_join, scope, name);
                    let id = format!("const::define::{qual}");
                    self.g.upsert_node(
                        id.clone(),
                        ont::CONSTANT,
                        name.to_string(),
                        vec![
                            ("binding", Json::str("define")),
                            ("language", Json::str("verilog")),
                            ("line", Json::U64(line as u64)),
                        ],
                    );
                    self.g.add_edge(container_id, edge::DECLARES, id, vec![]);
                }
            }
            "`include" => {
                // `` `include "file.vh" `` — the path is the first string literal.
                if let Some(t) = item.tokens().find(|t| t.kind == tk::STRING) {
                    let raw = t.span.text(src);
                    let path = strip_quotes(raw);
                    let base = path.rsplit('/').next().unwrap_or(&path).to_string();
                    self.emit_external_import_path(file_id, &base, &path, "include");
                }
            }
            _ => {}
        }
    }

    fn emit_external_import(&mut self, file_id: &str, root: &str, source: &str) {
        let dep_id = format!("ext::{root}");
        self.g.upsert_node(
            dep_id.clone(),
            ont::EXTERNAL_DEPENDENCY,
            root.to_string(),
            vec![
                ("external", Json::Bool(true)),
                ("source", Json::str(source.to_string())),
            ],
        );
        self.g.add_edge(
            file_id,
            edge::IMPORTS,
            dep_id.clone(),
            vec![("external", Json::Bool(true))],
        );
        self.g
            .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
    }

    fn emit_external_import_path(&mut self, file_id: &str, root: &str, path: &str, source: &str) {
        let dep_id = format!("ext::{root}");
        self.g.upsert_node(
            dep_id.clone(),
            ont::EXTERNAL_DEPENDENCY,
            root.to_string(),
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

    // --- call / instantiation resolution ------------------------------------

    fn emit_call(&mut self, caller_id: &str, call: &Ref) {
        if call.system {
            let target = format!("unresolved::{}", call.name);
            self.ensure_unresolved(&target, &call.name, "system_task");
            self.g.add_edge(
                caller_id,
                edge::CALLS,
                target,
                vec![
                    ("callee", Json::str(call.name.clone())),
                    ("resolution", Json::str("system")),
                    ("resolved", Json::Bool(false)),
                ],
            );
            return;
        }
        let cands = self.fn_by_name.get(&call.name).cloned().unwrap_or_default();
        let mut props = vec![
            ("callee", Json::str(call.name.clone())),
            ("method", Json::Bool(false)),
        ];
        match cands.len() {
            1 => {
                props.push(("resolution", Json::str("global")));
                props.push(("resolved", Json::Bool(true)));
                props.push(("candidate_count", Json::U64(1)));
                self.g
                    .add_edge(caller_id, edge::CALLS, cands[0].clone(), props);
            }
            0 => {
                let target = format!("unresolved::{}", call.name);
                self.ensure_unresolved(&target, &call.name, "call");
                props.push(("resolution", Json::str("external")));
                props.push(("resolved", Json::Bool(false)));
                props.push(("candidate_count", Json::U64(0)));
                self.g.add_edge(caller_id, edge::CALLS, target, props);
            }
            n => {
                let target = format!("unresolved::{}", call.name);
                self.ensure_unresolved(&target, &call.name, "call");
                props.push(("resolution", Json::str("ambiguous")));
                props.push(("resolved", Json::Bool(false)));
                props.push(("ambiguous", Json::Bool(true)));
                props.push(("candidate_count", Json::U64(n as u64)));
                props.push((
                    "candidates",
                    Json::Array(cands.into_iter().map(Json::Str).collect()),
                ));
                self.g.add_edge(caller_id, edge::CALLS, target, props);
            }
        }
    }

    fn emit_inst(&mut self, caller_id: &str, inst: &Inst) {
        let cands = self
            .module_by_name
            .get(&inst.module)
            .cloned()
            .unwrap_or_default();
        let mut props = vec![
            ("callee", Json::str(inst.module.clone())),
            ("kind", Json::str("instantiation")),
        ];
        match cands.len() {
            1 => {
                props.push(("resolution", Json::str("module")));
                props.push(("resolved", Json::Bool(true)));
                props.push(("candidate_count", Json::U64(1)));
                self.g
                    .add_edge(caller_id, edge::CALLS, cands[0].clone(), props);
            }
            0 => {
                let target = format!("unresolved::{}", inst.module);
                self.ensure_unresolved(&target, &inst.module, "instantiation");
                props.push(("resolution", Json::str("external")));
                props.push(("resolved", Json::Bool(false)));
                props.push(("candidate_count", Json::U64(0)));
                self.g.add_edge(caller_id, edge::CALLS, target, props);
            }
            n => {
                let target = format!("unresolved::{}", inst.module);
                self.ensure_unresolved(&target, &inst.module, "instantiation");
                props.push(("resolution", Json::str("ambiguous")));
                props.push(("resolved", Json::Bool(false)));
                props.push(("ambiguous", Json::Bool(true)));
                props.push(("candidate_count", Json::U64(n as u64)));
                props.push((
                    "candidates",
                    Json::Array(cands.into_iter().map(Json::Str).collect()),
                ));
                self.g.add_edge(caller_id, edge::CALLS, target, props);
            }
        }
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
}

// --- pure helpers -----------------------------------------------------------

fn mod_join(path: &[String]) -> String {
    path.join(".")
}

fn qual_name(module_join: &str, scope: &[String], name: &str) -> String {
    let mut parts: Vec<String> = Vec::new();
    if !module_join.is_empty() {
        parts.push(module_join.to_string());
    }
    parts.extend(scope.iter().cloned());
    if !name.is_empty() {
        parts.push(name.to_string());
    }
    parts.join(".")
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

/// True for an ordinary (non-keyword) identifier word.
fn is_word(txt: &str) -> bool {
    let mut chars = txt.chars();
    match chars.next() {
        Some(c) if c == '_' || c == '\\' || c.is_alphabetic() => !is_keyword(txt),
        _ => false,
    }
}

/// The `Name` child of a module-family / class / package definition.
fn simple_name(item: &Node, src: &str) -> Option<String> {
    let nm = item.child(cst::NAME)?;
    nm.tokens().next().map(|t| t.span.text(src).to_string())
}

/// Byte offset used for a definition's line number: the `Name` token when present
/// (module/class/package), else the item's own start (function/task, whose name
/// lives inline in the header).
fn name_start(item: &Node) -> u32 {
    item.child(cst::NAME)
        .map(|n| n.span.start)
        .unwrap_or(item.span.start)
}

/// The name of a `function`/`task`: the last identifier in the header before the
/// argument list `(` (or the last identifier when there is no `(`), since a return
/// type may precede the name (`function int add(...)`).
fn fn_name(item: &Node, src: &str) -> Option<String> {
    let header = item.child(cst::HEADER)?;
    let mut last: Option<String> = None;
    for c in &header.children {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) if t.kind == tk::IDENT => {
                let txt = t.span.text(src);
                if !is_keyword(txt) {
                    last = Some(txt.to_string());
                }
            }
            Child::Token(_) => {}
            // A Paren group is the argument list — the name is whatever preceded it.
            Child::Node(n) if n.kind == cst::PAREN => break,
            Child::Node(_) => {}
        }
    }
    last
}

/// The base class of a `class C extends Base` header (the identifier after the
/// `extends` keyword), or `None`.
fn class_base(item: &Node, src: &str) -> Option<String> {
    let header = item.child(cst::HEADER)?;
    let mut seen_extends = false;
    for t in header.tokens() {
        let txt = t.span.text(src);
        if seen_extends && t.kind == tk::IDENT && !is_keyword(txt) {
            return Some(txt.to_string());
        }
        if txt == "extends" {
            seen_extends = true;
        }
    }
    None
}

/// The bound name of a `parameter`/`localparam` declaration: the identifier just
/// before the first top-level `=`, else the last identifier.
fn param_name(item: &Node, src: &str) -> Option<String> {
    let mut last_ident: Option<String> = None;
    let mut before_eq: Option<String> = None;
    for c in &item.children {
        if let Child::Token(t) = c {
            if t.trivia {
                continue;
            }
            let txt = t.span.text(src);
            if txt == "=" {
                before_eq = last_ident.clone();
                break;
            }
            if t.kind == tk::IDENT && !is_keyword(txt) {
                last_ident = Some(txt.to_string());
            }
        }
    }
    before_eq.or(last_ident)
}

fn strip_quotes(text: &str) -> String {
    let t = text.trim();
    if t.len() >= 2 && t.starts_with('"') && t.ends_with('"') {
        t[1..t.len() - 1].to_string()
    } else {
        t.to_string()
    }
}

// --- reference scanning over the lossless token tree ------------------------

enum El<'a> {
    Tok { text: &'a str, kind: &'static str },
    Grp(&'a Node),
}

fn significant_children<'a>(node: &'a Node, src: &'a str) -> Vec<El<'a>> {
    let mut v = Vec::new();
    for c in &node.children {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => v.push(El::Tok {
                text: t.span.text(src),
                kind: t.kind,
            }),
            Child::Node(n) => v.push(El::Grp(n)),
        }
    }
    v
}

fn el_tok_text<'a>(e: &El<'a>) -> Option<&'a str> {
    match e {
        El::Tok { text, .. } => Some(text),
        El::Grp(_) => None,
    }
}

fn el_is_ident(e: &El) -> bool {
    matches!(e, El::Tok { kind, .. } if *kind == tk::IDENT)
}

fn el_is_paren(e: &El) -> bool {
    matches!(e, El::Grp(n) if n.kind == cst::PAREN)
}

/// True for nested definition nodes that own their own reference scope (not
/// descended into by an enclosing scan).
fn is_def_node(kind: &str) -> bool {
    matches!(
        kind,
        cst::MODULE
            | cst::INTERFACE
            | cst::PROGRAM
            | cst::PACKAGE
            | cst::CLASS
            | cst::FUNCTION
            | cst::TASK
    )
}

/// Detect reference sites over the real token tree:
///   - `$system(...)` / `$system` → a system call.
///   - `name(...)` (bare, not after `.`) → a function/task call.
///   - `Module inst (...)` / `Module #(...) inst (...)` → an instantiation
///     (only when `scan_insts`, i.e. in a module/interface/program body).
///
/// Recurses into groups and nested non-definition nodes; never into nested
/// definitions (those are scanned as their own pending scopes).
fn scan_refs<'a>(
    node: &'a Node,
    scan_insts: bool,
    src: &'a str,
    calls: &mut Vec<Ref>,
    insts: &mut Vec<Inst>,
) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        // System task / function.
        if let El::Tok { text, kind } = &els[i] {
            if *kind == tk::SYSTEM_IDENT {
                calls.push(Ref {
                    name: text.to_string(),
                    system: true,
                });
                i += 1;
                continue;
            }
        }

        if el_is_ident(&els[i]) {
            let name = el_tok_text(&els[i]).unwrap_or("");
            let prev = if i > 0 {
                el_tok_text(&els[i - 1])
            } else {
                None
            };
            let after_dot = matches!(prev, Some(".") | Some("::"));
            if !after_dot && !is_keyword(name) && is_word(name) {
                // Bare call: name(...).
                if i + 1 < n && el_is_paren(&els[i + 1]) {
                    calls.push(Ref {
                        name: name.to_string(),
                        system: false,
                    });
                    i += 2;
                    continue;
                }
                // Instantiation: Module [#(...)] inst (...).
                if scan_insts {
                    let mut j = i + 1;
                    if j + 1 < n && el_tok_text(&els[j]) == Some("#") && el_is_paren(&els[j + 1]) {
                        j += 2;
                    }
                    if j + 1 < n && el_is_ident(&els[j]) && el_is_paren(&els[j + 1]) {
                        let inst_word = el_tok_text(&els[j]).unwrap_or("");
                        if !is_keyword(inst_word) {
                            insts.push(Inst {
                                module: name.to_string(),
                            });
                            i = j + 2;
                            continue;
                        }
                    }
                }
            }
        }
        i += 1;
    }

    for e in &els {
        if let El::Grp(g) = e {
            if !is_def_node(g.kind) {
                scan_refs(g, scan_insts, src, calls, insts);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::verilog::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("top.sv", src);
        let file = SourceFile {
            rel_path: "top.sv".to_string(),
            module_path: vec!["top".to_string()],
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    fn call_edges(g: &Graph) -> Vec<&crate::graph::GraphEdge> {
        g.edges().filter(|e| e.kind == edge::CALLS).collect()
    }

    #[test]
    fn module_becomes_type() {
        let g = graph_for("module counter (input clk); endmodule");
        let ty = g
            .nodes()
            .find(|n| n.kind == ont::TYPE && n.name == "counter")
            .expect("a Type node for the module");
        assert_eq!(ty.props.get("type_kind"), Some(&Json::str("module")));
        assert!(g.edges().any(|e| e.kind == edge::DECLARES && e.to == ty.id));
    }

    #[test]
    fn function_and_task_become_functions() {
        let g = graph_for(
            "module m;\n  function int add(int a, int b); return a + b; endfunction\n  task run; endtask\nendmodule",
        );
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::FUNCTION && n.name == "add"));
        let run = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "run")
            .expect("the task");
        assert_eq!(run.props.get("subroutine"), Some(&Json::str("task")));
    }

    #[test]
    fn class_extends_makes_edge_and_methods() {
        let g =
            graph_for("class Packet extends BasePacket;\n  function new(); endfunction\nendclass");
        let cls = g
            .nodes()
            .find(|n| n.kind == ont::TYPE && n.name == "Packet")
            .expect("class type");
        assert_eq!(cls.props.get("type_kind"), Some(&Json::str("class")));
        assert!(g.edges().any(|e| e.kind == edge::EXTENDS));
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD));
    }

    #[test]
    fn instantiation_resolves_to_module() {
        let g = graph_for(
            "module sub (input a); endmodule\nmodule top;\n  sub u_sub (.a(x));\nendmodule",
        );
        let calls = call_edges(&g);
        let inst = calls
            .iter()
            .find(|e| e.props.get("kind") == Some(&Json::str("instantiation")))
            .expect("an instantiation CALLS edge");
        assert_eq!(inst.props.get("resolution"), Some(&Json::str("module")));
        assert!(inst.to.starts_with("type::"));
    }

    #[test]
    fn function_call_resolves() {
        let g = graph_for(
            "module m;\n  function int add(int a, int b); return a + b; endfunction\n  function int run(); return add(1, 2); endfunction\nendmodule",
        );
        let calls = call_edges(&g);
        let add = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("add")))
            .expect("a call to add");
        assert_eq!(add.props.get("resolved"), Some(&Json::Bool(true)));
        assert!(add.to.starts_with("fn::"));
    }

    #[test]
    fn system_task_is_unresolved_system_call() {
        let g = graph_for("module m; initial $display(\"hi\"); endmodule");
        let calls = call_edges(&g);
        let sys = calls
            .iter()
            .find(|e| e.props.get("resolution") == Some(&Json::str("system")))
            .expect("a system call");
        assert_eq!(sys.props.get("callee"), Some(&Json::str("$display")));
        assert!(g.has_node("unresolved::$display"));
    }

    #[test]
    fn parameter_and_define_are_constants() {
        let g = graph_for("`define WIDTH 8\nmodule m;\n  localparam int N = 4;\nendmodule");
        let consts: Vec<&str> = g
            .nodes()
            .filter(|n| n.kind == ont::CONSTANT)
            .map(|n| n.name.as_str())
            .collect();
        assert!(consts.contains(&"WIDTH"), "`define → Constant: {consts:?}");
        assert!(consts.contains(&"N"), "localparam → Constant: {consts:?}");
    }

    #[test]
    fn include_and_import_create_dependencies() {
        let g = graph_for("`include \"defs.vh\"\nmodule m;\n  import pkg::*;\nendmodule");
        assert!(g.has_node("ext::defs.vh"), "include → ExternalDependency");
        assert!(g.has_node("ext::pkg"), "import → ExternalDependency");
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
        assert!(g.edges().any(|e| e.kind == edge::DEPENDS_ON));
    }

    #[test]
    fn output_is_deterministic() {
        let src = "module sub(input a); endmodule\nmodule top; sub u(.a(b)); function int f(); return g(); endfunction endmodule\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
