//! Lower the VHDL CST into the canonical graph.
//!
//! This mirrors the Verilog and Ada lowerings — the same conservative principles
//! and the same shared ontology — adapted to VHDL's surface. The honest mapping
//! is:
//!
//!   - `entity` → [`Type`] (`type_kind: entity`) and `architecture` → [`Type`]
//!     (`type_kind: architecture`). An entity is a declared hardware interface and
//!     an architecture is a declared implementation; modelling both as `Type`
//!     keeps them first-class declared nodes that instantiations resolve to. An
//!     `architecture A of E` additionally [`IMPLEMENTS`] the entity `E` (resolved
//!     by name when unique, else an explicit [`UnresolvedSymbol`]).
//!   - `package` / `package body` → [`Module`] (a namespace scope). A subprogram
//!     declared directly inside a package is additionally [`HAS_METHOD`] of the
//!     package module and flagged `is_method`.
//!   - `function` / `procedure` → [`Function`].
//!   - `component` → [`Type`] (`type_kind: component`) — a local placeholder an
//!     instantiation can bind to.
//!   - `type` / `subtype` → [`Type`] (distinguished by `type_kind`).
//!   - `constant` → [`Constant`].
//!   - `library X;` and `use X.Y.all;` → [`IMPORTS`] (+ an [`ExternalDependency`]
//!     and a package `DEPENDS_ON`), unless the named unit matches a `Module` built
//!     in this batch, in which case the import is internal.
//!   - component / entity **instantiation** `lbl : C port map (…)` /
//!     `lbl : entity work.E port map (…)` → [`CALLS`] to the bound component/entity
//!     type (resolved by name, ambiguity preserved). A subprogram **call**
//!     `name (…)` → [`CALLS`] only when `name` resolves to a known project
//!     subprogram — the call-vs-array-index/type-conversion ambiguity is never
//!     guessed (the Ada/Fortran rule), so calls into libraries produce no edge.
//!
//! What has no honest home: `signal` / `variable` / `file` / `alias` /
//! `attribute` declarations are structure, not definitions or edges — they are
//! noted (their declaration nodes are walked for the calls they contain) but emit
//! no node of their own. `process` / `block` / `generate` concurrent statements
//! live in the architecture's flat statement region and are scanned for the
//! instantiations and calls they contain. Everything comes from real tokens on
//! the lossless tree; nothing is guessed.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::vhdl::lexer::{is_keyword, kind as tk};
use crate::lang::vhdl::parser::node as cst;

/// Lower a whole project's worth of VHDL files into a graph. `manifest_deps` is
/// unused (VHDL has no manifest the pipeline reads); dependencies are discovered
/// from `library`/`use` clauses instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    let mut local_roots: BTreeSet<String> = BTreeSet::new();
    local_roots.insert(package.to_ascii_lowercase());
    // `work` is VHDL's name for the current library — always local.
    local_roots.insert("work".to_string());
    for f in files {
        for seg in &f.module_path {
            local_roots.insert(seg.to_ascii_lowercase());
        }
    }

    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        local_roots,
        local_packages: BTreeSet::new(),
        fn_by_name: BTreeMap::new(),
        component_by_name: BTreeMap::new(),
        entity_by_name: BTreeMap::new(),
        pend_impls: Vec::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("vhdl"))],
    );

    // Pass B: definition nodes + structural edges; build symbol tables.
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
                ("language", Json::str("vhdl")),
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

    // Pass C: resolve architecture→entity links, calls, and instantiations.
    lo.resolve_implements();
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
    /// Lowercased simple name → function/procedure node ids.
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// Lowercased simple name → component type ids (direct-instantiation targets).
    component_by_name: BTreeMap<String, Vec<String>>,
    /// Lowercased simple name → entity type ids (entity-instantiation +
    /// architecture `IMPLEMENTS` targets).
    entity_by_name: BTreeMap<String, Vec<String>>,
    /// `architecture A of E` links, resolved in pass C once every entity exists.
    pend_impls: Vec<PendImpl>,
}

struct PendingScope<'a> {
    id: String,
    source: &'a str,
    body: &'a Node,
    /// Architecture statement regions scan for instantiations; subprogram bodies
    /// do not.
    scan_insts: bool,
}

/// A pending `architecture A of E` → `E` implements link, resolved in pass C.
struct PendImpl {
    arch_id: String,
    entity_name: String,
}

/// A detected subprogram-call reference site (`name (…)`).
struct Ref {
    name: String,
}

/// How an instantiation names its bound design unit — this picks the symbol table
/// the unit name resolves against.
#[derive(Clone, Copy, PartialEq, Eq)]
enum InstForm {
    /// `lbl : comp port map (…)` — a direct component instantiation.
    Direct,
    /// `lbl : entity work.E …` — an entity instantiation.
    Entity,
    /// `lbl : configuration cfg …` — a configuration instantiation.
    Config,
}

/// A detected component/entity instantiation (`lbl : unit … port map (…)`).
struct Inst {
    unit: String,
    form: InstForm,
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
            acc.push(seg.to_ascii_lowercase());
            let id = format!("mod::{}", acc.join("."));
            self.g.upsert_node(
                id.clone(),
                ont::MODULE,
                seg.clone(),
                vec![("language", Json::str("vhdl"))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    /// Walk an item container, creating definition nodes and recursing. `owner`
    /// carries the enclosing package (module id, name) so its direct subprogram
    /// members get `HAS_METHOD`.
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
                cst::ENTITY => self.handle_entity(
                    item,
                    file_id,
                    container_id,
                    module_join,
                    scope,
                    src,
                    li,
                    pend,
                ),
                cst::ARCHITECTURE => self.handle_architecture(
                    item,
                    file_id,
                    container_id,
                    module_join,
                    scope,
                    src,
                    li,
                    pend,
                ),
                cst::PACKAGE => self.handle_package(
                    item,
                    file_id,
                    container_id,
                    module_join,
                    scope,
                    src,
                    li,
                    pend,
                ),
                cst::FUNCTION | cst::PROCEDURE => self.handle_subprogram(
                    item,
                    file_id,
                    container_id,
                    module_join,
                    scope,
                    owner,
                    src,
                    li,
                    pend,
                ),
                cst::COMPONENT => {
                    self.handle_component(item, container_id, module_join, scope, src, li)
                }
                cst::TYPE_DECL | cst::SUBTYPE_DECL => {
                    self.handle_type(item, container_id, module_join, scope, src, li)
                }
                cst::CONSTANT_DECL => {
                    self.handle_constant(item, container_id, module_join, scope, src, li)
                }
                cst::LIBRARY_CLAUSE => self.handle_library(item, file_id, src),
                cst::USE_CLAUSE => self.handle_use(item, file_id, src),
                // Not new naming scopes, but may hold nested clauses / definitions.
                cst::CONTEXT | cst::CONFIGURATION => self.walk(
                    item,
                    file_id,
                    container_id,
                    module_join,
                    scope,
                    owner,
                    src,
                    li,
                    pend,
                ),
                _ => {}
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_entity<'a>(
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
        let qual = qual_lc(module_join, scope, &name);
        let id = format!("type::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str("entity")),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("vhdl")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
            ],
        );
        self.g
            .add_edge(container_id, edge::DECLARES, id.clone(), vec![]);
        self.entity_by_name
            .entry(name.to_ascii_lowercase())
            .or_default()
            .push(id.clone());

        // Nested declarations are first-class; the (passive) statement region is
        // scanned for calls only (no instantiations in an entity).
        let mut child_scope = scope.to_vec();
        child_scope.push(name);
        self.walk(
            item,
            file_id,
            &id,
            module_join,
            &child_scope,
            None,
            src,
            li,
            pend,
        );
        if let Some(body) = item.child(cst::BLOCK) {
            pend.push(PendingScope {
                id,
                source: src,
                body,
                scan_insts: false,
            });
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_architecture<'a>(
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
        let mut names = item.children_of(cst::NAME);
        let arch_name = names
            .next()
            .and_then(|n| n.tokens().next())
            .map(|t| t.span.text(src).to_string())
            .unwrap_or_else(|| "<anonymous>".to_string());
        let entity_name = names
            .next()
            .and_then(|n| n.tokens().next())
            .map(|t| t.span.text(src).to_string());
        let line = li.line_col(name_start(item)).line;
        let qual = qual_lc(module_join, scope, &arch_name);
        let id = format!("type::arch::{qual}");
        let mut props = vec![
            ("type_kind", Json::str("architecture")),
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("vhdl")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
        ];
        if let Some(e) = &entity_name {
            props.push(("of_entity", Json::str(e.clone())));
        }
        self.g
            .upsert_node(id.clone(), ont::TYPE, arch_name.clone(), props);
        self.g
            .add_edge(container_id, edge::DECLARES, id.clone(), vec![]);

        if let Some(e) = entity_name {
            self.pend_impls.push(PendImpl {
                arch_id: id.clone(),
                entity_name: e,
            });
        }

        let mut child_scope = scope.to_vec();
        child_scope.push(arch_name);
        self.walk(
            item,
            file_id,
            &id,
            module_join,
            &child_scope,
            None,
            src,
            li,
            pend,
        );
        if let Some(body) = item.child(cst::BLOCK) {
            pend.push(PendingScope {
                id,
                source: src,
                body,
                scan_insts: true,
            });
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_package<'a>(
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
        let is_body = item
            .tokens()
            .any(|t| t.span.text(src).eq_ignore_ascii_case("body"));
        let qual = qual_lc(module_join, scope, &name);
        let id = format!("mod::pkg::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::MODULE,
            name.clone(),
            vec![
                (
                    "module_kind",
                    Json::str(if is_body { "package_body" } else { "package" }),
                ),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("vhdl")),
            ],
        );
        self.g
            .add_edge(container_id, edge::CONTAINS, id.clone(), vec![]);
        self.local_packages.insert(name.to_ascii_lowercase());

        let owner = (id.clone(), name.clone());
        let mut child_scope = scope.to_vec();
        child_scope.push(name);
        self.walk(
            item,
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

    #[allow(clippy::too_many_arguments)]
    fn handle_subprogram<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        container_id: &str,
        module_join: &str,
        scope: &[String],
        owner: Option<&(String, String)>,
        src: &'a str,
        li: &LineIndex,
        pend: &mut Vec<PendingScope<'a>>,
    ) {
        let name = simple_name(item, src).unwrap_or_else(|| "<anonymous>".to_string());
        let line = li.line_col(name_start(item)).line;
        let qual = qual_lc(module_join, scope, &name);
        let id = format!("fn::{qual}#{line}");
        let has_body = item.child(cst::BLOCK).is_some();
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("vhdl")),
            (
                "subprogram_kind",
                Json::str(if item.kind == cst::PROCEDURE {
                    "procedure"
                } else {
                    "function"
                }),
            ),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            ("has_body", Json::Bool(has_body)),
        ];
        if item.kind == cst::PROCEDURE {
            props.push(("returns", Json::str("void")));
        }
        if let Some((_, owner_name)) = owner {
            props.push(("receiver_type", Json::str(owner_name.clone())));
            props.push(("is_method", Json::Bool(true)));
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, name.clone(), props);
        self.g
            .add_edge(container_id, edge::DECLARES, id.clone(), vec![]);
        self.fn_by_name
            .entry(name.to_ascii_lowercase())
            .or_default()
            .push(id.clone());

        if let Some((owner_id, _)) = owner {
            self.g
                .add_edge(owner_id.clone(), edge::HAS_METHOD, id.clone(), vec![]);
        }

        // Nested declarations (the subprogram's declarative part) are first-class,
        // scoped under this subprogram. They are not package methods, so descend
        // with no owner.
        let mut child_scope = scope.to_vec();
        child_scope.push(name);
        self.walk(
            item,
            file_id,
            &id,
            module_join,
            &child_scope,
            None,
            src,
            li,
            pend,
        );
        if let Some(body) = item.child(cst::BLOCK) {
            pend.push(PendingScope {
                id,
                source: src,
                body,
                scan_insts: false,
            });
        }
    }

    fn handle_component(
        &mut self,
        item: &Node,
        container_id: &str,
        module_join: &str,
        scope: &[String],
        src: &str,
        li: &LineIndex,
    ) {
        let name = simple_name(item, src).unwrap_or_else(|| "<anonymous>".to_string());
        let line = li.line_col(name_start(item)).line;
        let qual = qual_lc(module_join, scope, &name);
        let id = format!("type::comp::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str("component")),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("vhdl")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
            ],
        );
        self.g
            .add_edge(container_id, edge::DECLARES, id.clone(), vec![]);
        self.component_by_name
            .entry(name.to_ascii_lowercase())
            .or_default()
            .push(id);
    }

    fn handle_type(
        &mut self,
        item: &Node,
        container_id: &str,
        module_join: &str,
        scope: &[String],
        src: &str,
        li: &LineIndex,
    ) {
        let name = simple_name(item, src).unwrap_or_else(|| "<anonymous>".to_string());
        let line = li.line_col(name_start(item)).line;
        let qual = qual_lc(module_join, scope, &name);
        let id = format!("type::{qual}");
        let type_kind = if item.kind == cst::SUBTYPE_DECL {
            "subtype"
        } else {
            "type"
        };
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name,
            vec![
                ("type_kind", Json::str(type_kind)),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("vhdl")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
            ],
        );
        self.g.add_edge(container_id, edge::DECLARES, id, vec![]);
    }

    fn handle_constant(
        &mut self,
        item: &Node,
        container_id: &str,
        module_join: &str,
        scope: &[String],
        src: &str,
        li: &LineIndex,
    ) {
        let line = li.line_col(item.span.start).line;
        for name in constant_names(item, src) {
            let qual = qual_lc(module_join, scope, &name);
            let id = format!("const::{qual}");
            self.g.upsert_node(
                id.clone(),
                ont::CONSTANT,
                name,
                vec![
                    ("binding", Json::str("constant")),
                    ("language", Json::str("vhdl")),
                    ("line", Json::U64(line as u64)),
                ],
            );
            self.g.add_edge(container_id, edge::DECLARES, id, vec![]);
        }
    }

    // --- imports ------------------------------------------------------------

    fn handle_library(&mut self, item: &Node, file_id: &str, src: &str) {
        // `library a, b, c;` — each name is an external dependency (a design
        // library), unless it is the current/local library.
        for lib in clause_names(item, src) {
            let lc = lib.to_ascii_lowercase();
            if self.local_roots.contains(&lc) {
                continue; // the working library is not an external dependency
            }
            self.emit_external_import(file_id, &lib, "library");
        }
    }

    fn handle_use(&mut self, item: &Node, file_id: &str, src: &str) {
        // `use lib.pkg.all;` / `use lib.pkg.name;` — record the `lib.pkg` prefix as
        // the imported unit (the trailing `.all` / selected name is dropped).
        let full = match use_unit_name(item, src) {
            Some(u) => u,
            None => return,
        };
        let full_lc = full.to_ascii_lowercase();
        let root = full_lc.split('.').next().unwrap_or(&full_lc).to_string();
        let last = full_lc.rsplit('.').next().unwrap_or(&full_lc).to_string();
        // Internal if the prefix names a local package, or the library is local.
        let internal = self.local_packages.contains(&last)
            || self.local_packages.contains(&root)
            || self.local_roots.contains(&root);
        if internal {
            let id = format!("mod::use::{full_lc}");
            self.g.upsert_node(
                id.clone(),
                ont::MODULE,
                full.clone(),
                vec![("language", Json::str("vhdl"))],
            );
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                id,
                vec![("path", Json::str(full)), ("external", Json::Bool(false))],
            );
        } else {
            self.emit_external_import(file_id, &full, "use");
        }
    }

    fn emit_external_import(&mut self, file_id: &str, name: &str, source: &str) {
        let dep_id = format!("ext::{name}");
        self.g.upsert_node(
            dep_id.clone(),
            ont::EXTERNAL_DEPENDENCY,
            name.to_string(),
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
                ("path", Json::str(name.to_string())),
                ("external", Json::Bool(true)),
            ],
        );
        self.g
            .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
    }

    // --- architecture → entity resolution -----------------------------------

    fn resolve_implements(&mut self) {
        // Collected during pass B; drained here once every entity exists.
        let pend = std::mem::take(&mut self.pend_impls);
        for pi in pend {
            let cands = self
                .entity_by_name
                .get(&pi.entity_name.to_ascii_lowercase())
                .cloned()
                .unwrap_or_default();
            match cands.len() {
                1 => {
                    self.g.add_edge(
                        pi.arch_id,
                        edge::IMPLEMENTS,
                        cands[0].clone(),
                        vec![("entity_name", Json::str(pi.entity_name))],
                    );
                }
                0 => {
                    let target = format!("unresolved::{}", pi.entity_name.to_ascii_lowercase());
                    self.ensure_unresolved(&target, &pi.entity_name, "entity");
                    self.g.add_edge(
                        pi.arch_id,
                        edge::IMPLEMENTS,
                        target,
                        vec![
                            ("entity_name", Json::str(pi.entity_name)),
                            ("resolved", Json::Bool(false)),
                        ],
                    );
                }
                n => {
                    let target = format!("unresolved::{}", pi.entity_name.to_ascii_lowercase());
                    self.ensure_unresolved(&target, &pi.entity_name, "entity");
                    self.g.add_edge(
                        pi.arch_id,
                        edge::IMPLEMENTS,
                        target,
                        vec![
                            ("entity_name", Json::str(pi.entity_name)),
                            ("resolved", Json::Bool(false)),
                            ("ambiguous", Json::Bool(true)),
                            ("candidate_count", Json::U64(n as u64)),
                            (
                                "candidates",
                                Json::Array(cands.into_iter().map(Json::Str).collect()),
                            ),
                        ],
                    );
                }
            }
        }
    }

    // --- call / instantiation resolution ------------------------------------

    /// Emit a `CALLS` edge for `name (…)` **only** when the name resolves to a
    /// known project subprogram — the conservative signal that distinguishes a
    /// call from array indexing / a type conversion / a library call (never
    /// fabricated). Ambiguity across project subprograms is preserved.
    fn emit_call(&mut self, caller_id: &str, call: &Ref) {
        let cands = self
            .fn_by_name
            .get(&call.name.to_ascii_lowercase())
            .cloned()
            .unwrap_or_default();
        let mut props = vec![
            ("callee", Json::str(call.name.clone())),
            ("method", Json::Bool(false)),
        ];
        match cands.len() {
            0 => {} // unresolved → not a project call; emit nothing.
            1 => {
                props.push(("resolution", Json::str("global")));
                props.push(("resolved", Json::Bool(true)));
                props.push(("candidate_count", Json::U64(1)));
                self.g
                    .add_edge(caller_id, edge::CALLS, cands[0].clone(), props);
            }
            n => {
                let target = format!("unresolved::{}", call.name.to_ascii_lowercase());
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
        let key = inst.unit.to_ascii_lowercase();
        // A direct instantiation binds to a component; if none exists, VHDL's
        // default-binding rule falls back to an entity of the same name. Entity /
        // configuration forms resolve against entities directly.
        let cands = match inst.form {
            InstForm::Direct => {
                let c = self
                    .component_by_name
                    .get(&key)
                    .cloned()
                    .unwrap_or_default();
                if c.is_empty() {
                    self.entity_by_name.get(&key).cloned().unwrap_or_default()
                } else {
                    c
                }
            }
            InstForm::Entity | InstForm::Config => {
                self.entity_by_name.get(&key).cloned().unwrap_or_default()
            }
        };
        let form = match inst.form {
            InstForm::Direct => "component",
            InstForm::Entity => "entity",
            InstForm::Config => "configuration",
        };
        let mut props = vec![
            ("callee", Json::str(inst.unit.clone())),
            ("kind", Json::str("instantiation")),
            ("form", Json::str(form)),
        ];
        match cands.len() {
            1 => {
                props.push(("resolution", Json::str("unit")));
                props.push(("resolved", Json::Bool(true)));
                props.push(("candidate_count", Json::U64(1)));
                self.g
                    .add_edge(caller_id, edge::CALLS, cands[0].clone(), props);
            }
            0 => {
                let target = format!("unresolved::{}", inst.unit.to_ascii_lowercase());
                self.ensure_unresolved(&target, &inst.unit, "instantiation");
                props.push(("resolution", Json::str("external")));
                props.push(("resolved", Json::Bool(false)));
                props.push(("candidate_count", Json::U64(0)));
                self.g.add_edge(caller_id, edge::CALLS, target, props);
            }
            n => {
                let target = format!("unresolved::{}", inst.unit.to_ascii_lowercase());
                self.ensure_unresolved(&target, &inst.unit, "instantiation");
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
    path.iter()
        .map(|s| s.to_ascii_lowercase())
        .collect::<Vec<_>>()
        .join(".")
}

fn qual_lc(module_join: &str, scope: &[String], name: &str) -> String {
    let mut parts: Vec<String> = Vec::new();
    if !module_join.is_empty() {
        parts.push(module_join.to_string());
    }
    parts.extend(scope.iter().map(|s| s.to_ascii_lowercase()));
    if !name.is_empty() {
        parts.push(name.to_ascii_lowercase());
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

/// The `Name` child of a definition (entity/package/component/type/subprogram).
fn simple_name(item: &Node, src: &str) -> Option<String> {
    let nm = item.child(cst::NAME)?;
    nm.tokens().next().map(|t| t.span.text(src).to_string())
}

/// Byte offset used for a definition's line number: the first `Name` token.
fn name_start(item: &Node) -> u32 {
    item.child(cst::NAME)
        .map(|n| n.span.start)
        .unwrap_or(item.span.start)
}

/// The declared object names of a `constant N [, N]* : T …;` — the identifiers
/// before the first `:` that is not `:=`.
fn constant_names(item: &Node, src: &str) -> Vec<String> {
    let mut names = Vec::new();
    for c in &item.children {
        let t = match c {
            Child::Token(t) if !t.trivia => t,
            _ => continue,
        };
        let text = t.span.text(src);
        if text == ":" {
            break;
        }
        if t.kind == tk::IDENT && !is_keyword(text) {
            names.push(text.to_string());
        }
    }
    names
}

/// The library names in a `library a, b;` clause (comma-separated identifiers
/// after the `library` keyword).
fn clause_names(item: &Node, src: &str) -> Vec<String> {
    let mut names = Vec::new();
    for t in item.tokens() {
        let text = t.span.text(src);
        if t.kind == tk::IDENT && !text.eq_ignore_ascii_case("library") {
            names.push(text.to_string());
        }
    }
    names
}

/// The `lib.pkg` unit prefix of a `use lib.pkg.all;` / `use lib.pkg.name;` clause
/// (everything but the keyword, the trailing `.all`, and the final selected name).
fn use_unit_name(item: &Node, src: &str) -> Option<String> {
    // Build the dotted path of identifiers (skipping the `use` keyword), then drop
    // the final segment (`all` or a selected declaration name) to leave `lib.pkg`.
    let mut segs: Vec<String> = Vec::new();
    for t in item.tokens() {
        let text = t.span.text(src);
        if text == ";" || text == "," {
            break; // first named unit only
        }
        if t.kind == tk::IDENT {
            if text.eq_ignore_ascii_case("use") {
                continue;
            }
            segs.push(text.to_string());
        }
    }
    if segs.len() >= 2 {
        segs.pop(); // drop `all` / selected name
    }
    if segs.is_empty() {
        None
    } else {
        Some(segs.join("."))
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

fn el_text<'a>(e: &El<'a>) -> Option<&'a str> {
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
        cst::ENTITY
            | cst::ARCHITECTURE
            | cst::PACKAGE
            | cst::CONFIGURATION
            | cst::CONTEXT
            | cst::FUNCTION
            | cst::PROCEDURE
            | cst::COMPONENT
    )
}

/// True if a `map` keyword appears in `els[from..]` before the statement's
/// terminating `;` at this level — the signature that `els[from-2..]` is a
/// component/entity instantiation rather than some other labelled statement.
fn has_map_before_semicolon(els: &[El], from: usize) -> bool {
    let mut k = from;
    while k < els.len() {
        if let Some(t) = el_text(&els[k]) {
            if t == ";" {
                return false;
            }
            if t.eq_ignore_ascii_case("map") {
                return true;
            }
        }
        k += 1;
    }
    false
}

/// Detect reference sites over the real token tree:
///   - `lbl : entity lib.E …` / `lbl : component C …` / `lbl : configuration …`
///     → an instantiation of the named unit.
///   - `lbl : C … port map (…)` (direct component instantiation).
///   - `name (…)` (bare, not after `.` or attribute `'`) → a subprogram call.
///
/// Instantiations are detected only when `scan_insts` (an architecture statement
/// region) and only at the top level (not inside parens, where `scan_insts` is
/// cleared on recursion). Recurses into groups and nested non-definition nodes.
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
        // Instantiation: IDENT(label) ':' …
        if scan_insts
            && el_is_ident(&els[i])
            && i + 1 < n
            && el_text(&els[i + 1]) == Some(":")
            && i + 2 < n
        {
            let after = &els[i + 2];
            if let Some(kw) = el_text(after) {
                let form = if kw.eq_ignore_ascii_case("entity") {
                    Some(InstForm::Entity)
                } else if kw.eq_ignore_ascii_case("component") {
                    Some(InstForm::Direct)
                } else if kw.eq_ignore_ascii_case("configuration") {
                    Some(InstForm::Config)
                } else {
                    None
                };
                if let Some(form) = form {
                    // Read the (possibly dotted) unit name after the keyword.
                    let mut j = i + 3;
                    let mut unit: Option<String> = None;
                    while j < n && el_is_ident(&els[j]) {
                        unit = el_text(&els[j]).map(|s| s.to_string());
                        if j + 1 < n && el_text(&els[j + 1]) == Some(".") {
                            j += 2;
                        } else {
                            j += 1;
                            break;
                        }
                    }
                    if let Some(u) = unit {
                        insts.push(Inst { unit: u, form });
                    }
                    i = j;
                    continue;
                }
                // Direct instantiation: `lbl : comp … port map (…)`.
                if el_is_ident(after) && !is_keyword(kw) && has_map_before_semicolon(&els, i + 3) {
                    insts.push(Inst {
                        unit: kw.to_string(),
                        form: InstForm::Direct,
                    });
                    i += 3;
                    continue;
                }
            }
        }

        // Subprogram call: IDENT(…) not after `.` / attribute `'`.
        if el_is_ident(&els[i]) {
            let name = el_text(&els[i]).unwrap_or("");
            let prev = if i > 0 { el_text(&els[i - 1]) } else { None };
            let after_sel = matches!(prev, Some(".") | Some("'"));
            if !after_sel && !is_keyword(name) && i + 1 < n && el_is_paren(&els[i + 1]) {
                calls.push(Ref {
                    name: name.to_string(),
                });
            }
        }
        i += 1;
    }

    for e in &els {
        if let El::Grp(g) = e {
            if !is_def_node(g.kind) {
                // Instantiations never occur inside parens; clear the flag so a
                // `x : y` inside an expression cannot be misread as one.
                scan_refs(g, false, src, calls, insts);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::vhdl::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("top.vhd", src);
        let file = SourceFile {
            rel_path: "top.vhd".to_string(),
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
    fn entity_and_architecture_become_types() {
        let g = graph_for(
            "entity counter is end entity;\narchitecture rtl of counter is begin end rtl;\n",
        );
        let ent = g
            .nodes()
            .find(|n| n.kind == ont::TYPE && n.name == "counter")
            .expect("entity Type");
        assert_eq!(ent.props.get("type_kind"), Some(&Json::str("entity")));
        let arch = g
            .nodes()
            .find(|n| n.kind == ont::TYPE && n.name == "rtl")
            .expect("architecture Type");
        assert_eq!(
            arch.props.get("type_kind"),
            Some(&Json::str("architecture"))
        );
        // architecture implements the entity.
        assert!(g
            .edges()
            .any(|e| e.kind == edge::IMPLEMENTS && e.to == ent.id));
    }

    #[test]
    fn package_subprograms_are_methods() {
        let g = graph_for(
            "package p is\n   function inc (x : integer) return integer;\nend package;\n\
             package body p is\n   function inc (x : integer) return integer is\n   begin\n      \
             return x + 1;\n   end inc;\nend package body;\n",
        );
        assert!(g.nodes().any(|n| n.kind == ont::MODULE && n.name == "p"));
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::FUNCTION && n.name == "inc"));
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD));
    }

    #[test]
    fn type_subtype_constant() {
        let g = graph_for(
            "package p is\n   type state is (idle, busy);\n   subtype byte is bit_vector(7 downto 0);\n   \
             constant VERSION : integer := 2;\nend package;\n",
        );
        assert!(g.nodes().any(|n| n.kind == ont::TYPE && n.name == "state"));
        assert!(g.nodes().any(|n| n.kind == ont::TYPE && n.name == "byte"));
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::CONSTANT && n.name == "VERSION"));
    }

    #[test]
    fn instantiation_resolves_to_component() {
        let g = graph_for(
            "entity sub is end entity;\narchitecture a of top is\n   component sub is end component;\n\
             begin\n   u_sub : sub port map (a => x, y => z);\nend a;\n",
        );
        let inst = call_edges(&g)
            .into_iter()
            .find(|e| e.props.get("kind") == Some(&Json::str("instantiation")))
            .expect("an instantiation CALLS edge");
        assert_eq!(inst.props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn entity_instantiation_resolves() {
        let g = graph_for(
            "entity sub is end entity;\narchitecture a of top is\nbegin\n   \
             u : entity work.sub port map (clk => clk);\nend a;\n",
        );
        let inst = call_edges(&g)
            .into_iter()
            .find(|e| e.props.get("kind") == Some(&Json::str("instantiation")))
            .expect("an instantiation CALLS edge");
        assert_eq!(inst.props.get("callee"), Some(&Json::str("sub")));
        assert_eq!(inst.props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn subprogram_call_resolves_and_index_does_not() {
        let g = graph_for(
            "package body p is\n   function f (x : integer) return integer is begin return x; end f;\n   \
             function g (y : integer) return integer is\n      variable arr : bit_vector(0 to 3);\n   \
             begin\n      arr(0) := '0';\n      return f(y);\n   end g;\nend package body;\n",
        );
        let calls = call_edges(&g);
        let f = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("f")))
            .expect("a resolved call to f");
        assert_eq!(f.props.get("resolved"), Some(&Json::Bool(true)));
        // `arr(0)` resolves to no subprogram → no fabricated CALLS edge.
        assert!(
            !calls
                .iter()
                .any(|e| e.props.get("callee") == Some(&Json::str("arr"))),
            "array indexing must not become a CALLS edge"
        );
    }

    #[test]
    fn library_and_use_create_dependencies() {
        let g = graph_for("library ieee;\nuse ieee.std_logic_1164.all;\nentity e is end entity;\n");
        assert!(g.has_node("ext::ieee"), "library → ExternalDependency");
        assert!(
            g.has_node("ext::ieee.std_logic_1164"),
            "use → ExternalDependency"
        );
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
        assert!(g.edges().any(|e| e.kind == edge::DEPENDS_ON));
    }

    #[test]
    fn output_is_deterministic() {
        let src = "entity sub is end entity;\narchitecture a of top is\n   component sub is end component;\n\
                   begin\n   u : sub port map (a => b);\nend a;\n";
        let first = graph_for(src).to_jsonl();
        let second = graph_for(src).to_jsonl();
        assert_eq!(
            first, second,
            "graph output must be byte-identical across runs"
        );
    }
}
