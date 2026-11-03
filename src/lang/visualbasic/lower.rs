//! Lower the VB.NET CST into the canonical graph.
//!
//! This mirrors the C# lowering ([`crate::lang::csharp::lower`]) — same
//! conservative principles, same shared ontology — adapted to VB.NET's surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to
//!    a concrete project definition only when a scope level yields exactly one
//!    candidate; several candidates become an ambiguous edge carrying the full
//!    `candidates` set; none resolves to an explicit `UnresolvedSymbol`.
//! 2. **Everything comes from real tokens.** Calls, base lists, imports, and type
//!    uses are read off the lossless tree, never guessed.
//!
//! Honest mappings (see the IR Atlas):
//!   * `Namespace` and `Module` → `Module` (a scope). A VB `Module` is a static
//!     container, *not* a type, so its `Sub`/`Function` members are module-level
//!     functions with no `HAS_METHOD` edge.
//!   * `Class`/`Structure`/`Interface`/`Enum`/`Delegate` → `Type` with an apt
//!     `type_kind`.
//!   * `Sub`/`Function`/`Operator`/`Declare` → `Function`; one declared inside a
//!     type gets a `HAS_METHOD` edge from that type.
//!   * `Property`/`Const`/`Dim`/field/`Event` at type or module scope → `Constant`
//!     with a `binding` property (`property`, `const`, `field`, `event`). VB has no
//!     dedicated field/property IR node; `Constant` ("a value binding") is the
//!     closest existing kind. We do not fabricate an edge kind for it.
//!   * `Inherits X` → `EXTENDS`; `Implements X` → `IMPLEMENTS`.
//!   * `Imports X` → `IMPORTS` (plus `ExternalDependency`/`DEPENDS_ON` for
//!     non-project roots).
//!
//! Resolution uses a deterministic **scope ladder** (most specific first): for a
//! `Me`/`MyBase` member call, the enclosing type's methods; for a bare call, the
//! enclosing type's methods then any project function of that name; for any other
//! receiver, project methods of that name (ambiguity preserved).
//!
//! Honest punts: VB array indexing (`arr(i)`) is lexically identical to a call,
//! so it is detected as a `CALLS` candidate and falls through to `external` when
//! unresolved; `New Foo()` resolves to a function named `Foo`, but VB constructors
//! are named `New`, so a constructor call typically stays `external`.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::visualbasic::lexer::{is_keyword, kind as tk};
use crate::lang::visualbasic::parser::node as cst;

const LANG: &str = "vbnet";

/// Lower a whole project's worth of VB.NET files into a graph. `manifest_deps` is
/// unused (the pipeline's manifest reader is Cargo-only); dependencies are
/// discovered from `Imports` directives instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    // Project-local namespace roots: the package plus the first segment of every
    // declared namespace. An `Imports` whose first segment is one of these is an
    // intra-project import, not an external dependency.
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
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("dotnet"))],
    );

    // Pass B: definition nodes + structural edges + symbol tables. Inheritance
    // and call/type resolution are deferred to pass C so a base type or callee
    // defined later in the project still resolves.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_bases: Vec<PendingBase> = Vec::new();
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
            &mut pend_bases,
            &mut pend_type_uses,
        );
    }

    // Pass C: resolve calls, type usages, and inheritance.
    for pf in &pend_fns {
        if let Some(block) = pf.block {
            let mut calls = Vec::new();
            scan_calls(block, pf.source, &mut calls);
            for call in &calls {
                let res = lo.resolve(call, pf.owner_type.as_deref());
                lo.emit_call(&pf.id, call, res);
            }
        }
    }
    for entry in &pend_type_uses {
        lo.emit_type_uses(&entry.0, entry.1, entry.2);
    }
    for pb in &pend_bases {
        lo.emit_base(pb);
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    local_roots: BTreeSet<String>,
    fn_by_name: BTreeMap<String, Vec<String>>,
    method_by_name: BTreeMap<String, Vec<String>>,
    method_by_type: BTreeMap<(String, String), Vec<String>>,
    type_by_name: BTreeMap<String, Vec<String>>,
    type_kind_by_id: BTreeMap<String, &'static str>,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    block: Option<&'a Node>,
    owner_type: Option<String>,
}

/// A deferred base-type link, resolved into `EXTENDS`/`IMPLEMENTS` in pass C.
/// `is_interface` records whether the clause was `Implements` (true) or
/// `Inherits` (false) — VB states this explicitly, no naming heuristic needed.
struct PendingBase {
    type_id: String,
    base_name: String,
    is_interface: bool,
}

/// The enclosing type while walking (for methods' `HAS_METHOD` + receiver scope,
/// and for `Inherits`/`Implements` statements). `None` inside a Module/Namespace.
struct Owner {
    name: String,
    id: String,
}

struct Call {
    name: String,
    method: bool,
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
        pend_bases: &mut Vec<PendingBase>,
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
                    pend_bases,
                    pend_type_uses,
                ),
                cst::MODULE => self.handle_module(
                    item,
                    file_id,
                    ns_join,
                    module_id,
                    scope,
                    src,
                    li,
                    pend_fns,
                    pend_bases,
                    pend_type_uses,
                ),
                cst::CLASS | cst::STRUCTURE | cst::INTERFACE | cst::ENUM | cst::DELEGATE => self
                    .handle_type(
                        item,
                        file_id,
                        ns_join,
                        module_id,
                        scope,
                        src,
                        li,
                        pend_fns,
                        pend_bases,
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
                cst::FIELD | cst::PROPERTY | cst::EVENT => {
                    self.handle_field(item, file_id, ns_join, scope, src, li, pend_type_uses)
                }
                cst::IMPORTS => self.handle_imports(item, file_id, src),
                cst::INHERITS => self.handle_base(item, owner, src, pend_bases, false),
                cst::IMPLEMENTS => self.handle_base(item, owner, src, pend_bases, true),
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
        pend_bases: &mut Vec<PendingBase>,
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
                pend_bases,
                pend_type_uses,
            );
        }
    }

    /// A VB `Module` is a named static scope → a `Module` node (not a `Type`).
    /// Its members are module-level (no `HAS_METHOD`).
    #[allow(clippy::too_many_arguments)]
    fn handle_module<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        ns_join: &str,
        module_id: Option<&str>,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_bases: &mut Vec<PendingBase>,
        pend_type_uses: &mut Vec<(String, &'a Node, &'a str)>,
    ) {
        let name = node_name(item, src).unwrap_or_else(|| "<anonymous>".to_string());
        let qual = qual_name(ns_join, scope, &name);
        let id = format!("mod::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::MODULE,
            name.clone(),
            vec![
                ("language", Json::str(LANG)),
                ("module_kind", Json::str("vb_module")),
                ("qualified_name", Json::str(qual)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        let parent = module_id
            .map(|m| m.to_string())
            .unwrap_or_else(|| self.pkg_id());
        self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
        if let Some(block) = item.child(cst::ITEM_BLOCK) {
            let mut child_scope = scope.to_vec();
            child_scope.push(name);
            self.walk_items(
                block,
                file_id,
                ns_join,
                Some(&id),
                &child_scope,
                None, // a Module is not a type: members are not methods
                src,
                li,
                pend_fns,
                pend_bases,
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
        pend_bases: &mut Vec<PendingBase>,
        pend_type_uses: &mut Vec<(String, &'a Node, &'a str)>,
    ) {
        let name = node_name(item, src).unwrap_or_else(|| "<anonymous>".to_string());
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(ns_join, scope, &name);
        let id = format!("type::{qual}");
        let type_kind = match item.kind {
            cst::CLASS => "class",
            cst::STRUCTURE => "structure",
            cst::INTERFACE => "interface",
            cst::ENUM => "enum",
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

        // A delegate's header carries its signature → type uses.
        if let Some(header) = item.child(cst::HEADER) {
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
                pend_bases,
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
        let name = node_name(item, src).unwrap_or_else(|| "<anonymous>".to_string());
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
        if has_modifier(item, src, "shared") {
            props.push(("is_static", Json::Bool(true)));
        }
        if let Some(o) = owner {
            props.push(("receiver_type", Json::str(o.name.clone())));
            props.push(("is_method", Json::Bool(true)));
            if name.eq_ignore_ascii_case("New") {
                props.push(("is_constructor", Json::Bool(true)));
            }
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, name.clone(), props);
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);

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

        if let Some(h) = item.child(cst::HEADER) {
            pend_type_uses.push((id.clone(), h, src));
        }
        pend_fns.push(PendingFn {
            id,
            source: src,
            block,
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
        let header = item.child(cst::HEADER);
        // Property/Event carry an explicit Name node; a field's name lives in its
        // header (first non-keyword identifier).
        let name = match node_name(item, src) {
            Some(n) => n,
            None => match header.and_then(|h| field_name(h, src)) {
                Some(n) => n,
                None => return,
            },
        };
        let line = li.line_col(item.span.start).line;
        let qual = qual_name(ns_join, scope, &name);
        let id = format!("const::{qual}");
        let binding = match item.kind {
            cst::PROPERTY => "property",
            cst::EVENT => "event",
            _ if has_modifier(item, src, "const") => "const",
            _ => "field",
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
        if let Some(h) = header {
            pend_type_uses.push((id, h, src));
        }
    }

    /// `Imports A.B.C` / `Imports X = A.B` — each names a namespace (or type).
    /// Internal roots become `IMPORTS` to the module; external roots become an
    /// `ExternalDependency` plus a `DEPENDS_ON` edge.
    fn handle_imports(&mut self, item: &Node, file_id: &str, src: &str) {
        let header = match item.child(cst::HEADER) {
            Some(h) => h,
            None => return,
        };
        let toks = top_level_tokens(header, src);
        // `Imports X = A.B` — drop the alias and the `=`.
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
                    ("source", Json::str("imports")),
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

    /// Record an `Inherits`/`Implements` statement against the enclosing type.
    fn handle_base(
        &mut self,
        item: &Node,
        owner: Option<&Owner>,
        src: &str,
        pend_bases: &mut Vec<PendingBase>,
        is_interface: bool,
    ) {
        let owner = match owner {
            Some(o) => o,
            None => return,
        };
        if let Some(header) = item.child(cst::HEADER) {
            for base in base_list(header, src) {
                pend_bases.push(PendingBase {
                    type_id: owner.id.clone(),
                    base_name: base,
                    is_interface,
                });
            }
        }
    }

    // --- resolution ---------------------------------------------------------

    fn resolve(&self, call: &Call, owner_type: Option<&str>) -> Resolution {
        if call.method {
            // `Me.M()` / `MyBase.M()` → enclosing type's methods.
            if matches!(call.receiver.as_deref(), Some(r) if r.eq_ignore_ascii_case("Me") || r.eq_ignore_ascii_case("MyBase") || r.eq_ignore_ascii_case("MyClass"))
            {
                if let Some(owner) = owner_type {
                    let c = self.methods_of(owner, &call.name);
                    if !c.is_empty() {
                        return mk(c, "receiver");
                    }
                }
            }
            // Other receivers have an unknown static type: fall back to a global
            // match among methods only, preserving ambiguity.
            let c = self.global_methods(&call.name);
            return if c.is_empty() {
                external()
            } else {
                mk(c, "global_method")
            };
        }

        // Bare call: an implicit-`Me` method of the enclosing type first.
        if let Some(owner) = owner_type {
            let c = self.methods_of(owner, &call.name);
            if !c.is_empty() {
                return mk(c, "implicit_me");
            }
        }
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

    /// Resolve a deferred base-type link. `Implements` → `IMPLEMENTS`, `Inherits`
    /// → `EXTENDS` (VB states the relationship explicitly). The target is a
    /// concrete project type when unique, else an explicit `UnresolvedSymbol`.
    fn emit_base(&mut self, pb: &PendingBase) {
        let target = match self.unique_type(&pb.base_name) {
            Some(id) => id,
            None => {
                let id = unresolved_id(&pb.base_name);
                self.ensure_unresolved(&id, &pb.base_name, "base_type");
                id
            }
        };
        let edge_kind = if pb.is_interface {
            edge::IMPLEMENTS
        } else {
            edge::EXTENDS
        };
        self.g.add_edge(
            pb.type_id.clone(),
            edge_kind,
            target,
            vec![("base_name", Json::str(pb.base_name.clone()))],
        );
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

// --- pure helpers -----------------------------------------------------------

fn join_ns(parent: &str, child: &str) -> String {
    match (parent.is_empty(), child.is_empty()) {
        (_, true) => parent.to_string(),
        (true, false) => child.to_string(),
        (false, false) => format!("{parent}.{child}"),
    }
}

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

/// Name from a `Name` child node: the joined non-trivia token texts (an
/// identifier, or for a namespace a dotted path).
fn node_name(item: &Node, src: &str) -> Option<String> {
    let nm = item.child(cst::NAME)?;
    let mut s = String::new();
    for t in nm.tokens() {
        s.push_str(t.span.text(src));
    }
    // Strip escaped-identifier brackets if present (`[End]` → `End`).
    let s = s.trim_matches(|c| c == '[' || c == ']').to_string();
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

/// A field's name: the first non-keyword identifier in its header, at angle-depth
/// 0 and before the first `As`/`=`/`(`. (Multiple-declarator lines such as
/// `Dim a, b As Integer` report only the first name — a documented punt.)
fn field_name(header: &Node, src: &str) -> Option<String> {
    let toks = top_level_tokens(header, src);
    for t in &toks {
        if t.text == "(" || t.text == "=" || t.text.eq_ignore_ascii_case("As") {
            break;
        }
        if t.kind == tk::IDENT && !is_keyword(t.text) {
            return Some(t.text.trim_matches(|c| c == '[' || c == ']').to_string());
        }
    }
    None
}

/// Base-type simple names from an `Inherits`/`Implements` clause: each
/// comma-separated base's last non-keyword identifier at angle-depth 0
/// (`List(Of T)` → `List`; `A.B.IFoo` → `IFoo`).
fn base_list(header: &Node, src: &str) -> Vec<String> {
    let toks = top_level_tokens(header, src);
    let mut bases = Vec::new();
    let mut clause_last: Option<String> = None;
    let mut depth = 0i32;
    for t in &toks {
        adjust_paren(&mut depth, t.text);
        if depth == 0 && t.text == "," {
            if let Some(b) = clause_last.take() {
                bases.push(b);
            }
            continue;
        }
        if depth == 0 && t.kind == tk::IDENT && !is_keyword(t.text) {
            clause_last = Some(t.text.trim_matches(|c| c == '[' || c == ']').to_string());
        }
    }
    if let Some(b) = clause_last.take() {
        bases.push(b);
    }
    bases
}

/// Track `(…)` nesting (VB generic arguments use `(Of T)`, so the open-paren is
/// the depth marker, not `<`).
fn adjust_paren(depth: &mut i32, text: &str) {
    match text {
        "(" => *depth += 1,
        ")" => {
            if *depth > 0 {
                *depth -= 1;
            }
        }
        _ => {}
    }
}

fn has_modifier(item: &Node, src: &str, kw: &str) -> bool {
    item.tokens()
        .any(|t| t.span.text(src).eq_ignore_ascii_case(kw))
}

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
/// recursing into nested groups. Keywords (`New`, `If`, `TypeOf`, …) are excluded
/// as callee names. Note (honest): VB array indexing is `arr(i)` — syntactically a
/// call — so it is detected here and resolves to `external` when no project
/// function matches.
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
    for e in &els {
        if let Some(g) = grp(e) {
            scan_calls(g, src, out);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::visualbasic::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("Sample.vb", src);
        let file = SourceFile {
            rel_path: "Sample.vb".to_string(),
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
        let g = graph_for(
            "Namespace App\n Class C\n  Sub M()\n  End Sub\n  Dim F As Integer\n End Class\nEnd Namespace\n",
        );
        assert_eq!(g.count_nodes_of(ont::TYPE), 1, "class C is a Type");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 1, "method M");
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "namespace App");
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 1, "field F");
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD));
    }

    #[test]
    fn type_kinds_are_honest() {
        let g = graph_for(
            "Class C\nEnd Class\nStructure S\nEnd Structure\nInterface I\nEnd Interface\nEnum E\n A\nEnd Enum\n",
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
        for k in ["class", "structure", "interface", "enum"] {
            assert!(kinds.contains(k), "missing type_kind {k}: {kinds:?}");
        }
    }

    #[test]
    fn module_members_are_not_methods() {
        let g = graph_for("Module M\n Sub Run()\n End Sub\nEnd Module\n");
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "Module M is a Module");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 1, "Run is a Function");
        assert!(
            !g.edges().any(|e| e.kind == edge::HAS_METHOD),
            "a Module is not a type, so Run is not a method"
        );
    }

    #[test]
    fn resolves_unique_call_via_implicit_me() {
        let g = graph_for(
            "Class C\n Sub Run()\n  Helper()\n End Sub\n Sub Helper()\n End Sub\nEnd Class\n",
        );
        let h = call_edges(&g)
            .into_iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("Helper")))
            .expect("a call to Helper");
        assert_eq!(h.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(h.props.get("resolution"), Some(&Json::str("implicit_me")));
    }

    #[test]
    fn me_call_resolves_via_receiver() {
        let g = graph_for("Class P\n Sub A()\n  Me.B()\n End Sub\n Sub B()\n End Sub\nEnd Class\n");
        let recv = call_edges(&g)
            .into_iter()
            .find(|e| e.props.get("resolution") == Some(&Json::str("receiver")));
        assert!(recv.is_some(), "Me.B() should resolve via receiver scope");
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for("Class C\n Sub Run()\n  Mystery()\n End Sub\nEnd Class\n");
        let m = call_edges(&g)
            .into_iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("Mystery")))
            .expect("call to Mystery");
        assert_eq!(m.props.get("resolution"), Some(&Json::str("external")));
        assert!(g.has_node("unresolved::Mystery"));
    }

    #[test]
    fn external_imports_creates_dependency() {
        let g = graph_for("Imports System\nImports System.Text\nClass C\nEnd Class\n");
        assert!(g.has_node("ext::System"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::System"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn internal_imports_is_not_external() {
        let g =
            graph_for("Imports App.Core\nNamespace App.Core\n Class C\nEnd Class\nEnd Namespace\n");
        assert!(!g.has_node("ext::App"), "App should be internal");
        assert!(g.edges().any(
            |e| e.kind == edge::IMPORTS && e.props.get("external") == Some(&Json::Bool(false))
        ));
    }

    #[test]
    fn inherits_emits_extends() {
        let g = graph_for("Class Base\nEnd Class\nClass Derived\n Inherits Base\nEnd Class\n");
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an EXTENDS edge");
        assert!(ext.from.contains("Derived"));
        assert!(ext.to.contains("Base"));
    }

    #[test]
    fn implements_emits_implements() {
        let g = graph_for("Interface IFoo\nEnd Interface\nClass C\n Implements IFoo\nEnd Class\n");
        let imp = g
            .edges()
            .find(|e| e.kind == edge::IMPLEMENTS)
            .expect("an IMPLEMENTS edge");
        assert!(imp.to.contains("IFoo"));
    }

    #[test]
    fn field_const_property_bindings() {
        let g = graph_for("Class C\n Const K As Integer = 1\n Public Property P As Integer\n Dim F As Integer\nEnd Class\n");
        let consts: Vec<&crate::graph::GraphNode> =
            g.nodes().filter(|n| n.kind == ont::CONSTANT).collect();
        let k = consts.iter().find(|n| n.name == "K").expect("K");
        assert_eq!(k.props.get("binding"), Some(&Json::str("const")));
        let p = consts.iter().find(|n| n.name == "P").expect("P");
        assert_eq!(p.props.get("binding"), Some(&Json::str("property")));
        let f = consts.iter().find(|n| n.name == "F").expect("F");
        assert_eq!(f.props.get("binding"), Some(&Json::str("field")));
    }

    #[test]
    fn type_use_in_signature() {
        let g = graph_for(
            "Class Widget\nEnd Class\nClass C\n Sub Build(w As Widget)\n End Sub\nEnd Class\n",
        );
        assert!(
            g.edges()
                .any(|e| e.kind == edge::USES_TYPE && e.to.contains("Widget")),
            "parameter type should create USES_TYPE"
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src = "Namespace N\n Class C\n  Inherits B\n  Sub M()\n   f()\n   g()\n  End Sub\n  Sub f()\n  End Sub\n End Class\nEnd Namespace\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
