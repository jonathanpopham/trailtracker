//! Lower the Swift CST into the canonical graph.
//!
//! This mirrors the Rust and Python lowerings ([`crate::ir::lower`],
//! [`crate::lang::python::lower`]) — same conservative principles, same shared
//! ontology — adapted to Swift's surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to
//!    a concrete project definition only when a scope level yields exactly one
//!    candidate; several candidates are emitted as an ambiguous edge carrying the
//!    full `candidates` set; none resolves to an explicit external/unresolved
//!    node. There is no LLM in the airgapped runtime to guess.
//! 2. **Everything comes from real tokens.** Calls, inherited types, conformances,
//!    imports, and type uses are read off the lossless tree, never invented.
//!
//! Swift's symbols are *module-global*: a type declared in one file is visible in
//! another without an import, so there is no per-file module ladder (unlike
//! Python). Resolution uses a short deterministic ladder instead — receiver
//! (`self`/`Self`) → module-global — and every edge records the level that
//! resolved it, so the call graph stays auditable.
//!
//! Honest mappings (see the IR Atlas):
//!   `func`/`init`/`deinit`/`subscript` → `Function` (a member → `HAS_METHOD`
//!   from its enclosing type, plus a `func_kind` property); `class`/`struct`/
//!   `enum`/`protocol`/`actor` → `Type` (distinguished by `type_kind`);
//!   `typealias` → `Type` (`type_kind: alias`); file-scope `let`/`var` →
//!   `Constant`; `import` → `IMPORTS` + an `ExternalDependency`/`DEPENDS_ON` pair
//!   (every Swift import names another module, opaque in an airgap). Inheritance
//!   vs. conformance is split honestly: a class's superclass → `EXTENDS`, a
//!   protocol conformance → `IMPLEMENTS`, decided by the resolved supertype's
//!   `type_kind` (and, when unresolved, by Swift's rule that a class's superclass
//!   is the first clause — flagged `inferred_superclass`). An `extension`'s
//!   members become `HAS_METHOD` on the extended type and its conformances become
//!   `IMPLEMENTS`.

use std::collections::BTreeMap;

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::swift::lexer::{is_keyword, kind as tk};
use crate::lang::swift::parser::node as cst;

/// Lower a whole project's worth of Swift files into a graph. `manifest_deps` is
/// unused (the pipeline's manifest reader is Cargo-only); dependencies are
/// discovered from `import` statements instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        fn_by_name: BTreeMap::new(),
        method_by_name: BTreeMap::new(),
        method_by_type: BTreeMap::new(),
        type_by_name: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("swift"))],
    );

    // Pass B: create definition nodes + structural edges and build the global
    // symbol tables. Inheritance, conformance, extension ownership, calls, and
    // type uses are deferred to pass C so a type defined later still resolves.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_conf: Vec<PendingConformance> = Vec::new();
    let mut pend_has_method: Vec<PendingHasMethod> = Vec::new();
    let mut pend_ext_conf: Vec<PendingExtConformance> = Vec::new();

    for f in files {
        let li = LineIndex::new(f.source);
        let file_id = format!("file::{}", f.rel_path);
        lo.g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("swift")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        let pkg_id = lo.pkg_id();
        lo.g.add_edge(pkg_id, edge::CONTAINS, file_id.clone(), vec![]);

        let mut walk = WalkCtx {
            file_id: &file_id,
            src: f.source,
            li: &li,
            pend_fns: &mut pend_fns,
            pend_conf: &mut pend_conf,
            pend_has_method: &mut pend_has_method,
            pend_ext_conf: &mut pend_ext_conf,
        };
        lo.walk_members(f.root, &[], None, &mut walk);
    }

    // Pass C: resolve against the now-complete symbol tables.
    for pf in &pend_fns {
        if let Some(block) = pf.block {
            let mut calls = Vec::new();
            scan_calls(block, pf.source, &mut calls);
            for call in &calls {
                let res = lo.resolve(call, pf.owner_type.as_deref());
                lo.emit_call(&pf.id, call, res);
            }
        }
        if let Some(sig) = pf.signature {
            lo.emit_type_uses(&pf.id, sig, pf.source);
        }
    }
    for pc in &pend_conf {
        lo.emit_conformance(pc);
    }
    for pe in &pend_ext_conf {
        lo.emit_ext_conformance(pe);
    }
    for ph in &pend_has_method {
        lo.emit_deferred_has_method(ph);
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    /// Simple name → all free-function node ids (module-global level).
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// Simple name → method node ids only (global method-call fallback).
    method_by_name: BTreeMap<String, Vec<String>>,
    /// (type_name, method_name) → method ids (receiver / implicit-self level).
    method_by_type: BTreeMap<(String, String), Vec<String>>,
    /// Simple name → (type node id, type_kind) for every project type.
    type_by_name: BTreeMap<String, Vec<(String, &'static str)>>,
}

/// Mutable per-file walk context, threaded so the recursive walker keeps a small
/// argument list.
struct WalkCtx<'a, 'b> {
    file_id: &'a str,
    src: &'b str,
    li: &'a LineIndex,
    pend_fns: &'a mut Vec<PendingFn<'b>>,
    pend_conf: &'a mut Vec<PendingConformance>,
    pend_has_method: &'a mut Vec<PendingHasMethod>,
    pend_ext_conf: &'a mut Vec<PendingExtConformance>,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    block: Option<&'a Node>,
    signature: Option<&'a Node>,
    owner_type: Option<String>,
}

/// A deferred type inheritance/conformance list (`class C: Base, P { … }`),
/// resolved in pass C once every type is known.
struct PendingConformance {
    type_id: String,
    /// The declaring type's `type_kind` (`class`, `struct`, …).
    decl_kind: &'static str,
    /// Inherited / conformed names in source order.
    names: Vec<String>,
}

/// A deferred `HAS_METHOD` for a method declared in an `extension`, whose owning
/// type id is only known after every type is registered.
struct PendingHasMethod {
    owner_name: String,
    method_id: String,
}

/// A deferred `extension Target: Protocol` conformance.
struct PendingExtConformance {
    target_name: String,
    protocol_name: String,
}

/// The enclosing type while walking members (its id is `None` for `extension`
/// members, whose owner is resolved by name in pass C).
struct Owner {
    name: String,
    id: Option<String>,
}

/// A detected call site over the lossless tree.
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

    /// Walk a member container (a `SourceFile` or a type/extension `ItemBlock`),
    /// creating definition nodes and recursing into nested type scopes. `owner` is
    /// the enclosing type (cleared inside free functions, which have opaque
    /// bodies); `scope` is the chain of enclosing type names for qualified ids.
    fn walk_members<'b>(
        &mut self,
        container: &'b Node,
        scope: &[String],
        owner: Option<&Owner>,
        w: &mut WalkCtx<'_, 'b>,
    ) {
        for item in container.child_nodes() {
            match item.kind {
                cst::FUNCTION => self.handle_fn(item, "func", scope, owner, w),
                cst::INIT => self.handle_fn(item, "init", scope, owner, w),
                cst::DEINIT => self.handle_fn(item, "deinit", scope, owner, w),
                cst::SUBSCRIPT => self.handle_fn(item, "subscript", scope, owner, w),
                cst::CLASS => self.handle_type(item, "class", scope, w),
                cst::STRUCT => self.handle_type(item, "struct", scope, w),
                cst::ENUM => self.handle_type(item, "enum", scope, w),
                cst::PROTOCOL => self.handle_type(item, "protocol", scope, w),
                cst::ACTOR => self.handle_type(item, "actor", scope, w),
                cst::EXTENSION => self.handle_extension(item, scope, w),
                cst::TYPEALIAS => self.handle_typealias(item, scope, w),
                cst::IMPORT => self.handle_import(item, w),
                cst::PROPERTY => {
                    // File-scope `let`/`var` are global Constants; type members
                    // (properties) and function locals are not.
                    if owner.is_none() {
                        self.handle_property(item, w);
                    }
                }
                _ => {}
            }
        }
    }

    fn handle_fn<'b>(
        &mut self,
        item: &'b Node,
        func_kind: &'static str,
        scope: &[String],
        owner: Option<&Owner>,
        w: &mut WalkCtx<'_, 'b>,
    ) {
        let name = name_text(item, w.src).unwrap_or("<anonymous>").to_string();
        let line = w.li.line_col(name_span_start(item)).line;
        let qual = qual_name(scope, &name);
        let id = format!("fn::{qual}#{line}");
        let block = child_block(item);
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("swift")),
            ("func_kind", Json::str(func_kind)),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            ("has_body", Json::Bool(block.is_some())),
        ];
        if is_async(item, w.src) {
            props.push(("is_async", Json::Bool(true)));
        }
        if let Some(o) = owner {
            props.push(("receiver_type", Json::str(o.name.clone())));
            props.push(("is_method", Json::Bool(true)));
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, name.clone(), props);
        self.g
            .add_edge(w.file_id, edge::DECLARES, id.clone(), vec![]);

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
            match &o.id {
                Some(oid) => {
                    self.g
                        .add_edge(oid.clone(), edge::HAS_METHOD, id.clone(), vec![]);
                }
                None => {
                    // Extension member: owner type id is resolved in pass C.
                    w.pend_has_method.push(PendingHasMethod {
                        owner_name: o.name.clone(),
                        method_id: id.clone(),
                    });
                }
            }
        }

        w.pend_fns.push(PendingFn {
            id,
            source: w.src,
            block,
            signature: item.child(cst::SIGNATURE),
            owner_type: owner.map(|o| o.name.clone()),
        });
    }

    fn handle_type<'b>(
        &mut self,
        item: &'b Node,
        type_kind: &'static str,
        scope: &[String],
        w: &mut WalkCtx<'_, 'b>,
    ) {
        let name = name_text(item, w.src).unwrap_or("<anonymous>").to_string();
        let line = w.li.line_col(name_span_start(item)).line;
        let qual = qual_name(scope, &name);
        let id = format!("type::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str(type_kind)),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("swift")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
            ],
        );
        self.g
            .add_edge(w.file_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name
            .entry(name.clone())
            .or_default()
            .push((id.clone(), type_kind));

        // Inheritance / conformance list lives in the header after the NAME.
        let names = item
            .child(cst::HEADER)
            .map(|h| inheritance_names(h, w.src))
            .unwrap_or_default();
        if !names.is_empty() {
            w.pend_conf.push(PendingConformance {
                type_id: id.clone(),
                decl_kind: type_kind,
                names,
            });
        }

        if let Some(block) = item.child(cst::ITEM_BLOCK) {
            let owner = Owner {
                name: name.clone(),
                id: Some(id),
            };
            let mut child_scope = scope.to_vec();
            child_scope.push(name);
            self.walk_members(block, &child_scope, Some(&owner), w);
        }
    }

    /// `extension Target: P, Q where … { … }`. Members attach to `Target` via
    /// `HAS_METHOD` (deferred); conformances become `IMPLEMENTS` (deferred).
    fn handle_extension<'b>(&mut self, item: &'b Node, scope: &[String], w: &mut WalkCtx<'_, 'b>) {
        let header = item.child(cst::HEADER);
        let (target, confs) = match &header {
            Some(h) => extension_target(h, w.src),
            None => (None, Vec::new()),
        };
        let target = match target {
            Some(t) => t,
            None => return, // nothing nameable to extend; members still lossless
        };
        for p in confs {
            w.pend_ext_conf.push(PendingExtConformance {
                target_name: target.clone(),
                protocol_name: p,
            });
        }
        if let Some(block) = item.child(cst::ITEM_BLOCK) {
            let owner = Owner {
                name: target.clone(),
                id: None,
            };
            let mut child_scope = scope.to_vec();
            child_scope.push(target);
            self.walk_members(block, &child_scope, Some(&owner), w);
        }
    }

    fn handle_typealias(&mut self, item: &Node, scope: &[String], w: &mut WalkCtx) {
        let name = match name_text(item, w.src) {
            Some(n) => n.to_string(),
            None => return,
        };
        let line = w.li.line_col(name_span_start(item)).line;
        let qual = qual_name(scope, &name);
        let id = format!("type::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str("alias")),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("swift")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g
            .add_edge(w.file_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name
            .entry(name)
            .or_default()
            .push((id, "alias"));
    }

    /// Every Swift `import` names another module — opaque in an airgapped build —
    /// so it always becomes an `ExternalDependency` with an `IMPORTS` edge and a
    /// package-level `DEPENDS_ON`.
    fn handle_import(&mut self, item: &Node, w: &mut WalkCtx) {
        let header = match item.child(cst::HEADER) {
            Some(h) => h,
            None => return,
        };
        let idents: Vec<&str> = header
            .tokens()
            .filter(|t| t.kind == tk::IDENT && !is_keyword(t.span.text(w.src)))
            .map(|t| t.span.text(w.src))
            .collect();
        let module = match idents.first() {
            Some(m) => (*m).to_string(),
            None => return,
        };
        let path_text = idents.join(".");
        let dep_id = ext_id(&module);
        self.g.upsert_node(
            dep_id.clone(),
            ont::EXTERNAL_DEPENDENCY,
            module,
            vec![
                ("external", Json::Bool(true)),
                ("source", Json::str("import")),
            ],
        );
        self.g.add_edge(
            w.file_id,
            edge::IMPORTS,
            dep_id.clone(),
            vec![
                ("path", Json::str(path_text)),
                ("external", Json::Bool(true)),
            ],
        );
        let pkg_id = self.pkg_id();
        self.g.add_edge(pkg_id, edge::DEPENDS_ON, dep_id, vec![]);
    }

    /// File-scope `let NAME … ` / `var NAME …` → a `Constant`. Only a plain single
    /// identifier binder is recorded (tuple patterns are skipped) — conservative,
    /// never guessed.
    fn handle_property(&mut self, item: &Node, w: &mut WalkCtx) {
        let name = match name_text(item, w.src) {
            Some(n) => n.to_string(),
            None => return,
        };
        let line = w.li.line_col(name_span_start(item)).line;
        let binder = item
            .tokens()
            .find(|t| matches!(t.span.text(w.src), "let" | "var"))
            .map(|t| t.span.text(w.src))
            .unwrap_or("let");
        let id = format!("const::{}", qual_name(&[], &name));
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            name,
            vec![
                ("binding", Json::str(binder.to_string())),
                ("mutable", Json::Bool(binder == "var")),
                ("language", Json::str("swift")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(w.file_id, edge::DECLARES, id, vec![]);
    }

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, owner_type: Option<&str>) -> Resolution {
        if call.method {
            // `self.m()` / `Self.m()` → the enclosing type's methods.
            if matches!(call.receiver.as_deref(), Some("self") | Some("Self")) {
                if let Some(owner) = owner_type {
                    let c = self.methods_of(owner, &call.name);
                    if !c.is_empty() {
                        return mk(c, "receiver");
                    }
                }
            }
            // Unknown receiver type (no inference): fall back to a global match
            // among methods only, preserving any ambiguity.
            let c = self.global_methods(&call.name);
            return if c.is_empty() {
                none_res()
            } else {
                mk(c, "global_method")
            };
        }

        // Bare `foo()`: a free function first.
        let c = self.global_fns(&call.name);
        if !c.is_empty() {
            return mk(c, "global");
        }
        // Implicit-self method call inside a type body.
        if let Some(owner) = owner_type {
            let c = self.methods_of(owner, &call.name);
            if !c.is_empty() {
                return mk(c, "implicit_self");
            }
        }
        // Constructor call `Type(...)` → the type's initializers.
        let inits = self.methods_of(&call.name, "init");
        if !inits.is_empty() {
            return mk(inits, "initializer");
        }
        none_res()
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

    /// Resolve a deferred type inheritance/conformance list. A class's superclass
    /// becomes `EXTENDS`; protocol conformances become `IMPLEMENTS`. The split is
    /// driven by the resolved supertype's `type_kind`; for an unresolved name on a
    /// class, Swift's rule (the superclass, if any, is the first clause) decides,
    /// flagged `inferred_superclass` so the inference is auditable.
    fn emit_conformance(&mut self, pc: &PendingConformance) {
        for (i, name) in pc.names.iter().enumerate() {
            let resolved = self.unique_type(name);
            let (kind, target, inferred) = match &resolved {
                Some((tid, "protocol")) => (edge::IMPLEMENTS, tid.clone(), false),
                Some((tid, "class")) if pc.decl_kind == "class" && i == 0 => {
                    (edge::EXTENDS, tid.clone(), false)
                }
                Some((tid, _)) => (edge::IMPLEMENTS, tid.clone(), false),
                None => {
                    let uid = unresolved_id(name);
                    if pc.decl_kind == "class" && i == 0 {
                        self.ensure_unresolved(&uid, name, "supertype");
                        (edge::EXTENDS, uid, true)
                    } else {
                        self.ensure_unresolved(&uid, name, "protocol");
                        (edge::IMPLEMENTS, uid, false)
                    }
                }
            };
            let mut props = vec![
                ("base_name", Json::str(name.clone())),
                ("resolved", Json::Bool(resolved.is_some())),
            ];
            if inferred {
                props.push(("inferred_superclass", Json::Bool(true)));
            }
            self.g.add_edge(pc.type_id.clone(), kind, target, props);
        }
    }

    /// Resolve an `extension Target: Protocol` conformance into an `IMPLEMENTS`
    /// edge from the (resolved or unresolved) target to the (resolved or
    /// unresolved) protocol.
    fn emit_ext_conformance(&mut self, pe: &PendingExtConformance) {
        let from = self.type_or_unresolved(&pe.target_name, "extended_type");
        let to = self.type_or_unresolved(&pe.protocol_name, "protocol");
        self.g.add_edge(
            from,
            edge::IMPLEMENTS,
            to,
            vec![("base_name", Json::str(pe.protocol_name.clone()))],
        );
    }

    /// Resolve a deferred extension `HAS_METHOD` edge to its owning type.
    fn emit_deferred_has_method(&mut self, ph: &PendingHasMethod) {
        let owner = self.type_or_unresolved(&ph.owner_name, "extended_type");
        self.g
            .add_edge(owner, edge::HAS_METHOD, ph.method_id.clone(), vec![]);
    }

    /// The unique project type id for `name`, or an `UnresolvedSymbol` node
    /// (created on demand) standing in for a type the airgapped build cannot see.
    fn type_or_unresolved(&mut self, name: &str, role: &'static str) -> String {
        if let Some((id, _)) = self.unique_type(name) {
            return id;
        }
        let uid = unresolved_id(name);
        self.ensure_unresolved(&uid, name, role);
        uid
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

    fn unique_type(&self, name: &str) -> Option<(String, &'static str)> {
        match self.type_by_name.get(name) {
            Some(v) if v.len() == 1 => Some(v[0].clone()),
            _ => None,
        }
    }

    /// Add `USES_TYPE` edges for identifiers in a signature (parameter and return
    /// type annotations, generic constraints) that name a unique project type.
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
                if let Some((type_id, _)) = self.unique_type(name) {
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
}

fn mk(ids: Vec<String>, level: &'static str) -> Resolution {
    let outcome = if ids.len() == 1 {
        Outcome::One(ids[0].clone())
    } else {
        Outcome::Many(ids)
    };
    Resolution { outcome, level }
}

fn none_res() -> Resolution {
    Resolution {
        outcome: Outcome::None,
        level: "external",
    }
}

// --- pure helpers -----------------------------------------------------------

/// `Scope.…Name` — the dotted qualified name and the basis for node ids.
fn qual_name(scope: &[String], name: &str) -> String {
    if scope.is_empty() {
        name.to_string()
    } else {
        let mut parts = scope.to_vec();
        parts.push(name.to_string());
        parts.join(".")
    }
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

/// The function/closure body block, if present.
fn child_block(item: &Node) -> Option<&Node> {
    item.child(cst::BLOCK)
}

/// True if a declaration carries an `async` modifier in its signature.
fn is_async(item: &Node, src: &str) -> bool {
    if let Some(sig) = item.child(cst::SIGNATURE) {
        for t in sig.tokens() {
            if t.span.text(src) == "async" {
                return true;
            }
        }
    }
    false
}

/// A flat header element: a token carries its text and whether it is an
/// identifier; a balanced group is flattened to an empty, non-identifier marker
/// (its contents never name a top-level supertype).
struct HItem<'a> {
    text: &'a str,
    ident: bool,
}

fn header_items<'a>(header: &'a Node, src: &'a str) -> Vec<HItem<'a>> {
    let mut out = Vec::new();
    for c in &header.children {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => out.push(HItem {
                text: t.span.text(src),
                ident: t.kind == tk::IDENT,
            }),
            Child::Node(_) => out.push(HItem {
                text: "",
                ident: false,
            }),
        }
    }
    out
}

fn angle_delta(text: &str) -> i32 {
    let mut d = 0;
    for ch in text.chars() {
        match ch {
            '<' => d += 1,
            '>' => d -= 1,
            _ => {}
        }
    }
    d
}

/// Extract a type declaration's inheritance/conformance simple names from its
/// header. Skips a leading generic clause (`<…>`), reads the `: A, B, …` list up
/// to a `where` clause, and takes the final identifier of each comma clause
/// (`Bar` from `Foo.Bar`). Generic arguments and constraints are ignored.
fn inheritance_names(header: &Node, src: &str) -> Vec<String> {
    let items = header_items(header, src);
    let mut idx = 0;
    // Skip a leading generic parameter clause.
    if items.first().map(|h| h.text == "<").unwrap_or(false) {
        let mut depth = 0;
        while idx < items.len() {
            depth += angle_delta(items[idx].text);
            idx += 1;
            if depth <= 0 {
                break;
            }
        }
    }
    // Expect the inheritance colon.
    while idx < items.len() && items[idx].text != ":" && items[idx].text != "where" {
        idx += 1;
    }
    if idx >= items.len() || items[idx].text != ":" {
        return Vec::new();
    }
    idx += 1;
    collect_name_list(&items[idx..])
}

/// Extract an `extension` target's name and its conformance list. The target is
/// the dotted type name before `:`/`where`; conformances follow the `:`.
fn extension_target(header: &Node, src: &str) -> (Option<String>, Vec<String>) {
    let items = header_items(header, src);
    let mut idx = 0;
    let mut target: Option<String> = None;
    let mut angle = 0;
    while idx < items.len() {
        let it = &items[idx];
        if angle == 0 && (it.text == ":" || it.text == "where") {
            break;
        }
        angle += angle_delta(it.text);
        if angle < 0 {
            angle = 0;
        }
        if angle == 0 && it.ident && !is_keyword(it.text) {
            target = Some(it.text.to_string());
        }
        idx += 1;
    }
    let confs = if idx < items.len() && items[idx].text == ":" {
        collect_name_list(&items[idx + 1..])
    } else {
        Vec::new()
    };
    (target, confs)
}

/// Read a comma-separated list of type names (taking the final identifier of each
/// clause) up to a `where` clause, ignoring anything inside generic `<…>`.
fn collect_name_list(items: &[HItem<'_>]) -> Vec<String> {
    let mut names = Vec::new();
    let mut cur: Option<String> = None;
    let mut angle = 0;
    for it in items {
        if angle == 0 && it.text == "where" {
            break;
        }
        if angle == 0 && it.text == "," {
            if let Some(n) = cur.take() {
                names.push(n);
            }
            continue;
        }
        let before = angle;
        angle += angle_delta(it.text);
        if angle < 0 {
            angle = 0;
        }
        if before == 0 && it.ident && !is_keyword(it.text) {
            cur = Some(it.text.to_string());
        }
    }
    if let Some(n) = cur.take() {
        names.push(n);
    }
    names
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
/// recursing into nested groups. A trailing `(...)` argument group is required —
/// trailing-closure-only calls (`arr.map { … }`) are deliberately not inferred,
/// keeping with the no-fabrication rule. Keywords are excluded.
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        // Method/attribute call: `.` name `(...)`.
        if tok_text(&els[i]) == Some(".") {
            if i + 2 < n && is_ident_el(&els[i + 1]) {
                if let Some(g) = grp(&els[i + 2]) {
                    if g.kind == cst::PAREN {
                        let receiver = if i > 0 {
                            match &els[i - 1] {
                                El::Tok { text, ident: true } => Some(text.to_string()),
                                _ => None,
                            }
                        } else {
                            None
                        };
                        out.push(Call {
                            name: tok_text(&els[i + 1]).unwrap_or("").to_string(),
                            method: true,
                            receiver,
                        });
                        i += 3;
                        continue;
                    }
                }
            }
            i += 1;
            continue;
        }
        // Bare call: name `(...)`, not preceded by `.` (attribute) and not a
        // keyword (control flow such as `if (x)`).
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
    // Recurse into every nested group (Paren/Bracket/Brace).
    for e in &els {
        if let Some(g) = grp(e) {
            scan_calls(g, src, out);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::swift::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("mod.swift", src);
        let file = SourceFile {
            rel_path: "mod.swift".to_string(),
            module_path: Vec::new(),
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    fn call_edges(g: &Graph) -> Vec<&crate::graph::GraphEdge> {
        g.edges().filter(|e| e.kind == edge::CALLS).collect()
    }

    #[test]
    fn emits_function_type_method_nodes() {
        let g = graph_for("class C {\n    func m() {}\n}\n\nfunc f() {}\n");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "f + C.m");
        assert_eq!(g.count_nodes_of(ont::TYPE), 1, "class C is a Type");
        assert!(
            g.edges().any(|e| e.kind == edge::HAS_METHOD),
            "C has method m"
        );
    }

    #[test]
    fn type_kinds_are_honest() {
        for (src, want) in [
            ("class C {}", "class"),
            ("struct S {}", "struct"),
            ("enum E {}", "enum"),
            ("protocol P {}", "protocol"),
            ("actor A {}", "actor"),
        ] {
            let g = graph_for(src);
            let ty = g
                .nodes()
                .find(|n| n.kind == ont::TYPE)
                .expect("a Type node");
            assert_eq!(ty.props.get("type_kind"), Some(&Json::str(want)), "{src}");
            assert_eq!(ty.props.get("language"), Some(&Json::str("swift")));
        }
    }

    #[test]
    fn resolves_unique_global_call() {
        let g = graph_for("func add(a: Int, b: Int) -> Int { a + b }\nfunc run() { add(1, 2) }\n");
        let calls = call_edges(&g);
        let add = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("add")))
            .expect("a call to add");
        assert!(add.to.starts_with("fn::add"));
        assert_eq!(add.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(add.props.get("resolution"), Some(&Json::str("global")));
    }

    #[test]
    fn self_method_resolves_via_receiver() {
        let g = graph_for("class P {\n    func a() { self.b() }\n    func b() {}\n}\n");
        let calls = call_edges(&g);
        let recv = calls
            .iter()
            .find(|e| e.props.get("resolution") == Some(&Json::str("receiver")));
        assert!(recv.is_some(), "self.b() should resolve via receiver scope");
        assert_eq!(recv.unwrap().props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for("func run() { mystery() }\n");
        let calls = call_edges(&g);
        assert_eq!(calls.len(), 1);
        assert_eq!(
            calls[0].props.get("resolution"),
            Some(&Json::str("external"))
        );
        assert!(g.has_node("unresolved::mystery"));
    }

    #[test]
    fn import_creates_external_dependency() {
        let g = graph_for("import Foundation\n");
        assert!(g.has_node("ext::Foundation"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::Foundation"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn class_superclass_is_extends_protocol_is_implements() {
        let g = graph_for("class Base {}\nprotocol P {}\nclass Derived: Base, P {}\n");
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an EXTENDS edge");
        assert!(ext.from.starts_with("type::Derived"));
        assert!(ext.to.starts_with("type::Base"));
        let imp = g
            .edges()
            .find(|e| e.kind == edge::IMPLEMENTS && e.to.starts_with("type::P"))
            .expect("an IMPLEMENTS edge to P");
        assert!(imp.from.starts_with("type::Derived"));
    }

    #[test]
    fn struct_conformance_is_implements() {
        let g = graph_for("protocol Shape {}\nstruct Circle: Shape {}\n");
        let imp = g
            .edges()
            .find(|e| e.kind == edge::IMPLEMENTS)
            .expect("an IMPLEMENTS edge");
        assert!(imp.from.starts_with("type::Circle"));
        assert!(imp.to.starts_with("type::Shape"));
        // A struct never produces an EXTENDS edge.
        assert!(!g.edges().any(|e| e.kind == edge::EXTENDS));
    }

    #[test]
    fn unresolved_superclass_is_inferred() {
        let g = graph_for("class MyVC: UIViewController {}\n");
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an inferred EXTENDS edge");
        assert_eq!(
            ext.props.get("inferred_superclass"),
            Some(&Json::Bool(true))
        );
        assert!(g.has_node("unresolved::UIViewController"));
    }

    #[test]
    fn extension_methods_attach_to_type() {
        let g = graph_for("struct S {}\nextension S {\n    func extra() {}\n}\n");
        let has = g
            .edges()
            .find(|e| e.kind == edge::HAS_METHOD)
            .expect("HAS_METHOD from extension");
        assert!(has.from.starts_with("type::S"), "owner is S: {}", has.from);
    }

    #[test]
    fn extension_conformance_is_implements() {
        let g = graph_for("protocol Codable {}\nstruct S {}\nextension S: Codable {}\n");
        assert!(g.edges().any(|e| e.kind == edge::IMPLEMENTS
            && e.from.starts_with("type::S")
            && e.to.starts_with("type::Codable")));
    }

    #[test]
    fn file_scope_let_is_constant_member_is_not() {
        let g = graph_for("let version = \"1.0\"\nclass C {\n    var count = 0\n}\n");
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 1);
        let c = g
            .nodes()
            .find(|n| n.kind == ont::CONSTANT)
            .expect("a constant");
        assert_eq!(c.name, "version");
    }

    #[test]
    fn initializer_call_resolves_to_init() {
        let g = graph_for(
            "struct Point {\n    init(x: Int) {}\n}\nfunc make() { let p = Point(x: 1) }\n",
        );
        let calls = call_edges(&g);
        let ctor = calls
            .iter()
            .find(|e| e.props.get("resolution") == Some(&Json::str("initializer")));
        assert!(
            ctor.is_some(),
            "Point(x:) should resolve to the initializer"
        );
    }

    #[test]
    fn type_use_in_signature() {
        let g = graph_for("struct Widget {}\nfunc build(w: Widget) {}\n");
        assert!(
            g.edges()
                .any(|e| e.kind == edge::USES_TYPE && e.to.contains("Widget")),
            "param annotation should create USES_TYPE"
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src = "import UIKit\nclass C: Base {\n    func m() { helper() }\n}\nfunc helper() {}\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
