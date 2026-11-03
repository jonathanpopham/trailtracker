//! Lower the Crystal CST into the canonical graph.
//!
//! This mirrors the Ruby lowering ([`crate::lang::ruby::lower`]) — same
//! conservative principles, same shared ontology — adapted to Crystal's surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to a
//!    concrete project definition only when a scope level yields exactly one
//!    candidate; several candidates are emitted as an ambiguous edge with the full
//!    `candidates` set; none resolves to an explicit unresolved node.
//! 2. **Everything comes from real tokens.** Calls, superclasses, mixins, requires,
//!    and constants are read off the lossless tree, never guessed.
//!
//! Resolution uses a deterministic **scope ladder** (most specific first; the first
//! level with any candidate decides), the Crystal analogue of the Ruby ladder:
//! `self`-receiver → implicit-self (enclosing type) → local module → global. Each
//! edge records which level resolved it, so the call graph stays auditable.
//!
//! Honest mappings (see the IR Atlas):
//!   `def` → `Function` (a method → `HAS_METHOD` from its enclosing
//!   class/struct/enum/module); `macro` → `Macro`; `class`/`struct`/`enum`/
//!   `annotation` → `Type` (`type_kind: class|struct|enum|annotation`); `module` /
//!   `lib` → `Module` (a namespace scope — `lib` namespaces C bindings);
//!   top-level/scope-level `CONST =` → `Constant`; `class C < Base` → `C EXTENDS
//!   Base`; `include`/`extend M` → `IMPLEMENTS M` (a mixin is conformance, kept
//!   distinct from class inheritance); `require "…"` → `IMPORTS` (plus
//!   `ExternalDependency`/`DEPENDS_ON` for shards/stdlib; relativity is by the
//!   leading `.` of the path). Crystal has no IR kind for `@ivar`s, attribute
//!   annotations (`@[Link]`), `fun` C bindings, type `alias`es, or `getter`/
//!   `property` macros, so those are left as plain tokens/calls rather than
//!   fabricated — see `docs/ir-atlas.md` candidate extensions.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::Node;
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::crystal::lexer::{is_keyword, kind as tk};
use crate::lang::crystal::parser::node as cst;
use crate::lang::frontend::SourceFile;

/// Lower a whole project's worth of Crystal files into a graph. `manifest_deps` is
/// unused for Crystal (the pipeline's manifest reader is Cargo-only); dependencies
/// are discovered from `require` statements instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    // Project-local roots: the package plus every module-path segment. A require
    // whose root is one of these is intra-project, not an external shard.
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
        fn_by_name: BTreeMap::new(),
        method_by_name: BTreeMap::new(),
        fn_by_module: BTreeMap::new(),
        method_by_type: BTreeMap::new(),
        type_by_name: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("crystal"))],
    );

    // Pass B: definition nodes + structural edges + symbol tables. Inheritance and
    // mixins are deferred to pass C so a type defined later still resolves.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_extends: Vec<PendingLink> = Vec::new();
    let mut pend_impls: Vec<PendingLink> = Vec::new();
    for f in files.iter() {
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
                ("language", Json::str("crystal")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(leaf, edge::CONTAINS, file_id.clone(), vec![]);
        let mut walk = Walk {
            file_id: &file_id,
            module_join: &module_join,
            src: f.source,
            li: &li,
            pend_fns: &mut pend_fns,
            pend_extends: &mut pend_extends,
            pend_impls: &mut pend_impls,
        };
        lo.walk_stmts(f.root, &[], None, false, &mut walk);
    }

    // Pass C: resolve calls (scope ladder), constant/type usages, inheritance, and
    // mixins against the now-complete symbol tables.
    for pf in &pend_fns {
        let ctx = Ctx {
            module_join: pf.module_join.clone(),
            owner_type: pf.owner_type.clone(),
        };
        let mut calls = Vec::new();
        scan_calls(pf.body, pf.source, &mut calls);
        for call in &calls {
            let res = lo.resolve(call, &ctx);
            lo.emit_call(&pf.id, call, res);
        }
        lo.emit_type_uses(&pf.id, pf.body, pf.source);
    }
    for pe in &pend_extends {
        lo.emit_specialization(pe, edge::EXTENDS, "superclass");
    }
    for pi in &pend_impls {
        lo.emit_specialization(pi, edge::IMPLEMENTS, "mixin");
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    local_roots: BTreeSet<String>,
    /// Simple name → all function/method/macro node ids (global level).
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// Simple name → method node ids only (global method-call level).
    method_by_name: BTreeMap<String, Vec<String>>,
    /// (module_join, name) → function ids (local-module level).
    fn_by_module: BTreeMap<(String, String), Vec<String>>,
    /// (type_name, method_name) → method ids (receiver level).
    method_by_type: BTreeMap<(String, String), Vec<String>>,
    /// Simple name → type/module (class/struct/enum/module/lib) node ids.
    type_by_name: BTreeMap<String, Vec<String>>,
}

/// Mutable per-file walk context, bundled to keep recursion signatures small. `'a`
/// is the long-lived AST/source lifetime (what gets stored in the pending vectors);
/// `'s` is the short per-file lifetime of the borrowed locals.
struct Walk<'a, 's> {
    file_id: &'s str,
    module_join: &'s str,
    src: &'a str,
    li: &'s LineIndex,
    pend_fns: &'s mut Vec<PendingFn<'a>>,
    pend_extends: &'s mut Vec<PendingLink>,
    pend_impls: &'s mut Vec<PendingLink>,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    body: &'a Node,
    module_join: String,
    owner_type: Option<String>,
}

/// A deferred specialization link (`EXTENDS` superclass or `IMPLEMENTS` mixin),
/// resolved in pass C.
struct PendingLink {
    type_id: String,
    target_name: String,
}

/// The enclosing class/struct/enum/module while walking, for methods and mixins.
struct Owner {
    name: String,
    id: String,
}

/// A detected call site over the lossless tree.
struct Call {
    name: String,
    method: bool,
    receiver: Option<String>,
}

struct Ctx {
    module_join: String,
    owner_type: Option<String>,
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
                vec![("language", Json::str("crystal"))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    /// Walk a statement container, creating definition nodes and recursing into
    /// nested scopes. `owner` is the nearest enclosing type/module (cleared inside a
    /// method); `in_def` gates `Constant` emission.
    fn walk_stmts<'a>(
        &mut self,
        container: &'a Node,
        scope: &[String],
        owner: Option<&Owner>,
        in_def: bool,
        w: &mut Walk<'a, '_>,
    ) {
        for item in container.child_nodes() {
            match item.kind {
                cst::METHOD => self.handle_def(item, scope, owner, w),
                cst::MACRO_DEF => self.handle_macro(item, scope, owner, w),
                cst::CLASS => self.handle_type(item, scope, ont::TYPE, "class", w),
                cst::STRUCT => self.handle_type(item, scope, ont::TYPE, "struct", w),
                cst::ENUM => self.handle_type(item, scope, ont::TYPE, "enum", w),
                cst::ANNOTATION_DEF => self.handle_type(item, scope, ont::TYPE, "annotation", w),
                cst::MODULE => self.handle_type(item, scope, ont::MODULE, "module", w),
                cst::LIB => self.handle_type(item, scope, ont::MODULE, "lib", w),
                cst::COMPOUND => {
                    // if/while/case/begin/… are not new scopes: defs inside still
                    // belong to the enclosing type/module. Recurse each sub-body.
                    for block in item.children_of(cst::BLOCK) {
                        self.walk_stmts(block, scope, owner, in_def, w);
                    }
                }
                cst::EXPR_STMT => self.handle_expr_stmt(item, scope, owner, in_def, w),
                _ => {}
            }
        }
    }

    fn handle_def<'a>(
        &mut self,
        item: &'a Node,
        scope: &[String],
        owner: Option<&Owner>,
        w: &mut Walk<'a, '_>,
    ) {
        let (name, receiver) = method_name(item, w.src);
        let name = name.unwrap_or_else(|| "<anonymous>".to_string());
        let line = w.li.line_col(name_span_start(item)).line;
        let qual = qual_name(w.module_join, scope, &name);
        let id = format!("fn::{qual}#{line}");
        let body: &Node = item.child(cst::BLOCK).unwrap_or(item);
        let class_method = matches!(receiver.as_deref(), Some("self"));
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("crystal")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            ("has_body", Json::Bool(item.child(cst::BLOCK).is_some())),
        ];
        if let Some(o) = owner {
            props.push(("receiver_type", Json::str(o.name.clone())));
            props.push(("is_method", Json::Bool(true)));
            if class_method {
                props.push(("is_class_method", Json::Bool(true)));
            }
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, name.clone(), props);
        self.g
            .add_edge(w.file_id, edge::DECLARES, id.clone(), vec![]);

        self.register_callable(&name, &id, w.module_join, owner);
        if let Some(o) = owner {
            self.g
                .add_edge(o.id.clone(), edge::HAS_METHOD, id.clone(), vec![]);
        }

        w.pend_fns.push(PendingFn {
            id,
            source: w.src,
            body,
            module_join: w.module_join.to_string(),
            owner_type: owner.map(|o| o.name.clone()),
        });

        // A nested def (a method-defining-a-method) is rare; recurse its body for
        // any nested type/module definitions with a fresh (None) owner.
        if let Some(block) = item.child(cst::BLOCK) {
            let mut child_scope = scope.to_vec();
            child_scope.push(name);
            self.walk_stmts(block, &child_scope, None, true, w);
        }
    }

    /// `macro NAME … end` → `Macro`. A macro inside a type owns it via `HAS_METHOD`
    /// (it is invoked like a method); macro names also feed call resolution.
    fn handle_macro<'a>(
        &mut self,
        item: &'a Node,
        scope: &[String],
        owner: Option<&Owner>,
        w: &mut Walk<'a, '_>,
    ) {
        let (name, _receiver) = method_name(item, w.src);
        let name = name.unwrap_or_else(|| "<anonymous>".to_string());
        let line = w.li.line_col(name_span_start(item)).line;
        let qual = qual_name(w.module_join, scope, &name);
        let id = format!("macro::{qual}#{line}");
        let body: &Node = item.child(cst::BLOCK).unwrap_or(item);
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("crystal")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
        ];
        if let Some(o) = owner {
            props.push(("receiver_type", Json::str(o.name.clone())));
        }
        self.g
            .upsert_node(id.clone(), ont::MACRO, name.clone(), props);
        self.g
            .add_edge(w.file_id, edge::DECLARES, id.clone(), vec![]);

        self.register_callable(&name, &id, w.module_join, owner);
        if let Some(o) = owner {
            self.g
                .add_edge(o.id.clone(), edge::HAS_METHOD, id.clone(), vec![]);
        }

        w.pend_fns.push(PendingFn {
            id,
            source: w.src,
            body,
            module_join: w.module_join.to_string(),
            owner_type: owner.map(|o| o.name.clone()),
        });
    }

    /// Register a callable (function/method/macro) in the resolution symbol tables.
    /// `module_join` is the file's module join — the key for the local-module
    /// resolution lane, shared by top-level fns and methods in the same file.
    fn register_callable(
        &mut self,
        name: &str,
        id: &str,
        module_join: &str,
        owner: Option<&Owner>,
    ) {
        self.fn_by_name
            .entry(name.to_string())
            .or_default()
            .push(id.to_string());
        self.fn_by_module
            .entry((module_join.to_string(), name.to_string()))
            .or_default()
            .push(id.to_string());
        if let Some(o) = owner {
            self.method_by_name
                .entry(name.to_string())
                .or_default()
                .push(id.to_string());
            self.method_by_type
                .entry((o.name.clone(), name.to_string()))
                .or_default()
                .push(id.to_string());
        }
    }

    /// `class`/`struct`/`enum`/`annotation` → `Type`; `module`/`lib` → `Module`.
    /// `kind_label` is recorded as `type_kind` (Type) or `namespace_kind` (Module).
    fn handle_type<'a>(
        &mut self,
        item: &'a Node,
        scope: &[String],
        ont_kind: &'static str,
        kind_label: &'static str,
        w: &mut Walk<'a, '_>,
    ) {
        let name = type_name(item, w.src).unwrap_or_else(|| "<anonymous>".to_string());
        let line = w.li.line_col(name_span_start(item)).line;
        let qual = qual_name(w.module_join, scope, &name);
        let is_module = ont_kind == ont::MODULE;
        let id = if is_module {
            format!("mod::{qual}")
        } else {
            format!("type::{qual}")
        };
        let label_key = if is_module {
            "namespace_kind"
        } else {
            "type_kind"
        };
        self.g.upsert_node(
            id.clone(),
            ont_kind,
            name.clone(),
            vec![
                (label_key, Json::str(kind_label)),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("crystal")),
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
            .push(id.clone());

        // Superclass (defer the EXTENDS resolution to pass C).
        if let Some(base) = superclass_name(item, w.src) {
            w.pend_extends.push(PendingLink {
                type_id: id.clone(),
                target_name: base,
            });
        }

        if let Some(block) = item.child(cst::BLOCK) {
            let owner = Owner {
                name: name.clone(),
                id: id.clone(),
            };
            let mut child_scope = scope.to_vec();
            child_scope.push(name);
            self.walk_stmts(block, &child_scope, Some(&owner), false, w);
        }
    }

    /// An expression statement: detect `require`/`include`/constant assignment.
    fn handle_expr_stmt<'a>(
        &mut self,
        item: &'a Node,
        scope: &[String],
        owner: Option<&Owner>,
        in_def: bool,
        w: &mut Walk<'a, '_>,
    ) {
        let toks = top_level_tokens(item, w.src);
        let first = match toks.first() {
            Some(t) => *t,
            None => return,
        };
        match first.text {
            "require" => {
                if let Some(arg) = first_string(item, w.src) {
                    let relative = arg.starts_with('.');
                    self.emit_require(w.file_id, &arg, relative);
                }
            }
            "include" | "extend" => {
                if let Some(o) = owner {
                    for module_name in mixin_names(item, w.src) {
                        w.pend_impls.push(PendingLink {
                            type_id: o.id.clone(),
                            target_name: module_name,
                        });
                    }
                }
            }
            name if is_const(name) && is_const_decl(&toks) => {
                // `CONST = …` or typed `CONST : Type = …` at module/type scope (not
                // inside a method body).
                if !in_def {
                    let qual = qual_name(w.module_join, scope, name);
                    let id = format!("const::{qual}");
                    let line = w.li.line_col(first.span_start).line;
                    self.g.upsert_node(
                        id.clone(),
                        ont::CONSTANT,
                        name.to_string(),
                        vec![
                            ("binding", Json::str("constant")),
                            ("language", Json::str("crystal")),
                            ("line", Json::U64(line as u64)),
                        ],
                    );
                    self.g.add_edge(w.file_id, edge::DECLARES, id, vec![]);
                }
            }
            _ => {}
        }
    }

    /// Emit the `IMPORTS` edge for one `require`d path, plus the
    /// `ExternalDependency`/`DEPENDS_ON` pair when it is not project-local.
    fn emit_require(&mut self, file_id: &str, path: &str, relative: bool) {
        if path.is_empty() {
            return;
        }
        let root = require_root(path);
        let internal = relative || self.local_roots.contains(&root);
        if internal {
            let mod_id = format!("mod::{root}");
            self.g.upsert_node(
                mod_id.clone(),
                ont::MODULE,
                root.clone(),
                vec![("language", Json::str("crystal"))],
            );
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                mod_id,
                vec![
                    ("path", Json::str(path.to_string())),
                    ("external", Json::Bool(false)),
                    ("relative", Json::Bool(relative)),
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
                    ("source", Json::str("require")),
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

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        if call.method {
            // `self.m` → enclosing type's methods.
            if matches!(call.receiver.as_deref(), Some("self")) {
                if let Some(owner) = &ctx.owner_type {
                    let c = self.methods_of(owner, &call.name);
                    if !c.is_empty() {
                        return mk(c, "receiver");
                    }
                }
            }
            // Other receivers have an unknown type (no inference): fall back to a
            // global match among methods only, preserving any ambiguity.
            let c = self.global_methods(&call.name);
            return if c.is_empty() {
                Resolution {
                    outcome: Outcome::None,
                    level: "external",
                }
            } else {
                mk(c, "global_method")
            };
        }
        // A bare name inside a method may be a same-type method (Crystal's implicit
        // self) — try the enclosing type's methods first.
        if let Some(owner) = &ctx.owner_type {
            let c = self.methods_of(owner, &call.name);
            if !c.is_empty() {
                return mk(c, "implicit_self");
            }
        }
        // Local module.
        let c = self.fns_in_module(&ctx.module_join, &call.name);
        if !c.is_empty() {
            return mk(c, "local");
        }
        // Global.
        let c = self.global_fns(&call.name);
        if c.is_empty() {
            Resolution {
                outcome: Outcome::None,
                level: "external",
            }
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

    /// Resolve a deferred superclass/mixin link into a concrete edge, pointing at
    /// the project type when unique, otherwise an explicit `UnresolvedSymbol` (a
    /// stdlib/shard type we cannot see in an airgap).
    fn emit_specialization(&mut self, link: &PendingLink, kind: &'static str, role: &'static str) {
        let target = match self.unique_type(&link.target_name) {
            Some(id) => id,
            None => {
                let id = unresolved_id(&link.target_name);
                self.ensure_unresolved(&id, &link.target_name, role);
                id
            }
        };
        self.g.add_edge(
            link.type_id.clone(),
            kind,
            target,
            vec![("target_name", Json::str(link.target_name.clone()))],
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

    fn methods_of(&self, type_name: &str, method: &str) -> Vec<String> {
        self.method_by_type
            .get(&(type_name.to_string(), method.to_string()))
            .cloned()
            .unwrap_or_default()
    }

    fn fns_in_module(&self, module_join: &str, name: &str) -> Vec<String> {
        self.fn_by_module
            .get(&(module_join.to_string(), name.to_string()))
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

    /// Add `USES_TYPE` edges for constant references in a body that name a unique
    /// project type (e.g. `Widget.new`, `Geo::Point`).
    fn emit_type_uses(&mut self, from_id: &str, body: &Node, src: &str) {
        let mut seen: Vec<String> = Vec::new();
        for n in body.walk() {
            for t in n.tokens() {
                if t.kind != tk::IDENT {
                    continue;
                }
                let name = t.span.text(src);
                if !is_const(name) {
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
}

fn mk(ids: Vec<String>, level: &'static str) -> Resolution {
    let outcome = if ids.len() == 1 {
        Outcome::One(ids[0].clone())
    } else {
        Outcome::Many(ids)
    };
    Resolution { outcome, level }
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
    parts.push(name.to_string());
    parts.join(".")
}

/// The first path segment of a `require` argument, with any leading relative
/// prefix stripped (`"./foo/bar"` → `foo`, `"json"` → `json`).
fn require_root(path: &str) -> String {
    let trimmed = path.trim_start_matches("./").trim_start_matches("../");
    let trimmed = trimmed.trim_start_matches('/');
    trimmed.split('/').next().unwrap_or(trimmed).to_string()
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

/// Whether a constant-named expression statement is actually a constant *binding*:
/// `CONST = …` (second token `=`) or a typed `CONST : Type = …` (second token `:`
/// with an `=` later). Excludes comparisons (`CONST == x`) and scope access
/// (`CONST::Nested`, whose `::` lexes as one token, never bare `:`).
fn is_const_decl(toks: &[Tok<'_>]) -> bool {
    match toks.get(1).map(|t| t.text) {
        Some("=") => true,
        Some(":") => toks.iter().any(|t| t.text == "="),
        _ => false,
    }
}

fn is_const(name: &str) -> bool {
    name.chars()
        .next()
        .map(|c| c.is_ascii_uppercase())
        .unwrap_or(false)
}

/// The simple method name and its explicit receiver (if any) from a `Method`'s
/// `Name` node. `def self.foo` → (`foo`, Some("self")); `def a.b` → (`b`,
/// Some("a")); `def []=` → (`[]=`, None).
fn method_name(item: &Node, src: &str) -> (Option<String>, Option<String>) {
    let nm = match item.child(cst::NAME) {
        Some(n) => n,
        None => return (None, None),
    };
    let texts: Vec<&str> = nm.tokens().map(|t| t.span.text(src)).collect();
    if texts.is_empty() {
        return (None, None);
    }
    // Find the last `.`/`::` connector; the receiver is what precedes it.
    let dot = texts.iter().rposition(|t| *t == "." || *t == "::");
    match dot {
        Some(i) => {
            let receiver = texts[..i]
                .iter()
                .rev()
                .find(|t| !t.is_empty())
                .map(|s| s.to_string());
            let name: String = texts[i + 1..].concat();
            (Some(name), receiver)
        }
        None => (Some(texts.concat()), None),
    }
}

fn name_span_start(item: &Node) -> u32 {
    item.child(cst::NAME)
        .map(|n| n.span.start)
        .unwrap_or(item.span.start)
}

/// The defined type/module simple name — the last segment of its `Name` path
/// (`Geo::Point` → `Point`).
fn type_name(item: &Node, src: &str) -> Option<String> {
    let nm = item.child(cst::NAME)?;
    let mut last: Option<&str> = None;
    for t in nm.tokens() {
        let txt = t.span.text(src);
        if txt != "::" && txt != "." {
            last = Some(txt);
        }
    }
    last.map(|s| s.to_string())
}

/// The superclass simple name from a `class C < Base` header (`Superclass` node).
/// Direct tokens only — generic args (`< Bar(T)`) live in a child group and are
/// excluded — so the last constant-named ident is the base type's name.
fn superclass_name(item: &Node, src: &str) -> Option<String> {
    let sup = item.child(cst::SUPERCLASS)?;
    let mut last: Option<&str> = None;
    for t in sup.tokens() {
        if t.kind == tk::IDENT && !is_keyword(t.span.text(src)) {
            last = Some(t.span.text(src));
        }
    }
    last.map(|s| s.to_string())
}

/// Module names referenced by an `include`/`extend` call — every constant-named
/// identifier after the keyword (`include A, B` → [A, B]).
fn mixin_names(item: &Node, src: &str) -> Vec<String> {
    let mut names = Vec::new();
    let mut seen_keyword = false;
    for n in item.walk() {
        for t in n.tokens() {
            if t.kind != tk::IDENT {
                continue;
            }
            let txt = t.span.text(src);
            if !seen_keyword {
                if matches!(txt, "include" | "extend") {
                    seen_keyword = true;
                }
                continue;
            }
            if is_const(txt) {
                names.push(txt.to_string());
            }
        }
    }
    names
}

/// First string-literal argument anywhere in the subtree (for `require`).
fn first_string(item: &Node, src: &str) -> Option<String> {
    for n in item.walk() {
        for t in n.tokens() {
            if t.kind == tk::STRING {
                return Some(strip_quotes(t.span.text(src)));
            }
        }
    }
    None
}

/// Strip the surrounding double-quote characters from a simple string literal.
fn strip_quotes(s: &str) -> String {
    let bytes = s.as_bytes();
    if bytes.len() >= 2 {
        let first = bytes[0];
        let last = bytes[bytes.len() - 1];
        if first == b'"' && last == first {
            return s[1..s.len() - 1].to_string();
        }
    }
    s.to_string()
}

/// A flat token (text + kind + start) for the small token-list helpers.
#[derive(Clone, Copy)]
struct Tok<'a> {
    text: &'a str,
    /// Retained for parity with other front ends' token helpers; not yet read.
    #[allow(dead_code)]
    kind: &'static str,
    span_start: u32,
}

/// Direct, non-trivia child tokens of `node` (skips `newline`); does not descend
/// into child nodes.
fn top_level_tokens<'a>(node: &'a Node, src: &'a str) -> Vec<Tok<'a>> {
    node.tokens()
        .filter(|t| t.kind != tk::NEWLINE)
        .map(|t| Tok {
            text: t.span.text(src),
            kind: t.kind,
            span_start: t.span.start,
        })
        .collect()
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
            crate::core::cst::Child::Token(t) if t.trivia || t.kind == tk::NEWLINE => {}
            crate::core::cst::Child::Token(t) => v.push(El::Tok {
                text: t.span.text(src),
                ident: t.kind == tk::IDENT,
            }),
            crate::core::cst::Child::Node(n) => v.push(El::Grp(n)),
        }
    }
    v
}

fn is_def_node(kind: &str) -> bool {
    matches!(
        kind,
        cst::METHOD
            | cst::MACRO_DEF
            | cst::CLASS
            | cst::STRUCT
            | cst::ENUM
            | cst::ANNOTATION_DEF
            | cst::MODULE
            | cst::LIB
    )
}

/// Detect `name(...)`, `recv.name(...)`, and `recv.name` call sites over the real
/// token tree, recursing into nested groups/blocks but **not** into nested
/// definitions (those are scanned as their own functions). Keywords are excluded.
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        // Method/attribute call: `.` name (optionally followed by `(...)`).
        if matches!(tok_text(&els[i]), Some(".") | Some("&.")) {
            if i + 1 < n && is_ident_el(&els[i + 1]) {
                let name = tok_text(&els[i + 1]).unwrap_or("");
                // Skip an attribute *assignment* (`obj.x = …`): the next element is a
                // bare `=`. A call followed by `(` or anything else is kept.
                let assigned = i + 2 < n && tok_text(&els[i + 2]) == Some("=");
                if !assigned && !is_keyword(name) {
                    let receiver = if i > 0 {
                        match &els[i - 1] {
                            El::Tok { text, ident: true } => Some(text.to_string()),
                            _ => None,
                        }
                    } else {
                        None
                    };
                    out.push(Call {
                        name: name.to_string(),
                        method: true,
                        receiver,
                    });
                }
                i += 2;
                continue;
            }
            i += 1;
            continue;
        }
        // Bare call: name `(...)`, not preceded by `.` and not a keyword.
        if is_ident_el(&els[i]) {
            let prev = if i > 0 { tok_text(&els[i - 1]) } else { None };
            let text = tok_text(&els[i]).unwrap_or("");
            if prev != Some(".")
                && prev != Some("&.")
                && prev != Some("def")
                && !is_keyword(text)
                && i + 1 < n
            {
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
    // Recurse into groups and non-definition sub-nodes; never into nested defs.
    for e in &els {
        if let Some(g) = grp(e) {
            if !is_def_node(g.kind) {
                scan_calls(g, src, out);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::crystal::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("app.cr", src);
        let file = SourceFile {
            rel_path: "app.cr".to_string(),
            module_path: vec!["app".to_string()],
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    fn call_edges(g: &Graph) -> Vec<&crate::graph::GraphEdge> {
        g.edges().filter(|e| e.kind == edge::CALLS).collect()
    }

    #[test]
    fn emits_function_type_nodes() {
        let g = graph_for("class C\n  def m\n  end\nend\n\ndef f\nend\n");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "f + C#m");
        assert_eq!(g.count_nodes_of(ont::TYPE), 1, "class C is a Type");
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD));
    }

    #[test]
    fn class_struct_enum_are_types_module_is_module() {
        let g = graph_for(
            "module M\n  class C\n  end\n  struct S\n  end\n  enum E\n    A\n  end\nend\n",
        );
        let type_kinds: Vec<&Json> = g
            .nodes()
            .filter(|n| n.kind == ont::TYPE)
            .filter_map(|n| n.props.get("type_kind"))
            .collect();
        assert!(type_kinds.contains(&&Json::str("class")));
        assert!(type_kinds.contains(&&Json::str("struct")));
        assert!(type_kinds.contains(&&Json::str("enum")));
        // `module M` lowers to a Module node, not a Type.
        let m = g
            .nodes()
            .find(|n| n.kind == ont::MODULE && n.name == "M")
            .expect("module M is a Module node");
        assert_eq!(m.props.get("namespace_kind"), Some(&Json::str("module")));
        for n in g.nodes().filter(|n| n.kind == ont::TYPE) {
            assert_eq!(n.props.get("language"), Some(&Json::str("crystal")));
        }
    }

    #[test]
    fn lib_is_a_module() {
        let g = graph_for("lib LibC\n  fun printf : Int32\nend\n");
        let lib = g
            .nodes()
            .find(|n| n.kind == ont::MODULE && n.name == "LibC")
            .expect("lib LibC is a Module node");
        assert_eq!(lib.props.get("namespace_kind"), Some(&Json::str("lib")));
    }

    #[test]
    fn macro_is_a_macro_node() {
        let g = graph_for("macro define(x)\n  def {{x}}\n  end\nend\n");
        assert_eq!(g.count_nodes_of(ont::MACRO), 1);
        let m = g.nodes().find(|n| n.kind == ont::MACRO).expect("macro");
        assert_eq!(m.name, "define");
    }

    #[test]
    fn resolves_unique_local_call() {
        let g = graph_for("def add(a, b)\n  a + b\nend\n\ndef run\n  add(1, 2)\nend\n");
        let calls = call_edges(&g);
        let add = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("add")))
            .expect("a call to add");
        assert!(add.to.starts_with("fn::app.add"));
        assert_eq!(add.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(add.props.get("resolution"), Some(&Json::str("local")));
    }

    #[test]
    fn self_method_resolves_via_receiver() {
        let g = graph_for("class P\n  def a\n    self.b\n  end\n  def b\n  end\nend\n");
        let calls = call_edges(&g);
        let recv = calls
            .iter()
            .find(|e| e.props.get("resolution") == Some(&Json::str("receiver")));
        assert!(recv.is_some(), "self.b should resolve via receiver scope");
        assert_eq!(recv.unwrap().props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn implicit_self_call_resolves() {
        let g = graph_for("class P\n  def a\n    helper()\n  end\n  def helper\n  end\nend\n");
        let calls = call_edges(&g);
        let h = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("helper")));
        assert!(h.is_some());
        assert_eq!(
            h.unwrap().props.get("resolution"),
            Some(&Json::str("implicit_self"))
        );
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for("def run\n  mystery()\nend\n");
        let calls = call_edges(&g);
        assert_eq!(calls.len(), 1);
        assert_eq!(
            calls[0].props.get("resolution"),
            Some(&Json::str("external"))
        );
        assert!(g.has_node("unresolved::mystery"));
    }

    #[test]
    fn require_creates_dependency() {
        let g = graph_for("require \"json\"\nrequire \"./helper\"\n");
        assert!(g.has_node("ext::json"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::json"));
        // A relative require is internal.
        assert!(g.edges().any(
            |e| e.kind == edge::IMPORTS && e.props.get("external") == Some(&Json::Bool(false))
        ));
    }

    #[test]
    fn inheritance_emits_extends() {
        let g = graph_for("class Base\nend\n\nclass Derived < Base\nend\n");
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an EXTENDS edge");
        assert!(ext.from.starts_with("type::app.Derived"));
        assert!(ext.to.starts_with("type::app.Base"));
    }

    #[test]
    fn generic_superclass_resolves_base_name() {
        let g = graph_for("class Bar\nend\n\nclass Foo(T) < Bar\nend\n");
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an EXTENDS edge");
        assert_eq!(ext.props.get("target_name"), Some(&Json::str("Bar")));
    }

    #[test]
    fn mixin_emits_implements() {
        let g = graph_for("module Walkable\nend\n\nclass Dog\n  include Walkable\nend\n");
        let imp = g
            .edges()
            .find(|e| e.kind == edge::IMPLEMENTS)
            .expect("an IMPLEMENTS edge");
        assert!(imp.from.starts_with("type::app.Dog"));
        assert!(imp.to.starts_with("mod::app.Walkable"));
    }

    #[test]
    fn top_level_constant_is_constant() {
        // A bare `CONST =`, a typed `CONST : Type =`, and a lowercase non-constant.
        let g = graph_for("VERSION = \"1.0\"\nMAX : Int32 = 10\nclass C\n  x = 1\nend\n");
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 2);
        let names: BTreeSet<&str> = g
            .nodes()
            .filter(|n| n.kind == ont::CONSTANT)
            .map(|n| n.name.as_str())
            .collect();
        assert!(names.contains("VERSION"));
        assert!(names.contains("MAX"));
    }

    #[test]
    fn class_method_is_marked() {
        let g = graph_for("class C\n  def self.build\n  end\nend\n");
        let m = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "build")
            .expect("the class method");
        assert_eq!(m.props.get("is_class_method"), Some(&Json::Bool(true)));
    }

    #[test]
    fn type_use_via_constant_reference() {
        let g = graph_for("class Widget\nend\n\ndef build\n  Widget.new\nend\n");
        assert!(
            g.edges()
                .any(|e| e.kind == edge::USES_TYPE && e.to.contains("Widget")),
            "Widget.new should create USES_TYPE"
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src =
            "require \"json\"\nclass C < B\n  def m\n    helper()\n  end\nend\n\ndef helper\nend\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
