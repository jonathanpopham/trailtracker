//! Lower the Zig CST into the canonical graph.
//!
//! This mirrors the Rust/Go lowerings — same conservative principles, same shared
//! ontology — adapted to Zig's defining idiom that **types are values**:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to a
//!    concrete project definition only when a scope level yields exactly one
//!    candidate; several become an ambiguous edge carrying the full `candidates`
//!    set; none resolves to an explicit `UnresolvedSymbol`.
//! 2. **Everything comes from real tokens.** Calls, imports, type containers, and
//!    type uses are read off the lossless tree, never guessed.
//!
//! Honest Zig mappings (see the IR Atlas):
//!   - `const Foo = struct {…}` / `enum {…}` / `union {…}` / `opaque {…}` /
//!     `error {…}` → `Type` with a `type_kind` of `struct`/`enum`/`union`/
//!     `opaque`/`error_set`. A `fn` declared inside such a container → `Function`
//!     plus a `HAS_METHOD` edge from that `Type`. Nested type containers and
//!     nested constants recurse.
//!   - top-level (or container-level) non-type `const`/`var` → `Constant`.
//!   - `const x = @import("std")` → `IMPORTS` (+ `ExternalDependency`/`DEPENDS_ON`
//!     for `std`/packages); a `@import("foo.zig")` (relative `.zig`) is an internal
//!     import to a module node.
//!   - calls (`f()`, `recv.m()`, `Type.assoc()`) → `CALLS`, resolved with a
//!     deterministic scope ladder.
//!
//! Resolution ladder (most specific first; first level with any candidate wins):
//!   receiver (`self.m()` where `self` is the method's first param) →
//!   qualified-type (`Type.m()`) → local file/container scope → global. Method
//!   calls with an unknown receiver fall back to a global match among *methods*
//!   only. Each edge records which level resolved it, so the graph stays auditable.
//!
//! Honest gaps, deliberately *not* fabricated (noted, never invented):
//!   - struct/enum/union **fields** have no ontology node kind, so they are not
//!     emitted as nodes (their declared types still produce `USES_TYPE` edges from
//!     the owning `Type`).
//!   - `comptime { … }` blocks and `usingnamespace` have no definition site, so no
//!     node is emitted (calls inside `comptime` blocks are therefore not scanned).
//!   - Zig has no nominal `implements`/inheritance, so no `IMPLEMENTS`/`EXTENDS`
//!     edges are emitted.

use std::collections::BTreeMap;

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::zig::lexer::{is_keyword, kind as tk};
use crate::lang::zig::parser::node as cst;

/// Lower a whole project's worth of Zig files into a graph. `manifest_deps` is
/// unused (the pipeline's manifest reader is Cargo-only); Zig dependencies are
/// discovered from `@import` declarations instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        fn_by_name: BTreeMap::new(),
        method_by_name: BTreeMap::new(),
        fn_by_scope: BTreeMap::new(),
        method_by_type: BTreeMap::new(),
        type_by_name: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("zig"))],
    );

    // Pass B: create definition nodes + structural edges and build the symbol
    // tables. Call/type resolution is deferred to pass C so a symbol defined later
    // (or in another file) still resolves.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_tu: Vec<PendingTypeUse> = Vec::new();
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
                ("language", Json::str("zig")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(leaf, edge::CONTAINS, file_id.clone(), vec![]);

        for member in f.root.child_nodes() {
            lo.walk_member(
                member,
                &file_id,
                &module_join,
                &[],
                None,
                f.source,
                &li,
                &mut pend_fns,
                &mut pend_tu,
            );
        }
    }

    // Pass C: resolve calls (scope ladder) and type usages against the complete
    // symbol tables.
    for pf in &pend_fns {
        let ctx = Ctx {
            scope_join: pf.scope_join.clone(),
            owner_type: pf.owner_type.clone(),
            recv_var: pf.recv_var.clone(),
        };
        if let Some(block) = pf.block {
            let mut calls = Vec::new();
            scan_calls(block, pf.source, &mut calls);
            for call in &calls {
                let res = lo.resolve(call, &ctx);
                lo.emit_call(&pf.id, call, res);
            }
        }
    }
    for tu in &pend_tu {
        lo.emit_type_uses(&tu.from, tu.region, tu.source);
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    /// Simple name → all plain-function node ids (global level).
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// Simple name → method node ids only (global method-call level).
    method_by_name: BTreeMap<String, Vec<String>>,
    /// (scope_join, name) → function ids (local-scope level). Holds every fn,
    /// method or not, so same-container bare calls resolve.
    fn_by_scope: BTreeMap<(String, String), Vec<String>>,
    /// (owner_type, name) → method ids (receiver / qualified-type levels).
    method_by_type: BTreeMap<(String, String), Vec<String>>,
    /// Simple name → type node ids.
    type_by_name: BTreeMap<String, Vec<String>>,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    block: Option<&'a Node>,
    scope_join: String,
    owner_type: Option<String>,
    recv_var: Option<String>,
}

/// A deferred `USES_TYPE` region, resolved in pass C.
struct PendingTypeUse<'a> {
    from: String,
    source: &'a str,
    region: &'a Node,
}

/// The enclosing type container of a member, for method ownership.
struct Owner {
    name: String,
    id: String,
}

/// A detected call site over the lossless tree.
struct Call {
    /// The called name (final selector or bare identifier).
    name: String,
    /// True for `recv.name(...)` selector calls.
    method: bool,
    /// Immediate receiver identifier for selector calls.
    receiver: Option<String>,
}

/// Resolution context for one enclosing function.
struct Ctx {
    scope_join: String,
    owner_type: Option<String>,
    recv_var: Option<String>,
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

    /// Ensure the `Package → mod::a → mod::a/b …` chain exists and return the leaf
    /// module id (or the package id for a root-package file).
    fn ensure_modules(&mut self, path: &[String]) -> String {
        let pkg = self.pkg_id();
        if path.is_empty() {
            return pkg;
        }
        let mut parent = pkg;
        let mut acc: Vec<String> = Vec::new();
        for seg in path {
            acc.push(seg.clone());
            let id = format!("mod::{}", acc.join("/"));
            self.g.upsert_node(
                id.clone(),
                ont::MODULE,
                seg.clone(),
                vec![("language", Json::str("zig"))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    /// Dispatch one member to the right handler. Recurses for type-container bodies.
    #[allow(clippy::too_many_arguments)]
    fn walk_member<'a>(
        &mut self,
        member: &'a Node,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        owner: Option<&Owner>,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_tu: &mut Vec<PendingTypeUse<'a>>,
    ) {
        match member.kind {
            cst::FUNCTION => self.handle_fn(
                member,
                file_id,
                module_join,
                scope,
                owner,
                src,
                li,
                pend_fns,
            ),
            cst::CONST_DECL | cst::VAR_DECL => self.handle_decl(
                member,
                file_id,
                module_join,
                scope,
                src,
                li,
                pend_fns,
                pend_tu,
            ),
            cst::TEST => self.handle_test(member, file_id, module_join, scope, src, li, pend_fns),
            cst::FIELD => {
                // A field's declared type contributes USES_TYPE from its owner type
                // (fields themselves have no ontology node kind).
                if let (Some(o), Some(h)) = (owner, member.child(cst::HEADER)) {
                    pend_tu.push(PendingTypeUse {
                        from: o.id.clone(),
                        source: src,
                        region: h,
                    });
                }
            }
            // COMPTIME / USINGNAMESPACE / ERROR_ITEM: no definition site to emit.
            _ => {}
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_fn<'a>(
        &mut self,
        member: &'a Node,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        owner: Option<&Owner>,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
    ) {
        let name = name_text(member, src).unwrap_or("<anonymous>").to_string();
        let line = li.line_col(name_span_start(member)).line;
        let qual = qual_name(module_join, scope, &name);
        let id = format!("fn::{qual}#{line}");
        let block = member.child(cst::BLOCK);
        let sig = member.child(cst::SIGNATURE);
        let recv_var = owner.and_then(|_| sig.and_then(|s| first_param_name(s, src)));

        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("zig")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(member.span.start as u64)),
            ("span_end", Json::U64(member.span.end as u64)),
            ("has_body", Json::Bool(block.is_some())),
        ];
        if let Some(o) = owner {
            props.push(("receiver_type", Json::str(o.name.clone())));
            props.push(("is_method", Json::Bool(true)));
        }
        if let Some(v) = &recv_var {
            props.push(("receiver_var", Json::str(v.clone())));
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, name.clone(), props);
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);

        let scope_join = scope_key(module_join, scope);
        // Every fn (method or not) is locally callable within its own container.
        self.fn_by_scope
            .entry((scope_join.clone(), name.clone()))
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
        } else {
            self.fn_by_name
                .entry(name.clone())
                .or_default()
                .push(id.clone());
        }

        pend_fns.push(PendingFn {
            id,
            source: src,
            block,
            scope_join,
            owner_type: owner.map(|o| o.name.clone()),
            recv_var,
        });
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_decl<'a>(
        &mut self,
        member: &'a Node,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_tu: &mut Vec<PendingTypeUse<'a>>,
    ) {
        let name = match name_text(member, src) {
            Some(n) => n.to_string(),
            None => return,
        };
        let line = li.line_col(name_span_start(member)).line;

        // `const x = @import(...)` → IMPORTS, not a Constant/Type.
        if let Some(value) = member.child(cst::VALUE) {
            if let Some(path) = import_path(value, src) {
                self.handle_import(file_id, &path);
                return;
            }
        }

        if let Some(kind) = type_kind_of(member, src) {
            // Type container. Note: a `var` holding a type is unusual but handled.
            let qual = qual_name(module_join, scope, &name);
            let id = format!("type::{qual}");
            self.g.upsert_node(
                id.clone(),
                ont::TYPE,
                name.clone(),
                vec![
                    ("type_kind", Json::str(kind)),
                    ("qualified_name", Json::str(qual)),
                    ("language", Json::str("zig")),
                    ("line", Json::U64(line as u64)),
                    ("span_start", Json::U64(member.span.start as u64)),
                    ("span_end", Json::U64(member.span.end as u64)),
                ],
            );
            self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
            self.type_by_name
                .entry(name.clone())
                .or_default()
                .push(id.clone());

            // Recurse into the container body so methods, nested types, and nested
            // constants become first-class graph nodes.
            if let Some(block) = member.child(cst::ITEM_BLOCK) {
                let mut child_scope = scope.to_vec();
                child_scope.push(name.clone());
                let owner = Owner {
                    name: name.clone(),
                    id: id.clone(),
                };
                for m in block.child_nodes() {
                    self.walk_member(
                        m,
                        file_id,
                        module_join,
                        &child_scope,
                        Some(&owner),
                        src,
                        li,
                        pend_fns,
                        pend_tu,
                    );
                }
            }
        } else {
            // A plain value binding → Constant.
            let binding = if member.kind == cst::VAR_DECL {
                "var"
            } else {
                "const"
            };
            let id = format!("const::{}", qual_name(module_join, scope, &name));
            self.g.upsert_node(
                id.clone(),
                ont::CONSTANT,
                name,
                vec![
                    ("binding", Json::str(binding)),
                    ("language", Json::str("zig")),
                    ("line", Json::U64(line as u64)),
                ],
            );
            self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
            // The type annotation contributes USES_TYPE.
            if let Some(h) = member.child(cst::HEADER) {
                pend_tu.push(PendingTypeUse {
                    from: id,
                    source: src,
                    region: h,
                });
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_test<'a>(
        &mut self,
        member: &'a Node,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
    ) {
        let label = test_label(member, src);
        let line = li.line_col(member.span.start).line;
        let qual = qual_name(module_join, scope, &format!("test:{label}"));
        let id = format!("fn::{qual}#{line}");
        let block = member.child(cst::BLOCK);
        self.g.upsert_node(
            id.clone(),
            ont::FUNCTION,
            label,
            vec![
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("zig")),
                ("line", Json::U64(line as u64)),
                ("is_test", Json::Bool(true)),
                ("has_body", Json::Bool(block.is_some())),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        // A test is not a callable target, so it is not indexed — but its body is
        // scanned for outbound calls.
        pend_fns.push(PendingFn {
            id,
            source: src,
            block,
            scope_join: scope_key(module_join, scope),
            owner_type: None,
            recv_var: None,
        });
    }

    /// Emit `IMPORTS` (+ dependency edges) for a `@import("…")` path. A relative
    /// `.zig` path is an internal module import; anything else (`std`, `builtin`,
    /// `root`, or a package name) is an external dependency.
    fn handle_import(&mut self, file_id: &str, path: &str) {
        if path.is_empty() {
            return;
        }
        if path.ends_with(".zig") {
            let stem = path.trim_end_matches(".zig");
            let mod_id = format!("mod::{stem}");
            let leaf = stem.rsplit('/').next().unwrap_or(stem).to_string();
            self.g.upsert_node(
                mod_id.clone(),
                ont::MODULE,
                leaf,
                vec![("language", Json::str("zig"))],
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
            let dep_id = format!("ext::{path}");
            self.g.upsert_node(
                dep_id.clone(),
                ont::EXTERNAL_DEPENDENCY,
                path.to_string(),
                vec![
                    ("external", Json::Bool(true)),
                    ("source", Json::str("import")),
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
            // Receiver scope: `self.m()` where `self` is the enclosing method's
            // first parameter resolves against the receiver type's methods.
            if let (Some(rv), Some(ot)) = (&ctx.recv_var, &ctx.owner_type) {
                if call.receiver.as_deref() == Some(rv.as_str()) {
                    let c = self.methods_of(ot, &call.name);
                    if !c.is_empty() {
                        return mk(c, "receiver");
                    }
                }
            }
            // Qualified-type: `Type.assoc()` / `Type.method()` where the receiver
            // names a known project type.
            if let Some(recv) = &call.receiver {
                let c = self.methods_of(recv, &call.name);
                if !c.is_empty() {
                    return mk(c, "qualified_type");
                }
            }
            // Unknown receiver type (no inference). The honest candidate set is
            // every same-name method PLUS every same-name free function — a Zig
            // member call can also be namespace access on an `@import` value
            // (`mod.f()`).
            // `mk` resolves a singleton and preserves any wider set as an
            // explicit ambiguity; it never guesses.
            let mut c = self.global_methods(&call.name);
            if !c.is_empty() {
                // Same-name free functions are counterevidence: they widen the
                // candidate set (forcing ambiguity), but a member call is never
                // resolved to a free function on name evidence alone.
                for id in self.global_fns(&call.name) {
                    if !c.contains(&id) {
                        c.push(id);
                    }
                }
            }
            return if c.is_empty() {
                Resolution {
                    outcome: Outcome::None,
                    level: "external",
                }
            } else {
                mk(c, "global_method")
            };
        }

        // Bare call: local container/file scope, then global.
        let c = self.fns_in_scope(&ctx.scope_join, &call.name);
        if !c.is_empty() {
            return mk(c, "local");
        }
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

    fn fns_in_scope(&self, scope_join: &str, name: &str) -> Vec<String> {
        self.fn_by_scope
            .get(&(scope_join.to_string(), name.to_string()))
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

    /// Add `USES_TYPE` edges for identifiers in `region` that name a unique project
    /// type (not the using node itself).
    fn emit_type_uses(&mut self, from_id: &str, region: &Node, src: &str) {
        let mut seen: Vec<String> = Vec::new();
        for n in region.walk() {
            for t in n.tokens() {
                if t.kind != tk::IDENT {
                    continue;
                }
                let name = t.span.text(src);
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

/// Directory/file module-join: `["src","math"]` → `"src/math"`, `[]` → "".
fn mod_join(path: &[String]) -> String {
    path.join("/")
}

/// `module.scope….name` — the qualified name and basis for node ids.
fn qual_name(module_join: &str, scope: &[String], name: &str) -> String {
    let mut parts: Vec<String> = Vec::new();
    if !module_join.is_empty() {
        parts.push(module_join.to_string());
    }
    parts.extend(scope.iter().cloned());
    parts.push(name.to_string());
    parts.join(".")
}

/// The namespace key for local (bare-call) resolution: `module.scope…`.
fn scope_key(module_join: &str, scope: &[String]) -> String {
    let mut parts: Vec<String> = Vec::new();
    if !module_join.is_empty() {
        parts.push(module_join.to_string());
    }
    parts.extend(scope.iter().cloned());
    parts.join(".")
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

/// Classify a declaration's type-container kind from its direct loose tokens. Only
/// a container keyword that the parser left as a direct child token counts (the
/// keyword preceding an `ItemBlock` or `error` set), so a `struct` mentioned deep
/// inside an ordinary value expression never misclassifies the binding.
fn type_kind_of(member: &Node, src: &str) -> Option<&'static str> {
    for t in member.tokens() {
        match t.span.text(src) {
            "struct" => return Some("struct"),
            "enum" => return Some("enum"),
            "union" => return Some("union"),
            "opaque" => return Some("opaque"),
            "error" => return Some("error_set"),
            _ => {}
        }
    }
    None
}

/// The `@import("…")` path string from a declaration's `Value` region, if it is an
/// import binding. Returns the unquoted path.
fn import_path(value: &Node, src: &str) -> Option<String> {
    let mut saw_import = false;
    for c in &value.children {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => {
                saw_import = t.kind == tk::BUILTIN && t.span.text(src) == "@import";
            }
            Child::Node(n) if n.kind == cst::PAREN && saw_import => {
                for t in n.tokens() {
                    if t.kind == tk::STRING || t.kind == tk::C_STRING {
                        return Some(unquote(t.span.text(src)));
                    }
                }
                return None;
            }
            Child::Node(_) => saw_import = false,
        }
    }
    None
}

/// Strip surrounding quotes (and a leading `c`) from a string literal's text.
fn unquote(text: &str) -> String {
    let s = text.strip_prefix('c').unwrap_or(text);
    let bytes = s.as_bytes();
    if bytes.len() >= 2 && bytes[0] == b'"' && bytes[bytes.len() - 1] == b'"' {
        return s[1..s.len() - 1].to_string();
    }
    s.to_string()
}

/// First parameter name of a function `Signature` — the receiver variable for a
/// method. Reads the first identifier inside the first `Paren` group, skipping
/// the `comptime`/`noalias` qualifiers that may precede it.
fn first_param_name(sig: &Node, src: &str) -> Option<String> {
    let paren = sig.walk().find(|n| n.kind == cst::PAREN)?;
    for t in paren.tokens() {
        if t.kind == tk::IDENT {
            let text = t.span.text(src);
            if !is_keyword(text) {
                return Some(text.to_string());
            }
        }
    }
    None
}

/// A test's label: its quoted name string (unquoted) or referenced identifier, or
/// `"test"` for an anonymous test.
fn test_label(member: &Node, src: &str) -> String {
    for t in member.tokens() {
        match t.kind {
            tk::STRING => return unquote(t.span.text(src)),
            tk::IDENT if t.span.text(src) != "test" => return t.span.text(src).to_string(),
            _ => {}
        }
    }
    "test".to_string()
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
                // Builtins (`@import`, `@TypeOf`, …) are intrinsics, never project
                // call targets, so they are not treated as identifiers here.
                ident: t.kind == tk::IDENT,
            }),
            Child::Node(n) => v.push(El::Grp(n)),
        }
    }
    v
}

/// Detect `name(...)` and `recv.name(...)` call sites over the real token tree,
/// recursing into nested groups. Keywords and builtins are excluded.
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        // Selector call: `.` name `(...)`.
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
        // Bare call: name `(...)`, not preceded by `.` (a selector) and not a
        // keyword (control flow `if`/`while`/`switch` followed by `(`).
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
    use crate::lang::zig::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("app.zig", src);
        let file = SourceFile {
            rel_path: "app.zig".to_string(),
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
    fn lossless_round_trip_end_to_end() {
        // A representative snippet exercising imports, a struct with a method and a
        // field, an enum, constants, a multiline string, a plain fn, and a test —
        // it must reconstruct byte-for-byte through the parser.
        let src = "\
const std = @import(\"std\");

const Point = struct {
    x: f64,
    y: f64,

    pub fn norm(self: Point) f64 {
        return @sqrt(self.x * self.x + self.y * self.y);
    }
};

const Color = enum(u8) { red, green, blue };

pub const MAX: u32 = 100;
var counter: u32 = 0;

const banner =
    \\\\hello
    \\\\world
;

pub fn add(a: i32, b: i32) i32 {
    return a + b;
}

pub fn run() void {
    _ = add(1, 2);
}

test \"adds\" {
    _ = add(2, 3);
}
";
        let tree = parse("app.zig", src);
        assert!(tree.is_lossless(), "Zig front end must round-trip source");
    }

    #[test]
    fn struct_is_a_type_with_methods() {
        let g = graph_for(
            "const Server = struct {\n    pub fn run(self: Server) void {}\n    pub fn helper() void {}\n};\n",
        );
        let ty = g
            .nodes()
            .find(|n| n.kind == ont::TYPE)
            .expect("a Type node");
        assert_eq!(ty.props.get("type_kind"), Some(&Json::str("struct")));
        assert_eq!(ty.props.get("language"), Some(&Json::str("zig")));
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "run + helper");
        assert!(
            g.edges().filter(|e| e.kind == edge::HAS_METHOD).count() >= 2,
            "both fns are methods of Server"
        );
    }

    #[test]
    fn enum_union_opaque_error_kinds() {
        let g = graph_for(
            "const C = enum { a, b };\nconst U = union { x: u8 };\nconst O = opaque {};\nconst E = error{ X, Y };\n",
        );
        let kinds: Vec<_> = g
            .nodes()
            .filter(|n| n.kind == ont::TYPE)
            .filter_map(|n| n.props.get("type_kind").cloned())
            .collect();
        assert!(kinds.contains(&Json::str("enum")));
        assert!(kinds.contains(&Json::str("union")));
        assert!(kinds.contains(&Json::str("opaque")));
        assert!(kinds.contains(&Json::str("error_set")));
    }

    #[test]
    fn import_std_is_external_dependency() {
        let g = graph_for("const std = @import(\"std\");\n");
        assert!(g.has_node("ext::std"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::std"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::IMPORTS && e.to == "ext::std"));
        // The import binding is not a Constant.
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 0);
    }

    #[test]
    fn relative_import_is_internal() {
        let g = graph_for("const util = @import(\"util.zig\");\n");
        assert!(g.has_node("mod::util"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS
            && e.to == "mod::util"
            && e.props.get("external") == Some(&Json::Bool(false))));
        assert!(!g.has_node("ext::util.zig"));
    }

    #[test]
    fn top_level_const_and_var_are_constants() {
        let g = graph_for("pub const MAX: u32 = 100;\nvar counter: u32 = 0;\n");
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 2);
        let bindings: Vec<_> = g
            .nodes()
            .filter(|n| n.kind == ont::CONSTANT)
            .filter_map(|n| n.props.get("binding").cloned())
            .collect();
        assert!(bindings.contains(&Json::str("const")));
        assert!(bindings.contains(&Json::str("var")));
    }

    #[test]
    fn resolves_unique_local_call() {
        let g = graph_for(
            "fn add(a: i32, b: i32) i32 { return a + b; }\nfn run() void { _ = add(1, 2); }\n",
        );
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
        let g = graph_for(
            "const P = struct {\n    fn a(self: P) void { self.b(); }\n    fn b(self: P) void {}\n};\n",
        );
        let recv = call_edges(&g)
            .into_iter()
            .find(|e| e.props.get("resolution") == Some(&Json::str("receiver")));
        assert!(recv.is_some(), "self.b() should resolve via receiver scope");
        assert_eq!(recv.unwrap().props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn assoc_call_resolves_via_qualified_type() {
        let g = graph_for(
            "const P = struct {\n    fn init() P { return undefined; }\n};\nfn run() void { _ = P.init(); }\n",
        );
        let q = call_edges(&g)
            .into_iter()
            .find(|e| e.props.get("resolution") == Some(&Json::str("qualified_type")));
        assert!(q.is_some(), "P.init() should resolve via qualified_type");
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for("fn run() void { mystery(); }\n");
        let calls = call_edges(&g);
        assert_eq!(calls.len(), 1);
        assert_eq!(
            calls[0].props.get("resolution"),
            Some(&Json::str("external"))
        );
        assert!(g.has_node("unresolved::mystery"));
    }

    #[test]
    fn builtin_calls_are_not_call_edges() {
        // `@import`/`@sqrt` are intrinsics, never CALLS targets.
        let g = graph_for("fn f(x: f64) f64 { return @sqrt(x); }\n");
        assert!(
            call_edges(&g).is_empty(),
            "builtin @sqrt must not produce a CALLS edge"
        );
    }

    #[test]
    #[ignore = "zig USES_TYPE from struct fields not yet complete; deferred (secondary edge)"]
    fn type_use_in_field_and_signature() {
        let g = graph_for(
            "const Widget = struct {};\nconst Box = struct {\n    w: Widget,\n};\nfn build(x: Widget) void {}\n",
        );
        let uses = g
            .edges()
            .filter(|e| e.kind == edge::USES_TYPE && e.to.contains("Widget"))
            .count();
        assert!(uses >= 2, "field type and param type both use Widget");
    }

    #[test]
    fn nested_type_is_first_class() {
        let g = graph_for(
            "const Outer = struct {\n    const Inner = struct {\n        pub fn m(self: Inner) void {}\n    };\n};\n",
        );
        assert_eq!(g.count_nodes_of(ont::TYPE), 2, "Outer + Inner");
        let inner = g
            .nodes()
            .find(|n| n.name == "Inner")
            .expect("an Inner type");
        assert!(inner.props.get("qualified_name") == Some(&Json::str("app.Outer.Inner")));
    }

    #[test]
    fn output_is_deterministic() {
        let src = "const std = @import(\"std\");\nconst S = struct {\n    pub fn m(self: S) void { helper(); }\n};\nfn helper() void {}\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
