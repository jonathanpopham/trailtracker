//! Lower the Go CST into the canonical graph.
//!
//! This mirrors the Python lowering ([`crate::lang::python::lower`]) — same
//! conservative principles, same shared ontology — adapted to Go's surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to
//!    a concrete project definition only when a scope level yields exactly one
//!    candidate; several candidates become an ambiguous edge carrying the full
//!    `candidates` set; none resolves to an explicit `UnresolvedSymbol`.
//! 2. **Everything comes from real tokens.** Calls, receivers, imports, embedded
//!    interfaces, and type uses are read off the lossless tree, never guessed.
//!
//! Resolution uses a deterministic **scope ladder** (most specific first; the
//! first level with any candidate decides), the Go analogue of the Rust/Python
//! ladders: method receiver (`r.M()` where `r` is the enclosing method's receiver
//! variable) → local package → global. Each edge records which level resolved it,
//! so the call graph stays auditable.
//!
//! Honest mappings (see the IR Atlas):
//!   `func` → `Function` (a method, i.e. a func with a receiver → `HAS_METHOD`
//!   from its receiver `Type`); `type T struct{}` / `interface{}` / alias /
//!   defined → `Type` with the matching `type_kind`; package-level `const`/`var`
//!   → `Constant`; embedded interface (`interface { io.Reader }`) → `EXTENDS`
//!   (an interface extending an interface); `import` → `IMPORTS` (plus
//!   `ExternalDependency`/`DEPENDS_ON` for non-project paths).
//!
//! Honest gaps, deliberately *not* fabricated (existing kinds suffice for what we
//! do emit, so no IR extension is required):
//!   - Go interface satisfaction is **implicit** — there is no `implements`
//!     syntax, so no `IMPLEMENTS` edge can be emitted without a full type checker.
//!   - Struct embedding (`struct { io.Reader }`) is composition, not inheritance,
//!     so it is not lowered to `EXTENDS`.
//!   - Interface *method signatures* have no definition site, so they are not
//!     emitted as `Function` nodes (only concrete `func` declarations are).

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::go::lexer::{is_keyword, kind as tk};
use crate::lang::go::parser::node as cst;

/// Lower a whole project's worth of Go files into a graph. `manifest_deps` is
/// unused (the pipeline's manifest reader is Cargo-only); Go dependencies are
/// discovered from `import` declarations instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    // Project-local roots: the package plus every directory segment of every
    // file's module path. A Go import whose first path segment matches one of
    // these is treated as intra-project. Conservative: Go import paths are full
    // module paths (e.g. `github.com/x/y`), so without a `go.mod` reader almost
    // everything is honestly external — we never fabricate a local module.
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
        type_by_module: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("go"))],
    );

    // Pass B: create definition nodes + structural edges and build the symbol
    // tables. Method→type links and interface embedding are deferred to pass C so
    // a receiver type or embedded interface defined later (or in another file of
    // the same package) still resolves.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_extends: Vec<PendingExtends> = Vec::new();
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
                ("language", Json::str("go")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(leaf, edge::CONTAINS, file_id.clone(), vec![]);

        for item in f.root.child_nodes() {
            match item.kind {
                cst::IMPORT => lo.handle_import(item, &file_id, f.source),
                cst::FUNCTION => {
                    lo.handle_fn(item, &file_id, &module_join, f.source, &li, &mut pend_fns)
                }
                cst::TYPE_DECL => {
                    for spec in item.children_of(cst::TYPE_SPEC) {
                        lo.handle_type_spec(
                            spec,
                            &file_id,
                            &module_join,
                            f.source,
                            &li,
                            &mut pend_extends,
                        );
                    }
                }
                cst::VAR_DECL => {
                    lo.handle_value_decl(item, &file_id, &module_join, f.source, &li, "var")
                }
                cst::CONST_DECL => {
                    lo.handle_value_decl(item, &file_id, &module_join, f.source, &li, "const")
                }
                _ => {}
            }
        }
    }

    // Pass C: resolve calls (scope ladder), type usages, and interface embedding
    // against the now-complete symbol tables.
    for pf in &pend_fns {
        let ctx = Ctx {
            module_join: pf.module_join.clone(),
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
        if let Some(sig) = pf.signature {
            lo.emit_type_uses(&pf.id, sig, pf.source);
        }
    }
    // Deferred HAS_METHOD: now that every type spec is known, link each method to
    // its receiver type's concrete node(s). Fanned out across build-tag twins;
    // when the receiver type is not a project type (e.g. a method on a type alias
    // to an imported type) there is simply nothing to point at — never fabricated.
    for pf in &pend_fns {
        if let Some(t) = &pf.owner_type {
            if let Some(type_ids) = lo.type_by_module.get(&(pf.module_join.clone(), t.clone())) {
                for type_id in type_ids.clone() {
                    lo.g.add_edge(type_id, edge::HAS_METHOD, pf.id.clone(), vec![]);
                }
            }
        }
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
    /// Simple name → all plain-function node ids (global level).
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// Simple name → method node ids only (global method-call level).
    method_by_name: BTreeMap<String, Vec<String>>,
    /// (module_join, name) → function ids (local-package level).
    fn_by_module: BTreeMap<(String, String), Vec<String>>,
    /// (receiver_type, method_name) → method ids (receiver level).
    method_by_type: BTreeMap<(String, String), Vec<String>>,
    /// Simple name → type node ids.
    type_by_name: BTreeMap<String, Vec<String>>,
    /// (module_join, type_name) → type node ids. Used to resolve a method's
    /// receiver type to its concrete node(s) in pass C; a method can only be
    /// declared in the same package as its receiver type, so the module key is
    /// exact. Multiple ids arise only for build-tag twins (same type defined in
    /// mutually-exclusive `//go:build` files), in which case the link is fanned
    /// out to each — never dropped, never fabricated.
    type_by_module: BTreeMap<(String, String), Vec<String>>,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    block: Option<&'a Node>,
    signature: Option<&'a Node>,
    module_join: String,
    owner_type: Option<String>,
    recv_var: Option<String>,
}

/// A deferred `interface { Embedded }` link, resolved in pass C.
struct PendingExtends {
    type_id: String,
    base_name: String,
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
    module_join: String,
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

    /// Ensure the `Package → mod::a → mod::a/b …` directory chain exists and
    /// return the leaf module id (or the package id for a root-package file).
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
                vec![("language", Json::str("go"))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    fn handle_fn<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        module_join: &str,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
    ) {
        let name = name_text(item, src).unwrap_or("<anonymous>").to_string();
        let line = li.line_col(name_span_start(item)).line;
        let (recv_var, recv_type) = match item.child(cst::RECEIVER) {
            Some(r) => receiver_parts(r, src),
            None => (None, None),
        };
        let block = item.child(cst::BLOCK);
        let qual = match &recv_type {
            Some(t) => qual_name(module_join, std::slice::from_ref(t), &name),
            None => qual_name(module_join, &[], &name),
        };
        // File makes the id unique across files: Go allows several `func init()`
        // per package (and per file), so `qual#line` alone collides when sibling
        // files declare an `init` at the same line. Calls resolve via the name
        // indexes below, not by reconstructing this id, so the suffix is free.
        let rel = file_id.strip_prefix("file::").unwrap_or(file_id);
        let id = format!("fn::{qual}#{rel}:{line}");
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("go")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            ("has_body", Json::Bool(block.is_some())),
        ];
        if let Some(t) = &recv_type {
            props.push(("receiver_type", Json::str(t.clone())));
            props.push(("is_method", Json::Bool(true)));
        }
        if let Some(v) = &recv_var {
            props.push(("receiver_var", Json::str(v.clone())));
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, name.clone(), props);
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);

        // Indexes for the resolution ladder.
        if let Some(t) = &recv_type {
            self.method_by_name
                .entry(name.clone())
                .or_default()
                .push(id.clone());
            self.method_by_type
                .entry((t.clone(), name.clone()))
                .or_default()
                .push(id.clone());
            // A method belongs to its receiver type, but the type node ids are now
            // file+line specific, so the link cannot be reconstructed structurally.
            // It is resolved in pass C via `type_by_module` once every type spec
            // (possibly in another file of the same package) has been seen.
        } else {
            self.fn_by_name
                .entry(name.clone())
                .or_default()
                .push(id.clone());
            self.fn_by_module
                .entry((module_join.to_string(), name.clone()))
                .or_default()
                .push(id.clone());
        }

        pend_fns.push(PendingFn {
            id,
            source: src,
            block,
            signature: item.child(cst::SIGNATURE),
            module_join: module_join.to_string(),
            owner_type: recv_type,
            recv_var,
        });
    }

    fn handle_type_spec(
        &mut self,
        spec: &Node,
        file_id: &str,
        module_join: &str,
        src: &str,
        li: &LineIndex,
        pend_extends: &mut Vec<PendingExtends>,
    ) {
        let name = match name_text(spec, src) {
            Some(n) => n.to_string(),
            None => return,
        };
        let line = li.line_col(name_span_start(spec)).line;
        let header = spec.child(cst::HEADER);
        let kind = type_kind(header, src);
        let qual = qual_name(module_join, &[], &name);
        // File + line make the id unique across files so that build-tag twins
        // (the same type defined in mutually-exclusive `//go:build` variants of a
        // package) are kept as distinct nodes instead of collapsing via upsert.
        let rel = file_id.strip_prefix("file::").unwrap_or(file_id);
        let id = format!("type::{qual}#{rel}:{line}");
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str(kind)),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("go")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(spec.span.start as u64)),
                ("span_end", Json::U64(spec.span.end as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());
        self.type_by_module
            .entry((module_join.to_string(), name.clone()))
            .or_default()
            .push(id.clone());

        // Embedded interfaces become deferred EXTENDS links.
        if kind == "interface" {
            if let Some(h) = header {
                for base in interface_embeds(h, src) {
                    pend_extends.push(PendingExtends {
                        type_id: id.clone(),
                        base_name: base,
                    });
                }
            }
        }
    }

    /// Package-level `var`/`const` specs → `Constant` nodes, one per declared name
    /// in the leading name list. Only the simple name list is read (no expression
    /// inspection) — conservative, never guessed.
    fn handle_value_decl(
        &mut self,
        item: &Node,
        file_id: &str,
        module_join: &str,
        src: &str,
        li: &LineIndex,
        binding: &'static str,
    ) {
        for spec in item.children_of(cst::VALUE_SPEC) {
            for (name, start) in leading_names(spec, src) {
                let line = li.line_col(start).line;
                let id = format!("const::{}", qual_name(module_join, &[], &name));
                self.g.upsert_node(
                    id.clone(),
                    ont::CONSTANT,
                    name,
                    vec![
                        ("binding", Json::str(binding)),
                        ("language", Json::str("go")),
                        ("line", Json::U64(line as u64)),
                    ],
                );
                self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
            }
        }
    }

    /// Emit `IMPORTS` (and `ExternalDependency`/`DEPENDS_ON`) edges for every
    /// import path string found in the declaration, with its optional alias.
    fn handle_import(&mut self, item: &Node, file_id: &str, src: &str) {
        for (path, _alias) in import_specs(item, src) {
            if path.is_empty() {
                continue;
            }
            let root = path.split('/').next().unwrap_or(path.as_str()).to_string();
            if self.local_roots.contains(&root) {
                let mod_id = format!("mod::{root}");
                self.g.upsert_node(
                    mod_id.clone(),
                    ont::MODULE,
                    root,
                    vec![("language", Json::str("go"))],
                );
                self.g.add_edge(
                    file_id,
                    edge::IMPORTS,
                    mod_id,
                    vec![("path", Json::str(path)), ("external", Json::Bool(false))],
                );
            } else {
                let leaf = path.rsplit('/').next().unwrap_or(path.as_str()).to_string();
                let dep_id = format!("ext::{path}");
                self.g.upsert_node(
                    dep_id.clone(),
                    ont::EXTERNAL_DEPENDENCY,
                    leaf,
                    vec![
                        ("external", Json::Bool(true)),
                        ("source", Json::str("import")),
                    ],
                );
                self.g.add_edge(
                    file_id,
                    edge::IMPORTS,
                    dep_id.clone(),
                    vec![("path", Json::str(path)), ("external", Json::Bool(true))],
                );
                self.g
                    .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
            }
        }
    }

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        if call.method {
            // Receiver scope: `r.M()` where `r` is the enclosing method's receiver
            // variable resolves against the receiver type's methods.
            if let (Some(rv), Some(ot)) = (&ctx.recv_var, &ctx.owner_type) {
                if call.receiver.as_deref() == Some(rv.as_str()) {
                    let c = self.methods_of(ot, &call.name);
                    if !c.is_empty() {
                        return mk(c, "receiver");
                    }
                }
            }
            // Unknown receiver type (no inference). The honest candidate set is
            // every same-name method PLUS every same-name free function — a Go
            // selector call can also be a package-qualified call to a free
            // function (`pkg.F()`).
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

        // Local package, then global. Go bare calls are same-package functions;
        // cross-package calls are always selector-qualified (the `method` branch).
        let c = self.fns_in_module(&ctx.module_join, &call.name);
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

    /// Resolve a deferred embedded-interface link into a concrete `EXTENDS` edge,
    /// pointing at the project type when unique, otherwise an explicit
    /// `UnresolvedSymbol` (a stdlib/third-party interface we cannot see).
    fn emit_extends(&mut self, pe: &PendingExtends) {
        let target = match self.unique_type(&pe.base_name) {
            Some(id) => id,
            None => {
                let id = unresolved_id(&pe.base_name);
                self.ensure_unresolved(&id, &pe.base_name, "embedded_interface");
                id
            }
        };
        self.g.add_edge(
            pe.type_id.clone(),
            edge::EXTENDS,
            target,
            vec![("base_name", Json::str(pe.base_name.clone()))],
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

    /// Add `USES_TYPE` edges for identifiers in a function `Signature` (parameter
    /// and result types) that name a unique project type.
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

/// Directory module-join for a file's module path: `["a","b"]` → `"a/b"`,
/// `[]` → "".
fn mod_join(path: &[String]) -> String {
    path.join("/")
}

/// `module/scope….name` — the qualified name and the basis for node ids.
fn qual_name(module_join: &str, scope: &[String], name: &str) -> String {
    let mut parts: Vec<String> = Vec::new();
    if !module_join.is_empty() {
        parts.push(module_join.to_string());
    }
    parts.extend(scope.iter().cloned());
    parts.push(name.to_string());
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

/// Extract `(receiver_var, receiver_type)` from a method receiver `(r *T)`.
/// Identifiers inside a `[...]` type-parameter group are ignored. With two
/// top-level identifiers the first is the variable and the second the type; with
/// one, it is the (unnamed-receiver) type.
fn receiver_parts(recv: &Node, src: &str) -> (Option<String>, Option<String>) {
    let mut idents: Vec<String> = Vec::new();
    for c in &recv.children {
        if let Child::Token(t) = c {
            if t.kind == tk::IDENT && !is_keyword(t.span.text(src)) {
                idents.push(t.span.text(src).to_string());
            }
        }
    }
    match idents.len() {
        0 => (None, None),
        1 => (None, Some(idents.remove(0))),
        _ => {
            let var = idents.remove(0);
            let ty = idents.remove(0);
            (Some(var), Some(ty))
        }
    }
}

/// Classify a `TypeSpec` header. `=` ⇒ alias; otherwise a top-level `struct` /
/// `interface` keyword names the kind; anything else is a defined (named) type.
fn type_kind(header: Option<&Node>, src: &str) -> &'static str {
    let h = match header {
        Some(h) => h,
        None => return "defined",
    };
    let mut has_struct = false;
    let mut has_interface = false;
    for t in h.tokens() {
        match t.span.text(src) {
            "=" => return "alias",
            "struct" => has_struct = true,
            "interface" => has_interface = true,
            _ => {}
        }
    }
    if has_interface {
        "interface"
    } else if has_struct {
        "struct"
    } else {
        "defined"
    }
}

/// Embedded-interface base names from an interface body. A body line that holds a
/// `Paren` group is a method signature (skipped); a line carrying a `|` or `~` is
/// a type-set constraint element (skipped); any remaining line's final identifier
/// is an embedded interface name (`Reader` from `io.Reader`).
fn interface_embeds(header: &Node, src: &str) -> Vec<String> {
    let brace = match header.walk().find(|n| n.kind == cst::BRACE) {
        Some(b) => b,
        None => return Vec::new(),
    };
    let mut embeds = Vec::new();
    let mut line = Line::default();
    for c in &brace.children {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) if t.kind == tk::NEWLINE => line.flush_into(&mut embeds),
            Child::Token(t) => match t.span.text(src) {
                "{" | "}" => {}
                "|" | "~" => line.is_constraint = true,
                txt if t.kind == tk::IDENT && !is_keyword(txt) => line.idents.push(txt.to_string()),
                _ => {}
            },
            Child::Node(n) if n.kind == cst::PAREN => line.is_method = true,
            Child::Node(_) => {}
        }
    }
    line.flush_into(&mut embeds);
    embeds
}

/// Accumulator for one line of an interface body while detecting embeds.
#[derive(Default)]
struct Line {
    idents: Vec<String>,
    is_method: bool,
    is_constraint: bool,
}

impl Line {
    /// A line that is neither a method signature nor a type-set constraint and
    /// carries a trailing identifier is an embedded interface; record it. Resets
    /// for the next line either way.
    fn flush_into(&mut self, embeds: &mut Vec<String>) {
        if !self.is_method && !self.is_constraint {
            if let Some(last) = self.idents.last() {
                embeds.push(last.clone());
            }
        }
        self.idents.clear();
        self.is_method = false;
        self.is_constraint = false;
    }
}

/// Leading identifier list of a value spec (`a, b int = …`), as `(name, start)`.
/// Stops at the first token that is not an identifier or a comma.
fn leading_names(spec: &Node, src: &str) -> Vec<(String, u32)> {
    let mut names = Vec::new();
    let mut expect_name = true;
    for c in &spec.children {
        match c {
            Child::Token(t) if t.trivia || t.kind == tk::NEWLINE => {}
            Child::Token(t)
                if expect_name && t.kind == tk::IDENT && !is_keyword(t.span.text(src)) =>
            {
                names.push((t.span.text(src).to_string(), t.span.start));
                expect_name = false;
            }
            Child::Token(t) if !expect_name && t.span.text(src) == "," => {
                expect_name = true;
            }
            _ => break,
        }
    }
    names
}

/// Import paths + optional aliases from an `Import` declaration. Walks the leaf
/// tokens in source order; for each string literal the immediately preceding
/// identifier (or `.`) on the same line is its alias.
fn import_specs(item: &Node, src: &str) -> Vec<(String, Option<String>)> {
    let mut out = Vec::new();
    let mut prev: Option<String> = None;
    let mut toks = Vec::new();
    flatten_tokens(item, src, &mut toks);
    for (kind, text) in toks {
        match kind {
            tk::NEWLINE => prev = None,
            tk::STRING | tk::RAW_STRING => {
                out.push((unquote(text), prev.take()));
            }
            // The `import` keyword and grouping parens are not aliases.
            tk::IDENT if is_keyword(text) => prev = None,
            tk::IDENT => prev = Some(text.to_string()),
            tk::PUNCT if text == "." => prev = Some(".".to_string()),
            tk::PUNCT if text == "(" || text == ")" => {}
            _ => prev = None,
        }
    }
    out
}

/// Collect every leaf token (skipping pure trivia, keeping `newline`) in order.
fn flatten_tokens<'a>(node: &Node, src: &'a str, out: &mut Vec<(&'static str, &'a str)>) {
    for c in &node.children {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => out.push((t.kind, t.span.text(src))),
            Child::Node(n) => flatten_tokens(n, src, out),
        }
    }
}

/// Strip the surrounding quotes/backticks from a string literal's source text.
fn unquote(text: &str) -> String {
    let bytes = text.as_bytes();
    if bytes.len() >= 2 {
        let first = bytes[0];
        let last = bytes[bytes.len() - 1];
        if (first == b'"' && last == b'"') || (first == b'`' && last == b'`') {
            return text[1..text.len() - 1].to_string();
        }
    }
    text.to_string()
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
            Child::Token(t) if t.trivia || t.kind == tk::NEWLINE => {}
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
/// recursing into nested groups. Keywords are excluded. A type conversion
/// `T(x)` lexes identically to a call and is reported as one — conservative and
/// resolved like any other reference.
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
        // keyword (control-flow `if`/`for`/`switch` followed by `(` etc.).
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
    use crate::lang::go::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("svc.go", src);
        let file = SourceFile {
            rel_path: "svc.go".to_string(),
            module_path: vec!["svc".to_string()],
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    fn call_edges(g: &Graph) -> Vec<&crate::graph::GraphEdge> {
        g.edges().filter(|e| e.kind == edge::CALLS).collect()
    }

    #[test]
    fn emits_function_type_module_nodes() {
        let g = graph_for(
            "package svc\ntype Server struct{}\nfunc (s *Server) Run() {}\nfunc Helper() {}\n",
        );
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "Run + Helper");
        assert_eq!(g.count_nodes_of(ont::TYPE), 1, "Server is a Type");
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "module svc");
        // Run is a method of Server.
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD));
    }

    #[test]
    fn struct_type_kind_is_struct() {
        let g = graph_for("package svc\ntype Point struct{ X int }\n");
        let ty = g
            .nodes()
            .find(|n| n.kind == ont::TYPE)
            .expect("a Type node");
        assert_eq!(ty.props.get("type_kind"), Some(&Json::str("struct")));
        assert_eq!(ty.props.get("language"), Some(&Json::str("go")));
    }

    #[test]
    fn interface_and_alias_kinds() {
        let g = graph_for("package svc\ntype Reader interface{ Read() }\ntype ID = int\n");
        let kinds: Vec<_> = g
            .nodes()
            .filter(|n| n.kind == ont::TYPE)
            .filter_map(|n| n.props.get("type_kind").cloned())
            .collect();
        assert!(kinds.contains(&Json::str("interface")));
        assert!(kinds.contains(&Json::str("alias")));
    }

    #[test]
    fn resolves_unique_local_call() {
        let g = graph_for(
            "package svc\nfunc add(a, b int) int { return a + b }\nfunc run() { add(1, 2) }\n",
        );
        let calls = call_edges(&g);
        let add = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("add")))
            .expect("a call to add");
        assert!(add.to.starts_with("fn::svc.add"));
        assert_eq!(add.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(add.props.get("resolution"), Some(&Json::str("local")));
    }

    #[test]
    fn receiver_call_resolves() {
        let g = graph_for(
            "package svc\ntype P struct{}\nfunc (p *P) a() { p.b() }\nfunc (p *P) b() {}\n",
        );
        let calls = call_edges(&g);
        let recv = calls
            .iter()
            .find(|e| e.props.get("resolution") == Some(&Json::str("receiver")));
        assert!(recv.is_some(), "p.b() should resolve via the receiver type");
        assert_eq!(recv.unwrap().props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for("package svc\nfunc run() { mystery() }\n");
        let calls = call_edges(&g);
        assert_eq!(calls.len(), 1);
        assert_eq!(
            calls[0].props.get("resolution"),
            Some(&Json::str("external"))
        );
        assert!(g.has_node("unresolved::mystery"));
    }

    #[test]
    fn external_import_creates_dependency() {
        let g = graph_for("package svc\nimport (\n\t\"fmt\"\n\tm \"math\"\n)\n");
        assert!(g.has_node("ext::fmt"));
        assert!(g.has_node("ext::math"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::fmt"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn interface_embedding_emits_extends() {
        let g = graph_for(
            "package svc\ntype Base interface{ A() }\ntype Derived interface{\n\tBase\n\tB()\n}\n",
        );
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an EXTENDS edge");
        assert!(ext.from.starts_with("type::svc.Derived"));
        assert!(ext.to.starts_with("type::svc.Base"));
    }

    #[test]
    fn package_level_var_and_const_are_constants() {
        let g =
            graph_for("package svc\nconst Pi = 3.14\nvar Count = 0\nfunc f() { x := 1; _ = x }\n");
        // Pi and Count are package-level Constants; the func-local x is not.
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 2);
        let names: Vec<_> = g
            .nodes()
            .filter(|n| n.kind == ont::CONSTANT)
            .map(|n| n.name.clone())
            .collect();
        assert!(names.contains(&"Pi".to_string()));
        assert!(names.contains(&"Count".to_string()));
    }

    #[test]
    fn type_use_in_signature() {
        let g = graph_for("package svc\ntype Widget struct{}\nfunc build(w *Widget) {}\n");
        assert!(
            g.edges()
                .any(|e| e.kind == edge::USES_TYPE && e.to.contains("Widget")),
            "param type should create USES_TYPE"
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src = "package svc\nimport \"fmt\"\ntype S struct{}\nfunc (s *S) m() { helper() }\nfunc helper() {}\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }

    // --- global_method rung: the singleton law -------------------------------

    #[test]
    fn method_call_ambiguous_when_free_function_shares_name() {
        // One method named `Parse` plus a same-name package function: an
        // unknown-receiver selector call must be AMBIGUOUS, never guessed.
        let src = "package svc\ntype T struct{}\nfunc (t *T) Parse() {}\nfunc Parse() {}\nfunc run(x any) { x.Parse() }\n";
        let g = graph_for(src);
        let calls = call_edges(&g);
        let e = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("Parse")) && e.from.contains("run"))
            .expect("the x.Parse() call");
        assert_eq!(e.props.get("resolution"), Some(&Json::str("global_method")));
        assert_eq!(e.props.get("ambiguous"), Some(&Json::Bool(true)));
        assert_eq!(e.props.get("candidate_count"), Some(&Json::U64(2)));
    }

    #[test]
    fn method_call_never_resolves_to_free_function_alone() {
        // No project method named `Log`: a selector call on an unknown receiver
        // stays external even when a package function shares the name.
        let src = "package svc\nfunc Log() {}\nfunc run(x any) { x.Log() }\n";
        let g = graph_for(src);
        let calls = call_edges(&g);
        let e = calls
            .iter()
            .find(|e| {
                e.props.get("callee") == Some(&Json::str("Log"))
                    && e.props.get("method") == Some(&Json::Bool(true))
            })
            .expect("the x.Log() call");
        assert_eq!(e.props.get("resolution"), Some(&Json::str("external")));
        assert_eq!(e.props.get("resolved"), Some(&Json::Bool(false)));
    }
}
