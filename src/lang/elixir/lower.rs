//! Lower the Elixir CST into the canonical graph.
//!
//! This mirrors the Ruby lowering ([`crate::lang::ruby::lower`]) — same
//! conservative principles, same shared ontology — adapted to Elixir's surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to a
//!    concrete project definition only when a scope level yields exactly one
//!    candidate; several candidates are emitted as an ambiguous edge with the full
//!    `candidates` set; none resolves to an explicit unresolved node.
//! 2. **Everything comes from real tokens.** Calls, aliases, attributes, and
//!    function names are read off the lossless tree, never guessed.
//!
//! Resolution uses a deterministic **scope ladder** (most specific first; the
//! first level with any candidate decides): for a qualified call `Mod.fun` the
//! module name decides; for a bare call, the enclosing module's functions
//! (implicit self) → local file module → global. Each edge records which level
//! resolved it, so the call graph stays auditable.
//!
//! Honest mappings (see the IR Atlas):
//!   `def`/`defp`/`defmacro`/`defmacrop` → `Function` (a function inside a module
//!   → `HAS_METHOD` from the enclosing module `Type`); `defmodule` → `Type`
//!   (`type_kind: module` — an Elixir module is the first-class, function-bearing
//!   namespace, exactly the construct `HAS_METHOD` hangs off, so it is a `Type`
//!   like Ruby's modules); `defprotocol` → `Type` (`type_kind: protocol`);
//!   `defimpl` → `Type` (`type_kind: impl`); `import`/`alias`/`require`/`use` →
//!   `IMPORTS` (plus `ExternalDependency`/`DEPENDS_ON` for non-project modules);
//!   module-level `@attr value` → `Constant` (Elixir's module attributes are the
//!   constant/metadata bindings — `@doc`, `@spec`, and user attributes alike).
//!
//! No home in the current IR: `defstruct` defines the *enclosing* module's struct
//! shape — the module is already a `Type`, so `defstruct` is folded into it rather
//! than fabricating a second node; and Elixir has no `DECORATES` kind, so
//! `@behaviour`/`@derive`-style attributes stay plain `Constant`s. See
//! `docs/ir-atlas.md` candidate extensions.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::elixir::lexer::{is_keyword, kind as tk};
use crate::lang::elixir::parser::node as cst;
use crate::lang::frontend::SourceFile;

/// Lower a whole project's worth of Elixir files into a graph. `manifest_deps` is
/// unused (the pipeline's manifest reader is Cargo-only); dependencies are
/// discovered from `import`/`alias`/`require`/`use` instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    // Project-local roots: the package, every module-path segment, and the first
    // segment of every module/protocol/impl defined anywhere in the batch. An
    // alias whose root is one of these is intra-project, not an external dep.
    let mut local_roots: BTreeSet<String> = BTreeSet::new();
    local_roots.insert(package.to_string());
    for f in files {
        for seg in &f.module_path {
            local_roots.insert(seg.clone());
        }
        collect_module_roots(f.root, f.source, &mut local_roots);
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
        vec![("ecosystem", Json::str("elixir"))],
    );

    // Pass B: definition nodes + structural edges + symbol tables.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
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
                ("language", Json::str("elixir")),
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
        };
        lo.walk_stmts(f.root, &[], None, false, &mut walk);
    }

    // Pass C: resolve calls (scope ladder) and type usages against the now-complete
    // symbol tables.
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

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    local_roots: BTreeSet<String>,
    /// Simple name → all function node ids (global level).
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// Simple name → module-function ids only (global qualified-call level).
    method_by_name: BTreeMap<String, Vec<String>>,
    /// (module_join, name) → function ids (local-file-module level).
    fn_by_module: BTreeMap<(String, String), Vec<String>>,
    /// (type_name, fn_name) → function ids (receiver/module level).
    method_by_type: BTreeMap<(String, String), Vec<String>>,
    /// Simple name → type (module/protocol/impl) node ids.
    type_by_name: BTreeMap<String, Vec<String>>,
}

/// Mutable per-file walk context, bundled to keep recursion signatures small.
struct Walk<'a, 's> {
    file_id: &'s str,
    module_join: &'s str,
    src: &'a str,
    li: &'s LineIndex,
    pend_fns: &'s mut Vec<PendingFn<'a>>,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    body: &'a Node,
    module_join: String,
    owner_type: Option<String>,
}

/// The enclosing module/protocol/impl while walking, for methods.
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
                vec![("language", Json::str("elixir"))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    /// Walk a statement container, creating definition nodes and recursing into
    /// nested scopes. `owner` is the nearest enclosing module/protocol/impl
    /// (cleared inside a function); `in_def` gates `Constant` emission.
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
                cst::FUNCTION => self.handle_def(item, scope, owner, w),
                cst::DEFMODULE => self.handle_type(item, scope, "module", w),
                cst::DEFPROTOCOL => self.handle_type(item, scope, "protocol", w),
                cst::DEFIMPL => self.handle_type(item, scope, "impl", w),
                cst::EXPR_STMT => self.handle_expr_stmt(item, scope, owner, in_def, w),
                cst::BLOCK => {
                    // A bare block (e.g. a clause sub-body): not a new scope.
                    self.walk_stmts(item, scope, owner, in_def, w);
                }
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
        let name = def_name(item, w.src).unwrap_or_else(|| "<anonymous>".to_string());
        let line = w.li.line_col(name_span_start(item)).line;
        let qual = qual_name(w.module_join, scope, &name);
        let id = format!("fn::{qual}#{line}");
        let body: &Node = item.child(cst::BLOCK).unwrap_or(item);
        let def_kw = def_keyword(item, w.src);
        let is_private = matches!(def_kw.as_deref(), Some("defp") | Some("defmacrop"));
        let is_macro = matches!(def_kw.as_deref(), Some("defmacro") | Some("defmacrop"));
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("elixir")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            ("has_body", Json::Bool(item.child(cst::BLOCK).is_some())),
            ("private", Json::Bool(is_private)),
            ("macro", Json::Bool(is_macro)),
        ];
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
        self.fn_by_module
            .entry((w.module_join.to_string(), name.clone()))
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

        w.pend_fns.push(PendingFn {
            id,
            source: w.src,
            body,
            module_join: w.module_join.to_string(),
            owner_type: owner.map(|o| o.name.clone()),
        });

        // A nested defmodule inside a function body is rare but legal; recurse for
        // any nested definitions with a fresh (None) owner.
        if let Some(block) = item.child(cst::BLOCK) {
            let mut child_scope = scope.to_vec();
            child_scope.push(name);
            self.walk_stmts(block, &child_scope, None, true, w);
        }
    }

    /// `defmodule`/`defprotocol`/`defimpl` → `Type`. `kind` is the `type_kind`.
    fn handle_type<'a>(
        &mut self,
        item: &'a Node,
        scope: &[String],
        kind: &'static str,
        w: &mut Walk<'a, '_>,
    ) {
        let name = type_name(item, w.src).unwrap_or_else(|| "<anonymous>".to_string());
        let line = w.li.line_col(name_span_start(item)).line;
        let qual = qual_name(w.module_join, scope, &name);
        // A `defimpl P, for: M` is named after its protocol `P` and would collide
        // with `defprotocol P`'s node (upsert would merge them, dropping the impl).
        // Disambiguate impl nodes by span so each is distinct.
        let id = if kind == "impl" {
            format!("type::{qual}#{}", item.span.start)
        } else {
            format!("type::{qual}")
        };
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str(kind)),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("elixir")),
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

        let owner = Owner {
            name: name.clone(),
            id: id.clone(),
        };
        let mut child_scope = scope.to_vec();
        child_scope.push(name);
        for block in item.children_of(cst::BLOCK) {
            self.walk_stmts(block, &child_scope, Some(&owner), false, w);
        }
    }

    /// An expression statement: detect `import`/`alias`/`require`/`use` and
    /// module-level `@attr value` constants.
    fn handle_expr_stmt<'a>(
        &mut self,
        item: &'a Node,
        scope: &[String],
        _owner: Option<&Owner>,
        in_def: bool,
        w: &mut Walk<'a, '_>,
    ) {
        let toks = top_level_tokens(item, w.src);
        let first = match toks.first() {
            Some(t) => *t,
            None => return,
        };
        if first.kind == tk::ATTRIBUTE {
            // `@name value` at module scope is a Constant; a bare `@name` (an
            // attribute read) or one inside a function body is not a definition.
            // The value may be a trailing token *or* a group (`@keys [:a, :b]`),
            // so test for any significant element after the attribute.
            let has_value = significant_children(item, w.src).len() > 1;
            if !in_def && has_value {
                let attr = first.text.trim_start_matches('@');
                if !attr.is_empty() {
                    let qual = qual_name(w.module_join, scope, attr);
                    let id = format!("const::{qual}");
                    let line = w.li.line_col(first.span_start).line;
                    self.g.upsert_node(
                        id.clone(),
                        ont::CONSTANT,
                        attr.to_string(),
                        vec![
                            ("binding", Json::str("module_attribute")),
                            ("language", Json::str("elixir")),
                            ("line", Json::U64(line as u64)),
                        ],
                    );
                    self.g.add_edge(w.file_id, edge::DECLARES, id, vec![]);
                }
            }
            return;
        }
        match first.text {
            "import" | "alias" | "require" | "use" => {
                if let Some(full) = alias_path(item, w.src) {
                    self.emit_import(w.file_id, &full, first.text);
                }
            }
            _ => {}
        }
    }

    /// Emit the `IMPORTS` edge for an `import`/`alias`/`require`/`use` of a module
    /// alias, plus the `ExternalDependency`/`DEPENDS_ON` pair when not project-local.
    fn emit_import(&mut self, file_id: &str, full: &str, keyword: &str) {
        if full.is_empty() {
            return;
        }
        let root = full.split('.').next().unwrap_or(full).to_string();
        let internal = self.local_roots.contains(&root);
        if internal {
            let mod_id = format!("mod::{full}");
            let leaf = full.rsplit('.').next().unwrap_or(full).to_string();
            self.g.upsert_node(
                mod_id.clone(),
                ont::MODULE,
                leaf,
                vec![("language", Json::str("elixir"))],
            );
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                mod_id,
                vec![
                    ("path", Json::str(full.to_string())),
                    ("external", Json::Bool(false)),
                    ("kind", Json::str(keyword.to_string())),
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
                    ("source", Json::str(keyword.to_string())),
                ],
            );
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                dep_id.clone(),
                vec![
                    ("path", Json::str(full.to_string())),
                    ("external", Json::Bool(true)),
                    ("kind", Json::str(keyword.to_string())),
                ],
            );
            self.g
                .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
        }
    }

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        if call.method {
            // `Mod.fun` / `recv.fun`: a known module receiver decides; otherwise a
            // global match among module functions, preserving any ambiguity.
            if let Some(recv) = &call.receiver {
                let c = self.methods_of(recv, &call.name);
                if !c.is_empty() {
                    return mk(c, "receiver");
                }
            }
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
        // A bare call inside a module may be a same-module function (implicit self).
        if let Some(owner) = &ctx.owner_type {
            let c = self.methods_of(owner, &call.name);
            if !c.is_empty() {
                return mk(c, "implicit_self");
            }
        }
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

    /// Add `USES_TYPE` edges for alias references in a function body that name a
    /// unique project module/protocol (e.g. `Widget.new`, `%Geo.Point{}`).
    fn emit_type_uses(&mut self, from_id: &str, body: &Node, src: &str) {
        let mut seen: Vec<String> = Vec::new();
        for n in body.walk() {
            for t in n.tokens() {
                if t.kind != tk::IDENT {
                    continue;
                }
                let name = t.span.text(src);
                if !is_alias(name) {
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

/// An Elixir *alias* (a module name) starts with an uppercase ASCII letter.
fn is_alias(name: &str) -> bool {
    name.chars()
        .next()
        .map(|c| c.is_ascii_uppercase())
        .unwrap_or(false)
}

/// The `def` keyword token text (`def`/`defp`/`defmacro`/`defmacrop`).
fn def_keyword(item: &Node, src: &str) -> Option<String> {
    item.tokens().next().map(|t| t.span.text(src).to_string())
}

/// The defined function's simple name — the first token of its `Name` node.
fn def_name(item: &Node, src: &str) -> Option<String> {
    let nm = item.child(cst::NAME)?;
    nm.tokens().next().map(|t| t.span.text(src).to_string())
}

fn name_span_start(item: &Node) -> u32 {
    item.child(cst::NAME)
        .map(|n| n.span.start)
        .unwrap_or(item.span.start)
}

/// The defined module/protocol/impl simple name — the last segment of its `Name`
/// alias path (`Geo.Point` → `Point`).
fn type_name(item: &Node, src: &str) -> Option<String> {
    let nm = item.child(cst::NAME)?;
    let mut last: Option<&str> = None;
    for t in nm.tokens() {
        let txt = t.span.text(src);
        if txt != "." && txt != "::" {
            last = Some(txt);
        }
    }
    last.map(|s| s.to_string())
}

/// The full alias path of an `import`/`alias`/`require`/`use` target
/// (`alias Foo.Bar` → `"Foo.Bar"`). Reads the leading run of alias idents joined
/// by `.`, stopping at the first non-alias token (e.g. a `, only:` option).
fn alias_path(item: &Node, src: &str) -> Option<String> {
    let toks = top_level_tokens(item, src);
    let mut segs: Vec<&str> = Vec::new();
    let mut started = false;
    for t in toks.iter().skip(1) {
        if t.kind == tk::IDENT {
            if !started && !is_alias(t.text) {
                break; // first segment must be an alias (capitalized)
            }
            started = true;
            segs.push(t.text);
        } else if t.text == "." {
            if !started {
                break;
            }
        } else {
            break;
        }
    }
    if segs.is_empty() {
        None
    } else {
        Some(segs.join("."))
    }
}

/// A flat token (text + kind + start) for the small token-list helpers.
#[derive(Clone, Copy)]
struct Tok<'a> {
    text: &'a str,
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

/// Collect the first segment of every module/protocol/impl name in a tree into
/// `roots` — used to recognize project-local aliases for import classification.
fn collect_module_roots(root: &Node, src: &str, roots: &mut BTreeSet<String>) {
    for n in root.walk() {
        if matches!(n.kind, cst::DEFMODULE | cst::DEFPROTOCOL | cst::DEFIMPL) {
            if let Some(nm) = n.child(cst::NAME) {
                if let Some(first) = nm.tokens().find(|t| t.kind == tk::IDENT) {
                    let txt = first.span.text(src);
                    if is_alias(txt) {
                        roots.insert(txt.to_string());
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

fn is_def_node(kind: &str) -> bool {
    matches!(
        kind,
        cst::FUNCTION | cst::DEFMODULE | cst::DEFPROTOCOL | cst::DEFIMPL
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
        // Qualified/remote call: `.` name (optionally followed by `(...)`).
        if matches!(tok_text(&els[i]), Some(".")) {
            if i + 1 < n && is_ident_el(&els[i + 1]) {
                let name = tok_text(&els[i + 1]).unwrap_or("");
                // Skip an attribute *assignment* (`obj.x = …`).
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
        // Bare call: name `(...)`, not preceded by `.`/`def` and not a keyword.
        if is_ident_el(&els[i]) {
            let prev = if i > 0 { tok_text(&els[i - 1]) } else { None };
            let text = tok_text(&els[i]).unwrap_or("");
            if prev != Some(".")
                && prev != Some("def")
                && prev != Some("defp")
                && prev != Some("defmacro")
                && prev != Some("defmacrop")
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
    use crate::lang::elixir::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("app.ex", src);
        let file = SourceFile {
            rel_path: "app.ex".to_string(),
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
    fn lossless_round_trip_through_lowering() {
        // The whole pipeline (parse → lower) must not perturb the source; the CST
        // it lowers from still reconstructs byte-for-byte.
        let src = "\
defmodule App.Calc do
  @moduledoc \"calc\"
  alias App.Helper
  import Enum, only: [sum: 1]

  @pi 3.14

  def area(r), do: @pi * r * r

  def total(list) do
    list
    |> Enum.map(fn x -> double(x) end)
    |> Enum.sum()
  end

  defp double(x), do: x * 2
end
";
        let tree = parse("calc.ex", src);
        assert!(tree.is_lossless(), "parse must round-trip before lowering");
        let file = SourceFile {
            rel_path: "lib/app/calc.ex".to_string(),
            module_path: vec!["app".to_string(), "calc".to_string()],
            source: &tree.source,
            root: &tree.root,
        };
        let g = lower("app", std::slice::from_ref(&file), &[]);
        assert!(g.count_nodes_of(ont::TYPE) >= 1);
        assert!(g.count_nodes_of(ont::FUNCTION) >= 3);
    }

    #[test]
    fn emits_function_and_module_type_nodes() {
        let g = graph_for("defmodule C do\n  def m do\n  end\nend\n\ndef f do\nend\n");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "f + C.m");
        assert_eq!(g.count_nodes_of(ont::TYPE), 1, "defmodule C is a Type");
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD));
    }

    #[test]
    fn module_protocol_impl_type_kinds() {
        let g = graph_for(
            "defmodule M do\nend\n\ndefprotocol P do\n  def d(x)\nend\n\ndefimpl P, for: M do\n  def d(x), do: x\nend\n",
        );
        let kinds: Vec<&Json> = g
            .nodes()
            .filter(|n| n.kind == ont::TYPE)
            .filter_map(|n| n.props.get("type_kind"))
            .collect();
        assert!(kinds.contains(&&Json::str("module")));
        assert!(kinds.contains(&&Json::str("protocol")));
        assert!(kinds.contains(&&Json::str("impl")));
        for n in g.nodes().filter(|n| n.kind == ont::TYPE) {
            assert_eq!(n.props.get("language"), Some(&Json::str("elixir")));
        }
    }

    #[test]
    fn resolves_unique_local_call() {
        let g = graph_for("def add(a, b) do\n  a + b\nend\n\ndef run do\n  add(1, 2)\nend\n");
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
    fn implicit_self_call_resolves() {
        let g = graph_for(
            "defmodule P do\n  def a do\n    helper()\n  end\n  def helper do\n  end\nend\n",
        );
        let calls = call_edges(&g);
        let h = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("helper")))
            .expect("a call to helper");
        assert_eq!(h.props.get("resolution"), Some(&Json::str("implicit_self")));
    }

    #[test]
    fn qualified_call_resolves_via_receiver() {
        let g = graph_for(
            "defmodule M do\n  def go do\n    Helper.work()\n  end\nend\n\ndefmodule Helper do\n  def work do\n  end\nend\n",
        );
        let calls = call_edges(&g);
        let w = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("work")))
            .expect("a call to work");
        assert_eq!(w.props.get("resolution"), Some(&Json::str("receiver")));
        assert_eq!(w.props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for("def run do\n  IO.puts(mystery())\nend\n");
        let calls = call_edges(&g);
        assert!(calls
            .iter()
            .any(|e| e.props.get("callee") == Some(&Json::str("mystery"))
                && e.props.get("resolution") == Some(&Json::str("external"))));
        assert!(g.has_node("unresolved::mystery"));
    }

    #[test]
    fn alias_and_import_create_dependencies() {
        let g = graph_for("defmodule App do\n  alias External.Thing\n  import Enum\nend\n");
        assert!(g.has_node("ext::External"));
        assert!(g.has_node("ext::Enum"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::Enum"));
        assert!(
            g.edges()
                .any(|e| e.kind == edge::IMPORTS
                    && e.props.get("external") == Some(&Json::Bool(true)))
        );
    }

    #[test]
    fn internal_alias_is_not_external() {
        let g = graph_for(
            "defmodule App.User do\nend\n\ndefmodule App.Web do\n  alias App.User\nend\n",
        );
        // `App` is a project root, so `alias App.User` is internal.
        assert!(g.edges().any(
            |e| e.kind == edge::IMPORTS && e.props.get("external") == Some(&Json::Bool(false))
        ));
    }

    #[test]
    fn module_attribute_is_constant() {
        let g = graph_for(
            "defmodule C do\n  @version \"1.0\"\n  @spec f() :: :ok\n  def f, do: :ok\nend\n",
        );
        // @version and @spec are constants; the function f is not.
        assert!(g.count_nodes_of(ont::CONSTANT) >= 2);
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::CONSTANT && n.name == "version"));
    }

    #[test]
    fn private_and_macro_flags() {
        let g =
            graph_for("defmodule C do\n  defp secret do\n  end\n  defmacro mac do\n  end\nend\n");
        let secret = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "secret")
            .expect("the private function");
        assert_eq!(secret.props.get("private"), Some(&Json::Bool(true)));
        let mac = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "mac")
            .expect("the macro");
        assert_eq!(mac.props.get("macro"), Some(&Json::Bool(true)));
    }

    #[test]
    fn type_use_via_alias_reference() {
        let g = graph_for("defmodule Widget do\nend\n\ndef build do\n  Widget.new()\nend\n");
        assert!(
            g.edges()
                .any(|e| e.kind == edge::USES_TYPE && e.to.contains("Widget")),
            "Widget.new should create USES_TYPE"
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src =
            "defmodule C do\n  alias Ext.Thing\n  def m do\n    helper()\n  end\nend\n\ndef helper do\nend\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
