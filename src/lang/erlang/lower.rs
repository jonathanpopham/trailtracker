//! Lower the Erlang CST into the canonical graph.
//!
//! Same conservative principles as the Rust/Elixir lowerings, adapted to Erlang's
//! surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to a
//!    concrete project definition only when a scope level yields exactly one
//!    candidate; several candidates are emitted as an ambiguous edge carrying the
//!    full `candidates` set; none resolves to an explicit `UnresolvedSymbol` node.
//! 2. **Everything comes from real tokens.** Calls, record uses, attribute targets,
//!    and function names/arities are read off the lossless tree, never guessed.
//!
//! Resolution uses a deterministic **scope ladder** keyed on Erlang's name/arity
//! dispatch (most specific first; the first level with a candidate decides):
//!   - a remote call `mod:f(...)` resolves against `mod`'s functions when `mod` is
//!     a project module, else it is external;
//!   - a local call `f(...)` resolves against the current module exactly by
//!     name/arity, then by name, then globally by name; otherwise external (the
//!     common case for auto-imported BIFs like `length/1`).
//!
//! Honest mappings (see the IR Atlas):
//!   - `name(Args) -> Body` (one or more clauses) → `Function` (one node per
//!     name/arity, all clauses grouped);
//!   - `-module(M)` → `Module` (the namespace that `CONTAINS` the file);
//!   - `-record(R, {...})` → `Type` (`type_kind: record`); `-type`/`-opaque` →
//!     `Type` (`type_kind: type`/`opaque`);
//!   - `-define(NAME, ...)` → `Constant`;
//!   - `-import(Mod, [...])`, `-include`/`-include_lib`, `-behaviour` → `IMPORTS`
//!     (plus `ExternalDependency`/`DEPENDS_ON` when not project-local);
//!   - `-export([f/A, ...])` → the listed functions are tagged `exported: true`
//!     (an export declares which *local* functions are public; there is no module
//!     target for an `IMPORTS` edge, so a property is the honest mapping rather
//!     than a fabricated edge).
//!
//! No home in the current IR: `-spec`/`-callback` type signatures (kept losslessly
//! in the CST as `Attribute` nodes, but not lowered — there is no signature kind);
//! record *fields* (folded into the record `Type`, not separate nodes); macro
//! *invocations* `?NAME(...)` (a `?NAME` is preprocessor substitution, not a
//! function application, so it is not emitted as a `CALLS`). See `docs/ir-atlas.md`
//! candidate extensions.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::erlang::lexer::{is_keyword, kind as tk};
use crate::lang::erlang::parser::node as cst;
use crate::lang::frontend::SourceFile;

/// Lower a whole project's worth of Erlang files into a graph. `manifest_deps` is
/// unused (the pipeline's manifest reader is Cargo-only); dependencies are
/// discovered from `-import`/`-include`/`-behaviour` instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    // Project-local module names: every `-module(M)` declared in the batch (or the
    // file stem as a fallback). A remote call or import whose module is one of
    // these is intra-project, not an external dependency.
    let mut local_modules: BTreeSet<String> = BTreeSet::new();
    for f in files {
        local_modules.insert(module_name_of(f));
    }

    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        local_modules,
        fn_by_name: BTreeMap::new(),
        fn_by_module: BTreeMap::new(),
        fn_by_arity: BTreeMap::new(),
        type_by_name: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("erlang"))],
    );

    // Pass B: definition nodes + structural edges + symbol tables.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    for f in files.iter() {
        let module = module_name_of(f);
        let li = LineIndex::new(f.source);

        // The module is the primary Erlang namespace; it contains the file.
        let mod_id = format!("mod::{module}");
        lo.g.upsert_node(
            mod_id.clone(),
            ont::MODULE,
            module.clone(),
            vec![("language", Json::str("erlang"))],
        );
        lo.g.add_edge(lo.pkg_id(), edge::CONTAINS, mod_id.clone(), vec![]);

        let file_id = format!("file::{}", f.rel_path);
        lo.g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("erlang")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(mod_id, edge::CONTAINS, file_id.clone(), vec![]);

        // Exports must be known before functions are created so the `exported`
        // property is set first-seen (the graph keeps first-seen prop values).
        let exports = collect_exports(f.root, f.source);

        for form in f.root.child_nodes() {
            match form.kind {
                cst::FUNCTION => lo.handle_function(
                    form,
                    &file_id,
                    &module,
                    &exports,
                    f.source,
                    &li,
                    &mut pend_fns,
                ),
                cst::ATTRIBUTE => lo.handle_attribute(form, &file_id, &module, f.source, &li),
                _ => {}
            }
        }
    }

    // Pass C: resolve calls + record/type usages against the complete tables.
    for pf in &pend_fns {
        let ctx = Ctx {
            module: pf.module.clone(),
        };
        let mut calls = Vec::new();
        for &body in &pf.bodies {
            scan_calls(body, pf.source, &mut calls);
        }
        for call in &calls {
            let res = lo.resolve(call, &ctx);
            lo.emit_call(&pf.id, call, res);
        }
        lo.emit_type_uses(&pf.id, pf.node, pf.source);
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    local_modules: BTreeSet<String>,
    /// Simple name → all function node ids (global level).
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// (module, name) → function ids (module level, any arity).
    fn_by_module: BTreeMap<(String, String), Vec<String>>,
    /// (module, name, arity) → function ids (exact Erlang dispatch level).
    fn_by_arity: BTreeMap<(String, String, usize), Vec<String>>,
    /// Simple name → record/type node ids.
    type_by_name: BTreeMap<String, Vec<String>>,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    /// The whole `Function` node (used for record/type usage scanning).
    node: &'a Node,
    /// Each clause's `Body` node (used for call scanning; clause heads excluded).
    bodies: Vec<&'a Node>,
    module: String,
}

/// A detected call site over the lossless tree.
struct Call {
    name: String,
    arity: usize,
    remote: bool,
    /// The module/receiver for a remote call (`Some` only when it is a bare atom).
    receiver: Option<String>,
}

struct Ctx {
    module: String,
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

    #[allow(clippy::too_many_arguments)]
    fn handle_function<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        module: &str,
        exports: &BTreeSet<(String, usize)>,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
    ) {
        let clauses: Vec<&Node> = item.children_of(cst::CLAUSE).collect();
        let first = match clauses.first() {
            Some(c) => *c,
            None => return,
        };
        let name = clause_name(first, src).unwrap_or_else(|| "<anonymous>".to_string());
        let arity = clause_arity(first, src);
        let line = li.line_col(name_span_start(first)).line;
        let qual = format!("{module}:{name}/{arity}");
        let id = format!("fn::{qual}");
        let exported = exports.contains(&(name.clone(), arity));
        self.g.upsert_node(
            id.clone(),
            ont::FUNCTION,
            name.clone(),
            vec![
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("erlang")),
                ("arity", Json::U64(arity as u64)),
                ("clauses", Json::U64(clauses.len() as u64)),
                ("exported", Json::Bool(exported)),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
                (
                    "has_body",
                    Json::Bool(clauses.iter().any(|c| c.child(cst::BODY).is_some())),
                ),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);

        self.fn_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());
        self.fn_by_module
            .entry((module.to_string(), name.clone()))
            .or_default()
            .push(id.clone());
        self.fn_by_arity
            .entry((module.to_string(), name.clone(), arity))
            .or_default()
            .push(id.clone());

        let bodies: Vec<&Node> = clauses.iter().filter_map(|c| c.child(cst::BODY)).collect();
        pend_fns.push(PendingFn {
            id,
            source: src,
            node: item,
            bodies,
            module: module.to_string(),
        });
    }

    fn handle_attribute(
        &mut self,
        item: &Node,
        file_id: &str,
        module: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let attr = match attr_name(item, src) {
            Some(a) => a,
            None => return,
        };
        let args = item.child(cst::ARGS);
        match attr.as_str() {
            // Already consumed for module identity; nothing more to emit.
            "module" | "export" => {}
            "import" => {
                if let Some(m) = args.and_then(|a| first_atom_in_paren(a, src)) {
                    self.emit_import(file_id, &m, &m, "import");
                }
            }
            "include" | "include_lib" => {
                if let Some(path) = args.and_then(|a| first_string_in_paren(a, src)) {
                    self.emit_include(file_id, &path, &attr);
                }
            }
            "behaviour" | "behavior" => {
                if let Some(b) = args.and_then(|a| first_atom_in_paren(a, src)) {
                    self.emit_import(file_id, &b, &b, "behaviour");
                }
            }
            "record" => {
                if let Some(name) = args.and_then(|a| first_atom_in_paren(a, src)) {
                    self.emit_type(item, file_id, module, &name, "record", li);
                }
            }
            "type" | "opaque" => {
                if let Some(name) = args.and_then(|a| first_atom_token(a, src)) {
                    self.emit_type(item, file_id, module, &name, &attr, li);
                }
            }
            "define" => {
                if let Some(name) = args.and_then(|a| first_macro_name(a, src)) {
                    let qual = format!("{module}:{name}");
                    let id = format!("const::{qual}");
                    let line = li.line_col(item.span.start).line;
                    self.g.upsert_node(
                        id.clone(),
                        ont::CONSTANT,
                        name,
                        vec![
                            ("binding", Json::str("macro")),
                            ("language", Json::str("erlang")),
                            ("qualified_name", Json::str(qual)),
                            ("line", Json::U64(line as u64)),
                        ],
                    );
                    self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
                }
            }
            // `-spec`, `-callback`, `-compile`, `-vsn`, `-ifdef`, … : no graph node
            // (kept losslessly in the CST). See module docs.
            _ => {}
        }
    }

    fn emit_type(
        &mut self,
        item: &Node,
        file_id: &str,
        module: &str,
        name: &str,
        type_kind: &str,
        li: &LineIndex,
    ) {
        let qual = format!("{module}:{name}");
        let id = format!("type::{qual}");
        let line = li.line_col(item.span.start).line;
        // `type_kind` is borrowed; store it as an owned Json string.
        let kind_owned = type_kind.to_string();
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.to_string(),
            vec![
                ("type_kind", Json::Str(kind_owned)),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("erlang")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name
            .entry(name.to_string())
            .or_default()
            .push(id);
    }

    /// `-import(Mod, …)` / `-behaviour(Mod)`: a dependency on another module.
    fn emit_import(&mut self, file_id: &str, full: &str, root: &str, keyword: &str) {
        if full.is_empty() {
            return;
        }
        if self.local_modules.contains(root) {
            let mod_id = format!("mod::{full}");
            self.g.upsert_node(
                mod_id.clone(),
                ont::MODULE,
                full.to_string(),
                vec![("language", Json::str("erlang"))],
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
            let dep_id = ext_id(root);
            self.g.upsert_node(
                dep_id.clone(),
                ont::EXTERNAL_DEPENDENCY,
                root.to_string(),
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

    /// `-include("x.hrl")` / `-include_lib(...)`: a dependency on a header file.
    fn emit_include(&mut self, file_id: &str, path: &str, keyword: &str) {
        if path.is_empty() {
            return;
        }
        let dep_id = ext_id(path);
        self.g.upsert_node(
            dep_id.clone(),
            ont::EXTERNAL_DEPENDENCY,
            path.to_string(),
            vec![
                ("external", Json::Bool(true)),
                ("source", Json::str(keyword.to_string())),
                ("role", Json::str("include")),
            ],
        );
        self.g.add_edge(
            file_id,
            edge::IMPORTS,
            dep_id.clone(),
            vec![
                ("path", Json::str(path.to_string())),
                ("external", Json::Bool(true)),
                ("kind", Json::str(keyword.to_string())),
            ],
        );
        self.g
            .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
    }

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        if call.remote {
            if let Some(recv) = &call.receiver {
                if self.local_modules.contains(recv) {
                    let exact = self.fns_by_arity(recv, &call.name, call.arity);
                    if !exact.is_empty() {
                        return mk(exact, "remote");
                    }
                    let m = self.fns_in_module(recv, &call.name);
                    if !m.is_empty() {
                        return mk(m, "remote_name");
                    }
                }
            }
            return Resolution {
                outcome: Outcome::None,
                level: "external",
            };
        }
        // Local call: exact name/arity in this module, then name, then global.
        let exact = self.fns_by_arity(&ctx.module, &call.name, call.arity);
        if !exact.is_empty() {
            return mk(exact, "local");
        }
        let m = self.fns_in_module(&ctx.module, &call.name);
        if !m.is_empty() {
            return mk(m, "local_name");
        }
        let g = self.global_fns(&call.name);
        if g.is_empty() {
            Resolution {
                outcome: Outcome::None,
                level: "external",
            }
        } else {
            mk(g, "global")
        }
    }

    fn emit_call(&mut self, caller_id: &str, call: &Call, res: Resolution) {
        let mut props = vec![
            ("callee", Json::str(call.name.clone())),
            ("arity", Json::U64(call.arity as u64)),
            ("remote", Json::Bool(call.remote)),
            ("resolution", Json::str(res.level)),
        ];
        if let Some(recv) = &call.receiver {
            props.push(("module", Json::str(recv.clone())));
        }
        match res.outcome {
            Outcome::One(id) => {
                props.push(("resolved", Json::Bool(true)));
                props.push(("candidate_count", Json::U64(1)));
                self.g.add_edge(caller_id, edge::CALLS, id, props);
            }
            Outcome::Many(ids) => {
                let target = unresolved_id(&call.name);
                self.ensure_unresolved(&target, &call.name);
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
                self.ensure_unresolved(&target, &call.name);
                props.push(("resolved", Json::Bool(false)));
                props.push(("candidate_count", Json::U64(0)));
                self.g.add_edge(caller_id, edge::CALLS, target, props);
            }
        }
    }

    fn ensure_unresolved(&mut self, id: &str, name: &str) {
        if !self.g.has_node(id) {
            self.g.upsert_node(
                id.to_string(),
                ont::UNRESOLVED,
                name.to_string(),
                vec![
                    ("unresolved", Json::Bool(true)),
                    ("role", Json::str("call")),
                ],
            );
        }
    }

    fn fns_by_arity(&self, module: &str, name: &str, arity: usize) -> Vec<String> {
        self.fn_by_arity
            .get(&(module.to_string(), name.to_string(), arity))
            .cloned()
            .unwrap_or_default()
    }

    fn fns_in_module(&self, module: &str, name: &str) -> Vec<String> {
        self.fn_by_module
            .get(&(module.to_string(), name.to_string()))
            .cloned()
            .unwrap_or_default()
    }

    fn global_fns(&self, name: &str) -> Vec<String> {
        self.fn_by_name.get(name).cloned().unwrap_or_default()
    }

    fn unique_type(&self, name: &str) -> Option<String> {
        match self.type_by_name.get(name) {
            Some(ids) if ids.len() == 1 => Some(ids[0].clone()),
            _ => None,
        }
    }

    /// Add `USES_TYPE` edges for `#record` references in a function that name a
    /// unique project record/type.
    fn emit_type_uses(&mut self, from_id: &str, func: &Node, src: &str) {
        let mut refs: Vec<String> = Vec::new();
        scan_record_refs(func, src, &mut refs);
        let mut seen: Vec<String> = Vec::new();
        for name in refs {
            if let Some(type_id) = self.unique_type(&name) {
                if type_id != from_id && !seen.contains(&type_id) {
                    seen.push(type_id.clone());
                    self.g.add_edge(
                        from_id,
                        edge::USES_TYPE,
                        type_id,
                        vec![("type_name", Json::str(name))],
                    );
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

/// The module name: the `-module(M)` atom, or the file stem as a fallback.
fn module_name_of(f: &SourceFile<'_>) -> String {
    for form in f.root.child_nodes() {
        if form.kind == cst::ATTRIBUTE && attr_name(form, f.source).as_deref() == Some("module") {
            if let Some(args) = form.child(cst::ARGS) {
                if let Some(m) = first_atom_in_paren(args, f.source) {
                    return m;
                }
            }
        }
    }
    let base = file_name(&f.rel_path);
    base.rsplit_once('.')
        .map(|(stem, _)| stem.to_string())
        .unwrap_or(base)
}

/// The attribute keyword: the text of the attribute's `Name` atom.
fn attr_name(item: &Node, src: &str) -> Option<String> {
    let nm = item.child(cst::NAME)?;
    nm.tokens().next().map(|t| atom_text(t.span.text(src)))
}

/// A bare atom's text, with surrounding single quotes stripped (`'end'` → `end`).
fn atom_text(raw: &str) -> String {
    if raw.len() >= 2 && raw.starts_with('\'') && raw.ends_with('\'') {
        raw[1..raw.len() - 1].to_string()
    } else {
        raw.to_string()
    }
}

/// The clause's function name — the first token of its `Name` node.
fn clause_name(clause: &Node, src: &str) -> Option<String> {
    let nm = clause.child(cst::NAME)?;
    nm.tokens().next().map(|t| atom_text(t.span.text(src)))
}

fn name_span_start(clause: &Node) -> u32 {
    clause
        .child(cst::NAME)
        .map(|n| n.span.start)
        .unwrap_or(clause.span.start)
}

/// The clause's arity — the number of top-level arguments in its `Params` paren.
fn clause_arity(clause: &Node, src: &str) -> usize {
    match clause.child(cst::PARAMS) {
        Some(p) => paren_arity(p, src),
        None => 0,
    }
}

/// Count top-level arguments in a delimiter group (`,`-separated at the group's
/// own level). `()` is 0; one non-empty argument is 1.
fn paren_arity(g: &Node, src: &str) -> usize {
    let mut commas = 0usize;
    let mut any = false;
    for c in &g.children {
        match c {
            Child::Node(_) => any = true,
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => {
                let txt = t.span.text(src);
                if matches!(txt, "(" | ")" | "[" | "]" | "{" | "}") {
                    continue;
                }
                any = true;
                if txt == "," {
                    commas += 1;
                }
            }
        }
    }
    if any {
        commas + 1
    } else {
        0
    }
}

/// The first `Paren` group directly under a node (an attribute's `Args`).
fn args_paren(args: &Node) -> Option<&Node> {
    args.child_nodes().find(|n| n.kind == cst::PAREN)
}

/// The first atom token inside an attribute's parenthesized args
/// (`-module(foo)` → `foo`, `-import(lists, …)` → `lists`).
fn first_atom_in_paren(args: &Node, src: &str) -> Option<String> {
    let paren = args_paren(args)?;
    paren
        .tokens()
        .find(|t| t.kind == tk::ATOM)
        .map(|t| atom_text(t.span.text(src)))
}

/// The first atom token directly in an args region (`-type foo() :: …` → `foo`).
fn first_atom_token(args: &Node, src: &str) -> Option<String> {
    args.tokens()
        .find(|t| t.kind == tk::ATOM)
        .map(|t| atom_text(t.span.text(src)))
}

/// The macro name in `-define(NAME, …)` — the first significant token inside the
/// args paren (an atom or an UPPERCASE variable; a `?`-prefixed macro is rare).
fn first_macro_name(args: &Node, src: &str) -> Option<String> {
    let paren = args_paren(args)?;
    for t in paren.tokens() {
        let txt = t.span.text(src);
        match t.kind {
            tk::ATOM => return Some(atom_text(txt)),
            tk::VAR => return Some(txt.to_string()),
            tk::MACRO => return Some(txt.trim_start_matches('?').to_string()),
            _ => {}
        }
    }
    None
}

/// The first string literal inside an args paren, with quotes stripped
/// (`-include("foo.hrl")` → `foo.hrl`).
fn first_string_in_paren(args: &Node, src: &str) -> Option<String> {
    let paren = args_paren(args)?;
    let t = paren.tokens().find(|t| t.kind == tk::STRING)?;
    let raw = t.span.text(src);
    if raw.len() >= 2 && raw.starts_with('"') && raw.ends_with('"') {
        Some(raw[1..raw.len() - 1].to_string())
    } else {
        Some(raw.to_string())
    }
}

/// Collect the `(name, arity)` pairs exported by every `-export([f/1, …])` form.
fn collect_exports(root: &Node, src: &str) -> BTreeSet<(String, usize)> {
    let mut out = BTreeSet::new();
    for form in root.child_nodes() {
        if form.kind != cst::ATTRIBUTE || attr_name(form, src).as_deref() != Some("export") {
            continue;
        }
        if let Some(args) = form.child(cst::ARGS) {
            if let Some(paren) = args_paren(args) {
                collect_fa_pairs(paren, src, &mut out);
            }
        }
    }
    out
}

/// Scan a node's tokens (recursing into child groups) for `atom / int` arity
/// pairs (`fac/1`), used for export lists.
fn collect_fa_pairs(node: &Node, src: &str, out: &mut BTreeSet<(String, usize)>) {
    let toks: Vec<(&'static str, &str)> = flat_tokens(node, src);
    let mut i = 0;
    while i + 2 < toks.len() {
        if toks[i].0 == tk::ATOM && toks[i + 1].1 == "/" && toks[i + 2].0 == tk::INT {
            if let Ok(arity) = toks[i + 2].1.parse::<usize>() {
                out.insert((atom_text(toks[i].1), arity));
            }
            i += 3;
            continue;
        }
        i += 1;
    }
}

/// All non-trivia tokens in a subtree, in source order (kind, text).
fn flat_tokens<'a>(node: &'a Node, src: &'a str) -> Vec<(&'static str, &'a str)> {
    let mut out = Vec::new();
    for n in node.walk() {
        for c in &n.children {
            if let Child::Token(t) = c {
                if !t.trivia {
                    out.push((t.kind, t.span.text(src)));
                }
            }
        }
    }
    out
}

// --- call detection over the lossless token tree ----------------------------

enum El<'a> {
    Tok { text: &'a str, kind: &'static str },
    Grp(&'a Node),
}

fn el_text<'a>(e: &El<'a>) -> Option<&'a str> {
    match e {
        El::Tok { text, .. } => Some(text),
        El::Grp(_) => None,
    }
}

fn el_is(e: &El, k: &str) -> bool {
    matches!(e, El::Tok { kind, .. } if *kind == k)
}

/// A token usable as a call name / module: an atom, a variable (dynamic), or a
/// macro that expands to one.
fn el_is_name(e: &El) -> bool {
    matches!(e, El::Tok { kind, .. } if *kind == tk::ATOM || *kind == tk::VAR || *kind == tk::MACRO)
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
                kind: t.kind,
            }),
            Child::Node(n) => v.push(El::Grp(n)),
        }
    }
    v
}

/// Detect `name(...)` local calls and `mod:name(...)` remote calls over the real
/// token tree, recursing into nested groups. Reserved words, `fun f/A` references,
/// and record selectors are excluded; arity is read from the argument group.
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        // Remote call: name `:` name `(...)`.
        if el_is_name(&els[i])
            && i + 3 < n
            && el_is(&els[i + 1], tk::PUNCT)
            && el_text(&els[i + 1]) == Some(":")
            && el_is_name(&els[i + 2])
        {
            if let Some(g) = grp(&els[i + 3]) {
                if g.kind == cst::PAREN {
                    let module_tok = &els[i];
                    let receiver = match module_tok {
                        El::Tok { text, kind } if *kind == tk::ATOM => Some(atom_text(text)),
                        _ => None, // variable / macro module → dynamic, external
                    };
                    let name = el_text(&els[i + 2]).unwrap_or("");
                    if !is_keyword(name) {
                        out.push(Call {
                            name: atom_text(name),
                            arity: paren_arity(g, src),
                            remote: true,
                            receiver,
                        });
                    }
                    i += 4;
                    continue;
                }
            }
        }
        // Local call: atom `(...)`, not preceded by `:`/`#`/`fun`, not a keyword.
        if el_is(&els[i], tk::ATOM) && i + 1 < n {
            if let Some(g) = grp(&els[i + 1]) {
                if g.kind == cst::PAREN {
                    let text = el_text(&els[i]).unwrap_or("");
                    let prev = if i > 0 { el_text(&els[i - 1]) } else { None };
                    if !is_keyword(text)
                        && prev != Some(":")
                        && prev != Some("#")
                        && prev != Some("fun")
                    {
                        out.push(Call {
                            name: atom_text(text),
                            arity: paren_arity(g, src),
                            remote: false,
                            receiver: None,
                        });
                    }
                }
            }
        }
        i += 1;
    }
    // Recurse into nested groups (argument lists, comprehensions, fun bodies).
    for e in &els {
        if let Some(g) = grp(e) {
            scan_calls(g, src, out);
        }
    }
}

/// Collect record names referenced as `#name` anywhere in a subtree.
fn scan_record_refs(node: &Node, src: &str, out: &mut Vec<String>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        if el_text(&els[i]) == Some("#") && i + 1 < n && el_is(&els[i + 1], tk::ATOM) {
            out.push(atom_text(el_text(&els[i + 1]).unwrap_or("")));
        }
        i += 1;
    }
    for e in &els {
        if let Some(g) = grp(e) {
            scan_record_refs(g, src, out);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::erlang::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("app.erl", src);
        let file = SourceFile {
            rel_path: "app.erl".to_string(),
            module_path: vec![],
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
        let src = "\
-module(calc).
-export([area/1, total/1]).
-import(lists, [sum/1]).
-record(circle, {r = 0}).
-define(PI, 3.14159).

area(#circle{r = R}) -> ?PI * R * R.

total(List) ->
    Doubled = lists:map(fun(X) -> double(X) end, List),
    sum(Doubled).

double(X) -> X * 2.
";
        let tree = parse("calc.erl", src);
        assert!(tree.is_lossless(), "parse must round-trip before lowering");
        let file = SourceFile {
            rel_path: "src/calc.erl".to_string(),
            module_path: vec![],
            source: &tree.source,
            root: &tree.root,
        };
        let g = lower("calc", std::slice::from_ref(&file), &[]);
        assert!(g.count_nodes_of(ont::FUNCTION) >= 3, "area, total, double");
        assert!(g.count_nodes_of(ont::TYPE) >= 1, "circle record");
        assert!(g.count_nodes_of(ont::CONSTANT) >= 1, "PI macro");
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "calc module");
    }

    #[test]
    fn module_contains_file_and_declares_functions() {
        let g = graph_for("-module(m).\nf() -> ok.\n");
        assert!(g.has_node("mod::m"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::CONTAINS && e.from == "mod::m"));
        assert!(g.has_node("fn::m:f/0"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DECLARES && e.to == "fn::m:f/0"));
    }

    #[test]
    fn multi_clause_is_one_function_node() {
        let g = graph_for("-module(m).\nfac(0) -> 1;\nfac(N) -> N * fac(N - 1).\n");
        assert_eq!(g.count_nodes_of(ont::FUNCTION), 1, "one fac/1");
        let f = g.nodes().find(|n| n.kind == ont::FUNCTION).unwrap();
        assert_eq!(f.props.get("arity"), Some(&Json::U64(1)));
        assert_eq!(f.props.get("clauses"), Some(&Json::U64(2)));
    }

    #[test]
    fn resolves_local_call_by_arity() {
        let g = graph_for("-module(m).\nrun() -> add(1, 2).\nadd(A, B) -> A + B.\n");
        let calls = call_edges(&g);
        let add = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("add")))
            .expect("a call to add");
        assert_eq!(add.to, "fn::m:add/2");
        assert_eq!(add.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(add.props.get("resolution"), Some(&Json::str("local")));
        assert_eq!(add.props.get("arity"), Some(&Json::U64(2)));
    }

    #[test]
    fn remote_call_to_known_module_resolves() {
        let src = "-module(a).\nrun() -> b:work(1).\n";
        let tree_a = parse("a.erl", src);
        let src_b = "-module(b).\nwork(X) -> X.\n";
        let tree_b = parse("b.erl", src_b);
        let fa = SourceFile {
            rel_path: "a.erl".to_string(),
            module_path: vec![],
            source: &tree_a.source,
            root: &tree_a.root,
        };
        let fb = SourceFile {
            rel_path: "b.erl".to_string(),
            module_path: vec![],
            source: &tree_b.source,
            root: &tree_b.root,
        };
        let g = lower("proj", &[fa, fb], &[]);
        let calls = call_edges(&g);
        let w = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("work")))
            .expect("a call to work");
        assert_eq!(w.to, "fn::b:work/1");
        assert_eq!(w.props.get("resolution"), Some(&Json::str("remote")));
        assert_eq!(w.props.get("remote"), Some(&Json::Bool(true)));
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for("-module(m).\nrun() -> mystery(42).\n");
        let calls = call_edges(&g);
        let myst = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("mystery")))
            .expect("a call to mystery");
        assert_eq!(myst.props.get("resolution"), Some(&Json::str("external")));
        assert!(g.has_node("unresolved::mystery"));
    }

    #[test]
    fn bif_style_remote_is_external() {
        let g = graph_for("-module(m).\nrun() -> lists:map(fun(X) -> X end, []).\n");
        let calls = call_edges(&g);
        let m = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("map")))
            .expect("a call to lists:map");
        assert_eq!(m.props.get("resolution"), Some(&Json::str("external")));
        assert!(g.has_node("ext::lists") || g.has_node("unresolved::map"));
    }

    #[test]
    fn import_and_include_create_dependencies() {
        let g = graph_for(
            "-module(m).\n-import(lists, [map/2]).\n-include(\"defs.hrl\").\nf() -> ok.\n",
        );
        assert!(g.has_node("ext::lists"));
        assert!(g.has_node("ext::defs.hrl"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::lists"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::IMPORTS && e.to == "ext::defs.hrl"));
    }

    #[test]
    fn record_and_type_are_types() {
        let g = graph_for(
            "-module(m).\n-record(point, {x, y}).\n-type id() :: integer().\nf() -> ok.\n",
        );
        let kinds: Vec<&Json> = g
            .nodes()
            .filter(|n| n.kind == ont::TYPE)
            .filter_map(|n| n.props.get("type_kind"))
            .collect();
        assert!(kinds.contains(&&Json::str("record")));
        assert!(kinds.contains(&&Json::str("type")));
    }

    #[test]
    fn define_is_constant() {
        let g = graph_for("-module(m).\n-define(PI, 3.14).\n-define(MAX(X), X + 1).\nf() -> ok.\n");
        assert!(g.count_nodes_of(ont::CONSTANT) >= 2);
        assert!(g.nodes().any(|n| n.kind == ont::CONSTANT && n.name == "PI"));
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::CONSTANT && n.name == "MAX"));
    }

    #[test]
    fn export_tags_functions() {
        let g = graph_for("-module(m).\n-export([pub/0]).\npub() -> ok.\npriv() -> ok.\n");
        let pub_fn = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "pub")
            .unwrap();
        assert_eq!(pub_fn.props.get("exported"), Some(&Json::Bool(true)));
        let priv_fn = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "priv")
            .unwrap();
        assert_eq!(priv_fn.props.get("exported"), Some(&Json::Bool(false)));
    }

    #[test]
    fn record_use_creates_uses_type() {
        let g = graph_for("-module(m).\n-record(point, {x, y}).\nf(P) -> P#point.x.\n");
        assert!(
            g.edges()
                .any(|e| e.kind == edge::USES_TYPE && e.to.contains("point")),
            "P#point.x should create USES_TYPE"
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src = "-module(m).\n-import(lists, [map/2]).\nf() -> g().\ng() -> ok.\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
