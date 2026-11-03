//! Lower the Prolog CST into the canonical graph.
//!
//! Same conservative principles as the Rust/Elixir/Erlang lowerings, adapted to
//! Prolog's surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to a
//!    concrete project definition only when a scope level yields exactly one
//!    candidate; several candidates are emitted as an ambiguous edge carrying the
//!    full `candidates` set; none resolves to an explicit `UnresolvedSymbol` node.
//! 2. **Everything comes from real tokens.** Calls, imports, exports, and predicate
//!    names/arities are read off the lossless tree, never guessed.
//!
//! Resolution uses a deterministic **scope ladder** keyed on Prolog's name/arity
//! dispatch (most specific first; the first level with a candidate decides):
//!   - a module-qualified goal `mod:p(...)` resolves against `mod`'s predicates
//!     when `mod` is a project module, else it is external;
//!   - a plain goal `p(...)` resolves against the current module exactly by
//!     name/arity, then by name, then globally by name; otherwise external (the
//!     common case for built-ins like `format/2`, `member/2`).
//!
//! Honest mappings (see the IR Atlas):
//!   - a predicate — the group of clauses (`head.` facts and `head :- body.` /
//!     `head --> body.` rules) sharing one name/arity → one `Function` node (all
//!     clauses grouped, like Erlang). DCG rules are tagged `dcg: true`;
//!   - `:- module(Name, Exports)` → `Module` (the namespace that `CONTAINS` the
//!     file); the `Exports` pairs tag their predicates `exported: true`;
//!   - `:- use_module(M)` / `:- use_module(library(L))` / `:- ensure_loaded(F)` /
//!     `:- consult(F)` / `:- reexport(M)` / `:- include(F)` → `IMPORTS`
//!     (plus `ExternalDependency` / `DEPENDS_ON` when not project-local).
//!
//! Honest punts — kept losslessly in the CST, but with no home in the current IR:
//!   - **0-arity goal calls** (`p :- q, r.` calling `q/0`, `r/0`) and goals built
//!     in operator notation are *not* emitted as `CALLS` — only `p(Args)` /
//!     `mod:p(Args)` call shapes are detected, mirroring Erlang. This trades recall
//!     for zero fabrication.
//!   - **meta-call / data ambiguity**: a `p(Args)` term appearing inside another
//!     term's arguments (e.g. `assertz(foo(1))`, `findall(X, goal(X), L)`) is
//!     scanned like a call. Prolog cannot distinguish a called goal from a quoted
//!     data term without mode information, so this over-approximates; such edges
//!     resolve `external` when the name is unknown, never to a fabricated target.
//!   - **DCG hidden arguments**: a DCG nonterminal's real arity is its written
//!     arity + 2 (the difference-list pair). We record the *written* arity and the
//!     `dcg` tag rather than fabricate the hidden pair, so DCG call resolution is
//!     by written arity (and may under-resolve).
//!   - `:- dynamic/discontiguous/multifile`, `:- op`, `:- set_prolog_flag`,
//!     `:- initialization`, and goals inside directive bodies: no graph node.
//!   - Prolog has no type or constant declaration surface, so no `Type`/`Constant`
//!     / `USES_TYPE` is emitted. See `docs/ir-atlas.md` candidate extensions.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::prolog::lexer::kind as tk;
use crate::lang::prolog::parser::node as cst;

/// Lower a whole project's worth of Prolog files into a graph. `manifest_deps` is
/// unused (the pipeline's manifest reader is Cargo-only); dependencies are
/// discovered from `:- use_module`/`:- ensure_loaded`/… instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    // Project-local module names: every `:- module(M, …)` declared in the batch (or
    // the file stem as a fallback). A qualified call or import whose module is one
    // of these is intra-project, not an external dependency.
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
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("prolog"))],
    );

    // Pass B: structural nodes + collect predicate clauses + handle directives.
    let mut clauses: Vec<PendingClause<'_>> = Vec::new();
    for f in files.iter() {
        let module = module_name_of(f);
        let li = LineIndex::new(f.source);

        // The module is the primary Prolog namespace; it contains the file.
        let mod_id = format!("mod::{module}");
        lo.g.upsert_node(
            mod_id.clone(),
            ont::MODULE,
            module.clone(),
            vec![("language", Json::str("prolog"))],
        );
        lo.g.add_edge(lo.pkg_id(), edge::CONTAINS, mod_id.clone(), vec![]);

        let file_id = format!("file::{}", f.rel_path);
        lo.g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("prolog")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(mod_id, edge::CONTAINS, file_id.clone(), vec![]);

        let exports = collect_exports(f.root, f.source);

        for form in f.root.child_nodes() {
            match form.kind {
                cst::DIRECTIVE => lo.handle_directive(form, &file_id, f.source),
                cst::CLAUSE => {
                    if let Some(pc) =
                        pending_clause(form, &file_id, &module, &exports, f.source, &li)
                    {
                        clauses.push(pc);
                    }
                }
                _ => {}
            }
        }
    }

    // Aggregate clauses sharing a predicate (module, name, arity) into one
    // Function, then build the symbol tables the resolver reads.
    let mut aggs: BTreeMap<(String, String, usize), Agg<'_>> = BTreeMap::new();
    for pc in &clauses {
        let key = (pc.module.clone(), pc.name.clone(), pc.arity);
        let entry = aggs.entry(key).or_insert_with(|| Agg {
            file_id: pc.file_id.clone(),
            line: pc.line,
            span_start: pc.span_start,
            span_end: pc.span_end,
            clause_count: 0,
            is_dcg: false,
            exported: false,
            bodies: Vec::new(),
        });
        entry.clause_count += 1;
        entry.is_dcg |= pc.is_dcg;
        entry.exported |= pc.exported;
        entry.span_end = entry.span_end.max(pc.span_end);
        if let Some(body) = pc.body {
            // Pair each body with its own file's source: a predicate's clauses may
            // (via discontiguous) span files with different `&str` buffers, and a
            // body's spans index into its own buffer.
            entry.bodies.push((body, pc.source));
        }
    }

    for ((module, name, arity), agg) in &aggs {
        lo.emit_function(module, name, *arity, agg);
    }

    // Pass C: resolve calls against the complete tables.
    for ((module, name, arity), agg) in &aggs {
        let id = fn_id(module, name, *arity);
        let ctx = Ctx {
            module: module.clone(),
        };
        let mut calls = Vec::new();
        for &(body, bsrc) in &agg.bodies {
            scan_calls(body, bsrc, &mut calls);
        }
        for call in &calls {
            let res = lo.resolve(call, &ctx);
            lo.emit_call(&id, call, res);
        }
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
    /// (module, name, arity) → function ids (exact Prolog dispatch level).
    fn_by_arity: BTreeMap<(String, String, usize), Vec<String>>,
}

/// One detected clause, pre-aggregation.
struct PendingClause<'a> {
    name: String,
    arity: usize,
    module: String,
    file_id: String,
    is_dcg: bool,
    exported: bool,
    body: Option<&'a Node>,
    source: &'a str,
    line: u32,
    span_start: u32,
    span_end: u32,
}

/// Aggregated facts for one predicate (module, name, arity).
struct Agg<'a> {
    file_id: String,
    line: u32,
    span_start: u32,
    span_end: u32,
    clause_count: usize,
    is_dcg: bool,
    exported: bool,
    bodies: Vec<(&'a Node, &'a str)>,
}

/// A detected call site over the lossless tree.
struct Call {
    name: String,
    arity: usize,
    qualified: bool,
    /// The module/receiver for a qualified call (`Some` only when a bare atom).
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

    fn emit_function(&mut self, module: &str, name: &str, arity: usize, agg: &Agg<'_>) {
        let qual = format!("{module}:{name}/{arity}");
        let id = fn_id(module, name, arity);
        self.g.upsert_node(
            id.clone(),
            ont::FUNCTION,
            name.to_string(),
            vec![
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("prolog")),
                ("arity", Json::U64(arity as u64)),
                ("clauses", Json::U64(agg.clause_count as u64)),
                ("exported", Json::Bool(agg.exported)),
                ("dcg", Json::Bool(agg.is_dcg)),
                ("line", Json::U64(agg.line as u64)),
                ("span_start", Json::U64(agg.span_start as u64)),
                ("span_end", Json::U64(agg.span_end as u64)),
                ("has_body", Json::Bool(!agg.bodies.is_empty())),
            ],
        );
        self.g
            .add_edge(&agg.file_id, edge::DECLARES, id.clone(), vec![]);

        self.fn_by_name
            .entry(name.to_string())
            .or_default()
            .push(id.clone());
        self.fn_by_module
            .entry((module.to_string(), name.to_string()))
            .or_default()
            .push(id.clone());
        self.fn_by_arity
            .entry((module.to_string(), name.to_string(), arity))
            .or_default()
            .push(id);
    }

    /// Handle the import-bearing directives. Everything else (module/export/
    /// dynamic/op/…) is consumed elsewhere or intentionally punted (see module docs).
    fn handle_directive(&mut self, item: &Node, file_id: &str, src: &str) {
        let (name, paren) = match directive_goal(item, src) {
            Some(g) => g,
            None => return,
        };
        match name.as_str() {
            "use_module" | "ensure_loaded" | "consult" | "reexport" | "load_files" => {
                if let Some((target, is_library)) = paren.and_then(|p| dep_target(p, src)) {
                    self.emit_import(file_id, &target, is_library, &name);
                }
            }
            "include" => {
                if let Some((target, _)) = paren.and_then(|p| dep_target(p, src)) {
                    self.emit_include(file_id, &target, &name);
                }
            }
            // `module`/`export` (handled via exports), and `dynamic`/`discontiguous`/
            // `multifile`/`op`/`set_prolog_flag`/`initialization`/… : no graph node
            // (kept losslessly in the CST). See module docs.
            _ => {}
        }
    }

    /// `:- use_module(M)` etc.: a dependency on another module. A library import or
    /// a module not declared in the batch is external; a project-local module is an
    /// internal `IMPORTS` edge.
    fn emit_import(&mut self, file_id: &str, target: &str, is_library: bool, keyword: &str) {
        if target.is_empty() {
            return;
        }
        if !is_library && self.local_modules.contains(target) {
            let mod_id = format!("mod::{target}");
            self.g.upsert_node(
                mod_id.clone(),
                ont::MODULE,
                target.to_string(),
                vec![("language", Json::str("prolog"))],
            );
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                mod_id,
                vec![
                    ("path", Json::str(target.to_string())),
                    ("external", Json::Bool(false)),
                    ("kind", Json::str(keyword.to_string())),
                ],
            );
        } else {
            let dep_id = ext_id(target);
            let mut node_props = vec![
                ("external", Json::Bool(true)),
                ("source", Json::str(keyword.to_string())),
            ];
            if is_library {
                node_props.push(("role", Json::str("library")));
            }
            self.g.upsert_node(
                dep_id.clone(),
                ont::EXTERNAL_DEPENDENCY,
                target.to_string(),
                node_props,
            );
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                dep_id.clone(),
                vec![
                    ("path", Json::str(target.to_string())),
                    ("external", Json::Bool(true)),
                    ("kind", Json::str(keyword.to_string())),
                    ("library", Json::Bool(is_library)),
                ],
            );
            self.g
                .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
        }
    }

    /// `:- include("x.pl")` / `:- include(x)`: a dependency on an included file.
    fn emit_include(&mut self, file_id: &str, target: &str, keyword: &str) {
        if target.is_empty() {
            return;
        }
        let dep_id = ext_id(target);
        self.g.upsert_node(
            dep_id.clone(),
            ont::EXTERNAL_DEPENDENCY,
            target.to_string(),
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
                ("path", Json::str(target.to_string())),
                ("external", Json::Bool(true)),
                ("kind", Json::str(keyword.to_string())),
            ],
        );
        self.g
            .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
    }

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        if call.qualified {
            if let Some(recv) = &call.receiver {
                if self.local_modules.contains(recv) {
                    let exact = self.fns_by_arity(recv, &call.name, call.arity);
                    if !exact.is_empty() {
                        return mk(exact, "qualified");
                    }
                    let m = self.fns_in_module(recv, &call.name);
                    if !m.is_empty() {
                        return mk(m, "qualified_name");
                    }
                }
            }
            return Resolution {
                outcome: Outcome::None,
                level: "external",
            };
        }
        // Plain goal: exact name/arity in this module, then name, then global.
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
            ("qualified", Json::Bool(call.qualified)),
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

fn fn_id(module: &str, name: &str, arity: usize) -> String {
    format!("fn::{module}:{name}/{arity}")
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
    match file_name(rel).rsplit_once('.') {
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

/// A bare atom's text, with surrounding single quotes stripped (`'foo'` → `foo`).
fn atom_text(raw: &str) -> String {
    if raw.len() >= 2 && raw.starts_with('\'') && raw.ends_with('\'') {
        raw[1..raw.len() - 1].to_string()
    } else {
        raw.to_string()
    }
}

/// A string literal's text, with surrounding double quotes stripped.
fn string_text(raw: &str) -> String {
    if raw.len() >= 2 && raw.starts_with('"') && raw.ends_with('"') {
        raw[1..raw.len() - 1].to_string()
    } else {
        raw.to_string()
    }
}

/// Build a [`PendingClause`] from a `Clause` node, or `None` if it has no head.
fn pending_clause<'a>(
    item: &'a Node,
    file_id: &str,
    module: &str,
    exports: &BTreeSet<(String, usize)>,
    src: &'a str,
    li: &LineIndex,
) -> Option<PendingClause<'a>> {
    let name = clause_name(item, src)?;
    let arity = clause_arity(item, src);
    let line = li.line_col(name_span_start(item)).line;
    let exported = exports.contains(&(name.clone(), arity));
    Some(PendingClause {
        name,
        arity,
        module: module.to_string(),
        file_id: file_id.to_string(),
        is_dcg: clause_is_dcg(item, src),
        exported,
        body: item.child(cst::BODY),
        source: src,
        line,
        span_start: item.span.start,
        span_end: item.span.end,
    })
}

/// The module name: the `:- module(M, …)` atom, or the file stem as a fallback.
fn module_name_of(f: &SourceFile<'_>) -> String {
    for form in f.root.child_nodes() {
        if form.kind == cst::DIRECTIVE {
            if let Some((name, Some(paren))) = directive_goal(form, f.source) {
                if name == "module" {
                    if let Some(m) = first_atom_in(paren, f.source) {
                        return m;
                    }
                }
            }
        }
    }
    let base = file_name(&f.rel_path);
    base.rsplit_once('.')
        .map(|(stem, _)| stem.to_string())
        .unwrap_or(base)
}

/// The clause's predicate name — the first token of its `Name` node.
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

/// A clause is a DCG rule iff its neck operator is `-->` (a direct `-->` token).
fn clause_is_dcg(clause: &Node, src: &str) -> bool {
    clause.children.iter().any(|c| match c {
        Child::Token(t) if !t.trivia => t.span.text(src) == "-->",
        _ => false,
    })
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

/// The first `Paren` group directly under a node (a directive body's goal args).
fn args_paren(node: &Node) -> Option<&Node> {
    node.child_nodes().find(|n| n.kind == cst::PAREN)
}

/// A directive's goal: its predicate name (first atom in the `Body`) and its first
/// argument `Paren` group, if any. `:- module(m, [...])` → (`module`, the paren).
fn directive_goal<'a>(item: &'a Node, src: &'a str) -> Option<(String, Option<&'a Node>)> {
    let body = item.child(cst::BODY)?;
    let name = body.children.iter().find_map(|c| match c {
        Child::Token(t) if !t.trivia && t.kind == tk::ATOM => Some(atom_text(t.span.text(src))),
        _ => None,
    })?;
    Some((name, args_paren(body)))
}

/// The dependency target of an import goal's `Paren` (`use_module(library(lists))`
/// → (`lists`, true); `use_module(foo)` → (`foo`, false); `consult("x.pl")` →
/// (`x.pl`, false)). The first significant argument is inspected.
fn dep_target(paren: &Node, src: &str) -> Option<(String, bool)> {
    let els = significant_children(paren, src);
    let mut i = 0;
    while i < els.len() {
        match &els[i] {
            El::Tok { text, .. } if *text == "(" => {} // the paren's own delimiter
            El::Tok { text, kind } if *kind == tk::ATOM => {
                if *text == "library" {
                    // `library(Name)`: take the inner first atom.
                    if let Some(inner) = els
                        .get(i + 1)
                        .and_then(grp)
                        .and_then(|g| first_atom_in(g, src))
                    {
                        return Some((inner, true));
                    }
                    return Some(("library".to_string(), true));
                }
                return Some((atom_text(text), false));
            }
            El::Tok { text, kind } if *kind == tk::STRING => {
                return Some((string_text(text), false));
            }
            El::Tok { .. } => {}
            El::Grp(_) => {}
        }
        i += 1;
    }
    None
}

/// The first atom token (quotes stripped) anywhere in a subtree.
fn first_atom_in(node: &Node, src: &str) -> Option<String> {
    for n in node.walk() {
        for c in &n.children {
            if let Child::Token(t) = c {
                if !t.trivia && t.kind == tk::ATOM {
                    return Some(atom_text(t.span.text(src)));
                }
            }
        }
    }
    None
}

/// Collect the `(name, arity)` pairs exported by `:- module(_, [f/1, …])` and
/// `:- export([f/1, …])` / `:- export(f/1)` directives.
fn collect_exports(root: &Node, src: &str) -> BTreeSet<(String, usize)> {
    let mut out = BTreeSet::new();
    for form in root.child_nodes() {
        if form.kind != cst::DIRECTIVE {
            continue;
        }
        match directive_goal(form, src) {
            Some((name, Some(paren))) if name == "module" || name == "export" => {
                collect_fa_pairs(paren, src, &mut out);
            }
            _ => {}
        }
    }
    out
}

/// Scan a subtree's tokens for `atom / int` arity pairs (`append/3`), used for
/// export lists. A bare module-name atom (no following `/int`) never forms a pair.
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

/// A token usable as a goal/module name: an atom or a variable (dynamic module).
fn el_is_name(e: &El) -> bool {
    matches!(e, El::Tok { kind, .. } if *kind == tk::ATOM || *kind == tk::VAR)
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

/// Detect `p(...)` plain calls and `mod:p(...)` qualified calls over the real
/// token tree, recursing into nested groups. Only `name(Args)` shapes are
/// detected (0-arity goals and operator-notation goals are punted; see module
/// docs). Arity is read from the argument group.
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        // Qualified call: name `:` name `(...)`.
        if el_is_name(&els[i])
            && i + 3 < n
            && el_is(&els[i + 1], tk::ATOM)
            && el_text(&els[i + 1]) == Some(":")
            && el_is_name(&els[i + 2])
        {
            if let Some(g) = grp(&els[i + 3]) {
                if g.kind == cst::PAREN {
                    let receiver = match &els[i] {
                        El::Tok { text, kind } if *kind == tk::ATOM => Some(atom_text(text)),
                        _ => None, // variable module → dynamic, external
                    };
                    let name = el_text(&els[i + 2]).unwrap_or("");
                    out.push(Call {
                        name: atom_text(name),
                        arity: paren_arity(g, src),
                        qualified: true,
                        receiver,
                    });
                    i += 4;
                    continue;
                }
            }
        }
        // Plain call: atom `(...)`, not preceded by `:` (that is the qualified case).
        if el_is(&els[i], tk::ATOM) && i + 1 < n {
            if let Some(g) = grp(&els[i + 1]) {
                if g.kind == cst::PAREN {
                    let text = el_text(&els[i]).unwrap_or("");
                    let prev = if i > 0 { el_text(&els[i - 1]) } else { None };
                    if prev != Some(":") {
                        out.push(Call {
                            name: atom_text(text),
                            arity: paren_arity(g, src),
                            qualified: false,
                            receiver: None,
                        });
                    }
                }
            }
        }
        i += 1;
    }
    // Recurse into nested groups (argument lists, list terms, braces).
    for e in &els {
        if let Some(g) = grp(e) {
            scan_calls(g, src, out);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::prolog::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("app.pl", src);
        let file = SourceFile {
            rel_path: "app.pl".to_string(),
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
:- module(calc, [area/2, total/2]).
:- use_module(library(lists)).

area(R, A) :- A is 3.14159 * R * R.

total(List, Sum) :-
    maplist(double, List, Doubled),
    sumlist(Doubled, Sum).

double(X, Y) :- Y is X * 2.
";
        let tree = parse("calc.pl", src);
        assert!(tree.is_lossless(), "parse must round-trip before lowering");
        let file = SourceFile {
            rel_path: "src/calc.pl".to_string(),
            module_path: vec![],
            source: &tree.source,
            root: &tree.root,
        };
        let g = lower("calc", std::slice::from_ref(&file), &[]);
        assert!(g.count_nodes_of(ont::FUNCTION) >= 3, "area, total, double");
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "calc module");
        assert!(g.has_node("ext::lists"), "library(lists) dependency");
    }

    #[test]
    fn module_contains_file_and_declares_predicates() {
        let g = graph_for(":- module(m, []).\nf(ok).\n");
        assert!(g.has_node("mod::m"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::CONTAINS && e.from == "mod::m"));
        assert!(g.has_node("fn::m:f/1"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DECLARES && e.to == "fn::m:f/1"));
    }

    #[test]
    fn multi_clause_predicate_is_one_function_node() {
        let g = graph_for(
            ":- module(m, []).\nfac(0, 1).\nfac(N, F) :- N > 0, M is N - 1, fac(M, G), F is N * G.\n",
        );
        assert_eq!(g.count_nodes_of(ont::FUNCTION), 1, "one fac/2");
        let f = g.nodes().find(|n| n.kind == ont::FUNCTION).unwrap();
        assert_eq!(f.props.get("arity"), Some(&Json::U64(2)));
        assert_eq!(f.props.get("clauses"), Some(&Json::U64(2)));
    }

    #[test]
    fn resolves_local_call_by_arity() {
        let g =
            graph_for(":- module(m, []).\nrun(R) :- add(1, 2, R).\nadd(A, B, C) :- C is A + B.\n");
        let calls = call_edges(&g);
        let add = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("add")))
            .expect("a call to add");
        assert_eq!(add.to, "fn::m:add/3");
        assert_eq!(add.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(add.props.get("resolution"), Some(&Json::str("local")));
        assert_eq!(add.props.get("arity"), Some(&Json::U64(3)));
    }

    #[test]
    fn qualified_call_to_known_module_resolves() {
        let src_a = ":- module(a, []).\nrun(X) :- b:work(X).\n";
        let tree_a = parse("a.pl", src_a);
        let src_b = ":- module(b, [work/1]).\nwork(ok).\n";
        let tree_b = parse("b.pl", src_b);
        let fa = SourceFile {
            rel_path: "a.pl".to_string(),
            module_path: vec![],
            source: &tree_a.source,
            root: &tree_a.root,
        };
        let fb = SourceFile {
            rel_path: "b.pl".to_string(),
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
        assert_eq!(w.props.get("resolution"), Some(&Json::str("qualified")));
        assert_eq!(w.props.get("qualified"), Some(&Json::Bool(true)));
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for(":- module(m, []).\nrun :- mystery(42).\n");
        let calls = call_edges(&g);
        let myst = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("mystery")))
            .expect("a call to mystery");
        assert_eq!(myst.props.get("resolution"), Some(&Json::str("external")));
        assert!(g.has_node("unresolved::mystery"));
    }

    #[test]
    fn use_module_and_include_create_dependencies() {
        let g = graph_for(
            ":- module(m, []).\n:- use_module(library(lists)).\n:- include('defs.pl').\nf(ok).\n",
        );
        assert!(g.has_node("ext::lists"));
        assert!(g.has_node("ext::defs.pl"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::lists"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::IMPORTS && e.to == "ext::defs.pl"));
    }

    #[test]
    fn export_tags_predicates() {
        let g = graph_for(":- module(m, [pub/1]).\npub(ok).\npriv(secret).\n");
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
    fn dcg_rule_is_tagged() {
        let g = graph_for(":- module(m, []).\ngreeting --> [hello], thing.\nthing --> [world].\n");
        let greeting = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "greeting")
            .unwrap();
        assert_eq!(greeting.props.get("dcg"), Some(&Json::Bool(true)));
    }

    #[test]
    fn output_is_deterministic() {
        let src = ":- module(m, []).\n:- use_module(library(lists)).\nf(X) :- g(X).\ng(ok).\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
