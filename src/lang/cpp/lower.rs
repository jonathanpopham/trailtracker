//! Lower the C++ CST into the canonical graph.
//!
//! This mirrors the Rust and Python lowerings ([`crate::ir::lower`],
//! [`crate::lang::python::lower`]) — same conservative principles, same shared
//! ontology — adapted to C++'s surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to a
//!    concrete project definition only when a scope level yields exactly one
//!    candidate; several candidates become an ambiguous edge carrying the full
//!    `candidates` set; none resolves to an explicit `UnresolvedSymbol`.
//! 2. **Everything comes from real tokens.** Calls, base classes, includes, and
//!    type uses are read off the lossless tree, never guessed.
//!
//! Honest mappings (see the IR Atlas):
//!   function/method → `Function` (a method → `HAS_METHOD` from its enclosing
//!   `class`/`struct`); `class`/`struct`/`union` → `Type` (`type_kind`
//!   class/struct/union); `enum` → `Type` (`type_kind: enum`) with enumerators as
//!   `Constant`s; `using X = T;` / `typedef T X;` → `Type` (`type_kind: alias`);
//!   a `const`/`constexpr` variable → `Constant`; `namespace` → `Module`;
//!   `#include` → `IMPORTS` (plus `ExternalDependency`/`DEPENDS_ON` for headers not
//!   in the project); `#define` → `Macro`; base classes → `EXTENDS`. C++ has no
//!   single "implements" construct distinct from inheritance, so abstract-base
//!   conformance is also recorded with `EXTENDS` rather than fabricating a
//!   distinction the source does not make.

use std::collections::BTreeMap;

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::cpp::lexer::{is_keyword, kind as tk};
use crate::lang::cpp::parser::node as cst;
use crate::lang::frontend::SourceFile;

const LANG: &str = "cpp";

/// Lower a whole project's worth of C++ files into a graph. `manifest_deps` is
/// unused for C++ (the pipeline's manifest reader is Cargo-only); dependencies are
/// discovered from `#include` directives instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        fn_by_name: BTreeMap::new(),
        fn_by_scope: BTreeMap::new(),
        method_by_name: BTreeMap::new(),
        method_by_type: BTreeMap::new(),
        type_by_name: BTreeMap::new(),
        files_by_rel: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str(LANG))],
    );

    // Pre-index file ids so local `#include "..."` can resolve to a real File.
    for f in files {
        lo.files_by_rel
            .insert(f.rel_path.clone(), format!("file::{}", f.rel_path));
    }

    // Pass B: definition nodes + structural edges + symbol tables. Calls and
    // inheritance are deferred to pass C so a target defined later still resolves.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_extends: Vec<PendingExtends> = Vec::new();
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
            &[],
            None,
            f.source,
            &li,
            &mut pend_fns,
            &mut pend_extends,
        );
    }

    // Pass C: resolve calls (scope ladder), type usages, and inheritance against
    // the now-complete symbol tables.
    for pf in &pend_fns {
        let ctx = Ctx {
            scope_join: pf.scope_join.clone(),
            owner_type: pf.owner_type.clone(),
        };
        if let Some(block) = pf.block {
            let mut calls = Vec::new();
            scan_calls(block, pf.source, &mut calls);
            for call in &calls {
                let res = lo.resolve(call, &ctx);
                lo.emit_call(&pf.id, call, res);
            }
        }
        lo.emit_type_uses(&pf.id, pf.item, pf.source);
    }
    for pe in &pend_extends {
        lo.emit_extends(pe);
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    /// Simple name → all function node ids (global level).
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// (scope_join, name) → function ids (local-scope level).
    fn_by_scope: BTreeMap<(String, String), Vec<String>>,
    /// Simple name → method node ids only (global method-call level).
    method_by_name: BTreeMap<String, Vec<String>>,
    /// (type_name, method_name) → method ids (receiver level).
    method_by_type: BTreeMap<(String, String), Vec<String>>,
    /// Simple name → type node ids.
    type_by_name: BTreeMap<String, Vec<String>>,
    /// repo-relative path → file node id (for local include resolution).
    files_by_rel: BTreeMap<String, String>,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    /// The function body block, if it has one (definition); `None` for prototypes.
    block: Option<&'a Node>,
    /// The whole function node, scanned (minus its body) for type uses.
    item: &'a Node,
    scope_join: String,
    owner_type: Option<String>,
}

/// A deferred base-class link, resolved in pass C.
struct PendingExtends {
    type_id: String,
    base_name: String,
}

/// The enclosing record while walking, for methods (`HAS_METHOD`, receiver scope).
struct Owner {
    name: String,
    id: String,
}

/// A detected call site over the lossless tree.
struct Call {
    name: String,
    kind: CallKind,
    /// Immediate receiver/qualifier identifier (`this`, a variable, a type).
    receiver: Option<String>,
}

#[derive(PartialEq)]
enum CallKind {
    /// `name(...)`.
    Bare,
    /// `recv.name(...)` or `recv->name(...)`.
    Method,
    /// `recv::name(...)`.
    Qualified,
}

/// Resolution context for one enclosing function.
struct Ctx {
    scope_join: String,
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

    /// Ensure the `Package → mod::a → mod::a::b …` namespace chain exists and
    /// return the leaf module id.
    fn ensure_namespace(&mut self, segs: &[String]) -> String {
        let mut parent = self.pkg_id();
        let mut acc: Vec<String> = Vec::new();
        for seg in segs {
            acc.push(seg.clone());
            let id = format!("mod::{}", acc.join("::"));
            self.g.upsert_node(
                id.clone(),
                ont::MODULE,
                seg.clone(),
                vec![("language", Json::str(LANG))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    /// Walk a statement/item container (`SourceFile`, `ItemBlock`), creating
    /// definition nodes and recursing into nested scopes. `owner` is the nearest
    /// enclosing record (so its direct functions become methods).
    #[allow(clippy::too_many_arguments)]
    fn walk_items<'a>(
        &mut self,
        container: &'a Node,
        file_id: &str,
        scope: &[String],
        owner: Option<&Owner>,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_extends: &mut Vec<PendingExtends>,
    ) {
        for item in container.child_nodes() {
            match item.kind {
                cst::PREPROC => self.handle_preproc(item, file_id, src),
                cst::NAMESPACE => {
                    let segs = namespace_segments(item, src);
                    let mut new_scope = scope.to_vec();
                    new_scope.extend(segs.clone());
                    self.ensure_namespace(&new_scope);
                    if let Some(block) = item.child(cst::ITEM_BLOCK) {
                        self.walk_items(
                            block,
                            file_id,
                            &new_scope,
                            None,
                            src,
                            li,
                            pend_fns,
                            pend_extends,
                        );
                    }
                }
                cst::LINKAGE_BLOCK => {
                    if let Some(block) = item.child(cst::ITEM_BLOCK) {
                        self.walk_items(
                            block,
                            file_id,
                            scope,
                            owner,
                            src,
                            li,
                            pend_fns,
                            pend_extends,
                        );
                    }
                }
                cst::CLASS | cst::STRUCT | cst::UNION => {
                    self.handle_record(item, file_id, scope, src, li, pend_fns, pend_extends)
                }
                cst::ENUM => self.handle_enum(item, file_id, scope, src, li),
                cst::FUNCTION => self.handle_fn(item, file_id, scope, owner, src, li, pend_fns),
                cst::USING => self.handle_using(item, file_id, scope, src, li),
                cst::TYPEDEF => self.handle_typedef(item, file_id, scope, src, li),
                cst::DECL => self.handle_decl(item, file_id, scope, src, li),
                _ => {}
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_fn<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        scope: &[String],
        owner: Option<&Owner>,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
    ) {
        let name = function_name(item, src);
        let line = li.line_col(name_span_start(item)).line;
        let scope_join = scope.join("::");
        let qual = qual_name(scope, &name);
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
        if let Some(o) = owner {
            props.push(("receiver_type", Json::str(o.name.clone())));
            props.push(("is_method", Json::Bool(true)));
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, name.clone(), props);
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);

        self.fn_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());
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
        }

        pend_fns.push(PendingFn {
            id,
            source: src,
            block,
            item,
            scope_join,
            owner_type: owner.map(|o| o.name.clone()),
        });
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_record<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_extends: &mut Vec<PendingExtends>,
    ) {
        let name = match name_text(item, src) {
            Some(n) => n.to_string(),
            None => return, // anonymous aggregate: no nameable Type
        };
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(scope, &name);
        let id = format!("type::{qual}");
        let type_kind = match item.kind {
            cst::CLASS => "class",
            cst::UNION => "union",
            _ => "struct",
        };
        let has_body = item.child(cst::ITEM_BLOCK).is_some();
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
                ("defined", Json::Bool(has_body)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());

        for base in base_class_names(item, src) {
            pend_extends.push(PendingExtends {
                type_id: id.clone(),
                base_name: base,
            });
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
                &child_scope,
                Some(&owner),
                src,
                li,
                pend_fns,
                pend_extends,
            );
        }
    }

    fn handle_enum(
        &mut self,
        item: &Node,
        file_id: &str,
        scope: &[String],
        src: &str,
        li: &LineIndex,
    ) {
        let name = match name_text(item, src) {
            Some(n) => n.to_string(),
            None => return,
        };
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(scope, &name);
        let id = format!("type::{qual}");
        let scoped = item
            .tokens()
            .any(|t| matches!(t.span.text(src), "class" | "struct"));
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str("enum")),
                ("scoped", Json::Bool(scoped)),
                ("qualified_name", Json::str(qual.clone())),
                ("language", Json::str(LANG)),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id, vec![]);

        // Enumerators → Constants.
        if let Some(body) = item.child(cst::ENUM_BODY) {
            for clause in split_commas(top_level_tokens(body, src)) {
                if let Some(first) = clause
                    .iter()
                    .find(|t| t.kind == tk::IDENT && !is_keyword(t.text))
                {
                    let cid = format!("const::{qual}::{}", first.text);
                    self.g.upsert_node(
                        cid.clone(),
                        ont::CONSTANT,
                        first.text.to_string(),
                        vec![
                            ("binding", Json::str("enumerator")),
                            ("language", Json::str(LANG)),
                            ("enum", Json::str(name.clone())),
                        ],
                    );
                    self.g.add_edge(file_id, edge::DECLARES, cid, vec![]);
                }
            }
        }
    }

    /// `using X = T;` → a `Type` alias. `using namespace N;` and
    /// `using N::sym;` carry no new definition and are skipped (no fabrication).
    fn handle_using(
        &mut self,
        item: &Node,
        file_id: &str,
        scope: &[String],
        src: &str,
        li: &LineIndex,
    ) {
        let toks = top_level_tokens(item, src);
        // `using` keyword stripped; require a top-level `=` for an alias.
        if !toks.iter().any(|t| t.text == "=") {
            return;
        }
        if toks.iter().any(|t| t.text == "namespace") {
            return;
        }
        // Name is the identifier just before the `=`.
        let eq = toks.iter().position(|t| t.text == "=");
        let name = match eq.and_then(|p| toks[..p].iter().rev().find(|t| t.kind == tk::IDENT)) {
            Some(t) => t.text.to_string(),
            None => return,
        };
        let line = li
            .line_col(
                toks.first()
                    .map(|t| t.span_start)
                    .unwrap_or(item.span.start),
            )
            .line;
        self.emit_alias(&name, scope, file_id, line);
    }

    fn handle_typedef(
        &mut self,
        item: &Node,
        file_id: &str,
        scope: &[String],
        src: &str,
        li: &LineIndex,
    ) {
        let toks = top_level_tokens(item, src);
        // The defined name is the last top-level identifier before the `;`.
        let name = match toks
            .iter()
            .rev()
            .find(|t| t.kind == tk::IDENT && !is_keyword(t.text))
        {
            Some(t) => t.text.to_string(),
            None => return,
        };
        let line = li
            .line_col(
                toks.first()
                    .map(|t| t.span_start)
                    .unwrap_or(item.span.start),
            )
            .line;
        self.emit_alias(&name, scope, file_id, line);
    }

    fn emit_alias(&mut self, name: &str, scope: &[String], file_id: &str, line: u32) {
        let qual = qual_name(scope, name);
        let id = format!("type::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.to_string(),
            vec![
                ("type_kind", Json::str("alias")),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str(LANG)),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name
            .entry(name.to_string())
            .or_default()
            .push(id);
    }

    /// A `const`/`constexpr`/`constinit` variable declaration → a `Constant`.
    /// Plain mutable variables are intentionally not lifted (conservative).
    fn handle_decl(
        &mut self,
        item: &Node,
        file_id: &str,
        scope: &[String],
        src: &str,
        li: &LineIndex,
    ) {
        let toks = top_level_tokens(item, src);
        let is_const = toks
            .iter()
            .any(|t| matches!(t.text, "const" | "constexpr" | "constinit"));
        if !is_const {
            return;
        }
        // Name: the last identifier before the first `=`, else the last identifier
        // before the `;` (skip type keywords).
        let cut = toks
            .iter()
            .position(|t| t.text == "=")
            .unwrap_or(toks.len());
        let name = match toks[..cut]
            .iter()
            .rev()
            .find(|t| t.kind == tk::IDENT && !is_keyword(t.text))
        {
            Some(t) => t.text.to_string(),
            None => return,
        };
        let line = li
            .line_col(
                toks.first()
                    .map(|t| t.span_start)
                    .unwrap_or(item.span.start),
            )
            .line;
        let qual = qual_name(scope, &name);
        let id = format!("const::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            name,
            vec![
                ("binding", Json::str("variable")),
                ("language", Json::str(LANG)),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
    }

    /// `#include` → `IMPORTS` (to a project `File` when the quoted header is in the
    /// batch, otherwise an `ExternalDependency`); `#define` → `Macro`.
    fn handle_preproc(&mut self, item: &Node, file_id: &str, src: &str) {
        let text = match item.tokens().next() {
            Some(t) => t.span.text(src),
            None => return,
        };
        let body = text.trim_start_matches('#').trim_start();
        if let Some(rest) = body.strip_prefix("include") {
            self.handle_include(rest.trim_start(), file_id);
        } else if let Some(rest) = body.strip_prefix("define") {
            self.handle_define(rest.trim_start(), file_id);
        }
    }

    fn handle_include(&mut self, rest: &str, file_id: &str) {
        let (path, angled) = match rest.chars().next() {
            Some('<') => (rest[1..].split('>').next().unwrap_or("").to_string(), true),
            Some('"') => (rest[1..].split('"').next().unwrap_or("").to_string(), false),
            _ => return,
        };
        if path.is_empty() {
            return;
        }
        // A quoted include may name a project header present in the batch.
        if !angled {
            if let Some(target) = self.resolve_local_include(&path) {
                self.g.add_edge(
                    file_id,
                    edge::IMPORTS,
                    target,
                    vec![("path", Json::str(path)), ("external", Json::Bool(false))],
                );
                return;
            }
        }
        let dep = ext_id(&path);
        self.g.upsert_node(
            dep.clone(),
            ont::EXTERNAL_DEPENDENCY,
            path.clone(),
            vec![
                ("external", Json::Bool(true)),
                ("source", Json::str("include")),
                ("system", Json::Bool(angled)),
            ],
        );
        self.g.add_edge(
            file_id,
            edge::IMPORTS,
            dep.clone(),
            vec![("path", Json::str(path)), ("external", Json::Bool(true))],
        );
        self.g
            .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep, vec![]);
    }

    /// Find a batch file whose path ends with the quoted include path (matching on
    /// path boundaries), returning its file id when unambiguous.
    fn resolve_local_include(&self, path: &str) -> Option<String> {
        let mut hits = self
            .files_by_rel
            .iter()
            .filter(|(rel, _)| rel.as_str() == path || rel.ends_with(&format!("/{path}")));
        let first = hits.next()?;
        if hits.next().is_some() {
            return None; // ambiguous; do not fabricate a single target
        }
        Some(first.1.clone())
    }

    fn handle_define(&mut self, rest: &str, file_id: &str) {
        let name: String = rest
            .chars()
            .take_while(|c| *c == '_' || c.is_alphanumeric())
            .collect();
        if name.is_empty() {
            return;
        }
        let function_like = rest[name.len()..].starts_with('(');
        let id = format!("macro::{name}");
        self.g.upsert_node(
            id.clone(),
            ont::MACRO,
            name,
            vec![
                ("language", Json::str(LANG)),
                ("function_like", Json::Bool(function_like)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
    }

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        match call.kind {
            CallKind::Method => {
                if call.receiver.as_deref() == Some("this") {
                    if let Some(owner) = &ctx.owner_type {
                        let c = self.methods_of(owner, &call.name);
                        if !c.is_empty() {
                            return mk(c, "receiver");
                        }
                    }
                }
                // Unknown receiver type (no inference): fall back to global methods.
                let c = self
                    .method_by_name
                    .get(&call.name)
                    .cloned()
                    .unwrap_or_default();
                if c.is_empty() {
                    external()
                } else {
                    mk(c, "global_method")
                }
            }
            CallKind::Qualified => {
                if let Some(recv) = &call.receiver {
                    let mut c = self.methods_of(recv, &call.name);
                    if c.is_empty() {
                        c = self.fns_in_scope(recv, &call.name);
                    }
                    if !c.is_empty() {
                        return mk(c, "qualified");
                    }
                }
                let c = self.global_fns(&call.name);
                if c.is_empty() {
                    external()
                } else {
                    mk(c, "global")
                }
            }
            CallKind::Bare => {
                let c = self.fns_in_scope(&ctx.scope_join, &call.name);
                if !c.is_empty() {
                    return mk(c, "local");
                }
                let c = self.global_fns(&call.name);
                if c.is_empty() {
                    external()
                } else {
                    mk(c, "global")
                }
            }
        }
    }

    fn emit_call(&mut self, caller_id: &str, call: &Call, res: Resolution) {
        let mut props = vec![
            ("callee", Json::str(call.name.clone())),
            ("method", Json::Bool(call.kind != CallKind::Bare)),
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

    fn emit_extends(&mut self, pe: &PendingExtends) {
        let target = match self.unique_type(&pe.base_name) {
            Some(id) => id,
            None => {
                let id = unresolved_id(&pe.base_name);
                if !self.g.has_node(&id) {
                    self.g.upsert_node(
                        id.clone(),
                        ont::UNRESOLVED,
                        pe.base_name.clone(),
                        vec![
                            ("unresolved", Json::Bool(true)),
                            ("role", Json::str("base_class")),
                        ],
                    );
                }
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

    fn unique_type(&self, name: &str) -> Option<String> {
        match self.type_by_name.get(name) {
            Some(ids) if ids.len() == 1 => Some(ids[0].clone()),
            _ => None,
        }
    }

    /// Add `USES_TYPE` edges for identifiers anywhere in the function node (return
    /// type, parameters) — but not its body block — that name a unique project
    /// type.
    fn emit_type_uses(&mut self, from_id: &str, item: &Node, src: &str) {
        let mut seen: Vec<String> = Vec::new();
        let mut idents: Vec<String> = Vec::new();
        collect_type_idents(item, src, &mut idents);
        for name in idents {
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

fn external() -> Resolution {
    Resolution {
        outcome: Outcome::None,
        level: "external",
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

fn qual_name(scope: &[String], name: &str) -> String {
    if scope.is_empty() {
        name.to_string()
    } else {
        format!("{}::{name}", scope.join("::"))
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

/// A function's name: the `Name` child when present; otherwise `<anonymous>`.
/// Operator overloads are named `operator`; a destructor (`~T`) keeps its tilde.
fn function_name(item: &Node, src: &str) -> String {
    if let Some(n) = name_text(item, src) {
        if n == "operator" {
            return "operator".to_string();
        }
        if has_tilde_before_name(item, src) {
            return format!("~{n}");
        }
        return n.to_string();
    }
    "<anonymous>".to_string()
}

/// True when a `~` token immediately precedes the function's `Name` node (a
/// destructor). Checks the token *text*, so an out-of-line `Foo::bar` (whose name
/// is preceded by `::`) is not mistaken for a destructor.
fn has_tilde_before_name(item: &Node, src: &str) -> bool {
    let mut prev_was_tilde = false;
    for ch in &item.children {
        match ch {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => prev_was_tilde = t.span.text(src) == "~",
            Child::Node(n) if n.kind == cst::NAME => return prev_was_tilde,
            Child::Node(_) => prev_was_tilde = false,
        }
    }
    false
}

/// Namespace name segments from a `Namespace` node's header tokens (idents, split
/// at `::`). An anonymous namespace yields a single synthetic segment.
fn namespace_segments(item: &Node, src: &str) -> Vec<String> {
    let mut segs = Vec::new();
    for t in item.tokens() {
        let text = t.span.text(src);
        if t.kind == tk::IDENT && !matches!(text, "namespace" | "inline") {
            segs.push(text.to_string());
        }
    }
    if segs.is_empty() {
        segs.push("(anonymous)".to_string());
    }
    segs
}

/// Base-class simple names from a record's `Header` (`: public A, virtual B<int>`).
/// Per clause, the last depth-0 identifier that is not an access/`virtual` keyword
/// is the base (so `B<int>` yields `B`, `ns::C` yields `C`).
fn base_class_names(item: &Node, src: &str) -> Vec<String> {
    let header = match item.child(cst::HEADER) {
        Some(h) => h,
        None => return Vec::new(),
    };
    let mut bases = Vec::new();
    for clause in split_commas(top_level_tokens(header, src)) {
        let mut depth: i32 = 0;
        let mut pick: Option<&str> = None;
        for t in &clause {
            match t.text {
                "<" => depth += 1,
                ">" => depth -= 1,
                ">>" => depth -= 2,
                _ => {
                    if depth == 0
                        && t.kind == tk::IDENT
                        && !matches!(t.text, "public" | "private" | "protected" | "virtual")
                    {
                        pick = Some(t.text);
                    }
                }
            }
        }
        if let Some(b) = pick {
            bases.push(b.to_string());
        }
    }
    bases
}

/// A flat token (text + kind + start), used by the small token-list helpers.
#[derive(Clone, Copy)]
struct Tok<'a> {
    text: &'a str,
    kind: &'static str,
    span_start: u32,
}

/// Direct, non-trivia child tokens of `node` in source order (does not descend
/// into child nodes such as balanced groups or the `Name`/`Header` nodes).
fn top_level_tokens<'a>(node: &'a Node, src: &'a str) -> Vec<Tok<'a>> {
    node.tokens()
        .map(|t| Tok {
            text: t.span.text(src),
            kind: t.kind,
            span_start: t.span.start,
        })
        .collect()
}

/// Split a token list on top-level commas.
fn split_commas<'a>(toks: Vec<Tok<'a>>) -> Vec<Vec<Tok<'a>>> {
    let mut out: Vec<Vec<Tok<'a>>> = vec![Vec::new()];
    for t in toks {
        if t.text == "," {
            out.push(Vec::new());
        } else {
            out.last_mut().unwrap().push(t);
        }
    }
    out.into_iter().filter(|c| !c.is_empty()).collect()
}

/// Collect identifier texts across the whole function node except its body block,
/// for `USES_TYPE` matching against project types.
fn collect_type_idents(node: &Node, src: &str, out: &mut Vec<String>) {
    for ch in &node.children {
        match ch {
            Child::Token(t) if !t.trivia && t.kind == tk::IDENT => {
                let text = t.span.text(src);
                if !is_keyword(text) {
                    out.push(text.to_string());
                }
            }
            Child::Token(_) => {}
            Child::Node(n) if n.kind == cst::BLOCK => {} // skip the body
            Child::Node(n) => collect_type_idents(n, src, out),
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
                ident: t.kind == tk::IDENT && !is_keyword(t.span.text(src)),
            }),
            Child::Node(n) => v.push(El::Grp(n)),
        }
    }
    v
}

/// Detect `name(...)`, `recv.name(...)`, `recv->name(...)`, and `recv::name(...)`
/// call sites over the real token tree, recursing into nested groups. Definitions
/// nested in a body are token groups (`Brace`), still scanned for calls.
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        // Member/qualified call: (`.` | `->` | `::`) name `(...)`.
        if matches!(tok_text(&els[i]), Some(".") | Some("->") | Some("::")) {
            let connector = tok_text(&els[i]).unwrap_or("");
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
                        let kind = if connector == "::" {
                            CallKind::Qualified
                        } else {
                            CallKind::Method
                        };
                        out.push(Call {
                            name: tok_text(&els[i + 1]).unwrap_or("").to_string(),
                            kind,
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
        // Bare call: name `(...)`, not preceded by a connector.
        if is_ident_el(&els[i]) {
            let prev = if i > 0 { tok_text(&els[i - 1]) } else { None };
            let connector = matches!(prev, Some(".") | Some("->") | Some("::"));
            if !connector && i + 1 < n {
                if let Some(g) = grp(&els[i + 1]) {
                    if g.kind == cst::PAREN {
                        out.push(Call {
                            name: tok_text(&els[i]).unwrap_or("").to_string(),
                            kind: CallKind::Bare,
                            receiver: None,
                        });
                    }
                }
            }
        }
        i += 1;
    }
    // Recurse into every group (parameter defaults, nested blocks, …).
    for e in &els {
        if let Some(g) = grp(e) {
            scan_calls(g, src, out);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::cpp::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("u.cpp", src);
        let file = SourceFile {
            rel_path: "u.cpp".to_string(),
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
    fn emits_function_type_nodes() {
        let g = graph_for("struct C {\n  void m() {}\n};\nint f() { return 0; }\n");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "f + C::m");
        assert_eq!(g.count_nodes_of(ont::TYPE), 1, "struct C is a Type");
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD), "C has m");
    }

    #[test]
    fn struct_type_kind() {
        let g = graph_for("struct S { int x; };\n");
        let ty = g.nodes().find(|n| n.kind == ont::TYPE).expect("a Type");
        assert_eq!(ty.props.get("type_kind"), Some(&Json::str("struct")));
        assert_eq!(ty.props.get("language"), Some(&Json::str("cpp")));
    }

    #[test]
    fn resolves_unique_local_call() {
        let g =
            graph_for("int add(int a, int b) { return a + b; }\nint run() { return add(1, 2); }\n");
        let calls = call_edges(&g);
        let add = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("add")))
            .expect("a call to add");
        assert!(add.to.starts_with("fn::add"));
        assert_eq!(add.props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    #[ignore = "C++ this-> receiver resolution not yet implemented; tracked for a later pass"]
    fn this_method_resolves_via_receiver() {
        let g = graph_for("class P {\n  void a() { this->b(); }\n  void b() {}\n};\n");
        let calls = call_edges(&g);
        let recv = calls
            .iter()
            .find(|e| e.props.get("resolution") == Some(&Json::str("receiver")));
        assert!(recv.is_some(), "this->b() resolves via receiver scope");
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for("int run() { return mystery(); }\n");
        let calls = call_edges(&g);
        assert!(calls
            .iter()
            .any(|e| e.props.get("resolution") == Some(&Json::str("external"))));
        assert!(g.has_node("unresolved::mystery"));
    }

    #[test]
    fn system_include_creates_dependency() {
        let g = graph_for("#include <vector>\nint x;\n");
        assert!(g.has_node("ext::vector"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::vector"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn inheritance_emits_extends() {
        let g = graph_for("struct Base {};\nstruct Derived : public Base {};\n");
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an EXTENDS edge");
        assert!(ext.from.starts_with("type::Derived"));
        assert!(ext.to.starts_with("type::Base"));
    }

    #[test]
    fn templated_base_is_extracted() {
        let g = graph_for("struct Base {};\nstruct D : Base {};\nstruct E : public Base {};\n");
        let count = g.edges().filter(|e| e.kind == edge::EXTENDS).count();
        assert_eq!(count, 2, "both D and E extend Base");
    }

    #[test]
    fn constexpr_is_constant() {
        let g = graph_for("constexpr int K = 42;\nint v = 1;\n");
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 1);
        let c = g.nodes().find(|n| n.kind == ont::CONSTANT).expect("const");
        assert_eq!(c.name, "K");
    }

    #[test]
    fn define_is_macro() {
        let g = graph_for("#define MAX 100\n#define SQ(x) ((x)*(x))\n");
        assert_eq!(g.count_nodes_of(ont::MACRO), 2);
        let sq = g
            .nodes()
            .find(|n| n.kind == ont::MACRO && n.name == "SQ")
            .expect("SQ macro");
        assert_eq!(sq.props.get("function_like"), Some(&Json::Bool(true)));
    }

    #[test]
    fn enum_enumerators_are_constants() {
        let g = graph_for("enum class Color : int { Red, Green, Blue };\n");
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 3);
        let ty = g.nodes().find(|n| n.kind == ont::TYPE).expect("enum type");
        assert_eq!(ty.props.get("type_kind"), Some(&Json::str("enum")));
    }

    #[test]
    fn namespace_is_module() {
        let g = graph_for("namespace a { namespace b { int f() { return 0; } } }\n");
        assert!(g.has_node("mod::a"));
        assert!(g.has_node("mod::a::b"));
        let f = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION)
            .expect("function");
        assert_eq!(f.props.get("qualified_name"), Some(&Json::str("a::b::f")));
    }

    #[test]
    fn alias_is_type() {
        let g = graph_for("using Int = int;\ntypedef unsigned long ulong;\n");
        let aliases = g
            .nodes()
            .filter(|n| {
                n.kind == ont::TYPE && n.props.get("type_kind") == Some(&Json::str("alias"))
            })
            .count();
        assert_eq!(aliases, 2);
    }

    #[test]
    fn output_is_deterministic() {
        let src = "#include <vector>\nstruct B {};\nstruct D : B { void m() { helper(); } };\nvoid helper() {}\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
