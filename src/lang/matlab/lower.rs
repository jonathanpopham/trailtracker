//! Lower the MATLAB CST into the canonical graph.
//!
//! This mirrors the other front ends — same conservative principles, same shared
//! ontology — adapted to MATLAB's surface. The mapping is deliberately honest
//! about what the source actually states:
//!
//!   - `function [out] = name(args) … end` (and the no-`end` script form) →
//!     [`Function`].
//!   - `classdef Name < Super` → [`Type`] (`type_kind` `class`); each `< Super`
//!     clause → [`EXTENDS`] (MATLAB single/multiple class inheritance is
//!     inheritance-shaped, so `EXTENDS`, not the conforms-to [`IMPLEMENTS`]).
//!   - methods inside a `methods … end` block → [`Function`] owned by the class
//!     via [`HAS_METHOD`] (and declared by it).
//!   - names inside `properties`/`events`/`enumeration … end` blocks →
//!     [`Constant`] declared by the class (with a `member_kind` discriminator).
//!   - `import pkg.Fn` / `import pkg.*` → [`IMPORTS`] (plus an
//!     [`ExternalDependency`] + `DEPENDS_ON` when the imported root is not
//!     project-local).
//!   - call sites `f(...)` / `obj.m(...)` → [`CALLS`], **only** when the callee
//!     resolves to a known project function/method. MATLAB shares `()` between a
//!     function call and array indexing (`a(i)`), so — exactly like the Fortran
//!     front end — an unresolved name is assumed to be indexing and **no** edge
//!     is fabricated. Ambiguity (a name matching several definitions) is
//!     preserved as a `candidates` set, never invented away.
//!
//! Honest non-coverage: MATLAB is dynamically typed, so there are no signature
//! type annotations to lower into `USES_TYPE` (none are emitted). Top-level
//! statements in a *script* file are not attributed call edges (there is no
//! enclosing function to be the caller) — consistent with the Julia front end.
//! Everything comes from real tokens on the lossless tree; nothing is guessed.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::matlab::lexer::{is_keyword, kind as tk};
use crate::lang::matlab::parser::node as cst;

/// Lower a whole project's worth of MATLAB files into a graph. `manifest_deps` is
/// unused (the pipeline reads no MATLAB manifest); dependencies are discovered
/// from `import` statements instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
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
        fn_by_module: BTreeMap::new(),
        type_by_name: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("matlab"))],
    );

    // Pass B: definition nodes, structural edges, symbol tables.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_types: Vec<PendingType> = Vec::new();
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
                ("language", Json::str("matlab")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(leaf, edge::CONTAINS, file_id.clone(), vec![]);

        lo.walk(
            f.root,
            &file_id,
            &module_join,
            f.source,
            &li,
            &mut pend_fns,
            &mut pend_types,
        );
    }

    // Pass C: resolve extends against the complete type table, then calls.
    for pt in std::mem::take(&mut pend_types) {
        for sup in &pt.supertypes {
            lo.emit_extends(&pt.id, sup);
        }
    }
    for pf in std::mem::take(&mut pend_fns) {
        let ctx = Ctx {
            module_join: pf.module_join.clone(),
        };
        let mut calls = Vec::new();
        for region in &pf.bodies {
            scan_calls(region, pf.source, &mut calls);
        }
        for call in &calls {
            let res = lo.resolve(call, &ctx);
            lo.emit_call(&pf.id, call, res);
        }
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    local_roots: BTreeSet<String>,
    fn_by_name: BTreeMap<String, Vec<String>>,
    fn_by_module: BTreeMap<(String, String), Vec<String>>,
    type_by_name: BTreeMap<String, Vec<String>>,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    /// Regions to scan for call sites (the function body block).
    bodies: Vec<&'a Node>,
    module_join: String,
}

struct PendingType {
    id: String,
    supertypes: Vec<String>,
}

struct Call {
    name: String,
    /// Qualifier path before the name (`obj` in `obj.m(...)`), empty for bare.
    path: Vec<String>,
}

struct Ctx {
    module_join: String,
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

    /// Ensure the `Package → mod::a → mod::a.b …` chain exists; return the leaf
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
                vec![("language", Json::str("matlab"))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    /// Walk a statement container, creating definition nodes and recursing into
    /// nested scopes to find further definitions and calls.
    #[allow(clippy::too_many_arguments)]
    fn walk<'a>(
        &mut self,
        container: &'a Node,
        container_id: &str,
        module_join: &str,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_types: &mut Vec<PendingType>,
    ) {
        for item in container.child_nodes() {
            match item.kind {
                cst::FUNCTION => {
                    self.handle_fn(item, container_id, module_join, src, li, None, pend_fns);
                }
                cst::CLASSDEF => {
                    self.handle_classdef(item, container_id, module_join, src, li, pend_fns, pend_types);
                }
                cst::IMPORT => {
                    self.handle_import(item, container_id, src);
                }
                cst::CONTROL | cst::BLOCK | cst::HEADER | cst::PAREN | cst::BRACKET | cst::BRACE => {
                    // Not new scopes for naming: recurse to find nested defs.
                    self.walk(item, container_id, module_join, src, li, pend_fns, pend_types);
                }
                _ => {}
            }
        }
    }

    /// A `function` definition. `owner` is `Some(type_id, class_join)` when the
    /// function is a method inside a `classdef`'s `methods` block — then it is
    /// owned by the class via `HAS_METHOD`.
    #[allow(clippy::too_many_arguments)]
    fn handle_fn<'a>(
        &mut self,
        func: &'a Node,
        container_id: &str,
        module_join: &str,
        src: &'a str,
        li: &LineIndex,
        owner: Option<(&str, &str)>,
        pend: &mut Vec<PendingFn<'a>>,
    ) {
        let header = func.child(cst::HEADER);
        let name = match header.and_then(|h| def_name(h, src)) {
            Some(n) => n,
            None => return,
        };
        let line = li.line_col(name_start(func)).line;
        let scope_join = owner.map(|(_, cj)| cj).unwrap_or(module_join);
        let qual = qual_name(scope_join, &name);
        let id = format!("fn::{qual}#{line}");

        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("matlab")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(func.span.start as u64)),
            ("span_end", Json::U64(func.span.end as u64)),
            ("has_body", Json::Bool(func.child(cst::BLOCK).is_some())),
        ];
        if owner.is_some() {
            props.push(("is_method", Json::Bool(true)));
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, name.clone(), props);
        self.g
            .add_edge(container_id, edge::DECLARES, id.clone(), vec![]);
        if let Some((type_id, _)) = owner {
            self.g.add_edge(type_id, edge::HAS_METHOD, id.clone(), vec![]);
        }

        self.fn_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());
        self.fn_by_module
            .entry((scope_join.to_string(), name))
            .or_default()
            .push(id.clone());

        let mut bodies = Vec::new();
        if let Some(block) = func.child(cst::BLOCK) {
            bodies.push(block);
        }
        pend.push(PendingFn {
            id,
            source: src,
            bodies,
            module_join: scope_join.to_string(),
        });
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_classdef<'a>(
        &mut self,
        item: &'a Node,
        container_id: &str,
        module_join: &str,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_types: &mut Vec<PendingType>,
    ) {
        let header = item.child(cst::HEADER);
        let (name, supertypes) = header
            .map(|h| class_name_and_supers(h, src))
            .unwrap_or((None, Vec::new()));
        let name = match name {
            Some(n) => n,
            None => return,
        };
        let line = li.line_col(name_start(item)).line;
        let qual = qual_name(module_join, &name);
        let id = format!("type::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str("class")),
                ("qualified_name", Json::str(qual.clone())),
                ("language", Json::str("matlab")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
            ],
        );
        self.g
            .add_edge(container_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name
            .entry(name)
            .or_default()
            .push(id.clone());
        pend_types.push(PendingType {
            id: id.clone(),
            supertypes,
        });

        // Member blocks live directly under the classdef BLOCK.
        if let Some(block) = item.child(cst::BLOCK) {
            for member in block.child_nodes() {
                match member.kind {
                    cst::METHODS => {
                        if let Some(mblock) = member.child(cst::BLOCK) {
                            for f in mblock.children_of(cst::FUNCTION) {
                                self.handle_fn(
                                    f,
                                    &id,
                                    module_join,
                                    src,
                                    li,
                                    Some((&id, &qual)),
                                    pend_fns,
                                );
                            }
                        }
                    }
                    cst::PROPERTIES => {
                        self.handle_members(member, &id, "property", src, li);
                    }
                    cst::EVENTS => {
                        self.handle_members(member, &id, "event", src, li);
                    }
                    cst::ENUMERATION => {
                        self.handle_members(member, &id, "enum", src, li);
                    }
                    _ => {}
                }
            }
        }
    }

    /// Each named entry in a `properties`/`events`/`enumeration` block → a
    /// [`Constant`] declared by the owning class.
    fn handle_members(
        &mut self,
        member_block: &Node,
        type_id: &str,
        member_kind: &'static str,
        src: &str,
        li: &LineIndex,
    ) {
        let block = match member_block.child(cst::BLOCK) {
            Some(b) => b,
            None => return,
        };
        for stmt in block.children_of(cst::SIMPLE_STMT) {
            let name = match first_ident_name(stmt, src) {
                Some(n) => n,
                None => continue,
            };
            let line = li.line_col(stmt.span.start).line;
            let id = format!("const::{type_id}::{name}");
            self.g.upsert_node(
                id.clone(),
                ont::CONSTANT,
                name,
                vec![
                    ("binding", Json::str(member_kind)),
                    ("member_kind", Json::str(member_kind)),
                    ("language", Json::str("matlab")),
                    ("line", Json::U64(line as u64)),
                ],
            );
            self.g.add_edge(type_id, edge::DECLARES, id, vec![]);
        }
    }

    /// `import` → IMPORTS, plus ExternalDependency/DEPENDS_ON when the imported
    /// root package is not project-local.
    fn handle_import(&mut self, item: &Node, container_id: &str, src: &str) {
        for (root, path) in import_clauses(item, src) {
            if root.is_empty() {
                continue;
            }
            let internal = self.local_roots.contains(&root);
            if internal {
                let id = format!("mod::{root}");
                self.g.upsert_node(
                    id.clone(),
                    ont::MODULE,
                    root,
                    vec![("language", Json::str("matlab"))],
                );
                self.g.add_edge(
                    container_id,
                    edge::IMPORTS,
                    id,
                    vec![("path", Json::str(path)), ("external", Json::Bool(false))],
                );
            } else {
                let dep_id = format!("ext::{root}");
                self.g.upsert_node(
                    dep_id.clone(),
                    ont::EXTERNAL_DEPENDENCY,
                    root,
                    vec![
                        ("external", Json::Bool(true)),
                        ("source", Json::str("import")),
                    ],
                );
                self.g.add_edge(
                    container_id,
                    edge::IMPORTS,
                    dep_id.clone(),
                    vec![("path", Json::str(path)), ("external", Json::Bool(true))],
                );
                self.g
                    .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
            }
        }
    }

    // --- extends emission ---------------------------------------------------

    fn emit_extends(&mut self, from_id: &str, super_name: &str) {
        let target = match self.unique_type(super_name) {
            Some(id) => id,
            None => {
                let uid = unresolved_id(super_name);
                if !self.g.has_node(&uid) {
                    self.g.upsert_node(
                        uid.clone(),
                        ont::UNRESOLVED,
                        super_name.to_string(),
                        vec![
                            ("unresolved", Json::Bool(true)),
                            ("role", Json::str("superclass")),
                        ],
                    );
                }
                uid
            }
        };
        self.g.add_edge(
            from_id,
            edge::EXTENDS,
            target,
            vec![("supertype", Json::str(super_name.to_string()))],
        );
    }

    // --- resolution ladder --------------------------------------------------

    /// Resolve a call by simple name: same-scope definitions first, then global.
    /// Qualified `obj.m(...)` receivers have a runtime type we cannot infer, so
    /// they resolve by simple name globally (ambiguity preserved).
    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        if call.path.is_empty() {
            let c = self.fns_in_module(&ctx.module_join, &call.name);
            if !c.is_empty() {
                return mk(c, "local");
            }
        }
        let c = self.global_fns(&call.name);
        if c.is_empty() {
            Resolution {
                outcome: Outcome::None,
                level: "external",
            }
        } else {
            mk(
                c,
                if call.path.is_empty() {
                    "global"
                } else {
                    "qualified"
                },
            )
        }
    }

    fn emit_call(&mut self, caller_id: &str, call: &Call, res: Resolution) {
        // MATLAB shares `()` between calls and array indexing, so an unresolved
        // name is assumed to be indexing — never fabricate a call for it.
        if matches!(res.outcome, Outcome::None) {
            return;
        }
        let mut props = vec![
            ("callee", Json::str(call.name.clone())),
            ("resolution", Json::str(res.level)),
        ];
        if !call.path.is_empty() {
            props.push(("qualifier", Json::str(call.path.join("."))));
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
            Outcome::None => {}
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

    fn fns_in_module(&self, module_join: &str, name: &str) -> Vec<String> {
        self.fn_by_module
            .get(&(module_join.to_string(), name.to_string()))
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

fn qual_name(module_join: &str, name: &str) -> String {
    if module_join.is_empty() {
        name.to_string()
    } else {
        format!("{module_join}.{name}")
    }
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

fn name_start(item: &Node) -> u32 {
    item.child(cst::HEADER)
        .map(|h| h.span.start)
        .or_else(|| item.child(cst::NAME).map(|n| n.span.start))
        .unwrap_or(item.span.start)
}

/// A function definition's simple name: the identifier after a top-level `=`
/// (output assignment), or the first identifier when there is none. `[a,b] = f`
/// and `y = f` and `f(x)` and bare `f` all yield the right name.
fn def_name(header: &Node, src: &str) -> Option<String> {
    let els = significant_children(header, src);
    let eq = els.iter().position(|e| matches!(e, El::Tok { text, .. } if *text == "="));
    let start = eq.map(|p| p + 1).unwrap_or(0);
    for e in &els[start..] {
        if let El::Tok { text, kind } = e {
            if *kind == tk::IDENT && !is_keyword(text) {
                return Some(text.to_string());
            }
        }
    }
    None
}

/// `(name, supertypes)` from a classdef header `[(attrs)] Name [< Super1 & Sup2]`.
/// The leading identifier (after any `(attrs)` group) is the class name; each
/// `&`-separated clause after a top-level `<` contributes its last dotted segment
/// as a supertype simple name.
fn class_name_and_supers(header: &Node, src: &str) -> (Option<String>, Vec<String>) {
    let els = significant_children(header, src);
    let lt = els
        .iter()
        .position(|e| matches!(e, El::Tok { text, .. } if *text == "<"));
    // Name: first identifier before `<`.
    let name_region = &els[..lt.unwrap_or(els.len())];
    let mut name: Option<String> = None;
    for e in name_region {
        if let El::Tok { text, kind } = e {
            if *kind == tk::IDENT && !is_keyword(text) {
                name = Some(text.to_string());
                break;
            }
        }
    }
    // Supertypes: last segment of each `&`-separated clause after `<`.
    let mut supers: Vec<String> = Vec::new();
    if let Some(p) = lt {
        let mut current: Option<String> = None;
        for e in &els[p + 1..] {
            match e {
                El::Tok { text, kind } if *kind == tk::IDENT && !is_keyword(text) => {
                    current = Some(text.to_string());
                }
                El::Tok { text, .. } if *text == "&" => {
                    if let Some(s) = current.take() {
                        supers.push(s);
                    }
                }
                El::Tok { text, .. } if *text == "." => {} // keep accumulating (last segment wins)
                _ => {}
            }
        }
        if let Some(s) = current.take() {
            supers.push(s);
        }
    }
    (name, supers)
}

/// The first identifier in a statement — the bound name of a property / event /
/// enumeration member (`x`, `x = 5`, `x (1,1) double = 0`).
fn first_ident_name(item: &Node, src: &str) -> Option<String> {
    for c in &item.children {
        if let Child::Token(t) = c {
            if t.trivia {
                continue;
            }
            let txt = t.span.text(src);
            if t.kind == tk::IDENT && !is_keyword(txt) {
                return Some(txt.to_string());
            }
            // A leading non-identifier token means this is not a plain member.
            return None;
        }
    }
    None
}

/// `import` clauses: each is a dotted path; the returned root is its first
/// segment, the full text is the clause. Handles `import a.b.c`, `import a.*`,
/// and several whitespace- or comma-separated clauses on one line.
fn import_clauses(item: &Node, src: &str) -> Vec<(String, String)> {
    let els = significant_children(item, src);
    let mut out: Vec<(String, String)> = Vec::new();
    let mut root = String::new();
    let mut text = String::new();
    let flush = |root: &mut String, text: &mut String, out: &mut Vec<(String, String)>| {
        if !root.is_empty() {
            out.push((std::mem::take(root), std::mem::take(text)));
        } else {
            text.clear();
        }
    };
    for e in &els {
        match e {
            El::Tok { text: t, .. } if *t == "import" => {}
            El::Tok { text: t, .. } if *t == "," => flush(&mut root, &mut text, &mut out),
            El::Tok { text: t, kind } => {
                text.push_str(t);
                if *kind == tk::IDENT && root.is_empty() && !is_keyword(t) {
                    root = t.to_string();
                }
            }
            El::Grp(_) => {}
        }
    }
    flush(&mut root, &mut text, &mut out);
    out
}

// --- scanning over the lossless token tree ----------------------------------

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

fn el_tok_text<'a>(e: &El<'a>) -> Option<&'a str> {
    match e {
        El::Tok { text, .. } => Some(text),
        El::Grp(_) => None,
    }
}

fn el_is_ident(e: &El) -> bool {
    matches!(e, El::Tok { kind, .. } if *kind == tk::IDENT)
}

/// Detect call sites over the real token tree: `name(...)` and `a.b.name(...)`.
/// Recurses into groups and nested non-`Function` nodes; nested `Function` nodes
/// are scanned as their own pending functions.
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        if el_is_ident(&els[i]) {
            let text = el_tok_text(&els[i]).unwrap_or("");
            let prev = if i > 0 { el_tok_text(&els[i - 1]) } else { None };
            // Not a call if preceded by `.` (it is the tail of a qualified path
            // already gathered from its head); keywords are never callees.
            if prev != Some(".") && !is_keyword(text) {
                let mut segs = vec![text.to_string()];
                let mut j = i;
                while j + 2 < n
                    && el_tok_text(&els[j + 1]) == Some(".")
                    && el_is_ident(&els[j + 2])
                {
                    segs.push(el_tok_text(&els[j + 2]).unwrap_or("").to_string());
                    j += 2;
                }
                if j + 1 < n {
                    if let El::Grp(g) = &els[j + 1] {
                        if g.kind == cst::PAREN {
                            let name = segs.pop().unwrap();
                            out.push(Call { name, path: segs });
                        }
                    }
                }
                i = j + 1;
                continue;
            }
        }
        i += 1;
    }
    for e in &els {
        if let El::Grp(g) = e {
            if g.kind != cst::FUNCTION {
                scan_calls(g, src, out);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::matlab::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("mod.m", src);
        let file = SourceFile {
            rel_path: "mod.m".to_string(),
            module_path: vec!["mod".to_string()],
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    fn call_edges(g: &Graph) -> Vec<&crate::graph::GraphEdge> {
        g.edges().filter(|e| e.kind == edge::CALLS).collect()
    }

    #[test]
    fn emits_function_nodes() {
        let g = graph_for("function y = f(x)\n  y = x + 1;\nend\n");
        assert!(
            g.nodes().any(|n| n.kind == ont::FUNCTION && n.name == "f"),
            "f should be a Function node"
        );
    }

    #[test]
    fn classdef_is_type_with_extends_and_methods() {
        let g = graph_for(
            "classdef Circle < handle\n  properties\n    radius = 1.0\n  end\n  methods\n    function a = area(obj)\n      a = obj.radius;\n    end\n  end\nend\n",
        );
        assert!(
            g.nodes().any(|n| n.kind == ont::TYPE && n.name == "Circle"),
            "Circle should be a Type"
        );
        assert!(
            g.edges().any(|e| e.kind == edge::EXTENDS),
            "the `< handle` clause should yield an EXTENDS edge"
        );
        assert!(
            g.edges().any(|e| e.kind == edge::HAS_METHOD),
            "area should be owned by Circle via HAS_METHOD"
        );
        assert!(
            g.nodes()
                .any(|n| n.kind == ont::CONSTANT && n.name == "radius"),
            "radius property should be a Constant"
        );
    }

    #[test]
    fn resolves_unique_local_call() {
        let g = graph_for(
            "function r = run()\n  r = add(1, 2);\nend\nfunction c = add(a, b)\n  c = a + b;\nend\n",
        );
        let calls = call_edges(&g);
        let add = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("add")))
            .expect("a call to add");
        assert!(add.to.starts_with("fn::mod.add"));
        assert_eq!(add.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(add.props.get("resolution"), Some(&Json::str("local")));
    }

    #[test]
    fn unknown_call_is_not_fabricated() {
        // `data(i)` is array indexing — must NOT become a call edge.
        let g = graph_for("function y = f(data, i)\n  y = data(i);\nend\n");
        let calls = call_edges(&g);
        assert!(calls.is_empty(), "indexing must not fabricate a call: {calls:?}");
        assert!(!g.has_node("unresolved::data"));
    }

    #[test]
    fn import_creates_dependency() {
        let g = graph_for("import matlab.net.http.RequestMessage\nfunction f()\nend\n");
        assert!(g.has_node("ext::matlab"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::matlab"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn output_is_deterministic() {
        let src = "classdef P\n  methods\n    function run(obj)\n      helper();\n    end\n  end\nend\nfunction helper()\nend\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
