//! Lower the Fortran CST into the canonical graph.
//!
//! Same conservative principles as the other front ends, adapted to Fortran's
//! surface. The mapping is deliberately honest about what the source states:
//!
//!   - `subroutine NAME(...) … end` and `function NAME(...) … end` (with any
//!     prefix) → [`Function`] (a `subprogram_kind` property records which).
//!   - `module NAME … end` and `program NAME … end` → [`Module`] (a `unit`
//!     property records which).
//!   - `type[, attrs] :: Name … end type` (a derived type) → [`Type`]
//!     (`type_kind` = `type`); a `extends(Base)` clause → [`EXTENDS`] (Fortran's
//!     `extends` is single inheritance into the derived-type tree).
//!   - `parameter` constants (`real, parameter :: PI = …` and the old
//!     `parameter (PI = …)` form) → [`Constant`].
//!   - `use modname` / `include 'file'` → [`IMPORTS`] (plus an
//!     [`ExternalDependency`] + `DEPENDS_ON` when the module/file is not
//!     project-local).
//!   - `::Type` / `type(T)` / `class(T)` annotations → [`USES_TYPE`] to unique
//!     project types.
//!   - call sites → [`CALLS`], resolved through a deterministic scope ladder
//!     (host module → global), preserving ambiguity.
//!
//! What Fortran honestly has no clean home for here, and how it is handled:
//!   - **Array references and function references are syntactically identical**
//!     (`a(i)` could be either). To avoid fabricating calls for array indexing
//!     and intrinsics, an *implicit* function reference is emitted as `CALLS`
//!     **only** when its name resolves to a project subprogram. An explicit
//!     `call sub(...)` statement is always emitted (to an external/unresolved
//!     node when needed), because the source states it is a call.
//!   - **Interface bodies** declare signatures, not definitions, so they do not
//!     create `Function` nodes.
//!   - **Type-bound procedures** (`obj%method(...)`) keep the method's simple
//!     name and record the qualifier; no `HAS_METHOD` is fabricated.
//!
//! Everything comes from real tokens on the lossless tree; nothing is guessed.
//! Fortran is case-insensitive, so all name *keys* (symbol tables, ids) are
//! lowercased while the displayed `name` preserves the source spelling.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::fortran::lexer::{is_keyword, kind as tk};
use crate::lang::fortran::parser::node as cst;
use crate::lang::frontend::SourceFile;

/// Lower a whole project's worth of Fortran files into a graph. `manifest_deps`
/// is unused (the pipeline reads no Fortran manifest); dependencies are
/// discovered from `use`/`include` instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    let mut local_roots: BTreeSet<String> = BTreeSet::new();
    local_roots.insert(package.to_ascii_lowercase());
    for f in files {
        for seg in &f.module_path {
            local_roots.insert(seg.to_ascii_lowercase());
        }
    }
    // Pre-scan every file for defined module names so a `use` of a module defined
    // later (or in another file) is recognised as project-local, not external.
    for f in files {
        for n in f.root.walk() {
            if n.kind == cst::MODULE {
                if let Some(name) = unit_name(n, f.source) {
                    local_roots.insert(name.to_ascii_lowercase());
                }
            }
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
        vec![("ecosystem", Json::str("fortran"))],
    );

    // Pass B: definition nodes, structural edges, imports, constants, symbol
    // tables. Functions/types collect pending work for the resolution pass.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_types: Vec<PendingType> = Vec::new();
    for f in files.iter() {
        let li = LineIndex::new(f.source);
        let file_id = format!("file::{}", f.rel_path);
        lo.g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("fortran")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(lo.pkg_id(), edge::CONTAINS, file_id.clone(), vec![]);

        lo.walk(
            f.root,
            &file_id,
            &file_id,
            "",
            f.source,
            &li,
            &mut pend_fns,
            &mut pend_types,
        );
    }

    // Pass C: resolve type uses + extends, then calls, against complete tables.
    for pt in std::mem::take(&mut pend_types) {
        if let Some(sup) = &pt.supertype {
            lo.emit_extends(&pt.id, sup);
        }
        for region in &pt.regions {
            lo.emit_type_uses(&pt.id, region, pt.source);
        }
    }
    for pf in std::mem::take(&mut pend_fns) {
        if let Some(body) = pf.body {
            lo.emit_type_uses(&pf.id, body, pf.source);
        }
        let ctx = Ctx {
            module_join: pf.module_join.clone(),
        };
        let mut calls = Vec::new();
        if let Some(body) = pf.body {
            collect_body_calls(body, pf.source, &mut calls);
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
    /// Lowercased simple name → all function node ids (global level).
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// (module_join, lowercased name) → function ids (host-module level).
    fn_by_module: BTreeMap<(String, String), Vec<String>>,
    /// Lowercased simple name → type node ids.
    type_by_name: BTreeMap<String, Vec<String>>,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    body: Option<&'a Node>,
    module_join: String,
}

struct PendingType<'a> {
    id: String,
    source: &'a str,
    supertype: Option<String>,
    regions: Vec<&'a Node>,
}

/// A detected call site.
struct Call {
    /// Simple name of the callee (lowercased for resolution; displayed as-is).
    name: String,
    /// Qualifier path before the name (`obj` in `obj%method(...)`), empty for bare.
    path: Vec<String>,
    /// True for an explicit `call` statement; false for a function reference.
    explicit: bool,
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

    #[allow(clippy::too_many_arguments)]
    fn walk<'a>(
        &mut self,
        container: &'a Node,
        file_id: &str,
        container_id: &str,
        module_join: &str,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_types: &mut Vec<PendingType<'a>>,
    ) {
        for item in container.child_nodes() {
            match item.kind {
                cst::PROGRAM | cst::MODULE => {
                    self.handle_module(item, file_id, container_id, src, li, pend_fns, pend_types)
                }
                cst::SUBROUTINE | cst::FUNCTION => self.handle_subprogram(
                    item,
                    file_id,
                    container_id,
                    module_join,
                    src,
                    li,
                    pend_fns,
                    pend_types,
                ),
                cst::TYPE_DEF => {
                    self.handle_type(item, container_id, module_join, src, li, pend_types)
                }
                cst::SIMPLE_STMT => {
                    self.handle_stmt(item, file_id, container_id, module_join, src, li)
                }
                // Interface bodies are declarations, not definitions — skipped.
                _ => {}
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_module<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        container_id: &str,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_types: &mut Vec<PendingType<'a>>,
    ) {
        let name = match unit_name(item, src) {
            Some(n) => n,
            None => return,
        };
        let unit = if item.kind == cst::PROGRAM {
            "program"
        } else {
            "module"
        };
        let name_lc = name.to_ascii_lowercase();
        let mod_id = format!("mod::{name_lc}");
        self.g.upsert_node(
            mod_id.clone(),
            ont::MODULE,
            name,
            vec![
                ("language", Json::str("fortran")),
                ("unit", Json::str(unit)),
            ],
        );
        self.g
            .add_edge(container_id, edge::CONTAINS, mod_id.clone(), vec![]);
        if let Some(block) = item.child(cst::BLOCK) {
            self.walk(
                block, file_id, &mod_id, &name_lc, src, li, pend_fns, pend_types,
            );
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_subprogram<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        container_id: &str,
        module_join: &str,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_types: &mut Vec<PendingType<'a>>,
    ) {
        let header = item.child(cst::HEADER);
        let name = header
            .and_then(|h| subprogram_name(h, src))
            .unwrap_or_else(|| "<anonymous>".to_string());
        let name_lc = name.to_ascii_lowercase();
        let line = li.line_col(name_start(item)).line;
        let kind = if item.kind == cst::FUNCTION {
            "function"
        } else {
            "subroutine"
        };
        let qual = qual_name(module_join, &name_lc);
        let id = format!("fn::{qual}#{line}");
        self.g.upsert_node(
            id.clone(),
            ont::FUNCTION,
            name,
            vec![
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("fortran")),
                ("subprogram_kind", Json::str(kind)),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
                ("has_body", Json::Bool(item.child(cst::BLOCK).is_some())),
            ],
        );
        self.g
            .add_edge(container_id, edge::DECLARES, id.clone(), vec![]);
        self.fn_by_name
            .entry(name_lc.clone())
            .or_default()
            .push(id.clone());
        self.fn_by_module
            .entry((module_join.to_string(), name_lc))
            .or_default()
            .push(id.clone());

        pend_fns.push(PendingFn {
            id: id.clone(),
            source: src,
            body: item.child(cst::BLOCK),
            module_join: module_join.to_string(),
        });

        // Recurse into the body for internal procedures (after `contains`) and
        // their declarations/imports/constants.
        if let Some(block) = item.child(cst::BLOCK) {
            self.walk(
                block,
                file_id,
                &id,
                module_join,
                src,
                li,
                pend_fns,
                pend_types,
            );
        }
    }

    fn handle_type<'a>(
        &mut self,
        item: &'a Node,
        container_id: &str,
        module_join: &str,
        src: &'a str,
        li: &LineIndex,
        pend_types: &mut Vec<PendingType<'a>>,
    ) {
        let header = item.child(cst::HEADER);
        let name = match header.and_then(|h| type_name(h, src)) {
            Some(n) => n,
            None => return,
        };
        let name_lc = name.to_ascii_lowercase();
        let line = li.line_col(name_start(item)).line;
        let qual = qual_name(module_join, &name_lc);
        let id = format!("type::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name,
            vec![
                ("type_kind", Json::str("type")),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("fortran")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
            ],
        );
        self.g
            .add_edge(container_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name
            .entry(name_lc)
            .or_default()
            .push(id.clone());

        let supertype = header.and_then(|h| extends_base(h, src));
        let mut regions = Vec::new();
        if let Some(h) = header {
            regions.push(h);
        }
        if let Some(b) = item.child(cst::BLOCK) {
            regions.push(b);
        }
        pend_types.push(PendingType {
            id,
            source: src,
            supertype,
            regions,
        });
    }

    fn handle_stmt(
        &mut self,
        item: &Node,
        file_id: &str,
        container_id: &str,
        module_join: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let els = significant_children(item, src);
        if els.is_empty() {
            return;
        }
        let t0 = el_text(&els[0]).unwrap_or("").to_ascii_lowercase();
        match t0.as_str() {
            "use" => self.handle_use(&els, file_id, src),
            "include" => self.handle_include(&els, file_id),
            _ if has_top_level(&els, "parameter") => {
                self.handle_parameter(item, container_id, module_join, src, li)
            }
            _ => {}
        }
    }

    fn handle_use(&mut self, els: &[El], file_id: &str, _src: &str) {
        let name = match use_module_name(els) {
            Some(n) => n,
            None => return,
        };
        let path = name.clone();
        let internal = self.local_roots.contains(&name.to_ascii_lowercase());
        if internal {
            let id = format!("mod::{}", name.to_ascii_lowercase());
            self.g.upsert_node(
                id.clone(),
                ont::MODULE,
                name,
                vec![("language", Json::str("fortran"))],
            );
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                id,
                vec![("path", Json::str(path)), ("external", Json::Bool(false))],
            );
        } else {
            let dep_id = format!("ext::{}", name.to_ascii_lowercase());
            self.g.upsert_node(
                dep_id.clone(),
                ont::EXTERNAL_DEPENDENCY,
                name,
                vec![("external", Json::Bool(true)), ("source", Json::str("use"))],
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

    fn handle_include(&mut self, els: &[El], file_id: &str) {
        // `include 'file.inc'` — the second token is a string literal.
        let raw = els.iter().skip(1).find_map(|e| match e {
            El::Tok { text, kind } if *kind == tk::STRING => Some(*text),
            _ => None,
        });
        let file = match raw {
            Some(s) => strip_quotes(s),
            None => return,
        };
        if file.is_empty() {
            return;
        }
        let dep_id = format!("ext::include::{file}");
        self.g.upsert_node(
            dep_id.clone(),
            ont::EXTERNAL_DEPENDENCY,
            file.clone(),
            vec![
                ("external", Json::Bool(true)),
                ("source", Json::str("include")),
            ],
        );
        self.g.add_edge(
            file_id,
            edge::IMPORTS,
            dep_id,
            vec![("path", Json::str(file)), ("external", Json::Bool(true))],
        );
    }

    fn handle_parameter(
        &mut self,
        item: &Node,
        container_id: &str,
        module_join: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let line = li.line_col(item.span.start).line;
        for name in extract_parameter_names(item, src) {
            let name_lc = name.to_ascii_lowercase();
            let id = format!("const::{}", qual_name(module_join, &name_lc));
            self.g.upsert_node(
                id.clone(),
                ont::CONSTANT,
                name,
                vec![
                    ("binding", Json::str("parameter")),
                    ("language", Json::str("fortran")),
                    ("line", Json::U64(line as u64)),
                ],
            );
            self.g.add_edge(container_id, edge::DECLARES, id, vec![]);
        }
    }

    // --- type-use & extends emission ----------------------------------------

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
                            ("role", Json::str("supertype")),
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

    /// Add `USES_TYPE` edges for `type(X)` / `class(X)` annotations in `region`
    /// naming a unique project type (not the using node itself).
    fn emit_type_uses(&mut self, from_id: &str, region: &Node, src: &str) {
        let mut names = Vec::new();
        scan_type_uses(region, src, &mut names);
        let mut seen: Vec<String> = Vec::new();
        for name in names {
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

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        // Host-module scope first, then global. Qualified `obj%m(...)` calls have
        // a runtime receiver type we cannot infer, so they resolve by simple name
        // globally (ambiguity preserved).
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
        // Implicit function references that resolve to nothing are almost always
        // array indexing or intrinsics — never fabricate a call for them.
        if !call.explicit && matches!(res.outcome, Outcome::None) {
            return;
        }
        let mut props = vec![
            ("callee", Json::str(call.name.clone())),
            ("explicit", Json::Bool(call.explicit)),
            ("resolution", Json::str(res.level)),
        ];
        if !call.path.is_empty() {
            props.push(("qualifier", Json::str(call.path.join("%"))));
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
        match self.type_by_name.get(&name.to_ascii_lowercase()) {
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

fn qual_name(module_join: &str, name_lc: &str) -> String {
    if module_join.is_empty() {
        name_lc.to_string()
    } else {
        format!("{module_join}::{name_lc}")
    }
}

fn unresolved_id(name: &str) -> String {
    format!("unresolved::{}", name.to_ascii_lowercase())
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
        .unwrap_or(item.span.start)
}

fn strip_quotes(s: &str) -> String {
    let bytes = s.as_bytes();
    if bytes.len() >= 2 {
        let first = bytes[0] as char;
        let last = bytes[bytes.len() - 1] as char;
        if (first == '\'' || first == '"') && last == first {
            return s[1..s.len() - 1].to_string();
        }
    }
    s.to_string()
}

/// Name of a `program`/`module` unit: the identifier after the leading keyword.
fn unit_name(item: &Node, src: &str) -> Option<String> {
    let header = item.child(cst::HEADER)?;
    let els = significant_children(header, src);
    // els[0] is the program/module keyword; the name is the next identifier.
    for e in els.iter().skip(1) {
        if let El::Tok { text, kind } = e {
            if *kind == tk::IDENT {
                return Some(text.to_string());
            }
        }
    }
    None
}

/// Name of a subprogram: the identifier immediately after the `function` /
/// `subroutine` keyword in the header (any prefix is skipped).
fn subprogram_name(header: &Node, src: &str) -> Option<String> {
    let els = significant_children(header, src);
    for k in 0..els.len() {
        if let El::Tok { text, .. } = &els[k] {
            let low = text.to_ascii_lowercase();
            if low == "function" || low == "subroutine" {
                if let Some(El::Tok { text: n, kind }) = els.get(k + 1) {
                    if *kind == tk::IDENT {
                        return Some(n.to_string());
                    }
                }
            }
        }
    }
    None
}

/// Name of a derived type: the identifier after `::` if present, else the first
/// identifier after the leading `type` keyword.
fn type_name(header: &Node, src: &str) -> Option<String> {
    let els = significant_children(header, src);
    if let Some(p) = els.iter().position(|e| el_text(e) == Some("::")) {
        for e in els.iter().skip(p + 1) {
            if let El::Tok { text, kind } = e {
                if *kind == tk::IDENT {
                    return Some(text.to_string());
                }
            }
        }
        return None;
    }
    // No `::`: `type Name`.
    for e in els.iter().skip(1) {
        if let El::Tok { text, kind } = e {
            if *kind == tk::IDENT {
                return Some(text.to_string());
            }
        }
    }
    None
}

/// Base type of an `extends(Base)` clause in a derived-type header.
fn extends_base(header: &Node, src: &str) -> Option<String> {
    let els = significant_children(header, src);
    for k in 0..els.len() {
        if let El::Tok { text, .. } = &els[k] {
            if text.eq_ignore_ascii_case("extends") {
                if let Some(g) = els.get(k + 1).and_then(el_group) {
                    if g.kind == cst::PAREN {
                        return first_ident_in(g, src);
                    }
                }
            }
        }
    }
    None
}

fn first_ident_in(group: &Node, src: &str) -> Option<String> {
    for e in significant_children(group, src) {
        if let El::Tok { text, kind } = e {
            if kind == tk::IDENT {
                return Some(text.to_string());
            }
        }
    }
    None
}

/// Module name of a `use` statement, skipping `, intrinsic ::` style attributes.
fn use_module_name(els: &[El]) -> Option<String> {
    for e in els.iter().skip(1) {
        match e {
            El::Tok { text, kind } => {
                if *text == "," || *text == "::" {
                    continue;
                }
                if *kind == tk::IDENT {
                    let low = text.to_ascii_lowercase();
                    if low == "intrinsic" || low == "non_intrinsic" {
                        continue;
                    }
                    return Some(text.to_string());
                }
                return None;
            }
            El::Grp(_) => return None,
        }
    }
    None
}

fn has_top_level(els: &[El], kw: &str) -> bool {
    els.iter()
        .any(|e| matches!(e, El::Tok { text, .. } if text.eq_ignore_ascii_case(kw)))
}

/// Names bound by a `parameter` declaration. Handles both
/// `<type>, parameter :: A = …, B = …` and the old `parameter (A = …, B = …)`.
fn extract_parameter_names(stmt: &Node, src: &str) -> Vec<String> {
    let els = significant_children(stmt, src);
    // Old form: `parameter (A = .., B = ..)`.
    if els
        .first()
        .map(|e| el_text(e) == Some("parameter"))
        .unwrap_or(false)
    {
        if let Some(g) = els.get(1).and_then(el_group) {
            if g.kind == cst::PAREN {
                let inner = significant_children(g, src);
                return names_before_eq(&inner);
            }
        }
    }
    // Attribute form: everything after `::`.
    if let Some(p) = els.iter().position(|e| el_text(e) == Some("::")) {
        return names_before_eq(&els[p + 1..]);
    }
    Vec::new()
}

/// Split a token sequence on top-level `,` and return, for each part, the first
/// identifier (the bound name) appearing before any `=`.
fn names_before_eq(els: &[El]) -> Vec<String> {
    let mut out = Vec::new();
    let mut name: Option<String> = None;
    let mut past_eq = false;
    for e in els {
        match e {
            El::Tok { text, kind } => {
                if *text == "," {
                    if let Some(n) = name.take() {
                        out.push(n);
                    }
                    past_eq = false;
                    continue;
                }
                if *text == "=" {
                    past_eq = true;
                    continue;
                }
                if !past_eq && name.is_none() && *kind == tk::IDENT && !is_keyword(text) {
                    name = Some(text.to_string());
                }
            }
            El::Grp(_) => {}
        }
    }
    if let Some(n) = name.take() {
        out.push(n);
    }
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

fn el_text<'a>(e: &El<'a>) -> Option<&'a str> {
    match e {
        El::Tok { text, .. } => Some(text),
        El::Grp(_) => None,
    }
}

/// The inner node of a group element, with the element's own lifetime.
fn el_group<'a>(e: &El<'a>) -> Option<&'a Node> {
    match e {
        El::Grp(n) => Some(n),
        El::Tok { .. } => None,
    }
}

fn el_is_ident(e: &El) -> bool {
    matches!(e, El::Tok { kind, .. } if *kind == tk::IDENT)
}

/// Is this statement a declaration (so it should not be scanned for implicit
/// function-reference calls, where `a(i)` is array indexing, not a call)?
fn is_declaration_stmt(stmt: &Node, src: &str) -> bool {
    let els = significant_children(stmt, src);
    if let Some(El::Tok { text, .. }) = els.first() {
        let low = text.to_ascii_lowercase();
        if matches!(
            low.as_str(),
            "integer"
                | "real"
                | "double"
                | "complex"
                | "logical"
                | "character"
                | "type"
                | "class"
                | "dimension"
                | "allocatable"
                | "pointer"
                | "target"
                | "intent"
                | "optional"
                | "save"
                | "external"
                | "intrinsic"
                | "public"
                | "private"
                | "protected"
                | "sequence"
                | "common"
                | "data"
                | "equivalence"
                | "namelist"
                | "parameter"
                | "use"
                | "include"
                | "implicit"
                | "import"
                | "procedure"
                | "bind"
        ) {
            return true;
        }
    }
    // Any top-level `::` marks an entity declaration.
    els.iter().any(|e| el_text(e) == Some("::"))
}

/// Collect every `type(X)` / `class(X)` annotation name in `node`, recursively.
fn scan_type_uses(node: &Node, src: &str, out: &mut Vec<String>) {
    let els = significant_children(node, src);
    for k in 0..els.len() {
        if let El::Tok { text, .. } = &els[k] {
            let low = text.to_ascii_lowercase();
            if low == "type" || low == "class" {
                if let Some(g) = els.get(k + 1).and_then(el_group) {
                    if g.kind == cst::PAREN {
                        if let Some(name) = first_ident_in(g, src) {
                            out.push(name);
                        }
                    }
                }
            }
        }
    }
    for e in &els {
        if let Some(g) = el_group(e) {
            scan_type_uses(g, src, out);
        }
    }
}

/// Collect call sites from a subprogram body block. Nested subprogram nodes are
/// skipped (they are scanned as their own pending functions).
fn collect_body_calls(block: &Node, src: &str, out: &mut Vec<Call>) {
    for item in block.child_nodes() {
        if matches!(
            item.kind,
            cst::SUBROUTINE | cst::FUNCTION | cst::TYPE_DEF | cst::INTERFACE
        ) {
            continue;
        }
        let in_decl = is_declaration_stmt(item, src);
        scan_calls(item, src, in_decl, out);
    }
}

/// Detect call sites over the real token tree: an explicit `call name(...)` /
/// `call obj%name(...)`, and (unless `in_decl`) implicit function references
/// `name(...)` / `obj%name(...)`. Recurses into `()`/`[]` groups.
fn scan_calls(node: &Node, src: &str, in_decl: bool, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        // Explicit `call` statement keyword.
        if let El::Tok { text, .. } = &els[i] {
            if text.eq_ignore_ascii_case("call") {
                let mut path: Vec<String> = Vec::new();
                let mut j = i + 1;
                loop {
                    match els.get(j) {
                        Some(El::Tok { text: t, kind }) if *kind == tk::IDENT && !is_keyword(t) => {
                            path.push(t.to_string());
                            j += 1;
                            if let Some(El::Tok { text: p, .. }) = els.get(j) {
                                if *p == "%" {
                                    j += 1;
                                    continue;
                                }
                            }
                            break;
                        }
                        _ => break,
                    }
                }
                if let Some(name) = path.pop() {
                    out.push(Call {
                        name: name.to_ascii_lowercase(),
                        path: path.iter().map(|s| s.to_ascii_lowercase()).collect(),
                        explicit: true,
                    });
                }
                i = j;
                continue;
            }
        }
        // Implicit function reference: ident (% ident)* '(' ... ')'.
        if !in_decl && el_is_ident(&els[i]) {
            let text = el_text(&els[i]).unwrap_or("");
            let prev = if i > 0 { el_text(&els[i - 1]) } else { None };
            if prev != Some("%") && !is_keyword(text) {
                let mut segs = vec![text.to_string()];
                let mut j = i;
                while j + 2 < n && el_text(&els[j + 1]) == Some("%") && el_is_ident(&els[j + 2]) {
                    segs.push(el_text(&els[j + 2]).unwrap_or("").to_string());
                    j += 2;
                }
                if let Some(g) = els.get(j + 1).and_then(el_group) {
                    if g.kind == cst::PAREN {
                        let name = segs.pop().unwrap();
                        out.push(Call {
                            name: name.to_ascii_lowercase(),
                            path: segs.iter().map(|s| s.to_ascii_lowercase()).collect(),
                            explicit: false,
                        });
                    }
                }
                i = j + 1;
                continue;
            }
        }
        i += 1;
    }
    // Recurse into balanced groups for nested calls (e.g. `f(g(x))`).
    for e in &els {
        if let Some(g) = el_group(e) {
            if g.kind == cst::PAREN || g.kind == cst::BRACKET {
                scan_calls(g, src, in_decl, out);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::fortran::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("demo.f90", src);
        let file = SourceFile {
            rel_path: "demo.f90".to_string(),
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
    fn emits_module_function_and_type_nodes() {
        let g = graph_for(
            "module m\n  type :: point\n    real :: x\n  end type point\ncontains\n  subroutine s()\n  end subroutine s\nend module m\n",
        );
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "module m");
        assert!(g.count_nodes_of(ont::TYPE) >= 1, "type point");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 1, "subroutine s");
    }

    #[test]
    fn subprogram_kinds_recorded() {
        let g = graph_for("subroutine s()\nend subroutine\nfunction f()\nend function\n");
        let kinds: Vec<&str> = g
            .nodes()
            .filter(|n| n.kind == ont::FUNCTION)
            .map(|n| match n.props.get("subprogram_kind") {
                Some(Json::Str(s)) => s.as_str(),
                _ => "",
            })
            .collect();
        assert!(kinds.contains(&"subroutine"));
        assert!(kinds.contains(&"function"));
    }

    #[test]
    fn explicit_call_is_resolved_local() {
        let g = graph_for(
            "module m\ncontains\n  subroutine a()\n    call b()\n  end subroutine a\n  subroutine b()\n  end subroutine b\nend module m\n",
        );
        let calls = call_edges(&g);
        let b = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("b")))
            .expect("a call to b");
        assert!(b.to.starts_with("fn::m::b"), "to = {}", b.to);
        assert_eq!(b.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(b.props.get("resolution"), Some(&Json::str("local")));
    }

    #[test]
    fn explicit_unknown_call_is_external() {
        let g = graph_for("subroutine s()\n  call mystery()\nend subroutine s\n");
        let calls = call_edges(&g);
        assert_eq!(calls.len(), 1);
        assert_eq!(
            calls[0].props.get("resolution"),
            Some(&Json::str("external"))
        );
        assert!(g.has_node("unresolved::mystery"));
    }

    #[test]
    fn implicit_unknown_reference_is_not_a_call() {
        // `a(i)` is array indexing, not a known function — must not fabricate.
        let g = graph_for("subroutine s()\n  real :: a(10)\n  x = a(3) + 1\nend subroutine s\n");
        let calls = call_edges(&g);
        assert!(
            calls.is_empty(),
            "array index must not become a CALLS edge: {calls:?}"
        );
    }

    #[test]
    fn implicit_reference_to_project_function_is_a_call() {
        let g = graph_for(
            "function sq(x)\n  real :: x, sq\n  sq = x*x\nend function sq\nsubroutine s()\n  y = sq(2.0)\nend subroutine s\n",
        );
        let calls = call_edges(&g);
        let sq = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("sq")));
        assert!(
            sq.is_some(),
            "call to project function sq should be detected"
        );
        assert_eq!(sq.unwrap().props.get("explicit"), Some(&Json::Bool(false)));
    }

    #[test]
    fn parameter_constants_are_constant_nodes() {
        let g =
            graph_for("module m\n  real, parameter :: pi = 3.14159, tau = 6.28\nend module m\n");
        assert!(g.nodes().any(|n| n.kind == ont::CONSTANT && n.name == "pi"));
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::CONSTANT && n.name == "tau"));
    }

    #[test]
    fn old_style_parameter_form() {
        let g = graph_for("subroutine s()\n  integer e\n  parameter (e = 42)\nend subroutine s\n");
        assert!(g.nodes().any(|n| n.kind == ont::CONSTANT && n.name == "e"));
    }

    #[test]
    fn use_creates_dependency() {
        let g = graph_for("module m\n  use iso_fortran_env\nend module m\n");
        assert!(g.has_node("ext::iso_fortran_env"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::iso_fortran_env"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn use_of_project_module_is_internal() {
        let g = graph_for(
            "module helpers\nend module helpers\nmodule app\n  use helpers\nend module app\n",
        );
        // The internal use should not create an external dependency.
        assert!(!g.has_node("ext::helpers"));
        assert!(g.has_node("mod::helpers"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::IMPORTS && e.to == "mod::helpers"));
    }

    #[test]
    fn extends_is_an_extends_edge() {
        let g = graph_for(
            "module m\n  type :: base\n  end type base\n  type, extends(base) :: derived\n  end type derived\nend module m\n",
        );
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an EXTENDS edge");
        assert!(ext.to.starts_with("type::"), "resolves to base type");
    }

    #[test]
    fn type_annotation_is_uses_type() {
        let g = graph_for(
            "module m\n  type :: circle\n    real :: r\n  end type circle\ncontains\n  subroutine grow(c)\n    type(circle) :: c\n  end subroutine grow\nend module m\n",
        );
        assert!(
            g.edges().any(|e| e.kind == edge::USES_TYPE),
            "type(circle) annotation should yield a USES_TYPE edge"
        );
    }

    #[test]
    fn case_insensitive_resolution() {
        // The call uses different casing than the definition.
        let g = graph_for(
            "module m\ncontains\n  subroutine Foo()\n  end subroutine Foo\n  subroutine bar()\n    call FOO()\n  end subroutine bar\nend module m\n",
        );
        let calls = call_edges(&g);
        let foo = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("foo")))
            .expect("a call to foo");
        assert_eq!(foo.props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn output_is_deterministic() {
        let src = "module m\n  real, parameter :: pi = 3.14\ncontains\n  subroutine run()\n    call helper()\n  end subroutine run\n  subroutine helper()\n  end subroutine helper\nend module m\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
