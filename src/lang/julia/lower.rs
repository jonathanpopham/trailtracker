//! Lower the Julia CST into the canonical graph.
//!
//! This mirrors the other front ends — same conservative principles, same shared
//! ontology — adapted to Julia's surface. Julia is a multiple-dispatch language:
//! methods are *free functions* selected on argument types, not members bundled
//! inside a type. The mapping is therefore deliberately honest about what the
//! source actually states:
//!
//!   - `function f(...) … end` (long form) and `f(x) = …` (short form) →
//!     [`Function`]. A qualified definition target (`Base.show(...)`) keeps the
//!     simple name and records the qualifier.
//!   - `macro m(...) … end` → [`Macro`].
//!   - `struct` / `mutable struct` → [`Type`] (`type_kind` `struct` /
//!     `mutable_struct`); `abstract type` → `abstract`; `primitive type` →
//!     `primitive`.
//!   - a `<: Super` supertype clause → [`EXTENDS`] (Julia's `<:` is single
//!     subtyping into the abstract-type tree — inheritance-shaped, so `EXTENDS`,
//!     not the conforms-to [`IMPLEMENTS`]).
//!   - `using` / `import` → [`IMPORTS`] (plus an [`ExternalDependency`] +
//!     `DEPENDS_ON` when the module is not project-local; a leading `.` marks a
//!     relative/internal import).
//!   - `const NAME = …` → [`Constant`].
//!   - `::Type` annotations and field types → [`USES_TYPE`] to unique project
//!     types.
//!   - call sites `f(...)` / `Mod.f(...)` → [`CALLS`], resolved through a
//!     deterministic scope ladder (local module → global), preserving ambiguity.
//!
//! What Julia honestly has **no** home for here: there are no class methods (so
//! no `HAS_METHOD`), and multiple dispatch means a call name maps to *many*
//! method definitions — we never fabricate a single target; an ambiguous call is
//! emitted with its full `candidates` set. Everything comes from real tokens on
//! the lossless tree; nothing is guessed.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::julia::lexer::{is_keyword, kind as tk};
use crate::lang::julia::parser::node as cst;

/// Lower a whole project's worth of Julia files into a graph. `manifest_deps` is
/// unused for Julia (the pipeline reads no Julia manifest); dependencies are
/// discovered from `using`/`import` instead.
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
        vec![("ecosystem", Json::str("julia"))],
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
                ("language", Json::str("julia")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(leaf, edge::CONTAINS, file_id.clone(), vec![]);

        lo.walk(
            f.root,
            &file_id,
            &file_id,
            &module_join,
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
        if let Some(sig) = pf.signature {
            lo.emit_type_uses(&pf.id, sig, pf.source);
        }
        let ctx = Ctx {
            module_join: pf.module_join.clone(),
        };
        let mut calls = Vec::new();
        for region in &pf.bodies {
            scan_calls(region, pf.source, pf.skip_first_call, &mut calls);
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
    /// Regions to scan for call sites (function body, or short-form RHS).
    bodies: Vec<&'a Node>,
    /// Signature region for `USES_TYPE` extraction (`None` for anonymous).
    signature: Option<&'a Node>,
    module_join: String,
    /// When the body region is the whole short-form statement, skip the leading
    /// `name(args)` so the definition is not mistaken for a self-call.
    skip_first_call: bool,
}

struct PendingType<'a> {
    id: String,
    source: &'a str,
    supertype: Option<String>,
    regions: Vec<&'a Node>,
}

struct Call {
    name: String,
    /// Qualifier path before the name (`Base` in `Base.show(...)`), empty for bare.
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
                vec![("language", Json::str("julia"))],
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
                cst::FUNCTION => {
                    self.handle_fn(item, None, container_id, module_join, src, li, pend_fns);
                }
                cst::MACRO_DEF => {
                    self.handle_macro(item, container_id, module_join, src, li);
                }
                cst::STRUCT | cst::ABSTRACT_TYPE | cst::PRIMITIVE_TYPE => {
                    self.handle_type(item, container_id, module_join, src, li, pend_types);
                }
                cst::MODULE => {
                    self.handle_module(
                        item,
                        file_id,
                        container_id,
                        module_join,
                        src,
                        li,
                        pend_fns,
                        pend_types,
                    );
                }
                cst::CONST => {
                    self.handle_const(item, container_id, module_join, src, li);
                }
                cst::IMPORT => {
                    self.handle_import(item, file_id, src);
                }
                cst::SIMPLE_STMT => {
                    self.handle_simple(item, file_id, container_id, module_join, src, li, pend_fns);
                }
                cst::CONTROL
                | cst::BLOCK
                | cst::HEADER
                | cst::PAREN
                | cst::BRACKET
                | cst::BRACE => {
                    // Not new scopes for naming: recurse to find nested defs/funcs.
                    self.walk(
                        item,
                        file_id,
                        container_id,
                        module_join,
                        src,
                        li,
                        pend_fns,
                        pend_types,
                    );
                }
                _ => {}
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_fn<'a>(
        &mut self,
        func: &'a Node,
        name_override: Option<Vec<String>>,
        container_id: &str,
        module_join: &str,
        src: &'a str,
        li: &LineIndex,
        pend: &mut Vec<PendingFn<'a>>,
    ) {
        let header = func.child(cst::HEADER);
        let path = name_override
            .or_else(|| header.and_then(|h| def_name_path(h, src)))
            .unwrap_or_default();
        let line = li.line_col(name_start(func)).line;

        let (name, qual) = if path.is_empty() {
            (
                "<anonymous>".to_string(),
                qual_name(module_join, "<anonymous>"),
            )
        } else {
            let n = path.last().unwrap().clone();
            (n.clone(), qual_name(module_join, &path.join(".")))
        };
        let id = if path.is_empty() {
            format!("fn::{qual}#{line}@{}", func.span.start)
        } else {
            format!("fn::{qual}#{line}")
        };

        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("julia")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(func.span.start as u64)),
            ("span_end", Json::U64(func.span.end as u64)),
            ("has_body", Json::Bool(func.child(cst::BLOCK).is_some())),
        ];
        if path.len() > 1 {
            props.push(("qualifier", Json::str(path[..path.len() - 1].join("."))));
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, name.clone(), props);
        self.g
            .add_edge(container_id, edge::DECLARES, id.clone(), vec![]);

        if !path.is_empty() {
            self.fn_by_name
                .entry(name.clone())
                .or_default()
                .push(id.clone());
            self.fn_by_module
                .entry((module_join.to_string(), name.clone()))
                .or_default()
                .push(id.clone());
        }

        let mut bodies = Vec::new();
        if let Some(block) = func.child(cst::BLOCK) {
            bodies.push(block);
        }
        pend.push(PendingFn {
            id,
            source: src,
            bodies,
            signature: header,
            module_join: module_join.to_string(),
            skip_first_call: false,
        });

        // Recurse into the body for nested definitions / anonymous functions.
        if let Some(block) = func.child(cst::BLOCK) {
            let mut tmp_types = Vec::new();
            self.walk(
                block,
                container_id,
                container_id,
                module_join,
                src,
                li,
                pend,
                &mut tmp_types,
            );
            for pt in tmp_types {
                pend_types_into(self, pt);
            }
        }
    }

    fn handle_macro(
        &mut self,
        item: &Node,
        container_id: &str,
        module_join: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let path = item
            .child(cst::HEADER)
            .and_then(|h| def_name_path(h, src))
            .unwrap_or_default();
        if path.is_empty() {
            return;
        }
        let name = path.last().unwrap().clone();
        let line = li.line_col(name_start(item)).line;
        let qual = qual_name(module_join, &name);
        let id = format!("macro::{qual}#{line}");
        self.g.upsert_node(
            id.clone(),
            ont::MACRO,
            name,
            vec![
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("julia")),
                ("line", Json::U64(line as u64)),
                ("role", Json::str("definition")),
            ],
        );
        self.g.add_edge(container_id, edge::DECLARES, id, vec![]);
    }

    #[allow(clippy::too_many_arguments)]
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
        let (name, supertype) = header
            .map(|h| type_name_and_super(h, src))
            .unwrap_or((None, None));
        let name = match name {
            Some(n) => n,
            None => return,
        };
        let line = li.line_col(name_start(item)).line;
        let mutable = item.tokens().any(|t| t.span.text(src) == "mutable");
        let type_kind = match item.kind {
            cst::STRUCT if mutable => "mutable_struct",
            cst::STRUCT => "struct",
            cst::ABSTRACT_TYPE => "abstract",
            cst::PRIMITIVE_TYPE => "primitive",
            _ => "type",
        };
        let qual = qual_name(module_join, &name);
        let id = format!("type::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str(type_kind)),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("julia")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
            ],
        );
        self.g
            .add_edge(container_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name.entry(name).or_default().push(id.clone());

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

    #[allow(clippy::too_many_arguments)]
    fn handle_module<'a>(
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
        let name = match item.child(cst::NAME).and_then(|n| n.tokens().next()) {
            Some(t) => t.span.text(src).to_string(),
            None => return,
        };
        let child_join = if module_join.is_empty() {
            name.clone()
        } else {
            format!("{module_join}.{name}")
        };
        let mod_id = format!("mod::{child_join}");
        self.g.upsert_node(
            mod_id.clone(),
            ont::MODULE,
            name,
            vec![
                ("language", Json::str("julia")),
                ("inline", Json::Bool(true)),
            ],
        );
        self.g
            .add_edge(container_id, edge::CONTAINS, mod_id.clone(), vec![]);
        if let Some(block) = item.child(cst::BLOCK) {
            self.walk(
                block,
                file_id,
                &mod_id,
                &child_join,
                src,
                li,
                pend_fns,
                pend_types,
            );
        }
    }

    fn handle_const(
        &mut self,
        item: &Node,
        container_id: &str,
        module_join: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let name = match first_binding_name(item, src) {
            Some(n) => n,
            None => return,
        };
        let line = li.line_col(item.span.start).line;
        let id = format!("const::{}", qual_name(module_join, &name));
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            name,
            vec![
                ("binding", Json::str("const")),
                ("language", Json::str("julia")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(container_id, edge::DECLARES, id, vec![]);
    }

    /// `using`/`import` → IMPORTS, plus ExternalDependency/DEPENDS_ON when the
    /// imported root module is not project-local. A leading `.` (relative import)
    /// is treated as internal.
    fn handle_import(&mut self, item: &Node, file_id: &str, src: &str) {
        for (root, relative, path) in import_roots(item, src) {
            if root.is_empty() {
                continue;
            }
            let internal = relative || self.local_roots.contains(&root);
            if internal {
                let id = format!("mod::{root}");
                self.g.upsert_node(
                    id.clone(),
                    ont::MODULE,
                    root,
                    vec![("language", Json::str("julia"))],
                );
                self.g.add_edge(
                    file_id,
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
                        ("source", Json::str("using_import")),
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

    /// A simple statement: detect a short-form function definition `f(x) = …`,
    /// otherwise recurse for nested anonymous functions / do-blocks and scan no
    /// definitions.
    #[allow(clippy::too_many_arguments)]
    fn handle_simple<'a>(
        &mut self,
        stmt: &'a Node,
        file_id: &str,
        container_id: &str,
        module_join: &str,
        src: &'a str,
        li: &LineIndex,
        pend: &mut Vec<PendingFn<'a>>,
    ) {
        if let Some(name) = short_func_name(stmt, src) {
            let line = li.line_col(stmt.span.start).line;
            let qual = qual_name(module_join, &name);
            let id = format!("fn::{qual}#{line}");
            self.g.upsert_node(
                id.clone(),
                ont::FUNCTION,
                name.clone(),
                vec![
                    ("qualified_name", Json::str(qual)),
                    ("language", Json::str("julia")),
                    ("line", Json::U64(line as u64)),
                    ("span_start", Json::U64(stmt.span.start as u64)),
                    ("span_end", Json::U64(stmt.span.end as u64)),
                    ("has_body", Json::Bool(true)),
                    ("short_form", Json::Bool(true)),
                ],
            );
            self.g
                .add_edge(container_id, edge::DECLARES, id.clone(), vec![]);
            self.fn_by_name
                .entry(name.clone())
                .or_default()
                .push(id.clone());
            self.fn_by_module
                .entry((module_join.to_string(), name.clone()))
                .or_default()
                .push(id.clone());
            pend.push(PendingFn {
                id,
                source: src,
                bodies: vec![stmt],
                signature: Some(stmt),
                module_join: module_join.to_string(),
                skip_first_call: true,
            });
        }

        // Recurse into groups / nested constructs for anonymous functions.
        let mut tmp_types = Vec::new();
        self.walk(
            stmt,
            file_id,
            container_id,
            module_join,
            src,
            li,
            pend,
            &mut tmp_types,
        );
        for pt in tmp_types {
            pend_types_into(self, pt);
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

    /// Add `USES_TYPE` edges for identifiers in `region` naming a unique project
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

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        if !call.path.is_empty() {
            // Qualified `Mod.f(...)`: Julia's dispatch is undecidable statically,
            // so match by simple name globally; ambiguity is preserved.
            let c = self.global_fns(&call.name);
            return if c.is_empty() {
                Resolution {
                    outcome: Outcome::None,
                    level: "external",
                }
            } else {
                mk(c, "qualified")
            };
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
        match self.type_by_name.get(name) {
            Some(ids) if ids.len() == 1 => Some(ids[0].clone()),
            _ => None,
        }
    }
}

/// Defer a pending type discovered while recursing into a function/simple-stmt
/// body. Type uses/extends for these are resolved immediately (the symbol tables
/// for nested types are rare; resolve against what is known so far). Kept as a
/// free function to avoid borrow tangles in the recursive walk.
fn pend_types_into(lo: &mut Lowerer, pt: PendingType<'_>) {
    if let Some(sup) = &pt.supertype {
        lo.emit_extends(&pt.id, sup);
    }
    for region in &pt.regions {
        lo.emit_type_uses(&pt.id, region, pt.source);
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

/// Extract a function definition's dotted name path from its HEADER: the leading
/// `ident (. ident)*` run that precedes the `(` parameter list. An anonymous
/// `function (x)` (header begins with a group) yields `None`.
fn def_name_path(header: &Node, src: &str) -> Option<Vec<String>> {
    let mut segs: Vec<String> = Vec::new();
    let mut expect_name = true;
    for c in &header.children {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => {
                let txt = t.span.text(src);
                if expect_name {
                    if t.kind == tk::IDENT && !is_keyword(txt) {
                        segs.push(txt.to_string());
                        expect_name = false;
                    } else {
                        break;
                    }
                } else if txt == "." {
                    expect_name = true;
                } else {
                    break; // `(`, `::`, operator, etc. ends the name path
                }
            }
            Child::Node(_) => break, // a `(...)` param group ends the name path
        }
    }
    if segs.is_empty() {
        None
    } else {
        Some(segs)
    }
}

/// Extract `(name, supertype)` simple names from a type header
/// (`Name[{params}] [<: Super[{...}]]`). Only the leading identifier is the name;
/// the identifier following a top-level `<:` is the supertype.
fn type_name_and_super(header: &Node, src: &str) -> (Option<String>, Option<String>) {
    let mut name: Option<String> = None;
    let mut supertype: Option<String> = None;
    let mut seen_sub = false;
    let mut depth: i32 = 0;
    for c in &header.children {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => {
                let txt = t.span.text(src);
                if txt == "<:" && depth == 0 {
                    seen_sub = true;
                    continue;
                }
                // Track `{...}` curly depth via single punct chars (a `{` group is
                // a Node, but a bare `{`/`}` token may appear in flat headers).
                if txt == "{" {
                    depth += 1;
                } else if txt == "}" {
                    depth -= 1;
                    if depth < 0 {
                        depth = 0;
                    }
                } else if depth == 0 && t.kind == tk::IDENT && !is_keyword(txt) {
                    if seen_sub {
                        if supertype.is_none() {
                            supertype = Some(txt.to_string());
                        }
                    } else if name.is_none() {
                        name = Some(txt.to_string());
                    }
                }
            }
            // A `{...}` type-parameter group (or any nested group) is not part of
            // the name/supertype reading; the supertype is the top-level ident
            // after `<:`.
            Child::Node(_) => {}
        }
    }
    (name, supertype)
}

/// The bound name of a `const NAME = …` statement (the first identifier).
fn first_binding_name(item: &Node, src: &str) -> Option<String> {
    for c in &item.children {
        if let Child::Token(t) = c {
            if t.trivia {
                continue;
            }
            let txt = t.span.text(src);
            if t.kind == tk::IDENT && !is_keyword(txt) {
                return Some(txt.to_string());
            }
            if txt == "const" || txt == "global" || txt == "local" {
                continue;
            }
            break;
        }
    }
    None
}

/// If `stmt` is a short-form function definition `name(args) [::T] [where …] = …`,
/// return the function's simple name. Conservative: anything other than an
/// identifier, a `(...)` group, a `::` type clause, a `where` clause, or a `.`
/// before the `=` clears the match.
fn short_func_name(stmt: &Node, src: &str) -> Option<String> {
    let els = significant_children(stmt, src);
    if els.len() < 3 {
        return None;
    }
    // [0] must be an identifier (the function name).
    let name = match &els[0] {
        El::Tok { text, kind } if *kind == tk::IDENT && !is_keyword(text) => text.to_string(),
        _ => return None,
    };
    // [1] must be a parameter `(...)` group.
    match &els[1] {
        El::Grp(g) if g.kind == cst::PAREN => {}
        _ => return None,
    }
    // Between the param group and a top-level `=`, allow only signature tokens.
    let mut j = 2;
    while j < els.len() {
        match &els[j] {
            El::Tok { text, .. } if *text == "=" => return Some(name),
            El::Tok { text, .. } if matches!(*text, "::" | "where" | "." | "<:") => {
                j += 1;
            }
            El::Tok { kind, text } if *kind == tk::IDENT && !is_keyword(text) => {
                j += 1;
            }
            El::Grp(g) if matches!(g.kind, cst::BRACE | cst::PAREN) => {
                j += 1;
            }
            _ => return None,
        }
    }
    None
}

/// `using`/`import` roots: each comma-separated clause's first module segment,
/// whether it is relative (leading `.`), and the full clause text. Handles
/// `using A, B`, `import A.B`, `using A: x, y` (one root `A`).
fn import_roots(item: &Node, src: &str) -> Vec<(String, bool, String)> {
    let els = significant_children(item, src);
    let mut out: Vec<(String, bool, String)> = Vec::new();
    // Split on top-level `,` (not inside the `: a, b` selector — but we stop a
    // clause at the first `:` anyway, so `,` after `:` just starts new selectors
    // we ignore for root purposes).
    let mut clauses: Vec<Vec<&El>> = vec![Vec::new()];
    let mut after_colon = false;
    for e in &els {
        match e {
            El::Tok { text, .. } if *text == "using" || *text == "import" => {}
            El::Tok { text, .. } if *text == ":" => after_colon = true,
            El::Tok { text, .. } if *text == "," && !after_colon => {
                clauses.push(Vec::new());
            }
            El::Tok { text, .. } if *text == "," && after_colon => {}
            _ if !after_colon => clauses.last_mut().unwrap().push(e),
            _ => {}
        }
    }
    for clause in clauses {
        let mut relative = false;
        let mut root = String::new();
        let mut text = String::new();
        for &e in &clause {
            if let El::Tok { text: t, kind } = e {
                text.push_str(t);
                if *t == "." {
                    if root.is_empty() {
                        relative = true;
                    }
                } else if *kind == tk::IDENT && root.is_empty() && !is_keyword(t) {
                    root = t.to_string();
                }
            }
        }
        if !root.is_empty() {
            out.push((root, relative, text));
        }
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
/// `skip_first` ignores a leading `name(...)` (a short-form definition's own
/// signature). Recurses into groups and nested non-`Function` nodes; nested
/// `Function` nodes are scanned as their own pending functions.
fn scan_calls(node: &Node, src: &str, skip_first: bool, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    let mut skipped = !skip_first;
    while i < n {
        if el_is_ident(&els[i]) {
            let text = el_tok_text(&els[i]).unwrap_or("");
            let prev = if i > 0 {
                el_tok_text(&els[i - 1])
            } else {
                None
            };
            // Not a call if preceded by `.` (handled as part of a qualified path
            // starting at the path head) or `@`-adjacent macro; keywords excluded.
            if prev != Some(".") && !is_keyword(text) {
                // Gather a `name (. name)*` path.
                let mut segs = vec![text.to_string()];
                let mut j = i;
                while j + 2 < n && el_tok_text(&els[j + 1]) == Some(".") && el_is_ident(&els[j + 2])
                {
                    segs.push(el_tok_text(&els[j + 2]).unwrap_or("").to_string());
                    j += 2;
                }
                if j + 1 < n {
                    if let El::Grp(g) = &els[j + 1] {
                        if g.kind == cst::PAREN {
                            if !skipped {
                                // This is the definition's own signature.
                                skipped = true;
                            } else {
                                let name = segs.pop().unwrap();
                                out.push(Call { name, path: segs });
                            }
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
            if g.kind != cst::FUNCTION && g.kind != cst::MACRO_DEF {
                scan_calls(g, src, false, out);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::julia::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("mod.jl", src);
        let file = SourceFile {
            rel_path: "mod.jl".to_string(),
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
    fn emits_function_and_type_nodes() {
        let g = graph_for(
            "abstract type Shape end\nstruct Circle <: Shape\n  r::Float64\nend\nfunction area(c)\nend\n",
        );
        assert!(g.count_nodes_of(ont::FUNCTION) >= 1, "area");
        assert!(g.count_nodes_of(ont::TYPE) >= 2, "Shape + Circle");
    }

    #[test]
    fn struct_supertype_is_extends() {
        let g = graph_for("abstract type Shape end\nstruct Circle <: Shape\nend\n");
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an EXTENDS edge");
        assert!(ext.to.starts_with("type::"), "resolves to the Shape type");
    }

    #[test]
    fn short_form_function_is_detected() {
        let g = graph_for("scale(c, k) = c * k\n");
        assert!(
            g.nodes()
                .any(|n| n.kind == ont::FUNCTION && n.name == "scale"),
            "short-form def should be a Function"
        );
    }

    #[test]
    fn resolves_unique_local_call() {
        let g = graph_for(
            "function add(a, b)\n  return a + b\nend\nfunction run()\n  add(1, 2)\nend\n",
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
    fn unknown_call_is_external() {
        let g = graph_for("function run()\n  mystery()\nend\n");
        let calls = call_edges(&g);
        assert_eq!(calls.len(), 1);
        assert_eq!(
            calls[0].props.get("resolution"),
            Some(&Json::str("external"))
        );
        assert!(g.has_node("unresolved::mystery"));
    }

    #[test]
    fn short_form_body_call_not_self_call() {
        // The `f(...)` signature must not be read as a call to f.
        let g = graph_for("f(x) = g(x)\nfunction g(x)\nend\n");
        let calls = call_edges(&g);
        assert!(
            calls
                .iter()
                .all(|e| e.props.get("callee") != Some(&Json::str("f"))),
            "definition signature should not be a self-call"
        );
        assert!(
            calls
                .iter()
                .any(|e| e.props.get("callee") == Some(&Json::str("g"))),
            "the body call to g should be detected"
        );
    }

    #[test]
    fn using_creates_dependency() {
        let g = graph_for("using LinearAlgebra\nimport Base: show\n");
        assert!(g.has_node("ext::LinearAlgebra"));
        assert!(g.has_node("ext::Base"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::LinearAlgebra"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn macro_def_is_macro_node() {
        let g = graph_for("macro sayhello(name)\n  return :(println($name))\nend\n");
        assert!(
            g.nodes()
                .any(|n| n.kind == ont::MACRO && n.name == "sayhello"),
            "macro definition should be a Macro node"
        );
    }

    #[test]
    fn const_is_constant() {
        let g = graph_for("const PI = 3.14159\n");
        assert!(g.nodes().any(|n| n.kind == ont::CONSTANT && n.name == "PI"));
    }

    #[test]
    fn signature_type_annotation_is_uses_type() {
        let g = graph_for("struct Circle\nend\nfunction area(c::Circle)\nend\n");
        assert!(
            g.edges().any(|e| e.kind == edge::USES_TYPE),
            "::Circle annotation should yield a USES_TYPE edge"
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src = "struct P\nend\nfunction run()\n  helper()\nend\nhelper() = 1\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
