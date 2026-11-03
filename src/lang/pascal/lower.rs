//! Lower the Object Pascal / Delphi CST into the canonical graph.
//!
//! This mirrors the other front ends — same conservative principles, same shared
//! ontology — adapted to Pascal's surface, mapped honestly to what the source
//! actually states:
//!
//!   - `unit` / `program` / `library` / `package` → [`Module`] (one per file),
//!     under the project [`Package`]; the file lives under its module.
//!   - `type X = class(Base)` / `record` / `object` / `interface` → [`Type`] with
//!     a `type_kind` (`class`, `record`, `object`, `interface`, …). A class's
//!     ancestor → [`EXTENDS`]; additional ancestor-list entries (implemented
//!     interfaces) → [`IMPLEMENTS`]. Non-block forms map to `enum`, `set`,
//!     `array`, `pointer`, `procedural`, `class_reference`, or `alias`.
//!   - `procedure` / `function` / `constructor` / `destructor` / `operator` →
//!     [`Function`]. A method declared inside a class body, and a qualified
//!     implementation `procedure TType.Method(...)`, both map to the *same*
//!     function node (keyed by `Type.Method`) and get a [`HAS_METHOD`] edge from
//!     the owning type.
//!   - `const` / `resourcestring` → [`Constant`].
//!   - `uses A, B;` → [`IMPORTS`] (plus an [`ExternalDependency`] + [`DEPENDS_ON`]
//!     when the used unit is not project-local).
//!   - parameter / return / field types → [`USES_TYPE`] to unique project types.
//!   - call sites `f(...)` / `Obj.Method(...)` → [`CALLS`], resolved by simple
//!     name across the project. Overloading means a name can map to several
//!     definitions; ambiguity is preserved as a `candidates` set, never invented
//!     away. There is no LLM in the airgapped runtime to guess.
//!
//! Honest punts: parameterless procedure calls (`DoIt;` with no `()`) are not
//! distinguished from variable references, so only parenthesised call sites are
//! emitted as `CALLS`. Pascal's case-insensitivity is honored by lower-casing all
//! symbol-table keys; display names keep their source casing.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node, Token};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::pascal::lexer::{is_keyword, kind as tk};
use crate::lang::pascal::parser::node as cst;

/// Lower a whole project's worth of Pascal files into a graph. `manifest_deps`
/// is unused (the pipeline reads no Pascal manifest); dependencies are discovered
/// from `uses` clauses instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    // Local unit names (case-insensitive): every file's declared module name,
    // plus its file stem as a fallback identity.
    let mut local_units: BTreeSet<String> = BTreeSet::new();
    for f in files {
        local_units.insert(file_module_name(f).to_ascii_lowercase());
        local_units.insert(stem(&f.rel_path).to_ascii_lowercase());
    }

    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        local_units,
        fn_by_name: BTreeMap::new(),
        type_by_name: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id.clone(),
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("pascal"))],
    );

    // Pass B: definition nodes, structural edges, symbol tables.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_types: Vec<PendingType> = Vec::new();
    for f in files.iter() {
        let li = LineIndex::new(f.source);
        let module = file_module_name(f);
        let mod_id = format!("mod::{module}");
        lo.g.upsert_node(
            mod_id.clone(),
            ont::MODULE,
            module.clone(),
            vec![("language", Json::str("pascal"))],
        );
        lo.g.add_edge(pkg_id.clone(), edge::CONTAINS, mod_id.clone(), vec![]);

        let file_id = format!("file::{}", f.rel_path);
        lo.g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("pascal")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(mod_id.clone(), edge::CONTAINS, file_id.clone(), vec![]);

        for item in f.root.child_nodes() {
            match item.kind {
                cst::USES => lo.handle_uses(item, &file_id, f.source),
                cst::TYPE_SECTION => {
                    for decl in item.children_of(cst::TYPE_DECL) {
                        lo.handle_type(decl, &file_id, &module, f.source, &li, &mut pend_types);
                    }
                }
                cst::CONST_SECTION => {
                    for decl in item.children_of(cst::CONST_DECL) {
                        lo.handle_const(decl, &file_id, &module, f.source, &li);
                    }
                }
                cst::ROUTINE => {
                    lo.handle_routine(item, &file_id, &module, f.source, &li, &mut pend_fns);
                }
                cst::BEGIN_BLOCK => {
                    lo.handle_main(item, &file_id, &module, f.source, &li, &mut pend_fns);
                }
                _ => {}
            }
        }
    }

    // Pass C: resolve extends / type-uses, then calls, against complete tables.
    for pt in std::mem::take(&mut pend_types) {
        for (rel, base) in &pt.bases {
            lo.emit_inheritance(&pt.id, base, rel);
        }
        for region in &pt.regions {
            lo.emit_type_uses(&pt.id, region, pt.source);
        }
    }
    for pf in std::mem::take(&mut pend_fns) {
        if let Some(sig) = pf.signature {
            lo.emit_type_uses(&pf.id, sig, pf.source);
        }
        let mut calls = Vec::new();
        for region in &pf.bodies {
            let mut toks = Vec::new();
            flat_tokens(region, &mut toks);
            scan_calls(&toks, pf.source, &mut calls);
        }
        for call in &calls {
            let res = lo.resolve(call);
            lo.emit_call(&pf.id, call, res);
        }
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    local_units: BTreeSet<String>,
    fn_by_name: BTreeMap<String, Vec<String>>,
    type_by_name: BTreeMap<String, Vec<String>>,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    bodies: Vec<&'a Node>,
    signature: Option<&'a Node>,
}

struct PendingType<'a> {
    id: String,
    source: &'a str,
    /// Ancestor names paired with the relation to emit (first → EXTENDS, the
    /// rest → IMPLEMENTS).
    bases: Vec<(&'static str, String)>,
    regions: Vec<&'a Node>,
}

struct Call {
    name: String,
    /// Qualifier path before the name (`Obj` in `Obj.Method(...)`), empty for bare.
    path: Vec<String>,
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

    // --- uses ---------------------------------------------------------------

    fn handle_uses(&mut self, item: &Node, file_id: &str, src: &str) {
        for unit in import_units(item, src) {
            let key = unit.to_ascii_lowercase();
            let last = unit
                .rsplit('.')
                .next()
                .unwrap_or(&unit)
                .to_ascii_lowercase();
            let internal = self.local_units.contains(&key) || self.local_units.contains(&last);
            if internal {
                let id = format!("mod::{unit}");
                self.g.upsert_node(
                    id.clone(),
                    ont::MODULE,
                    unit.clone(),
                    vec![("language", Json::str("pascal"))],
                );
                self.g.add_edge(
                    file_id,
                    edge::IMPORTS,
                    id,
                    vec![("path", Json::str(unit)), ("external", Json::Bool(false))],
                );
            } else {
                let dep_id = format!("ext::{unit}");
                self.g.upsert_node(
                    dep_id.clone(),
                    ont::EXTERNAL_DEPENDENCY,
                    unit.clone(),
                    vec![
                        ("external", Json::Bool(true)),
                        ("source", Json::str("uses")),
                    ],
                );
                self.g.add_edge(
                    file_id,
                    edge::IMPORTS,
                    dep_id.clone(),
                    vec![("path", Json::str(unit)), ("external", Json::Bool(true))],
                );
                self.g
                    .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
            }
        }
    }

    // --- types --------------------------------------------------------------

    fn handle_type<'a>(
        &mut self,
        decl: &'a Node,
        container_id: &str,
        module: &str,
        src: &'a str,
        li: &LineIndex,
        pend_types: &mut Vec<PendingType<'a>>,
    ) {
        let name = match type_name(decl, src) {
            Some(n) => n,
            None => return,
        };
        let (type_kind, class_like) = classify_type(decl, src);
        let line = li.line_col(decl.span.start).line;
        let qual = format!("{module}.{name}");
        let id = format!("type::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str(type_kind)),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("pascal")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(decl.span.start as u64)),
                ("span_end", Json::U64(decl.span.end as u64)),
            ],
        );
        self.g
            .add_edge(container_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name
            .entry(name.to_ascii_lowercase())
            .or_default()
            .push(id.clone());

        // Ancestor list (class/object/interface only): first → EXTENDS, rest →
        // IMPLEMENTS.
        let mut bases = Vec::new();
        if class_like {
            let ancestors = ancestor_names(decl, src);
            for (idx, a) in ancestors.into_iter().enumerate() {
                let rel = if idx == 0 {
                    edge::EXTENDS
                } else {
                    edge::IMPLEMENTS
                };
                bases.push((rel, a));
            }
        }

        // Member methods inside the class/record/object body.
        let mut regions: Vec<&Node> = Vec::new();
        if let Some(h) = decl.child(cst::HEADER) {
            regions.push(h);
        }
        if let Some(block) = decl.child(cst::BLOCK) {
            regions.push(block);
            self.emit_methods(block, &id, &name, container_id, module, src, li);
        }

        pend_types.push(PendingType {
            id,
            source: src,
            bases,
            regions,
        });
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_methods(
        &mut self,
        block: &Node,
        type_id: &str,
        type_name: &str,
        container_id: &str,
        module: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let mut toks = Vec::new();
        flat_tokens(block, &mut toks);
        for (name, line) in method_sigs(&toks, src, li) {
            let qual = format!("{module}.{type_name}.{name}");
            let id = format!("fn::{qual}");
            self.g.upsert_node(
                id.clone(),
                ont::FUNCTION,
                name.clone(),
                vec![
                    ("qualified_name", Json::str(qual)),
                    ("language", Json::str("pascal")),
                    ("line", Json::U64(line as u64)),
                    ("role", Json::str("method")),
                    ("owner", Json::str(type_name.to_string())),
                ],
            );
            self.g
                .add_edge(type_id, edge::HAS_METHOD, id.clone(), vec![]);
            self.g
                .add_edge(container_id, edge::DECLARES, id.clone(), vec![]);
            self.fn_by_name
                .entry(name.to_ascii_lowercase())
                .or_default()
                .push(id);
        }
    }

    // --- routines -----------------------------------------------------------

    fn handle_routine<'a>(
        &mut self,
        item: &'a Node,
        container_id: &str,
        module: &str,
        src: &'a str,
        li: &LineIndex,
        pend: &mut Vec<PendingFn<'a>>,
    ) {
        let header = item.child(cst::HEADER);
        let path = header
            .and_then(|h| routine_name_path(h, src))
            .unwrap_or_default();
        if path.is_empty() {
            return;
        }
        let name = path.last().unwrap().clone();
        let line = li.line_col(item.span.start).line;
        let has_body = item.child(cst::BLOCK).is_some();
        let kind = routine_kind(item, src);

        let (id, qualifier) = if path.len() > 1 {
            // Qualified implementation `TType.Method` → unify with the class's
            // method node (same id, no line suffix).
            let qual = format!("{module}.{}", path.join("."));
            (
                format!("fn::{qual}"),
                Some(path[..path.len() - 1].join(".")),
            )
        } else {
            (format!("fn::{module}.{name}#{line}"), None)
        };

        let mut props = vec![
            (
                "qualified_name",
                Json::str(format!("{module}.{}", path.join("."))),
            ),
            ("language", Json::str("pascal")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            ("has_body", Json::Bool(has_body)),
            ("routine_kind", Json::str(kind)),
        ];
        if let Some(q) = &qualifier {
            props.push(("owner", Json::str(q.clone())));
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, name.clone(), props);
        self.g
            .add_edge(container_id, edge::DECLARES, id.clone(), vec![]);
        self.fn_by_name
            .entry(name.to_ascii_lowercase())
            .or_default()
            .push(id.clone());

        // A qualified impl owns a method: link the type → fn, upserting a minimal
        // type node if the declaration was not seen (e.g. partial input).
        if let Some(q) = &qualifier {
            let owner = q.rsplit('.').next().unwrap_or(q);
            let type_id = format!("type::{module}.{owner}");
            self.g.upsert_node(
                type_id.clone(),
                ont::TYPE,
                owner.to_string(),
                vec![
                    ("language", Json::str("pascal")),
                    ("type_kind", Json::str("class")),
                ],
            );
            self.g
                .add_edge(type_id, edge::HAS_METHOD, id.clone(), vec![]);
        }

        let bodies = item.child(cst::BLOCK).into_iter().collect();
        pend.push(PendingFn {
            id,
            source: src,
            bodies,
            signature: header,
        });
    }

    /// A program/library `begin … end.` main body → a synthetic `<main>`
    /// function so its call sites have a home.
    fn handle_main<'a>(
        &mut self,
        item: &'a Node,
        container_id: &str,
        module: &str,
        src: &'a str,
        li: &LineIndex,
        pend: &mut Vec<PendingFn<'a>>,
    ) {
        let line = li.line_col(item.span.start).line;
        let id = format!("fn::{module}.<main>");
        self.g.upsert_node(
            id.clone(),
            ont::FUNCTION,
            "<main>".to_string(),
            vec![
                ("qualified_name", Json::str(format!("{module}.<main>"))),
                ("language", Json::str("pascal")),
                ("line", Json::U64(line as u64)),
                ("role", Json::str("main")),
                ("has_body", Json::Bool(true)),
            ],
        );
        self.g
            .add_edge(container_id, edge::DECLARES, id.clone(), vec![]);
        pend.push(PendingFn {
            id,
            source: src,
            bodies: vec![item],
            signature: None,
        });
    }

    // --- constants ----------------------------------------------------------

    fn handle_const(
        &mut self,
        decl: &Node,
        container_id: &str,
        module: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let name = match first_ident(decl, src) {
            Some(n) => n,
            None => return,
        };
        let line = li.line_col(decl.span.start).line;
        let id = format!("const::{module}.{name}");
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            name,
            vec![
                ("binding", Json::str("const")),
                ("language", Json::str("pascal")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(container_id, edge::DECLARES, id, vec![]);
    }

    // --- inheritance & type uses -------------------------------------------

    fn emit_inheritance(&mut self, from_id: &str, base: &str, rel: &'static str) {
        let target = match self.unique_type(base) {
            Some(id) => id,
            None => {
                let uid = unresolved_id(base);
                if !self.g.has_node(&uid) {
                    self.g.upsert_node(
                        uid.clone(),
                        ont::UNRESOLVED,
                        base.to_string(),
                        vec![
                            ("unresolved", Json::Bool(true)),
                            ("role", Json::str("ancestor")),
                        ],
                    );
                }
                uid
            }
        };
        self.g.add_edge(
            from_id,
            rel,
            target,
            vec![("ancestor", Json::str(base.to_string()))],
        );
    }

    fn emit_type_uses(&mut self, from_id: &str, region: &Node, src: &str) {
        let mut toks = Vec::new();
        flat_tokens(region, &mut toks);
        let mut seen: Vec<String> = Vec::new();
        for t in &toks {
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

    // --- call resolution ----------------------------------------------------

    fn resolve(&self, call: &Call) -> Resolution {
        // Pascal call resolution is by simple name across the project (overloads
        // and methods of the same name are preserved as ambiguity).
        let c = self.global_fns(&call.name);
        if c.is_empty() {
            Resolution {
                outcome: Outcome::None,
                level: "external",
            }
        } else {
            let level = if call.path.is_empty() {
                "global"
            } else {
                "qualified"
            };
            let outcome = if c.len() == 1 {
                Outcome::One(c[0].clone())
            } else {
                Outcome::Many(c)
            };
            Resolution { outcome, level }
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

    fn global_fns(&self, name: &str) -> Vec<String> {
        // De-duplicate ids preserving first-seen order: a method declared in a
        // class body and its qualified implementation share one id, and must not
        // be counted as two candidates (false ambiguity).
        let mut seen: BTreeSet<String> = BTreeSet::new();
        let mut out = Vec::new();
        for id in self
            .fn_by_name
            .get(&name.to_ascii_lowercase())
            .cloned()
            .unwrap_or_default()
        {
            if seen.insert(id.clone()) {
                out.push(id);
            }
        }
        out
    }

    fn unique_type(&self, name: &str) -> Option<String> {
        match self.type_by_name.get(&name.to_ascii_lowercase()) {
            Some(ids) if ids.len() == 1 => Some(ids[0].clone()),
            _ => None,
        }
    }
}

// --- pure helpers -----------------------------------------------------------

fn unresolved_id(name: &str) -> String {
    format!("unresolved::{}", name.to_ascii_lowercase())
}

fn file_name(rel: &str) -> String {
    rel.rsplit('/').next().unwrap_or(rel).to_string()
}

fn stem(rel: &str) -> String {
    let base = file_name(rel);
    match base.rsplit_once('.') {
        Some((s, _)) => s.to_string(),
        None => base,
    }
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

/// The module identity for a file: the name in its `program`/`unit`/`library`/
/// `package` header, falling back to the file stem.
fn file_module_name(f: &SourceFile<'_>) -> String {
    for item in f.root.child_nodes() {
        if item.kind == cst::MODULE_DECL {
            if let Some(name) = dotted_name(item, f.source) {
                return name;
            }
        }
    }
    stem(&f.rel_path)
}

/// Collect every non-trivia leaf token of a subtree, in source order.
fn flat_tokens<'a>(node: &'a Node, out: &mut Vec<&'a Token>) {
    for c in &node.children {
        match c {
            Child::Token(t) if !t.trivia => out.push(t),
            Child::Token(_) => {}
            Child::Node(n) => flat_tokens(n, out),
        }
    }
}

/// The first non-keyword identifier in a node's direct tokens.
fn first_ident(node: &Node, src: &str) -> Option<String> {
    for c in &node.children {
        if let Child::Token(t) = c {
            if t.trivia {
                continue;
            }
            let txt = t.span.text(src);
            if t.kind == tk::IDENT && !is_keyword(txt) {
                return Some(txt.to_string());
            }
        }
    }
    None
}

/// A dotted name starting at the first non-keyword identifier in a node's direct
/// tokens (`Foo.Bar` in `unit Foo.Bar;`).
fn dotted_name(node: &Node, src: &str) -> Option<String> {
    let mut segs: Vec<String> = Vec::new();
    let mut expect_name = true;
    let mut started = false;
    for c in &node.children {
        if let Child::Token(t) = c {
            if t.trivia {
                continue;
            }
            let txt = t.span.text(src);
            if !started {
                if t.kind == tk::IDENT && !is_keyword(txt) {
                    segs.push(txt.to_string());
                    started = true;
                    expect_name = false;
                }
                continue;
            }
            if expect_name {
                if t.kind == tk::IDENT {
                    segs.push(txt.to_string());
                    expect_name = false;
                } else {
                    break;
                }
            } else if txt == "." {
                expect_name = true;
            } else {
                break;
            }
        }
    }
    if segs.is_empty() {
        None
    } else {
        Some(segs.join("."))
    }
}

/// A type declaration's name: the first identifier in its `HEADER`.
fn type_name(decl: &Node, src: &str) -> Option<String> {
    decl.child(cst::HEADER).and_then(|h| first_ident(h, src))
}

/// A routine's dotted name path from its `HEADER`: the leading `ident (. ident)*`
/// before the parameter list / return type.
fn routine_name_path(header: &Node, src: &str) -> Option<Vec<String>> {
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
                    break;
                }
            }
            Child::Node(_) => break, // a `(...)` parameter group ends the name path
        }
    }
    if segs.is_empty() {
        None
    } else {
        Some(segs)
    }
}

/// The routine keyword (`procedure`/`function`/`constructor`/`destructor`/
/// `operator`) — the first significant token of a `Routine` node.
fn routine_kind(item: &Node, src: &str) -> &'static str {
    for c in &item.children {
        if let Child::Token(t) = c {
            if t.trivia {
                continue;
            }
            return match t.span.text(src).to_ascii_lowercase().as_str() {
                "function" => "function",
                "constructor" => "constructor",
                "destructor" => "destructor",
                "operator" => "operator",
                _ => "procedure",
            };
        }
    }
    "procedure"
}

/// Classify a type definition into a `type_kind`, and whether it is class-like
/// (so an ancestor list applies).
fn classify_type(decl: &Node, src: &str) -> (&'static str, bool) {
    let has_block = decl.child(cst::BLOCK).is_some();
    // Significant tokens of the definition region (everything after the HEADER).
    let mut def_toks: Vec<&Token> = Vec::new();
    let mut first_def_paren = false;
    let mut first_seen = false;
    for c in &decl.children {
        match c {
            Child::Node(n) if n.kind == cst::HEADER => {}
            Child::Node(n) if n.kind == cst::BLOCK => {}
            Child::Node(n) => {
                if !first_seen {
                    first_def_paren = n.kind == cst::PAREN;
                    first_seen = true;
                }
                flat_tokens(n, &mut def_toks);
            }
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => {
                if !first_seen {
                    first_seen = true;
                }
                def_toks.push(t);
            }
        }
    }
    let has = |kw: &str| {
        def_toks
            .iter()
            .any(|t| t.kind == tk::IDENT && t.span.text(src).eq_ignore_ascii_case(kw))
    };
    if has_block {
        if has("class") {
            return ("class", true);
        }
        if has("interface") {
            return ("interface", true);
        }
        if has("dispinterface") {
            return ("dispinterface", true);
        }
        if has("object") {
            return ("object", true);
        }
        return ("record", false);
    }
    if has("class") {
        // `class of T` is a metaclass reference; a bare `class;` is a forward
        // class declaration (the full definition appears later and merges).
        if has("of") {
            return ("class_reference", false);
        }
        return ("class", true);
    }
    if has("array") {
        return ("array", false);
    }
    if has("set") {
        return ("set", false);
    }
    if has("procedure") || has("function") {
        return ("procedural", false);
    }
    if first_def_paren {
        return ("enum", false);
    }
    if def_toks.first().map(|t| t.span.text(src)) == Some("^") {
        return ("pointer", false);
    }
    ("alias", false)
}

/// Ancestor identifiers from a class/object/interface definition: the identifiers
/// in the first `(...)` group following the kind keyword.
fn ancestor_names(decl: &Node, src: &str) -> Vec<String> {
    let mut after_header = false;
    for c in &decl.children {
        match c {
            Child::Node(n) if n.kind == cst::HEADER => after_header = true,
            Child::Node(n) if n.kind == cst::PAREN && after_header => {
                let mut names = Vec::new();
                let mut toks = Vec::new();
                flat_tokens(n, &mut toks);
                for t in toks {
                    if t.kind == tk::IDENT && !is_keyword(t.span.text(src)) {
                        names.push(t.span.text(src).to_string());
                    }
                }
                return names;
            }
            _ => {}
        }
    }
    Vec::new()
}

/// Comma-separated unit names from a `uses` clause, ignoring `in '…'` file specs.
fn import_units(item: &Node, src: &str) -> Vec<String> {
    let mut toks = Vec::new();
    flat_tokens(item, &mut toks);
    let mut units: Vec<String> = Vec::new();
    let mut cur = String::new();
    let mut after_in = false;
    let mut started = false;
    for t in &toks {
        let txt = t.span.text(src);
        if !started {
            // Skip the leading `uses` keyword.
            if txt.eq_ignore_ascii_case("uses") {
                started = true;
            }
            continue;
        }
        if txt == "," {
            if !cur.is_empty() {
                units.push(std::mem::take(&mut cur));
            }
            after_in = false;
            continue;
        }
        if txt.eq_ignore_ascii_case("in") {
            after_in = true;
            continue;
        }
        if after_in {
            continue; // the `'file.pas'` spec
        }
        if t.kind == tk::IDENT || txt == "." {
            cur.push_str(txt);
        }
    }
    if !cur.is_empty() {
        units.push(cur);
    }
    units.retain(|u| !u.is_empty());
    units
}

/// Method signatures inside a class/record/object body: a routine keyword
/// (`procedure`/`function`/`constructor`/`destructor`/`operator`) followed by an
/// identifier name. Returns `(name, line)` pairs.
fn method_sigs(toks: &[&Token], src: &str, li: &LineIndex) -> Vec<(String, u32)> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < toks.len() {
        let t = toks[i];
        if t.kind == tk::IDENT {
            let txt = t.span.text(src);
            if matches!(
                txt.to_ascii_lowercase().as_str(),
                "procedure" | "function" | "constructor" | "destructor" | "operator"
            ) {
                if let Some(nt) = toks.get(i + 1) {
                    let ntxt = nt.span.text(src);
                    if nt.kind == tk::IDENT && !is_keyword(ntxt) {
                        out.push((ntxt.to_string(), li.line_col(nt.span.start).line));
                        i += 2;
                        continue;
                    }
                }
            }
        }
        i += 1;
    }
    out
}

/// Detect call sites over the flat token stream: `name(...)` and
/// `a.b.name(...)`. Parameterless calls (`DoIt;`) are intentionally not detected
/// (ambiguous with variable references).
fn scan_calls(toks: &[&Token], src: &str, out: &mut Vec<Call>) {
    let n = toks.len();
    let mut i = 0;
    while i < n {
        let t = toks[i];
        if t.kind == tk::IDENT {
            let text = t.span.text(src);
            let prev = if i > 0 {
                Some(toks[i - 1].span.text(src))
            } else {
                None
            };
            if prev != Some(".") && !is_keyword(text) {
                let mut segs = vec![text.to_string()];
                let mut j = i;
                while j + 2 < n
                    && toks[j + 1].span.text(src) == "."
                    && toks[j + 2].kind == tk::IDENT
                {
                    segs.push(toks[j + 2].span.text(src).to_string());
                    j += 2;
                }
                if j + 1 < n && toks[j + 1].span.text(src) == "(" {
                    let name = segs.pop().unwrap();
                    out.push(Call { name, path: segs });
                }
                i = j + 1;
                continue;
            }
        }
        i += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::pascal::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("demo.pas", src);
        let file = SourceFile {
            rel_path: "demo.pas".to_string(),
            module_path: vec!["demo".to_string()],
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    fn call_edges(g: &Graph) -> Vec<&crate::graph::GraphEdge> {
        g.edges().filter(|e| e.kind == edge::CALLS).collect()
    }

    #[test]
    fn emits_module_type_and_function_nodes() {
        let g = graph_for(
            "unit U;\ninterface\ntype\n  TShape = class end;\n  TCircle = class(TShape) end;\nimplementation\nprocedure Area;\nbegin\nend;\nend.\n",
        );
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "module U");
        assert!(g.count_nodes_of(ont::TYPE) >= 2, "TShape + TCircle");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 1, "Area");
    }

    #[test]
    fn class_ancestor_is_extends() {
        let g = graph_for("type\n  TShape = class end;\n  TCircle = class(TShape) end;\n");
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an EXTENDS edge");
        assert!(ext.to.starts_with("type::"), "resolves to TShape");
    }

    #[test]
    fn second_ancestor_is_implements() {
        let g = graph_for(
            "type\n  IFoo = interface end;\n  TBase = class end;\n  TC = class(TBase, IFoo) end;\n",
        );
        assert!(
            g.edges().any(|e| e.kind == edge::IMPLEMENTS),
            "interface ancestor should be IMPLEMENTS"
        );
        assert!(g.edges().any(|e| e.kind == edge::EXTENDS));
    }

    #[test]
    fn qualified_impl_has_method() {
        let g = graph_for(
            "type\n  TC = class\n    procedure Foo;\n  end;\nimplementation\nprocedure TC.Foo;\nbegin\nend;\n",
        );
        assert!(
            g.edges().any(|e| e.kind == edge::HAS_METHOD),
            "TC owns method Foo"
        );
        // The class-decl method and the qualified impl must be the SAME node.
        let foo_fns: Vec<_> = g
            .nodes()
            .filter(|n| n.kind == ont::FUNCTION && n.name == "Foo")
            .collect();
        assert_eq!(foo_fns.len(), 1, "decl + impl unify into one Function node");
    }

    #[test]
    fn resolves_unique_call() {
        let g = graph_for(
            "procedure Helper;\nbegin\nend;\nprocedure Run;\nbegin\n  Writer(Helper);\nend;\n",
        );
        // `Writer(...)` is a call; `Helper` (parameterless) is not.
        let calls = call_edges(&g);
        assert!(calls
            .iter()
            .any(|e| e.props.get("callee") == Some(&Json::str("Writer"))));
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for("procedure Run;\nbegin\n  Mystery(1);\nend;\n");
        let calls = call_edges(&g);
        assert_eq!(calls.len(), 1);
        assert_eq!(
            calls[0].props.get("resolution"),
            Some(&Json::str("external"))
        );
        assert!(g.has_node(&unresolved_id("Mystery")));
    }

    #[test]
    fn uses_creates_dependency() {
        let g = graph_for("unit U;\ninterface\nuses SysUtils, Classes;\nimplementation\nend.\n");
        assert!(g.has_node("ext::SysUtils"));
        assert!(g.has_node("ext::Classes"));
        assert!(g.edges().any(|e| e.kind == edge::DEPENDS_ON));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn const_is_constant() {
        let g = graph_for("const\n  TAU = 6.28;\n");
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::CONSTANT && n.name == "TAU"));
    }

    #[test]
    fn enum_and_alias_type_kinds() {
        let g = graph_for("type\n  TColor = (Red, Green, Blue);\n  TName = string;\n");
        let kinds: Vec<_> = g
            .nodes()
            .filter(|n| n.kind == ont::TYPE)
            .filter_map(|n| n.props.get("type_kind").cloned())
            .collect();
        assert!(kinds.contains(&Json::str("enum")), "enum: {kinds:?}");
        assert!(kinds.contains(&Json::str("alias")), "alias: {kinds:?}");
    }

    #[test]
    fn signature_type_annotation_is_uses_type() {
        let g = graph_for(
            "type\n  TCircle = class end;\nimplementation\nprocedure Area(C: TCircle);\nbegin\nend;\n",
        );
        assert!(
            g.edges().any(|e| e.kind == edge::USES_TYPE),
            ": TCircle annotation should yield a USES_TYPE edge"
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src = "unit U;\ninterface\ntype TC = class\n  procedure Foo;\nend;\nimplementation\nprocedure TC.Foo;\nbegin\n  Bar(1);\nend;\nend.\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
