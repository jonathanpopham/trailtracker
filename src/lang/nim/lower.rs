//! Lower the Nim CST into the canonical graph.
//!
//! Mirrors the Python lowering ([`crate::lang::python::lower`]) — same
//! conservative principles, same shared ontology — adapted to Nim's surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to
//!    a concrete project definition only when a scope level yields exactly one
//!    candidate; several candidates are emitted as an ambiguous edge carrying the
//!    full `candidates` set; none resolves to an explicit `UnresolvedSymbol`.
//! 2. **Everything comes from real tokens.** Calls, base types, imports, and type
//!    uses are read off the lossless tree, never guessed.
//!
//! Honest mappings (see the IR Atlas):
//!   `proc`/`func`/`method`/`iterator`/`converter`/`template`/`macro` →
//!   `Function` (distinguished by a `routine_kind` property — Nim has no
//!   class-owned methods, so no `HAS_METHOD` is emitted);
//!   `type X = object|enum|tuple|…` → `Type` (`type_kind` property);
//!   `type X = object of Base` → `X EXTENDS Base`;
//!   module-level `const`/`let`/`var` → `Constant` (`binding` property);
//!   `import`/`from … import`/`include` → `IMPORTS` (plus
//!   `ExternalDependency`/`DEPENDS_ON` for non-project roots).
//!
//! **UFCS.** Nim's uniform function call syntax makes `x.f(y)` identical to
//! `f(x, y)`: both are a call to a free function named `f`. The resolver keys on
//! the *name* in both forms (dotted calls are flagged `ufcs: true`) and preserves
//! ambiguity rather than inventing a receiver type — there is no type inference in
//! the airgapped runtime.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::nim::lexer::{is_keyword, kind as tk};
use crate::lang::nim::parser::node as cst;

/// Definition-introducing keywords — a following name is a declaration, not a call.
const ROUTINE_KW: &[&str] = &[
    "proc",
    "func",
    "method",
    "iterator",
    "converter",
    "template",
    "macro",
];

/// Lower a whole project's worth of Nim files into a graph. `manifest_deps` is
/// unused (the pipeline's manifest reader is Cargo-only); dependencies are
/// discovered from `import` statements instead.
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
        imports: Vec::new(),
        cur_file: 0,
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("nim"))],
    );

    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_extends: Vec<PendingExtends> = Vec::new();
    for (idx, f) in files.iter().enumerate() {
        lo.imports.push(BTreeMap::new());
        lo.cur_file = idx;
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
                ("language", Json::str("nim")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(leaf, edge::CONTAINS, file_id.clone(), vec![]);
        lo.walk_module(
            f.root,
            &file_id,
            &module_join,
            f.source,
            &li,
            &mut pend_fns,
            &mut pend_extends,
        );
    }

    // Pass C: resolve calls, type usages, and inheritance against the now-complete
    // symbol tables.
    for pf in &pend_fns {
        let ctx = Ctx {
            module_join: pf.module_join.clone(),
            imports: lo.imports.get(pf.file_idx).cloned().unwrap_or_default(),
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
    for pe in &pend_extends {
        lo.emit_extends(pe);
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    local_roots: BTreeSet<String>,
    /// Simple name → all function node ids (global level).
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// (module_join, name) → function ids (local-module level).
    fn_by_module: BTreeMap<(String, String), Vec<String>>,
    /// Simple name → type node ids.
    type_by_name: BTreeMap<String, Vec<String>>,
    /// Per-file import maps: imported leaf name → full path segments.
    imports: Vec<BTreeMap<String, Vec<String>>>,
    cur_file: usize,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    block: Option<&'a Node>,
    signature: Option<&'a Node>,
    module_join: String,
    file_idx: usize,
}

struct PendingExtends {
    type_id: String,
    base_name: String,
}

/// A detected call site over the lossless tree.
struct Call {
    name: String,
    /// True for dotted `recv.name(...)` (UFCS) calls.
    ufcs: bool,
}

struct Ctx {
    module_join: String,
    imports: BTreeMap<String, Vec<String>>,
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
                vec![("language", Json::str("nim"))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    /// Walk the module's top-level statements, creating definition nodes and
    /// indexing symbols. Nim definitions are module-level (bodies are captured as
    /// flat regions), so there is no nested-scope recursion here.
    #[allow(clippy::too_many_arguments)]
    fn walk_module<'a>(
        &mut self,
        module: &'a Node,
        file_id: &str,
        module_join: &str,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_extends: &mut Vec<PendingExtends>,
    ) {
        for item in module.child_nodes() {
            match item.kind {
                cst::ROUTINE => self.handle_routine(item, file_id, module_join, src, li, pend_fns),
                cst::TYPE_SECTION => {
                    for def in section_defs(item, cst::TYPE_DEF) {
                        self.handle_type_def(def, file_id, module_join, src, li, pend_extends);
                    }
                }
                cst::VAR_SECTION => {
                    let binding = section_keyword(item, src).unwrap_or("var").to_string();
                    for def in section_defs(item, cst::VAR_DEF) {
                        self.handle_var_def(def, file_id, module_join, &binding, src, li);
                    }
                }
                cst::IMPORT => self.handle_import(item, file_id, src),
                _ => {}
            }
        }
    }

    fn handle_routine<'a>(
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
        let qual = qual_name(module_join, &name);
        let id = format!("fn::{qual}#{line}");
        let block = item.child(cst::BLOCK);
        let rkind = routine_keyword(item, src).unwrap_or("proc");
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("nim")),
            ("routine_kind", Json::str(rkind.to_string())),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            ("has_body", Json::Bool(block.is_some())),
        ];
        if is_exported(item, src) {
            props.push(("exported", Json::Bool(true)));
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, name.clone(), props);
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);

        self.fn_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());
        self.fn_by_module
            .entry((module_join.to_string(), name))
            .or_default()
            .push(id.clone());

        pend_fns.push(PendingFn {
            id,
            source: src,
            block,
            signature: item.child(cst::HEADER),
            module_join: module_join.to_string(),
            file_idx: self.cur_file,
        });
    }

    fn handle_type_def(
        &mut self,
        item: &Node,
        file_id: &str,
        module_join: &str,
        src: &str,
        li: &LineIndex,
        pend_extends: &mut Vec<PendingExtends>,
    ) {
        let name = match name_text(item, src) {
            Some(n) => n.to_string(),
            None => return,
        };
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(module_join, &name);
        let id = format!("type::{qual}#{line}");
        let header = item.child(cst::HEADER);
        let (kind_str, is_ref, base) = match header {
            Some(h) => type_shape(h, src),
            None => ("alias", false, None),
        };
        let mut props = vec![
            ("type_kind", Json::str(kind_str.to_string())),
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("nim")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
        ];
        if is_ref {
            props.push(("is_ref", Json::Bool(true)));
        }
        if is_exported(item, src) {
            props.push(("exported", Json::Bool(true)));
        }
        self.g
            .upsert_node(id.clone(), ont::TYPE, name.clone(), props);
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name.entry(name).or_default().push(id.clone());

        if let Some(b) = base {
            pend_extends.push(PendingExtends {
                type_id: id,
                base_name: b,
            });
        }
    }

    fn handle_var_def(
        &mut self,
        item: &Node,
        file_id: &str,
        module_join: &str,
        binding: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let name = match name_text(item, src) {
            Some(n) => n.to_string(),
            None => return,
        };
        let line = li.line_col(name_span_start(item)).line;
        let id = format!("const::{}", qual_name(module_join, &name));
        let mut props = vec![
            ("binding", Json::str(binding.to_string())),
            ("language", Json::str("nim")),
            ("line", Json::U64(line as u64)),
        ];
        if is_exported(item, src) {
            props.push(("exported", Json::Bool(true)));
        }
        self.g.upsert_node(id.clone(), ont::CONSTANT, name, props);
        self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
    }

    /// `import a, b/c, d as e` / `from x import y` / `include z` / `export w`.
    fn handle_import(&mut self, item: &Node, file_id: &str, src: &str) {
        let toks = top_level_tokens(item, src);
        let kw = toks.first().map(|t| t.text).unwrap_or("");
        let body = strip_leading(&toks, kw);
        if kw == "from" {
            // `from <module> import <names>`: only the module names a dependency.
            let split = body.iter().position(|t| t.text == "import");
            let module_part = match split {
                Some(p) => &body[..p],
                None => body,
            };
            let (segs, _) = path_and_alias(module_part);
            let path_text = module_part.iter().map(|t| t.text).collect::<String>();
            self.emit_import_edge(file_id, &segs, &path_text);
            return;
        }
        // `import` / `include` / `export`: a comma-separated list of module paths.
        for clause in split_commas(body.to_vec()) {
            let (segs, alias) = path_and_alias(&clause);
            if segs.is_empty() {
                continue;
            }
            let path_text = segs.join("/");
            let leaf = alias.unwrap_or_else(|| segs.last().cloned().unwrap());
            self.imports[self.cur_file].insert(leaf, segs.clone());
            self.emit_import_edge(file_id, &segs, &path_text);
        }
    }

    fn emit_import_edge(&mut self, file_id: &str, segs: &[String], path_text: &str) {
        let root = segs.first().cloned().unwrap_or_default();
        // A leading-dot relative import (`./foo`, `../bar`) has an empty first seg.
        let relative = path_text.starts_with('.');
        if root.is_empty() && !relative {
            return;
        }
        let internal = relative || self.local_roots.contains(&root);
        if internal {
            let mod_id = if root.is_empty() {
                self.pkg_id()
            } else {
                let id = format!("mod::{root}");
                self.g.upsert_node(
                    id.clone(),
                    ont::MODULE,
                    root.clone(),
                    vec![("language", Json::str("nim"))],
                );
                id
            };
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                mod_id,
                vec![
                    ("path", Json::str(path_text.to_string())),
                    ("external", Json::Bool(false)),
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
                    ("source", Json::str("import")),
                ],
            );
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                dep_id.clone(),
                vec![
                    ("path", Json::str(path_text.to_string())),
                    ("external", Json::Bool(true)),
                ],
            );
            self.g
                .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
        }
    }

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        // Local module.
        let c = self.fns_in_module(&ctx.module_join, &call.name);
        if !c.is_empty() {
            return mk(c, "local");
        }
        // File imports: a name brought in via `from mod import name`.
        if let Some(segs) = ctx.imports.get(&call.name) {
            if let Some(modj) = self.import_module_join(segs) {
                let c = self.fns_in_module(&modj, &call.name);
                if !c.is_empty() {
                    return mk(c, "import");
                }
            }
        }
        // Global (UFCS collapses dotted and bare forms to the same name).
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
            ("ufcs", Json::Bool(call.ufcs)),
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
                            ("role", Json::str("base_type")),
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

    fn fns_in_module(&self, module_join: &str, name: &str) -> Vec<String> {
        self.fn_by_module
            .get(&(module_join.to_string(), name.to_string()))
            .cloned()
            .unwrap_or_default()
    }

    fn global_fns(&self, name: &str) -> Vec<String> {
        self.fn_by_name.get(name).cloned().unwrap_or_default()
    }

    fn import_module_join(&self, segs: &[String]) -> Option<String> {
        if segs.is_empty() {
            return None;
        }
        if self.local_roots.contains(&segs[0]) {
            Some(segs.join("."))
        } else {
            None
        }
    }

    fn unique_type(&self, name: &str) -> Option<String> {
        match self.type_by_name.get(name) {
            Some(ids) if ids.len() == 1 => Some(ids[0].clone()),
            _ => None,
        }
    }

    /// Add `USES_TYPE` edges for identifiers in a routine's `Header` (parameter
    /// and return-type region) that name a unique project type.
    fn emit_type_uses(&mut self, from_id: &str, region: &Node, src: &str) {
        let mut seen: Vec<String> = Vec::new();
        for n in region.walk() {
            for t in n.tokens() {
                if t.kind != tk::NAME {
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

/// The leading keyword of a routine node (`proc`/`func`/…), read from its first
/// non-trivia token.
fn routine_keyword<'a>(item: &'a Node, src: &'a str) -> Option<&'a str> {
    item.tokens().next().map(|t| t.span.text(src))
}

/// The leading keyword of a section node (`const`/`let`/`var`/`type`).
fn section_keyword<'a>(item: &'a Node, src: &'a str) -> Option<&'a str> {
    item.tokens().next().map(|t| t.span.text(src))
}

/// True if the definition's name carries Nim's `*` export marker (`Foo*`), which
/// appears as a `*` token immediately after the name inside the def's `Header`.
fn is_exported(item: &Node, src: &str) -> bool {
    if let Some(h) = item.child(cst::HEADER) {
        if let Some(first) = h.tokens().next() {
            return first.span.text(src) == "*";
        }
    }
    false
}

/// Determine a type definition's shape from its right-hand-side `Header`:
/// `(type_kind, is_ref, base)`. `base` is the supertype name from `object of Base`.
fn type_shape(header: &Node, src: &str) -> (&'static str, bool, Option<String>) {
    let toks: Vec<&str> = header
        .tokens()
        .filter(|t| t.kind == tk::NAME)
        .map(|t| t.span.text(src))
        .collect();
    let has = |w: &str| toks.contains(&w);
    let is_ref = has("ref") || has("ptr");
    let kind = if has("enum") {
        "enum"
    } else if has("tuple") {
        "tuple"
    } else if has("object") {
        "object"
    } else if has("concept") {
        "concept"
    } else if has("distinct") {
        "distinct"
    } else {
        "alias"
    };
    // `object of Base`: the name following a top-level `of`.
    let mut base = None;
    let mut prev_of = false;
    for t in header.tokens() {
        if prev_of && t.kind == tk::NAME {
            base = Some(t.span.text(src).to_string());
            break;
        }
        prev_of = t.span.text(src) == "of";
    }
    (kind, is_ref, base)
}

/// A flat token (text + kind), used by the small token-list helpers.
#[derive(Clone, Copy)]
struct Tok<'a> {
    text: &'a str,
    kind: &'static str,
}

/// Direct, non-trivia child tokens of `node` in source order (does not descend
/// into child nodes such as balanced groups).
fn top_level_tokens<'a>(node: &'a Node, src: &'a str) -> Vec<Tok<'a>> {
    node.tokens()
        .filter(|t| t.kind != tk::NEWLINE)
        .map(|t| Tok {
            text: t.span.text(src),
            kind: t.kind,
        })
        .collect()
}

fn strip_leading<'a, 'b>(toks: &'b [Tok<'a>], kw: &str) -> &'b [Tok<'a>] {
    match toks.split_first() {
        Some((first, rest)) if first.text == kw => rest,
        _ => toks,
    }
}

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

/// Read a module path (`a/b/c`, `a.b`) and an optional `as` alias from one import
/// clause. Path separators (`/`, `.`) are skipped; the names are the segments.
fn path_and_alias(clause: &[Tok<'_>]) -> (Vec<String>, Option<String>) {
    let mut segs = Vec::new();
    let mut alias = None;
    let mut expect_alias = false;
    for t in clause {
        if t.kind != tk::NAME {
            continue; // `/`, `.`, etc.
        }
        if expect_alias {
            alias = Some(t.text.to_string());
            expect_alias = false;
        } else if t.text == "as" {
            expect_alias = true;
        } else {
            segs.push(t.text.to_string());
        }
    }
    (segs, alias)
}

// --- type/section def access ------------------------------------------------

/// All nodes of `kind` belonging to a section: either direct children (inline
/// form) or children of the section's `Block` (indented form).
fn section_defs<'a>(section: &'a Node, kind: &str) -> Vec<&'a Node> {
    let mut v = Vec::new();
    for ch in section.child_nodes() {
        if ch.kind == kind {
            v.push(ch);
        } else if ch.kind == cst::BLOCK {
            for d in ch.child_nodes() {
                if d.kind == kind {
                    v.push(d);
                }
            }
        }
    }
    v
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
                ident: t.kind == tk::NAME,
            }),
            Child::Node(n) => v.push(El::Grp(n)),
        }
    }
    v
}

/// Detect `name(...)` and `recv.name(...)` (UFCS) call sites over the real token
/// tree, recursing into nested groups. Keywords are excluded, as is a name
/// immediately following a routine-introducing keyword (a nested declaration, not
/// a call).
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        // UFCS / member call: `.` name `(...)`.
        if tok_text(&els[i]) == Some(".") {
            if i + 2 < n && is_ident_el(&els[i + 1]) {
                if let Some(g) = grp(&els[i + 2]) {
                    if g.kind == cst::PAREN {
                        let name = tok_text(&els[i + 1]).unwrap_or("");
                        if !is_keyword(name) {
                            out.push(Call {
                                name: name.to_string(),
                                ufcs: true,
                            });
                        }
                        i += 3;
                        continue;
                    }
                }
            }
            i += 1;
            continue;
        }
        // Bare call: name `(...)`, not preceded by `.` and not a declaration name.
        if is_ident_el(&els[i]) {
            let prev = if i > 0 { tok_text(&els[i - 1]) } else { None };
            let text = tok_text(&els[i]).unwrap_or("");
            let is_def = prev.map(|p| ROUTINE_KW.contains(&p)).unwrap_or(false);
            if prev != Some(".") && !is_def && !is_keyword(text) && i + 1 < n {
                if let Some(g) = grp(&els[i + 1]) {
                    if g.kind == cst::PAREN {
                        out.push(Call {
                            name: text.to_string(),
                            ufcs: false,
                        });
                    }
                }
            }
        }
        i += 1;
    }
    // Recurse into groups (parameter lists, nested calls). Bodies are flat regions,
    // so there are no nested Routine/Type nodes to skip here.
    for e in &els {
        if let Some(g) = grp(e) {
            scan_calls(g, src, out);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::nim::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("mod.nim", src);
        let file = SourceFile {
            rel_path: "mod.nim".to_string(),
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
    fn emits_function_type_module_nodes() {
        let g = graph_for("type T = object\nproc f() =\n  discard\nproc g() =\n  discard\n");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "f + g");
        assert_eq!(g.count_nodes_of(ont::TYPE), 1, "type T is a Type");
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "module mod");
    }

    #[test]
    fn type_kind_and_ref() {
        let g = graph_for("type\n  A = object\n  B = enum\n    x\n  C = ref object\n");
        let kinds: Vec<String> = g
            .nodes()
            .filter(|n| n.kind == ont::TYPE)
            .filter_map(|n| n.props.get("type_kind"))
            .map(|j| j.to_line())
            .collect();
        assert!(kinds.iter().any(|k| k.contains("object")));
        assert!(kinds.iter().any(|k| k.contains("enum")));
        let c = g.nodes().find(|n| n.name == "C").expect("type C");
        assert_eq!(c.props.get("is_ref"), Some(&Json::Bool(true)));
    }

    #[test]
    fn resolves_unique_local_call() {
        let g = graph_for("proc add(a, b: int): int =\n  a + b\nproc run() =\n  add(1, 2)\n");
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
    fn ufcs_call_resolves_by_name() {
        // `x.f()` is UFCS sugar for `f(x)`; resolve by the name `f`.
        let g = graph_for("proc f(a: int) =\n  discard\nproc run() =\n  var x = 1\n  x.f()\n");
        let calls = call_edges(&g);
        let ufcs = calls
            .iter()
            .find(|e| e.props.get("ufcs") == Some(&Json::Bool(true)))
            .expect("a UFCS call");
        assert_eq!(ufcs.props.get("callee"), Some(&Json::str("f")));
        assert_eq!(ufcs.props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for("proc run() =\n  mystery()\n");
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
        let g = graph_for("import strutils\nfrom os import getEnv\n");
        assert!(g.has_node("ext::strutils"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::strutils"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn inheritance_emits_extends() {
        let g = graph_for("type\n  Base = object of RootObj\n  Derived = object of Base\n");
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS && e.to.starts_with("type::mod.Base"))
            .expect("Derived EXTENDS Base");
        assert!(ext.from.starts_with("type::mod.Derived"));
    }

    #[test]
    fn module_level_binding_is_constant() {
        let g = graph_for("const Version = \"1.0\"\nlet count = 3\nvar mutable = 0\n");
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 3);
        let v = g.nodes().find(|n| n.name == "Version").expect("a constant");
        assert_eq!(v.props.get("binding"), Some(&Json::str("const")));
    }

    #[test]
    fn type_use_in_signature() {
        let g = graph_for("type Widget = object\nproc build(w: Widget) =\n  discard\n");
        assert!(
            g.edges()
                .any(|e| e.kind == edge::USES_TYPE && e.to.contains("Widget")),
            "param type should create USES_TYPE"
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src = "import os\ntype T = object of RootObj\nproc m() =\n  helper()\nproc helper() =\n  discard\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
