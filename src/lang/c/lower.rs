//! Lower the C CST into the canonical graph.
//!
//! This mirrors the Rust and Python lowerings ([`crate::ir::lower`],
//! [`crate::lang::python::lower`]) — same conservative principles, same shared
//! ontology — adapted to C's surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to a
//!    concrete project definition only when a scope level yields exactly one
//!    candidate; several candidates become an ambiguous edge carrying the full
//!    `candidates` set; none resolves to an explicit `UnresolvedSymbol`.
//! 2. **Everything comes from real tokens.** Calls, includes, macro names, and
//!    type uses are read off the lossless tree, never guessed.
//!
//! Resolution uses a deterministic **scope ladder** (most specific first; the
//! first level with any candidate decides), the C analogue of the Rust/Python
//! ladders: local translation unit → global → object-like/function-like macros.
//! C has no methods or inheritance, so the ladder is shorter; member-style calls
//! (`p->f()`, `s.f()`) still resolve against the same function/macro tables, since
//! C function pointers carry no statically-known owning type in an airgap.
//!
//! Honest mappings (see the IR Atlas):
//!   function *definition* → `Function`; `struct`/`union`/`enum` definition →
//!   `Type` (`type_kind: struct|union|enum`); `typedef` → `Type`
//!   (`type_kind: typedef`); `#define` → `Macro`; a top-level object declaration
//!   (`int x = …;`) → `Constant`; `#include "x"` → `IMPORTS` (internal module);
//!   `#include <x>` → `IMPORTS` + `ExternalDependency`/`DEPENDS_ON`. Function
//!   *prototypes* are declarations, not definitions, so they create no `Function`
//!   node (mirroring how the Rust/Python front ends only emit real definitions).

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::c::lexer::{is_keyword, kind as tk};
use crate::lang::c::parser::node as cst;
use crate::lang::frontend::SourceFile;

/// Lower a whole project's worth of C files into a graph. `manifest_deps` is unused
/// for C (the pipeline's manifest reader is Cargo-only); dependencies are
/// discovered from `#include` directives instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    // Project-local roots: the package plus every module segment. A quoted include
    // whose stem is one of these is intra-project; conservative, never fabricated.
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
        fn_by_name: BTreeMap::new(),
        fn_by_module: BTreeMap::new(),
        type_by_name: BTreeMap::new(),
        macro_by_name: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("c"))],
    );

    // Pass B: create definition nodes + structural edges and build the symbol
    // tables. Call/type resolution is deferred to pass C so a callee defined later
    // in the project still resolves.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
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
                ("language", Json::str("c")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(leaf, edge::CONTAINS, file_id.clone(), vec![]);

        for item in f.root.child_nodes() {
            match item.kind {
                cst::FUNCTION => {
                    lo.handle_fn(item, &file_id, &module_join, f.source, &li, &mut pend_fns)
                }
                cst::STRUCT | cst::UNION | cst::ENUM | cst::TYPEDEF => {
                    lo.handle_type(item, &file_id, &module_join, f.source, &li)
                }
                cst::INCLUDE => lo.handle_include(item, &file_id, &local_roots, f.source),
                cst::DEFINE => lo.handle_define(item, &file_id, &module_join, f.source, &li),
                cst::DECL => lo.handle_decl_const(item, &file_id, &module_join, f.source, &li),
                _ => {}
            }
        }
    }

    // Pass C: resolve calls (scope ladder) and type usages against the complete
    // symbol tables.
    for pf in &pend_fns {
        if let Some(body) = pf.body {
            let mut calls = Vec::new();
            scan_calls(body, pf.source, &mut calls);
            for call in &calls {
                let res = lo.resolve(call, &pf.module_join);
                lo.emit_call(&pf.id, call, res);
            }
        }
        lo.emit_type_uses(&pf.id, pf.func, pf.source);
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    /// Simple name → all function-definition node ids (global level).
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// (module_join, name) → function ids (local translation-unit level).
    fn_by_module: BTreeMap<(String, String), Vec<String>>,
    /// Simple name → type (struct/union/enum/typedef) node ids.
    type_by_name: BTreeMap<String, Vec<String>>,
    /// Simple name → macro node ids.
    macro_by_name: BTreeMap<String, Vec<String>>,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    func: &'a Node,
    body: Option<&'a Node>,
    module_join: String,
}

/// A detected call site over the lossless tree.
struct Call {
    /// The called name (member name or bare name).
    name: String,
    /// True for `recv.name(...)` / `recv->name(...)` member calls.
    method: bool,
    /// Immediate receiver identifier for member calls.
    receiver: Option<String>,
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
    /// module id (or the package id for a file with no module segments).
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
                vec![("language", Json::str("c"))],
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
        pend: &mut Vec<PendingFn<'a>>,
    ) {
        let name = name_text(item, src).unwrap_or("<anonymous>").to_string();
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(module_join, &name);
        let id = format!("fn::{qual}#{line}");
        let body = item.child(cst::BRACE);
        let props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("c")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            ("has_body", Json::Bool(body.is_some())),
            ("is_static", Json::Bool(has_top_kw(item, src, "static"))),
        ];
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

        pend.push(PendingFn {
            id,
            source: src,
            func: item,
            body,
            module_join: module_join.to_string(),
        });
    }

    fn handle_type(
        &mut self,
        item: &Node,
        file_id: &str,
        module_join: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let type_kind = match item.kind {
            cst::STRUCT => "struct",
            cst::UNION => "union",
            cst::ENUM => "enum",
            cst::TYPEDEF => "typedef",
            _ => "type",
        };
        // Skip anonymous aggregates (no usable name → no stable id).
        let name = match name_text(item, src) {
            Some(n) => n.to_string(),
            None => return,
        };
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(module_join, &name);
        let id = format!("type::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str(type_kind)),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("c")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name.entry(name).or_default().push(id);
    }

    /// `#include "x.h"` (local) or `#include <x.h>` (system). The former becomes an
    /// internal `IMPORTS` to a module node; the latter an `ExternalDependency` with
    /// `DEPENDS_ON`, mirroring the Python import lowering.
    fn handle_include(
        &mut self,
        item: &Node,
        file_id: &str,
        local_roots: &BTreeSet<String>,
        src: &str,
    ) {
        // Quoted form: a single string-literal token holds the path.
        for t in item.tokens() {
            if t.kind == tk::STRING {
                let path = unquote(t.span.text(src));
                let stem = header_stem(&path);
                let internal = local_roots.contains(&stem) || !path.contains('/');
                if internal {
                    let mod_id = format!("mod::{stem}");
                    self.g.upsert_node(
                        mod_id.clone(),
                        ont::MODULE,
                        stem,
                        vec![("language", Json::str("c"))],
                    );
                    self.g.add_edge(
                        file_id,
                        edge::IMPORTS,
                        mod_id,
                        vec![("path", Json::str(path)), ("external", Json::Bool(false))],
                    );
                } else {
                    self.emit_external_include(file_id, &path);
                }
                return;
            }
        }
        // Angled form: collect the header name between `<` and `>`.
        let mut collecting = false;
        let mut parts = String::new();
        for t in item.tokens() {
            let txt = t.span.text(src);
            if !collecting {
                if txt == "<" {
                    collecting = true;
                }
                continue;
            }
            if txt == ">" {
                break;
            }
            parts.push_str(txt);
        }
        if !parts.is_empty() {
            self.emit_external_include(file_id, &parts);
        }
    }

    fn emit_external_include(&mut self, file_id: &str, path: &str) {
        let dep_id = ext_id(path);
        self.g.upsert_node(
            dep_id.clone(),
            ont::EXTERNAL_DEPENDENCY,
            path.to_string(),
            vec![
                ("external", Json::Bool(true)),
                ("source", Json::str("include")),
            ],
        );
        self.g.add_edge(
            file_id,
            edge::IMPORTS,
            dep_id.clone(),
            vec![
                ("path", Json::str(path.to_string())),
                ("external", Json::Bool(true)),
            ],
        );
        self.g
            .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
    }

    /// `#define NAME …` / `#define NAME(args) …` → a `Macro` node. Function-like is
    /// detected by an `(` immediately following the name with no intervening
    /// whitespace, exactly as the C preprocessor requires.
    fn handle_define(
        &mut self,
        item: &Node,
        file_id: &str,
        module_join: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let kids = &item.children;
        let mut define_idx = None;
        for (i, c) in kids.iter().enumerate() {
            if let Child::Token(t) = c {
                if !t.trivia && t.kind == tk::IDENT && t.span.text(src) == "define" {
                    define_idx = Some(i);
                    break;
                }
            }
        }
        let define_idx = match define_idx {
            Some(i) => i,
            None => return,
        };
        // First identifier following `define` is the macro name.
        let mut name_idx = None;
        for (i, c) in kids.iter().enumerate().skip(define_idx + 1) {
            match c {
                Child::Token(t) if t.trivia => continue,
                Child::Token(t) if t.kind == tk::IDENT => {
                    name_idx = Some(i);
                    break;
                }
                _ => break,
            }
        }
        let name_idx = match name_idx {
            Some(i) => i,
            None => return,
        };
        let name_tok = match &kids[name_idx] {
            Child::Token(t) => t,
            _ => return,
        };
        let name = name_tok.span.text(src).to_string();
        let line = li.line_col(name_tok.span.start).line;
        let function_like = matches!(
            kids.get(name_idx + 1),
            Some(Child::Token(t)) if !t.trivia && t.span.text(src) == "("
        );
        let qual = qual_name(module_join, &name);
        let id = format!("macro::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::MACRO,
            name.clone(),
            vec![
                (
                    "macro_kind",
                    Json::str(if function_like {
                        "function_like"
                    } else {
                        "object_like"
                    }),
                ),
                ("language", Json::str("c")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.macro_by_name.entry(name).or_default().push(id);
    }

    /// A top-level object declaration (`int x = …;`, `static const T NAME;`) → a
    /// `Constant`. Declarations carrying a parameter `Paren` (prototypes, function
    /// pointers) are not constants and are skipped — conservative, never guessed.
    fn handle_decl_const(
        &mut self,
        item: &Node,
        file_id: &str,
        module_join: &str,
        src: &str,
        li: &LineIndex,
    ) {
        if item.child_nodes().any(|n| n.kind == cst::PAREN) {
            return;
        }
        let name = match name_text(item, src) {
            Some(n) => n.to_string(),
            None => return,
        };
        let line = li.line_col(name_span_start(item)).line;
        let id = format!("const::{}", qual_name(module_join, &name));
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            name,
            vec![
                ("binding", Json::str("global_var")),
                ("language", Json::str("c")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
    }

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, module_join: &str) -> Resolution {
        // Local translation unit.
        let c = self.fns_in_module(module_join, &call.name);
        if !c.is_empty() {
            return mk(c, "local");
        }
        // Global (e.g. declared in a header, defined in another unit).
        let c = self.global_fns(&call.name);
        if !c.is_empty() {
            return mk(c, "global");
        }
        // Macros expand like calls.
        let c = self.macros(&call.name);
        if !c.is_empty() {
            return mk(c, "macro");
        }
        Resolution {
            outcome: Outcome::None,
            level: "external",
        }
    }

    fn emit_call(&mut self, caller_id: &str, call: &Call, res: Resolution) {
        let mut props = vec![
            ("callee", Json::str(call.name.clone())),
            ("method", Json::Bool(call.method)),
            ("resolution", Json::str(res.level)),
        ];
        if let Some(r) = &call.receiver {
            props.push(("receiver", Json::str(r.clone())));
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

    fn macros(&self, name: &str) -> Vec<String> {
        self.macro_by_name.get(name).cloned().unwrap_or_default()
    }

    fn unique_type(&self, name: &str) -> Option<String> {
        match self.type_by_name.get(name) {
            Some(ids) if ids.len() == 1 => Some(ids[0].clone()),
            _ => None,
        }
    }

    /// Add `USES_TYPE` edges for identifiers in the function's signature region
    /// (everything before the body brace) that name a unique project type.
    fn emit_type_uses(&mut self, from_id: &str, func: &Node, src: &str) {
        let mut seen: Vec<String> = Vec::new();
        for ch in &func.children {
            match ch {
                Child::Node(n) if n.kind == cst::BRACE => break, // reached the body
                Child::Node(n) if n.kind == cst::NAME => {}      // the function's own name
                Child::Node(n) => {
                    for nn in n.walk() {
                        for t in nn.tokens() {
                            if t.kind == tk::IDENT {
                                self.maybe_use_type(from_id, t.span.text(src), &mut seen);
                            }
                        }
                    }
                }
                Child::Token(t) if !t.trivia && t.kind == tk::IDENT => {
                    self.maybe_use_type(from_id, t.span.text(src), &mut seen);
                }
                _ => {}
            }
        }
    }

    fn maybe_use_type(&mut self, from_id: &str, name: &str, seen: &mut Vec<String>) {
        if is_keyword(name) {
            return;
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

fn mk(ids: Vec<String>, level: &'static str) -> Resolution {
    let outcome = if ids.len() == 1 {
        Outcome::One(ids[0].clone())
    } else {
        Outcome::Many(ids)
    };
    Resolution { outcome, level }
}

// --- pure helpers -----------------------------------------------------------

/// Dotted module-join for a file's module path: `["a","b"]` → `"a.b"`, `[]` → "".
fn mod_join(path: &[String]) -> String {
    path.join(".")
}

/// `module.name` — the dotted qualified name and the basis for node ids.
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

/// Strip the surrounding quotes from an include path string literal.
fn unquote(s: &str) -> String {
    s.trim_matches('"').to_string()
}

/// The bare header stem used as a module name: drop directories and a trailing
/// `.h`/`.hpp`/`.hh` extension (`"sys/types.h"` → `"types"`).
fn header_stem(path: &str) -> String {
    let base = path.rsplit('/').next().unwrap_or(path);
    match base.rsplit_once('.') {
        Some((stem, _)) => stem.to_string(),
        None => base.to_string(),
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

/// True if a top-level (non-trivia, direct) identifier token of `item` equals
/// `kw` — used for storage-class hints like `static` on a function definition.
fn has_top_kw(item: &Node, src: &str, kw: &str) -> bool {
    item.tokens()
        .any(|t| t.kind == tk::IDENT && t.span.text(src) == kw)
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

/// Detect `name(...)` and `recv.name(...)` / `recv->name(...)` call sites over the
/// real token tree, recursing into nested balanced groups. Keywords are excluded
/// (so `if (…)`, `sizeof (…)`, `return (…)` are not calls).
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        // Member call: (`.` | `->`) name `(...)`.
        if matches!(tok_text(&els[i]), Some(".") | Some("->")) {
            if i + 2 < n && is_ident_el(&els[i + 1]) {
                if let Some(g) = grp(&els[i + 2]) {
                    if g.kind == cst::PAREN {
                        let name = tok_text(&els[i + 1]).unwrap_or("").to_string();
                        if !is_keyword(&name) {
                            let receiver = if i > 0 {
                                match &els[i - 1] {
                                    El::Tok { text, ident: true } => Some(text.to_string()),
                                    _ => None,
                                }
                            } else {
                                None
                            };
                            out.push(Call {
                                name,
                                method: true,
                                receiver,
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
        // Bare call: name `(...)`, not a member access and not a keyword.
        if is_ident_el(&els[i]) {
            let prev = if i > 0 { tok_text(&els[i - 1]) } else { None };
            let text = tok_text(&els[i]).unwrap_or("");
            let is_member = prev == Some(".") || prev == Some("->");
            if !is_member && !is_keyword(text) && i + 1 < n {
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
    // Recurse into nested groups (the body brace, parenthesized sub-expressions).
    for e in &els {
        if let Some(g) = grp(e) {
            scan_calls(g, src, out);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::c::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("mod.c", src);
        let file = SourceFile {
            rel_path: "mod.c".to_string(),
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
        let g = graph_for(
            "struct Point { int x; int y; };\nint add(int a, int b) {\n    return a + b;\n}\n",
        );
        assert_eq!(g.count_nodes_of(ont::FUNCTION), 1, "add");
        assert_eq!(g.count_nodes_of(ont::TYPE), 1, "struct Point");
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "module mod");
    }

    #[test]
    fn struct_type_kind() {
        let g = graph_for("struct C { int a; };\n");
        let ty = g
            .nodes()
            .find(|n| n.kind == ont::TYPE)
            .expect("a Type node");
        assert_eq!(ty.props.get("type_kind"), Some(&Json::str("struct")));
        assert_eq!(ty.props.get("language"), Some(&Json::str("c")));
    }

    #[test]
    fn typedef_is_typedef_type_kind() {
        let g = graph_for("typedef struct Node { int v; } Node;\n");
        let td = g
            .nodes()
            .find(|n| n.kind == ont::TYPE && n.name == "Node")
            .expect("a typedef Type");
        assert_eq!(td.props.get("type_kind"), Some(&Json::str("typedef")));
    }

    #[test]
    fn resolves_unique_local_call() {
        let g = graph_for(
            "int add(int a, int b) {\n    return a + b;\n}\nint run(void) {\n    return add(1, 2);\n}\n",
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
        let g = graph_for("int run(void) {\n    mystery();\n    return 0;\n}\n");
        let calls = call_edges(&g);
        let m = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("mystery")))
            .expect("the mystery call");
        assert_eq!(m.props.get("resolution"), Some(&Json::str("external")));
        assert!(g.has_node("unresolved::mystery"));
    }

    #[test]
    fn macro_call_resolves_to_macro() {
        let g =
            graph_for("#define DOUBLE(x) ((x) * 2)\nint run(int n) {\n    return DOUBLE(n);\n}\n");
        assert!(g.count_nodes_of(ont::MACRO) >= 1, "macro node exists");
        let calls = call_edges(&g);
        let d = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("DOUBLE")))
            .expect("a DOUBLE call");
        assert_eq!(d.props.get("resolution"), Some(&Json::str("macro")));
    }

    #[test]
    fn system_include_creates_dependency() {
        let g = graph_for("#include <stdio.h>\n");
        assert!(g.has_node("ext::stdio.h"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::stdio.h"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn local_include_is_internal_import() {
        let g = graph_for("#include \"point.h\"\n");
        let imp = g
            .edges()
            .find(|e| e.kind == edge::IMPORTS)
            .expect("an IMPORTS edge");
        assert_eq!(imp.props.get("external"), Some(&Json::Bool(false)));
        assert!(
            !g.has_node("ext::point.h"),
            "quoted include is not external"
        );
    }

    #[test]
    fn global_variable_is_constant() {
        let g = graph_for("static int g_count = 0;\nint f(void) { return 0; }\n");
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 1);
        let c = g
            .nodes()
            .find(|n| n.kind == ont::CONSTANT)
            .expect("a constant");
        assert_eq!(c.name, "g_count");
    }

    #[test]
    fn prototype_creates_no_function_node() {
        let g = graph_for("int proto(int);\n");
        assert_eq!(g.count_nodes_of(ont::FUNCTION), 0);
    }

    #[test]
    fn type_use_in_signature() {
        let g = graph_for(
            "struct Widget { int w; };\nint build(struct Widget *p) {\n    return p->w;\n}\n",
        );
        assert!(
            g.edges()
                .any(|e| e.kind == edge::USES_TYPE && e.to.contains("Widget")),
            "parameter type should create USES_TYPE"
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src = "#include <stdio.h>\nstruct S { int a; };\nint helper(void) { return 1; }\nint main(void) {\n    return helper();\n}\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
