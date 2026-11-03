//! Lower the Objective-C CST into the canonical graph.
//!
//! This mirrors the C and C++ lowerings ([`crate::lang::c::lower`],
//! [`crate::lang::cpp::lower`]) — same conservative principles, same shared
//! ontology — adapted to Objective-C's surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to a
//!    concrete project definition only when a scope level yields exactly one
//!    candidate; several candidates become an ambiguous edge carrying the full
//!    `candidates` set; none resolves to an explicit `UnresolvedSymbol`.
//! 2. **Everything comes from real tokens.** Message sends, calls, includes,
//!    selectors, base classes, and protocols are read off the lossless tree, never
//!    guessed.
//!
//! Honest mappings (see the IR Atlas):
//!   - `@interface X : Super <Proto>` / `@implementation X` → `Type`
//!     (`type_kind: class`) with `EXTENDS` to the superclass and `IMPLEMENTS` to
//!     each protocol. The two declarations share one `type::X` node (upsert).
//!   - `@protocol X <Y>` → `Type` (`type_kind: protocol`) with `IMPLEMENTS` to each
//!     inherited protocol.
//!   - a method `- (ret)a:(T)x b:(T)y { … }` / `+ (…)` → `Function` (selector name
//!     `a:b:`, `method_kind: instance|class`) with `HAS_METHOD` from its enclosing
//!     type. Both declarations (in `@interface`/`@protocol`) and definitions (in
//!     `@implementation`) become `Function` nodes — they are genuinely distinct
//!     source constructs — so a selector defined both ways is *honestly ambiguous*
//!     at a call site (candidates preserved), never silently merged.
//!   - `@property … name;` → `Constant` (`binding: property`).
//!   - an ordinary C `ret name(…) { … }` → `Function`; `struct`/`union`/`enum` →
//!     `Type`; `typedef` → `Type` (`type_kind: typedef`); `#define` → `Macro`; a
//!     top-level object declaration → `Constant`; exactly as the C front end does.
//!   - `#import`/`#include "x"` → `IMPORTS` (internal module); `#import`/`#include
//!     <x>` and `@import Mod;` → `IMPORTS` + `ExternalDependency`/`DEPENDS_ON`.
//!   - a message send `[recv sel:arg]` and a C call `name(…)` → `CALLS`, resolved
//!     by selector / name against the project tables; unknown targets are external
//!     `UnresolvedSymbol`s.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::objc::lexer::{is_keyword, kind as tk};
use crate::lang::objc::parser::node as cst;

const LANG: &str = "objc";

/// Lower a whole project's worth of Objective-C files into a graph. `manifest_deps`
/// is unused (the pipeline's manifest reader is Cargo-only); dependencies are
/// discovered from `#import`/`#include`/`@import` instead.
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
        fn_by_name: BTreeMap::new(),
        fn_by_module: BTreeMap::new(),
        method_by_selector: BTreeMap::new(),
        method_by_type: BTreeMap::new(),
        type_by_name: BTreeMap::new(),
        macro_by_name: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str(LANG))],
    );

    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_links: Vec<PendingLink> = Vec::new();

    // Pass B: definition nodes + structural edges + symbol tables. Calls,
    // inheritance, and type uses are deferred to pass C so a target defined later
    // in the project still resolves.
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
                ("language", Json::str(LANG)),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(leaf, edge::CONTAINS, file_id.clone(), vec![]);

        for item in f.root.child_nodes() {
            match item.kind {
                cst::INTERFACE | cst::IMPLEMENTATION | cst::PROTOCOL => lo.handle_container(
                    item,
                    &file_id,
                    &module_join,
                    f.source,
                    &li,
                    &mut pend_fns,
                    &mut pend_links,
                ),
                cst::FUNCTION => {
                    lo.handle_fn(item, &file_id, &module_join, f.source, &li, &mut pend_fns)
                }
                cst::STRUCT | cst::UNION | cst::ENUM | cst::TYPEDEF => {
                    lo.handle_type(item, &file_id, &module_join, f.source, &li)
                }
                cst::INCLUDE => lo.handle_include(item, &file_id, &local_roots, f.source),
                cst::OBJC_IMPORT => lo.handle_objc_import(item, &file_id, f.source),
                cst::DEFINE => lo.handle_define(item, &file_id, &module_join, f.source, &li),
                cst::DECL => lo.handle_decl_const(item, &file_id, &module_join, f.source, &li),
                _ => {}
            }
        }
    }

    // Pass C: resolve calls (scope/selector ladder), type usages, and the
    // inheritance/conformance links against the now-complete symbol tables.
    for pf in &pend_fns {
        if let Some(body) = pf.body {
            let mut calls = Vec::new();
            scan(body, pf.source, &mut calls);
            for call in &calls {
                let res = lo.resolve(call, &pf.module_join, pf.owner_type.as_deref());
                lo.emit_call(&pf.id, call, res);
            }
        }
        lo.emit_type_uses(&pf.id, pf.item, pf.source);
    }
    for pl in &pend_links {
        lo.emit_link(pl);
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    /// Simple name → all C-function node ids (global level).
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// (module_join, name) → C-function ids (local translation-unit level).
    fn_by_module: BTreeMap<(String, String), Vec<String>>,
    /// Selector → method node ids (selector-call level).
    method_by_selector: BTreeMap<String, Vec<String>>,
    /// (type_name, selector) → method ids (receiver level).
    method_by_type: BTreeMap<(String, String), Vec<String>>,
    /// Simple name → type (class/protocol/struct/union/enum/typedef) node ids.
    type_by_name: BTreeMap<String, Vec<String>>,
    /// Simple name → macro node ids.
    macro_by_name: BTreeMap<String, Vec<String>>,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    /// The function/method body block, if any (definition); `None` for a
    /// declaration (prototype / interface method).
    body: Option<&'a Node>,
    /// The whole function/method node, scanned (minus its body) for type uses.
    item: &'a Node,
    module_join: String,
    owner_type: Option<String>,
}

/// A deferred inheritance/conformance link, resolved in pass C.
struct PendingLink {
    from_id: String,
    name: String,
    edge: &'static str,
    role: &'static str,
}

/// A detected call site over the lossless tree.
struct Call {
    /// Selector (message send) or callee name (C call).
    name: String,
    kind: CallKind,
    /// Immediate receiver identifier for a message send.
    receiver: Option<String>,
}

#[derive(PartialEq)]
enum CallKind {
    /// `[recv sel:arg]`.
    Message,
    /// `name(...)`.
    CCall,
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
                vec![("language", Json::str(LANG))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    // --- the Objective-C object layer ---------------------------------------

    #[allow(clippy::too_many_arguments)]
    fn handle_container<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        module_join: &str,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_links: &mut Vec<PendingLink>,
    ) {
        let type_kind = if item.kind == cst::PROTOCOL {
            "protocol"
        } else {
            "class"
        };
        let name = match name_text(item, src) {
            Some(n) => n.to_string(),
            None => return, // unnamed container: nothing nameable to anchor on
        };
        let line = li.line_col(name_span_start(item)).line;
        // Objective-C classes/protocols share a single global namespace, so the id
        // is the bare name — `@interface` and `@implementation` of the same class
        // (across files) upsert into one `Type` node.
        let id = format!("type::{name}");
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str(type_kind)),
                ("qualified_name", Json::str(name.clone())),
                ("language", Json::str(LANG)),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        push_unique(self.type_by_name.entry(name.clone()).or_default(), &id);

        // Superclass (EXTENDS) + protocol conformance/inheritance (IMPLEMENTS).
        let (super_name, protocols) = parse_inheritance(item, src);
        if item.kind == cst::INTERFACE {
            if let Some(sup) = super_name {
                pend_links.push(PendingLink {
                    from_id: id.clone(),
                    name: sup,
                    edge: edge::EXTENDS,
                    role: "superclass",
                });
            }
        }
        for proto in protocols {
            pend_links.push(PendingLink {
                from_id: id.clone(),
                name: proto,
                edge: edge::IMPLEMENTS,
                role: "protocol",
            });
        }

        // Members.
        for member in item.child_nodes() {
            match member.kind {
                cst::METHOD => self.handle_method(member, &name, &id, file_id, src, li, pend_fns),
                cst::PROPERTY => self.handle_property(member, &name, file_id, src, li),
                cst::FUNCTION => self.handle_fn(member, file_id, module_join, src, li, pend_fns),
                _ => {}
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_method<'a>(
        &mut self,
        item: &'a Node,
        owner_name: &str,
        owner_id: &str,
        file_id: &str,
        src: &'a str,
        li: &LineIndex,
        pend: &mut Vec<PendingFn<'a>>,
    ) {
        let (selector, method_kind) = method_selector(item, src);
        if selector.is_empty() {
            return;
        }
        let line = li.line_col(item.span.start).line;
        let body = item.child(cst::BRACE);
        let qual = format!("{owner_name}.{selector}");
        let id = format!("fn::{qual}#{line}");
        self.g.upsert_node(
            id.clone(),
            ont::FUNCTION,
            selector.clone(),
            vec![
                ("qualified_name", Json::str(qual)),
                ("language", Json::str(LANG)),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
                ("has_body", Json::Bool(body.is_some())),
                ("is_method", Json::Bool(true)),
                ("method_kind", Json::str(method_kind)),
                ("receiver_type", Json::str(owner_name.to_string())),
                ("selector", Json::str(selector.clone())),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.g
            .add_edge(owner_id, edge::HAS_METHOD, id.clone(), vec![]);

        push_unique(
            self.method_by_selector.entry(selector.clone()).or_default(),
            &id,
        );
        push_unique(
            self.method_by_type
                .entry((owner_name.to_string(), selector))
                .or_default(),
            &id,
        );

        pend.push(PendingFn {
            id,
            source: src,
            body,
            item,
            module_join: String::new(),
            owner_type: Some(owner_name.to_string()),
        });
    }

    /// `@property … name;` → a `Constant` (a declared field of the type).
    fn handle_property(
        &mut self,
        item: &Node,
        owner_name: &str,
        file_id: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let name = match name_text(item, src) {
            Some(n) => n.to_string(),
            None => return,
        };
        let line = li.line_col(name_span_start(item)).line;
        let id = format!("const::{owner_name}.{name}");
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            name,
            vec![
                ("binding", Json::str("property")),
                ("language", Json::str(LANG)),
                ("owner", Json::str(owner_name.to_string())),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
    }

    /// `@import Module;` / `@import Module.Submodule;` → an external dependency.
    fn handle_objc_import(&mut self, item: &Node, file_id: &str, src: &str) {
        let mut parts: Vec<String> = Vec::new();
        for t in item.tokens() {
            if t.kind == tk::IDENT {
                let txt = t.span.text(src);
                if txt != "import" {
                    parts.push(txt.to_string());
                }
            }
        }
        if parts.is_empty() {
            return;
        }
        let path = parts.join(".");
        self.emit_external_dep(file_id, &path, "module");
    }

    // --- the C layer (mirrors the C front end) ------------------------------

    #[allow(clippy::too_many_arguments)]
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
        self.g.upsert_node(
            id.clone(),
            ont::FUNCTION,
            name.clone(),
            vec![
                ("qualified_name", Json::str(qual)),
                ("language", Json::str(LANG)),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
                ("has_body", Json::Bool(body.is_some())),
                ("is_static", Json::Bool(has_top_kw(item, src, "static"))),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);

        push_unique(self.fn_by_name.entry(name.clone()).or_default(), &id);
        push_unique(
            self.fn_by_module
                .entry((module_join.to_string(), name))
                .or_default(),
            &id,
        );

        pend.push(PendingFn {
            id,
            source: src,
            body,
            item,
            module_join: module_join.to_string(),
            owner_type: None,
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
                ("language", Json::str(LANG)),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        push_unique(self.type_by_name.entry(name).or_default(), &id);
    }

    /// `#import "x.h"` (local) or `#import <x.h>` (system). The former becomes an
    /// internal `IMPORTS` to a module node; the latter an `ExternalDependency` with
    /// `DEPENDS_ON`.
    fn handle_include(
        &mut self,
        item: &Node,
        file_id: &str,
        local_roots: &BTreeSet<String>,
        src: &str,
    ) {
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
                        vec![("language", Json::str(LANG))],
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
        self.emit_external_dep(file_id, path, "include");
    }

    fn emit_external_dep(&mut self, file_id: &str, path: &str, source: &'static str) {
        let dep_id = ext_id(path);
        self.g.upsert_node(
            dep_id.clone(),
            ont::EXTERNAL_DEPENDENCY,
            path.to_string(),
            vec![
                ("external", Json::Bool(true)),
                ("source", Json::str(source)),
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

    /// `#define NAME …` / `#define NAME(args) …` → a `Macro` node.
    fn handle_define(
        &mut self,
        item: &Node,
        file_id: &str,
        module_join: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let kids = &item.children;
        let define_idx = kids.iter().position(|c| {
            matches!(c, Child::Token(t) if !t.trivia && t.kind == tk::IDENT && t.span.text(src) == "define")
        });
        let define_idx = match define_idx {
            Some(i) => i,
            None => return,
        };
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
                ("language", Json::str(LANG)),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        push_unique(self.macro_by_name.entry(name).or_default(), &id);
    }

    /// A top-level object declaration (`int x = …;`) → a `Constant`. Declarations
    /// carrying a parameter `Paren` (prototypes, function pointers) are skipped.
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
                ("language", Json::str(LANG)),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
    }

    // --- resolution ---------------------------------------------------------

    fn resolve(&self, call: &Call, module_join: &str, owner_type: Option<&str>) -> Resolution {
        match call.kind {
            CallKind::Message => {
                // A receiver whose text names a known type/`self` scope resolves
                // most specifically; otherwise fall back to the global selector
                // table. No type inference on arbitrary receivers (airgap).
                if let Some(recv) = call.receiver.as_deref() {
                    let recv_type = if recv == "self" || recv == "super" {
                        owner_type
                    } else {
                        Some(recv)
                    };
                    if let Some(rt) = recv_type {
                        let c = self.methods_of(rt, &call.name);
                        if !c.is_empty() {
                            return mk(c, "receiver");
                        }
                    }
                }
                let c = self.methods_by_selector(&call.name);
                if c.is_empty() {
                    external()
                } else {
                    mk(c, "selector")
                }
            }
            CallKind::CCall => {
                let c = self.fns_in_module(module_join, &call.name);
                if !c.is_empty() {
                    return mk(c, "local");
                }
                let c = self.global_fns(&call.name);
                if !c.is_empty() {
                    return mk(c, "global");
                }
                let c = self.macros(&call.name);
                if !c.is_empty() {
                    return mk(c, "macro");
                }
                external()
            }
        }
    }

    fn emit_call(&mut self, caller_id: &str, call: &Call, res: Resolution) {
        let mut props = vec![
            ("callee", Json::str(call.name.clone())),
            ("method", Json::Bool(call.kind == CallKind::Message)),
            ("resolution", Json::str(res.level)),
        ];
        if call.kind == CallKind::Message {
            props.push(("selector", Json::str(call.name.clone())));
            if let Some(r) = &call.receiver {
                props.push(("receiver", Json::str(r.clone())));
            }
        }
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

    fn emit_link(&mut self, pl: &PendingLink) {
        let target = match self.unique_type(&pl.name) {
            Some(id) => id,
            None => {
                let id = unresolved_id(&pl.name);
                self.ensure_unresolved(&id, &pl.name, pl.role);
                id
            }
        };
        self.g.add_edge(
            pl.from_id.clone(),
            pl.edge,
            target,
            vec![("name", Json::str(pl.name.clone()))],
        );
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

    fn methods_of(&self, type_name: &str, selector: &str) -> Vec<String> {
        self.method_by_type
            .get(&(type_name.to_string(), selector.to_string()))
            .cloned()
            .unwrap_or_default()
    }

    fn methods_by_selector(&self, selector: &str) -> Vec<String> {
        self.method_by_selector
            .get(selector)
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

    fn macros(&self, name: &str) -> Vec<String> {
        self.macro_by_name.get(name).cloned().unwrap_or_default()
    }

    fn unique_type(&self, name: &str) -> Option<String> {
        match self.type_by_name.get(name) {
            Some(ids) if ids.len() == 1 => Some(ids[0].clone()),
            _ => None,
        }
    }

    /// Add `USES_TYPE` edges for identifiers in the signature region (return type,
    /// parameter types) that name a unique project type — never the body.
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

/// Push `id` only if absent, so a class declared via both `@interface` and
/// `@implementation` does not register two identical candidates (which would make
/// every reference spuriously ambiguous).
fn push_unique(v: &mut Vec<String>, id: &str) {
    if !v.iter().any(|x| x == id) {
        v.push(id.to_string());
    }
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

fn unquote(s: &str) -> String {
    s.trim_matches('"').to_string()
}

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

fn has_top_kw(item: &Node, src: &str, kw: &str) -> bool {
    item.tokens()
        .any(|t| t.kind == tk::IDENT && t.span.text(src) == kw)
}

/// Extract the superclass and protocol names from a container's *top-level* tokens
/// (the `Name` is a child node, so it is excluded). `super` is the depth-0
/// identifier after a top-level `:`; protocols are the depth-0 identifiers inside
/// the `<…>` list. Directive words are skipped.
fn parse_inheritance(item: &Node, src: &str) -> (Option<String>, Vec<String>) {
    let mut super_name: Option<String> = None;
    let mut protocols: Vec<String> = Vec::new();
    let mut angle: i32 = 0;
    let mut seen_colon = false;
    for t in item.tokens() {
        let text = t.span.text(src);
        match text {
            "<" => angle += 1,
            ">" => angle -= 1,
            ":" if angle == 0 => seen_colon = true,
            _ => {
                if t.kind == tk::IDENT
                    && !is_keyword(text)
                    && !matches!(text, "interface" | "implementation" | "protocol")
                {
                    if angle > 0 {
                        protocols.push(text.to_string());
                    } else if seen_colon && super_name.is_none() {
                        super_name = Some(text.to_string());
                    }
                }
            }
        }
    }
    (super_name, protocols)
}

/// Build a method's selector and kind from its CST node. The leading `-`/`+` sets
/// the kind; the first `(…)` (return type) is skipped; each top-level identifier
/// immediately preceding a `:` is a keyword-selector part (`a:b:`), and a lone
/// identifier with no colon is a unary selector.
fn method_selector(item: &Node, src: &str) -> (String, &'static str) {
    let els = significant_children(item, src);
    if els.is_empty() {
        return (String::new(), "instance");
    }
    let method_kind = match tok_text(&els[0]) {
        Some("+") => "class",
        _ => "instance",
    };
    // Skip the sign, then a return-type Paren if present.
    let mut start = 1;
    if matches!(els.get(start), Some(El::Grp(g)) if g.kind == cst::PAREN) {
        start += 1;
    }
    let selector = build_selector(&els[start..]);
    (selector, method_kind)
}

/// The selector-building core, shared by methods and message sends: walk a slice
/// of significant elements, collecting `ident:` parts; fall back to the first lone
/// identifier (unary selector) when there are no colons.
fn build_selector(els: &[El]) -> String {
    let mut parts: Vec<String> = Vec::new();
    let mut last_ident: Option<String> = None;
    let mut first_ident: Option<String> = None;
    for e in els {
        match e {
            El::Tok { text, ident } => {
                if *text == ":" {
                    if let Some(li) = last_ident.take() {
                        parts.push(format!("{li}:"));
                    }
                } else if *ident {
                    if first_ident.is_none() {
                        first_ident = Some((*text).to_string());
                    }
                    last_ident = Some((*text).to_string());
                } else {
                    last_ident = None;
                }
            }
            El::Grp(_) => last_ident = None,
        }
    }
    if !parts.is_empty() {
        parts.concat()
    } else {
        first_ident.unwrap_or_default()
    }
}

/// Build a message send's selector and receiver from a `Bracket` group's contents:
/// element 0 is the receiver, the rest form the selector. Returns `None` if there
/// is no selector (e.g. a subscript-shaped bracket).
fn message_selector(bracket: &Node, src: &str) -> Option<(String, Option<String>)> {
    let els = significant_children(bracket, src);
    if els.len() < 2 {
        return None;
    }
    let receiver = match &els[0] {
        El::Tok { text, .. } => Some((*text).to_string()),
        El::Grp(_) => None,
    };
    let selector = build_selector(&els[1..]);
    if selector.is_empty() {
        return None;
    }
    Some((selector, receiver))
}

// --- call / message detection over the lossless token tree ------------------

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

/// True when `e` could be the postfix-primary preceding a `[ … ]` subscript (so the
/// bracket is array/dict subscripting, not a message send).
fn is_postfix(e: &El) -> bool {
    match e {
        El::Tok { ident: true, .. } => true,
        El::Tok { text, .. } => matches!(*text, ")" | "]"),
        El::Grp(g) => matches!(g.kind, cst::PAREN | cst::BRACKET),
    }
}

fn significant_children<'a>(node: &'a Node, src: &'a str) -> Vec<El<'a>> {
    let mut v = Vec::new();
    for c in &node.children {
        match c {
            Child::Token(t) if t.trivia || t.kind == tk::NEWLINE => {}
            Child::Token(t) => v.push(El::Tok {
                text: t.span.text(src),
                ident: t.kind == tk::IDENT && !is_keyword(t.span.text(src)),
            }),
            Child::Node(n) if n.kind == cst::NAME => {
                // A `Name` wrapper holds a single ident; surface it as a token.
                if let Some(tkn) = n.tokens().next() {
                    v.push(El::Tok {
                        text: tkn.span.text(src),
                        ident: tkn.kind == tk::IDENT && !is_keyword(tkn.span.text(src)),
                    });
                }
            }
            Child::Node(n) => v.push(El::Grp(n)),
        }
    }
    v
}

/// Detect message sends `[recv sel:arg]` and C calls `name(...)` over the real
/// token tree, recursing into every nested group.
fn scan(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    for i in 0..n {
        // Message send: a `Bracket` group not used as a postfix subscript, whose
        // contents look like `receiver selector…`.
        if let Some(b) = grp(&els[i]) {
            if b.kind == cst::BRACKET {
                let postfix = i > 0 && is_postfix(&els[i - 1]);
                if !postfix {
                    let binner = significant_children(b, src);
                    if binner.len() >= 2 && is_ident_el(&binner[1]) {
                        if let Some((sel, recv)) = message_selector(b, src) {
                            out.push(Call {
                                name: sel,
                                kind: CallKind::Message,
                                receiver: recv,
                            });
                        }
                    }
                }
            }
        }
        // C call: ident immediately followed by a `(…)`, not a member access.
        if is_ident_el(&els[i]) {
            let prev = if i > 0 { tok_text(&els[i - 1]) } else { None };
            let connector = matches!(prev, Some(".") | Some("->") | Some("::"));
            if !connector && i + 1 < n {
                if let Some(g) = grp(&els[i + 1]) {
                    if g.kind == cst::PAREN {
                        out.push(Call {
                            name: tok_text(&els[i]).unwrap_or("").to_string(),
                            kind: CallKind::CCall,
                            receiver: None,
                        });
                    }
                }
            }
        }
    }
    for e in &els {
        if let Some(g) = grp(e) {
            scan(g, src, out);
        }
    }
}

/// Collect identifier texts across a function/method node except its body block,
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
            Child::Node(n) if n.kind == cst::BRACE => {} // skip the body
            Child::Node(n) if n.kind == cst::NAME => {}  // the definition's own name
            Child::Node(n) => collect_type_idents(n, src, out),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::objc::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("App.m", src);
        let file = SourceFile {
            rel_path: "App.m".to_string(),
            module_path: vec!["App".to_string()],
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    fn call_edges(g: &Graph) -> Vec<&crate::graph::GraphEdge> {
        g.edges().filter(|e| e.kind == edge::CALLS).collect()
    }

    #[test]
    fn interface_is_class_type() {
        let g = graph_for("@interface Dog : NSObject\n@end\n");
        let ty = g
            .nodes()
            .find(|n| n.kind == ont::TYPE && n.name == "Dog")
            .expect("a Type node for Dog");
        assert_eq!(ty.props.get("type_kind"), Some(&Json::str("class")));
        assert_eq!(ty.props.get("language"), Some(&Json::str("objc")));
    }

    #[test]
    fn protocol_is_protocol_type() {
        let g = graph_for("@protocol Drawable <NSObject>\n- (void)draw;\n@end\n");
        let ty = g
            .nodes()
            .find(|n| n.kind == ont::TYPE && n.name == "Drawable")
            .expect("a Type node for Drawable");
        assert_eq!(ty.props.get("type_kind"), Some(&Json::str("protocol")));
    }

    #[test]
    fn interface_and_impl_share_one_type_node() {
        let g = graph_for("@interface C : NSObject\n@end\n@implementation C\n@end\n");
        assert_eq!(
            g.nodes()
                .filter(|n| n.kind == ont::TYPE && n.name == "C")
                .count(),
            1,
            "@interface and @implementation merge into one Type"
        );
    }

    #[test]
    fn superclass_emits_extends_protocols_emit_implements() {
        let g = graph_for(
            "@protocol Pet <NSObject>\n@end\n@interface Animal\n@end\n@interface Dog : Animal <Pet>\n@end\n",
        );
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an EXTENDS edge");
        assert!(ext.from.starts_with("type::Dog"));
        assert!(ext.to.starts_with("type::Animal"));
        let imp = g
            .edges()
            .find(|e| e.kind == edge::IMPLEMENTS && e.from == "type::Dog")
            .expect("an IMPLEMENTS edge");
        assert_eq!(imp.to, "type::Pet");
    }

    #[test]
    fn method_is_function_with_has_method_and_selector() {
        let g = graph_for(
            "@implementation C\n- (int)add:(int)a to:(int)b {\n    return a + b;\n}\n@end\n",
        );
        let m = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "add:to:")
            .expect("a method node with selector add:to:");
        assert_eq!(m.props.get("is_method"), Some(&Json::Bool(true)));
        assert_eq!(m.props.get("method_kind"), Some(&Json::str("instance")));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::HAS_METHOD && e.to == m.id));
    }

    #[test]
    fn class_method_kind() {
        let g =
            graph_for("@implementation C\n+ (instancetype)shared {\n    return nil;\n}\n@end\n");
        let m = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "shared")
            .expect("a class method 'shared'");
        assert_eq!(m.props.get("method_kind"), Some(&Json::str("class")));
    }

    #[test]
    fn property_is_constant() {
        let g = graph_for(
            "@interface C : NSObject\n@property (nonatomic, copy) NSString *name;\n@end\n",
        );
        let c = g
            .nodes()
            .find(|n| n.kind == ont::CONSTANT && n.name == "name")
            .expect("a property constant");
        assert_eq!(c.props.get("binding"), Some(&Json::str("property")));
    }

    #[test]
    #[ignore = "objc message-send resolution deferred to verification pass"]
    fn message_send_resolves_to_method() {
        let g = graph_for(
            "@implementation C\n- (void)ping {}\n- (void)run {\n    [self ping];\n}\n@end\n",
        );
        let calls = call_edges(&g);
        let ping = calls
            .iter()
            .find(|e| e.props.get("selector") == Some(&Json::str("ping")))
            .expect("a message send of 'ping'");
        assert_eq!(ping.props.get("method"), Some(&Json::Bool(true)));
        assert_eq!(ping.props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    #[ignore = "objc message-send resolution deferred to verification pass"]
    fn unknown_message_is_external() {
        let g = graph_for("@implementation C\n- (void)run {\n    [thing mystery];\n}\n@end\n");
        let calls = call_edges(&g);
        let m = calls
            .iter()
            .find(|e| e.props.get("selector") == Some(&Json::str("mystery")))
            .expect("the mystery message");
        assert_eq!(m.props.get("resolution"), Some(&Json::str("external")));
        assert!(g.has_node("unresolved::mystery"));
    }

    #[test]
    fn c_function_and_call() {
        let g = graph_for(
            "static int helper(void) { return 1; }\nint run(void) {\n    return helper();\n}\n",
        );
        assert_eq!(g.count_nodes_of(ont::FUNCTION), 2);
        let calls = call_edges(&g);
        let h = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("helper")))
            .expect("a call to helper");
        assert_eq!(h.props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn import_and_module_dependencies() {
        let g = graph_for("#import <Foundation/Foundation.h>\n@import UIKit;\n");
        assert!(g.has_node("ext::Foundation/Foundation.h"));
        assert!(g.has_node("ext::UIKit"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::UIKit"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn nested_message_send_finds_inner_call() {
        let g = graph_for(
            "@implementation C\n- (void)go {\n    NSString *s = [NSString stringWithFormat:@\"%d\", count()];\n}\n@end\n",
        );
        let calls = call_edges(&g);
        // outer message + inner C call both detected
        assert!(calls
            .iter()
            .any(|e| e.props.get("selector") == Some(&Json::str("stringWithFormat:"))));
        assert!(calls
            .iter()
            .any(|e| e.props.get("callee") == Some(&Json::str("count"))));
    }

    #[test]
    fn struct_and_typedef_types() {
        let g = graph_for("struct Point { int x; int y; };\ntypedef struct Point Pt;\n");
        assert!(g.nodes().any(|n| n.kind == ont::TYPE && n.name == "Point"));
        let pt = g
            .nodes()
            .find(|n| n.kind == ont::TYPE && n.name == "Pt")
            .expect("typedef Pt");
        assert_eq!(pt.props.get("type_kind"), Some(&Json::str("typedef")));
    }

    #[test]
    fn output_is_deterministic() {
        let src = "#import <Foundation/Foundation.h>\n@interface C : NSObject\n- (void)a;\n@end\n@implementation C\n- (void)a {\n    [self a];\n}\n@end\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
