//! Lower the Java CST into the canonical graph.
//!
//! This mirrors the Python lowering ([`crate::lang::python::lower`]) — same
//! conservative principles, same shared ontology — adapted to Java's surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to
//!    a concrete project definition only when a scope level yields exactly one
//!    candidate; several candidates are emitted as an ambiguous edge with the full
//!    `candidates` set; none resolves to an explicit external/unresolved node.
//! 2. **Everything comes from real tokens.** Calls, supertypes, imports, and type
//!    uses are read off the lossless tree, never guessed.
//!
//! Resolution uses a deterministic **scope ladder** (most specific first; the
//! first level with any candidate decides): receiver (`this`/`super`) →
//! enclosing-type methods → global methods. Each edge records which level resolved
//! it, so the call graph stays auditable.
//!
//! Honest mappings (see the IR Atlas):
//!   `class`/`interface`/`enum`/`record`/`@interface` → `Type` distinguished by a
//!   `type_kind` property; a `method`/constructor → `Function` (with `HAS_METHOD`
//!   from its enclosing `Type`); a field/enum-constant/record-component →
//!   `Constant` (a value binding, distinguished by a `binding` property);
//!   `class X extends Y` and `interface I extends J` → `EXTENDS`; `class X
//!   implements I` → `IMPLEMENTS`; `import a.b.C` → `IMPORTS` (plus
//!   `ExternalDependency`/`DEPENDS_ON` for non-project roots). Annotations are
//!   recorded as an `annotations` property (no `ANNOTATES` edge constant exists
//!   yet, so we do not fabricate one — see `docs/ir-atlas.md` candidate
//!   extensions).

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node, Token};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::java::lexer::{is_keyword, kind as tk};
use crate::lang::java::parser::node as cst;

/// Lower a whole project's worth of Java files into a graph. `manifest_deps` is
/// unused for Java (the pipeline's manifest reader is Cargo-only); dependencies
/// are discovered from `import` statements instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    // Project-local package prefixes: every file's dotted module path. An import
    // whose path lies under one of these is intra-project, not an external
    // dependency. Conservative: prefer under-reporting externals to fabricating
    // one for a package we actually own.
    let mut local_packages: BTreeSet<String> = BTreeSet::new();
    for f in files {
        if !f.module_path.is_empty() {
            local_packages.insert(f.module_path.join("."));
        }
    }

    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        local_packages,
        method_by_name: BTreeMap::new(),
        method_by_type: BTreeMap::new(),
        type_by_name: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("java"))],
    );

    // Pass B: create definition nodes + structural edges and build symbol tables.
    // Supertype links are deferred to pass C so a base defined later still resolves.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_ext: Vec<PendingSuper> = Vec::new();
    let mut pend_impl: Vec<PendingSuper> = Vec::new();
    for f in files {
        let li = LineIndex::new(f.source);
        let module_join = f.module_path.join(".");
        let leaf = lo.ensure_packages(&f.module_path);
        let file_id = format!("file::{}", f.rel_path);
        lo.g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("java")),
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
            &[],
            None,
            f.source,
            &li,
            &mut pend_fns,
            &mut pend_ext,
            &mut pend_impl,
        );
    }

    // Pass C: resolve calls (scope ladder), type usages, and supertypes against
    // the now-complete symbol tables.
    for pf in &pend_fns {
        let ctx = Ctx {
            owner_type: pf.owner_type.clone(),
        };
        if let Some(block) = pf.item.child(cst::BLOCK) {
            let mut calls = Vec::new();
            scan_calls(block, pf.source, &mut calls);
            for call in &calls {
                let res = lo.resolve(call, &ctx);
                lo.emit_call(&pf.id, call, res);
            }
        }
        lo.emit_type_uses(&pf.id, pf.item, pf.source);
    }
    for pe in &pend_ext {
        lo.emit_super(pe, edge::EXTENDS, "supertype");
    }
    for pe in &pend_impl {
        lo.emit_super(pe, edge::IMPLEMENTS, "interface");
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    /// Dotted package prefixes the project owns (from file module paths).
    local_packages: BTreeSet<String>,
    /// Simple name → all method node ids (global method-call level).
    method_by_name: BTreeMap<String, Vec<String>>,
    /// (type_name, method_name) → method ids (receiver / same-type level).
    method_by_type: BTreeMap<(String, String), Vec<String>>,
    /// Simple name → type node ids.
    type_by_name: BTreeMap<String, Vec<String>>,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    item: &'a Node,
    owner_type: Option<String>,
}

/// A deferred `extends`/`implements` link, resolved in pass C.
struct PendingSuper {
    type_id: String,
    base_name: String,
}

/// The enclosing type while walking, for methods (`HAS_METHOD`, receiver scope).
struct Owner {
    name: String,
    id: String,
}

/// A detected call site over the lossless tree.
struct Call {
    /// The called name (final attribute or bare name; the type for a constructor).
    name: String,
    /// True for `recv.name(...)` attribute calls.
    method: bool,
    /// Immediate receiver identifier for method calls (`this`, `super`, a variable).
    receiver: Option<String>,
    /// True for `new Type(...)` constructor calls.
    constructor: bool,
}

/// Resolution context for one enclosing method.
struct Ctx {
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

    /// Ensure the `Package → mod::a → mod::a.b …` chain exists and return the leaf
    /// module id (or the package id for a file with no package).
    fn ensure_packages(&mut self, path: &[String]) -> String {
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
                vec![("language", Json::str("java"))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    /// Walk a declaration container (a `CompilationUnit` or `ItemBlock`), creating
    /// definition nodes and recursing into nested types. `owner` is the enclosing
    /// type (the receiver scope for methods).
    #[allow(clippy::too_many_arguments)]
    fn walk<'a>(
        &mut self,
        container: &'a Node,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        owner: Option<&Owner>,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_ext: &mut Vec<PendingSuper>,
        pend_impl: &mut Vec<PendingSuper>,
    ) {
        for item in container.child_nodes() {
            if is_type_decl(item.kind) {
                self.handle_type(
                    item,
                    file_id,
                    module_join,
                    scope,
                    src,
                    li,
                    pend_fns,
                    pend_ext,
                    pend_impl,
                );
                continue;
            }
            match item.kind {
                cst::METHOD => {
                    self.handle_method(item, file_id, module_join, scope, owner, src, li, pend_fns)
                }
                cst::FIELD => self.handle_field(item, file_id, module_join, scope, src, li),
                cst::IMPORT => self.handle_import(item, file_id, src),
                _ => {}
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_type<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_ext: &mut Vec<PendingSuper>,
        pend_impl: &mut Vec<PendingSuper>,
    ) {
        let name = name_text(item, src).unwrap_or("<anonymous>").to_string();
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(module_join, scope, &name);
        let id = format!("type::{qual}");
        let type_kind = match item.kind {
            cst::CLASS => "class",
            cst::INTERFACE => "interface",
            cst::ENUM => "enum",
            cst::RECORD => "record",
            _ => "annotation",
        };
        let mut props = vec![
            ("type_kind", Json::str(type_kind)),
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("java")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
        ];
        if let Some(a) = annotations(item, src) {
            props.push(("annotations", a));
        }
        self.g
            .upsert_node(id.clone(), ont::TYPE, name.clone(), props);
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());

        // Supertypes (deferred to pass C).
        let (extends, implements) = supertypes(item, src);
        for base in extends {
            pend_ext.push(PendingSuper {
                type_id: id.clone(),
                base_name: base,
            });
        }
        for iface in implements {
            pend_impl.push(PendingSuper {
                type_id: id.clone(),
                base_name: iface,
            });
        }

        // Record components are final value bindings: emit as Constants.
        if item.kind == cst::RECORD {
            if let Some(paren) = item.child(cst::HEADER).and_then(|h| h.child(cst::PAREN)) {
                let mut child_scope = scope.to_vec();
                child_scope.push(name.clone());
                for (cname, cstart) in decl_names(paren, src) {
                    let cline = li.line_col(cstart).line;
                    let cid = format!("const::{}", qual_name(module_join, &child_scope, &cname));
                    self.g.upsert_node(
                        cid.clone(),
                        ont::CONSTANT,
                        cname,
                        vec![
                            ("binding", Json::str("record_component")),
                            ("language", Json::str("java")),
                            ("line", Json::U64(cline as u64)),
                        ],
                    );
                    self.g.add_edge(file_id, edge::DECLARES, cid, vec![]);
                }
            }
        }

        if let Some(block) = item.child(cst::ITEM_BLOCK) {
            let owner = Owner {
                name: name.clone(),
                id: id.clone(),
            };
            let mut child_scope = scope.to_vec();
            child_scope.push(name);
            self.walk(
                block,
                file_id,
                module_join,
                &child_scope,
                Some(&owner),
                src,
                li,
                pend_fns,
                pend_ext,
                pend_impl,
            );
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_method<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        owner: Option<&Owner>,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
    ) {
        let (name, name_start) = match method_name(item, src) {
            Some(n) => n,
            None => ("<anonymous>".to_string(), item.span.start),
        };
        let line = li.line_col(name_start).line;
        let qual = qual_name(module_join, scope, &name);
        let id = format!("fn::{qual}#{line}");
        let block = item.child(cst::BLOCK);
        let is_ctor = owner.map(|o| o.name == name).unwrap_or(false);
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("java")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            ("has_body", Json::Bool(block.is_some())),
        ];
        if is_ctor {
            props.push(("is_constructor", Json::Bool(true)));
        }
        if has_modifier(item, src, "static") {
            props.push(("is_static", Json::Bool(true)));
        }
        if let Some(o) = owner {
            props.push(("receiver_type", Json::str(o.name.clone())));
            props.push(("is_method", Json::Bool(true)));
        }
        if let Some(a) = annotations(item, src) {
            props.push(("annotations", a));
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, name.clone(), props);
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);

        self.method_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());
        if let Some(o) = owner {
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
            item,
            owner_type: owner.map(|o| o.name.clone()),
        });
    }

    fn handle_field(
        &mut self,
        item: &Node,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        src: &str,
        li: &LineIndex,
    ) {
        let binding = field_binding(item, src);
        for (name, start) in field_names(item, src) {
            let line = li.line_col(start).line;
            let qual = qual_name(module_join, scope, &name);
            let id = format!("const::{qual}");
            self.g.upsert_node(
                id.clone(),
                ont::CONSTANT,
                name,
                vec![
                    ("binding", Json::str(binding)),
                    ("language", Json::str("java")),
                    ("line", Json::U64(line as u64)),
                ],
            );
            self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
        }
    }

    /// `import [static] a.b.C;` / `import a.b.*;` → an `IMPORTS` edge, plus the
    /// `ExternalDependency`/`DEPENDS_ON` pair when the path is not project-local.
    fn handle_import(&mut self, item: &Node, file_id: &str, src: &str) {
        let header = match item.child(cst::HEADER) {
            Some(h) => h,
            None => return,
        };
        let mut segs: Vec<String> = Vec::new();
        let mut wildcard = false;
        for t in header.tokens() {
            let text = t.span.text(src);
            match text {
                "static" => {}
                "*" => wildcard = true,
                "." => {}
                _ if t.kind == tk::IDENT && !is_keyword(text) => segs.push(text.to_string()),
                _ => {}
            }
        }
        if segs.is_empty() {
            return;
        }
        let mut path_text = segs.join(".");
        if wildcard {
            path_text.push_str(".*");
        }
        let internal = self.is_local_import(&segs);
        if internal {
            let mod_path = segs.join(".");
            let mod_id = format!("mod::{mod_path}");
            self.g.upsert_node(
                mod_id.clone(),
                ont::MODULE,
                segs.last().cloned().unwrap_or_default(),
                vec![("language", Json::str("java"))],
            );
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                mod_id,
                vec![
                    ("path", Json::str(path_text)),
                    ("external", Json::Bool(false)),
                ],
            );
        } else {
            let root = segs[0].clone();
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
                    ("path", Json::str(path_text)),
                    ("external", Json::Bool(true)),
                ],
            );
            self.g
                .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
        }
    }

    /// An import is project-local when its dotted path equals or lies under one of
    /// the packages the project owns. (Top-level-segment matching would be wrong
    /// for Java, where `com.acme` and `com.google` share a root.)
    fn is_local_import(&self, segs: &[String]) -> bool {
        let path = segs.join(".");
        self.local_packages
            .iter()
            .any(|p| pkg_covers(&path, p) || pkg_covers(p, &path))
    }

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        if call.constructor {
            // Constructors are methods named like their class.
            let c = self.methods_of(&call.name, &call.name);
            return if c.is_empty() {
                Resolution {
                    outcome: Outcome::None,
                    level: "external",
                }
            } else {
                mk(c, "constructor")
            };
        }
        if call.method {
            // Receiver scope: `this.m()` / `super.m()` → enclosing type's methods.
            if matches!(call.receiver.as_deref(), Some("this") | Some("super")) {
                if let Some(owner) = &ctx.owner_type {
                    let c = self.methods_of(owner, &call.name);
                    if !c.is_empty() {
                        return mk(c, "receiver");
                    }
                }
            }
            // Other receivers have an unknown type (no inference): fall back to a
            // global match among methods, preserving any ambiguity.
            let c = self.global_methods(&call.name);
            return if c.is_empty() {
                Resolution {
                    outcome: Outcome::None,
                    level: "external",
                }
            } else {
                mk(c, "global_method")
            };
        }
        // Bare call `m(...)`: same-type method first, then any project method.
        if let Some(owner) = &ctx.owner_type {
            let c = self.methods_of(owner, &call.name);
            if !c.is_empty() {
                return mk(c, "receiver");
            }
        }
        let c = self.global_methods(&call.name);
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
            ("method", Json::Bool(call.method)),
            ("resolution", Json::str(res.level)),
        ];
        if call.constructor {
            props.push(("constructor", Json::Bool(true)));
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

    /// Resolve a deferred supertype link into a concrete `EXTENDS`/`IMPLEMENTS`
    /// edge, pointing at the project type when unique, otherwise an explicit
    /// `UnresolvedSymbol` (a JDK/third-party type we cannot see in an airgap).
    fn emit_super(&mut self, pe: &PendingSuper, kind: &'static str, role: &'static str) {
        let target = match self.unique_type(&pe.base_name) {
            Some(id) => id,
            None => {
                let id = unresolved_id(&pe.base_name);
                self.ensure_unresolved(&id, &pe.base_name, role);
                id
            }
        };
        self.g.add_edge(
            pe.type_id.clone(),
            kind,
            target,
            vec![("base_name", Json::str(pe.base_name.clone()))],
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

    fn methods_of(&self, type_name: &str, method: &str) -> Vec<String> {
        self.method_by_type
            .get(&(type_name.to_string(), method.to_string()))
            .cloned()
            .unwrap_or_default()
    }

    fn global_methods(&self, name: &str) -> Vec<String> {
        self.method_by_name.get(name).cloned().unwrap_or_default()
    }

    fn unique_type(&self, name: &str) -> Option<String> {
        match self.type_by_name.get(name) {
            Some(ids) if ids.len() == 1 => Some(ids[0].clone()),
            _ => None,
        }
    }

    /// Add `USES_TYPE` edges for identifiers in a method's signature regions
    /// (type params, return/parameter types, `throws`) that name a unique project
    /// type. Bodies are deliberately excluded — parity with the Python lowering.
    fn emit_type_uses(&mut self, from_id: &str, item: &Node, src: &str) {
        let mut seen: Vec<String> = Vec::new();
        for region in [cst::SIGNATURE, cst::PARAMS, cst::HEADER] {
            let node = match item.child(region) {
                Some(n) => n,
                None => continue,
            };
            for n in node.walk() {
                for t in n.tokens() {
                    if t.kind != tk::IDENT {
                        continue;
                    }
                    let name = t.span.text(src);
                    if is_keyword(name) {
                        continue;
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

/// `package.scope….name` — the dotted qualified name and the basis for node ids.
fn qual_name(module_join: &str, scope: &[String], name: &str) -> String {
    let mut parts: Vec<String> = Vec::new();
    if !module_join.is_empty() {
        parts.push(module_join.to_string());
    }
    parts.extend(scope.iter().cloned());
    parts.push(name.to_string());
    parts.join(".")
}

/// True when dotted package `a` is `b` or a descendant package of `b` (`a`
/// begins with `b` followed by a `.` segment boundary).
fn pkg_covers(a: &str, b: &str) -> bool {
    a == b || (a.len() > b.len() && a.starts_with(b) && a.as_bytes()[b.len()] == b'.')
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

/// True if a member carries a given top-level modifier keyword (e.g. `static`).
fn has_modifier(item: &Node, src: &str, kw: &str) -> bool {
    item.tokens().any(|t| t.span.text(src) == kw)
}

/// The method/constructor name and its byte offset: the last top-level identifier
/// in the `Signature` (a constructor's signature is just the type name).
fn method_name(item: &Node, src: &str) -> Option<(String, u32)> {
    let sig = item.child(cst::SIGNATURE)?;
    let mut last: Option<(String, u32)> = None;
    let mut angle: i32 = 0;
    for t in sig.tokens() {
        let text = t.span.text(src);
        if angle == 0 && t.kind == tk::IDENT && !is_keyword(text) {
            last = Some((text.to_string(), t.span.start));
        }
        angle += angle_delta(text);
        if angle < 0 {
            angle = 0;
        }
    }
    last
}

/// Declared field names (and offsets) from a member's `Signature`. Handles
/// multi-declarators (`int a, b, c`) while skipping identifiers nested in
/// generics. A declarator name is a top-level identifier immediately followed by
/// `,`, `=`, `[`, or the end of the signature.
fn field_names(item: &Node, src: &str) -> Vec<(String, u32)> {
    match item.child(cst::SIGNATURE) {
        Some(sig) => decl_names(sig, src),
        None => Vec::new(),
    }
}

/// Shared declarator-name extraction over a node's top-level token run (used for
/// fields and record components).
fn decl_names(node: &Node, src: &str) -> Vec<(String, u32)> {
    let toks: Vec<&Token> = node
        .children
        .iter()
        .filter_map(|c| match c {
            Child::Token(t) if !t.trivia => Some(t),
            _ => None,
        })
        .collect();
    let mut out = Vec::new();
    let mut angle: i32 = 0;
    for (k, t) in toks.iter().enumerate() {
        let text = t.span.text(src);
        if angle == 0 && t.kind == tk::IDENT && !is_keyword(text) {
            let is_name = matches!(
                toks.get(k + 1).map(|n| n.span.text(src)),
                None | Some(",") | Some("=") | Some("[") | Some(")")
            );
            if is_name {
                out.push((text.to_string(), t.span.start));
            }
        }
        angle += angle_delta(text);
        if angle < 0 {
            angle = 0;
        }
    }
    out
}

/// Classify a field's value binding from its modifiers.
fn field_binding(item: &Node, src: &str) -> &'static str {
    let is_static = has_modifier(item, src, "static");
    let is_final = has_modifier(item, src, "final");
    match (is_static, is_final) {
        (true, true) => "constant",
        (true, false) => "static_field",
        (false, true) => "final_field",
        (false, false) => "field",
    }
}

/// Annotation simple names attached to a declaration, as a JSON array property
/// (the last identifier of each `@a.b.Name`), or `None` when there are none.
fn annotations(item: &Node, src: &str) -> Option<Json> {
    let mut names: Vec<Json> = Vec::new();
    for ann in item.children_of(cst::ANNOTATION) {
        let mut last: Option<&str> = None;
        for t in ann.tokens() {
            if t.kind == tk::IDENT && !is_keyword(t.span.text(src)) {
                last = Some(t.span.text(src));
            }
        }
        if let Some(n) = last {
            names.push(Json::str(n.to_string()));
        }
    }
    if names.is_empty() {
        None
    } else {
        Some(Json::Array(names))
    }
}

/// Simple supertype names from a type's `Header`: `(extends, implements)`. Only
/// `extends`/`implements`/`permits`/`,` at angle-bracket depth 0 are structural,
/// so a type-parameter bound (`<T extends Comparable>`) is never mistaken for a
/// superclass. Each clause's simple name is its last depth-0 identifier.
fn supertypes(item: &Node, src: &str) -> (Vec<String>, Vec<String>) {
    let mut ext: Vec<String> = Vec::new();
    let mut impls: Vec<String> = Vec::new();
    let header = match item.child(cst::HEADER) {
        Some(h) => h,
        None => return (ext, impls),
    };
    let mut mode = 0i32; // 0 none, 1 extends, 2 implements, 3 permits (stop)
    let mut angle: i32 = 0;
    let mut last: Option<String> = None;
    for t in header.tokens() {
        let text = t.span.text(src);
        if angle == 0 {
            match text {
                "extends" => {
                    commit(&mut last, mode, &mut ext, &mut impls);
                    mode = 1;
                }
                "implements" => {
                    commit(&mut last, mode, &mut ext, &mut impls);
                    mode = 2;
                }
                "permits" => {
                    commit(&mut last, mode, &mut ext, &mut impls);
                    mode = 3;
                }
                "," => commit(&mut last, mode, &mut ext, &mut impls),
                _ if t.kind == tk::IDENT && !is_keyword(text) => last = Some(text.to_string()),
                _ => {}
            }
        }
        angle += angle_delta(text);
        if angle < 0 {
            angle = 0;
        }
    }
    commit(&mut last, mode, &mut ext, &mut impls);
    (ext, impls)
}

fn commit(last: &mut Option<String>, mode: i32, ext: &mut Vec<String>, impls: &mut Vec<String>) {
    if let Some(n) = last.take() {
        match mode {
            1 => ext.push(n),
            2 => impls.push(n),
            _ => {}
        }
    }
}

/// Net angle-bracket nesting change a punctuation token contributes (`<` → +1,
/// `>>` → -2), used to keep generic arguments from being read as structure.
fn angle_delta(text: &str) -> i32 {
    let mut d = 0i32;
    for c in text.chars() {
        match c {
            '<' => d += 1,
            '>' => d -= 1,
            _ => {}
        }
    }
    d
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
                ident: t.kind == tk::IDENT,
            }),
            Child::Node(n) => v.push(El::Grp(n)),
        }
    }
    v
}

/// Detect `name(...)`, `recv.name(...)`, and `new Type(...)` call sites over the
/// real token tree, recursing into nested groups but **not** into nested
/// type/method definitions (those are scanned as their own functions). Keywords,
/// annotation targets, and definition names are excluded.
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        // Method/attribute call: `.` name `(...)`.
        if tok_text(&els[i]) == Some(".") {
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
                        out.push(Call {
                            name: tok_text(&els[i + 1]).unwrap_or("").to_string(),
                            method: true,
                            receiver,
                            constructor: false,
                        });
                        i += 3;
                        continue;
                    }
                }
            }
            i += 1;
            continue;
        }
        // Bare call `name(...)` or constructor `new Type(...)`, not preceded by `.`
        // (attribute), `@` (annotation), or a definition keyword.
        if is_ident_el(&els[i]) {
            let prev = if i > 0 { tok_text(&els[i - 1]) } else { None };
            let text = tok_text(&els[i]).unwrap_or("");
            let is_def = matches!(prev, Some("class") | Some("interface") | Some("enum"));
            if prev != Some(".") && prev != Some("@") && !is_def && !is_keyword(text) && i + 1 < n {
                if let Some(g) = grp(&els[i + 1]) {
                    if g.kind == cst::PAREN {
                        out.push(Call {
                            name: text.to_string(),
                            method: false,
                            receiver: None,
                            constructor: prev == Some("new"),
                        });
                    }
                }
            }
        }
        i += 1;
    }
    // Recurse into groups, but never into nested type/method definitions (handled
    // as their own pending functions).
    for e in &els {
        if let Some(g) = grp(e) {
            if !is_definition_node(g.kind) {
                scan_calls(g, src, out);
            }
        }
    }
}

fn is_definition_node(kind: &str) -> bool {
    is_type_decl(kind) || kind == cst::METHOD
}

fn is_type_decl(kind: &str) -> bool {
    matches!(
        kind,
        cst::CLASS | cst::INTERFACE | cst::ENUM | cst::RECORD | cst::ANNOTATION_TYPE
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::java::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("Demo.java", src);
        let file = SourceFile {
            rel_path: "com/demo/Demo.java".to_string(),
            module_path: vec!["com".to_string(), "demo".to_string()],
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    fn call_edges(g: &Graph) -> Vec<&crate::graph::GraphEdge> {
        g.edges().filter(|e| e.kind == edge::CALLS).collect()
    }

    #[test]
    fn emits_type_function_module_nodes() {
        let g = graph_for("class C {\n  void m() {}\n  void f() {}\n}");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "m + f");
        assert_eq!(g.count_nodes_of(ont::TYPE), 1, "class C is a Type");
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "package modules");
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD));
    }

    #[test]
    fn type_kinds_are_honest() {
        for (src, kind) in [
            ("class C {}", "class"),
            ("interface I {}", "interface"),
            ("enum E { A }", "enum"),
            ("record R(int x) {}", "record"),
            ("@interface A {}", "annotation"),
        ] {
            let g = graph_for(src);
            let ty = g
                .nodes()
                .find(|n| n.kind == ont::TYPE)
                .expect("a Type node");
            assert_eq!(
                ty.props.get("type_kind"),
                Some(&Json::str(kind)),
                "for {src}"
            );
            assert_eq!(ty.props.get("language"), Some(&Json::str("java")));
        }
    }

    #[test]
    fn resolves_same_type_call() {
        let g = graph_for("class C {\n  void run() { helper(); }\n  void helper() {}\n}");
        let calls = call_edges(&g);
        let h = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("helper")))
            .expect("a call to helper");
        assert_eq!(h.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(h.props.get("resolution"), Some(&Json::str("receiver")));
    }

    #[test]
    fn this_call_resolves_via_receiver() {
        let g = graph_for("class P {\n  void a() { this.b(); }\n  void b() {}\n}");
        let recv = call_edges(&g)
            .into_iter()
            .find(|e| e.props.get("resolution") == Some(&Json::str("receiver")));
        assert!(recv.is_some(), "this.b() resolves via receiver scope");
    }

    #[test]
    fn constructor_call_resolves() {
        let g = graph_for(
            "class Widget {\n  Widget() {}\n  static Widget make() { return new Widget(); }\n}",
        );
        let ctor = call_edges(&g)
            .into_iter()
            .find(|e| e.props.get("constructor") == Some(&Json::Bool(true)))
            .expect("a constructor call");
        assert_eq!(
            ctor.props.get("resolution"),
            Some(&Json::str("constructor"))
        );
        assert_eq!(ctor.props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for("class C { void run() { mystery(); } }");
        let calls = call_edges(&g);
        assert!(calls
            .iter()
            .any(|e| e.props.get("resolution") == Some(&Json::str("external"))));
        assert!(g.has_node("unresolved::mystery"));
    }

    #[test]
    fn external_import_creates_dependency() {
        let g = graph_for("import java.util.List;\nclass C {}");
        assert!(g.has_node("ext::java"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::java"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn local_import_is_internal() {
        let g = graph_for("import com.demo.Helper;\nclass C {}");
        let imp = g
            .edges()
            .find(|e| e.kind == edge::IMPORTS)
            .expect("an import edge");
        assert_eq!(imp.props.get("external"), Some(&Json::Bool(false)));
    }

    #[test]
    fn extends_and_implements_are_distinct() {
        let g =
            graph_for("interface I {}\nclass Base {}\nclass Derived extends Base implements I {}");
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an EXTENDS edge");
        assert!(ext.from.contains("Derived"));
        assert!(ext.to.contains("Base"));
        let imp = g
            .edges()
            .find(|e| e.kind == edge::IMPLEMENTS)
            .expect("an IMPLEMENTS edge");
        assert!(imp.from.contains("Derived"));
        assert!(imp.to.contains("type::") && imp.to.contains("I"));
    }

    #[test]
    fn generic_bound_is_not_a_supertype() {
        // `<T extends Comparable>` must not produce an EXTENDS to Comparable.
        let g = graph_for("class Box<T extends Comparable<T>> {}");
        assert!(
            !g.edges().any(|e| e.kind == edge::EXTENDS),
            "type-parameter bound is not inheritance"
        );
    }

    #[test]
    fn fields_become_constants() {
        let g = graph_for("class C {\n  static final int MAX = 10;\n  private int count;\n}");
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 2);
        let max = g.nodes().find(|n| n.name == "MAX").expect("the MAX field");
        assert_eq!(max.props.get("binding"), Some(&Json::str("constant")));
        let count = g
            .nodes()
            .find(|n| n.name == "count")
            .expect("the count field");
        assert_eq!(count.props.get("binding"), Some(&Json::str("field")));
    }

    #[test]
    fn multi_declarator_field() {
        let g = graph_for("class C { int a, b, c; }");
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 3, "a, b, c");
    }

    #[test]
    fn record_components_are_constants() {
        let g = graph_for("record Point(int x, int y) {}");
        let names: BTreeSet<String> = g
            .nodes()
            .filter(|n| n.kind == ont::CONSTANT)
            .map(|n| n.name.clone())
            .collect();
        assert!(names.contains("x") && names.contains("y"), "got {names:?}");
    }

    #[test]
    fn type_use_in_signature() {
        let g = graph_for("class Widget {}\nclass Factory {\n  Widget build() { return null; }\n}");
        assert!(
            g.edges()
                .any(|e| e.kind == edge::USES_TYPE && e.to.contains("Widget")),
            "return type should create USES_TYPE"
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src = "import java.util.List;\nclass Base {}\nclass C extends Base {\n  void m() { helper(); }\n  void helper() {}\n}";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
