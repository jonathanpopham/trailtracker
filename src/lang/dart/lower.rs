//! Lower the Dart CST into the canonical graph.
//!
//! This mirrors the Java lowering ([`crate::lang::java::lower`]) — same
//! conservative principles, same shared ontology — adapted to Dart's surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to
//!    a concrete project definition only when a scope level yields exactly one
//!    candidate; several candidates become an ambiguous edge carrying the full
//!    `candidates` set; none resolves to an explicit `UnresolvedSymbol`.
//! 2. **Everything comes from real tokens.** Calls, supertypes, imports, and
//!    type uses are read off the lossless tree, never guessed.
//!
//! Resolution uses a deterministic **scope ladder** (most specific first; the
//! first level with any candidate decides): receiver (`this`/`super`) →
//! enclosing-type methods → global functions. Each edge records which level
//! resolved it, so the call graph stays auditable.
//!
//! Honest mappings (see the IR Atlas):
//!   `class`/`mixin`/`enum`/`extension`/`typedef` → `Type` distinguished by a
//!   `type_kind` property; a function/method/getter/setter/constructor →
//!   `Function` (with `HAS_METHOD` from its enclosing `Type`); a field /
//!   top-level variable / enum constant → `Constant` (distinguished by a
//!   `binding` property); `class X extends Y` → `EXTENDS`; `with M` /
//!   `implements I` → `IMPLEMENTS`; an `import`/`export`/`part` of a `dart:` or
//!   `package:` URI → `IMPORTS` plus `ExternalDependency`/`DEPENDS_ON`; a
//!   relative or own-package URI → `IMPORTS` to the resolved project file.
//!
//! Two honest approximations are documented rather than hidden: a mixin/class
//! `on T` constraint is mapped to `IMPLEMENTS` (the nearest specialization
//! edge), while an `extension on T` target is mapped to `USES_TYPE` (an
//! extension references the type it augments). Named constructors (`C.named`)
//! and `operator` declarations are recorded as ordinary `Function`s.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node, Token};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::dart::lexer::{is_keyword, kind as tk};
use crate::lang::dart::parser::node as cst;
use crate::lang::frontend::SourceFile;

/// Lower a whole project's worth of Dart files into a graph. `manifest_deps` is
/// unused for Dart (the pipeline's manifest reader is Cargo-only); dependencies
/// are discovered from `import`/`export` directives instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    let known_files: BTreeSet<String> = files.iter().map(|f| f.rel_path.clone()).collect();

    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        known_files,
        method_by_name: BTreeMap::new(),
        method_by_type: BTreeMap::new(),
        type_by_name: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("dart"))],
    );

    // Pass B: create definition nodes + structural edges and build symbol tables.
    // Supertype/usage links are deferred to pass C so a base defined later still
    // resolves.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_ext: Vec<PendingSuper> = Vec::new();
    let mut pend_impl: Vec<PendingSuper> = Vec::new();
    let mut pend_uses: Vec<(String, String)> = Vec::new();
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
                ("language", Json::str("dart")),
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
            &mut pend_uses,
        );
    }

    // Pass C: resolve calls (scope ladder), type usages, and supertypes against
    // the now-complete symbol tables.
    for pf in &pend_fns {
        let ctx = Ctx {
            owner_type: pf.owner_type.clone(),
        };
        let mut calls = Vec::new();
        if let Some(block) = pf.item.child(cst::BLOCK) {
            scan_calls(block, pf.source, &mut calls);
        }
        if let Some(arrow) = pf.item.child(cst::ARROW) {
            scan_calls(arrow, pf.source, &mut calls);
        }
        for call in &calls {
            let res = lo.resolve(call, &ctx);
            lo.emit_call(&pf.id, call, res);
        }
        lo.emit_type_uses(&pf.id, pf.item, pf.source);
    }
    for pe in &pend_ext {
        lo.emit_super(pe, edge::EXTENDS, "supertype");
    }
    for pe in &pend_impl {
        lo.emit_super(pe, edge::IMPLEMENTS, "interface");
    }
    for (from, name) in &pend_uses {
        if let Some(tid) = lo.unique_type(name) {
            if &tid != from {
                lo.g.add_edge(
                    from.clone(),
                    edge::USES_TYPE,
                    tid,
                    vec![("type_name", Json::str(name.clone()))],
                );
            }
        }
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    /// Repo-relative paths of every file in the batch (for import resolution).
    known_files: BTreeSet<String>,
    /// Simple name → all function node ids (global call level).
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
    name: String,
    method: bool,
    receiver: Option<String>,
    constructor: bool,
}

/// Resolution context for one enclosing function.
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
    /// module id (or the package id for a file with no module path).
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
                vec![("language", Json::str("dart"))],
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
        pend_uses: &mut Vec<(String, String)>,
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
                    pend_uses,
                );
                continue;
            }
            match item.kind {
                cst::FUNCTION => {
                    self.handle_method(item, file_id, module_join, scope, owner, src, li, pend_fns)
                }
                cst::FIELD => self.handle_field(item, file_id, module_join, scope, src, li),
                cst::DIRECTIVE => self.handle_directive(item, file_id, src),
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
        pend_uses: &mut Vec<(String, String)>,
    ) {
        let name = name_text(item, src).unwrap_or("<anonymous>").to_string();
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(module_join, scope, &name);
        let id = format!("type::{qual}");
        let type_kind = match item.kind {
            cst::CLASS => "class",
            cst::MIXIN => "mixin",
            cst::ENUM => "enum",
            cst::EXTENSION => "extension",
            _ => "typedef",
        };
        let mut props = vec![
            ("type_kind", Json::str(type_kind)),
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("dart")),
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

        // Supertypes / constraints (deferred to pass C).
        let (extends, implements, ons) = supertypes(item, src);
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
        for on in ons {
            if item.kind == cst::EXTENSION {
                // `extension E on T` — E augments T; honestly a type usage.
                pend_uses.push((id.clone(), on));
            } else {
                // `mixin M on T` / class `on` constraint — a specialization bound.
                pend_impl.push(PendingSuper {
                    type_id: id.clone(),
                    base_name: on,
                });
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
                pend_uses,
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
        let has_body = item.child(cst::BLOCK).is_some() || item.child(cst::ARROW).is_some();
        let is_ctor = owner.map(|o| o.name == name).unwrap_or(false);
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("dart")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            ("has_body", Json::Bool(has_body)),
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
                    ("language", Json::str("dart")),
                    ("line", Json::U64(line as u64)),
                ],
            );
            self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
        }
    }

    /// `import|export|part 'uri' …;` → an `IMPORTS` edge. A `dart:`/`package:`
    /// (other-package) URI also yields an `ExternalDependency`/`DEPENDS_ON` pair;
    /// a relative or own-package URI resolves to the project file when known.
    /// `library`/`part of` (no URI) carry no edges.
    fn handle_directive(&mut self, item: &Node, file_id: &str, src: &str) {
        let kw = item
            .tokens()
            .next()
            .map(|t| t.span.text(src))
            .unwrap_or("")
            .to_string();
        let header = match item.child(cst::HEADER) {
            Some(h) => h,
            None => return,
        };
        let uri_tok = header.tokens().find(|t| t.kind == tk::STRING);
        let uri = match uri_tok {
            Some(t) => string_content(t.span.text(src)),
            None => return, // library / part of — no edges
        };

        let importer_rel = file_id.strip_prefix("file::").unwrap_or(file_id);
        match classify_uri(&uri, &self.package, importer_rel) {
            UriTarget::External(root) => {
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
                        ("path", Json::str(uri)),
                        ("directive", Json::str(kw)),
                        ("external", Json::Bool(true)),
                    ],
                );
                self.g
                    .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
            }
            UriTarget::Internal(rel) => {
                if self.known_files.contains(&rel) {
                    let target = format!("file::{rel}");
                    self.g.add_edge(
                        file_id,
                        edge::IMPORTS,
                        target,
                        vec![
                            ("path", Json::str(uri)),
                            ("directive", Json::str(kw)),
                            ("external", Json::Bool(false)),
                        ],
                    );
                } else {
                    let target = unresolved_id(&uri);
                    self.ensure_unresolved(&target, &uri, "import");
                    self.g.add_edge(
                        file_id,
                        edge::IMPORTS,
                        target,
                        vec![
                            ("path", Json::str(uri)),
                            ("directive", Json::str(kw)),
                            ("external", Json::Bool(false)),
                            ("resolved", Json::Bool(false)),
                        ],
                    );
                }
            }
        }
    }

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        if call.constructor {
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
            if matches!(call.receiver.as_deref(), Some("this") | Some("super")) {
                if let Some(owner) = &ctx.owner_type {
                    let c = self.methods_of(owner, &call.name);
                    if !c.is_empty() {
                        return mk(c, "receiver");
                    }
                }
            }
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
    /// `UnresolvedSymbol` (an SDK/third-party type we cannot see in an airgap).
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

    /// Add `USES_TYPE` edges for identifiers in a function's signature regions
    /// (type params, return/parameter types) that name a unique project type.
    /// Bodies are deliberately excluded — parity with the Java/Python lowerings.
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

// --- import URI classification ----------------------------------------------

enum UriTarget {
    /// External root id (a `dart:` library or a third-party package name).
    External(String),
    /// A repo-relative project file path.
    Internal(String),
}

/// Classify an import/export/part URI into an external dependency or a project
/// file. `dart:foo` → external `dart:foo`; `package:other/…` → external `other`;
/// `package:<self>/p` → `lib/p`; a relative path → resolved against the importer.
fn classify_uri(uri: &str, package: &str, importer_rel: &str) -> UriTarget {
    if let Some(rest) = uri.strip_prefix("dart:") {
        return UriTarget::External(format!("dart:{}", rest.split('/').next().unwrap_or(rest)));
    }
    if let Some(rest) = uri.strip_prefix("package:") {
        let (pkg, path) = match rest.split_once('/') {
            Some((p, rest)) => (p, rest),
            None => (rest, ""),
        };
        if pkg == package && !path.is_empty() {
            return UriTarget::Internal(format!("lib/{path}"));
        }
        return UriTarget::External(pkg.to_string());
    }
    UriTarget::Internal(resolve_relative(parent_dir(importer_rel), uri))
}

/// Join a relative URI onto a base directory, collapsing `.`/`..` segments.
fn resolve_relative(base_dir: &str, rel: &str) -> String {
    let mut parts: Vec<&str> = if base_dir.is_empty() {
        Vec::new()
    } else {
        base_dir.split('/').collect()
    };
    for seg in rel.split('/') {
        match seg {
            "" | "." => {}
            ".." => {
                parts.pop();
            }
            s => parts.push(s),
        }
    }
    parts.join("/")
}

fn parent_dir(rel: &str) -> &str {
    match rel.rfind('/') {
        Some(i) => &rel[..i],
        None => "",
    }
}

/// Strip an optional `r` raw prefix and the surrounding quotes (single, double,
/// or triple) from a string-literal's raw text, returning the inner content.
fn string_content(raw: &str) -> String {
    let s = raw
        .strip_prefix('r')
        .or_else(|| raw.strip_prefix('R'))
        .unwrap_or(raw);
    for q in ["'''", "\"\"\""] {
        if s.len() >= 2 * q.len() && s.starts_with(q) && s.ends_with(q) {
            return s[q.len()..s.len() - q.len()].to_string();
        }
    }
    for q in ['\'', '"'] {
        if s.len() >= 2 && s.starts_with(q) && s.ends_with(q) {
            return s[1..s.len() - 1].to_string();
        }
    }
    s.to_string()
}

// --- pure helpers -----------------------------------------------------------

/// `module.scope….name` — the dotted qualified name and the basis for node ids.
fn qual_name(module_join: &str, scope: &[String], name: &str) -> String {
    let mut parts: Vec<String> = Vec::new();
    if !module_join.is_empty() {
        parts.push(module_join.to_string());
    }
    parts.extend(scope.iter().cloned());
    parts.push(name.to_string());
    parts.join(".")
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

/// The function/method/constructor name and its byte offset: the last top-level
/// identifier in the `Signature` (a default constructor's signature is just the
/// type name; a getter's is `… get name`). Identifiers inside generic angle
/// brackets are skipped.
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

/// Declared names (and offsets) from a member's `Signature` — handles
/// multi-declarators (`int a, b, c`) and enum-constant lists while skipping
/// identifiers nested in generics. A name is a top-level identifier immediately
/// followed by `,`, `=`, `[`, `)`, or the end of the signature.
fn field_names(item: &Node, src: &str) -> Vec<(String, u32)> {
    match item.child(cst::SIGNATURE) {
        Some(sig) => decl_names(sig, src),
        None => Vec::new(),
    }
}

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
                None | Some(",") | Some("=") | Some("[") | Some(")") | Some(";")
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
    let is_const = has_modifier(item, src, "const");
    let is_static = has_modifier(item, src, "static");
    let is_final = has_modifier(item, src, "final");
    if is_const {
        "constant"
    } else {
        match (is_static, is_final) {
            (true, true) => "static_final",
            (true, false) => "static_field",
            (false, true) => "final_field",
            (false, false) => "field",
        }
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

/// Simple supertype names from a type's `Header`: `(extends, implements, on)`.
/// Only `extends`/`with`/`implements`/`on`/`,` at angle-bracket depth 0 are
/// structural, so a type-parameter bound (`<T extends Comparable>`) is never
/// mistaken for a superclass. Each clause's simple name is its last depth-0
/// identifier. `with` and `implements` share the `implements` bucket.
fn supertypes(item: &Node, src: &str) -> (Vec<String>, Vec<String>, Vec<String>) {
    let mut ext: Vec<String> = Vec::new();
    let mut impls: Vec<String> = Vec::new();
    let mut ons: Vec<String> = Vec::new();
    let header = match item.child(cst::HEADER) {
        Some(h) => h,
        None => return (ext, impls, ons),
    };
    let mut mode = 0i32; // 0 none, 1 extends, 2 with/implements, 3 on
    let mut angle: i32 = 0;
    let mut last: Option<String> = None;
    for t in header.tokens() {
        let text = t.span.text(src);
        if angle == 0 {
            match text {
                "extends" => {
                    commit(&mut last, mode, &mut ext, &mut impls, &mut ons);
                    mode = 1;
                }
                "with" | "implements" => {
                    commit(&mut last, mode, &mut ext, &mut impls, &mut ons);
                    mode = 2;
                }
                "on" => {
                    commit(&mut last, mode, &mut ext, &mut impls, &mut ons);
                    mode = 3;
                }
                "," => commit(&mut last, mode, &mut ext, &mut impls, &mut ons),
                _ if t.kind == tk::IDENT && !is_keyword(text) => last = Some(text.to_string()),
                _ => {}
            }
        }
        angle += angle_delta(text);
        if angle < 0 {
            angle = 0;
        }
    }
    commit(&mut last, mode, &mut ext, &mut impls, &mut ons);
    (ext, impls, ons)
}

fn commit(
    last: &mut Option<String>,
    mode: i32,
    ext: &mut Vec<String>,
    impls: &mut Vec<String>,
    ons: &mut Vec<String>,
) {
    if let Some(n) = last.take() {
        match mode {
            1 => ext.push(n),
            2 => impls.push(n),
            3 => ons.push(n),
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
/// type/function definitions (those are scanned as their own functions).
/// Keywords, annotation targets, and definition names are excluded.
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        // Method / property call: `.` name `(...)`.
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
        // (property access), `@` (annotation), or a definition keyword.
        if is_ident_el(&els[i]) {
            let prev = if i > 0 { tok_text(&els[i - 1]) } else { None };
            let text = tok_text(&els[i]).unwrap_or("");
            let is_def = matches!(
                prev,
                Some("class") | Some("mixin") | Some("enum") | Some("extension")
            );
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
    for e in &els {
        if let Some(g) = grp(e) {
            if !is_definition_node(g.kind) {
                scan_calls(g, src, out);
            }
        }
    }
}

fn is_definition_node(kind: &str) -> bool {
    is_type_decl(kind) || kind == cst::FUNCTION
}

fn is_type_decl(kind: &str) -> bool {
    matches!(
        kind,
        cst::CLASS | cst::MIXIN | cst::ENUM | cst::EXTENSION | cst::TYPEDEF
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::dart::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("demo.dart", src);
        let file = SourceFile {
            rel_path: "lib/demo.dart".to_string(),
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
    fn emits_type_function_nodes() {
        let g = graph_for("class C {\n  void m() {}\n  void f() {}\n}");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "m + f");
        assert_eq!(g.count_nodes_of(ont::TYPE), 1, "class C is a Type");
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD));
    }

    #[test]
    fn type_kinds_are_honest() {
        for (src, kind) in [
            ("class C {}", "class"),
            ("mixin M {}", "mixin"),
            ("enum E { a }", "enum"),
            ("extension X on int {}", "extension"),
            ("typedef T = int;", "typedef"),
        ] {
            let g = graph_for(src);
            let ty = g
                .nodes()
                .find(|n| n.kind == ont::TYPE)
                .unwrap_or_else(|| panic!("a Type node for {src}"));
            assert_eq!(
                ty.props.get("type_kind"),
                Some(&Json::str(kind)),
                "for {src}"
            );
            assert_eq!(ty.props.get("language"), Some(&Json::str("dart")));
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
    fn arrow_body_calls_are_scanned() {
        let g = graph_for("class C {\n  int a() => b();\n  int b() => 0;\n}");
        let calls = call_edges(&g);
        assert!(
            calls
                .iter()
                .any(|e| e.props.get("callee") == Some(&Json::str("b"))),
            "call in arrow body should be found"
        );
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
    fn dart_sdk_import_is_external() {
        let g = graph_for("import 'dart:math';\nclass C {}");
        assert!(g.has_node("ext::dart:math"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::dart:math"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn package_import_is_external_by_package_name() {
        let g = graph_for("import 'package:meta/meta.dart';\nclass C {}");
        assert!(g.has_node("ext::meta"));
    }

    #[test]
    fn extends_and_implements_are_distinct() {
        let g = graph_for(
            "abstract class I {}\nclass Base {}\nclass Derived extends Base implements I {}",
        );
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
        assert!(imp.to.contains("I"));
    }

    #[test]
    fn with_clause_is_implements() {
        let g = graph_for("mixin M {}\nclass C with M {}");
        let imp = g
            .edges()
            .find(|e| e.kind == edge::IMPLEMENTS && e.to.contains("M"))
            .expect("with M maps to IMPLEMENTS");
        assert!(imp.from.contains("C"));
    }

    #[test]
    fn extension_on_is_use_type() {
        let g = graph_for("class Foo {}\nextension Bar on Foo { void x() {} }");
        assert!(
            g.edges()
                .any(|e| e.kind == edge::USES_TYPE && e.to.contains("Foo")),
            "extension on Foo should USES_TYPE Foo"
        );
    }

    #[test]
    fn generic_bound_is_not_a_supertype() {
        let g = graph_for("class Box<T extends Comparable<T>> {}");
        assert!(
            !g.edges().any(|e| e.kind == edge::EXTENDS),
            "type-parameter bound is not inheritance"
        );
    }

    #[test]
    fn fields_become_constants() {
        let g = graph_for(
            "class C {\n  static const int max = 10;\n  final int count = 0;\n  int n = 1;\n}",
        );
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 3);
        let max = g.nodes().find(|n| n.name == "max").expect("the max field");
        assert_eq!(max.props.get("binding"), Some(&Json::str("constant")));
        let count = g
            .nodes()
            .find(|n| n.name == "count")
            .expect("the count field");
        assert_eq!(count.props.get("binding"), Some(&Json::str("final_field")));
    }

    #[test]
    fn enum_constants_become_constants() {
        let g = graph_for("enum Color { red, green, blue }");
        let names: BTreeSet<String> = g
            .nodes()
            .filter(|n| n.kind == ont::CONSTANT)
            .map(|n| n.name.clone())
            .collect();
        assert!(
            names.contains("red") && names.contains("green") && names.contains("blue"),
            "got {names:?}"
        );
    }

    #[test]
    fn top_level_function_has_no_owner() {
        let g = graph_for("void main() { helper(); }\nvoid helper() {}");
        let main = g.nodes().find(|n| n.name == "main").expect("main fn");
        assert_eq!(main.props.get("is_method"), None);
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
        let src = "import 'dart:math';\nclass Base {}\nclass C extends Base {\n  void m() { helper(); }\n  void helper() {}\n}";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
