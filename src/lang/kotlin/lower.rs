//! Lower the Kotlin CST into the canonical graph.
//!
//! This mirrors the Python lowering ([`crate::lang::python::lower`]) — same
//! conservative principles, same shared ontology — adapted to Kotlin's surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to
//!    a concrete project definition only when a scope level yields exactly one
//!    candidate; several candidates become an ambiguous edge carrying the full
//!    `candidates` set; none resolves to an explicit `UnresolvedSymbol`.
//! 2. **Everything comes from real tokens.** Calls, supertypes, imports, and type
//!    uses are read off the lossless tree, never guessed. There is no LLM in the
//!    airgapped runtime to fill gaps.
//!
//! Resolution uses a deterministic **scope ladder** (most specific first; the
//! first level with any candidate decides): receiver (`this`) → local package →
//! file imports → global. Each edge records which level resolved it, so the call
//! graph stays auditable.
//!
//! Honest mappings (see the IR Atlas):
//!   `fun` → `Function` (a member fun → `HAS_METHOD` from its enclosing type);
//!   `class`/`data class` → `Type` (`type_kind: class`), `enum class` →
//!   (`type_kind: enum`), `interface` → (`type_kind: interface`), `object`/
//!   `companion object` → (`type_kind: object`), `typealias` → (`type_kind:
//!   alias`); top-level `val`/`var` → `Constant`; `import` → `IMPORTS` (plus
//!   `ExternalDependency`/`DEPENDS_ON` for non-project roots).
//!
//! Inheritance honors the Atlas's distinction between `EXTENDS` (is-a / subclass)
//! and `IMPLEMENTS` (conforms-to). Kotlin writes both in one `:`-separated
//! supertype list, but a *superclass* is the only supertype that may carry a
//! constructor invocation (`: Base(args)`) — interfaces never can — so a supertype
//! with a constructor-call `()` lowers to `EXTENDS` and a bare supertype to
//! `IMPLEMENTS`. (Interface-to-interface inheritance therefore surfaces as
//! `IMPLEMENTS`; both sit under the `SPECIALIZES` super-relation, so coarse
//! queries are unaffected. Noted as a known nuance.)

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node, Token};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::kotlin::lexer::{is_keyword, kind as tk};
use crate::lang::kotlin::parser::node as cst;

/// Lower a whole project's worth of Kotlin files into a graph. `manifest_deps` is
/// unused (the pipeline's manifest reader is Cargo-only); dependencies are
/// discovered from `import` statements instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    // Per-file module path, derived from the in-file `package` declaration (the
    // Kotlin source of truth) and falling back to the path-based module path.
    let module_paths: Vec<Vec<String>> = files
        .iter()
        .map(|f| {
            let pkg = package_segs(f.root, f.source);
            if pkg.is_empty() {
                f.module_path.clone()
            } else {
                pkg
            }
        })
        .collect();

    // Project-local roots: the package plus every module segment. An import whose
    // first segment is one of these is intra-project, not an external dependency.
    let mut local_roots: BTreeSet<String> = BTreeSet::new();
    local_roots.insert(package.to_string());
    for segs in &module_paths {
        for seg in segs {
            local_roots.insert(seg.clone());
        }
    }

    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        local_roots,
        fn_by_name: BTreeMap::new(),
        method_by_name: BTreeMap::new(),
        fn_by_module: BTreeMap::new(),
        method_by_type: BTreeMap::new(),
        type_by_name: BTreeMap::new(),
        imports: Vec::new(),
        cur_file: 0,
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("kotlin"))],
    );

    // Pass B: create definition nodes + structural edges, build symbol tables and
    // per-file import maps. Inheritance is deferred to pass C so a supertype
    // defined later in the project still resolves.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_super: Vec<PendingSupertype> = Vec::new();
    for (idx, f) in files.iter().enumerate() {
        lo.imports.push(BTreeMap::new());
        lo.cur_file = idx;
        let li = LineIndex::new(f.source);
        let segs = &module_paths[idx];
        let module_join = segs.join(".");
        let leaf = lo.ensure_modules(segs);
        let file_id = format!("file::{}", f.rel_path);
        lo.g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("kotlin")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(leaf, edge::CONTAINS, file_id.clone(), vec![]);
        lo.walk_items(
            f.root,
            &file_id,
            &module_join,
            &[],
            None,
            false,
            f.source,
            &li,
            &mut pend_fns,
            &mut pend_super,
        );
    }

    // Pass C: resolve calls (scope ladder), type usages, and supertypes against
    // the now-complete symbol tables.
    for pf in &pend_fns {
        let ctx = Ctx {
            module_join: pf.module_join.clone(),
            owner_type: pf.owner_type.clone(),
            imports: lo.imports.get(pf.file_idx).cloned().unwrap_or_default(),
        };
        if let Some(body) = pf.body {
            let mut calls = Vec::new();
            scan_calls(body, pf.source, &mut calls);
            for call in &calls {
                let res = lo.resolve(call, &ctx);
                lo.emit_call(&pf.id, call, res);
            }
        }
        if let Some(sig) = pf.signature {
            lo.emit_type_uses(&pf.id, sig, pf.source);
        }
    }
    for ps in &pend_super {
        lo.emit_supertype(ps);
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    local_roots: BTreeSet<String>,
    /// Simple name → all function node ids (global level).
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// Simple name → member-function node ids only (global method-call level).
    method_by_name: BTreeMap<String, Vec<String>>,
    /// (module_join, name) → function ids (local-package level).
    fn_by_module: BTreeMap<(String, String), Vec<String>>,
    /// (type_name, method_name) → method ids (receiver level).
    method_by_type: BTreeMap<(String, String), Vec<String>>,
    /// Simple name → type node ids.
    type_by_name: BTreeMap<String, Vec<String>>,
    /// Per-file import maps: imported leaf name → full dotted path segments.
    imports: Vec<BTreeMap<String, Vec<String>>>,
    cur_file: usize,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    body: Option<&'a Node>,
    signature: Option<&'a Node>,
    module_join: String,
    owner_type: Option<String>,
    file_idx: usize,
}

/// A deferred supertype link (`: Base(...)` or `: Iface`), resolved in pass C.
struct PendingSupertype {
    type_id: String,
    super_name: String,
    /// True if the supertype carried a constructor call → a superclass.
    is_ctor: bool,
}

/// The enclosing type while walking, for members (`HAS_METHOD`, receiver scope).
struct Owner {
    name: String,
    id: String,
}

/// A detected call site over the lossless tree.
struct Call {
    /// The called name (final attribute or bare name).
    name: String,
    /// True for `recv.name(...)` calls.
    method: bool,
    /// Immediate receiver identifier (`this`, a variable) for method calls.
    receiver: Option<String>,
}

/// Resolution context for one enclosing function.
struct Ctx {
    module_join: String,
    owner_type: Option<String>,
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

    /// Ensure the `Package → mod::a → mod::a.b …` chain exists and return the leaf
    /// module id (or the package id for a file with no package declaration).
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
                vec![("language", Json::str("kotlin"))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    /// Walk a declaration container (a `SourceFile` or `ItemBlock`), creating
    /// definition nodes and recursing into nested type bodies. `owner` is the
    /// nearest enclosing type (members become `HAS_METHOD`); `in_function` is
    /// unused for Kotlin bodies (function bodies are opaque token trees, like the
    /// Rust front end) but kept for parity with the constant-emission gate.
    #[allow(clippy::too_many_arguments)]
    fn walk_items<'a>(
        &mut self,
        container: &'a Node,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        owner: Option<&Owner>,
        in_function: bool,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_super: &mut Vec<PendingSupertype>,
    ) {
        for item in container.child_nodes() {
            match item.kind {
                cst::FUNCTION => {
                    self.handle_fn(item, file_id, module_join, scope, owner, src, li, pend_fns)
                }
                cst::CLASS | cst::INTERFACE | cst::OBJECT => self.handle_type(
                    item,
                    file_id,
                    module_join,
                    scope,
                    src,
                    li,
                    pend_fns,
                    pend_super,
                ),
                cst::TYPE_ALIAS => {
                    self.handle_typealias(item, file_id, module_join, scope, src, li)
                }
                cst::IMPORT => self.handle_import(item, file_id, src),
                cst::PROPERTY => {
                    // Top-level val/var → Constant; member properties (inside a
                    // type body) are fields and are not emitted, mirroring Python.
                    if !in_function && owner.is_none() {
                        self.handle_property(item, file_id, module_join, src, li);
                    }
                }
                _ => {}
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_fn<'a>(
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
        let name_tok = fn_name_token(item);
        let name = name_tok
            .map(|t| t.span.text(src))
            .unwrap_or("<anonymous>")
            .to_string();
        let line = li
            .line_col(name_tok.map(|t| t.span.start).unwrap_or(item.span.start))
            .line;
        let qual = qual_name(module_join, scope, &name);
        let id = format!("fn::{qual}#{line}");
        let body = item
            .child(cst::BLOCK)
            .or_else(|| item.child(cst::EXPR_BODY));
        let signature = item.child(cst::SIGNATURE);
        let mods = modifier_set(item, src);
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("kotlin")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            ("has_body", Json::Bool(body.is_some())),
        ];
        if mods.contains("suspend") {
            props.push(("is_suspend", Json::Bool(true)));
        }
        if mods.contains("override") {
            props.push(("is_override", Json::Bool(true)));
        }
        if let Some(a) = annotation_names(item, src) {
            props.push(("annotations", a));
        }
        if let Some(o) = owner {
            props.push(("receiver_type", Json::str(o.name.clone())));
            props.push(("is_method", Json::Bool(true)));
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, name.clone(), props);
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);

        // Indexes for the resolution ladder.
        self.fn_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());
        self.fn_by_module
            .entry((module_join.to_string(), name.clone()))
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
            body,
            signature,
            module_join: module_join.to_string(),
            owner_type: owner.map(|o| o.name.clone()),
            file_idx: self.cur_file,
        });
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
        pend_super: &mut Vec<PendingSupertype>,
    ) {
        let name_tok = name_token(item);
        let name = name_tok
            .map(|t| t.span.text(src))
            .unwrap_or("<anonymous>")
            .to_string();
        let line = li
            .line_col(name_tok.map(|t| t.span.start).unwrap_or(item.span.start))
            .line;
        let qual = qual_name(module_join, scope, &name);
        let id = format!("type::{qual}");
        let mods = modifier_set(item, src);
        let type_kind = match item.kind {
            cst::INTERFACE => "interface",
            cst::OBJECT => "object",
            _ if mods.contains("enum") => "enum",
            _ if mods.contains("annotation") => "annotation",
            _ => "class",
        };
        let mut props = vec![
            ("type_kind", Json::str(type_kind)),
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("kotlin")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
        ];
        if mods.contains("data") {
            props.push(("is_data", Json::Bool(true)));
        }
        if mods.contains("sealed") {
            props.push(("is_sealed", Json::Bool(true)));
        }
        if let Some(a) = annotation_names(item, src) {
            props.push(("annotations", a));
        }
        self.g
            .upsert_node(id.clone(), ont::TYPE, name.clone(), props);
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());

        // Supertypes (defer the EXTENDS/IMPLEMENTS resolution to pass C).
        for (super_name, is_ctor) in class_supertypes(item, src) {
            pend_super.push(PendingSupertype {
                type_id: id.clone(),
                super_name,
                is_ctor,
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
                module_join,
                &child_scope,
                Some(&owner),
                false,
                src,
                li,
                pend_fns,
                pend_super,
            );
        }
    }

    fn handle_typealias(
        &mut self,
        item: &Node,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        src: &str,
        li: &LineIndex,
    ) {
        let name_tok = name_token(item);
        let name = match name_tok {
            Some(t) => t.span.text(src).to_string(),
            None => return,
        };
        let line = li
            .line_col(name_tok.map(|t| t.span.start).unwrap_or(0))
            .line;
        let qual = qual_name(module_join, scope, &name);
        let id = format!("type::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str("alias")),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("kotlin")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name.entry(name).or_default().push(id);
    }

    /// `import a.b.C` / `import a.b.*` / `import a.b.C as D`.
    fn handle_import(&mut self, item: &Node, file_id: &str, src: &str) {
        let mut segs: Vec<String> = Vec::new();
        let mut alias: Option<String> = None;
        let mut star = false;
        let mut expect_alias = false;
        let mut first = true;
        for t in item.tokens() {
            let txt = t.span.text(src);
            if t.kind == tk::IDENT {
                if first && txt == "import" {
                    first = false;
                    continue;
                }
                first = false;
                if txt == "as" {
                    expect_alias = true;
                } else if expect_alias {
                    alias = Some(txt.to_string());
                    expect_alias = false;
                } else {
                    segs.push(txt.to_string());
                }
            } else if txt == "*" {
                star = true;
            }
        }
        if segs.is_empty() {
            return;
        }
        let leaf = alias.unwrap_or_else(|| {
            if star {
                segs[0].clone()
            } else {
                segs.last().cloned().unwrap()
            }
        });
        let mut path_text = segs.join(".");
        if star {
            path_text.push_str(".*");
        }
        if !star {
            self.imports[self.cur_file].insert(leaf, segs.clone());
        }
        self.emit_import_edge(file_id, &segs, &path_text);
    }

    /// Emit the `IMPORTS` edge for one imported path, plus the
    /// `ExternalDependency`/`DEPENDS_ON` pair when the root is not project-local.
    fn emit_import_edge(&mut self, file_id: &str, segs: &[String], path_text: &str) {
        let root = match segs.first() {
            Some(r) => r.clone(),
            None => return,
        };
        if self.local_roots.contains(&root) {
            let mod_id = format!("mod::{root}");
            self.g.upsert_node(
                mod_id.clone(),
                ont::MODULE,
                root,
                vec![("language", Json::str("kotlin"))],
            );
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

    /// Top-level `val`/`var NAME … ` → a `Constant`.
    fn handle_property(
        &mut self,
        item: &Node,
        file_id: &str,
        module_join: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let name_tok = name_token(item);
        let name = match name_tok {
            Some(t) => t.span.text(src).to_string(),
            None => return,
        };
        let line = li
            .line_col(name_tok.map(|t| t.span.start).unwrap_or(0))
            .line;
        let mods = modifier_set(item, src);
        let is_var = item
            .tokens()
            .any(|t| t.kind == tk::IDENT && t.span.text(src) == "var");
        let id = format!("const::{}", qual_name(module_join, &[], &name));
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            name,
            vec![
                ("binding", Json::str(if is_var { "var" } else { "val" })),
                ("is_const", Json::Bool(mods.contains("const"))),
                ("language", Json::str("kotlin")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
    }

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        if call.method {
            // Receiver scope: `this.m()` → enclosing type's methods.
            if call.receiver.as_deref() == Some("this") {
                if let Some(owner) = &ctx.owner_type {
                    let c = self.methods_of(owner, &call.name);
                    if !c.is_empty() {
                        return mk(c, "receiver");
                    }
                }
            }
            // Unknown receiver type (no inference). The honest candidate set is
            // every same-name method PLUS every same-name free function — a Kotlin
            // member call can also reach a top-level extension function
            // (`fun T.f()`), which is indexed as a plain function.
            // `mk` resolves a singleton and preserves any wider set as an
            // explicit ambiguity; it never guesses.
            let mut c = self.global_methods(&call.name);
            if !c.is_empty() {
                // Same-name free functions are counterevidence: they widen the
                // candidate set (forcing ambiguity), but a member call is never
                // resolved to a free function on name evidence alone.
                for id in self.global_fns(&call.name) {
                    if !c.contains(&id) {
                        c.push(id);
                    }
                }
            }
            return if c.is_empty() {
                Resolution {
                    outcome: Outcome::None,
                    level: "external",
                }
            } else {
                mk(c, "global_method")
            };
        }

        // Local package.
        let c = self.fns_in_module(&ctx.module_join, &call.name);
        if !c.is_empty() {
            return mk(c, "local");
        }
        // File imports: a bare name brought in via `import pkg.name`.
        if let Some(segs) = ctx.imports.get(&call.name) {
            if let Some(modj) = self.import_module_join(segs) {
                let c = self.fns_in_module(&modj, &call.name);
                if !c.is_empty() {
                    return mk(c, "import");
                }
            }
        }
        // Global.
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
            ("method", Json::Bool(call.method)),
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

    /// Resolve a deferred supertype into a concrete `EXTENDS` (superclass) or
    /// `IMPLEMENTS` (interface) edge, pointing at the project type when unique,
    /// otherwise an explicit `UnresolvedSymbol` (a stdlib/third-party supertype we
    /// cannot see in an airgap).
    fn emit_supertype(&mut self, ps: &PendingSupertype) {
        let target = match self.unique_type(&ps.super_name) {
            Some(id) => id,
            None => {
                let id = unresolved_id(&ps.super_name);
                self.ensure_unresolved(&id, &ps.super_name, "supertype");
                id
            }
        };
        let kind = if ps.is_ctor {
            edge::EXTENDS
        } else {
            edge::IMPLEMENTS
        };
        let prop_key = if ps.is_ctor {
            "base_name"
        } else {
            "trait_name"
        };
        self.g.add_edge(
            ps.type_id.clone(),
            kind,
            target,
            vec![(prop_key, Json::str(ps.super_name.clone()))],
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

    fn fns_in_module(&self, module_join: &str, name: &str) -> Vec<String> {
        self.fn_by_module
            .get(&(module_join.to_string(), name.to_string()))
            .cloned()
            .unwrap_or_default()
    }

    fn global_fns(&self, name: &str) -> Vec<String> {
        self.fn_by_name.get(name).cloned().unwrap_or_default()
    }

    fn global_methods(&self, name: &str) -> Vec<String> {
        self.method_by_name.get(name).cloned().unwrap_or_default()
    }

    /// Module-join for an imported symbol's defining module (`segs` includes the
    /// leaf name). `None` when the import points outside the project.
    fn import_module_join(&self, segs: &[String]) -> Option<String> {
        if segs.len() < 2 {
            return None;
        }
        let module_segs = &segs[..segs.len() - 1];
        if self.local_roots.contains(&module_segs[0]) {
            Some(module_segs.join("."))
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

    /// Add `USES_TYPE` edges for identifiers in `region` (a function `Signature`,
    /// i.e. parameter/return type references) that name a unique project type.
    fn emit_type_uses(&mut self, from_id: &str, region: &Node, src: &str) {
        let mut seen: Vec<String> = Vec::new();
        for n in region.walk() {
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

fn mk(ids: Vec<String>, level: &'static str) -> Resolution {
    let outcome = if ids.len() == 1 {
        Outcome::One(ids[0].clone())
    } else {
        Outcome::Many(ids)
    };
    Resolution { outcome, level }
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

/// Dotted segments of a file's `package` declaration, or `[]` if there is none.
fn package_segs(root: &Node, src: &str) -> Vec<String> {
    for item in root.child_nodes() {
        if item.kind == cst::PACKAGE {
            let mut segs = Vec::new();
            for t in item.tokens() {
                let txt = t.span.text(src);
                if t.kind == tk::IDENT && txt != "package" {
                    segs.push(txt.to_string());
                }
            }
            return segs;
        }
    }
    Vec::new()
}

/// The `Name` node's first token, for type/property/typealias declarations.
fn name_token(item: &Node) -> Option<&Token> {
    item.child(cst::NAME).and_then(|n| n.tokens().next())
}

/// The function name token: the last identifier in the `Signature` before the
/// value-parameter list `(`. This correctly skips an extension receiver
/// (`fun Foo.bar()` → `bar`) and type parameters (`fun <T> f()` → `f`).
fn fn_name_token(item: &Node) -> Option<&Token> {
    let sig = item.child(cst::SIGNATURE)?;
    let mut last_ident: Option<&Token> = None;
    for ch in &sig.children {
        match ch {
            Child::Token(t) if t.kind == tk::IDENT => last_ident = Some(t),
            Child::Node(n) if n.kind == cst::PAREN => return last_ident,
            _ => {}
        }
    }
    last_ident
}

/// The set of modifier-keyword texts appearing as direct tokens of a declaration
/// node (before its keyword): `data`, `enum`, `sealed`, `suspend`, `override`, …
fn modifier_set(item: &Node, src: &str) -> BTreeSet<String> {
    let mut set = BTreeSet::new();
    for t in item.tokens() {
        if t.kind == tk::IDENT {
            set.insert(t.span.text(src).to_string());
        }
    }
    set
}

/// Annotation names attached to a declaration (the last identifier of each
/// `@expr`, e.g. `Serializable` from `@Serializable` or `Inject` from
/// `@field:Inject`), or `None` when there are none.
fn annotation_names(item: &Node, src: &str) -> Option<Json> {
    let mut names: Vec<Json> = Vec::new();
    for a in item.children_of(cst::ANNOTATION) {
        let mut last: Option<&str> = None;
        for t in a.tokens() {
            let txt = t.span.text(src);
            if t.kind == tk::IDENT && !is_keyword(txt) {
                last = Some(txt);
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

/// One element of a type header (a token or a balanced group), used for
/// supertype extraction.
enum HdrEl<'a> {
    Tok(&'static str, &'a str),
    Grp(&'static str),
}

/// Supertypes from a `class`/`interface`/`object` header, as `(name, is_ctor)`.
/// `is_ctor` is true when the supertype carries a constructor call (`Base(args)`),
/// which in Kotlin can only be a superclass. The supertype list begins at the
/// first top-level `:` (skipping type-parameter bounds inside `<...>` and the
/// primary-constructor parameter list, which is a balanced group) and ends at a
/// `where` clause or the body.
fn class_supertypes(item: &Node, src: &str) -> Vec<(String, bool)> {
    let header = match item.child(cst::HEADER) {
        Some(h) => h,
        None => return Vec::new(),
    };
    let mut elems: Vec<HdrEl> = Vec::new();
    for ch in &header.children {
        match ch {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => elems.push(HdrEl::Tok(t.kind, t.span.text(src))),
            Child::Node(n) => elems.push(HdrEl::Grp(n.kind)),
        }
    }

    // Locate the supertype-list `:` at angle depth 0.
    let mut angle = 0i32;
    let mut start = None;
    for (idx, e) in elems.iter().enumerate() {
        if let HdrEl::Tok(_, txt) = e {
            match *txt {
                "<" => angle += 1,
                ">" => angle -= 1,
                ":" if angle <= 0 => {
                    start = Some(idx + 1);
                    break;
                }
                _ => {}
            }
        }
    }
    let start = match start {
        Some(s) => s,
        None => return Vec::new(),
    };

    // Split the remainder into comma-separated entries at angle depth 0.
    let mut result: Vec<(String, bool)> = Vec::new();
    let mut cur_name: Option<String> = None;
    let mut cur_ctor = false;
    let mut a = 0i32;
    for e in &elems[start..] {
        match e {
            HdrEl::Tok(kind, txt) => match *txt {
                "<" => a += 1,
                ">" => a -= 1,
                "where" if a <= 0 => break,
                "," if a <= 0 => {
                    if let Some(n) = cur_name.take() {
                        result.push((n, cur_ctor));
                    }
                    cur_ctor = false;
                }
                _ => {
                    if a <= 0 && *kind == tk::IDENT && !cur_ctor && !is_keyword(txt) {
                        // The name is the last identifier before any constructor
                        // call; keep overwriting until a `(` group is seen.
                        cur_name = Some(txt.to_string());
                    }
                }
            },
            HdrEl::Grp(kind) => {
                if a <= 0 && *kind == cst::PAREN && cur_name.is_some() {
                    cur_ctor = true;
                }
            }
        }
    }
    if let Some(n) = cur_name.take() {
        result.push((n, cur_ctor));
    }
    result
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

/// Detect `name(...)` and `recv.name(...)` call sites over the real token tree,
/// recursing into nested groups but **not** into nested type/function definition
/// nodes. Keywords are excluded, as is a name immediately following a definition
/// keyword. Generic call forms (`name<T>(...)`) are conservatively not matched —
/// under-reporting rather than guessing.
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        // Method/qualified call: `.` name `(...)`.
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
                        });
                        i += 3;
                        continue;
                    }
                }
            }
            i += 1;
            continue;
        }
        // Bare call: name `(...)`, not preceded by `.` (qualified) or by a
        // definition keyword.
        if is_ident_el(&els[i]) {
            let prev = if i > 0 { tok_text(&els[i - 1]) } else { None };
            let text = tok_text(&els[i]).unwrap_or("");
            let is_def = matches!(
                prev,
                Some("fun") | Some("class") | Some("object") | Some("interface")
            );
            if prev != Some(".") && !is_def && !is_keyword(text) && i + 1 < n {
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
    // Recurse into groups, but never into nested definition nodes (those are
    // handled as their own pending functions / types).
    for e in &els {
        if let Some(g) = grp(e) {
            if !matches!(
                g.kind,
                cst::FUNCTION | cst::CLASS | cst::INTERFACE | cst::OBJECT
            ) {
                scan_calls(g, src, out);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::kotlin::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("Main.kt", src);
        let file = SourceFile {
            rel_path: "Main.kt".to_string(),
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
    fn emits_function_type_module_nodes() {
        let g = graph_for("package p\nclass C {\n    fun m() {}\n}\n\nfun f() {}\n");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "f + C.m");
        assert_eq!(g.count_nodes_of(ont::TYPE), 1, "class C is a Type");
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "module p");
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD), "C has m");
    }

    #[test]
    fn type_kinds_map_honestly() {
        let g =
            graph_for("enum class E { A, B }\ninterface I\nobject O\ndata class D(val x: Int)\n");
        let kinds: BTreeSet<String> = g
            .nodes()
            .filter(|n| n.kind == ont::TYPE)
            .filter_map(|n| n.props.get("type_kind"))
            .filter_map(|j| match j {
                Json::Str(s) => Some(s.clone()),
                _ => None,
            })
            .collect();
        assert!(kinds.contains("enum"), "enum class: {kinds:?}");
        assert!(kinds.contains("interface"), "interface: {kinds:?}");
        assert!(kinds.contains("object"), "object: {kinds:?}");
        assert!(kinds.contains("class"), "data class: {kinds:?}");
    }

    #[test]
    fn extension_function_name_skips_receiver() {
        let g = graph_for("fun String.shout(): String = this\n");
        let f = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION)
            .expect("a function");
        assert_eq!(f.name, "shout", "receiver must not be taken as the name");
    }

    #[test]
    fn resolves_unique_local_call() {
        let g = graph_for(
            "package p\nfun add(a: Int, b: Int): Int = a + b\nfun run() {\n    add(1, 2)\n}\n",
        );
        let calls = call_edges(&g);
        let add = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("add")))
            .expect("a call to add");
        assert!(add.to.starts_with("fn::p.add"), "resolved to {}", add.to);
        assert_eq!(add.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(add.props.get("resolution"), Some(&Json::str("local")));
    }

    #[test]
    fn this_method_resolves_via_receiver() {
        let g = graph_for("class P {\n    fun a() {\n        this.b()\n    }\n    fun b() {}\n}\n");
        let calls = call_edges(&g);
        let recv = calls
            .iter()
            .find(|e| e.props.get("resolution") == Some(&Json::str("receiver")));
        assert!(recv.is_some(), "this.b() should resolve via receiver scope");
        assert_eq!(recv.unwrap().props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for("fun run() {\n    mystery()\n}\n");
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
        let g = graph_for("import kotlin.math.sqrt\nimport com.acme.Widget\n");
        assert!(g.has_node("ext::kotlin"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::kotlin"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn superclass_extends_interface_implements() {
        let g = graph_for("open class Base\ninterface Drawable\nclass Shape : Base(), Drawable\n");
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an EXTENDS edge for the superclass");
        assert!(ext.from.starts_with("type::Shape"));
        assert!(ext.to.starts_with("type::Base"), "extends {}", ext.to);
        let imp = g
            .edges()
            .find(|e| e.kind == edge::IMPLEMENTS)
            .expect("an IMPLEMENTS edge for the interface");
        assert!(
            imp.to.starts_with("type::Drawable"),
            "implements {}",
            imp.to
        );
    }

    #[test]
    fn top_level_val_is_constant() {
        let g = graph_for("const val VERSION = \"1.0\"\nclass C {\n    val field = 1\n}\n");
        // VERSION is a top-level Constant; C.field (member property) is not.
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 1);
        let c = g
            .nodes()
            .find(|n| n.kind == ont::CONSTANT)
            .expect("a constant");
        assert_eq!(c.name, "VERSION");
        assert_eq!(c.props.get("is_const"), Some(&Json::Bool(true)));
    }

    #[test]
    fn type_use_in_signature() {
        let g = graph_for("class Widget\n\nfun build(w: Widget) {}\n");
        assert!(
            g.edges()
                .any(|e| e.kind == edge::USES_TYPE && e.to.contains("Widget")),
            "parameter type should create USES_TYPE"
        );
    }

    #[test]
    fn package_declaration_sets_module() {
        let g = graph_for("package com.example.app\nfun f() {}\n");
        let f = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION)
            .expect("a function");
        assert_eq!(
            f.props.get("qualified_name"),
            Some(&Json::str("com.example.app.f"))
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src = "package p\nimport a.b.C\nclass K(val x: Int) : C() {\n    fun m() {\n        helper()\n    }\n}\nfun helper() {}\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
