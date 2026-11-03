//! Lower the TypeScript CST into the canonical graph.
//!
//! This mirrors the Rust and Python lowerings — same conservative principles,
//! same shared ontology — adapted to TypeScript's surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to
//!    a concrete project definition only when a scope level yields exactly one
//!    candidate; several candidates become an ambiguous edge carrying the full
//!    `candidates` set; none resolves to an explicit `UnresolvedSymbol`.
//! 2. **Everything comes from real tokens.** Calls, base types, imports, and type
//!    uses are read off the lossless tree, never guessed.
//!
//! Resolution uses a deterministic **scope ladder** (most specific first; the
//! first level with any candidate decides): receiver (`this`/`super`) → local
//! file functions → file imports (relative specifiers resolved to project files)
//! → global functions → a unique project type (a constructor call). Each edge
//! records which level resolved it, so the call graph stays auditable.
//!
//! Honest mappings (see the IR Atlas):
//!   `function` → `Function`; a `class`/`interface`/`enum`/`type` alias → `Type`
//!   with the apt `type_kind`; a `namespace` → `Module`; a method → a `Function`
//!   plus `HAS_METHOD` from its enclosing type; a `const`/`let`/`var` binding →
//!   `Constant` (unless its initializer is an arrow/function expression, in which
//!   case it is a `Function`); `class C extends B` → `EXTENDS`; `class C
//!   implements I` and `interface I extends J` → `IMPLEMENTS`/`EXTENDS`;
//!   `import … from …` → `IMPORTS` (plus `ExternalDependency`/`DEPENDS_ON` for
//!   bare specifiers). Decorators are recorded as a `decorators` property (no
//!   `DECORATES` edge constant exists yet, so we do not fabricate one).
//!
//! Known breadth gaps (honest, never silent): generic call sites `f<T>()` and
//! expression-bodied arrow calls (`() => foo()` without a block) are not always
//! captured; CommonJS `require(...)` is seen only as a call, not an `IMPORTS`
//! edge. These under-report rather than fabricate.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::typescript::lexer::{is_keyword, kind as tk};
use crate::lang::typescript::parser::node as cst;

const LANG: &str = "typescript";

/// Lower a whole project's worth of TypeScript files into a graph. `manifest_deps`
/// is unused (the pipeline's manifest reader is Cargo-only); dependencies are
/// discovered from `import` statements instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    // Map every file's repo-relative path to its module-join, and remember the
    // set of known files so relative imports can resolve to a concrete file.
    let mut file_modjoin: BTreeMap<String, String> = BTreeMap::new();
    let mut known_files: BTreeSet<String> = BTreeSet::new();
    for f in files {
        file_modjoin.insert(f.rel_path.clone(), mod_join(&f.module_path));
        known_files.insert(f.rel_path.clone());
    }

    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        known_files,
        file_modjoin,
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
        vec![("ecosystem", Json::str("npm"))],
    );

    // Pass B: create definition nodes + structural edges, build symbol tables and
    // per-file import maps. Base types are deferred to pass C so a class defined
    // later in the project still resolves.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_bases: Vec<PendingBase> = Vec::new();
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
                ("language", Json::str(LANG)),
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
            f.source,
            &li,
            &mut pend_fns,
            &mut pend_bases,
        );
    }

    // Pass C: resolve calls (scope ladder), type usages, and base types against
    // the now-complete symbol tables.
    for pf in &pend_fns {
        let ctx = Ctx {
            module_join: pf.module_join.clone(),
            owner_type: pf.owner_type.clone(),
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
    for pb in &pend_bases {
        lo.emit_base(pb);
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    known_files: BTreeSet<String>,
    /// Repo-relative path → module-join, for resolving relative imports.
    file_modjoin: BTreeMap<String, String>,
    /// Simple name → all function node ids (global level).
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// Simple name → method node ids only (global method-call level).
    method_by_name: BTreeMap<String, Vec<String>>,
    /// (module_join, name) → function ids (local-module level).
    fn_by_module: BTreeMap<(String, String), Vec<String>>,
    /// (type_name, method_name) → method ids (receiver level).
    method_by_type: BTreeMap<(String, String), Vec<String>>,
    /// Simple name → type node ids.
    type_by_name: BTreeMap<String, Vec<String>>,
    /// Per-file import maps: imported leaf name → defining module-join (internal
    /// imports only; bare/external specifiers do not aid call resolution).
    imports: Vec<BTreeMap<String, String>>,
    cur_file: usize,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    block: Option<&'a Node>,
    signature: Option<&'a Node>,
    module_join: String,
    owner_type: Option<String>,
    file_idx: usize,
}

/// A deferred base-type link (`extends` / `implements`), resolved in pass C.
struct PendingBase {
    type_id: String,
    base_name: String,
    edge_kind: &'static str,
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
}

struct Ctx {
    module_join: String,
    owner_type: Option<String>,
    imports: BTreeMap<String, String>,
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
                vec![("language", Json::str(LANG))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    /// Walk an item container (`SourceFile`, namespace `ItemBlock`), creating
    /// definition nodes and recursing into nested scopes.
    #[allow(clippy::too_many_arguments)]
    fn walk_items<'a>(
        &mut self,
        container: &'a Node,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        owner: Option<&Owner>,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_bases: &mut Vec<PendingBase>,
    ) {
        for item in container.child_nodes() {
            match item.kind {
                cst::FUNCTION => {
                    if item.child(cst::NAME).is_some() {
                        self.handle_fn(item, file_id, module_join, scope, None, src, li, pend_fns)
                    }
                }
                cst::CLASS => self.handle_type_with_members(
                    item,
                    file_id,
                    module_join,
                    scope,
                    "class",
                    src,
                    li,
                    pend_fns,
                    pend_bases,
                ),
                cst::INTERFACE => self.handle_type_with_members(
                    item,
                    file_id,
                    module_join,
                    scope,
                    "interface",
                    src,
                    li,
                    pend_fns,
                    pend_bases,
                ),
                cst::ENUM => {
                    self.handle_simple_type(item, file_id, module_join, scope, "enum", src, li)
                }
                cst::TYPE_ALIAS => {
                    self.handle_simple_type(item, file_id, module_join, scope, "alias", src, li)
                }
                cst::NAMESPACE => self.handle_namespace(
                    item,
                    file_id,
                    module_join,
                    scope,
                    src,
                    li,
                    pend_fns,
                    pend_bases,
                ),
                cst::VARIABLE => {
                    // Module/namespace-level bindings only (owner.is_none()).
                    if owner.is_none() {
                        self.handle_var(item, file_id, module_join, scope, src, li, pend_fns);
                    }
                }
                cst::IMPORT => self.handle_import(item, file_id, src),
                cst::STMT if is_reexport(item, src) => self.handle_import(item, file_id, src),
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
        let name = name_text(item, src).unwrap_or("<anonymous>").to_string();
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(module_join, scope, &name);
        let id = format!("fn::{qual}#{line}");
        let block = item.child(cst::BLOCK);
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str(LANG)),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            ("has_body", Json::Bool(block.is_some())),
        ];
        append_export_props(&mut props, item, src);
        if has_token(item, src, "async") {
            props.push(("is_async", Json::Bool(true)));
        }
        if let Some(d) = decorators(item, src) {
            props.push(("decorators", d));
        }
        if let Some(o) = owner {
            props.push(("receiver_type", Json::str(o.name.clone())));
            props.push(("is_method", Json::Bool(true)));
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, name.clone(), props);
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);

        self.index_fn(&name, module_join, &id, owner);

        pend_fns.push(PendingFn {
            id,
            source: src,
            block,
            signature: item.child(cst::SIGNATURE),
            module_join: module_join.to_string(),
            owner_type: owner.map(|o| o.name.clone()),
            file_idx: self.cur_file,
        });
    }

    fn index_fn(&mut self, name: &str, module_join: &str, id: &str, owner: Option<&Owner>) {
        self.fn_by_name
            .entry(name.to_string())
            .or_default()
            .push(id.to_string());
        self.fn_by_module
            .entry((module_join.to_string(), name.to_string()))
            .or_default()
            .push(id.to_string());
        if let Some(o) = owner {
            self.method_by_name
                .entry(name.to_string())
                .or_default()
                .push(id.to_string());
            self.method_by_type
                .entry((o.name.clone(), name.to_string()))
                .or_default()
                .push(id.to_string());
            self.g
                .add_edge(o.id.clone(), edge::HAS_METHOD, id.to_string(), vec![]);
        }
    }

    /// `class` / `interface`: a `Type` node whose members (methods + function-
    /// valued fields) become `Function`s linked by `HAS_METHOD`.
    #[allow(clippy::too_many_arguments)]
    fn handle_type_with_members<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        type_kind: &'static str,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_bases: &mut Vec<PendingBase>,
    ) {
        let name = name_text(item, src).unwrap_or("<anonymous>").to_string();
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(module_join, scope, &name);
        let id = format!("type::{qual}");
        let mut props = vec![
            ("type_kind", Json::str(type_kind)),
            ("qualified_name", Json::str(qual)),
            ("language", Json::str(LANG)),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
        ];
        append_export_props(&mut props, item, src);
        if let Some(d) = decorators(item, src) {
            props.push(("decorators", d));
        }
        self.g
            .upsert_node(id.clone(), ont::TYPE, name.clone(), props);
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());

        // `extends` / `implements` clauses (deferred to pass C). A class/interface
        // `extends` → EXTENDS (subtype); a class `implements` an interface →
        // IMPLEMENTS (conforms-to). This keeps the lattice honest.
        for (clause, base) in base_clauses(item, src) {
            let edge_kind = match clause {
                Clause::Extends => edge::EXTENDS,
                Clause::Implements => edge::IMPLEMENTS,
            };
            pend_bases.push(PendingBase {
                type_id: id.clone(),
                base_name: base,
                edge_kind,
            });
        }

        if let Some(body) = item.child(cst::MEMBER_BLOCK) {
            let owner = Owner {
                name: name.clone(),
                id: id.clone(),
            };
            let mut child_scope = scope.to_vec();
            child_scope.push(name);
            for member in body.child_nodes() {
                match member.kind {
                    cst::METHOD
                        if member.child(cst::NAME).is_some()
                            && !is_construct_signature(member, src) =>
                    {
                        self.handle_fn(
                            member,
                            file_id,
                            module_join,
                            &child_scope,
                            Some(&owner),
                            src,
                            li,
                            pend_fns,
                        )
                    }
                    cst::PROPERTY => {
                        // A property whose initializer is an arrow/function is a
                        // method in all but syntax; emit it as one.
                        if let Some(decl) = function_valued_property(member, src) {
                            self.handle_member_fn(
                                member,
                                &decl,
                                file_id,
                                module_join,
                                &child_scope,
                                &owner,
                                src,
                                li,
                                pend_fns,
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    /// Emit a `Function` for a function-valued class field (`handler = () => …`).
    #[allow(clippy::too_many_arguments)]
    fn handle_member_fn<'a>(
        &mut self,
        member: &'a Node,
        decl: &FnDecl<'a>,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        owner: &Owner,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
    ) {
        let name = name_text(member, src).unwrap_or("<anonymous>").to_string();
        let line = li.line_col(name_span_start(member)).line;
        let qual = qual_name(module_join, scope, &name);
        let id = format!("fn::{qual}#{line}");
        self.g.upsert_node(
            id.clone(),
            ont::FUNCTION,
            name.clone(),
            vec![
                ("qualified_name", Json::str(qual)),
                ("language", Json::str(LANG)),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(member.span.start as u64)),
                ("span_end", Json::U64(member.span.end as u64)),
                ("has_body", Json::Bool(decl.block.is_some())),
                ("receiver_type", Json::str(owner.name.clone())),
                ("is_method", Json::Bool(true)),
                ("binding", Json::str("field")),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.index_fn(&name, module_join, &id, Some(owner));
        pend_fns.push(PendingFn {
            id,
            source: src,
            block: decl.block,
            signature: decl.signature,
            module_join: module_join.to_string(),
            owner_type: Some(owner.name.clone()),
            file_idx: self.cur_file,
        });
    }

    /// `enum` / `type` alias: a `Type` node with no member walk.
    #[allow(clippy::too_many_arguments)]
    fn handle_simple_type(
        &mut self,
        item: &Node,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        type_kind: &'static str,
        src: &str,
        li: &LineIndex,
    ) {
        let name = match name_text(item, src) {
            Some(n) if !n.is_empty() => n.to_string(),
            _ => return,
        };
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(module_join, scope, &name);
        let id = format!("type::{qual}");
        let mut props = vec![
            ("type_kind", Json::str(type_kind)),
            ("qualified_name", Json::str(qual)),
            ("language", Json::str(LANG)),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
        ];
        append_export_props(&mut props, item, src);
        self.g
            .upsert_node(id.clone(), ont::TYPE, name.clone(), props);
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name.entry(name).or_default().push(id);
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_namespace<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_bases: &mut Vec<PendingBase>,
    ) {
        let name = name_text(item, src).unwrap_or("<anonymous>").to_string();
        // Namespaces nest as dotted module-joins, so a `function` inside is keyed
        // under the namespace just like a Python sub-module.
        let inner_join = if module_join.is_empty() {
            name.clone()
        } else {
            format!("{module_join}.{name}")
        };
        let mod_id = format!("mod::{inner_join}");
        let mut props = vec![
            ("language", Json::str(LANG)),
            ("namespace", Json::Bool(true)),
        ];
        append_export_props(&mut props, item, src);
        self.g
            .upsert_node(mod_id.clone(), ont::MODULE, name.clone(), props);
        self.g.add_edge(file_id, edge::DECLARES, mod_id, vec![]);

        if let Some(body) = item.child(cst::ITEM_BLOCK) {
            self.walk_items(
                body,
                file_id,
                &inner_join,
                scope,
                None,
                src,
                li,
                pend_fns,
                pend_bases,
            );
        }
    }

    /// `const`/`let`/`var`: each declarator is a `Constant`, unless its
    /// initializer is an arrow or function expression (then a `Function`).
    #[allow(clippy::too_many_arguments)]
    fn handle_var<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
    ) {
        let kw = item
            .tokens()
            .next()
            .map(|t| t.span.text(src))
            .unwrap_or("const")
            .to_string();
        let header = match item.child(cst::HEADER) {
            Some(h) => h,
            None => return,
        };
        for decl in split_declarators(header, src) {
            let name = match decl.name {
                Some(n) => n.to_string(),
                None => continue,
            };
            let line = li.line_col(decl.name_start).line;
            if let Some(fnd) = decl.as_function() {
                let qual = qual_name(module_join, scope, &name);
                let id = format!("fn::{qual}#{line}");
                let mut props = vec![
                    ("qualified_name", Json::str(qual)),
                    ("language", Json::str(LANG)),
                    ("line", Json::U64(line as u64)),
                    ("span_start", Json::U64(item.span.start as u64)),
                    ("span_end", Json::U64(item.span.end as u64)),
                    ("has_body", Json::Bool(fnd.block.is_some())),
                    ("binding", Json::str(kw.clone())),
                ];
                append_export_props(&mut props, item, src);
                self.g
                    .upsert_node(id.clone(), ont::FUNCTION, name.clone(), props);
                self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
                self.index_fn(&name, module_join, &id, None);
                pend_fns.push(PendingFn {
                    id,
                    source: src,
                    block: fnd.block,
                    signature: fnd.signature,
                    module_join: module_join.to_string(),
                    owner_type: None,
                    file_idx: self.cur_file,
                });
            } else {
                let id = format!("const::{}", qual_name(module_join, scope, &name));
                let mut props = vec![
                    ("binding", Json::str(kw.clone())),
                    ("language", Json::str(LANG)),
                    ("line", Json::U64(line as u64)),
                ];
                append_export_props(&mut props, item, src);
                self.g.upsert_node(id.clone(), ont::CONSTANT, name, props);
                self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
            }
        }
    }

    /// Parse an `import` declaration: emit the `IMPORTS` edge and bind imported
    /// names to their defining module for cross-file call resolution.
    fn handle_import(&mut self, item: &Node, file_id: &str, src: &str) {
        let header = item.child(cst::HEADER).unwrap_or(item);
        let spec = match import_specifier(header, src) {
            Some(s) => s,
            None => return,
        };
        let cur_rel = file_id.strip_prefix("file::").unwrap_or("").to_string();
        let resolved = resolve_relative(&cur_rel, &spec, &self.known_files);
        let target_modjoin = resolved
            .as_ref()
            .and_then(|r| self.file_modjoin.get(r).cloned());

        let reexport = is_reexport(item, src);
        let reexport_all = reexport && tree_has_token(header, src, "*");
        // Bind each imported leaf name to the defining module-join (internal only).
        if let Some(mj) = &target_modjoin {
            for leaf in imported_names(header, src) {
                self.imports[self.cur_file].insert(leaf, mj.clone());
            }
        }

        if spec.starts_with('.') || spec.starts_with('/') {
            // Relative / project import.
            let target = match &resolved {
                Some(r) => format!("file::{r}"),
                None => {
                    // Unresolved relative path: anchor at a synthesized module node
                    // rather than fabricating a file that does not exist.
                    let norm = normalize_join(&cur_rel, &spec);
                    let id = format!("mod::{norm}");
                    self.g.upsert_node(
                        id.clone(),
                        ont::MODULE,
                        norm,
                        vec![
                            ("language", Json::str(LANG)),
                            ("unresolved_path", Json::Bool(true)),
                        ],
                    );
                    id
                }
            };
            let props = import_edge_props(&spec, false, reexport, reexport_all);
            self.g.add_edge(file_id, edge::IMPORTS, target, props);
        } else {
            // Bare specifier → an external dependency (package root, honoring an
            // `@scope/pkg` prefix).
            let root = package_root(&spec);
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
            let props = import_edge_props(&spec, true, reexport, reexport_all);
            self.g
                .add_edge(file_id, edge::IMPORTS, dep_id.clone(), props);
            self.g
                .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
        }
    }

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        if call.method {
            if matches!(call.receiver.as_deref(), Some("this") | Some("super")) {
                if let Some(owner) = &ctx.owner_type {
                    let c = self.methods_of(owner, &call.name);
                    if !c.is_empty() {
                        return mk(c, "receiver");
                    }
                }
            }
            // Unknown receiver type (no inference). The honest candidate set is
            // every same-name method PLUS every same-name free function — a TS
            // member call can reach namespace imports (`ns.f()`) and functions
            // stored as object properties. `mk` resolves a singleton and
            // preserves any wider set as an explicit ambiguity; it never guesses.
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

        // Local module.
        let c = self.fns_in_module(&ctx.module_join, &call.name);
        if !c.is_empty() {
            return mk(c, "local");
        }
        // File imports: a bare name brought in via `import { name } from './m'`.
        if let Some(mj) = ctx.imports.get(&call.name) {
            let c = self.fns_in_module(mj, &call.name);
            if !c.is_empty() {
                return mk(c, "import");
            }
        }
        // Global functions.
        let c = self.global_fns(&call.name);
        if !c.is_empty() {
            return mk(c, "global");
        }
        // A unique project type → a constructor call.
        if let Some(id) = self.unique_type(&call.name) {
            return Resolution {
                outcome: Outcome::One(id),
                level: "constructor",
            };
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

    /// Resolve a deferred base type into a concrete `EXTENDS`/`IMPLEMENTS` edge,
    /// pointing at the project type when unique, else an explicit
    /// `UnresolvedSymbol` (a base we cannot see in an airgap).
    fn emit_base(&mut self, pb: &PendingBase) {
        let target = match self.unique_type(&pb.base_name) {
            Some(id) => id,
            None => {
                let id = unresolved_id(&pb.base_name);
                self.ensure_unresolved(&id, &pb.base_name, "base_type");
                id
            }
        };
        self.g.add_edge(
            pb.type_id.clone(),
            pb.edge_kind,
            target,
            vec![("base_name", Json::str(pb.base_name.clone()))],
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

    fn unique_type(&self, name: &str) -> Option<String> {
        match self.type_by_name.get(name) {
            Some(ids) if ids.len() == 1 => Some(ids[0].clone()),
            _ => None,
        }
    }

    /// Add `USES_TYPE` edges for identifiers in a signature region that name a
    /// unique project type (parameter / return annotations, type-alias RHS).
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

fn mod_join(path: &[String]) -> String {
    path.join(".")
}

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
    let t = nm.tokens().next()?;
    let text = t.span.text(src);
    // A string-literal member name (`"~validate"() {}`, `"foo-bar": …`) carries its
    // own name unquoted, exactly as TS reports it.
    if t.kind == tk::STRING {
        Some(unquote_str(text))
    } else {
        Some(text)
    }
}

/// Strip a single matching pair of surrounding `"`, `'`, or backtick quotes,
/// borrowing (unlike [`unquote`], which allocates).
fn unquote_str(s: &str) -> &str {
    let b = s.as_bytes();
    if b.len() >= 2 {
        let q = b[0];
        if (q == b'"' || q == b'\'' || q == b'`') && b[b.len() - 1] == q {
            return &s[1..s.len() - 1];
        }
    }
    s
}

/// A construct signature `new (…): T` in an interface/type: the parser captures
/// `new` as the member name, but TS reports it as a ConstructSignature, never a
/// definition. Identified by the name `new` with no body block (a real class
/// method literally named `new` has a block and is still emitted).
fn is_construct_signature(member: &Node, src: &str) -> bool {
    name_text(member, src) == Some("new") && member.child(cst::BLOCK).is_none()
}

fn name_span_start(item: &Node) -> u32 {
    item.child(cst::NAME)
        .map(|n| n.span.start)
        .unwrap_or(item.span.start)
}

/// True if `item` has a direct non-trivia child token with the given text.
fn has_token(item: &Node, src: &str, text: &str) -> bool {
    item.tokens().any(|t| t.span.text(src) == text)
}

fn append_export_props(props: &mut Vec<(&'static str, Json)>, item: &Node, src: &str) {
    if has_token(item, src, "export") {
        props.push(("exported", Json::Bool(true)));
        if has_token(item, src, "default") {
            props.push(("default_export", Json::Bool(true)));
        }
    }
}

fn tree_has_token(item: &Node, src: &str, text: &str) -> bool {
    item.walk()
        .any(|node| node.tokens().any(|token| token.span.text(src) == text))
}

fn is_reexport(item: &Node, src: &str) -> bool {
    let header = item.child(cst::HEADER).unwrap_or(item);
    has_token(item, src, "export") && has_token(header, src, "from")
}

fn import_edge_props(
    spec: &str,
    external: bool,
    reexport: bool,
    reexport_all: bool,
) -> Vec<(&'static str, Json)> {
    let mut props = vec![
        ("path", Json::str(spec.to_string())),
        ("external", Json::Bool(external)),
    ];
    if reexport {
        props.push(("reexport", Json::Bool(true)));
    }
    if reexport_all {
        props.push(("reexport_all", Json::Bool(true)));
    }
    props
}

/// Decorator base names attached to a definition (the last identifier of each
/// `@expr`), or `None` when there are none.
fn decorators(item: &Node, src: &str) -> Option<Json> {
    let mut names: Vec<Json> = Vec::new();
    for d in item.children_of(cst::DECORATOR) {
        let mut last: Option<&str> = None;
        for t in d.tokens() {
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

#[derive(Clone, Copy, PartialEq)]
enum Clause {
    Extends,
    Implements,
}

/// Base classes/interfaces from a class/interface `Header`: pairs of (clause,
/// base simple name). Only the first identifier of each base is taken (`B` from
/// `B<X>`); type arguments are skipped via angle-bracket depth tracking.
fn base_clauses(item: &Node, src: &str) -> Vec<(Clause, String)> {
    let header = match item.child(cst::HEADER) {
        Some(h) => h,
        None => return Vec::new(),
    };
    let mut out = Vec::new();
    let mut clause: Option<Clause> = None;
    let mut want_name = false;
    let mut angle: i32 = 0;
    for t in header.tokens() {
        let text = t.span.text(src);
        // Track generic-argument depth so `extends Base<Other>` does not record
        // `Other` as a base. `>>`/`>>>` close several levels at once.
        if t.kind == tk::PUNCT {
            angle += text.chars().filter(|&c| c == '<').count() as i32;
            angle -= text.chars().filter(|&c| c == '>').count() as i32;
            if angle < 0 {
                angle = 0;
            }
        }
        match text {
            "extends" => {
                clause = Some(Clause::Extends);
                want_name = true;
                continue;
            }
            "implements" => {
                clause = Some(Clause::Implements);
                want_name = true;
                continue;
            }
            "," if angle <= 0 => {
                want_name = true;
                continue;
            }
            _ => {}
        }
        if want_name && angle <= 0 && t.kind == tk::IDENT && !is_keyword(text) {
            if let Some(cl) = clause {
                out.push((cl, text.to_string()));
            }
            want_name = false;
        }
    }
    out
}

/// A function-shaped initializer: its signature (params) and body block, if any.
struct FnDecl<'a> {
    signature: Option<&'a Node>,
    block: Option<&'a Node>,
}

/// If a class/interface `Property` member's initializer is an arrow or function
/// expression (`handler = () => { … }`), return its params/body for emitting a
/// `Function`; otherwise `None` (an ordinary field).
fn function_valued_property<'a>(member: &'a Node, src: &'a str) -> Option<FnDecl<'a>> {
    let header = member.child(cst::HEADER)?;
    let mut after_eq = false;
    let mut is_fn = false;
    let mut signature = None;
    let mut block = None;
    for ch in &header.children {
        match ch {
            Child::Token(t) if !t.trivia => {
                let text = t.span.text(src);
                if !after_eq {
                    if text == "=" {
                        after_eq = true;
                    }
                } else if text == "=>" || text == "function" {
                    is_fn = true;
                }
            }
            Child::Node(n) if after_eq => {
                if n.kind == cst::PAREN && signature.is_none() {
                    signature = Some(n);
                }
                if n.kind == cst::BRACE {
                    block = Some(n);
                }
            }
            _ => {}
        }
    }
    if is_fn {
        Some(FnDecl { signature, block })
    } else {
        None
    }
}

/// One `const`/`let`/`var` declarator: its bound name plus the children of its
/// initializer (after the first `=`) for function detection.
struct Declarator<'a> {
    name: Option<&'a str>,
    name_start: u32,
    init: Vec<&'a Child>,
    /// Whether the initializer is an arrow or function expression, precomputed
    /// at split time (it needs the source buffer, which the builder holds).
    init_is_function: bool,
}

impl<'a> Declarator<'a> {
    /// If the initializer is function-shaped, return its first paren group
    /// (params) and a brace group (body) for downstream scanning.
    fn as_function(&self) -> Option<FnDecl<'a>> {
        if !self.init_is_function {
            return None;
        }
        let mut signature = None;
        let mut block = None;
        for &ch in &self.init {
            if let Child::Node(n) = ch {
                if n.kind == cst::PAREN && signature.is_none() {
                    signature = Some(n);
                }
                if n.kind == cst::BRACE {
                    block = Some(n);
                }
            }
        }
        Some(FnDecl { signature, block })
    }
}

/// Build one [`Declarator`] from a slice of declarator children: the name is the
/// first identifier; the initializer is everything after the first top-level `=`.
fn build_declarator<'a>(children: &[&'a Child], src: &'a str) -> Option<Declarator<'a>> {
    let mut name = None;
    let mut name_start = 0u32;
    let mut eq_idx = None;
    for (idx, ch) in children.iter().enumerate() {
        match ch {
            Child::Token(t) if t.trivia => continue,
            Child::Token(t) => {
                let text = t.span.text(src);
                if text == "=" {
                    eq_idx = Some(idx);
                    break; // the name is the binder before `=`; never scan the init
                }
                if name.is_none() {
                    // The first significant token before `=` is the binding name.
                    // Contextual keywords are valid identifiers here (`const string`,
                    // `const type`, `const get`), so they are accepted — matching the
                    // oracle, which sees them as plain Identifiers.
                    if t.kind == tk::IDENT || is_keyword(text) {
                        name = Some(text);
                        name_start = t.span.start;
                    } else {
                        return None; // not a simple binder (operator, etc.)
                    }
                }
            }
            // A node before the name (a `{ … }` / `[ … ]` destructuring pattern) has
            // no single binding name.
            Child::Node(_) if name.is_none() => return None,
            Child::Node(_) => {}
        }
    }
    let name = name?;
    let init: Vec<&'a Child> = match eq_idx {
        Some(i) => children[i + 1..].to_vec(),
        None => Vec::new(),
    };
    // A top-level `=>` (arrow value) or `function` *keyword* makes the initializer
    // function-valued. `function` as a member name (`z.function(…)`) is a call, not
    // a definition, so it must not count — track a preceding `.`.
    let mut init_is_function = false;
    let mut prev_dot = false;
    for ch in &init {
        match ch {
            Child::Token(t) if !t.trivia => {
                let x = t.span.text(src);
                if x == "=>" || (x == "function" && !prev_dot) {
                    init_is_function = true;
                    break;
                }
                prev_dot = x == ".";
            }
            Child::Token(_) => {}
            Child::Node(_) => prev_dot = false,
        }
    }
    Some(Declarator {
        name: Some(name),
        name_start,
        init,
        init_is_function,
    })
}

/// Split a variable `Header` into declarators on top-level commas.
fn split_declarators<'a>(header: &'a Node, src: &'a str) -> Vec<Declarator<'a>> {
    let mut decls = Vec::new();
    let mut cur_children: Vec<&'a Child> = Vec::new();
    let mut angle: i32 = 0;
    for ch in &header.children {
        if let Child::Token(t) = ch {
            if !t.trivia && t.kind == tk::PUNCT {
                let text = t.span.text(src);
                angle += text.chars().filter(|&c| c == '<').count() as i32;
                angle -= text.chars().filter(|&c| c == '>').count() as i32;
                if angle < 0 {
                    angle = 0;
                }
                if text == "," && angle == 0 {
                    if let Some(d) = build_declarator(&cur_children, src) {
                        decls.push(d);
                    }
                    cur_children.clear();
                    continue;
                }
            }
        }
        cur_children.push(ch);
    }
    if let Some(d) = build_declarator(&cur_children, src) {
        decls.push(d);
    }
    decls
}

// --- import parsing ---------------------------------------------------------

/// The module specifier string (without quotes) of an `import`/`export … from`
/// header: the string after `from`, inside `require(...)`, or a lone string.
fn import_specifier(header: &Node, src: &str) -> Option<String> {
    let toks: Vec<(&'static str, &str)> = header
        .walk()
        .flat_map(|n| n.tokens())
        .map(|t| (t.kind, t.span.text(src)))
        .collect();
    // Prefer the string following a `from` keyword.
    for i in 0..toks.len() {
        if toks[i].1 == "from" {
            for t in toks.iter().skip(i + 1) {
                if t.0 == tk::STRING {
                    return Some(unquote(t.1));
                }
            }
        }
    }
    // `import x = require('spec')` or any string at all (side-effect import).
    for t in &toks {
        if t.0 == tk::STRING {
            return Some(unquote(t.1));
        }
    }
    None
}

/// Imported leaf names bound by a header: the default binding, namespace alias,
/// and each `{ a, b as c }` member (the alias when present).
fn imported_names(header: &Node, src: &str) -> Vec<String> {
    let mut names = Vec::new();
    // Default / namespace: top-level identifiers before the brace / `from`.
    for ch in &header.children {
        match ch {
            Child::Token(t) if !t.trivia => {
                let text = t.span.text(src);
                if text == "from" {
                    break;
                }
                if t.kind == tk::IDENT && !is_keyword(text) {
                    names.push(text.to_string());
                }
            }
            Child::Node(n) if n.kind == cst::BRACE => {
                // Named bindings inside `{ … }`.
                for clause in split_top_commas(n, src) {
                    if let Some(leaf) = clause_leaf(&clause) {
                        names.push(leaf);
                    }
                }
            }
            _ => {}
        }
    }
    names
}

/// The bound leaf of a `{ a }` / `{ a as b }` clause: the alias if present, else
/// the imported name.
fn clause_leaf(clause: &[(&'static str, String)]) -> Option<String> {
    let idents: Vec<&String> = clause
        .iter()
        .filter(|(k, t)| *k == tk::IDENT && !is_keyword(t))
        .map(|(_, t)| t)
        .collect();
    idents.last().map(|s| s.to_string())
}

/// Split a brace group's top-level tokens on commas, returning per-clause
/// (kind, text) lists (descends no further than the group itself).
fn split_top_commas(group: &Node, src: &str) -> Vec<Vec<(&'static str, String)>> {
    let mut out: Vec<Vec<(&'static str, String)>> = vec![Vec::new()];
    for ch in &group.children {
        if let Child::Token(t) = ch {
            if t.trivia {
                continue;
            }
            let text = t.span.text(src).to_string();
            if text == "," {
                out.push(Vec::new());
            } else if text != "{" && text != "}" {
                out.last_mut().unwrap().push((t.kind, text));
            }
        }
    }
    out.into_iter().filter(|c| !c.is_empty()).collect()
}

fn unquote(s: &str) -> String {
    let bytes = s.as_bytes();
    if bytes.len() >= 2 {
        let first = bytes[0];
        let last = bytes[bytes.len() - 1];
        if (first == b'"' || first == b'\'' || first == b'`') && last == first {
            return s[1..s.len() - 1].to_string();
        }
    }
    s.to_string()
}

/// The dependency root of a bare specifier: `@scope/pkg` keeps two segments,
/// `pkg/sub/path` keeps the first.
fn package_root(spec: &str) -> String {
    if let Some(rest) = spec.strip_prefix('@') {
        let mut it = rest.splitn(3, '/');
        let scope = it.next().unwrap_or("");
        let pkg = it.next().unwrap_or("");
        if pkg.is_empty() {
            format!("@{scope}")
        } else {
            format!("@{scope}/{pkg}")
        }
    } else {
        spec.split('/').next().unwrap_or(spec).to_string()
    }
}

/// Normalize a relative import against the importing file's path into a
/// `.`-joined, extension-less key (used for an unresolved-path module node).
fn normalize_join(cur_rel: &str, spec: &str) -> String {
    let segs = normalize_segments(cur_rel, spec);
    segs.join(".")
}

/// Resolve a relative specifier to a concrete project file path, trying the
/// usual TypeScript extension and `index` conventions.
fn resolve_relative(cur_rel: &str, spec: &str, known: &BTreeSet<String>) -> Option<String> {
    if !(spec.starts_with('.') || spec.starts_with('/')) {
        return None;
    }
    let base = normalize_segments(cur_rel, spec).join("/");
    let candidates = [
        base.clone(),
        format!("{base}.ts"),
        format!("{base}.tsx"),
        format!("{base}.d.ts"),
        format!("{base}/index.ts"),
        format!("{base}/index.tsx"),
    ];
    candidates.into_iter().find(|c| known.contains(c))
}

/// Join a relative `spec` onto the directory of `cur_rel`, resolving `.`/`..`.
fn normalize_segments(cur_rel: &str, spec: &str) -> Vec<String> {
    let mut dir: Vec<String> = cur_rel.split('/').map(|s| s.to_string()).collect();
    dir.pop(); // drop the file name → its directory
    for seg in spec.split('/') {
        match seg {
            "" | "." => {}
            ".." => {
                dir.pop();
            }
            other => dir.push(other.to_string()),
        }
    }
    dir
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

/// Detect `name(...)` and `recv.name(...)` call sites over the real token tree,
/// recursing into nested groups. Keywords are excluded; a bare identifier
/// immediately preceded by `.` is treated as a member access, not a bare call.
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
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
        if is_ident_el(&els[i]) {
            let prev = if i > 0 { tok_text(&els[i - 1]) } else { None };
            let text = tok_text(&els[i]).unwrap_or("");
            if prev != Some(".") && !is_keyword(text) && i + 1 < n {
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
    for e in &els {
        if let Some(g) = grp(e) {
            scan_calls(g, src, out);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::typescript::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("mod.ts", src);
        let file = SourceFile {
            rel_path: "mod.ts".to_string(),
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
    fn emits_function_type_method_nodes() {
        let g = graph_for("class C {\n  m() {}\n}\nfunction f() {}\n");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "f + C.m");
        assert_eq!(g.count_nodes_of(ont::TYPE), 1, "class C is a Type");
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD));
    }

    #[test]
    fn class_type_kind_is_class() {
        let g = graph_for("class C {}\n");
        let ty = g
            .nodes()
            .find(|n| n.kind == ont::TYPE)
            .expect("a Type node");
        assert_eq!(ty.props.get("type_kind"), Some(&Json::str("class")));
        assert_eq!(ty.props.get("language"), Some(&Json::str(LANG)));
    }

    #[test]
    fn interface_enum_alias_are_types() {
        let g = graph_for("interface I {}\nenum E { A }\ntype T = number;\n");
        let kinds: Vec<String> = g
            .nodes()
            .filter(|n| n.kind == ont::TYPE)
            .filter_map(|n| n.props.get("type_kind").cloned())
            .map(|j| match j {
                Json::Str(s) => s,
                _ => String::new(),
            })
            .collect();
        assert!(kinds.contains(&"interface".to_string()), "{kinds:?}");
        assert!(kinds.contains(&"enum".to_string()), "{kinds:?}");
        assert!(kinds.contains(&"alias".to_string()), "{kinds:?}");
    }

    fn fn_names(g: &Graph) -> Vec<String> {
        let mut v: Vec<String> = g
            .nodes()
            .filter(|n| n.kind == ont::FUNCTION)
            .map(|n| n.name.clone())
            .collect();
        v.sort();
        v
    }

    // The four regression cases below all stem from one root cause — the
    // signature/header regions did not track `<…>` (or object-type braces), so a
    // type-parameter comma or an object/mapped type was mistaken for the end of
    // the signature, truncating it and swallowing every following member. Each was
    // observed on real code (colinhacks/zod) via the ground-truth oracle.

    #[test]
    fn generic_method_comma_does_not_drop_following_member() {
        // `m<X, Y>(…)`: the comma between type params must not end the signature.
        let g = graph_for("class C {\n  m<X, Y>(a: X): void {}\n  after(): void {}\n}\n");
        let names = fn_names(&g);
        assert!(names.contains(&"m".to_string()), "{names:?}");
        assert!(names.contains(&"after".to_string()), "{names:?}");
        assert!(
            !names.contains(&"Y".to_string()),
            "type param leaked: {names:?}"
        );
    }

    #[test]
    fn object_type_return_is_not_the_body() {
        // `m(): { a: T } { body }`: the return-type object literal is not the body.
        let g = graph_for(
            "class C {\n  m(x: number): { a: number; b: number } { return {a:1,b:2}; }\n  after(): void {}\n}\n",
        );
        let names = fn_names(&g);
        assert!(names.contains(&"m".to_string()), "{names:?}");
        assert!(names.contains(&"after".to_string()), "{names:?}");
    }

    #[test]
    fn interface_extends_mapped_type_arg_keeps_following_items() {
        // `extends Base<…, { [K in D]: U }>`: the mapped type inside a type
        // argument must not be read as the interface body.
        let g = graph_for(
            "interface A<D extends string = string>\n  extends Base<unknown, { [K in D]?: unknown }> {\n  x: number;\n}\nfunction after(): void {}\n",
        );
        let names = fn_names(&g);
        assert!(names.contains(&"after".to_string()), "{names:?}");
        assert_eq!(g.count_nodes_of(ont::TYPE), 1, "interface A");
    }

    #[test]
    fn top_level_fn_object_return_keeps_following_fn() {
        let g = graph_for(
            "export function a(): { slug: string }[] { return []; }\nexport function b(): void {}\n",
        );
        let names = fn_names(&g);
        assert!(names.contains(&"a".to_string()), "{names:?}");
        assert!(names.contains(&"b".to_string()), "{names:?}");
    }

    #[test]
    fn resolves_unique_local_call() {
        let g = graph_for("function add(a, b) { return a + b; }\nfunction run() { add(1, 2); }\n");
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
    fn this_method_resolves_via_receiver() {
        let g = graph_for("class P {\n  a() { this.b(); }\n  b() {}\n}\n");
        let calls = call_edges(&g);
        let recv = calls
            .iter()
            .find(|e| e.props.get("resolution") == Some(&Json::str("receiver")));
        assert!(recv.is_some(), "this.b() should resolve via receiver scope");
        assert_eq!(recv.unwrap().props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for("function run() { mystery(); }\n");
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
        let g = graph_for("import { readFile } from 'fs';\nimport _ from 'lodash';\n");
        assert!(g.has_node("ext::fs"));
        assert!(g.has_node("ext::lodash"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::fs"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn scoped_package_root_is_two_segments() {
        let g = graph_for("import { x } from '@scope/pkg/sub';\n");
        assert!(g.has_node("ext::@scope/pkg"), "scoped root kept whole");
    }

    #[test]
    fn inheritance_emits_extends_and_implements() {
        let g = graph_for(
            "class Base {}\ninterface Shape {}\nclass Derived extends Base implements Shape {}\n",
        );
        // Shape resolves uniquely; Base resolves uniquely.
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an EXTENDS edge");
        assert!(ext.from.starts_with("type::mod.Derived"));
        assert!(ext.to.starts_with("type::mod.Base"));
        assert!(
            g.edges().any(|e| e.kind == edge::IMPLEMENTS),
            "implements Shape should be an IMPLEMENTS edge"
        );
    }

    #[test]
    fn const_is_constant_arrow_is_function() {
        let g = graph_for("const VERSION = '1.0';\nconst handler = () => { run(); };\n");
        let consts: Vec<&str> = g
            .nodes()
            .filter(|n| n.kind == ont::CONSTANT)
            .map(|n| n.name.as_str())
            .collect();
        assert_eq!(consts, vec!["VERSION"], "only VERSION is a Constant");
        assert!(
            g.nodes()
                .any(|n| n.kind == ont::FUNCTION && n.name == "handler"),
            "arrow-valued const is a Function"
        );
    }

    #[test]
    fn arrow_function_body_calls_are_scanned() {
        let g = graph_for("function run() {}\nconst go = () => { run(); };\n");
        let calls = call_edges(&g);
        assert!(
            calls
                .iter()
                .any(|e| e.props.get("callee") == Some(&Json::str("run"))
                    && e.props.get("resolved") == Some(&Json::Bool(true))),
            "call inside an arrow body should resolve"
        );
    }

    #[test]
    fn decorator_recorded_as_property() {
        let g = graph_for("@Component\nclass Widget {}\n");
        let w = g
            .nodes()
            .find(|n| n.kind == ont::TYPE && n.name == "Widget")
            .expect("the decorated class");
        assert_eq!(
            w.props.get("decorators"),
            Some(&Json::Array(vec![Json::str("Component")]))
        );
    }

    #[test]
    fn type_use_in_signature() {
        let g = graph_for("class Widget {}\nfunction build(w: Widget): void {}\n");
        assert!(
            g.edges()
                .any(|e| e.kind == edge::USES_TYPE && e.to.contains("Widget")),
            "param annotation should create USES_TYPE"
        );
    }

    #[test]
    fn namespace_is_module() {
        let g = graph_for("namespace N {\n  function g() {}\n}\n");
        assert!(g.has_node("mod::mod.N"), "namespace becomes a module");
        assert!(
            g.nodes().any(|n| n.kind == ont::FUNCTION && n.name == "g"),
            "namespaced function discovered"
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src = "import { x } from './u';\nclass C extends Base { m() { helper(); } }\nfunction helper() {}\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }

    // --- global_method rung: the singleton law -------------------------------

    #[test]
    fn method_call_with_singleton_method_still_resolves() {
        // Exactly one project callable named `save` → the member call resolves.
        let g = graph_for("class Repo { save() {} }\nfunction run(r: Repo) { r.save(); }\n");
        let calls = call_edges(&g);
        let e = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("save")))
            .expect("the r.save() call");
        assert_eq!(e.props.get("resolution"), Some(&Json::str("global_method")));
        assert_eq!(e.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(e.props.get("candidate_count"), Some(&Json::U64(1)));
    }

    #[test]
    fn method_call_ambiguous_across_two_classes() {
        // Two methods named `go` on different classes → AMBIGUOUS, both candidates.
        let g =
            graph_for("class A { go() {} }\nclass B { go() {} }\nfunction run(x: A) { x.go(); }\n");
        let calls = call_edges(&g);
        let e = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("go")))
            .expect("the x.go() call");
        assert_eq!(e.props.get("ambiguous"), Some(&Json::Bool(true)));
        assert_eq!(e.props.get("resolved"), Some(&Json::Bool(false)));
        assert_eq!(e.props.get("candidate_count"), Some(&Json::U64(2)));
        match e.props.get("candidates") {
            Some(Json::Array(c)) => assert_eq!(c.len(), 2, "both candidates carried"),
            other => panic!("candidates array expected, got {other:?}"),
        }
    }

    #[test]
    fn method_call_ambiguous_when_free_function_shares_name() {
        // The bio-mcp-client artifact shape: ONE class method named `json` plus a
        // same-name free function. A bare `resp.json()` must NOT resolve to the
        // class method — the free function is counterevidence → AMBIGUOUS with
        // the full candidate set.
        let g = graph_for(
            "class JsonToSqlDO { json(d: unknown) {} }\n\
             function json(body: unknown) {}\n\
             function handle(resp: Response) { resp.json(); }\n",
        );
        let calls = call_edges(&g);
        let e = calls
            .iter()
            .find(|e| {
                e.props.get("callee") == Some(&Json::str("json")) && e.from.contains("handle")
            })
            .expect("the resp.json() call");
        assert_eq!(e.props.get("resolution"), Some(&Json::str("global_method")));
        assert_eq!(e.props.get("ambiguous"), Some(&Json::Bool(true)));
        assert_eq!(e.props.get("resolved"), Some(&Json::Bool(false)));
        assert_eq!(e.props.get("candidate_count"), Some(&Json::U64(2)));
    }

    #[test]
    fn method_call_never_resolves_to_free_function_alone() {
        // No project METHOD named `log` — a member call must stay external even
        // though a free function shares the name (`console.log()` must not
        // manufacture fan-in on a project helper).
        let g = graph_for("function log(msg: string) {}\nfunction run() { console.log('x'); }\n");
        let calls = call_edges(&g);
        let e = calls
            .iter()
            .find(|e| {
                e.props.get("callee") == Some(&Json::str("log"))
                    && e.props.get("method") == Some(&Json::Bool(true))
            })
            .expect("the console.log() call");
        assert_eq!(e.props.get("resolution"), Some(&Json::str("external")));
        assert_eq!(e.props.get("resolved"), Some(&Json::Bool(false)));
        assert!(
            e.to.starts_with("unresolved::"),
            "explicit UnresolvedSymbol"
        );
    }
    #[test]
    fn exported_declarations_are_marked_without_marking_private_declarations() {
        let g = graph_for(
            "export function exported_fn() {}\n\
             function private_fn() {}\n\
             export class ExportedClass {}\n\
             class PrivateClass {}\n\
             export interface ExportedInterface {}\n\
             interface PrivateInterface {}\n\
             export const EXPORTED_CONST = 1;\n\
             const PRIVATE_CONST = 1;\n\
             export namespace ExportedNamespace {}\n\
             namespace PrivateNamespace {}\n",
        );
        for name in [
            "exported_fn",
            "ExportedClass",
            "ExportedInterface",
            "EXPORTED_CONST",
            "ExportedNamespace",
        ] {
            let node = g
                .nodes()
                .find(|n| n.name == name)
                .unwrap_or_else(|| panic!("expected node named {name}"));
            assert_eq!(
                node.props.get("exported"),
                Some(&Json::Bool(true)),
                "{name}"
            );
        }
        for name in [
            "private_fn",
            "PrivateClass",
            "PrivateInterface",
            "PRIVATE_CONST",
            "PrivateNamespace",
        ] {
            let node = g
                .nodes()
                .find(|n| n.name == name)
                .unwrap_or_else(|| panic!("expected node named {name}"));
            assert_eq!(node.props.get("exported"), None, "{name}");
        }
    }

    #[test]
    fn default_export_records_both_export_properties() {
        let g = graph_for("export default function chosen() {}\n");
        let node = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "chosen")
            .expect("default-exported function");
        assert_eq!(node.props.get("exported"), Some(&Json::Bool(true)));
        assert_eq!(node.props.get("default_export"), Some(&Json::Bool(true)));
    }

    #[test]
    fn default_export_object_with_from_key_is_not_a_reexport() {
        let g = graph_for("export default { from: \"x\" };\n");
        assert_eq!(
            g.edges().filter(|e| e.kind == edge::IMPORTS).count(),
            0,
            "a nested object key named from must not create an import"
        );
    }

    #[test]
    fn default_export_call_with_from_argument_is_not_a_reexport() {
        let g = graph_for("export default f(from, \"./p\");\n");
        assert_eq!(
            g.edges().filter(|e| e.kind == edge::IMPORTS).count(),
            0,
            "a nested argument named from must not create an import"
        );
    }

    #[test]
    fn named_reexport_matches_javascript_import_edge_shape() {
        use crate::lang::javascript::{lower as js_lower, parser as js_parser};

        let barrel = parse("barrel.ts", "export { X } from './y';\n");
        let target = parse("y.ts", "export function X() {}\n");
        let ts_files = [
            SourceFile {
                rel_path: "barrel.ts".to_string(),
                module_path: vec!["barrel".to_string()],
                source: &barrel.source,
                root: &barrel.root,
            },
            SourceFile {
                rel_path: "y.ts".to_string(),
                module_path: vec!["y".to_string()],
                source: &target.source,
                root: &target.root,
            },
        ];
        let ts_graph = lower("demo", &ts_files, &[]);
        let ts_edge = ts_graph
            .edges()
            .find(|e| e.kind == edge::IMPORTS && e.from == "file::barrel.ts")
            .expect("TypeScript re-export import edge");

        let js_tree = js_parser::parse("barrel.js", "export { X } from './y';\n");
        let js_file = SourceFile {
            rel_path: "barrel.js".to_string(),
            module_path: vec!["barrel".to_string()],
            source: &js_tree.source,
            root: &js_tree.root,
        };
        let js_graph = js_lower::lower("demo", std::slice::from_ref(&js_file), &[]);
        let js_edge = js_graph
            .edges()
            .find(|e| e.kind == edge::IMPORTS)
            .expect("JavaScript re-export import edge");

        // JS precedent: javascript::lower::Lowerer::handle_import emits IMPORTS
        // with the source path and external=false. TS keeps its stronger concrete
        // file target while matching that edge shape and adding reexport=true.
        assert_eq!(ts_edge.kind, js_edge.kind);
        assert_eq!(ts_edge.props.get("path"), js_edge.props.get("path"));
        assert_eq!(ts_edge.props.get("external"), js_edge.props.get("external"));
        assert_eq!(ts_edge.to, "file::y.ts");
        assert_eq!(ts_edge.props.get("reexport"), Some(&Json::Bool(true)));
    }

    #[test]
    fn type_reexport_is_lowered_as_an_import_edge() {
        let g = graph_for("export type { Shape } from './shape';\n");
        let edge = g
            .edges()
            .find(|e| e.kind == edge::IMPORTS)
            .expect("type-only re-export import edge");
        assert_eq!(edge.props.get("path"), Some(&Json::str("./shape")));
        assert_eq!(edge.props.get("reexport"), Some(&Json::Bool(true)));
    }

    #[test]
    fn star_reexport_is_marked_without_fabricated_names() {
        let g = graph_for("export * from './all';\n");
        let edge = g
            .edges()
            .find(|e| e.kind == edge::IMPORTS)
            .expect("star re-export import edge");
        assert_eq!(edge.props.get("reexport"), Some(&Json::Bool(true)));
        assert_eq!(edge.props.get("reexport_all"), Some(&Json::Bool(true)));
        assert_eq!(edge.props.get("names"), None);
    }

    #[test]
    fn missing_reexport_target_uses_unresolved_module_convention() {
        let g = graph_for("export { X } from './missing';\n");
        let edge = g
            .edges()
            .find(|e| e.kind == edge::IMPORTS)
            .expect("missing-target re-export import edge");
        assert!(edge.to.starts_with("mod::"), "{}", edge.to);
        let target = g
            .nodes()
            .find(|n| n.id == edge.to)
            .expect("synthesized unresolved module");
        assert_eq!(target.props.get("unresolved_path"), Some(&Json::Bool(true)));
        assert_eq!(edge.props.get("reexport"), Some(&Json::Bool(true)));
    }

    #[test]
    fn reexport_lowering_is_byte_deterministic() {
        let src =
            "export { X } from './y';\nexport type { Shape } from './shape';\nexport * from './all';\n";
        assert_eq!(graph_for(src).to_jsonl(), graph_for(src).to_jsonl());
    }
}
