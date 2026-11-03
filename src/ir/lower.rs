//! Lower the Rust CST into the canonical graph.
//!
//! This is where language-specific structure becomes the neutral ontology. Two
//! conservative principles hold throughout:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to
//!    a concrete project definition only when a scope level yields exactly one
//!    candidate. When a level yields several, the edge is emitted with the full
//!    `candidates` set and marked ambiguous — TrailTracker never picks one (there
//!    is no LLM in the airgapped runtime to ask). When no level matches, the
//!    target is an explicit external/unresolved node.
//! 2. **Everything comes from real tokens.** Calls are detected as genuine
//!    `path(...)` / `.method(...)` patterns over the lossless tree, never guessed.
//!
//! Resolution uses a deterministic **scope ladder** (most specific first; the
//! first level with any candidates decides):
//!   receiver (`self`/`Self`) → qualified-type (`Type::m`) → qualified-module
//!   (`a::b::f`) → local module → file imports → global. Every edge records which
//!   level resolved it, so the call graph is fully auditable.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::rust::lexer::{is_keyword, kind as tk};
use crate::lang::rust::parser::node as cst;

/// Lower a whole crate's worth of files plus manifest dependencies into a graph.
/// The input is the shared [`SourceFile`] batch; for Rust each file's
/// `module_path` is its crate-relative module segments (empty for the crate root
/// `lib.rs` / `main.rs`).
pub fn lower(package: &str, files: &[SourceFile<'_>], manifest_deps: &[String]) -> Graph {
    lower_impl(package, files, manifest_deps, false)
}

/// [`lower`] plus the opt-in CPG overlay (ADR-0003): after the base facts are
/// emitted, each function body additionally yields `Statement` nodes and
/// intra-function `FLOWS_TO`/`DATA_DEP` edges. The base sub-graph is
/// byte-identical to [`lower`]'s — the overlay is strictly additive.
pub fn lower_with_cpg(package: &str, files: &[SourceFile<'_>], manifest_deps: &[String]) -> Graph {
    lower_impl(package, files, manifest_deps, true)
}

fn lower_impl(
    package: &str,
    files: &[SourceFile<'_>],
    manifest_deps: &[String],
    cpg: bool,
) -> Graph {
    // Crate-local roots: the package itself plus every module segment. A `use`
    // whose first segment is one of these is a relative/intra-crate import, not
    // an external dependency. Conservative: prefer under-reporting externals to
    // fabricating one for a path we actually own.
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
        method_by_name: BTreeMap::new(),
        fn_by_module: BTreeMap::new(),
        method_by_type: BTreeMap::new(),
        type_by_name: BTreeMap::new(),
        imports: Vec::new(),
        cur_file: 0,
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id.clone(),
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("cargo"))],
    );
    for dep in manifest_deps {
        let dep_id = ext_id(dep);
        lo.g.upsert_node(
            dep_id.clone(),
            ont::EXTERNAL_DEPENDENCY,
            dep.clone(),
            vec![
                ("external", Json::Bool(true)),
                ("source", Json::str("manifest")),
            ],
        );
        lo.g.add_edge(pkg_id.clone(), edge::DEPENDS_ON, dep_id, vec![]);
    }

    // Pass B: create definition nodes + structural edges, build symbol tables
    // and per-file import maps.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_types: Vec<PendingType> = Vec::new();
    for (idx, f) in files.iter().enumerate() {
        lo.imports.push(BTreeMap::new());
        lo.cur_file = idx;
        let li = LineIndex::new(f.source);
        let leaf = lo.ensure_modules(&f.module_path);
        let file_id = format!("file::{}", f.rel_path);
        lo.g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("rust")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(leaf, edge::CONTAINS, file_id.clone(), vec![]);
        lo.walk_items(
            f.root,
            &file_id,
            &file_id,
            &f.module_path,
            f.source,
            &li,
            None,
            &mut pend_fns,
            &mut pend_types,
        );
    }

    // Pass C: resolve calls (scope ladder) and type usages against the complete
    // symbol tables.
    for pf in &pend_fns {
        let ctx = Ctx {
            module_join: mod_join(&pf.module_path),
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
        if cpg {
            if let Some(block) = pf.block {
                crate::ir::cpg::emit_function_cpg(
                    &mut lo.g,
                    &pf.id,
                    block,
                    pf.signature,
                    pf.source,
                );
            }
        }
    }
    for pt in &pend_types {
        for region in [
            cst::FIELD_LIST,
            cst::TUPLE_FIELDS,
            cst::VARIANT_LIST,
            cst::HEADER,
        ] {
            if let Some(r) = pt.node.child(region) {
                lo.emit_type_uses(&pt.id, r, pt.source);
            }
        }
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    local_roots: BTreeSet<String>,
    /// Simple name → all function node ids (global level).
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// Simple name → method node ids only (global method-call level).
    method_by_name: BTreeMap<String, Vec<String>>,
    /// (module_join, name) → function ids (local / qualified-module levels).
    fn_by_module: BTreeMap<(String, String), Vec<String>>,
    /// (type_name, method_name) → method ids (receiver / qualified-type levels).
    method_by_type: BTreeMap<(String, String), Vec<String>>,
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
    module_path: Vec<String>,
    owner_type: Option<String>,
    file_idx: usize,
}

struct PendingType<'a> {
    id: String,
    source: &'a str,
    node: &'a Node,
}

/// A detected call site, carrying the native Rust scope hints.
struct Call {
    /// Final segment: the called function / method name.
    name: String,
    /// Qualifier path before the name (`a::b` in `a::b::f()`), empty for bare.
    path: Vec<String>,
    /// True for `.method(...)` calls.
    method: bool,
    /// Immediate receiver identifier for method calls (`self`, a variable, …).
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

    fn ensure_modules(&mut self, path: &[String]) -> String {
        let pkg = self.pkg_id();
        let root = "mod::crate".to_string();
        self.g.upsert_node(
            root.clone(),
            ont::MODULE,
            "crate",
            vec![("language", Json::str("rust"))],
        );
        self.g.add_edge(pkg, edge::CONTAINS, root.clone(), vec![]);
        let mut cur = root;
        let mut acc = vec!["crate".to_string()];
        for seg in path {
            acc.push(seg.clone());
            let id = format!("mod::{}", acc.join("::"));
            self.g.upsert_node(
                id.clone(),
                ont::MODULE,
                seg.clone(),
                vec![("language", Json::str("rust"))],
            );
            self.g
                .add_edge(cur.clone(), edge::CONTAINS, id.clone(), vec![]);
            cur = id;
        }
        cur
    }

    #[allow(clippy::too_many_arguments)]
    fn walk_items<'a>(
        &mut self,
        block: &'a Node,
        file_id: &str,
        container_id: &str,
        mod_path: &[String],
        src: &'a str,
        li: &LineIndex,
        owner_type: Option<&OwnerType>,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_types: &mut Vec<PendingType<'a>>,
    ) {
        for item in block.child_nodes() {
            match item.kind {
                cst::FUNCTION => {
                    self.handle_fn(item, container_id, mod_path, src, li, owner_type, pend_fns)
                }
                cst::STRUCT | cst::ENUM | cst::TRAIT | cst::UNION | cst::TYPE_ALIAS => {
                    self.handle_type(item, container_id, mod_path, src, li, pend_types)
                }
                cst::IMPL => {
                    self.handle_impl(item, file_id, mod_path, src, li, pend_fns, pend_types)
                }
                cst::MODULE => self.handle_mod(
                    item,
                    file_id,
                    container_id,
                    mod_path,
                    src,
                    li,
                    pend_fns,
                    pend_types,
                ),
                cst::USE => self.handle_use(item, file_id, src),
                cst::EXTERN_CRATE => self.handle_extern_crate(item, file_id, src),
                cst::CONST | cst::STATIC => {
                    self.handle_const(item, container_id, mod_path, src, li)
                }
                cst::EXTERN_BLOCK => {
                    if let Some(inner) = item.child(cst::ITEM_BLOCK) {
                        self.walk_items(
                            inner,
                            file_id,
                            container_id,
                            mod_path,
                            src,
                            li,
                            owner_type,
                            pend_fns,
                            pend_types,
                        );
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
        container_id: &str,
        mod_path: &[String],
        src: &'a str,
        li: &LineIndex,
        owner_type: Option<&OwnerType>,
        pend_fns: &mut Vec<PendingFn<'a>>,
    ) {
        let name = name_text(item, src).unwrap_or("<anonymous>").to_string();
        let line = li.line_col(name_span_start(item)).line;
        let module_join = mod_join(mod_path);
        let qual = match owner_type {
            Some(o) => format!("{}::{}::{}", module_join, o.name, name),
            None => format!("{}::{}", module_join, name),
        };
        let id = format!("fn::{qual}#{line}");
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("rust")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            ("has_body", Json::Bool(item.child(cst::BLOCK).is_some())),
        ];
        if let Some(o) = owner_type {
            props.push(("receiver_type", Json::str(o.name.clone())));
            props.push(("is_method", Json::Bool(true)));
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, name.clone(), props);
        self.g
            .add_edge(container_id, edge::DECLARES, id.clone(), vec![]);

        // Indexes for the resolution ladder.
        self.fn_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());
        self.fn_by_module
            .entry((module_join, name.clone()))
            .or_default()
            .push(id.clone());
        if let Some(o) = owner_type {
            self.method_by_name
                .entry(name.clone())
                .or_default()
                .push(id.clone());
            self.method_by_type
                .entry((o.name.clone(), name.clone()))
                .or_default()
                .push(id.clone());
            if let Some(type_id) = &o.id {
                self.g
                    .add_edge(type_id.clone(), edge::HAS_METHOD, id.clone(), vec![]);
            }
        }

        pend_fns.push(PendingFn {
            id,
            source: src,
            block: item.child(cst::BLOCK),
            signature: item.child(cst::SIGNATURE),
            module_path: mod_path.to_vec(),
            owner_type: owner_type.map(|o| o.name.clone()),
            file_idx: self.cur_file,
        });
    }

    fn handle_type<'a>(
        &mut self,
        item: &'a Node,
        container_id: &str,
        mod_path: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_types: &mut Vec<PendingType<'a>>,
    ) {
        let name = name_text(item, src).unwrap_or("<anonymous>").to_string();
        let line = li.line_col(name_span_start(item)).line;
        let subtype = match item.kind {
            cst::STRUCT => "struct",
            cst::ENUM => "enum",
            cst::TRAIT => "trait",
            cst::UNION => "union",
            cst::TYPE_ALIAS => "type_alias",
            _ => "type",
        };
        let qual = format!("{}::{}", mod_join(mod_path), name);
        let id = format!("type::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str(subtype)),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("rust")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
            ],
        );
        self.g
            .add_edge(container_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name.entry(name).or_default().push(id.clone());
        pend_types.push(PendingType {
            id,
            source: src,
            node: item,
        });
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_impl<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        mod_path: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_types: &mut Vec<PendingType<'a>>,
    ) {
        let (self_name, trait_name) = impl_header_types(item, src);
        let self_type_id = self_name.as_ref().and_then(|n| self.unique_type(n));

        if let (Some(self_id), Some(trait_n)) = (&self_type_id, &trait_name) {
            let trait_target = self
                .unique_type(trait_n)
                .unwrap_or_else(|| unresolved_id(trait_n));
            if !self.g.has_node(&trait_target) {
                self.g.upsert_node(
                    trait_target.clone(),
                    ont::UNRESOLVED,
                    trait_n.clone(),
                    vec![
                        ("unresolved", Json::Bool(true)),
                        ("role", Json::str("trait")),
                    ],
                );
            }
            self.g.add_edge(
                self_id.clone(),
                edge::IMPLEMENTS,
                trait_target,
                vec![("trait_name", Json::str(trait_n.clone()))],
            );
        }

        let owner = OwnerType {
            name: self_name.unwrap_or_else(|| "<unknown>".to_string()),
            id: self_type_id,
        };
        if let Some(inner) = item.child(cst::ITEM_BLOCK) {
            self.walk_items(
                inner,
                file_id,
                file_id,
                mod_path,
                src,
                li,
                Some(&owner),
                pend_fns,
                pend_types,
            );
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_mod<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        container_id: &str,
        mod_path: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_types: &mut Vec<PendingType<'a>>,
    ) {
        let name = match name_text(item, src) {
            Some(n) => n.to_string(),
            None => return,
        };
        let mut child_path = mod_path.to_vec();
        child_path.push(name.clone());
        let mod_id = format!("mod::crate::{}", child_path.join("::"));
        let inline = item.child(cst::ITEM_BLOCK).is_some();
        self.g.upsert_node(
            mod_id.clone(),
            ont::MODULE,
            name,
            vec![
                ("language", Json::str("rust")),
                ("inline", Json::Bool(inline)),
                ("external_file", Json::Bool(!inline)),
            ],
        );
        self.g
            .add_edge(container_id, edge::CONTAINS, mod_id.clone(), vec![]);
        if let Some(inner) = item.child(cst::ITEM_BLOCK) {
            self.walk_items(
                inner,
                file_id,
                &mod_id,
                &child_path,
                src,
                li,
                None,
                pend_fns,
                pend_types,
            );
        }
    }

    fn handle_use(&mut self, item: &Node, file_id: &str, src: &str) {
        let tree = match item.child(cst::USE_TREE) {
            Some(t) => t,
            None => return,
        };

        // Record imported leaf names for the import resolution level.
        let mut leaves = Vec::new();
        flatten_use(tree, &[], src, &mut leaves);
        for (leaf, segs) in &leaves {
            self.imports[self.cur_file].insert(leaf.clone(), segs.clone());
        }

        let (root, path) = use_root_and_path(tree, src);
        if root.is_empty() {
            return;
        }
        let internal = matches!(root.as_str(), "crate" | "self" | "super" | "Self")
            || self.local_roots.contains(&root);
        if internal {
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                "mod::crate",
                vec![("path", Json::str(path)), ("external", Json::Bool(false))],
            );
        } else {
            let dep_id = ext_id(&root);
            self.g.upsert_node(
                dep_id.clone(),
                ont::EXTERNAL_DEPENDENCY,
                root.clone(),
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

    fn handle_extern_crate(&mut self, item: &Node, file_id: &str, src: &str) {
        let name = match name_text(item, src) {
            Some(n) => n.to_string(),
            None => return,
        };
        let dep_id = ext_id(&name);
        self.g.upsert_node(
            dep_id.clone(),
            ont::EXTERNAL_DEPENDENCY,
            name,
            vec![
                ("external", Json::Bool(true)),
                ("source", Json::str("extern_crate")),
            ],
        );
        self.g
            .add_edge(file_id, edge::IMPORTS, dep_id.clone(), vec![]);
        self.g
            .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
    }

    fn handle_const(
        &mut self,
        item: &Node,
        container_id: &str,
        mod_path: &[String],
        src: &str,
        li: &LineIndex,
    ) {
        let name = name_text(item, src).unwrap_or("<anonymous>").to_string();
        let line = li.line_col(name_span_start(item)).line;
        let kind = if item.kind == cst::STATIC {
            "static"
        } else {
            "const"
        };
        let id = format!("const::{}::{}", mod_join(mod_path), name);
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            name,
            vec![
                ("binding", Json::str(kind)),
                ("language", Json::str("rust")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(container_id, edge::DECLARES, id, vec![]);
    }

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        if call.method {
            // Receiver scope: `self.m()` / `Self.m()` → enclosing type's methods.
            if matches!(call.receiver.as_deref(), Some("self") | Some("Self")) {
                if let Some(owner) = &ctx.owner_type {
                    let c = self.methods_of(owner, &call.name);
                    if !c.is_empty() {
                        return mk(c, "receiver");
                    }
                }
            }
            // Other method calls have an unknown receiver type (no inference yet):
            // fall back to a global match among *methods* only.
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

        if !call.path.is_empty() {
            // Qualified-type: `Type::m()` / `Self::m()`.
            let qual_last = call.path.last().unwrap();
            let type_name = if qual_last == "Self" {
                ctx.owner_type.clone()
            } else {
                Some(qual_last.clone())
            };
            if let Some(t) = type_name {
                let c = self.methods_of(&t, &call.name);
                if !c.is_empty() {
                    return mk(c, "qualified_type");
                }
            }
            // Qualified-module: `a::b::f()`.
            let mut c = Vec::new();
            for m in self.module_candidates(&call.path, ctx) {
                c.extend(self.fns_in_module(&m, &call.name));
            }
            dedup(&mut c);
            if !c.is_empty() {
                return mk(c, "qualified");
            }
        } else {
            // Local module.
            let c = self.fns_in_module(&ctx.module_join, &call.name);
            if !c.is_empty() {
                return mk(c, "local");
            }
            // File imports.
            if let Some(segs) = ctx.imports.get(&call.name) {
                if let Some(modj) = self.import_module_join(segs) {
                    let c = self.fns_in_module(&modj, &call.name);
                    if !c.is_empty() {
                        return mk(c, "import");
                    }
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
        let qualifier = if call.path.is_empty() {
            None
        } else {
            Some(call.path.join("::"))
        };
        let mut props = vec![
            ("callee", Json::str(call.name.clone())),
            ("method", Json::Bool(call.method)),
            ("resolution", Json::str(res.level)),
        ];
        if let Some(q) = qualifier {
            props.push(("qualifier", Json::str(q)));
        }
        match res.outcome {
            Outcome::One(id) => {
                props.push(("resolved", Json::Bool(true)));
                props.push(("candidate_count", Json::U64(1)));
                self.g.add_edge(caller_id, edge::CALLS, id, props);
            }
            Outcome::Many(ids) => {
                let target = unresolved_id(&call.name);
                self.g.upsert_node(
                    target.clone(),
                    ont::UNRESOLVED,
                    call.name.clone(),
                    vec![
                        ("unresolved", Json::Bool(true)),
                        ("role", Json::str("call")),
                    ],
                );
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
                self.g.upsert_node(
                    target.clone(),
                    ont::UNRESOLVED,
                    call.name.clone(),
                    vec![
                        ("unresolved", Json::Bool(true)),
                        ("role", Json::str("call")),
                    ],
                );
                props.push(("resolved", Json::Bool(false)));
                props.push(("candidate_count", Json::U64(0)));
                self.g.add_edge(caller_id, edge::CALLS, target, props);
            }
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

    /// Candidate module-join strings for a qualifier path (excluding the callee
    /// name, which has already been split off).
    fn module_candidates(&self, path: &[String], ctx: &Ctx) -> Vec<String> {
        if path.is_empty() {
            return Vec::new();
        }
        match path[0].as_str() {
            "crate" => vec![join_crate(&path[1..])],
            "self" => vec![join_under(&ctx.module_join, &path[1..])],
            "super" => vec![join_under(&parent_module(&ctx.module_join), &path[1..])],
            "Self" => Vec::new(),
            _ => vec![join_crate(path), join_under(&ctx.module_join, path)],
        }
    }

    /// Module-join for an imported symbol's defining module (path includes the
    /// leaf). `None` when the import points outside the crate.
    fn import_module_join(&self, segs: &[String]) -> Option<String> {
        if segs.len() < 2 {
            return None;
        }
        let module_segs = &segs[..segs.len() - 1];
        match module_segs[0].as_str() {
            "crate" => Some(join_crate(&module_segs[1..])),
            first if self.local_roots.contains(first) => Some(join_crate(module_segs)),
            _ => None,
        }
    }

    fn unique_type(&self, name: &str) -> Option<String> {
        match self.type_by_name.get(name) {
            Some(ids) if ids.len() == 1 => Some(ids[0].clone()),
            _ => None,
        }
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
}

struct OwnerType {
    name: String,
    id: Option<String>,
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
    if path.is_empty() {
        "crate".to_string()
    } else {
        format!("crate::{}", path.join("::"))
    }
}

fn join_crate(segs: &[String]) -> String {
    if segs.is_empty() {
        "crate".to_string()
    } else {
        format!("crate::{}", segs.join("::"))
    }
}

fn join_under(base: &str, segs: &[String]) -> String {
    if segs.is_empty() {
        base.to_string()
    } else {
        format!("{}::{}", base, segs.join("::"))
    }
}

fn parent_module(module_join: &str) -> String {
    match module_join.rsplit_once("::") {
        Some((head, _)) => head.to_string(),
        None => "crate".to_string(),
    }
}

fn dedup(v: &mut Vec<String>) {
    let mut seen = BTreeSet::new();
    v.retain(|x| seen.insert(x.clone()));
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

/// Extract `(self_type, trait)` simple names from an impl header. Only
/// identifiers at angle-depth 0 are considered, so generics and trait args are
/// skipped. Handles `impl Trait for Type`, `impl Type`, and path-qualified names.
fn impl_header_types(item: &Node, src: &str) -> (Option<String>, Option<String>) {
    let header = match item.child(cst::HEADER) {
        Some(h) => h,
        None => return (None, None),
    };
    let mut before: Vec<String> = Vec::new();
    let mut after: Vec<String> = Vec::new();
    let mut seen_for = false;
    let mut depth: i32 = 0;
    for c in &header.children {
        let t = match c {
            Child::Token(t) if !t.trivia => t,
            _ => continue,
        };
        let text = t.span.text(src);
        if t.kind == tk::PUNCT {
            for ch in text.chars() {
                if ch == '<' {
                    depth += 1;
                } else if ch == '>' {
                    depth -= 1;
                }
            }
            if depth < 0 {
                depth = 0;
            }
            continue;
        }
        if t.kind != tk::IDENT || depth != 0 {
            continue;
        }
        match text {
            "for" => seen_for = true,
            "where" => break,
            kw if is_keyword(kw) => {}
            name if seen_for => after.push(name.to_string()),
            name => before.push(name.to_string()),
        }
    }
    if seen_for {
        (after.last().cloned(), before.last().cloned())
    } else {
        (before.last().cloned(), None)
    }
}

/// `(root_segment, full_path_text)` of a use tree (for external-dep detection).
fn use_root_and_path(tree: &Node, src: &str) -> (String, String) {
    let mut path = String::new();
    let mut root = String::new();
    for c in &tree.children {
        if let Child::Token(t) = c {
            if t.trivia {
                continue;
            }
            let text = t.span.text(src);
            if (t.kind == tk::IDENT || t.kind == tk::RAW_IDENT) && root.is_empty() {
                root = text.to_string();
            }
            if t.kind == tk::IDENT || t.kind == tk::RAW_IDENT || text == "::" {
                path.push_str(text);
            } else {
                break;
            }
        } else {
            break;
        }
    }
    (root, path)
}

/// Flatten a use tree into `(leaf_name, full_path_segments)` pairs. Handles a
/// path, brace groups (`{a, b}`), `as` renames, `self` in braces, and skips
/// glob imports (no nameable leaf). Best-effort over the real CST.
fn flatten_use(tree: &Node, prefix: &[String], src: &str, out: &mut Vec<(String, Vec<String>)>) {
    let refs: Vec<&Child> = tree.children.iter().collect();
    flatten_seq(&refs, prefix, src, out);
}

fn flatten_seq(
    children: &[&Child],
    prefix: &[String],
    src: &str,
    out: &mut Vec<(String, Vec<String>)>,
) {
    let mut segs: Vec<String> = prefix.to_vec();
    let mut alias: Option<String> = None;
    let mut expect_alias = false;
    for c in children {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => {
                let text = t.span.text(src);
                if t.kind == tk::IDENT || t.kind == tk::RAW_IDENT {
                    if expect_alias {
                        alias = Some(text.to_string());
                        expect_alias = false;
                    } else if text == "as" {
                        expect_alias = true;
                    } else if text == "self" {
                        if let Some(last) = prefix.last() {
                            out.push((last.clone(), prefix.to_vec()));
                        }
                        return;
                    } else {
                        segs.push(text.to_string());
                    }
                } else if t.kind == tk::PUNCT && text == "*" {
                    return; // glob: no nameable leaf
                }
            }
            Child::Node(g) if g.kind == cst::BRACE => {
                expand_brace(g, &segs, src, out);
                return;
            }
            Child::Node(_) => {}
        }
    }
    if !segs.is_empty() {
        let leaf = alias.unwrap_or_else(|| segs.last().cloned().unwrap());
        out.push((leaf, segs));
    }
}

fn expand_brace(g: &Node, prefix: &[String], src: &str, out: &mut Vec<(String, Vec<String>)>) {
    let mut items: Vec<Vec<&Child>> = vec![Vec::new()];
    for c in &g.children {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) if matches!(t.span.text(src), "{" | "}") => {}
            Child::Token(t) if t.span.text(src) == "," => items.push(Vec::new()),
            other => items.last_mut().unwrap().push(other),
        }
    }
    for item in items {
        if !item.is_empty() {
            flatten_seq(&item, prefix, src, out);
        }
    }
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
                ident: t.kind == tk::IDENT || t.kind == tk::RAW_IDENT,
            }),
            Child::Node(n) => v.push(El::Grp(n)),
        }
    }
    v
}

fn is_path_qualifier(text: &str) -> bool {
    matches!(text, "crate" | "super" | "self" | "Self")
}

/// Detect `path(...)` and `.method(...)` call sites over the real token tree,
/// capturing the full qualifier path and (for methods) the receiver. Recurses
/// into nested groups. Keywords (except path qualifiers) and macro invocations
/// are excluded.
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        // Method call: `.` ident `(...)`.
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
                            path: Vec::new(),
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
        // Path call: ident (`::` ident)* `(...)`.
        if is_ident_el(&els[i]) {
            let prev = if i > 0 { tok_text(&els[i - 1]) } else { None };
            let text = tok_text(&els[i]).unwrap_or("");
            let allowed = !is_keyword(text) || is_path_qualifier(text);
            if prev != Some("::") && prev != Some(".") && allowed {
                let mut segs = vec![text.to_string()];
                let mut j = i;
                while j + 2 < n && tok_text(&els[j + 1]) == Some("::") && is_ident_el(&els[j + 2]) {
                    segs.push(tok_text(&els[j + 2]).unwrap_or("").to_string());
                    j += 2;
                }
                if j + 1 < n {
                    if tok_text(&els[j + 1]) == Some("!") {
                        i = j + 2; // macro invocation, not a call
                        continue;
                    }
                    if let Some(g) = grp(&els[j + 1]) {
                        if g.kind == cst::PAREN {
                            let name = segs.pop().unwrap();
                            out.push(Call {
                                name,
                                path: segs,
                                method: false,
                                receiver: None,
                            });
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
        if let Some(g) = grp(e) {
            scan_calls(g, src, out);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::rust::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("lib.rs", src);
        let file = SourceFile {
            rel_path: "lib.rs".to_string(),
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
    fn resolves_unique_local_call() {
        let g = graph_for("fn add(a: i32, b: i32) -> i32 { a + b }\nfn run() { add(1, 2); }");
        let calls = call_edges(&g);
        assert_eq!(calls.len(), 1);
        assert!(calls[0].to.starts_with("fn::crate::add"));
        assert_eq!(calls[0].props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(calls[0].props.get("resolution"), Some(&Json::str("local")));
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for("fn run() { mystery(); }");
        let calls = call_edges(&g);
        assert_eq!(calls.len(), 1);
        assert_eq!(
            calls[0].props.get("resolution"),
            Some(&Json::str("external"))
        );
        assert!(g.has_node("unresolved::mystery"));
    }

    #[test]
    fn self_method_resolves_via_receiver() {
        let g = graph_for("struct P; impl P { fn a(&self) { self.b(); } fn b(&self) {} }");
        let calls = call_edges(&g);
        let recv = calls
            .iter()
            .find(|e| e.props.get("resolution") == Some(&Json::str("receiver")));
        assert!(recv.is_some(), "self.b() should resolve via receiver scope");
        assert_eq!(recv.unwrap().props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn assoc_call_resolves_via_qualified_type() {
        let g = graph_for("struct P; impl P { fn new() -> P { P } } fn run() { P::new(); }");
        let calls = call_edges(&g);
        let q = calls
            .iter()
            .find(|e| e.props.get("resolution") == Some(&Json::str("qualified_type")));
        assert!(q.is_some(), "P::new() should resolve via qualified_type");
    }

    #[test]
    fn ambiguous_call_keeps_candidates() {
        // Two methods named `go` on different types → global_method ambiguity.
        let g = graph_for(
            "struct A; struct B; impl A { fn go(&self) {} } impl B { fn go(&self) {} } \
             fn run(x: A) { x.go(); }",
        );
        let calls = call_edges(&g);
        let amb = calls
            .iter()
            .find(|e| e.props.get("ambiguous") == Some(&Json::Bool(true)));
        assert!(amb.is_some(), "x.go() is ambiguous across two types");
        assert_eq!(
            amb.unwrap().props.get("candidate_count"),
            Some(&Json::U64(2))
        );
    }

    #[test]
    fn external_use_creates_dependency() {
        let g = graph_for("use std::fmt;\nfn x() {}");
        assert!(g.has_node("ext::std"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::std"));
    }
}
