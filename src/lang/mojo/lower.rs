//! Lower the Mojo CST into the canonical graph.
//!
//! This mirrors the Python lowering ([`crate::lang::python::lower`]) — same
//! conservative principles, same shared ontology, same deterministic scope
//! ladder — adapted to Mojo's surface. Mojo is a Python superset, so the call
//! detection, import handling and resolution machinery carry over verbatim; the
//! mapping differences are entirely at the definition layer:
//!
//! Honest mappings (see the IR Atlas):
//!   - `fn` **and** `def` → [`ont::FUNCTION`] (a `def_kind` property records which
//!     keyword introduced it); a function inside a struct/trait/class becomes a
//!     [`edge::HAS_METHOD`] of its enclosing type.
//!   - `struct` → [`ont::TYPE`] (`type_kind: struct`); its conformance list
//!     `struct S(Trait)` becomes [`edge::IMPLEMENTS`] edges (a struct *conforms
//!     to* a trait — it does not inherit it).
//!   - `trait` → [`ont::TYPE`] (`type_kind: trait`); a super-trait list
//!     `trait T(Base)` becomes [`edge::EXTENDS`] edges.
//!   - `class` → [`ont::TYPE`] (`type_kind: class`); base list → [`edge::EXTENDS`]
//!     (Mojo is a Python superset, so a `class` may appear).
//!   - `alias NAME = …` (at any scope outside a function body) and module-level
//!     `var`/`let` bindings → [`ont::CONSTANT`].
//!   - `import x` / `from x import y` → [`edge::IMPORTS`] (plus
//!     [`ont::EXTERNAL_DEPENDENCY`]/[`edge::DEPENDS_ON`] for non-project roots).
//!   - calls and `obj.method(...)` → [`edge::CALLS`], resolved by the scope ladder.
//!
//! No fabricated targets: an edge resolves to a concrete project definition only
//! when a scope level yields exactly one candidate; several candidates are emitted
//! as an ambiguous edge with the full `candidates` set; none resolves to an
//! explicit [`ont::EXTERNAL_DEPENDENCY`]/[`ont::UNRESOLVED`] node. There is no LLM
//! in the airgapped runtime to guess.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::Node;
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::mojo::lexer::{is_keyword, kind as tk};
use crate::lang::mojo::parser::node as cst;

/// Lower a whole project's worth of Mojo files into a graph. `manifest_deps` is
/// unused for Mojo (the pipeline's manifest reader is Cargo-only); dependencies
/// are discovered from `import` statements instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    // Project-local roots: the package plus every module segment. An import whose
    // first segment is one of these is an intra-project import, not an external
    // dependency. Conservative: prefer under-reporting externals to fabricating
    // one for a module we actually own.
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
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("mojo"))],
    );

    // Pass B: create definition nodes + structural edges, build symbol tables and
    // per-file import maps. Inheritance/conformance is deferred to pass C so a base
    // type defined later in the project still resolves.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_rels: Vec<PendingRel> = Vec::new();
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
                ("language", Json::str("mojo")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(leaf, edge::CONTAINS, file_id.clone(), vec![]);
        lo.walk_stmts(
            f.root,
            &file_id,
            &module_join,
            &[],
            None,
            false,
            f.source,
            &li,
            &mut pend_fns,
            &mut pend_rels,
        );
    }

    // Pass C: resolve calls (scope ladder), type usages, inheritance and
    // conformances against the now-complete symbol tables.
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
    for pe in &pend_rels {
        lo.emit_rel(pe);
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
    /// (module_join, name) → function ids (local-module level).
    fn_by_module: BTreeMap<(String, String), Vec<String>>,
    /// (type_name, method_name) → method ids (receiver level).
    method_by_type: BTreeMap<(String, String), Vec<String>>,
    /// Simple name → type (struct/trait/class) node ids.
    type_by_name: BTreeMap<String, Vec<String>>,
    /// Per-file import maps: imported leaf name → full dotted path segments.
    imports: Vec<BTreeMap<String, Vec<String>>>,
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

/// A deferred type relationship (`struct S(Trait)` → IMPLEMENTS, `trait T(Base)`
/// / `class K(Base)` → EXTENDS), resolved in pass C.
struct PendingRel {
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
    /// The called name (final attribute or bare name).
    name: String,
    /// True for `recv.name(...)` attribute calls.
    method: bool,
    /// Immediate receiver identifier for method calls (`self`, a variable).
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
                vec![("language", Json::str("mojo"))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    /// Walk a statement container (a `Module` or `Block`), creating definition
    /// nodes and recursing into nested scopes. `owner` is the nearest enclosing
    /// type (cleared when descending into a function); `in_function` gates
    /// local-binding suppression.
    #[allow(clippy::too_many_arguments)]
    fn walk_stmts<'a>(
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
        pend_rels: &mut Vec<PendingRel>,
    ) {
        for item in container.child_nodes() {
            match item.kind {
                cst::FUNCTION => self.handle_fn(
                    item,
                    file_id,
                    module_join,
                    scope,
                    owner,
                    src,
                    li,
                    pend_fns,
                    pend_rels,
                ),
                cst::STRUCT => self.handle_type(
                    item,
                    "struct",
                    edge::IMPLEMENTS,
                    file_id,
                    module_join,
                    scope,
                    src,
                    li,
                    pend_fns,
                    pend_rels,
                ),
                cst::TRAIT => self.handle_type(
                    item,
                    "trait",
                    edge::EXTENDS,
                    file_id,
                    module_join,
                    scope,
                    src,
                    li,
                    pend_fns,
                    pend_rels,
                ),
                cst::CLASS => self.handle_type(
                    item,
                    "class",
                    edge::EXTENDS,
                    file_id,
                    module_join,
                    scope,
                    src,
                    li,
                    pend_fns,
                    pend_rels,
                ),
                cst::COMPOUND => {
                    // A compound statement (if/for/with/try/…) is not a new scope:
                    // definitions inside it still belong to the enclosing
                    // type/module, so recurse with the same owner.
                    if let Some(block) = item.child(cst::BLOCK) {
                        self.walk_stmts(
                            block,
                            file_id,
                            module_join,
                            scope,
                            owner,
                            in_function,
                            src,
                            li,
                            pend_fns,
                            pend_rels,
                        );
                    }
                }
                cst::IMPORT => self.handle_import(item, file_id, src),
                cst::FROM_IMPORT => self.handle_from_import(item, file_id, src),
                cst::SIMPLE_STMT => self.handle_binding(
                    item,
                    file_id,
                    module_join,
                    scope,
                    owner,
                    in_function,
                    src,
                    li,
                ),
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
        pend_rels: &mut Vec<PendingRel>,
    ) {
        let name = name_text(item, src).unwrap_or("<anonymous>").to_string();
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(module_join, scope, &name);
        let id = format!("fn::{qual}#{line}");
        let block = item.child(cst::BLOCK);
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("mojo")),
            ("def_kind", Json::str(def_kind(item, src))),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            ("has_body", Json::Bool(block.is_some())),
        ];
        if is_async(item, src) {
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
            block,
            signature: item.child(cst::HEADER),
            module_join: module_join.to_string(),
            owner_type: owner.map(|o| o.name.clone()),
            file_idx: self.cur_file,
        });

        // Nested fns/types are not methods of the enclosing type: descend with a
        // fresh (None) owner and an extended scope path.
        if let Some(block) = block {
            let mut child_scope = scope.to_vec();
            child_scope.push(name);
            self.walk_stmts(
                block,
                file_id,
                module_join,
                &child_scope,
                None,
                true,
                src,
                li,
                pend_fns,
                pend_rels,
            );
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_type<'a>(
        &mut self,
        item: &'a Node,
        type_kind: &'static str,
        rel_edge: &'static str,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_rels: &mut Vec<PendingRel>,
    ) {
        let name = name_text(item, src).unwrap_or("<anonymous>").to_string();
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(module_join, scope, &name);
        // Include the line so a type redefined under the same qualified name stays
        // a distinct node instead of colliding on upsert (mirrors Function ids).
        let id = format!("type::{qual}#{line}");
        let mut props = vec![
            ("type_kind", Json::str(type_kind)),
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("mojo")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
        ];
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

        // Conformances / base types (defer resolution to pass C).
        for base in type_bases(item, src) {
            pend_rels.push(PendingRel {
                type_id: id.clone(),
                base_name: base,
                edge_kind: rel_edge,
            });
        }

        if let Some(block) = item.child(cst::BLOCK) {
            let owner = Owner {
                name: name.clone(),
                id: id.clone(),
            };
            let mut child_scope = scope.to_vec();
            child_scope.push(name);
            self.walk_stmts(
                block,
                file_id,
                module_join,
                &child_scope,
                Some(&owner),
                false,
                src,
                li,
                pend_fns,
                pend_rels,
            );
        }
    }

    /// `import a.b.c, d as e` — each clause names a module; the bound leaf is its
    /// first segment (or the alias).
    fn handle_import(&mut self, item: &Node, file_id: &str, src: &str) {
        let toks = top_level_tokens(item, src);
        let body = strip_leading(&toks, "import");
        for clause in split_commas(body.to_vec()) {
            let (segs, alias) = dotted_path_and_alias(&clause);
            if segs.is_empty() {
                continue;
            }
            let leaf = alias.unwrap_or_else(|| segs[0].clone());
            self.imports[self.cur_file].insert(leaf, segs.clone());
            self.emit_import_edge(file_id, &segs, &segs.join("."));
        }
    }

    /// `from a.b import c, d as e` / `from . import x` — one module, many names.
    fn handle_from_import(&mut self, item: &Node, file_id: &str, src: &str) {
        let all = top_level_tokens(item, src);
        let toks = strip_leading(&all, "from");
        // Split on the `import` keyword that separates module from the name list.
        let split = toks.iter().position(|t| t.text == "import");
        let (module_part, names_part) = match split {
            Some(p) => (&toks[..p], &toks[p + 1..]),
            None => (toks, &[][..]),
        };
        let (module_segs, _) = dotted_path_and_alias(module_part);
        let path_text = module_part
            .iter()
            .map(|t| t.text)
            .collect::<Vec<_>>()
            .join("");
        self.emit_import_edge(file_id, &module_segs, &path_text);

        for clause in split_commas(names_part.to_vec()) {
            let (segs, alias) = dotted_path_and_alias(&clause);
            if segs.is_empty() {
                continue; // e.g. a `*` glob — no nameable leaf
            }
            let leaf = alias.unwrap_or_else(|| segs.last().cloned().unwrap());
            // Full path to the imported symbol: module + name (mirrors the resolver
            // import-map shape so it can find the defining module).
            let mut full = module_segs.clone();
            full.extend(segs);
            self.imports[self.cur_file].insert(leaf, full);
        }
    }

    /// Emit the `IMPORTS` edge for one imported module path, plus the
    /// `ExternalDependency`/`DEPENDS_ON` pair when the root is not project-local.
    fn emit_import_edge(&mut self, file_id: &str, module_segs: &[String], path_text: &str) {
        let root = module_segs.first().cloned().unwrap_or_default();
        // A leading-dot relative import has an empty first segment.
        let relative = path_text.starts_with('.');
        if root.is_empty() && !relative {
            return;
        }
        let internal = relative || self.local_roots.contains(&root);
        if internal {
            let mod_id = if root.is_empty() {
                self.pkg_id() // relative import: anchor at the project package
            } else {
                let id = format!("mod::{root}");
                self.g.upsert_node(
                    id.clone(),
                    ont::MODULE,
                    root.clone(),
                    vec![("language", Json::str("mojo"))],
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

    /// `alias NAME = …` / module-level `var`/`let`/`NAME` bindings → a `Constant`.
    /// Only plain single-target bindings are recognized (no augmented assignment,
    /// no tuple unpacking) — conservative, never guessed. Local bindings inside a
    /// function body are skipped; `alias` is recognized at type scope too (a
    /// struct-level compile-time constant) but plain `var`/`let`/`NAME =` only at
    /// module scope (struct-level `var` is a field, not a constant).
    #[allow(clippy::too_many_arguments)]
    fn handle_binding(
        &mut self,
        item: &Node,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        owner: Option<&Owner>,
        in_function: bool,
        src: &str,
        li: &LineIndex,
    ) {
        if in_function {
            return; // function-local binding, not a module/type constant
        }
        let toks = top_level_tokens(item, src);
        let mut sig = toks.iter().filter(|t| t.kind != tk::NEWLINE);
        let first = match sig.next() {
            Some(t) => t,
            None => return,
        };
        // Determine the binding form and which token carries the bound name.
        let (binding_kind, name_tok) = if first.kind == tk::NAME && first.text == "alias" {
            match sig.next() {
                Some(t) if t.kind == tk::NAME && !is_keyword(t.text) => ("alias", t),
                _ => return,
            }
        } else if owner.is_none()
            && first.kind == tk::NAME
            && (first.text == "var" || first.text == "let")
        {
            match sig.next() {
                Some(t) if t.kind == tk::NAME && !is_keyword(t.text) => ("module_var", t),
                _ => return,
            }
        } else if owner.is_none() && first.kind == tk::NAME && !is_keyword(first.text) {
            // Bare `NAME = …` / `NAME: T = …` at module scope (Python-style).
            match sig.next() {
                Some(t) if t.text == "=" || t.text == ":" => ("module_var", first),
                _ => return,
            }
        } else {
            return;
        };

        let name = name_tok.text.to_string();
        let line = li.line_col(name_tok.span_start).line;
        let id = format!("const::{}", qual_name(module_join, scope, &name));
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            name,
            vec![
                ("binding", Json::str(binding_kind)),
                ("language", Json::str("mojo")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
    }

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        if call.method {
            // Receiver scope: `self.m()` → enclosing type's methods.
            if matches!(call.receiver.as_deref(), Some("self") | Some("cls")) {
                if let Some(owner) = &ctx.owner_type {
                    let c = self.methods_of(owner, &call.name);
                    if !c.is_empty() {
                        return mk(c, "receiver");
                    }
                }
            }
            // Unknown receiver type (no inference). The honest candidate set is
            // every same-name method PLUS every same-name free function — a Mojo
            // member call can reach module-level functions (`mod.f()`).
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

        // Local module.
        let c = self.fns_in_module(&ctx.module_join, &call.name);
        if !c.is_empty() {
            return mk(c, "local");
        }
        // File imports: a bare name brought in via `from mod import name`.
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

    /// Resolve a deferred type relationship into a concrete `IMPLEMENTS`/`EXTENDS`
    /// edge, pointing at the project type when unique, otherwise an explicit
    /// `UnresolvedSymbol` (a stdlib/third-party base we cannot see in an airgap).
    fn emit_rel(&mut self, pe: &PendingRel) {
        let role = if pe.edge_kind == edge::IMPLEMENTS {
            "conformance"
        } else {
            "supertype"
        };
        let target = match self.unique_type(&pe.base_name) {
            Some(id) => id,
            None => {
                let id = unresolved_id(&pe.base_name);
                if !self.g.has_node(&id) {
                    self.g.upsert_node(
                        id.clone(),
                        ont::UNRESOLVED,
                        pe.base_name.clone(),
                        vec![("unresolved", Json::Bool(true)), ("role", Json::str(role))],
                    );
                }
                id
            }
        };
        self.g.add_edge(
            pe.type_id.clone(),
            pe.edge_kind,
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

    /// Add `USES_TYPE` edges for identifiers in `region` (a function `Header`,
    /// i.e. parameter/return annotations) that name a unique project type.
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

/// Dotted module-join for a file's module path: `["a","b"]` → `"a.b"`, `[]` → "".
fn mod_join(path: &[String]) -> String {
    path.join(".")
}

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

/// Which keyword introduced a function: `"fn"` or `"def"` (defaults to `"fn"` if
/// neither is seen, which cannot happen for a well-formed Function node).
fn def_kind(item: &Node, src: &str) -> &'static str {
    for t in item.tokens() {
        match t.span.text(src) {
            "fn" => return "fn",
            "def" => return "def",
            _ => {}
        }
    }
    "fn"
}

/// True if a function carries an `async` modifier before its `fn`/`def` keyword.
fn is_async(item: &Node, src: &str) -> bool {
    for t in item.tokens() {
        match t.span.text(src) {
            "async" => return true,
            "fn" | "def" => return false,
            _ => {}
        }
    }
    false
}

/// Decorator names attached to a fn/struct/trait/class, as a JSON array property
/// (the last top-level identifier of each `@expr`, e.g. `value` from `@value`),
/// or `None` when there are no decorators.
fn decorators(item: &Node, src: &str) -> Option<Json> {
    let mut names: Vec<Json> = Vec::new();
    for d in item.children_of(cst::DECORATOR) {
        let mut last: Option<&str> = None;
        for t in d.tokens() {
            if t.kind == tk::NAME && !is_keyword(t.span.text(src)) {
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

/// Conformance / base-type simple names from a `struct S(A, b.B)`, `trait T(A)`,
/// or `class K(A)` header. Only the final identifier of each comma-separated entry
/// is taken (`B` from `b.B`); the generic-parameter `[...]` group is ignored, as
/// are keyword arguments such as `metaclass=...`.
fn type_bases(item: &Node, src: &str) -> Vec<String> {
    let header = match item.child(cst::HEADER) {
        Some(h) => h,
        None => return Vec::new(),
    };
    // Conformances/bases live in the `(...)` group; `[...]` holds generic params.
    let paren = match header.child(cst::PAREN) {
        Some(p) => p,
        None => return Vec::new(),
    };
    let mut bases = Vec::new();
    for clause in split_commas(top_level_tokens(paren, src)) {
        // Skip keyword args (`metaclass=Meta`): they contain a top-level `=`.
        if clause.iter().any(|t| t.text == "=") {
            continue;
        }
        if let Some(last) = clause
            .iter()
            .rev()
            .find(|t| t.kind == tk::NAME && !is_keyword(t.text))
        {
            bases.push(last.text.to_string());
        }
    }
    bases
}

/// A flat token (text + kind + start), used by the small token-list helpers.
#[derive(Clone, Copy)]
struct Tok<'a> {
    text: &'a str,
    kind: &'static str,
    span_start: u32,
}

/// Direct, non-trivia child tokens of `node` in source order (does not descend
/// into child nodes such as balanced groups).
fn top_level_tokens<'a>(node: &'a Node, src: &'a str) -> Vec<Tok<'a>> {
    node.tokens()
        .filter(|t| t.kind != tk::NEWLINE)
        .map(|t| Tok {
            text: t.span.text(src),
            kind: t.kind,
            span_start: t.span.start,
        })
        .collect()
}

/// Drop a single leading keyword token (`import` / `from`) if present, returning
/// the remaining tokens — the import/from keyword is not part of the path.
fn strip_leading<'a, 'b>(toks: &'b [Tok<'a>], kw: &str) -> &'b [Tok<'a>] {
    match toks.split_first() {
        Some((first, rest)) if first.text == kw => rest,
        _ => toks,
    }
}

/// Split a token list on top-level commas.
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

/// Read a dotted path (`a . b . c`) and an optional `as` alias from one clause,
/// returning the path segments and the alias if present. Leading-dot relative
/// segments (empty names) are dropped from the segment list but still signal a
/// relative import to the caller via the original text.
fn dotted_path_and_alias(clause: &[Tok<'_>]) -> (Vec<String>, Option<String>) {
    let mut segs = Vec::new();
    let mut alias = None;
    let mut expect_alias = false;
    for t in clause {
        if t.kind != tk::NAME {
            continue; // dots and other punctuation
        }
        if expect_alias {
            alias = Some(t.text.to_string());
            expect_alias = false;
        } else if t.text == "as" {
            expect_alias = true;
        } else if t.text == "import" {
            break;
        } else {
            segs.push(t.text.to_string());
        }
    }
    (segs, alias)
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
            crate::core::cst::Child::Token(t) if t.trivia => {}
            crate::core::cst::Child::Token(t) => v.push(El::Tok {
                text: t.span.text(src),
                ident: t.kind == tk::NAME,
            }),
            crate::core::cst::Child::Node(n) => v.push(El::Grp(n)),
        }
    }
    v
}

/// Detect `name(...)` and `recv.name(...)` call sites over the real token tree,
/// recursing into nested groups but **not** into nested fn/struct/trait/class
/// definitions (those are scanned as their own functions). Keywords are excluded,
/// as is the name in a definition header.
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
                        });
                        i += 3;
                        continue;
                    }
                }
            }
            i += 1;
            continue;
        }
        // Bare call: name `(...)`, not preceded by `.` (attribute) or by a
        // definition keyword (a definition, not a call).
        if is_ident_el(&els[i]) {
            let prev = if i > 0 { tok_text(&els[i - 1]) } else { None };
            let text = tok_text(&els[i]).unwrap_or("");
            let is_def = matches!(
                prev,
                Some("fn") | Some("def") | Some("struct") | Some("trait") | Some("class")
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
    // Recurse into groups and into nested non-definition statement blocks; never
    // into nested Function/Struct/Trait/Class nodes (handled as their own pending
    // functions / types).
    for e in &els {
        if let Some(g) = grp(e) {
            if g.kind != cst::FUNCTION
                && g.kind != cst::STRUCT
                && g.kind != cst::TRAIT
                && g.kind != cst::CLASS
            {
                scan_calls(g, src, out);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::mojo::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("mod.mojo", src);
        let file = SourceFile {
            rel_path: "mod.mojo".to_string(),
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
        let g = graph_for("struct C:\n    fn m(self):\n        pass\n\nfn f():\n    pass\n");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "f + C.m");
        assert_eq!(g.count_nodes_of(ont::TYPE), 1, "struct C is a Type");
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "module mod");
        // C.m is a method of C.
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD));
    }

    #[test]
    fn fn_and_def_both_lower_to_function() {
        let g = graph_for("fn a():\n    pass\n\ndef b():\n    pass\n");
        let kinds: Vec<&str> = g
            .nodes()
            .filter(|n| n.kind == ont::FUNCTION)
            .filter_map(|n| n.props.get("def_kind"))
            .filter_map(|j| match j {
                Json::Str(s) => Some(s.as_str()),
                _ => None,
            })
            .collect();
        assert!(kinds.contains(&"fn"), "fn def_kind recorded");
        assert!(kinds.contains(&"def"), "def def_kind recorded");
    }

    #[test]
    fn struct_type_kind_is_struct() {
        let g = graph_for("struct C:\n    pass\n");
        let ty = g
            .nodes()
            .find(|n| n.kind == ont::TYPE)
            .expect("a Type node");
        assert_eq!(ty.props.get("type_kind"), Some(&Json::str("struct")));
        assert_eq!(ty.props.get("language"), Some(&Json::str("mojo")));
    }

    #[test]
    fn struct_conformance_emits_implements() {
        let g = graph_for(
            "trait Stringable:\n    fn s(self): ...\n\nstruct P(Stringable):\n    pass\n",
        );
        let imp = g
            .edges()
            .find(|e| e.kind == edge::IMPLEMENTS)
            .expect("an IMPLEMENTS edge");
        assert!(imp.from.starts_with("type::mod.P"));
        assert!(imp.to.starts_with("type::mod.Stringable"));
    }

    #[test]
    fn trait_inheritance_emits_extends() {
        let g = graph_for(
            "trait Base:\n    fn b(self): ...\n\ntrait Derived(Base):\n    fn d(self): ...\n",
        );
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an EXTENDS edge");
        assert!(ext.from.starts_with("type::mod.Derived"));
        assert!(ext.to.starts_with("type::mod.Base"));
    }

    #[test]
    fn resolves_unique_local_call() {
        let g = graph_for("fn add(a, b):\n    return a + b\n\nfn run():\n    add(1, 2)\n");
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
    fn self_method_resolves_via_receiver() {
        let g = graph_for(
            "struct P:\n    fn a(self):\n        self.b()\n    fn b(self):\n        pass\n",
        );
        let calls = call_edges(&g);
        let recv = calls
            .iter()
            .find(|e| e.props.get("resolution") == Some(&Json::str("receiver")));
        assert!(recv.is_some(), "self.b() should resolve via receiver scope");
        assert_eq!(recv.unwrap().props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for("fn run():\n    mystery()\n");
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
        let g = graph_for("import numpy\nfrom os import path\n");
        assert!(g.has_node("ext::numpy"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::numpy"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn alias_and_module_var_are_constants() {
        let g = graph_for("alias PI = 3.14\nvar count = 0\nstruct C:\n    var field: Int\n");
        // PI (alias) and count (module var) are Constants; C.field (struct field)
        // is not.
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 2);
        let names: Vec<&str> = g
            .nodes()
            .filter(|n| n.kind == ont::CONSTANT)
            .map(|n| n.name.as_str())
            .collect();
        assert!(names.contains(&"PI"));
        assert!(names.contains(&"count"));
    }

    #[test]
    fn decorator_recorded_as_property() {
        let g = graph_for("@value\nstruct C:\n    pass\n");
        let ty = g
            .nodes()
            .find(|n| n.kind == ont::TYPE && n.name == "C")
            .expect("the decorated struct");
        assert_eq!(
            ty.props.get("decorators"),
            Some(&Json::Array(vec![Json::str("value")]))
        );
    }

    #[test]
    fn type_use_in_signature() {
        let g = graph_for("struct Widget:\n    pass\n\nfn build(w: Widget):\n    pass\n");
        assert!(
            g.edges()
                .any(|e| e.kind == edge::USES_TYPE && e.to.contains("Widget")),
            "param annotation should create USES_TYPE"
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src = "import os\nstruct C(Base):\n    fn m(self):\n        helper()\n\nfn helper():\n    pass\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }

    #[test]
    fn lossless_round_trip_through_lowering_inputs() {
        // The lowering must never require lossy parsing: every fixture round-trips.
        for src in [
            "fn f[T](x: T) -> T:\n    return x\n",
            "@value\nstruct P(Stringable, Copyable):\n    var x: Int\n    fn __init__(inout self):\n        self.x = 0\n",
            "trait A(B, C):\n    fn m(self): ...\n",
            "alias N = 10\nfrom math import sqrt\n",
        ] {
            let tree = parse("rt.mojo", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
