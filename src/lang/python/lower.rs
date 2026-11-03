//! Lower the Python CST into the canonical graph.
//!
//! This mirrors the Rust lowering ([`crate::ir::lower`]) — same conservative
//! principles, same shared ontology — adapted to Python's surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to
//!    a concrete project definition only when a scope level yields exactly one
//!    candidate; several candidates are emitted as an ambiguous edge with the full
//!    `candidates` set; none resolves to an explicit external/unresolved node.
//! 2. **Everything comes from real tokens.** Calls, base classes, imports, and
//!    type uses are read off the lossless tree, never guessed.
//!
//! Resolution uses a deterministic **scope ladder** (most specific first; the
//! first level with any candidate decides), the Python analogue of the Rust
//! ladder: receiver (`self`/`cls`) → local module → file imports → global. Each
//! edge records which level resolved it, so the call graph stays auditable.
//!
//! Honest mappings (see the IR Atlas):
//!   `def` → `Function` (a method → `HAS_METHOD` from its enclosing `class`),
//!   `class` → `Type` (`type_kind: class`), module-level assignment → `Constant`,
//!   `class C(Base)` → `C EXTENDS Base`, `import`/`from … import` → `IMPORTS`
//!   (plus `ExternalDependency`/`DEPENDS_ON` for non-project roots). Class
//!   inheritance uses the substrate's [`edge::EXTENDS`]; decorators are recorded
//!   as a `decorators` property (no `DECORATES` edge constant exists yet, so we do
//!   not fabricate one — see `docs/ir-atlas.md` candidate extensions).

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::Node;
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::python::lexer::{is_keyword, kind as tk};
use crate::lang::python::parser::node as cst;

/// Lower a whole project's worth of Python files into a graph. `manifest_deps` is
/// unused for Python (the pipeline's manifest reader is Cargo-only); dependencies
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
        symbols_by_module: BTreeMap::new(),
        modules: BTreeSet::new(),
        constant_ids: BTreeSet::new(),
        from_imports: Vec::new(),
        imports: Vec::new(),
        cur_file: 0,
        cur_exports: None,
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("python"))],
    );

    // Pass B: create definition nodes + structural edges, build symbol tables and
    // per-file import maps. Inheritance is deferred to pass C so a base class
    // defined later in the project still resolves.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_extends: Vec<PendingExtends> = Vec::new();
    let mut pend_modules: Vec<PendingModule> = Vec::new();
    for (idx, f) in files.iter().enumerate() {
        lo.imports.push(BTreeMap::new());
        lo.cur_file = idx;
        let li = LineIndex::new(f.source);
        let module_join = mod_join(&f.module_path);
        lo.modules.insert(module_join.clone());
        let leaf = lo.ensure_modules(&f.module_path);
        lo.cur_exports = literal_all_exports(f.root, f.source);
        let file_id = format!("file::{}", f.rel_path);
        let mut file_props = vec![
            ("path", Json::str(f.rel_path.clone())),
            ("language", Json::str("python")),
            ("extension", Json::str(extension(&f.rel_path))),
            ("bytes", Json::U64(f.source.len() as u64)),
            ("lines", Json::U64(line_count(f.source) as u64)),
        ];
        if f.source.as_bytes().starts_with(b"#!") {
            file_props.push(("shebang", Json::Bool(true)));
        }
        if has_main_guard(f.root, f.source) {
            file_props.push(("main_guard", Json::Bool(true)));
        }
        lo.g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            file_props,
        );
        lo.g.add_edge(leaf.clone(), edge::CONTAINS, file_id.clone(), vec![]);
        pend_modules.push(PendingModule {
            id: leaf,
            source: f.source,
            root: f.root,
            module_join: module_join.clone(),
            file_idx: idx,
        });
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
            &mut pend_extends,
        );
    }
    for candidates in lo.symbols_by_module.values_mut() {
        candidates.sort_unstable();
        candidates.dedup();
    }

    let from_imports = std::mem::take(&mut lo.from_imports);
    for import in &from_imports {
        lo.emit_from_import_symbol_edge(import);
    }

    // Pass C: resolve calls (scope ladder), type usages, and inheritance against
    // the now-complete symbol tables.
    for pm in &pend_modules {
        let ctx = Ctx {
            module_join: pm.module_join.clone(),
            owner_type: None,
            imports: lo.imports.get(pm.file_idx).cloned().unwrap_or_default(),
        };
        let mut calls = Vec::new();
        scan_calls(pm.root, pm.source, &mut calls);
        for call in &calls {
            let res = lo.resolve(call, &ctx);
            lo.emit_call(&pm.id, call, res);
        }
    }
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
            lo.emit_constant_reads(pf, block);
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
    /// Simple name → method node ids only (global method-call level).
    method_by_name: BTreeMap<String, Vec<String>>,
    /// (module_join, name) → function ids (local-module level).
    fn_by_module: BTreeMap<(String, String), Vec<String>>,
    /// (class_name, method_name) → method ids (receiver level).
    method_by_type: BTreeMap<(String, String), Vec<String>>,
    /// Simple name → type (class) node ids.
    type_by_name: BTreeMap<String, Vec<String>>,
    /// (module_join, name) → module-level symbol ids.
    symbols_by_module: BTreeMap<(String, String), Vec<String>>,
    /// Every analyzed module join, including modules with no importable symbols.
    modules: BTreeSet<String>,
    /// Constant node ids for O(log n) kind checks during READS emission.
    constant_ids: BTreeSet<String>,
    /// Deferred symbol-grain from-imports, resolved after every definition exists.
    from_imports: Vec<PendingFromImport>,
    /// Per-file import maps: imported leaf name → full dotted path segments.
    imports: Vec<BTreeMap<String, Vec<String>>>,
    /// Literal `__all__` for the file currently lowered; `None` uses the public-name rule.
    cur_exports: Option<BTreeSet<String>>,
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

struct PendingModule<'a> {
    id: String,
    source: &'a str,
    root: &'a Node,
    module_join: String,
    file_idx: usize,
}

/// A deferred `class C(Base, ...)` inheritance link, resolved in pass C.
struct PendingExtends {
    type_id: String,
    base_name: String,
}

struct PendingFromImport {
    file_id: String,
    module_join: String,
    name: String,
}

/// The enclosing class while walking, for methods (`HAS_METHOD`, receiver scope).
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
    /// Immediate receiver identifier for method calls (`self`, `cls`, a variable).
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
    /// module id (or the package id for a root file with no module segments, e.g.
    /// a top-level `__init__.py`).
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
                vec![("language", Json::str("python"))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    /// Walk a statement container (a `Module` or `Block`), creating definition
    /// nodes and recursing into nested scopes. `owner` is the nearest enclosing
    /// class (cleared when descending into a function); `in_function` gates
    /// module-level `Constant` emission.
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
        pend_extends: &mut Vec<PendingExtends>,
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
                    pend_extends,
                ),
                cst::CLASS => self.handle_class(
                    item,
                    file_id,
                    module_join,
                    scope,
                    src,
                    li,
                    pend_fns,
                    pend_extends,
                ),
                cst::COMPOUND => {
                    // A compound statement (if/for/with/try/…) is not a new scope in
                    // Python: definitions inside it still belong to the enclosing
                    // class/module, so recurse with the same owner.
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
                            pend_extends,
                        );
                    }
                }
                cst::IMPORT => self.handle_import(item, file_id, src),
                cst::FROM_IMPORT => self.handle_from_import(item, file_id, src),
                cst::SIMPLE_STMT => {
                    // Module-level bindings become Constants; bindings inside a
                    // function (locals) or class body (attributes) are not.
                    if !in_function && owner.is_none() {
                        self.handle_assignment(item, file_id, module_join, src, li);
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
        pend_extends: &mut Vec<PendingExtends>,
    ) {
        let name = name_text(item, src).unwrap_or("<anonymous>").to_string();
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(module_join, scope, &name);
        let id = format!("fn::{qual}#{line}");
        let block = item.child(cst::BLOCK);
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("python")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            ("has_body", Json::Bool(block.is_some())),
        ];
        if self.is_exported(&name, scope.is_empty() && owner.is_none()) {
            props.push(("exported", Json::Bool(true)));
        }
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
        if scope.is_empty() && owner.is_none() {
            self.symbols_by_module
                .entry((module_join.to_string(), name.clone()))
                .or_default()
                .push(id.clone());
        }

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

        // Nested defs/classes are not methods of the enclosing class: descend with
        // a fresh (None) owner and an extended scope path.
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
                pend_extends,
            );
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_class<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_extends: &mut Vec<PendingExtends>,
    ) {
        let name = name_text(item, src).unwrap_or("<anonymous>").to_string();
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(module_join, scope, &name);
        // Include the line so a class redefined under the same qualified name (e.g.
        // a local fixture class defined twice in one test method) stays a distinct
        // node instead of colliding on upsert. Mirrors how Function ids carry #line.
        let id = format!("type::{qual}#{line}");
        let mut props = vec![
            ("type_kind", Json::str("class")),
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("python")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
        ];
        if self.is_exported(&name, scope.is_empty()) {
            props.push(("exported", Json::Bool(true)));
        }
        if let Some(d) = decorators(item, src) {
            props.push(("decorators", d));
        }
        self.g
            .upsert_node(id.clone(), ont::TYPE, name.clone(), props);
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        if scope.is_empty() {
            self.symbols_by_module
                .entry((module_join.to_string(), name.clone()))
                .or_default()
                .push(id.clone());
        }
        self.type_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());

        // Base classes (defer the EXTENDS resolution to pass C).
        for base in class_bases(item, src) {
            pend_extends.push(PendingExtends {
                type_id: id.clone(),
                base_name: base,
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
                pend_extends,
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
        let internal_module = if path_text.starts_with('.') {
            None
        } else {
            module_segs
                .first()
                .is_some_and(|root| self.local_roots.contains(root))
                .then(|| module_segs.join("."))
        };

        for clause in split_commas(names_part.to_vec()) {
            let (segs, alias) = dotted_path_and_alias(&clause);
            if segs.is_empty() {
                continue; // e.g. a `*` glob — no nameable leaf
            }
            let imported_name = segs.last().cloned().unwrap();
            let leaf = alias.unwrap_or_else(|| imported_name.clone());
            // Full path to the imported symbol: module + name (mirrors the Rust
            // import map shape so the resolver can find the defining module).
            let mut full = module_segs.clone();
            full.extend(segs);
            self.imports[self.cur_file].insert(leaf, full);
            if let Some(module_join) = &internal_module {
                self.from_imports.push(PendingFromImport {
                    file_id: file_id.to_string(),
                    module_join: module_join.clone(),
                    name: imported_name,
                });
            }
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
                    vec![("language", Json::str("python"))],
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

    fn emit_from_import_symbol_edge(&mut self, import: &PendingFromImport) {
        let key = (import.module_join.clone(), import.name.clone());
        let mut candidates: Vec<&str> = if let Some(exact) = self.symbols_by_module.get(&key) {
            exact.iter().map(String::as_str).collect()
        } else if self.modules.contains(&import.module_join) {
            Vec::new()
        } else {
            // A directory above a Python import root may be part of the analyzed
            // tree (for example a cohort containing `repo/integrations.py`) while
            // the runtime import remains `integrations`. Fall back to a suffix
            // match only when there is no exact module, and preserve ambiguity.
            let suffix = format!(".{}", import.module_join);
            self.symbols_by_module
                .iter()
                .filter(|((module, name), _)| name == &import.name && module.ends_with(&suffix))
                .flat_map(|(_, ids)| ids.iter().map(String::as_str))
                .collect()
        };
        candidates.sort_unstable();
        candidates.dedup();
        let [candidate] = candidates.as_slice() else {
            return;
        };
        let candidate = (*candidate).to_string();
        self.g.add_edge(
            import.file_id.clone(),
            edge::IMPORTS,
            candidate,
            vec![
                (
                    "path",
                    Json::str(format!("{}.{}", import.module_join, import.name)),
                ),
                ("external", Json::Bool(false)),
                ("symbol", Json::Bool(true)),
            ],
        );
    }

    /// Module-level `NAME = …` / `NAME: T = …` / `NAME: T` → a `Constant`. Only
    /// plain single-target bindings are recognized (no augmented assignment, no
    /// tuple unpacking) — conservative, never guessed.
    fn handle_assignment(
        &mut self,
        item: &Node,
        file_id: &str,
        module_join: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let toks = top_level_tokens(item, src);
        let mut sig = toks.iter().filter(|t| t.kind != tk::NEWLINE);
        let first = match sig.next() {
            Some(t) if t.kind == tk::NAME && !is_keyword(t.text) => t,
            _ => return,
        };
        let binder = match sig.next() {
            Some(t) if t.text == "=" || t.text == ":" => t.text,
            _ => return,
        };
        let name = first.text.to_string();
        let line = li.line_col(first.span_start).line;
        let id = format!("const::{}", qual_name(module_join, &[], &name));
        let mut props = vec![
            ("binding", Json::str("module_var")),
            ("annotated", Json::Bool(binder == ":")),
            ("language", Json::str("python")),
            ("line", Json::U64(line as u64)),
        ];
        if self.is_exported(&name, true) {
            props.push(("exported", Json::Bool(true)));
        }
        self.g
            .upsert_node(id.clone(), ont::CONSTANT, name.clone(), props);
        self.constant_ids.insert(id.clone());
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.symbols_by_module
            .entry((module_join.to_string(), name))
            .or_default()
            .push(id);
    }

    fn emit_constant_reads(&mut self, function: &PendingFn<'_>, block: &Node) {
        let mut parameters = BTreeSet::new();
        if let Some(signature) = function.signature {
            collect_parameter_names(signature, function.source, &mut parameters);
        }
        let facts = function_body_facts(block, function.source);
        for name in facts.reads {
            if parameters.contains(&name) || facts.assigned.contains(&name) {
                continue;
            }
            let key = (function.module_join.clone(), name);
            let Some(candidates) = self.symbols_by_module.get(&key) else {
                continue;
            };
            let [candidate] = candidates.as_slice() else {
                continue;
            };
            let target = candidate.clone();
            if !self.constant_ids.contains(&target) {
                continue;
            }
            self.g
                .add_edge(function.id.clone(), edge::READS, target, vec![]);
        }
    }

    fn is_exported(&self, name: &str, module_level: bool) -> bool {
        module_level
            && self
                .cur_exports
                .as_ref()
                .map_or_else(|| !name.starts_with('_'), |names| names.contains(name))
    }

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        if call.method {
            // Receiver scope: `self.m()` / `cls.m()` → enclosing class's methods.
            if matches!(call.receiver.as_deref(), Some("self") | Some("cls")) {
                if let Some(owner) = &ctx.owner_type {
                    let c = self.methods_of(owner, &call.name);
                    if !c.is_empty() {
                        return mk(c, "receiver");
                    }
                }
            }
            // Unknown receiver type (no inference). The honest candidate set is
            // every same-name method PLUS every same-name free function — a Python
            // member call can reach module-level functions (`mod.f()`) and
            // functions bound as attributes.
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

    /// Resolve a deferred `class C(Base)` link into a concrete `EXTENDS` edge,
    /// pointing at the project type when unique, otherwise an explicit
    /// `UnresolvedSymbol` (a stdlib/third-party base we cannot see in an airgap).
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
                            ("role", Json::str("base_class")),
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

/// A literal module-level `__all__` is authoritative. Any computed assignment or
/// mutation makes the value unknowable without evaluation, so the caller falls
/// back to Python's public-name convention.
fn literal_all_exports(root: &Node, src: &str) -> Option<BTreeSet<String>> {
    let mut found = None;
    for item in root.child_nodes().filter(|n| n.kind == cst::SIMPLE_STMT) {
        let els = significant_children(item, src);
        if els.first().and_then(tok_text) != Some("__all__") {
            continue;
        }
        let eq_idx = els.iter().position(|el| tok_text(el) == Some("="))?;
        let plain_assignment = eq_idx == 1;
        let annotated_assignment = eq_idx >= 3 && els.get(1).and_then(tok_text) == Some(":");
        if !plain_assignment && !annotated_assignment {
            return None;
        }
        let group = match els.get(eq_idx + 1).and_then(grp) {
            Some(group) if matches!(group.kind, cst::BRACKET | cst::PAREN) => group,
            _ => return None,
        };
        if els[eq_idx + 2..]
            .iter()
            .filter_map(tok_text)
            .any(|text| text != "\n")
        {
            return None;
        }
        found = Some(literal_string_group(group, src)?);
    }
    found
}

fn literal_string_group(group: &Node, src: &str) -> Option<BTreeSet<String>> {
    let toks = top_level_tokens(group, src);
    let (open, close) = match group.kind {
        cst::BRACKET => ("[", "]"),
        cst::PAREN => ("(", ")"),
        _ => return None,
    };
    if toks.first().map(|t| t.text) != Some(open) || toks.last().map(|t| t.text) != Some(close) {
        return None;
    }
    let values: Vec<Tok<'_>> = toks[1..toks.len() - 1]
        .iter()
        .copied()
        .filter(|t| t.kind != tk::NEWLINE)
        .collect();
    if values.is_empty() {
        return Some(BTreeSet::new());
    }
    if group.kind == cst::PAREN && !toks.iter().any(|tok| tok.text == ",") {
        return None;
    }
    let mut names = BTreeSet::new();
    for clause in split_commas(values) {
        if clause.is_empty() {
            continue;
        }
        if clause.len() != 1 || clause[0].kind != tk::STRING {
            return None;
        }
        names.insert(simple_string_contents(clause[0].text)?.to_string());
    }
    Some(names)
}

/// Borrow the contents of a plain single- or double-quoted literal. Prefixed,
/// escaped, and triple-quoted forms are deliberately rejected rather than
/// interpreted incompletely.
fn simple_string_contents(text: &str) -> Option<&str> {
    let bytes = text.as_bytes();
    if bytes.len() < 2 || text.contains('\\') {
        return None;
    }
    let quote = bytes[0];
    if !matches!(quote, b'\'' | b'"') || bytes[bytes.len() - 1] != quote {
        return None;
    }
    if bytes.len() >= 6 && bytes[..3] == [quote; 3] {
        return None;
    }
    Some(&text[1..text.len() - 1])
}

fn has_main_guard(root: &Node, src: &str) -> bool {
    root.child_nodes().any(|item| {
        item.kind == cst::COMPOUND
            && significant_children(item, src).first().and_then(tok_text) == Some("if")
            && item.child(cst::HEADER).is_some_and(|header| {
                let els = significant_children(header, src);
                matches_main_guard(&els)
            })
    })
}

fn matches_main_guard(els: &[El<'_>]) -> bool {
    if els.len() != 3 || els.get(1).and_then(tok_text) != Some("==") {
        return false;
    }
    let left = els.first().and_then(tok_text);
    let right = els.get(2).and_then(tok_text);
    (left == Some("__name__") && right.and_then(simple_string_contents) == Some("__main__"))
        || (right == Some("__name__") && left.and_then(simple_string_contents) == Some("__main__"))
}

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

/// True if a `def` carries an `async` modifier before the `def` keyword.
fn is_async(item: &Node, src: &str) -> bool {
    for t in item.tokens() {
        match t.span.text(src) {
            "async" => return true,
            "def" => return false,
            _ => {}
        }
    }
    false
}

/// Decorator names attached to a def/class, as a JSON array property (the last
/// top-level identifier of each `@expr`, e.g. `route` from `@app.route(...)`),
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

/// Base-class simple names from a `class C(A, b.B)` header. Only the final
/// identifier of each comma-separated base is taken (`B` from `b.B`); keyword
/// arguments such as `metaclass=...` are skipped.
fn class_bases(item: &Node, src: &str) -> Vec<String> {
    let header = match item.child(cst::HEADER) {
        Some(h) => h,
        None => return Vec::new(),
    };
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

#[derive(Default)]
struct FunctionBodyFacts {
    reads: BTreeSet<String>,
    assigned: BTreeSet<String>,
}

fn collect_names(node: &Node, src: &str, names: &mut BTreeSet<String>) {
    for child in &node.children {
        match child {
            crate::core::cst::Child::Token(token) if token.kind == tk::NAME => {
                let text = token.span.text(src);
                if !is_keyword(text) {
                    names.insert(text.to_string());
                }
            }
            crate::core::cst::Child::Node(child) => collect_names(child, src, names),
            crate::core::cst::Child::Token(_) => {}
        }
    }
}

fn collect_parameter_names(node: &Node, src: &str, names: &mut BTreeSet<String>) {
    let Some(parameters) = node.child(cst::PAREN) else {
        return;
    };
    collect_parameter_names_from_tokens(&top_level_tokens(parameters, src), names);
}

fn collect_parameter_names_from_tokens(tokens: &[Tok<'_>], names: &mut BTreeSet<String>) {
    for clause in split_commas(tokens.to_vec()) {
        let boundary = clause
            .iter()
            .position(|token| matches!(token.text, ":" | "="))
            .unwrap_or(clause.len());
        if let Some(parameter) = clause[..boundary]
            .iter()
            .find(|token| token.kind == tk::NAME && !is_keyword(token.text))
        {
            names.insert(parameter.text.to_string());
        }
    }
}

fn function_body_facts(block: &Node, src: &str) -> FunctionBodyFacts {
    let mut facts = FunctionBodyFacts::default();
    scan_function_body(block, src, &mut facts);
    facts
}

fn scan_function_body(node: &Node, src: &str, facts: &mut FunctionBodyFacts) {
    for child in node.child_nodes() {
        if matches!(child.kind, cst::FUNCTION | cst::CLASS) {
            continue;
        }
        match child.kind {
            cst::IMPORT | cst::FROM_IMPORT => {
                collect_names(child, src, &mut facts.assigned);
            }
            cst::SIMPLE_STMT => scan_simple_statement(child, src, facts),
            cst::COMPOUND => {
                if let Some(header) = child.child(cst::HEADER) {
                    let binds_for = top_level_tokens(child, src)
                        .iter()
                        .any(|token| token.text == "for");
                    scan_compound_header(header, src, facts, binds_for);
                }
                scan_function_body(child, src, facts);
            }
            _ => scan_function_body(child, src, facts),
        }
    }
}

fn scan_simple_statement(node: &Node, src: &str, facts: &mut FunctionBodyFacts) {
    let mut tokens = Vec::new();
    collect_tokens(node, src, &mut tokens);
    let first = tokens.first().map(|token| token.text);
    if matches!(first, Some("global") | Some("nonlocal")) {
        return;
    }
    let statement_tokens = top_level_tokens(node, src);
    if let Some(assign_at) = statement_tokens
        .iter()
        .position(|token| is_assignment(token.text))
    {
        mark_assigned(&statement_tokens[..assign_at], &mut facts.assigned);
    }
    scan_generator_bindings(&tokens, facts);
    collect_reads(&tokens, &mut facts.reads);
}

fn scan_compound_header(node: &Node, src: &str, facts: &mut FunctionBodyFacts, binds_for: bool) {
    let mut tokens = Vec::new();
    collect_tokens(node, src, &mut tokens);
    if binds_for {
        if let Some(in_at) = tokens.iter().position(|token| token.text == "in") {
            mark_assigned(&tokens[..in_at], &mut facts.assigned);
        }
    }
    scan_generator_bindings(&tokens, facts);
    for window in tokens.windows(2) {
        if window[0].text == "as" && window[1].kind == tk::NAME {
            facts.assigned.insert(window[1].text.to_string());
        }
    }
    collect_reads(&tokens, &mut facts.reads);
}

fn scan_generator_bindings(tokens: &[Tok<'_>], facts: &mut FunctionBodyFacts) {
    for (for_at, token) in tokens.iter().enumerate() {
        if token.text != "for" {
            continue;
        }
        let Some(relative_in) = tokens[for_at + 1..]
            .iter()
            .position(|candidate| candidate.text == "in")
        else {
            continue;
        };
        let in_at = for_at + 1 + relative_in;
        mark_assigned(&tokens[for_at + 1..in_at], &mut facts.assigned);
    }
}

fn mark_assigned(tokens: &[Tok<'_>], assigned: &mut BTreeSet<String>) {
    for token in tokens {
        if token.kind == tk::NAME && !is_keyword(token.text) {
            assigned.insert(token.text.to_string());
        }
    }
}

fn collect_tokens<'a>(node: &'a Node, src: &'a str, out: &mut Vec<Tok<'a>>) {
    for child in &node.children {
        match child {
            crate::core::cst::Child::Token(token) if !token.trivia => out.push(Tok {
                text: token.span.text(src),
                kind: token.kind,
                span_start: token.span.start,
            }),
            crate::core::cst::Child::Node(child)
                if !matches!(child.kind, cst::FUNCTION | cst::CLASS) =>
            {
                collect_tokens(child, src, out);
            }
            _ => {}
        }
    }
}

fn collect_reads(tokens: &[Tok<'_>], reads: &mut BTreeSet<String>) {
    let mut lambda_parameters = BTreeSet::new();
    for (lambda_at, token) in tokens.iter().enumerate() {
        if token.text != "lambda" {
            continue;
        }
        let Some(colon_at) = tokens[lambda_at + 1..]
            .iter()
            .position(|candidate| candidate.text == ":")
            .map(|offset| lambda_at + 1 + offset)
        else {
            continue;
        };
        collect_parameter_names_from_tokens(
            &tokens[lambda_at + 1..colon_at],
            &mut lambda_parameters,
        );
    }
    for (index, token) in tokens.iter().enumerate() {
        if token.kind == tk::NAME
            && !is_keyword(token.text)
            && !lambda_parameters.contains(token.text)
            && index
                .checked_sub(1)
                .is_none_or(|prev| tokens[prev].text != ".")
        {
            reads.insert(token.text.to_string());
        }
    }
}

fn is_assignment(text: &str) -> bool {
    matches!(
        text,
        "=" | ":="
            | "+="
            | "-="
            | "*="
            | "/="
            | "//="
            | "%="
            | "**="
            | "@="
            | "&="
            | "|="
            | "^="
            | ">>="
            | "<<="
    )
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
/// recursing into nested groups but **not** into nested `def`/`class` definitions
/// (those are scanned as their own functions). Keywords are excluded, as is the
/// name in a `def`/`class` header.
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
        // `def`/`class` keyword (a definition, not a call).
        if is_ident_el(&els[i]) {
            let prev = if i > 0 { tok_text(&els[i - 1]) } else { None };
            let text = tok_text(&els[i]).unwrap_or("");
            let is_def = matches!(prev, Some("def") | Some("class"));
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
    // into nested Function/Class nodes (handled as their own pending functions).
    for e in &els {
        if let Some(g) = grp(e) {
            if g.kind != cst::FUNCTION && g.kind != cst::CLASS {
                scan_calls(g, src, out);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::python::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("mod.py", src);
        let file = SourceFile {
            rel_path: "mod.py".to_string(),
            module_path: vec!["mod".to_string()],
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    fn graph_for_import_pair(import_src: &str, provider_src: &str) -> Graph {
        let importer = parse("consumer.py", import_src);
        let provider = parse("integrations.py", provider_src);
        let files = [
            SourceFile {
                rel_path: "consumer.py".to_string(),
                module_path: vec!["consumer".to_string()],
                source: &importer.source,
                root: &importer.root,
            },
            SourceFile {
                rel_path: "integrations.py".to_string(),
                module_path: vec!["integrations".to_string()],
                source: &provider.source,
                root: &provider.root,
            },
        ];
        lower("demo", &files, &[])
    }

    fn graph_for_nested_import_pair(import_src: &str, provider_src: &str) -> Graph {
        let importer = parse("act1-quadron/import_parsers.py", import_src);
        let provider = parse("act1-quadron/integrations.py", provider_src);
        let files = [
            SourceFile {
                rel_path: "act1-quadron/import_parsers.py".to_string(),
                module_path: vec!["act1-quadron".to_string(), "import_parsers".to_string()],
                source: &importer.source,
                root: &importer.root,
            },
            SourceFile {
                rel_path: "act1-quadron/integrations.py".to_string(),
                module_path: vec!["act1-quadron".to_string(), "integrations".to_string()],
                source: &provider.source,
                root: &provider.root,
            },
        ];
        lower("demo", &files, &[])
    }

    fn graph_for_relative_import() -> Graph {
        let consumer = parse("pkg/consumer.py", "from .integrations import X\n");
        let top_level = parse("integrations.py", "X = 1\n");
        let package = parse("pkg/integrations.py", "Y = 2\n");
        let files = [
            SourceFile {
                rel_path: "pkg/consumer.py".to_string(),
                module_path: vec!["pkg".to_string(), "consumer".to_string()],
                source: &consumer.source,
                root: &consumer.root,
            },
            SourceFile {
                rel_path: "integrations.py".to_string(),
                module_path: vec!["integrations".to_string()],
                source: &top_level.source,
                root: &top_level.root,
            },
            SourceFile {
                rel_path: "pkg/integrations.py".to_string(),
                module_path: vec!["pkg".to_string(), "integrations".to_string()],
                source: &package.source,
                root: &package.root,
            },
        ];
        lower("demo", &files, &[])
    }

    fn call_edges(g: &Graph) -> Vec<&crate::graph::GraphEdge> {
        g.edges().filter(|e| e.kind == edge::CALLS).collect()
    }

    #[test]
    fn module_level_public_symbols_are_exported_by_default() {
        let g = graph_for(
            "def foo():\n    def inner():\n        pass\n\ndef _bar():\n    pass\n\nclass Widget:\n    def method(self):\n        pass\n\nclass _Hidden:\n    pass\n\nVALUE = 1\n_PRIVATE = 2\n",
        );
        for name in ["foo", "Widget", "VALUE"] {
            let node = g
                .nodes()
                .find(|n| n.name == name)
                .unwrap_or_else(|| panic!("missing {name}"));
            assert_eq!(
                node.props.get("exported"),
                Some(&Json::Bool(true)),
                "{name}"
            );
        }
        for name in ["_bar", "_Hidden", "_PRIVATE", "inner", "method"] {
            let node = g
                .nodes()
                .find(|n| n.name == name)
                .unwrap_or_else(|| panic!("missing {name}"));
            assert_eq!(node.props.get("exported"), None, "{name}");
        }
    }

    #[test]
    fn literal_all_is_authoritative_for_exports() {
        let g = graph_for(
            "__all__ = (\"_bar\", '_Type', \"_VALUE\")\n\ndef foo():\n    pass\n\ndef _bar():\n    pass\n\nclass Public:\n    pass\n\nclass _Type:\n    pass\n\nPUBLIC = 1\n_VALUE = 2\n",
        );
        for name in ["_bar", "_Type", "_VALUE"] {
            let node = g
                .nodes()
                .find(|n| n.name == name)
                .unwrap_or_else(|| panic!("missing {name}"));
            assert_eq!(
                node.props.get("exported"),
                Some(&Json::Bool(true)),
                "{name}"
            );
        }
        for name in ["foo", "Public", "PUBLIC"] {
            let node = g
                .nodes()
                .find(|n| n.name == name)
                .unwrap_or_else(|| panic!("missing {name}"));
            assert_eq!(node.props.get("exported"), None, "{name}");
        }
    }

    #[test]
    fn parenthesized_string_all_falls_back_to_public_name_rule() {
        let g = graph_for(
            "__all__ = (\"solo\")\n\ndef solo():\n    pass\n\ndef other():\n    pass\n\ndef _hidden():\n    pass\n",
        );
        for name in ["solo", "other"] {
            let node = g
                .nodes()
                .find(|n| n.name == name)
                .unwrap_or_else(|| panic!("missing {name}"));
            assert_eq!(node.props.get("exported"), Some(&Json::Bool(true)));
        }
        let hidden = g.nodes().find(|n| n.name == "_hidden").unwrap();
        assert_eq!(hidden.props.get("exported"), None);
    }

    #[test]
    fn annotated_literal_all_is_authoritative() {
        let g = graph_for(
            "__all__: list = [\"listed\"]\n\ndef listed():\n    pass\n\ndef other():\n    pass\n",
        );
        let listed = g.nodes().find(|n| n.name == "listed").unwrap();
        let other = g.nodes().find(|n| n.name == "other").unwrap();
        assert_eq!(listed.props.get("exported"), Some(&Json::Bool(true)));
        assert_eq!(other.props.get("exported"), None);
    }

    #[test]
    fn empty_tuple_all_is_authoritative() {
        let g = graph_for("__all__ = ()\n\ndef public():\n    pass\n");
        let public = g.nodes().find(|n| n.name == "public").unwrap();
        assert_eq!(public.props.get("exported"), None);
    }

    #[test]
    fn singleton_tuple_all_is_authoritative() {
        let g = graph_for(
            "__all__ = (\"listed\",)\n\ndef listed():\n    pass\n\ndef other():\n    pass\n",
        );
        let listed = g.nodes().find(|n| n.name == "listed").unwrap();
        let other = g.nodes().find(|n| n.name == "other").unwrap();
        assert_eq!(listed.props.get("exported"), Some(&Json::Bool(true)));
        assert_eq!(other.props.get("exported"), None);
    }

    #[test]
    fn computed_all_falls_back_to_public_name_rule() {
        let g = graph_for(
            "exports = [\"_bar\"]\n__all__ = exports\n\ndef foo():\n    pass\n\ndef _bar():\n    pass\n",
        );
        let foo = g
            .nodes()
            .find(|n| n.name == "foo")
            .expect("the public function");
        let bar = g
            .nodes()
            .find(|n| n.name == "_bar")
            .expect("the private function");
        assert_eq!(foo.props.get("exported"), Some(&Json::Bool(true)));
        assert_eq!(bar.props.get("exported"), None);
    }

    #[test]
    fn detects_top_level_main_guard_in_both_orders_and_quote_styles() {
        for src in [
            "if __name__ == \"__main__\":\n    main()\n",
            "if __name__ == '__main__':\n    main()\n",
            "if \"__main__\" == __name__:\n    main()\n",
        ] {
            let g = graph_for(src);
            let file = g
                .nodes()
                .find(|n| n.kind == ont::FILE)
                .expect("the File node");
            assert_eq!(file.props.get("main_guard"), Some(&Json::Bool(true)));
        }
    }

    #[test]
    fn nested_main_guard_is_not_a_file_fact() {
        let g = graph_for("def run():\n    if __name__ == \"__main__\":\n        main()\n");
        let file = g
            .nodes()
            .find(|n| n.kind == ont::FILE)
            .expect("the File node");
        assert_eq!(file.props.get("main_guard"), None);
    }

    #[test]
    fn shebang_is_a_file_fact() {
        let g = graph_for("#!/usr/bin/env python3\nVALUE = 1\n");
        let file = g
            .nodes()
            .find(|n| n.kind == ont::FILE)
            .expect("the File node");
        assert_eq!(file.props.get("shebang"), Some(&Json::Bool(true)));
    }

    #[test]
    fn module_level_call_resolves_from_module_node() {
        let g = graph_for("def main():\n    pass\n\nif __name__ == \"__main__\":\n    main()\n");
        let call = call_edges(&g)
            .into_iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("main")))
            .expect("the module-level call");
        assert_eq!(call.from, "mod::mod");
        assert!(call.to.starts_with("fn::mod.main"));
        assert_eq!(call.props.get("resolution"), Some(&Json::str("local")));
        assert_eq!(call.props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn unresolved_module_level_call_still_emits_an_edge() {
        let g = graph_for("mystery()\n");
        let calls = call_edges(&g);
        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].from, "mod::mod");
        assert_eq!(calls[0].to, "unresolved::mystery");
        assert_eq!(
            calls[0].props.get("resolution"),
            Some(&Json::str("external"))
        );
        assert_eq!(calls[0].props.get("resolved"), Some(&Json::Bool(false)));
    }

    #[test]
    fn liveness_facts_are_deterministic() {
        let src = "#!/usr/bin/env python3\n__all__ = (\"_main\",)\n\ndef _main():\n    pass\n\nif __name__ == '__main__':\n    _main()\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a.as_bytes(), b.as_bytes());
    }

    #[test]
    fn emits_function_type_module_nodes() {
        let g = graph_for("class C:\n    def m(self):\n        pass\n\ndef f():\n    pass\n");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "f + C.m");
        assert_eq!(g.count_nodes_of(ont::TYPE), 1, "class C is a Type");
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "module mod");
        // C.m is a method of C.
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD));
    }

    #[test]
    fn class_type_kind_is_class() {
        let g = graph_for("class C:\n    pass\n");
        let ty = g
            .nodes()
            .find(|n| n.kind == ont::TYPE)
            .expect("a Type node");
        assert_eq!(ty.props.get("type_kind"), Some(&Json::str("class")));
        assert_eq!(ty.props.get("language"), Some(&Json::str("python")));
    }

    #[test]
    fn resolves_unique_local_call() {
        let g = graph_for("def add(a, b):\n    return a + b\n\ndef run():\n    add(1, 2)\n");
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
            "class P:\n    def a(self):\n        self.b()\n    def b(self):\n        pass\n",
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
        let g = graph_for("def run():\n    mystery()\n");
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
    fn aliased_from_import_emits_symbol_grain_edge() {
        let g = graph_for_import_pair(
            "def load():\n    from integrations import INTEGRATION_PARSERS as _INT_PARSERS\n",
            "INTEGRATION_PARSERS = {}\n",
        );
        let target = g
            .nodes()
            .find(|n| n.kind == ont::CONSTANT && n.name == "INTEGRATION_PARSERS")
            .expect("provider constant");
        let import = g
            .edges()
            .find(|e| e.kind == edge::IMPORTS && e.from == "file::consumer.py" && e.to == target.id)
            .expect("symbol-grain import");
        assert_eq!(import.props.get("symbol"), Some(&Json::Bool(true)));
        assert!(g.edges().any(|e| {
            e.kind == edge::IMPORTS && e.from == "file::consumer.py" && e.to == "mod::integrations"
        }));
    }

    fn symbol_import_count(g: &Graph, name: &str) -> usize {
        let target = g
            .nodes()
            .find(|node| node.kind == ont::CONSTANT && node.name == name)
            .expect("provider constant");
        g.edges()
            .filter(|edge| {
                edge.kind == super::edge::IMPORTS
                    && edge.to == target.id
                    && edge.props.get("symbol") == Some(&Json::Bool(true))
            })
            .count()
    }

    #[test]
    fn module_level_aliased_from_import_emits_one_symbol_edge() {
        let g = graph_for_nested_import_pair(
            "from integrations import INTEGRATION_PARSERS as _INT_PARSERS\n",
            "INTEGRATION_PARSERS = {}\n",
        );
        assert_eq!(symbol_import_count(&g, "INTEGRATION_PARSERS"), 1);
    }

    #[test]
    fn try_wrapped_from_import_emits_one_symbol_edge() {
        let g = graph_for_nested_import_pair(
            "try:\n    from integrations import INTEGRATION_PARSERS\nexcept ImportError:\n    pass\n",
            "INTEGRATION_PARSERS = {}\n",
        );
        assert_eq!(symbol_import_count(&g, "INTEGRATION_PARSERS"), 1);
    }

    #[test]
    fn aliased_try_wrapped_from_import_emits_one_symbol_edge() {
        let g = graph_for_nested_import_pair(
            "try:\n    from integrations import INTEGRATION_PARSERS as _INT_PARSERS\nexcept ImportError:\n    pass\n",
            "INTEGRATION_PARSERS = {}\n",
        );
        assert_eq!(symbol_import_count(&g, "INTEGRATION_PARSERS"), 1);
    }

    #[test]
    fn ambiguous_suffix_matched_from_import_emits_no_symbol_edge() {
        let importer = parse(
            "act1-quadron/import_parsers.py",
            "from integrations import INTEGRATION_PARSERS\n",
        );
        let first = parse("act1-quadron/integrations.py", "INTEGRATION_PARSERS = {}\n");
        let second = parse(
            "other-project/integrations.py",
            "INTEGRATION_PARSERS = {}\n",
        );
        let files = [
            SourceFile {
                rel_path: "act1-quadron/import_parsers.py".to_string(),
                module_path: vec!["act1-quadron".to_string(), "import_parsers".to_string()],
                source: &importer.source,
                root: &importer.root,
            },
            SourceFile {
                rel_path: "act1-quadron/integrations.py".to_string(),
                module_path: vec!["act1-quadron".to_string(), "integrations".to_string()],
                source: &first.source,
                root: &first.root,
            },
            SourceFile {
                rel_path: "other-project/integrations.py".to_string(),
                module_path: vec!["other-project".to_string(), "integrations".to_string()],
                source: &second.source,
                root: &second.root,
            },
        ];
        let g = lower("demo", &files, &[]);
        assert!(!g.edges().any(|edge| {
            edge.kind == super::edge::IMPORTS && edge.props.get("symbol") == Some(&Json::Bool(true))
        }));
    }

    #[test]
    fn exact_module_without_symbol_blocks_suffix_fallback() {
        let importer = parse(
            "consumer.py",
            "try:\n    from integrations import INTEGRATION_PARSERS\nexcept ImportError:\n    pass\n",
        );
        let exact = parse("integrations.py", "OTHER = 1\n");
        let vendor = parse("vendor/integrations.py", "INTEGRATION_PARSERS = {}\n");
        let files = [
            SourceFile {
                rel_path: "consumer.py".to_string(),
                module_path: vec!["consumer".to_string()],
                source: &importer.source,
                root: &importer.root,
            },
            SourceFile {
                rel_path: "integrations.py".to_string(),
                module_path: vec!["integrations".to_string()],
                source: &exact.source,
                root: &exact.root,
            },
            SourceFile {
                rel_path: "vendor/integrations.py".to_string(),
                module_path: vec!["vendor".to_string(), "integrations".to_string()],
                source: &vendor.source,
                root: &vendor.root,
            },
        ];
        let g = lower("demo", &files, &[]);
        assert!(!g.edges().any(|edge| {
            edge.kind == super::edge::IMPORTS && edge.props.get("symbol") == Some(&Json::Bool(true))
        }));
    }

    #[test]
    fn unknown_from_import_name_has_no_symbol_grain_edge() {
        let g = graph_for_import_pair(
            "def load():\n    from integrations import UNKNOWN as alias\n",
            "KNOWN = 1\n",
        );
        assert!(!g.edges().any(|e| {
            e.kind == edge::IMPORTS && e.props.get("symbol") == Some(&Json::Bool(true))
        }));
        assert!(g.edges().any(|e| {
            e.kind == edge::IMPORTS && e.from == "file::consumer.py" && e.to == "mod::integrations"
        }));
    }

    #[test]
    fn from_import_symbol_edges_are_deterministic() {
        let src = "from integrations import parse as alias\n";
        let provider = "def parse():\n    pass\n";
        assert_eq!(
            graph_for_import_pair(src, provider).to_jsonl(),
            graph_for_import_pair(src, provider).to_jsonl()
        );
    }

    #[test]
    fn function_reads_same_module_constant_once() {
        let g = graph_for(
            "_FORECAST_ENGINE = object()\n\ndef main():\n    return (_FORECAST_ENGINE, _FORECAST_ENGINE)\n",
        );
        let function = g
            .nodes()
            .find(|node| node.kind == ont::FUNCTION && node.name == "main")
            .expect("main function");
        let constant = g
            .nodes()
            .find(|node| node.kind == ont::CONSTANT && node.name == "_FORECAST_ENGINE")
            .expect("module constant");
        let reads: Vec<_> = g
            .edges()
            .filter(|edge| {
                edge.kind == super::edge::READS
                    && edge.from == function.id
                    && edge.to == constant.id
            })
            .collect();
        assert_eq!(reads.len(), 1);
    }

    #[test]
    fn parameter_or_assignment_shadowing_suppresses_constant_reads() {
        for src in [
            "VALUE = 1\n\ndef use(VALUE):\n    return VALUE\n",
            "VALUE = 1\n\ndef use():\n    before = VALUE\n    VALUE = 2\n    return before\n",
            "VALUE = 1\n\ndef use():\n    global VALUE\n    VALUE = 2\n    return VALUE\n",
        ] {
            let g = graph_for(src);
            assert!(
                !g.edges().any(|edge| edge.kind == super::edge::READS),
                "shadowed binding emitted READS for:\n{src}"
            );
        }
    }

    #[test]
    fn keyword_argument_assignment_does_not_shadow_constant_read() {
        let g = graph_for(
            "_ENGINE = \"x\"\n\ndef log(value, mode):\n    return value\n\ndef use():\n    return log(_ENGINE, mode=1)\n",
        );
        let constant = g
            .nodes()
            .find(|node| node.kind == ont::CONSTANT && node.name == "_ENGINE")
            .expect("module constant");
        assert!(g
            .edges()
            .any(|edge| edge.kind == super::edge::READS && edge.to == constant.id));
    }

    #[test]
    fn statement_assignment_still_shadows_constant_read() {
        let g = graph_for("VALUE = 1\n\ndef use():\n    VALUE = consume(VALUE, mode=1)\n");
        assert!(
            !g.edges().any(|edge| edge.kind == super::edge::READS),
            "a real statement-level assignment must shadow the module constant"
        );
    }

    #[test]
    fn lambda_parameters_do_not_read_same_named_module_constants() {
        let g = graph_for(
            "x = 1\n\ndef use():\n    handler = lambda x: x + 1\n    return handler(2)\n",
        );
        assert!(
            !g.edges().any(|edge| edge.kind == super::edge::READS),
            "lambda-local x must not resolve to the module constant"
        );
    }

    #[test]
    fn signature_defaults_and_annotations_are_not_parameters() {
        let g = graph_for("CONST = 1\n\ndef use(mode: CONST = CONST):\n    return CONST\n");
        let constant = g
            .nodes()
            .find(|node| node.kind == ont::CONSTANT && node.name == "CONST")
            .expect("module constant");
        assert!(g
            .edges()
            .any(|edge| edge.kind == super::edge::READS && edge.to == constant.id));
    }

    #[test]
    fn constant_id_index_does_not_classify_functions_as_constants() {
        let g = graph_for("def helper():\n    return 1\n\ndef use():\n    return helper\n");
        assert!(
            !g.edges().any(|edge| edge.kind == super::edge::READS),
            "READS must target module constants only"
        );
    }

    #[test]
    fn relative_from_import_does_not_target_same_named_top_level_module() {
        let first = graph_for_relative_import();
        assert!(!first.edges().any(|e| {
            e.kind == edge::IMPORTS
                && e.from == "file::pkg/consumer.py"
                && e.props.get("symbol") == Some(&Json::Bool(true))
        }));
        assert_eq!(
            first.to_jsonl(),
            graph_for_relative_import().to_jsonl(),
            "relative import lowering must be byte-deterministic"
        );
    }

    #[test]
    fn reassigned_constant_still_receives_symbol_grain_import() {
        let g = graph_for_import_pair(
            "from integrations import INTEGRATION_PARSERS\n",
            "INTEGRATION_PARSERS: dict = {}\nINTEGRATION_PARSERS = {}\n",
        );
        let target = g
            .nodes()
            .find(|n| n.kind == ont::CONSTANT && n.name == "INTEGRATION_PARSERS")
            .expect("provider constant");
        assert!(g.edges().any(|e| {
            e.kind == edge::IMPORTS
                && e.from == "file::consumer.py"
                && e.to == target.id
                && e.props.get("symbol") == Some(&Json::Bool(true))
        }));
    }

    #[test]
    fn inheritance_emits_extends() {
        let g = graph_for("class Base:\n    pass\n\nclass Derived(Base):\n    pass\n");
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an EXTENDS edge");
        assert!(ext.from.starts_with("type::mod.Derived"));
        assert!(ext.to.starts_with("type::mod.Base"));
    }

    #[test]
    fn membership_before_generator_for_does_not_confuse_shadow_scan() {
        let g = graph_for(
            "VALUE = 1\n\ndef main(items):\n    if VALUE in (item for item in items):\n        return VALUE\n",
        );
        let constant = g
            .nodes()
            .find(|node| node.kind == ont::CONSTANT && node.name == "VALUE")
            .expect("module constant");
        assert_eq!(
            g.edges()
                .filter(|edge| edge.kind == super::edge::READS && edge.to == constant.id)
                .count(),
            1
        );
    }

    #[test]
    fn module_level_assignment_is_constant() {
        let g = graph_for("VERSION = \"1.0\"\nclass C:\n    attr = 1\n");
        // VERSION is a module-level Constant; C.attr (class attribute) is not.
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 1);
        let c = g
            .nodes()
            .find(|n| n.kind == ont::CONSTANT)
            .expect("a constant");
        assert_eq!(c.name, "VERSION");
    }

    #[test]
    fn decorator_recorded_as_property() {
        let g = graph_for("class C:\n    @staticmethod\n    def s():\n        pass\n");
        let m = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "s")
            .expect("the decorated method");
        assert_eq!(
            m.props.get("decorators"),
            Some(&Json::Array(vec![Json::str("staticmethod")]))
        );
    }

    #[test]
    fn type_use_in_annotation() {
        let g = graph_for("class Widget:\n    pass\n\ndef build(w: Widget):\n    pass\n");
        assert!(
            g.edges()
                .any(|e| e.kind == edge::USES_TYPE && e.to.contains("Widget")),
            "param annotation should create USES_TYPE"
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src = "import os\nclass C(Base):\n    def m(self):\n        helper()\n\ndef helper():\n    pass\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }

    // --- global_method rung: the singleton law -------------------------------

    #[test]
    fn method_call_ambiguous_when_free_function_shares_name() {
        // One class method named `json` plus a same-name module function: an
        // unknown-receiver call must be AMBIGUOUS, never guessed.
        let src = "class D:\n    def json(self, d):\n        pass\n\ndef json(body):\n    pass\n\ndef handle(resp):\n    resp.json()\n";
        let g = graph_for(src);
        let calls = call_edges(&g);
        let e = calls
            .iter()
            .find(|e| {
                e.props.get("callee") == Some(&Json::str("json")) && e.from.contains("handle")
            })
            .expect("the resp.json() call");
        assert_eq!(e.props.get("resolution"), Some(&Json::str("global_method")));
        assert_eq!(e.props.get("ambiguous"), Some(&Json::Bool(true)));
        assert_eq!(e.props.get("candidate_count"), Some(&Json::U64(2)));
    }

    #[test]
    fn method_call_never_resolves_to_free_function_alone() {
        // No project method named `log`: `console.log()`-shaped calls stay
        // external even when a module function shares the name.
        let src = "def log(msg):\n    pass\n\ndef run(logger):\n    logger.log(\"x\")\n";
        let g = graph_for(src);
        let calls = call_edges(&g);
        let e = calls
            .iter()
            .find(|e| {
                e.props.get("callee") == Some(&Json::str("log"))
                    && e.props.get("method") == Some(&Json::Bool(true))
            })
            .expect("the logger.log() call");
        assert_eq!(e.props.get("resolution"), Some(&Json::str("external")));
        assert_eq!(e.props.get("resolved"), Some(&Json::Bool(false)));
    }
}
