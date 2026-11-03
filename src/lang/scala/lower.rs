//! Lower the Scala CST into the canonical graph.
//!
//! This mirrors the Rust and Python lowerings — same conservative principles,
//! same shared ontology — adapted to Scala's surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to
//!    a concrete project definition only when a scope level yields exactly one
//!    candidate; several candidates are emitted as an ambiguous edge with the
//!    full `candidates` set; none resolves to an explicit external/unresolved
//!    node.
//! 2. **Everything comes from real tokens.** Calls, parents, imports, and type
//!    uses are read off the lossless tree, never guessed.
//!
//! Resolution uses a deterministic **scope ladder** (most specific first; the
//! first level with any candidate decides), the Scala analogue of the Rust/Python
//! ladder: receiver (`this`/`self`) → local package → file imports → global.
//! Each edge records which level resolved it, so the call graph stays auditable.
//!
//! Honest mappings (see the IR Atlas):
//!   - `def` → [`Function`] (a method of a `class`/`trait`/`object`/`enum` →
//!     `HAS_METHOD`).
//!   - `class`/`case class` → [`Type`] (`type_kind: class`), `trait` →
//!     `type_kind: trait`, `object`/`package object` → `type_kind: object`,
//!     `enum` → `type_kind: enum`, `type X = …` → `type_kind: alias`.
//!   - `val`/`var` (outside a method body) → [`Constant`]; `given` → `Constant`.
//!   - `import a.b.c` / `import a.b.{…}` → [`IMPORTS`] (plus
//!     `ExternalDependency`/`DEPENDS_ON` for non-project roots).
//!   - `extends Parent` → [`EXTENDS`] (the primary supertype); each `with Trait`
//!     mixin → [`IMPLEMENTS`] (conforms-to). This split is the honest reading of
//!     Scala's surface: `extends` names the primary parent, `with` names mixed-in
//!     traits.
//!
//! Constructs without an IR home are not force-fit: Scala 3 `enum` *cases* (a
//! constructor-like form) stay inside the lossless tree but get no dedicated node
//! kind — there is no `EnumCase`/`Variant` kind in the Atlas, and inventing a
//! `CALLS`/`Constant` for them would be a lie. See `docs/ir-atlas.md` candidate
//! extensions.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::Node;
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::scala::lexer::{is_keyword, kind as tk};
use crate::lang::scala::parser::node as cst;

/// Lower a whole project's worth of Scala files into a graph. `manifest_deps` is
/// unused for Scala (the pipeline's manifest reader is Cargo-only); dependencies
/// are discovered from `import` statements instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    // Project-local roots: the package plus every package/module segment. An
    // import whose first segment is one of these is intra-project, not external.
    let mut local_roots: BTreeSet<String> = BTreeSet::new();
    local_roots.insert(package.to_string());
    for f in files {
        for seg in &f.module_path {
            local_roots.insert(seg.clone());
        }
        for seg in package_segments(f.root, f.source) {
            local_roots.insert(seg);
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
        vec![("ecosystem", Json::str("scala"))],
    );

    // Pass B: create definition nodes + structural edges, build symbol tables and
    // per-file import maps. Parents (extends/with) are deferred to pass C so a
    // base defined later in the project still resolves.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_parents: Vec<PendingParent> = Vec::new();
    for (idx, f) in files.iter().enumerate() {
        lo.imports.push(BTreeMap::new());
        lo.cur_file = idx;
        let li = LineIndex::new(f.source);
        // Scala's module scope comes from `package` declarations; fall back to the
        // path-derived module path when a file has none.
        let pkg_segs = package_segments(f.root, f.source);
        let module_path: Vec<String> = if pkg_segs.is_empty() {
            f.module_path.clone()
        } else {
            pkg_segs
        };
        let module_join = module_path.join(".");
        let leaf = lo.ensure_modules(&module_path);
        let file_id = format!("file::{}", f.rel_path);
        lo.g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("scala")),
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
            &mut pend_parents,
        );
    }

    // Pass C: resolve calls (scope ladder), type usages, and parents against the
    // now-complete symbol tables.
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
    for pp in &pend_parents {
        lo.emit_parent(pp);
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
    block: Option<&'a Node>,
    signature: Option<&'a Node>,
    module_join: String,
    owner_type: Option<String>,
    file_idx: usize,
}

/// A deferred `extends`/`with` link, resolved in pass C.
struct PendingParent {
    type_id: String,
    parent_name: String,
    /// `EXTENDS` for the primary supertype, `IMPLEMENTS` for `with` mixins.
    relation: &'static str,
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
    /// module id (or the package id for a file with no package/module segments).
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
                vec![("language", Json::str("scala"))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    /// Walk a statement container (a `SourceFile` or `Block`), creating definition
    /// nodes and recursing into nested scopes. `owner` is the nearest enclosing
    /// type (cleared when descending into a function); `in_function` gates
    /// `Constant` emission for `val`/`var`.
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
        pend_parents: &mut Vec<PendingParent>,
    ) {
        for item in container.child_nodes() {
            match item.kind {
                cst::DEF => self.handle_fn(
                    item,
                    file_id,
                    module_join,
                    scope,
                    owner,
                    src,
                    li,
                    pend_fns,
                    pend_parents,
                ),
                cst::CLASS | cst::TRAIT | cst::OBJECT | cst::ENUM => self.handle_type(
                    item,
                    file_id,
                    module_join,
                    scope,
                    src,
                    li,
                    pend_fns,
                    pend_parents,
                ),
                cst::TYPE_DEF => self.handle_typedef(item, file_id, module_join, scope, src, li),
                cst::VAL => {
                    if !in_function {
                        self.handle_val(item, file_id, module_join, scope, src, li);
                    }
                }
                cst::GIVEN => {
                    if !in_function {
                        self.handle_given(item, file_id, module_join, scope, src, li, pend_fns);
                    }
                }
                cst::EXTENSION => {
                    // An `extension` block's defs are functions, not methods of a
                    // named type: recurse with a fresh (None) owner.
                    if let Some(block) = item.child(cst::BLOCK) {
                        self.walk_stmts(
                            block,
                            file_id,
                            module_join,
                            scope,
                            None,
                            false,
                            src,
                            li,
                            pend_fns,
                            pend_parents,
                        );
                    }
                }
                cst::PACKAGE => {
                    // `package a.b { … }` block form: definitions inside are scoped
                    // under the extra package segments.
                    if let Some(block) = item.child(cst::BLOCK) {
                        let segs = ident_path(item.child(cst::HEADER), src);
                        let inner_join = join_modules(module_join, &segs);
                        let leaf = self.ensure_modules_join(&inner_join);
                        self.g
                            .add_edge(leaf, edge::CONTAINS, file_id.to_string(), vec![]);
                        self.walk_stmts(
                            block,
                            file_id,
                            &inner_join,
                            scope,
                            None,
                            false,
                            src,
                            li,
                            pend_fns,
                            pend_parents,
                        );
                    }
                }
                cst::IMPORT => self.handle_import(item, file_id, src),
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
        pend_parents: &mut Vec<PendingParent>,
    ) {
        let name = name_text(item, src).unwrap_or("<anonymous>").to_string();
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(module_join, scope, &name);
        let id = format!("fn::{qual}#{line}");
        let block = item.child(cst::BLOCK);
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("scala")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            ("has_body", Json::Bool(block.is_some())),
        ];
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

        // Nested defs inside a method body are plain functions: descend with a
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
                pend_parents,
            );
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
        pend_parents: &mut Vec<PendingParent>,
    ) {
        let name = name_text(item, src).unwrap_or("<anonymous>").to_string();
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(module_join, scope, &name);
        let id = format!("type::{qual}");
        let type_kind = match item.kind {
            cst::TRAIT => "trait",
            cst::OBJECT => "object",
            cst::ENUM => "enum",
            _ => "class",
        };
        let mut props = vec![
            ("type_kind", Json::str(type_kind)),
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("scala")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
        ];
        if has_modifier(item, src, "case") {
            props.push(("case", Json::Bool(true)));
        }
        if has_modifier(item, src, "sealed") {
            props.push(("sealed", Json::Bool(true)));
        }
        if has_modifier(item, src, "abstract") {
            props.push(("abstract", Json::Bool(true)));
        }
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

        // Parents: `extends P` (EXTENDS) and each `with T` (IMPLEMENTS), resolved
        // in pass C.
        let (ext, withs) = parents(item, src);
        if let Some(p) = ext {
            pend_parents.push(PendingParent {
                type_id: id.clone(),
                parent_name: p,
                relation: edge::EXTENDS,
            });
        }
        for w in withs {
            pend_parents.push(PendingParent {
                type_id: id.clone(),
                parent_name: w,
                relation: edge::IMPLEMENTS,
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
                pend_parents,
            );
        }
    }

    fn handle_typedef(
        &mut self,
        item: &Node,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        src: &str,
        li: &LineIndex,
    ) {
        let name = match name_text(item, src) {
            Some(n) => n.to_string(),
            None => return,
        };
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(module_join, scope, &name);
        let id = format!("type::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str("alias")),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("scala")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name.entry(name).or_default().push(id);
    }

    fn handle_val(
        &mut self,
        item: &Node,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        src: &str,
        li: &LineIndex,
    ) {
        let name = match name_text(item, src) {
            Some(n) if !is_keyword(n) => n.to_string(),
            _ => return, // pattern binding / no simple name: not a named constant
        };
        let line = li.line_col(name_span_start(item)).line;
        let binding = item
            .tokens()
            .map(|t| t.span.text(src))
            .find(|t| *t == "val" || *t == "var")
            .unwrap_or("val");
        let id = format!("const::{}", qual_name(module_join, scope, &name));
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            name,
            vec![
                ("binding", Json::str(binding.to_string())),
                ("language", Json::str("scala")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_given<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
    ) {
        // A `given` may be named (`given x: T = …`) or anonymous (`given T = …`).
        // Use the leading identifier as the name when present; otherwise key it by
        // line so distinct anonymous givens stay distinct and deterministic.
        let header = item.child(cst::HEADER);
        let line = li.line_col(item.span.start).line;
        let name = given_name(header, src).unwrap_or_else(|| format!("given${line}"));
        let qual = qual_name(module_join, scope, &name);
        let id = format!("const::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            name,
            vec![
                ("binding", Json::str("given")),
                ("language", Json::str("scala")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        // Scan the given body for calls, like a function.
        pend_fns.push(PendingFn {
            id,
            source: src,
            block: item.child(cst::BLOCK),
            signature: header,
            module_join: module_join.to_string(),
            owner_type: None,
            file_idx: self.cur_file,
        });
    }

    /// `import a.b.c` / `import a.b._` / `import a.b.{x, y => z, _}`. Emits the
    /// `IMPORTS` edge for the module path and records explicit imported names in
    /// the per-file import map for the call resolver.
    fn handle_import(&mut self, item: &Node, file_id: &str, src: &str) {
        // Direct children: leading `import`/`export` token, the dotted path tokens,
        // and an optional `{ … }` selector group.
        let mut segs: Vec<String> = Vec::new();
        let mut selectors: Option<&Node> = None;
        for child in &item.children {
            match child {
                crate::core::cst::Child::Token(t) if t.trivia => {}
                crate::core::cst::Child::Token(t) => {
                    let text = t.span.text(src);
                    if text == "import" || text == "export" || text == "." {
                        continue;
                    }
                    if (t.kind == tk::IDENT || t.kind == tk::BACKTICK_IDENT) && text != "_" {
                        segs.push(strip_backticks(text).to_string());
                    }
                    // `_` and stray punctuation are ignored for the path.
                }
                crate::core::cst::Child::Node(n) if n.kind == cst::BRACE => {
                    selectors = Some(n);
                }
                crate::core::cst::Child::Node(_) => {}
            }
        }
        if segs.is_empty() && selectors.is_none() {
            return;
        }
        let path_text = segs.join(".");
        self.emit_import_edge(file_id, &segs, &path_text);

        match selectors {
            Some(group) => {
                // `import a.b.{x, y => z, _}`: each selector binds a name.
                for clause in split_commas(top_level_tokens(group, src)) {
                    let names: Vec<&Tok> = clause
                        .iter()
                        .filter(|t| t.kind == tk::IDENT || t.kind == tk::BACKTICK_IDENT)
                        .collect();
                    if names.is_empty() {
                        continue; // a `_` wildcard selector
                    }
                    // `orig => alias` keeps the alias as the bound leaf.
                    let leaf = strip_backticks(names.last().unwrap().text).to_string();
                    let orig = strip_backticks(names[0].text).to_string();
                    let mut full = segs.clone();
                    full.push(orig);
                    self.imports[self.cur_file].insert(leaf, full);
                }
            }
            None => {
                // `import a.b.c`: the leaf `c` binds to the full path.
                if let Some(leaf) = segs.last() {
                    self.imports[self.cur_file].insert(leaf.clone(), segs.clone());
                }
            }
        }
    }

    fn emit_import_edge(&mut self, file_id: &str, segs: &[String], path_text: &str) {
        let root = match segs.first() {
            Some(r) => r.clone(),
            None => return,
        };
        let internal = self.local_roots.contains(&root);
        if internal {
            let id = format!("mod::{root}");
            self.g.upsert_node(
                id.clone(),
                ont::MODULE,
                root.clone(),
                vec![("language", Json::str("scala"))],
            );
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                id,
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

    /// Ensure a dotted module-join chain (`a.b.c`) exists, returning the leaf id.
    fn ensure_modules_join(&mut self, join: &str) -> String {
        if join.is_empty() {
            return self.pkg_id();
        }
        let path: Vec<String> = join.split('.').map(|s| s.to_string()).collect();
        self.ensure_modules(&path)
    }

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        if call.method {
            if matches!(call.receiver.as_deref(), Some("this") | Some("self")) {
                if let Some(owner) = &ctx.owner_type {
                    let c = self.methods_of(owner, &call.name);
                    if !c.is_empty() {
                        return mk(c, "receiver");
                    }
                }
            }
            // Unknown receiver type (no inference). The honest candidate set is
            // every same-name method PLUS every same-name free function — a Scala
            // member call can also reach a top-level def or an `extension`
            // block's defs, which are indexed as plain functions.
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

        let c = self.fns_in_module(&ctx.module_join, &call.name);
        if !c.is_empty() {
            return mk(c, "local");
        }
        if let Some(segs) = ctx.imports.get(&call.name) {
            if let Some(modj) = self.import_module_join(segs) {
                let c = self.fns_in_module(&modj, &call.name);
                if !c.is_empty() {
                    return mk(c, "import");
                }
            }
        }
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

    /// Resolve a deferred `extends`/`with` link into a concrete edge, pointing at
    /// the project type when unique, otherwise an explicit `UnresolvedSymbol`.
    fn emit_parent(&mut self, pp: &PendingParent) {
        let target = match self.unique_type(&pp.parent_name) {
            Some(id) => id,
            None => {
                let id = unresolved_id(&pp.parent_name);
                if !self.g.has_node(&id) {
                    self.g.upsert_node(
                        id.clone(),
                        ont::UNRESOLVED,
                        pp.parent_name.clone(),
                        vec![
                            ("unresolved", Json::Bool(true)),
                            ("role", Json::str("supertype")),
                        ],
                    );
                }
                id
            }
        };
        self.g.add_edge(
            pp.type_id.clone(),
            pp.relation,
            target,
            vec![("parent_name", Json::str(pp.parent_name.clone()))],
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

    /// Add `USES_TYPE` edges for identifiers in a signature `Header` (parameter /
    /// return-type annotations) that name a unique project type.
    fn emit_type_uses(&mut self, from_id: &str, region: &Node, src: &str) {
        let mut seen: Vec<String> = Vec::new();
        for n in region.walk() {
            for t in n.tokens() {
                if t.kind != tk::IDENT && t.kind != tk::BACKTICK_IDENT {
                    continue;
                }
                let name = strip_backticks(t.span.text(src));
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

/// `module.scope….name` — the dotted qualified name and basis for node ids.
fn qual_name(module_join: &str, scope: &[String], name: &str) -> String {
    let mut parts: Vec<String> = Vec::new();
    if !module_join.is_empty() {
        parts.push(module_join.to_string());
    }
    parts.extend(scope.iter().cloned());
    parts.push(strip_backticks(name).to_string());
    parts.join(".")
}

fn join_modules(base: &str, extra: &[String]) -> String {
    let mut parts: Vec<String> = Vec::new();
    if !base.is_empty() {
        parts.push(base.to_string());
    }
    parts.extend(extra.iter().cloned());
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

fn strip_backticks(s: &str) -> &str {
    s.strip_prefix('`')
        .and_then(|s| s.strip_suffix('`'))
        .unwrap_or(s)
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

/// True if a definition node carries the given modifier token before its name.
fn has_modifier(item: &Node, src: &str, word: &str) -> bool {
    item.tokens().any(|t| t.span.text(src) == word)
}

/// Annotation type names attached to a definition (the last identifier of each
/// `@Ann` path), as a JSON array property, or `None` when there are none.
fn annotations(item: &Node, src: &str) -> Option<Json> {
    let mut names: Vec<Json> = Vec::new();
    for a in item.children_of(cst::ANNOTATION) {
        let mut last: Option<&str> = None;
        for t in a.tokens() {
            if t.kind == tk::IDENT || t.kind == tk::BACKTICK_IDENT {
                last = Some(strip_backticks(t.span.text(src)));
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

/// Extract `(extends_parent, with_mixins)` simple names from a type node's header.
/// Only the final identifier of each dotted parent path is taken (`Parent` from
/// `a.b.Parent`); type arguments and constructor arguments are child groups and
/// are skipped naturally.
fn parents(item: &Node, src: &str) -> (Option<String>, Vec<String>) {
    let header = match item.child(cst::HEADER) {
        Some(h) => h,
        None => return (None, Vec::new()),
    };
    let mut ext: Option<String> = None;
    let mut withs: Vec<String> = Vec::new();
    let mut mode: Mode = Mode::None;
    let mut cur: Option<String> = None;
    for t in top_level_tokens(header, src) {
        match t.text {
            "extends" => {
                finalize(&mut mode, &mut cur, &mut ext, &mut withs);
                mode = Mode::Extends;
            }
            "with" => {
                finalize(&mut mode, &mut cur, &mut ext, &mut withs);
                mode = Mode::With;
            }
            "derives" => {
                finalize(&mut mode, &mut cur, &mut ext, &mut withs);
                mode = Mode::None; // `derives` typeclasses are not supertypes
            }
            "." => {} // path separator; keep accumulating the last ident
            _ if t.kind == tk::IDENT || t.kind == tk::BACKTICK_IDENT => {
                if !matches!(mode, Mode::None) {
                    cur = Some(strip_backticks(t.text).to_string());
                }
            }
            _ => {
                // Any other token (an operator, etc.) ends the current parent name.
                finalize(&mut mode, &mut cur, &mut ext, &mut withs);
            }
        }
    }
    finalize(&mut mode, &mut cur, &mut ext, &mut withs);
    (ext, withs)
}

enum Mode {
    None,
    Extends,
    With,
}

fn finalize(
    mode: &mut Mode,
    cur: &mut Option<String>,
    ext: &mut Option<String>,
    withs: &mut Vec<String>,
) {
    if let Some(name) = cur.take() {
        match mode {
            Mode::Extends => {
                if ext.is_none() {
                    *ext = Some(name);
                }
            }
            Mode::With => withs.push(name),
            Mode::None => {}
        }
    }
}

/// The bound name of a `given` from its header: the leading identifier when the
/// header is `name : Type …` (a top-level `:` op follows the name), else `None`
/// for an anonymous given.
fn given_name(header: Option<&Node>, src: &str) -> Option<String> {
    let header = header?;
    let toks = top_level_tokens(header, src);
    let first = toks.first()?;
    if first.kind != tk::IDENT && first.kind != tk::BACKTICK_IDENT {
        return None;
    }
    // A named given is `given name: T`; the second top-level token is `:`.
    match toks.get(1) {
        Some(t) if t.text == ":" => Some(strip_backticks(first.text).to_string()),
        _ => None,
    }
}

/// Collect dotted identifier path segments from a header node (used for package
/// paths): the IDENT tokens in order, dots ignored.
fn ident_path(header: Option<&Node>, src: &str) -> Vec<String> {
    let header = match header {
        Some(h) => h,
        None => return Vec::new(),
    };
    top_level_tokens(header, src)
        .into_iter()
        .filter(|t| t.kind == tk::IDENT || t.kind == tk::BACKTICK_IDENT)
        .map(|t| strip_backticks(t.text).to_string())
        .collect()
}

/// Package-declaration segments from a source file's top-level `package` nodes,
/// concatenated in order (`package a.b` then `package c` → `[a, b, c]`). Block
/// package forms (`package a { … }`) are intentionally excluded here — their
/// scope is applied where the block is walked.
fn package_segments(root: &Node, src: &str) -> Vec<String> {
    let mut segs = Vec::new();
    for item in root.children_of(cst::PACKAGE) {
        if item.child(cst::BLOCK).is_some() {
            continue;
        }
        segs.extend(ident_path(item.child(cst::HEADER), src));
    }
    segs
}

/// A flat token (text + kind), used by the small token-list helpers.
#[derive(Clone, Copy)]
struct Tok<'a> {
    text: &'a str,
    kind: &'static str,
}

/// Direct, non-trivia child tokens of `node` in source order (does not descend
/// into child group nodes).
fn top_level_tokens<'a>(node: &'a Node, src: &'a str) -> Vec<Tok<'a>> {
    node.tokens()
        .map(|t| Tok {
            text: t.span.text(src),
            kind: t.kind,
        })
        .collect()
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
                ident: t.kind == tk::IDENT || t.kind == tk::BACKTICK_IDENT,
            }),
            crate::core::cst::Child::Node(n) => v.push(El::Grp(n)),
        }
    }
    v
}

/// Is `els[from]` the application of an argument list — an optional `[type args]`
/// bracket group followed by a `(…)` or `{…}` group? Returns the matched flag.
fn is_application_at(els: &[El<'_>], from: usize) -> bool {
    let mut j = from;
    if let Some(g) = els.get(j).and_then(grp) {
        if g.kind == cst::BRACKET {
            j += 1; // skip type-argument group
        }
    }
    matches!(
        els.get(j).and_then(grp),
        Some(g) if g.kind == cst::PAREN || g.kind == cst::BRACE
    )
}

/// Detect `name(...)`, `name { ... }`, `name[T](...)`, and `recv.name(...)` call
/// sites over the real token tree, recursing into nested groups and blocks but
/// **not** into nested definition nodes (those are scanned as their own
/// functions). Keywords are excluded.
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        // Method/selector call: `.` name [type args] (args).
        if tok_text(&els[i]) == Some(".") {
            if i + 1 < n && is_ident_el(&els[i + 1]) && is_application_at(&els, i + 2) {
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
            }
            i += 1;
            continue;
        }
        // Bare call: name [type args] (args), not preceded by `.` or a definition
        // keyword.
        if is_ident_el(&els[i]) {
            let prev = if i > 0 { tok_text(&els[i - 1]) } else { None };
            let text = tok_text(&els[i]).unwrap_or("");
            let is_def = matches!(
                prev,
                Some("def")
                    | Some("class")
                    | Some("trait")
                    | Some("object")
                    | Some("enum")
                    | Some("val")
                    | Some("var")
                    | Some("type")
            );
            if prev != Some(".") && !is_def && !is_keyword(text) && is_application_at(&els, i + 1) {
                out.push(Call {
                    name: text.to_string(),
                    method: false,
                    receiver: None,
                });
            }
        }
        i += 1;
    }
    // Recurse into groups and nested non-definition blocks; never into nested
    // definition nodes (handled as their own pending functions).
    for e in &els {
        if let Some(g) = grp(e) {
            if !is_definition_kind(g.kind) {
                scan_calls(g, src, out);
            }
        }
    }
}

fn is_definition_kind(kind: &str) -> bool {
    matches!(
        kind,
        cst::DEF
            | cst::CLASS
            | cst::TRAIT
            | cst::OBJECT
            | cst::ENUM
            | cst::GIVEN
            | cst::TYPE_DEF
            | cst::EXTENSION
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::scala::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("Mod.scala", src);
        let file = SourceFile {
            rel_path: "Mod.scala".to_string(),
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
        let g = graph_for(
            "package p\nclass C {\n  def m: Int = 1\n}\nobject O {\n  def f: Int = 2\n}\n",
        );
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "C.m + O.f");
        assert_eq!(g.count_nodes_of(ont::TYPE), 2, "class C + object O");
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "package p module");
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD));
    }

    #[test]
    fn type_kinds_are_honest() {
        let g = graph_for("class A\ntrait B\nobject C\nenum E { case X }\ntype T = Int\n");
        let kinds: BTreeSet<String> = g
            .nodes()
            .filter(|n| n.kind == ont::TYPE)
            .filter_map(|n| n.props.get("type_kind"))
            .filter_map(|j| match j {
                Json::Str(s) => Some(s.clone()),
                _ => None,
            })
            .collect();
        for expect in ["class", "trait", "object", "enum", "alias"] {
            assert!(
                kinds.contains(expect),
                "missing type_kind {expect}: {kinds:?}"
            );
        }
    }

    #[test]
    fn case_class_is_flagged() {
        let g = graph_for("case class Point(x: Int, y: Int)\n");
        let ty = g
            .nodes()
            .find(|n| n.kind == ont::TYPE && n.name == "Point")
            .expect("Point type");
        assert_eq!(ty.props.get("type_kind"), Some(&Json::str("class")));
        assert_eq!(ty.props.get("case"), Some(&Json::Bool(true)));
        assert_eq!(ty.props.get("language"), Some(&Json::str("scala")));
    }

    #[test]
    fn resolves_unique_local_call() {
        let g = graph_for("def add(a: Int, b: Int): Int = a + b\ndef run(): Unit = add(1, 2)\n");
        let calls = call_edges(&g);
        let add = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("add")))
            .expect("a call to add");
        assert!(add.to.starts_with("fn::add"));
        assert_eq!(add.props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn this_method_resolves_via_receiver() {
        let g = graph_for("class P {\n  def a(): Unit = this.b()\n  def b(): Unit = ()\n}\n");
        let calls = call_edges(&g);
        let recv = calls
            .iter()
            .find(|e| e.props.get("resolution") == Some(&Json::str("receiver")));
        assert!(recv.is_some(), "this.b() should resolve via receiver scope");
        assert_eq!(recv.unwrap().props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for("def run(): Unit = mystery()\n");
        let calls = call_edges(&g);
        assert!(calls
            .iter()
            .any(|e| e.props.get("resolution") == Some(&Json::str("external"))));
        assert!(g.has_node("unresolved::mystery"));
    }

    #[test]
    fn external_import_creates_dependency() {
        let g = graph_for("import scala.collection.mutable\nimport java.util.{List, Map}\n");
        assert!(g.has_node("ext::scala"));
        assert!(g.has_node("ext::java"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::scala"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn extends_and_with_split() {
        let g = graph_for("trait Drawable\nclass Base\nclass C extends Base with Drawable\n");
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an EXTENDS edge");
        assert!(ext.from.starts_with("type::C"));
        assert!(ext.to.starts_with("type::Base"));
        let imp = g
            .edges()
            .find(|e| e.kind == edge::IMPLEMENTS)
            .expect("an IMPLEMENTS edge");
        assert!(imp.to.starts_with("type::Drawable"));
    }

    #[test]
    fn val_is_constant_field_not_local() {
        let g = graph_for(
            "object O {\n  val version = \"1.0\"\n  def f(): Int = {\n    val local = 1\n    local\n  }\n}\n",
        );
        // `version` is a field-level Constant; `local` (inside f's body) is not.
        let consts: Vec<&str> = g
            .nodes()
            .filter(|n| n.kind == ont::CONSTANT)
            .map(|n| n.name.as_str())
            .collect();
        assert!(
            consts.contains(&"version"),
            "version is a constant: {consts:?}"
        );
        assert!(!consts.contains(&"local"), "local must not be a constant");
    }

    #[test]
    fn type_use_in_signature() {
        let g = graph_for("class Widget\ndef build(w: Widget): Unit = ()\n");
        assert!(
            g.edges()
                .any(|e| e.kind == edge::USES_TYPE && e.to.contains("Widget")),
            "param type should create USES_TYPE"
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src = "package p\nimport a.b.C\nclass D extends C {\n  def m(): Unit = helper()\n}\ndef helper(): Unit = ()\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
