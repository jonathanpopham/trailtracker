//! Lower the D CST into the canonical graph.
//!
//! This mirrors the Rust and C++ lowerings ([`crate::ir::lower`],
//! [`crate::lang::cpp::lower`]) — same conservative principles, same shared
//! ontology — adapted to D's surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to
//!    a concrete project definition only when a scope level yields exactly one
//!    candidate; several candidates become an ambiguous edge carrying the full
//!    `candidates` set; none resolves to an explicit `UnresolvedSymbol`.
//! 2. **Everything comes from real tokens.** Calls, base lists, imports, and
//!    type uses are read off the lossless tree, never guessed.
//!
//! Honest mappings (see the IR Atlas):
//!   - `module a.b.c;` → a `Module` chain (`a` → `a.b` → `a.b.c`), which also
//!     becomes the file's scope.
//!   - `import a.b;` → `IMPORTS` (to a project `File` when the imported module is
//!     declared in the batch, otherwise an `ExternalDependency` + `DEPENDS_ON`).
//!   - `class`/`struct`/`interface`/`union` → `Type` (`type_kind`); `enum` with a
//!     body → `Type` (`type_kind: enum`) + enumerator `Constant`s; `enum X = v;`
//!     → a manifest `Constant`; `template` → `Type` (`type_kind: template`).
//!   - function/method → `Function` (a method → `HAS_METHOD` from its enclosing
//!     aggregate); `this`/`~this` are constructors/destructors.
//!   - `alias X = T;` / `alias T X;` → `Type` (`type_kind: alias`).
//!   - module-level `const`/`immutable` variable → `Constant`.
//!   - base list `: B, I` → `EXTENDS` to a base class / `IMPLEMENTS` to an
//!     interface, decided by the resolved supertype's kind (interfaces only ever
//!     `EXTENDS`); see [`Lowerer::emit_extends`]. This is a documented heuristic,
//!     since D's `:` list does not syntactically separate the base class from
//!     interfaces.
//!   - call sites `name(...)`, `recv.name(...)`, and `new T(...)` → `CALLS`,
//!     resolved by a deterministic scope ladder.

use std::collections::BTreeMap;

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::d::lexer::{is_keyword, kind as tk};
use crate::lang::d::parser::node as cst;
use crate::lang::frontend::SourceFile;

const LANG: &str = "d";

/// Lower a whole project's worth of D files into a graph. `manifest_deps` is
/// unused for D (the pipeline's manifest reader is Cargo-only); dependencies are
/// discovered from `import` declarations instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        fn_by_name: BTreeMap::new(),
        fn_by_scope: BTreeMap::new(),
        method_by_name: BTreeMap::new(),
        method_by_type: BTreeMap::new(),
        type_by_name: BTreeMap::new(),
        type_is_interface: BTreeMap::new(),
        modules_by_name: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str(LANG))],
    );

    // Pass A: index every file's declared module name so `import` can resolve to
    // a real File in the batch.
    for f in files {
        if let Some(segs) = module_segments(f.root, f.source) {
            lo.modules_by_name
                .insert(segs.join("."), format!("file::{}", f.rel_path));
        }
    }

    // Pass B: definition nodes + structural edges + symbol tables. Calls and
    // inheritance are deferred to pass C so a target defined later still resolves.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_extends: Vec<PendingExtends> = Vec::new();
    for f in files {
        let li = LineIndex::new(f.source);
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
        lo.g.add_edge(lo.pkg_id(), edge::CONTAINS, file_id.clone(), vec![]);

        // The file's module declaration sets its base scope.
        let base_scope = match module_segments(f.root, f.source) {
            Some(segs) => {
                lo.ensure_module(&segs);
                segs
            }
            None => Vec::new(),
        };
        lo.walk_items(
            f.root,
            &file_id,
            &base_scope,
            None,
            f.source,
            &li,
            &mut pend_fns,
            &mut pend_extends,
        );
    }

    // Pass C: resolve calls (scope ladder), type usages, and inheritance against
    // the now-complete symbol tables.
    for pf in &pend_fns {
        let ctx = Ctx {
            scope_join: pf.scope_join.clone(),
            owner_type: pf.owner_type.clone(),
        };
        if let Some(block) = pf.block {
            let mut calls = Vec::new();
            scan_calls(block, pf.source, &mut calls);
            for call in &calls {
                let res = lo.resolve(call, &ctx);
                lo.emit_call(&pf.id, call, res);
            }
        }
        lo.emit_type_uses(&pf.id, pf.item, pf.source);
    }
    for pe in &pend_extends {
        lo.emit_extends(pe);
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    /// Simple name → all function node ids (global level).
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// (scope_join, name) → function ids (local-scope level).
    fn_by_scope: BTreeMap<(String, String), Vec<String>>,
    /// Simple name → method node ids only (global method-call level).
    method_by_name: BTreeMap<String, Vec<String>>,
    /// (type_name, method_name) → method ids (receiver level).
    method_by_type: BTreeMap<(String, String), Vec<String>>,
    /// Simple name → type node ids.
    type_by_name: BTreeMap<String, Vec<String>>,
    /// Type node id → whether it is an `interface` (drives EXTENDS vs IMPLEMENTS).
    type_is_interface: BTreeMap<String, bool>,
    /// Declared module name (dotted) → file node id (for local import resolution).
    modules_by_name: BTreeMap<String, String>,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    /// The function body block, if it has one (definition); `None` for prototypes.
    block: Option<&'a Node>,
    /// The whole function node, scanned (minus its body) for type uses.
    item: &'a Node,
    scope_join: String,
    owner_type: Option<String>,
}

/// A deferred base link, resolved in pass C.
struct PendingExtends {
    type_id: String,
    base_name: String,
    /// True when the subtype is an `interface` (interfaces only ever EXTENDS).
    sub_is_interface: bool,
}

/// The enclosing aggregate while walking, for methods (`HAS_METHOD`, receiver).
struct Owner {
    name: String,
    id: String,
}

/// A detected call site over the lossless tree.
struct Call {
    name: String,
    kind: CallKind,
    /// Immediate receiver/qualifier identifier (`this`, a variable, a module seg).
    receiver: Option<String>,
}

#[derive(PartialEq)]
enum CallKind {
    /// `name(...)`.
    Bare,
    /// `recv.name(...)`.
    Method,
    /// `new T(...)`.
    New,
}

/// Resolution context for one enclosing function.
struct Ctx {
    scope_join: String,
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

    /// Ensure the `Package → mod::a → mod::a.b …` module chain exists.
    fn ensure_module(&mut self, segs: &[String]) -> String {
        let mut parent = self.pkg_id();
        let mut acc: Vec<String> = Vec::new();
        for seg in segs {
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

    /// Walk a statement/item container (`SourceFile`, `ItemBlock`), creating
    /// definition nodes and recursing into nested scopes. `owner` is the nearest
    /// enclosing aggregate (so its direct functions become methods).
    #[allow(clippy::too_many_arguments)]
    fn walk_items<'a>(
        &mut self,
        container: &'a Node,
        file_id: &str,
        scope: &[String],
        owner: Option<&Owner>,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_extends: &mut Vec<PendingExtends>,
    ) {
        for item in container.child_nodes() {
            match item.kind {
                cst::MODULE_DECL => {} // already handled at file entry
                cst::IMPORT_DECL => self.handle_import(item, file_id, src),
                cst::ATTR_BLOCK | cst::ACCESS_SPEC => {
                    if let Some(block) = item.child(cst::ITEM_BLOCK) {
                        self.walk_items(
                            block,
                            file_id,
                            scope,
                            owner,
                            src,
                            li,
                            pend_fns,
                            pend_extends,
                        );
                    }
                }
                cst::CLASS | cst::STRUCT | cst::INTERFACE | cst::UNION => {
                    self.handle_record(item, file_id, scope, src, li, pend_fns, pend_extends)
                }
                cst::TEMPLATE => {
                    self.handle_template(item, file_id, scope, src, li, pend_fns, pend_extends)
                }
                cst::ENUM => self.handle_enum(item, file_id, scope, src, li),
                cst::FUNCTION => self.handle_fn(item, file_id, scope, owner, src, li, pend_fns),
                cst::ALIAS => self.handle_alias(item, file_id, scope, src, li),
                cst::DECL => self.handle_decl(item, file_id, scope, src, li),
                _ => {}
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_fn<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        scope: &[String],
        owner: Option<&Owner>,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
    ) {
        let name = function_name(item, src);
        let line = li.line_col(name_span_start(item)).line;
        let scope_join = scope.join(".");
        let qual = qual_name(scope, &name);
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
        if let Some(o) = owner {
            props.push(("receiver_type", Json::str(o.name.clone())));
            props.push(("is_method", Json::Bool(true)));
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, name.clone(), props);
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);

        self.fn_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());
        self.fn_by_scope
            .entry((scope_join.clone(), name.clone()))
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
            item,
            scope_join,
            owner_type: owner.map(|o| o.name.clone()),
        });
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_record<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_extends: &mut Vec<PendingExtends>,
    ) {
        let name = match name_text(item, src) {
            Some(n) => n.to_string(),
            None => return, // anonymous aggregate: no nameable Type
        };
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(scope, &name);
        let id = format!("type::{qual}");
        let type_kind = match item.kind {
            cst::CLASS => "class",
            cst::INTERFACE => "interface",
            cst::UNION => "union",
            _ => "struct",
        };
        let is_interface = item.kind == cst::INTERFACE;
        let has_body = item.child(cst::ITEM_BLOCK).is_some();
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
                ("defined", Json::Bool(has_body)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());
        self.type_is_interface.insert(id.clone(), is_interface);

        // Only class/interface participate in inheritance in D.
        if matches!(item.kind, cst::CLASS | cst::INTERFACE) {
            for base in base_names(item, src) {
                pend_extends.push(PendingExtends {
                    type_id: id.clone(),
                    base_name: base,
                    sub_is_interface: is_interface,
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
            self.walk_items(
                block,
                file_id,
                &child_scope,
                Some(&owner),
                src,
                li,
                pend_fns,
                pend_extends,
            );
        }
    }

    /// `template Name(args) { items }` → a `Type` (`type_kind: template`); its
    /// body is walked as a nested scope.
    #[allow(clippy::too_many_arguments)]
    fn handle_template<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_extends: &mut Vec<PendingExtends>,
    ) {
        let name = match name_text(item, src) {
            Some(n) => n.to_string(),
            None => return,
        };
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(scope, &name);
        let id = format!("type::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str("template")),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str(LANG)),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());
        self.type_is_interface.insert(id.clone(), false);

        if let Some(block) = item.child(cst::ITEM_BLOCK) {
            let mut child_scope = scope.to_vec();
            child_scope.push(name);
            // A template is not an aggregate receiver, so no `owner`.
            self.walk_items(
                block,
                file_id,
                &child_scope,
                None,
                src,
                li,
                pend_fns,
                pend_extends,
            );
        }
    }

    fn handle_enum(
        &mut self,
        item: &Node,
        file_id: &str,
        scope: &[String],
        src: &str,
        li: &LineIndex,
    ) {
        let name_opt = name_text(item, src).map(|s| s.to_string());
        let body = item.child(cst::ENUM_BODY);
        let toks = top_level_tokens(item, src);
        let has_eq = toks.iter().any(|t| t.text == "=");

        // `enum NAME = value;` — a manifest constant, not a Type.
        if body.is_none() && has_eq {
            if let Some(name) = &name_opt {
                let line = li.line_col(name_span_start(item)).line;
                let qual = qual_name(scope, name);
                let id = format!("const::{qual}");
                self.g.upsert_node(
                    id.clone(),
                    ont::CONSTANT,
                    name.clone(),
                    vec![
                        ("binding", Json::str("manifest")),
                        ("language", Json::str(LANG)),
                        ("line", Json::U64(line as u64)),
                    ],
                );
                self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
            }
            return;
        }

        // A named enum is a Type; enumerators (named or anonymous) are Constants.
        let enum_qual = name_opt.as_ref().map(|n| qual_name(scope, n));
        if let (Some(name), Some(qual)) = (&name_opt, &enum_qual) {
            let line = li.line_col(name_span_start(item)).line;
            let id = format!("type::{qual}");
            self.g.upsert_node(
                id.clone(),
                ont::TYPE,
                name.clone(),
                vec![
                    ("type_kind", Json::str("enum")),
                    ("qualified_name", Json::str(qual.clone())),
                    ("language", Json::str(LANG)),
                    ("line", Json::U64(line as u64)),
                ],
            );
            self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
            self.type_by_name
                .entry(name.clone())
                .or_default()
                .push(id.clone());
            self.type_is_interface.insert(id, false);
        }

        if let Some(body) = body {
            let const_scope = match &enum_qual {
                Some(q) => q.clone(),
                None => scope.join("."),
            };
            for clause in split_commas(top_level_tokens(body, src)) {
                if let Some(first) = clause
                    .iter()
                    .find(|t| t.kind == tk::IDENT && !is_keyword(t.text))
                {
                    let cid = if const_scope.is_empty() {
                        format!("const::{}", first.text)
                    } else {
                        format!("const::{const_scope}::{}", first.text)
                    };
                    self.g.upsert_node(
                        cid.clone(),
                        ont::CONSTANT,
                        first.text.to_string(),
                        vec![
                            ("binding", Json::str("enumerator")),
                            ("language", Json::str(LANG)),
                            (
                                "enum",
                                Json::str(name_opt.clone().unwrap_or_else(|| "(anonymous)".into())),
                            ),
                        ],
                    );
                    self.g.add_edge(file_id, edge::DECLARES, cid, vec![]);
                }
            }
        }
    }

    /// `alias X = T;` or `alias T X;` → a `Type` alias. `alias this = member;`
    /// carries no new named type and is skipped (no fabrication).
    fn handle_alias(
        &mut self,
        item: &Node,
        file_id: &str,
        scope: &[String],
        src: &str,
        li: &LineIndex,
    ) {
        let toks = top_level_tokens(item, src);
        let name = if let Some(eq) = toks.iter().position(|t| t.text == "=") {
            // `alias NewName = Target;` — name is the ident just before `=`.
            match toks[..eq]
                .iter()
                .rev()
                .find(|t| t.kind == tk::IDENT && !is_keyword(t.text))
            {
                Some(t) => t.text.to_string(),
                None => return,
            }
        } else {
            // `alias Target NewName;` — name is the last top-level ident.
            match toks
                .iter()
                .rev()
                .find(|t| t.kind == tk::IDENT && !is_keyword(t.text))
            {
                Some(t) => t.text.to_string(),
                None => return,
            }
        };
        if name == "this" {
            return; // `alias this = ...;`
        }
        let line = li
            .line_col(
                toks.first()
                    .map(|t| t.span_start)
                    .unwrap_or(item.span.start),
            )
            .line;
        let qual = qual_name(scope, &name);
        let id = format!("type::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str("alias")),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str(LANG)),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name.entry(name).or_default().push(id.clone());
        self.type_is_interface.insert(id, false);
    }

    /// A `const`/`immutable` variable declaration → a `Constant`. Plain mutable
    /// variables are intentionally not lifted (conservative).
    fn handle_decl(
        &mut self,
        item: &Node,
        file_id: &str,
        scope: &[String],
        src: &str,
        li: &LineIndex,
    ) {
        let toks = top_level_tokens(item, src);
        let is_const = toks.iter().any(|t| matches!(t.text, "const" | "immutable"));
        if !is_const {
            return;
        }
        // Name: the last identifier before the first `=`, else the last identifier
        // before the `;` (skip type keywords).
        let cut = toks
            .iter()
            .position(|t| t.text == "=")
            .unwrap_or(toks.len());
        let name = match toks[..cut]
            .iter()
            .rev()
            .find(|t| t.kind == tk::IDENT && !is_keyword(t.text))
        {
            Some(t) => t.text.to_string(),
            None => return,
        };
        let line = li
            .line_col(
                toks.first()
                    .map(|t| t.span_start)
                    .unwrap_or(item.span.start),
            )
            .line;
        let qual = qual_name(scope, &name);
        let id = format!("const::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            name,
            vec![
                ("binding", Json::str("variable")),
                ("language", Json::str(LANG)),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
    }

    /// `import a.b, c.d : sym;` → an `IMPORTS` edge per imported module (to a
    /// project `File` when the module is declared in the batch, else an
    /// `ExternalDependency` + `DEPENDS_ON`).
    fn handle_import(&mut self, item: &Node, file_id: &str, src: &str) {
        let toks = top_level_tokens(item, src);
        for clause in split_commas(toks) {
            // Drop any selective-import tail (`: writeln, ...`).
            let head: Vec<Tok> = clause
                .iter()
                .take_while(|t| t.text != ":")
                .copied()
                .collect();
            // Renamed import `name = a.b.c`: keep the part after `=`.
            let body: Vec<Tok> = match head.iter().position(|t| t.text == "=") {
                Some(eq) => head[eq + 1..].to_vec(),
                None => head,
            };
            let module: String = body
                .iter()
                .filter(|t| t.kind == tk::IDENT && t.text != "import")
                .map(|t| t.text)
                .collect::<Vec<_>>()
                .join(".");
            if module.is_empty() {
                continue;
            }
            if let Some(target) = self.modules_by_name.get(&module).cloned() {
                if target != file_id {
                    self.g.add_edge(
                        file_id,
                        edge::IMPORTS,
                        target,
                        vec![
                            ("module", Json::str(module)),
                            ("external", Json::Bool(false)),
                        ],
                    );
                    continue;
                }
            }
            let dep = ext_id(&module);
            self.g.upsert_node(
                dep.clone(),
                ont::EXTERNAL_DEPENDENCY,
                module.clone(),
                vec![
                    ("external", Json::Bool(true)),
                    ("source", Json::str("import")),
                ],
            );
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                dep.clone(),
                vec![
                    ("module", Json::str(module)),
                    ("external", Json::Bool(true)),
                ],
            );
            self.g
                .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep, vec![]);
        }
    }

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        match call.kind {
            CallKind::New => {
                // `new T(...)` resolves to T's constructors when known.
                let c = self.methods_of(&call.name, "this");
                if c.is_empty() {
                    external()
                } else {
                    mk(c, "constructor")
                }
            }
            CallKind::Method => {
                if call.receiver.as_deref() == Some("this") {
                    if let Some(owner) = &ctx.owner_type {
                        let c = self.methods_of(owner, &call.name);
                        if !c.is_empty() {
                            return mk(c, "receiver");
                        }
                    }
                }
                if let Some(recv) = &call.receiver {
                    let c = self.methods_of(recv, &call.name);
                    if !c.is_empty() {
                        return mk(c, "member");
                    }
                }
                let c = self
                    .method_by_name
                    .get(&call.name)
                    .cloned()
                    .unwrap_or_default();
                if !c.is_empty() {
                    return mk(c, "global_method");
                }
                // Module-qualified free function (`std.math.sqrt(...)`).
                let c = self.global_fns(&call.name);
                if c.is_empty() {
                    external()
                } else {
                    mk(c, "global")
                }
            }
            CallKind::Bare => {
                let c = self.fns_in_scope(&ctx.scope_join, &call.name);
                if !c.is_empty() {
                    return mk(c, "local");
                }
                let c = self.global_fns(&call.name);
                if c.is_empty() {
                    external()
                } else {
                    mk(c, "global")
                }
            }
        }
    }

    fn emit_call(&mut self, caller_id: &str, call: &Call, res: Resolution) {
        let mut props = vec![
            ("callee", Json::str(call.name.clone())),
            ("method", Json::Bool(call.kind == CallKind::Method)),
            ("new", Json::Bool(call.kind == CallKind::New)),
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

    /// Emit the inheritance edge for a base link. The edge kind is decided by the
    /// resolved supertype's kind: an `interface` supertype is always reached via
    /// `IMPLEMENTS` from a class (and `EXTENDS` from another interface); a class
    /// supertype via `EXTENDS`. Unresolved supertypes default to `EXTENDS`.
    fn emit_extends(&mut self, pe: &PendingExtends) {
        let (target, super_is_interface) = match self.unique_type(&pe.base_name) {
            Some(id) => {
                let is_iface = self.type_is_interface.get(&id).copied().unwrap_or(false);
                (id, is_iface)
            }
            None => {
                let id = unresolved_id(&pe.base_name);
                if !self.g.has_node(&id) {
                    self.g.upsert_node(
                        id.clone(),
                        ont::UNRESOLVED,
                        pe.base_name.clone(),
                        vec![
                            ("unresolved", Json::Bool(true)),
                            ("role", Json::str("base_type")),
                        ],
                    );
                }
                (id, false)
            }
        };
        let edge_kind = if pe.sub_is_interface {
            edge::EXTENDS
        } else if super_is_interface {
            edge::IMPLEMENTS
        } else {
            edge::EXTENDS
        };
        self.g.add_edge(
            pe.type_id.clone(),
            edge_kind,
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

    fn fns_in_scope(&self, scope_join: &str, name: &str) -> Vec<String> {
        self.fn_by_scope
            .get(&(scope_join.to_string(), name.to_string()))
            .cloned()
            .unwrap_or_default()
    }

    fn global_fns(&self, name: &str) -> Vec<String> {
        self.fn_by_name.get(name).cloned().unwrap_or_default()
    }

    fn unique_type(&self, name: &str) -> Option<String> {
        match self.type_by_name.get(name) {
            Some(ids) if ids.len() == 1 => Some(ids[0].clone()),
            _ => None,
        }
    }

    /// Add `USES_TYPE` edges for identifiers anywhere in the function node (return
    /// type, parameters) — but not its body block — that name a unique project
    /// type.
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

// --- pure helpers -----------------------------------------------------------

fn qual_name(scope: &[String], name: &str) -> String {
    if scope.is_empty() {
        name.to_string()
    } else {
        format!("{}.{name}", scope.join("."))
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

fn name_text<'a>(item: &'a Node, src: &'a str) -> Option<&'a str> {
    let nm = item.child(cst::NAME)?;
    nm.tokens().next().map(|t| t.span.text(src))
}

fn name_span_start(item: &Node) -> u32 {
    item.child(cst::NAME)
        .map(|n| n.span.start)
        .unwrap_or(item.span.start)
}

/// A function's name: the `Name` child when present; otherwise `<anonymous>`. A
/// destructor (`~this`) keeps its tilde.
fn function_name(item: &Node, src: &str) -> String {
    if let Some(n) = name_text(item, src) {
        if has_tilde_before_name(item, src) {
            return format!("~{n}");
        }
        return n.to_string();
    }
    "<anonymous>".to_string()
}

/// True when a `~` token immediately precedes the function's `Name` node (a
/// destructor `~this`).
fn has_tilde_before_name(item: &Node, src: &str) -> bool {
    let mut prev_was_tilde = false;
    for ch in &item.children {
        match ch {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => prev_was_tilde = t.span.text(src) == "~",
            Child::Node(n) if n.kind == cst::NAME => return prev_was_tilde,
            Child::Node(_) => prev_was_tilde = false,
        }
    }
    false
}

/// Module-declaration name segments from the file's `ModuleDecl` (if any).
fn module_segments(root: &Node, src: &str) -> Option<Vec<String>> {
    let decl = root.children_of(cst::MODULE_DECL).next()?;
    let segs: Vec<String> = decl
        .tokens()
        .filter(|t| t.kind == tk::IDENT && t.span.text(src) != "module")
        .map(|t| t.span.text(src).to_string())
        .collect();
    if segs.is_empty() {
        None
    } else {
        Some(segs)
    }
}

/// Base / interface simple names from an aggregate's `Header` (`: A, B!T, ns.C`).
/// Per clause, ignoring any template-instantiation tail after `!`, the last
/// identifier is the base's simple name (so `B!T` yields `B`, `ns.C` yields `C`).
fn base_names(item: &Node, src: &str) -> Vec<String> {
    let header = match item.child(cst::HEADER) {
        Some(h) => h,
        None => return Vec::new(),
    };
    let mut bases = Vec::new();
    for clause in split_commas(top_level_tokens(header, src)) {
        let cut = clause
            .iter()
            .position(|t| t.text == "!")
            .unwrap_or(clause.len());
        if let Some(t) = clause[..cut]
            .iter()
            .rev()
            .find(|t| t.kind == tk::IDENT && !is_keyword(t.text))
        {
            bases.push(t.text.to_string());
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
/// into child nodes such as balanced groups or the `Name`/`Header` nodes).
fn top_level_tokens<'a>(node: &'a Node, src: &'a str) -> Vec<Tok<'a>> {
    node.tokens()
        .map(|t| Tok {
            text: t.span.text(src),
            kind: t.kind,
            span_start: t.span.start,
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

/// Collect identifier texts across the whole function node except its body block,
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
            Child::Node(n) if n.kind == cst::BLOCK => {} // skip the body
            Child::Node(n) => collect_type_idents(n, src, out),
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
                ident: t.kind == tk::IDENT && !is_keyword(t.span.text(src)),
            }),
            Child::Node(n) => v.push(El::Grp(n)),
        }
    }
    v
}

/// Detect `name(...)`, `recv.name(...)`, and `new T(...)` call sites over the
/// real token tree, recursing into nested groups. Definitions nested in a body
/// are token groups (`Brace`), still scanned for calls.
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        // `new T(...)` — `new` is a keyword (so not an ident element).
        if tok_text(&els[i]) == Some("new") && i + 2 < n && is_ident_el(&els[i + 1]) {
            if let Some(g) = grp(&els[i + 2]) {
                if g.kind == cst::PAREN {
                    out.push(Call {
                        name: tok_text(&els[i + 1]).unwrap_or("").to_string(),
                        kind: CallKind::New,
                        receiver: None,
                    });
                    i += 3;
                    continue;
                }
            }
        }
        // Member call: `.` name `(...)`.
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
                            kind: CallKind::Method,
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
        // Bare call: name `(...)`, not preceded by a `.` connector.
        if is_ident_el(&els[i]) {
            let prev = if i > 0 { tok_text(&els[i - 1]) } else { None };
            let connector = matches!(prev, Some("."));
            if !connector && i + 1 < n {
                if let Some(g) = grp(&els[i + 1]) {
                    if g.kind == cst::PAREN {
                        out.push(Call {
                            name: tok_text(&els[i]).unwrap_or("").to_string(),
                            kind: CallKind::Bare,
                            receiver: None,
                        });
                    }
                }
            }
        }
        i += 1;
    }
    // Recurse into every group (parameter defaults, nested blocks, …).
    for e in &els {
        if let Some(g) = grp(e) {
            scan_calls(g, src, out);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::d::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("u.d", src);
        let file = SourceFile {
            rel_path: "u.d".to_string(),
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
    fn emits_function_type_nodes() {
        let g = graph_for("class C {\n  void m() {}\n}\nint f() { return 0; }\n");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "f + C.m");
        assert_eq!(g.count_nodes_of(ont::TYPE), 1, "class C is a Type");
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD), "C has m");
    }

    #[test]
    fn struct_type_kind() {
        let g = graph_for("struct S { int x; }\n");
        let ty = g.nodes().find(|n| n.kind == ont::TYPE).expect("a Type");
        assert_eq!(ty.props.get("type_kind"), Some(&Json::str("struct")));
        assert_eq!(ty.props.get("language"), Some(&Json::str("d")));
    }

    #[test]
    fn resolves_unique_local_call() {
        let g =
            graph_for("int add(int a, int b) { return a + b; }\nint run() { return add(1, 2); }\n");
        let calls = call_edges(&g);
        let add = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("add")))
            .expect("a call to add");
        assert!(add.to.starts_with("fn::add"));
        assert_eq!(add.props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for("int run() { return mystery(); }\n");
        let calls = call_edges(&g);
        assert!(calls
            .iter()
            .any(|e| e.props.get("resolution") == Some(&Json::str("external"))));
        assert!(g.has_node("unresolved::mystery"));
    }

    #[test]
    fn new_resolves_to_constructor() {
        let g = graph_for(
            "class Widget {\n  this(int n) {}\n}\nvoid make() { auto w = new Widget(3); }\n",
        );
        let calls = call_edges(&g);
        let nw = calls
            .iter()
            .find(|e| e.props.get("new") == Some(&Json::Bool(true)))
            .expect("a new-expression call");
        assert_eq!(nw.props.get("resolution"), Some(&Json::str("constructor")));
        assert_eq!(nw.props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn import_creates_dependency() {
        let g = graph_for("import std.stdio;\nvoid main() {}\n");
        assert!(g.has_node("ext::std.stdio"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::std.stdio"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn selective_and_renamed_import() {
        let g = graph_for("import std.stdio : writeln;\nimport io = std.file;\n");
        assert!(g.has_node("ext::std.stdio"));
        assert!(g.has_node("ext::std.file"));
    }

    #[test]
    fn class_extends_class() {
        let g = graph_for("class Base {}\nclass Derived : Base {}\n");
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an EXTENDS edge");
        assert!(ext.from.starts_with("type::Derived"));
        assert!(ext.to.starts_with("type::Base"));
    }

    #[test]
    fn class_implements_interface() {
        let g = graph_for("interface I { void f(); }\nclass C : I { void f() {} }\n");
        assert!(
            g.edges()
                .any(|e| e.kind == edge::IMPLEMENTS && e.to.starts_with("type::I")),
            "class implementing an interface should be IMPLEMENTS"
        );
    }

    #[test]
    fn interface_extends_interface() {
        let g = graph_for("interface A {}\ninterface B : A {}\n");
        assert!(
            g.edges()
                .any(|e| e.kind == edge::EXTENDS && e.from.starts_with("type::B")),
            "an interface extending an interface should be EXTENDS"
        );
    }

    #[test]
    fn immutable_is_constant() {
        let g = graph_for("immutable int K = 42;\nint v = 1;\n");
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 1);
        let c = g.nodes().find(|n| n.kind == ont::CONSTANT).expect("const");
        assert_eq!(c.name, "K");
    }

    #[test]
    fn manifest_enum_is_constant() {
        let g = graph_for("enum PI = 3.14;\n");
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 1);
        assert_eq!(
            g.count_nodes_of(ont::TYPE),
            0,
            "a manifest enum is not a Type"
        );
        let c = g.nodes().find(|n| n.kind == ont::CONSTANT).expect("const");
        assert_eq!(c.props.get("binding"), Some(&Json::str("manifest")));
    }

    #[test]
    fn enum_enumerators_are_constants() {
        let g = graph_for("enum Color : int { Red, Green, Blue }\n");
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 3);
        let ty = g.nodes().find(|n| n.kind == ont::TYPE).expect("enum type");
        assert_eq!(ty.props.get("type_kind"), Some(&Json::str("enum")));
    }

    #[test]
    fn module_is_module_chain() {
        let g = graph_for("module a.b;\nint f() { return 0; }\n");
        assert!(g.has_node("mod::a"));
        assert!(g.has_node("mod::a.b"));
        let f = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION)
            .expect("function");
        assert_eq!(f.props.get("qualified_name"), Some(&Json::str("a.b.f")));
    }

    #[test]
    fn template_is_type() {
        let g = graph_for("template Stack(T) {\n  T[] data;\n  void push(T x) {}\n}\n");
        let ty = g
            .nodes()
            .find(|n| n.kind == ont::TYPE && n.name == "Stack")
            .expect("Stack template");
        assert_eq!(ty.props.get("type_kind"), Some(&Json::str("template")));
    }

    #[test]
    fn alias_is_type() {
        let g = graph_for("alias Real = double;\nalias int MyInt;\n");
        let aliases = g
            .nodes()
            .filter(|n| {
                n.kind == ont::TYPE && n.props.get("type_kind") == Some(&Json::str("alias"))
            })
            .count();
        assert_eq!(aliases, 2);
    }

    #[test]
    fn output_is_deterministic() {
        let src = "module m;\nimport std.stdio;\nclass B {}\nclass D : B { void m() { helper(); } }\nvoid helper() {}\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
