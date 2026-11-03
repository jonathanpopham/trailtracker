//! Lower the PHP CST into the canonical graph.
//!
//! This mirrors the Python lowering ([`crate::lang::python::lower`]) — same
//! conservative principles, same shared ontology — adapted to PHP's surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to
//!    a concrete project definition only when a scope level yields exactly one
//!    candidate; several candidates are emitted as an ambiguous edge carrying the
//!    full `candidates` set; none resolves to an explicit external/unresolved
//!    node. The airgapped runtime has no LLM to guess.
//! 2. **Everything comes from real tokens.** Calls, base classes, imports, and
//!    type uses are read off the lossless tree, never invented.
//!
//! Resolution uses a deterministic **scope ladder** (most specific first; the
//! first level with any candidate decides): receiver (`$this`/`self`/`static`/a
//! known class) → local namespace → file imports → global. Each edge records
//! which level resolved it, so the call graph stays auditable.
//!
//! Honest mappings (see the IR Atlas):
//!   `function` → `Function` (a method → `HAS_METHOD` from its enclosing type),
//!   `class`/`interface`/`trait`/`enum` → `Type` (with the matching `type_kind`),
//!   `const` / `define(...)` → `Constant`,
//!   `class C extends B` / `interface I extends J` → `EXTENDS`,
//!   `class C implements I` → `IMPLEMENTS`,
//!   `use X\Y` → `IMPORTS` (plus `ExternalDependency`/`DEPENDS_ON` for non-project
//!   roots), `require`/`include` → `IMPORTS` to an `UnresolvedSymbol` (the file
//!   target is not resolvable in-graph without runtime path math).
//!
//! Honest non-mappings: a PHP **trait** is a mixin, not an interface contract, so
//! `use Trait;` inside a class is recorded as `USES_TYPE` (`role: trait`) rather
//! than overstated as `IMPLEMENTS`; `enum` **cases** are left in the lossless tree
//! but not given a dedicated node (no apt ontology kind yet — a candidate IR
//! extension, not something to force-fit).

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::php::lexer::{is_keyword, kind as tk};
use crate::lang::php::parser::node as cst;

/// Lower a whole project's worth of PHP files into a graph. `manifest_deps` is
/// unused for PHP (the pipeline's manifest reader is Cargo-only); dependencies
/// are discovered from `use` / `require` statements instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    // Project-local namespace roots: the package plus the first segment of every
    // declared namespace. A `use` whose root is one of these is an intra-project
    // import, not an external (vendor) dependency. Conservative: prefer
    // under-reporting externals to fabricating one for code we actually own.
    let mut local_roots: BTreeSet<String> = BTreeSet::new();
    local_roots.insert(package.to_string());
    for f in files {
        collect_namespace_roots(f.root, f.source, &mut local_roots);
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
        vec![("ecosystem", Json::str("php"))],
    );

    // Pass B: create definition nodes + structural edges, build symbol tables and
    // per-file import maps. Inheritance/type-use is deferred to pass C so a target
    // defined later in the project still resolves.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_rels: Vec<PendingRel> = Vec::new();
    for (idx, f) in files.iter().enumerate() {
        lo.imports.push(BTreeMap::new());
        lo.cur_file = idx;
        let li = LineIndex::new(f.source);
        let file_id = format!("file::{}", f.rel_path);
        lo.g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("php")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(lo.pkg_id(), edge::CONTAINS, file_id.clone(), vec![]);
        lo.walk_stmts(
            f.root,
            &file_id,
            "",
            &[],
            None,
            false,
            f.source,
            &li,
            &mut pend_fns,
            &mut pend_rels,
        );
    }

    // Pass C: resolve calls (scope ladder), type usages, and inheritance against
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
            let mut type_names = Vec::new();
            scan_new_instantiations(block, pf.source, &mut type_names);
            lo.emit_type_use_names(&pf.id, &type_names);
        }
        if let Some(sig) = pf.signature {
            lo.emit_type_uses(&pf.id, sig, pf.source);
        }
    }
    for pr in &pend_rels {
        lo.emit_rel(pr);
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
    /// (module_join, name) → function ids (local-namespace level).
    fn_by_module: BTreeMap<(String, String), Vec<String>>,
    /// (type_name, method_name) → method ids (receiver level).
    method_by_type: BTreeMap<(String, String), Vec<String>>,
    /// Simple name → type (class/interface/trait/enum) node ids.
    type_by_name: BTreeMap<String, Vec<String>>,
    /// Per-file import maps: imported leaf name → full namespace-path segments.
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

/// A deferred type-to-type relationship (`extends`/`implements`/trait `use`),
/// resolved in pass C once every type is known.
struct PendingRel {
    type_id: String,
    target_name: String,
    edge_kind: &'static str,
    role: &'static str,
}

/// The enclosing type while walking, for methods (`HAS_METHOD`, receiver scope).
struct Owner {
    name: String,
    id: String,
}

/// A detected call site over the lossless tree.
struct Call {
    /// The called name (final member or bare name).
    name: String,
    kind: CallKind,
    /// Immediate receiver text (`$this`, `self`, a class name, a variable).
    receiver: Option<String>,
}

#[derive(PartialEq)]
enum CallKind {
    /// `name(...)`.
    Bare,
    /// `$recv->name(...)` / `$recv?->name(...)`.
    Instance,
    /// `Recv::name(...)`.
    Static,
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

    /// Ensure the `Package → mod::A → mod::A\B …` chain exists and return the leaf
    /// module id (or the package id for the global namespace).
    fn ensure_modules(&mut self, module_join: &str) -> String {
        let pkg = self.pkg_id();
        if module_join.is_empty() {
            return pkg;
        }
        let mut parent = pkg;
        let mut acc: Vec<String> = Vec::new();
        for seg in module_join.split('\\') {
            acc.push(seg.to_string());
            let id = format!("mod::{}", acc.join("\\"));
            self.g.upsert_node(
                id.clone(),
                ont::MODULE,
                seg.to_string(),
                vec![("language", Json::str("php"))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    /// Walk a statement container (a `SourceFile`, `Block`, or namespace block),
    /// creating definition nodes and recursing into nested scopes. `module_join`
    /// is the namespace in effect (updated by semicolon-form `namespace` siblings);
    /// `owner` is the nearest enclosing type (cleared when descending into a
    /// function); `in_function` gates `Constant` emission for `const`.
    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::only_used_in_recursion)]
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
        let mut cur_module = module_join.to_string();
        for item in container.child_nodes() {
            match item.kind {
                cst::NAMESPACE => {
                    let ns = namespace_path(item, src);
                    // A declared namespace is a Module regardless of whether any
                    // definition later references it.
                    if !ns.is_empty() {
                        self.ensure_modules(&ns);
                    }
                    if let Some(block) = item.child(cst::BLOCK) {
                        // Block-form namespace: scoped to its braces.
                        self.walk_stmts(
                            block,
                            file_id,
                            &ns,
                            &[],
                            None,
                            false,
                            src,
                            li,
                            pend_fns,
                            pend_rels,
                        );
                    } else {
                        // Statement-form namespace: applies to following siblings.
                        cur_module = ns;
                    }
                }
                cst::FUNCTION => self.handle_fn(
                    item,
                    file_id,
                    &cur_module,
                    scope,
                    owner,
                    src,
                    li,
                    pend_fns,
                    pend_rels,
                ),
                cst::CLASS | cst::INTERFACE | cst::TRAIT | cst::ENUM => self.handle_type(
                    item,
                    file_id,
                    &cur_module,
                    scope,
                    src,
                    li,
                    pend_fns,
                    pend_rels,
                ),
                cst::COMPOUND => {
                    // A control structure (if/for/while/…) is not a new scope:
                    // definitions inside still belong to the enclosing scope.
                    if let Some(block) = item.child(cst::BLOCK) {
                        self.walk_stmts(
                            block,
                            file_id,
                            &cur_module,
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
                cst::USE => self.handle_use(item, file_id, src, owner, pend_rels),
                cst::REQUIRE => self.handle_require(item, file_id, src),
                cst::CONST => self.handle_const(item, file_id, &cur_module, owner, src, li),
                cst::SIMPLE_STMT => {
                    // `define('NAME', …)` is a runtime constant declaration.
                    self.handle_define(item, file_id, src, li);
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
        pend_rels: &mut Vec<PendingRel>,
    ) {
        let name = name_text(item, src).unwrap_or("<anonymous>").to_string();
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(module_join, scope, &name);
        let id = format!("fn::{qual}#{line}");
        let block = item.child(cst::BLOCK);
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("php")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            ("has_body", Json::Bool(block.is_some())),
        ];
        if let Some(o) = owner {
            props.push(("receiver_type", Json::str(o.name.clone())));
            props.push(("is_method", Json::Bool(true)));
        }
        if has_modifier(item, src, "abstract") {
            props.push(("is_abstract", Json::Bool(true)));
        }
        if has_modifier(item, src, "static") {
            props.push(("is_static", Json::Bool(true)));
        }
        if let Some(v) = visibility(item, src) {
            props.push(("visibility", Json::str(v)));
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

        // Nested defs are not methods of an enclosing type: descend with a fresh
        // (None) owner and an extended scope path.
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
        let id = format!("type::{qual}");
        let type_kind = type_kind_of(item.kind);
        let mut props = vec![
            ("type_kind", Json::str(type_kind)),
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("php")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
        ];
        if has_modifier(item, src, "abstract") {
            props.push(("is_abstract", Json::Bool(true)));
        }
        if has_modifier(item, src, "final") {
            props.push(("is_final", Json::Bool(true)));
        }
        self.g
            .upsert_node(id.clone(), ont::TYPE, name.clone(), props);
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());

        // `extends` / `implements` clauses (resolve in pass C).
        let (extends, implements) = class_relations(item, src);
        // An interface `extends` is interface inheritance → EXTENDS (possibly many);
        // a class `extends` is single inheritance → EXTENDS; `implements` → IMPLEMENTS.
        for base in extends {
            pend_rels.push(PendingRel {
                type_id: id.clone(),
                target_name: base,
                edge_kind: edge::EXTENDS,
                role: "extends",
            });
        }
        for iface in implements {
            pend_rels.push(PendingRel {
                type_id: id.clone(),
                target_name: iface,
                edge_kind: edge::IMPLEMENTS,
                role: "interface",
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

    /// `use A\B\C [as D];`, `use function …`, grouped `use A\{B, C};`, or — inside
    /// a class body — a trait `use Trait;`. Trait uses become deferred `USES_TYPE`
    /// relations; namespace imports become `IMPORTS` edges + the resolution map.
    fn handle_use(
        &mut self,
        item: &Node,
        file_id: &str,
        src: &str,
        owner: Option<&Owner>,
        pend_rels: &mut Vec<PendingRel>,
    ) {
        if let Some(o) = owner {
            // In-class `use Trait1, Trait2;` — composition, recorded as USES_TYPE.
            for clause in split_commas(top_level_tokens(item, src)) {
                if let Some(last) = clause
                    .iter()
                    .rev()
                    .find(|t| t.kind == tk::NAME && !is_keyword(t.text))
                {
                    pend_rels.push(PendingRel {
                        type_id: o.id.clone(),
                        target_name: last.text.to_string(),
                        edge_kind: edge::USES_TYPE,
                        role: "trait",
                    });
                }
            }
            return;
        }

        let toks = top_level_tokens(item, src);
        // Drop the `use` keyword and an optional `function`/`const` import kind.
        let body = strip_leading_kw(&toks, &["use"]);
        let body = strip_leading_kw(body, &["function", "const"]);

        if let Some(group) = item.child(cst::BRACE) {
            // Grouped use: `use Prefix\{A, B as C};`.
            let (prefix, _) = dotted_path_and_alias(body);
            for clause in split_commas(top_level_tokens(group, src)) {
                let clause = strip_leading_kw(&clause, &["function", "const"]);
                let (segs, alias) = dotted_path_and_alias(clause);
                if segs.is_empty() {
                    continue;
                }
                let mut full = prefix.clone();
                full.extend(segs.clone());
                let leaf = alias.unwrap_or_else(|| segs.last().cloned().unwrap());
                self.imports[self.cur_file].insert(leaf, full.clone());
                self.emit_import_edge(file_id, &full);
            }
        } else {
            let (segs, alias) = dotted_path_and_alias(body);
            if segs.is_empty() {
                return;
            }
            let leaf = alias.unwrap_or_else(|| segs.last().cloned().unwrap());
            self.imports[self.cur_file].insert(leaf, segs.clone());
            self.emit_import_edge(file_id, &segs);
        }
    }

    /// Emit the `IMPORTS` edge for one imported namespace path, plus the
    /// `ExternalDependency`/`DEPENDS_ON` pair when the root is not project-local.
    fn emit_import_edge(&mut self, file_id: &str, segs: &[String]) {
        let root = match segs.first() {
            Some(r) => r.clone(),
            None => return,
        };
        let path_text = segs.join("\\");
        if self.local_roots.contains(&root) {
            let id = format!("mod::{root}");
            self.g.upsert_node(
                id.clone(),
                ont::MODULE,
                root.clone(),
                vec![("language", Json::str("php"))],
            );
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                id,
                vec![
                    ("path", Json::str(path_text)),
                    ("external", Json::Bool(false)),
                ],
            );
        } else {
            let dep_id = ext_id(&root);
            self.g.upsert_node(
                dep_id.clone(),
                ont::EXTERNAL_DEPENDENCY,
                root,
                vec![("external", Json::Bool(true)), ("source", Json::str("use"))],
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

    /// `require|include 'path';` — a dependency on another file we cannot resolve
    /// to a concrete node without runtime path math, so the target is an explicit
    /// `UnresolvedSymbol` (role `include`). Only a literal-string operand is used.
    fn handle_require(&mut self, item: &Node, file_id: &str, src: &str) {
        let toks = top_level_tokens(item, src);
        let kw = toks.first().map(|t| t.text.to_string()).unwrap_or_default();
        let lit = toks.iter().find(|t| t.kind == tk::STRING);
        let path_text = lit
            .map(|t| string_inner(t.text).to_string())
            .unwrap_or_default();
        if path_text.is_empty() {
            return; // dynamic include (`require $x`) — nothing nameable, never guessed
        }
        let target = format!("include::{path_text}");
        if !self.g.has_node(&target) {
            self.g.upsert_node(
                target.clone(),
                ont::UNRESOLVED,
                path_text.clone(),
                vec![
                    ("unresolved", Json::Bool(true)),
                    ("role", Json::str("include")),
                ],
            );
        }
        self.g.add_edge(
            file_id,
            edge::IMPORTS,
            target,
            vec![
                ("path", Json::str(path_text)),
                ("include", Json::Bool(true)),
                ("directive", Json::str(kw)),
            ],
        );
    }

    /// `const NAME = expr [, NAME2 = expr2];` — at file/namespace level the scope
    /// is the file; inside a type the type declares it.
    fn handle_const(
        &mut self,
        item: &Node,
        file_id: &str,
        module_join: &str,
        owner: Option<&Owner>,
        src: &str,
        li: &LineIndex,
    ) {
        for clause in split_commas(top_level_tokens(item, src)) {
            // First NAME token of the clause is the constant's name.
            let nm = match clause
                .iter()
                .find(|t| t.kind == tk::NAME && !is_keyword(t.text))
            {
                Some(t) => t,
                None => continue,
            };
            let name = nm.text.to_string();
            let line = li.line_col(nm.span_start).line;
            let scope_owner = owner.map(|o| o.name.as_str()).unwrap_or("");
            let qual = qual_name(module_join, &[], &name);
            let qual = if scope_owner.is_empty() {
                qual
            } else {
                format!("{scope_owner}::{name}")
            };
            let id = format!("const::{qual}");
            self.g.upsert_node(
                id.clone(),
                ont::CONSTANT,
                name,
                vec![
                    (
                        "binding",
                        Json::str(if owner.is_some() {
                            "class_const"
                        } else {
                            "const"
                        }),
                    ),
                    ("language", Json::str("php")),
                    ("line", Json::U64(line as u64)),
                ],
            );
            let scope_id = owner
                .map(|o| o.id.clone())
                .unwrap_or_else(|| file_id.to_string());
            self.g.add_edge(scope_id, edge::DECLARES, id, vec![]);
        }
    }

    /// `define('NAME', value)` — a global runtime constant. Only a leading
    /// `define(` with a string-literal first argument is recognized; never guessed.
    fn handle_define(&mut self, item: &Node, file_id: &str, src: &str, li: &LineIndex) {
        // The statement is `define ( "NAME" , ... ) ;` — a NAME token followed by a
        // PAREN group whose first string literal is the constant name.
        let mut name_tok = None;
        for c in &item.children {
            match c {
                Child::Token(t) if t.trivia => continue,
                Child::Token(t) => {
                    name_tok = Some(t);
                    break;
                }
                // First significant element is a group/node, not `define`.
                Child::Node(_) => return,
            }
        }
        let nt = match name_tok {
            Some(t) if t.span.text(src).eq_ignore_ascii_case("define") => t,
            _ => return,
        };
        let paren = match item.child(cst::PAREN) {
            Some(p) => p,
            None => return,
        };
        let lit = match paren.tokens().find(|t| t.kind == tk::STRING) {
            Some(t) => t,
            None => return,
        };
        let name = string_inner(lit.span.text(src)).to_string();
        if name.is_empty() {
            return;
        }
        let line = li.line_col(nt.span.start).line;
        let id = format!("const::{name}");
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            name,
            vec![
                ("binding", Json::str("define")),
                ("language", Json::str("php")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
    }

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        match call.kind {
            CallKind::Static => {
                match call.receiver.as_deref() {
                    Some("self") | Some("static") => {
                        if let Some(owner) = &ctx.owner_type {
                            let c = self.methods_of(owner, &call.name);
                            if !c.is_empty() {
                                return mk(c, "receiver");
                            }
                        }
                    }
                    Some("parent") => {} // unknown parent type: fall through to global
                    Some(cls) => {
                        let simple = last_segment(cls);
                        let c = self.methods_of(&simple, &call.name);
                        if !c.is_empty() {
                            return mk(c, "static_class");
                        }
                    }
                    None => {}
                }
                let c = self.global_methods(&call.name);
                if c.is_empty() {
                    Resolution {
                        outcome: Outcome::None,
                        level: "external",
                    }
                } else {
                    mk(c, "global_method")
                }
            }
            CallKind::Instance => {
                if call.receiver.as_deref() == Some("$this") {
                    if let Some(owner) = &ctx.owner_type {
                        let c = self.methods_of(owner, &call.name);
                        if !c.is_empty() {
                            return mk(c, "receiver");
                        }
                    }
                }
                let c = self.global_methods(&call.name);
                if c.is_empty() {
                    Resolution {
                        outcome: Outcome::None,
                        level: "external",
                    }
                } else {
                    mk(c, "global_method")
                }
            }
            CallKind::Bare => {
                // Local namespace.
                let c = self.fns_in_module(&ctx.module_join, &call.name);
                if !c.is_empty() {
                    return mk(c, "local");
                }
                // File imports: a name brought in via `use Ns\name;`.
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
        }
    }

    fn emit_call(&mut self, caller_id: &str, call: &Call, res: Resolution) {
        let mut props = vec![
            ("callee", Json::str(call.name.clone())),
            ("call_kind", Json::str(call_kind_str(&call.kind))),
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

    /// Resolve a deferred type-to-type relation (`extends`/`implements`/trait
    /// `use`) into a concrete edge pointing at the project type when unique,
    /// otherwise an explicit `UnresolvedSymbol` (a vendor/stdlib type we cannot see
    /// in an airgap).
    fn emit_rel(&mut self, pr: &PendingRel) {
        let simple = last_segment(&pr.target_name);
        let target = match self.unique_type(&simple) {
            Some(id) => id,
            None => {
                let id = unresolved_id(&simple);
                self.ensure_unresolved(&id, &simple, pr.role);
                id
            }
        };
        self.g.add_edge(
            pr.type_id.clone(),
            pr.edge_kind,
            target,
            vec![
                ("target_name", Json::str(pr.target_name.clone())),
                ("role", Json::str(pr.role)),
            ],
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

    /// Namespace-join for an imported symbol's defining namespace (`segs` includes
    /// the leaf name). `None` when the import points outside the project.
    fn import_module_join(&self, segs: &[String]) -> Option<String> {
        if segs.len() < 2 {
            return None;
        }
        let ns = &segs[..segs.len() - 1];
        if self.local_roots.contains(&ns[0]) {
            Some(ns.join("\\"))
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

    /// Add `USES_TYPE` edges for identifiers in `region` (a function `Header`, i.e.
    /// parameter/return type annotations) that name a unique project type.
    fn emit_type_uses(&mut self, from_id: &str, region: &Node, src: &str) {
        let mut seen: Vec<String> = Vec::new();
        for n in region.walk() {
            for t in n.tokens() {
                if t.kind != tk::NAME {
                    continue;
                }
                let name = t.span.text(src);
                self.add_type_use(from_id, name, &mut seen);
            }
        }
    }

    /// Add `USES_TYPE` edges for a set of simple type names (e.g. from `new X`).
    fn emit_type_use_names(&mut self, from_id: &str, names: &[String]) {
        let mut seen: Vec<String> = Vec::new();
        for name in names {
            self.add_type_use(from_id, name, &mut seen);
        }
    }

    fn add_type_use(&mut self, from_id: &str, name: &str, seen: &mut Vec<String>) {
        let simple = last_segment(name);
        if let Some(type_id) = self.unique_type(&simple) {
            if type_id != from_id && !seen.contains(&type_id) {
                seen.push(type_id.clone());
                self.g.add_edge(
                    from_id,
                    edge::USES_TYPE,
                    type_id,
                    vec![("type_name", Json::str(simple))],
                );
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

fn type_kind_of(node_kind: &str) -> &'static str {
    match node_kind {
        cst::CLASS => "class",
        cst::INTERFACE => "interface",
        cst::TRAIT => "trait",
        cst::ENUM => "enum",
        _ => "class",
    }
}

fn call_kind_str(k: &CallKind) -> &'static str {
    match k {
        CallKind::Bare => "function",
        CallKind::Instance => "instance",
        CallKind::Static => "static",
    }
}

/// Dotted namespace-join: `["App","Models"]` → `"App\Models"`.
fn qual_name(module_join: &str, scope: &[String], name: &str) -> String {
    let mut parts: Vec<String> = Vec::new();
    if !module_join.is_empty() {
        parts.push(module_join.to_string());
    }
    parts.extend(scope.iter().cloned());
    parts.push(name.to_string());
    parts.join("\\")
}

/// Final segment of a possibly-qualified PHP name (`A\B\C` → `C`).
fn last_segment(name: &str) -> String {
    name.rsplit('\\').next().unwrap_or(name).to_string()
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

/// Strip the surrounding quotes of a PHP string literal token, if present.
fn string_inner(lit: &str) -> &str {
    let bytes = lit.as_bytes();
    if bytes.len() >= 2 {
        let first = bytes[0];
        let last = bytes[bytes.len() - 1];
        if (first == b'\'' || first == b'"' || first == b'`') && last == first {
            return &lit[1..lit.len() - 1];
        }
    }
    lit
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

/// True if a definition node carries `modifier` as a direct keyword token (e.g.
/// `abstract`, `final`, `static`).
fn has_modifier(item: &Node, src: &str, modifier: &str) -> bool {
    for t in item.tokens() {
        let text = t.span.text(src);
        if text.eq_ignore_ascii_case(modifier) {
            return true;
        }
        // Stop at the def keyword / name so we only inspect leading modifiers.
        if matches!(
            text.to_ascii_lowercase().as_str(),
            "function" | "class" | "interface" | "trait" | "enum"
        ) {
            return false;
        }
    }
    false
}

fn visibility(item: &Node, src: &str) -> Option<&'static str> {
    for t in item.tokens() {
        match t.span.text(src).to_ascii_lowercase().as_str() {
            "public" => return Some("public"),
            "private" => return Some("private"),
            "protected" => return Some("protected"),
            "function" => return None,
            _ => {}
        }
    }
    None
}

/// The namespace path declared by a `Namespace` node (`["App","Models"]`).
fn namespace_path(item: &Node, src: &str) -> String {
    let header = match item.child(cst::HEADER) {
        Some(h) => h,
        None => return String::new(),
    };
    let segs: Vec<&str> = header
        .tokens()
        .filter(|t| t.kind == tk::NAME)
        .map(|t| t.span.text(src))
        .collect();
    segs.join("\\")
}

/// Pre-scan: collect the first segment of every declared namespace as a
/// project-local root. Walks the whole tree (namespaces may be block-form).
fn collect_namespace_roots(root: &Node, src: &str, out: &mut BTreeSet<String>) {
    for n in root.walk() {
        if n.kind == cst::NAMESPACE {
            let ns = namespace_path(n, src);
            if let Some(first) = ns.split('\\').next() {
                if !first.is_empty() {
                    out.insert(first.to_string());
                }
            }
        }
    }
}

/// `extends` and `implements` target names from a class-like header. Returns
/// (extends_names, implements_names), each the final identifier of a clause.
fn class_relations(item: &Node, src: &str) -> (Vec<String>, Vec<String>) {
    let header = match item.child(cst::HEADER) {
        Some(h) => h,
        None => return (Vec::new(), Vec::new()),
    };
    let toks = top_level_tokens(header, src);
    let mut extends = Vec::new();
    let mut implements = Vec::new();
    // Walk tokens, tracking which clause keyword we are under. Each comma-separated
    // target contributes its final identifier (`A\B` → `B`); a comma or a clause
    // keyword flushes the pending target.
    let mut section: Option<&str> = None;
    let mut last_name: Option<&str> = None;
    for t in &toks {
        let low = t.text.to_ascii_lowercase();
        match low.as_str() {
            "extends" => {
                push_target(section, last_name, &mut extends, &mut implements);
                last_name = None;
                section = Some("extends");
            }
            "implements" => {
                push_target(section, last_name, &mut extends, &mut implements);
                last_name = None;
                section = Some("implements");
            }
            "," => {
                push_target(section, last_name, &mut extends, &mut implements);
                last_name = None;
            }
            _ if t.kind == tk::NAME => last_name = Some(t.text),
            _ => {}
        }
    }
    push_target(section, last_name, &mut extends, &mut implements);
    (extends, implements)
}

/// Append `name` to the `extends` or `implements` list according to the active
/// clause `section`. A no-op when there is no pending name or no active section.
fn push_target(
    section: Option<&str>,
    name: Option<&str>,
    ext: &mut Vec<String>,
    imp: &mut Vec<String>,
) {
    if let Some(n) = name {
        match section {
            Some("extends") => ext.push(n.to_string()),
            Some("implements") => imp.push(n.to_string()),
            _ => {}
        }
    }
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
        .map(|t| Tok {
            text: t.span.text(src),
            kind: t.kind,
            span_start: t.span.start,
        })
        .collect()
}

/// Drop a single leading keyword token if it matches one of `kws` (case-insensitive).
fn strip_leading_kw<'a, 'b>(toks: &'b [Tok<'a>], kws: &[&str]) -> &'b [Tok<'a>] {
    match toks.split_first() {
        Some((first, rest)) if kws.iter().any(|k| first.text.eq_ignore_ascii_case(k)) => rest,
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

/// Read a `\`-separated path (`A \ B \ C`) and an optional `as` alias from one
/// clause, returning the path segments and the alias if present.
fn dotted_path_and_alias(clause: &[Tok<'_>]) -> (Vec<String>, Option<String>) {
    let mut segs = Vec::new();
    let mut alias = None;
    let mut expect_alias = false;
    for t in clause {
        if expect_alias {
            if t.kind == tk::NAME {
                alias = Some(t.text.to_string());
                expect_alias = false;
            }
            continue;
        }
        if t.text.eq_ignore_ascii_case("as") {
            expect_alias = true;
        } else if t.kind == tk::NAME {
            segs.push(t.text.to_string());
        }
    }
    (segs, alias)
}

// --- call detection over the lossless token tree ----------------------------

enum El<'a> {
    Tok { text: &'a str, kind: &'static str },
    Grp(&'a Node),
}

fn tok_text<'a>(e: &El<'a>) -> Option<&'a str> {
    match e {
        El::Tok { text, .. } => Some(text),
        El::Grp(_) => None,
    }
}

fn is_name_el(e: &El) -> bool {
    matches!(e, El::Tok { kind, .. } if *kind == tk::NAME)
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
                kind: t.kind,
            }),
            Child::Node(n) => v.push(El::Grp(n)),
        }
    }
    v
}

fn is_definition_node(kind: &str) -> bool {
    matches!(
        kind,
        cst::FUNCTION | cst::CLASS | cst::INTERFACE | cst::TRAIT | cst::ENUM
    )
}

/// Detect `name(...)`, `$recv->name(...)`, `$recv?->name(...)`, and
/// `Recv::name(...)` call sites over the real token tree, recursing into nested
/// groups but **not** into nested definitions (those are scanned as their own
/// functions). Keywords and `new X(...)` instantiations are excluded.
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        let text = tok_text(&els[i]);
        // Member call: `->` / `?->` name `(...)`.
        if matches!(text, Some("->") | Some("?->")) {
            if i + 2 < n && is_name_el(&els[i + 1]) {
                if let Some(g) = grp(&els[i + 2]) {
                    if g.kind == cst::PAREN {
                        let receiver = if i > 0 {
                            tok_text(&els[i - 1]).map(str::to_string)
                        } else {
                            None
                        };
                        out.push(Call {
                            name: tok_text(&els[i + 1]).unwrap_or("").to_string(),
                            kind: CallKind::Instance,
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
        // Static call: `Recv` `::` name `(...)`.
        if text == Some("::") {
            if i + 2 < n && is_name_el(&els[i + 1]) {
                if let Some(g) = grp(&els[i + 2]) {
                    if g.kind == cst::PAREN {
                        let receiver = if i > 0 {
                            tok_text(&els[i - 1]).map(str::to_string)
                        } else {
                            None
                        };
                        out.push(Call {
                            name: tok_text(&els[i + 1]).unwrap_or("").to_string(),
                            kind: CallKind::Static,
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
        // Bare call: name `(...)`, not preceded by a member/static operator, `new`,
        // or `function`, and not a keyword/language construct.
        if is_name_el(&els[i]) {
            let prev = if i > 0 { tok_text(&els[i - 1]) } else { None };
            let name = tok_text(&els[i]).unwrap_or("");
            let blocked = matches!(prev, Some("->") | Some("?->") | Some("::") | Some("new"))
                || prev
                    .map(|p| p.eq_ignore_ascii_case("function"))
                    .unwrap_or(false);
            if !blocked && !is_keyword(name) && i + 1 < n {
                if let Some(g) = grp(&els[i + 1]) {
                    if g.kind == cst::PAREN {
                        out.push(Call {
                            name: name.to_string(),
                            kind: CallKind::Bare,
                            receiver: None,
                        });
                    }
                }
            }
        }
        i += 1;
    }
    // Recurse into groups and nested non-definition item nodes.
    for e in &els {
        if let Some(g) = grp(e) {
            if !is_definition_node(g.kind) {
                scan_calls(g, src, out);
            }
        }
    }
}

/// Collect simple type names instantiated with `new X` / `new X(...)` in a body.
fn scan_new_instantiations(node: &Node, src: &str, out: &mut Vec<String>) {
    let els = significant_children(node, src);
    for (i, e) in els.iter().enumerate() {
        if tok_text(e)
            .map(|t| t.eq_ignore_ascii_case("new"))
            .unwrap_or(false)
            && i + 1 < els.len()
            && is_name_el(&els[i + 1])
        {
            let name = tok_text(&els[i + 1]).unwrap_or("");
            if !is_keyword(name) {
                out.push(name.to_string());
            }
        }
    }
    for e in &els {
        if let Some(g) = grp(e) {
            if !is_definition_node(g.kind) {
                scan_new_instantiations(g, src, out);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::php::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("mod.php", src);
        let file = SourceFile {
            rel_path: "mod.php".to_string(),
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
    fn emits_function_type_module_nodes() {
        let g = graph_for(
            "<?php\nnamespace App;\nclass C {\n  public function m() {}\n}\nfunction f() {}\n",
        );
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "f + C::m");
        assert_eq!(g.count_nodes_of(ont::TYPE), 1, "class C is a Type");
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "module App");
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD));
    }

    #[test]
    fn class_type_kind_is_class() {
        let g = graph_for("<?php class C {}\n");
        let ty = g
            .nodes()
            .find(|n| n.kind == ont::TYPE)
            .expect("a Type node");
        assert_eq!(ty.props.get("type_kind"), Some(&Json::str("class")));
        assert_eq!(ty.props.get("language"), Some(&Json::str("php")));
    }

    #[test]
    fn interface_and_trait_and_enum_kinds() {
        let g = graph_for("<?php\ninterface I {}\ntrait T {}\nenum E { case A; }\n");
        let kinds: Vec<String> = g
            .nodes()
            .filter(|n| n.kind == ont::TYPE)
            .filter_map(|n| match n.props.get("type_kind") {
                Some(Json::Str(s)) => Some(s.clone()),
                _ => None,
            })
            .collect();
        assert!(kinds.contains(&"interface".to_string()));
        assert!(kinds.contains(&"trait".to_string()));
        assert!(kinds.contains(&"enum".to_string()));
    }

    #[test]
    fn resolves_unique_local_call() {
        let g = graph_for(
            "<?php\nnamespace App;\nfunction add($a, $b) { return $a + $b; }\nfunction run() { add(1, 2); }\n",
        );
        let calls = call_edges(&g);
        let add = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("add")))
            .expect("a call to add");
        assert!(add.to.starts_with("fn::App\\add"));
        assert_eq!(add.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(add.props.get("resolution"), Some(&Json::str("local")));
    }

    #[test]
    fn this_method_resolves_via_receiver() {
        let g =
            graph_for("<?php class P {\n  function a() { $this->b(); }\n  function b() {}\n}\n");
        let calls = call_edges(&g);
        let recv = calls
            .iter()
            .find(|e| e.props.get("resolution") == Some(&Json::str("receiver")));
        assert!(
            recv.is_some(),
            "$this->b() should resolve via receiver scope"
        );
        assert_eq!(recv.unwrap().props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn static_self_call_resolves() {
        let g = graph_for(
            "<?php class P {\n  static function a() { self::b(); }\n  static function b() {}\n}\n",
        );
        let calls = call_edges(&g);
        let recv = calls
            .iter()
            .find(|e| e.props.get("call_kind") == Some(&Json::str("static")))
            .expect("a static call");
        assert_eq!(recv.props.get("resolution"), Some(&Json::str("receiver")));
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for("<?php function run() { mystery(); }\n");
        let calls = call_edges(&g);
        assert_eq!(calls.len(), 1);
        assert_eq!(
            calls[0].props.get("resolution"),
            Some(&Json::str("external"))
        );
        assert!(g.has_node("unresolved::mystery"));
    }

    #[test]
    fn external_use_creates_dependency() {
        let g = graph_for("<?php\nuse Symfony\\Component\\HttpFoundation\\Request;\n");
        assert!(g.has_node("ext::Symfony"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::Symfony"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn inheritance_emits_extends_and_implements() {
        let g = graph_for(
            "<?php\ninterface Saveable {}\nclass Base {}\nclass Derived extends Base implements Saveable {}\n",
        );
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an EXTENDS edge");
        assert!(ext.from.starts_with("type::Derived"));
        assert!(ext.to.starts_with("type::Base"));
        let imp = g
            .edges()
            .find(|e| e.kind == edge::IMPLEMENTS)
            .expect("an IMPLEMENTS edge");
        assert!(imp.to.starts_with("type::Saveable"));
    }

    #[test]
    fn trait_use_is_uses_type() {
        let g = graph_for("<?php\ntrait Loggable {}\nclass C {\n  use Loggable;\n}\n");
        let ut = g
            .edges()
            .find(|e| e.kind == edge::USES_TYPE && e.to.contains("Loggable"))
            .expect("a USES_TYPE edge for the trait");
        assert_eq!(ut.props.get("role"), Some(&Json::str("trait")));
    }

    #[test]
    fn const_and_define_are_constants() {
        let g = graph_for("<?php\nconst VERSION = '1.0';\ndefine('APP_NAME', 'demo');\n");
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 2);
        let names: BTreeSet<String> = g
            .nodes()
            .filter(|n| n.kind == ont::CONSTANT)
            .map(|n| n.name.clone())
            .collect();
        assert!(names.contains("VERSION"));
        assert!(names.contains("APP_NAME"));
    }

    #[test]
    fn require_emits_import_to_unresolved_include() {
        let g = graph_for("<?php require_once 'helpers.php';\n");
        assert!(g.has_node("include::helpers.php"));
        let imp = g
            .edges()
            .find(|e| e.kind == edge::IMPORTS && e.to == "include::helpers.php")
            .expect("an include IMPORTS edge");
        assert_eq!(imp.props.get("include"), Some(&Json::Bool(true)));
    }

    #[test]
    fn type_use_via_new_and_signature() {
        let g =
            graph_for("<?php\nclass Widget {}\nfunction build(Widget $w) { $x = new Widget(); }\n");
        assert!(
            g.edges()
                .any(|e| e.kind == edge::USES_TYPE && e.to.contains("Widget")),
            "param annotation and `new` should create USES_TYPE"
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src = "<?php\nnamespace App;\nuse Vendor\\Lib;\nclass C extends Base {\n  function m() { helper(); $this->n(); }\n  function n() {}\n}\nfunction helper() {}\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
