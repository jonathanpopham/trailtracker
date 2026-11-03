//! Lower the Lua CST into the canonical graph.
//!
//! This mirrors the Rust and Python lowerings — same conservative principles,
//! same shared ontology — adapted to Lua's surface. Lua has no classes, no
//! `import`/`include` keyword, and no static type system; its only "type-like"
//! construct is the **table used as a namespace / object**, and its module
//! system is the `require` function. The mapping is therefore:
//!
//!   - `function name(...)` / `local function name(...)` → [`Function`].
//!   - `function T.m(...)` / `function T:m(...)` and `T.m = function(...)` →
//!     a [`Function`] plus a [`Type`] (`type_kind: table`) for `T` that
//!     `HAS_METHOD` it. `:` definitions are flagged `is_method` (implicit
//!     `self`); `.` definitions are table functions. This is the honest reading
//!     of Lua OOP, which is table-based rather than class-based.
//!   - `require "m"` / `require("m")` → [`IMPORTS`] (plus an
//!     [`ExternalDependency`] + `DEPENDS_ON` when the module is not project-local,
//!     exactly like the Python import handling).
//!   - top-level `local x = …` / `x = …` (single name, non-function RHS) →
//!     [`Constant`].
//!   - call sites → [`CALLS`], resolved through a deterministic scope ladder.
//!
//! What Lua honestly has **no** home for: there is no static inheritance
//! (metatable inheritance via `setmetatable` is a runtime call, not a
//! declaration), so no `EXTENDS`/`IMPLEMENTS` edges are emitted, and there are no
//! type annotations, so no `USES_TYPE` edges. Forcing those would fabricate
//! facts the source does not state — see the airgap "no fabricated targets" rule.
//!
//! Everything comes from real tokens on the lossless tree; nothing is guessed.
//! Resolution uses a deterministic ladder (most specific first): for a method
//! call, `self:m()`→enclosing table, `recv:m()`/`recv.m()`→a table named `recv`,
//! else a global method by name; for a bare call, local chunk → global.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::lua::lexer::{is_keyword, kind as tk};
use crate::lang::lua::parser::node as cst;

/// Lower a whole project's worth of Lua files into a graph. `manifest_deps` is
/// unused for Lua (it has no manifest concept the pipeline reads); dependencies
/// are discovered from `require` calls instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
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
        cur_file: 0,
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("lua"))],
    );

    let mut pend_fns: Vec<PendingFn> = Vec::new();
    for (idx, f) in files.iter().enumerate() {
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
                ("language", Json::str("lua")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(leaf, edge::CONTAINS, file_id.clone(), vec![]);

        // Requires anywhere in the file become IMPORTS edges.
        let mut reqs = Vec::new();
        scan_requires(f.root, f.source, &mut reqs);
        for module in reqs {
            lo.emit_require(&file_id, &module);
        }

        lo.walk(
            f.root,
            &file_id,
            &module_join,
            &[],
            false,
            f.source,
            &li,
            &mut pend_fns,
        );
    }

    // Pass C: resolve calls against the now-complete symbol tables.
    for pf in &pend_fns {
        if let Some(block) = pf.block {
            let mut calls = Vec::new();
            scan_calls(block, pf.source, &mut calls);
            let ctx = Ctx {
                module_join: pf.module_join.clone(),
                owner_type: pf.owner_type.clone(),
            };
            for call in &calls {
                let res = lo.resolve(call, &ctx);
                lo.emit_call(&pf.id, call, res);
            }
        }
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    local_roots: BTreeSet<String>,
    fn_by_name: BTreeMap<String, Vec<String>>,
    method_by_name: BTreeMap<String, Vec<String>>,
    fn_by_module: BTreeMap<(String, String), Vec<String>>,
    method_by_type: BTreeMap<(String, String), Vec<String>>,
    type_by_name: BTreeMap<String, Vec<String>>,
    cur_file: usize,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    block: Option<&'a Node>,
    module_join: String,
    owner_type: Option<String>,
}

struct Call {
    name: String,
    /// `recv.name(...)` or `recv:name(...)` (vs a bare `name(...)`).
    qualified: bool,
    /// True specifically for the `:` colon-call form (implicit `self`).
    colon: bool,
    receiver: Option<String>,
}

struct Ctx {
    module_join: String,
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
                vec![("language", Json::str("lua"))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    /// Walk a statement container, creating definition nodes and recursing into
    /// nested scopes. `in_function` gates top-level `Constant` emission.
    #[allow(clippy::too_many_arguments)]
    fn walk<'a>(
        &mut self,
        container: &'a Node,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        in_function: bool,
        src: &'a str,
        li: &LineIndex,
        pend: &mut Vec<PendingFn<'a>>,
    ) {
        for item in container.child_nodes() {
            match item.kind {
                cst::FUNCTION => {
                    self.handle_fn(item, None, file_id, module_join, scope, src, li, pend);
                }
                cst::CONTROL
                | cst::BLOCK
                | cst::HEADER
                | cst::RETURN
                | cst::PAREN
                | cst::BRACKET
                | cst::BRACE => {
                    // Not new scopes: definitions inside still belong to the
                    // enclosing chunk/function. Recurse to find nested functions.
                    self.walk(
                        item,
                        file_id,
                        module_join,
                        scope,
                        in_function,
                        src,
                        li,
                        pend,
                    );
                }
                cst::LOCAL_STMT | cst::SIMPLE_STMT => {
                    self.handle_stmt(
                        item,
                        file_id,
                        module_join,
                        scope,
                        in_function,
                        src,
                        li,
                        pend,
                    );
                }
                _ => {}
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_stmt<'a>(
        &mut self,
        stmt: &'a Node,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        in_function: bool,
        src: &'a str,
        li: &LineIndex,
        pend: &mut Vec<PendingFn<'a>>,
    ) {
        let lhs = analyze_lhs(stmt, src);
        let func_children: Vec<&Node> = stmt.children_of(cst::FUNCTION).collect();

        if lhs.has_eq && !lhs.path.is_empty() && func_children.len() == 1 {
            // `x = function(...)` / `M.foo = function(...)` — a named function.
            self.handle_fn(
                func_children[0],
                Some((lhs.path.clone(), false)),
                file_id,
                module_join,
                scope,
                src,
                li,
                pend,
            );
        } else {
            if lhs.has_eq && !in_function && lhs.path.len() == 1 && func_children.is_empty() {
                self.handle_constant(&lhs.path[0], lhs.is_local, stmt, file_id, module_join, li);
            }
            // Any direct anonymous functions (e.g. multi-assignment RHS).
            for f in &func_children {
                self.handle_fn(f, None, file_id, module_join, scope, src, li, pend);
            }
        }

        // Descend into argument / table groups for nested anonymous functions.
        for ch in stmt.child_nodes() {
            if matches!(ch.kind, cst::PAREN | cst::BRACKET | cst::BRACE) {
                self.walk(ch, file_id, module_join, scope, in_function, src, li, pend);
            }
        }
    }

    /// Emit a `Function` node (and, for a dotted/colon name, its owning table
    /// `Type` + `HAS_METHOD`), populate the resolution indexes, and recurse into
    /// the body for nested definitions. `name_override` carries the name path for
    /// an anonymous function bound by assignment (`M.foo = function …`).
    #[allow(clippy::too_many_arguments)]
    fn handle_fn<'a>(
        &mut self,
        func: &'a Node,
        name_override: Option<(Vec<String>, bool)>,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend: &mut Vec<PendingFn<'a>>,
    ) {
        let info = name_override.or_else(|| funcname_info(func, src));
        let line = li.line_col(name_start(func)).line;
        let is_local = func.tokens().any(|t| t.span.text(src) == "local");
        let block = func.child(cst::BLOCK);

        // Resolve (display name, qualified name, node id, owning table) from the
        // name path. A single segment is a plain function; multiple segments name
        // a method/field of an owning table; no segments is an anonymous function.
        let mut name = "<anonymous>".to_string();
        let mut qual = qual_name(module_join, scope, "<anonymous>");
        let mut id = format!("fn::{qual}#{line}@{}", func.span.start);
        let mut owner: Option<(String, String)> = None;
        if let Some((segs, _)) = info.filter(|(s, _)| !s.is_empty()) {
            if segs.len() == 1 {
                name = segs[0].clone();
                qual = qual_name(module_join, scope, &name);
                id = format!("fn::{qual}#{line}");
            } else {
                name = segs.last().unwrap().clone();
                let owner_join = segs[..segs.len() - 1].join(".");
                let owner_last = segs[segs.len() - 2].clone();
                qual = qual_name(module_join, scope, &segs.join("."));
                id = format!("fn::{qual}#{line}");
                owner = Some((owner_join, owner_last));
            }
        }

        let is_method = owner.is_some() && method_flag(func, src);
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("lua")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(func.span.start as u64)),
            ("span_end", Json::U64(func.span.end as u64)),
            ("has_body", Json::Bool(block.is_some())),
        ];
        if is_local {
            props.push(("is_local", Json::Bool(true)));
        }
        if let Some((_, owner_last)) = &owner {
            props.push(("receiver_type", Json::str(owner_last.clone())));
        }
        if is_method {
            props.push(("is_method", Json::Bool(true)));
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

        let owner_last = if let Some((owner_join, owner_last)) = owner {
            let type_qual = qual_name(module_join, &[], &owner_join);
            let type_id = format!("type::{type_qual}");
            self.g.upsert_node(
                type_id.clone(),
                ont::TYPE,
                owner_join.clone(),
                vec![
                    ("type_kind", Json::str("table")),
                    ("qualified_name", Json::str(type_qual)),
                    ("language", Json::str("lua")),
                ],
            );
            self.g
                .add_edge(file_id, edge::DECLARES, type_id.clone(), vec![]);
            self.type_by_name
                .entry(owner_last.clone())
                .or_default()
                .push(type_id.clone());
            self.g
                .add_edge(type_id.clone(), edge::HAS_METHOD, id.clone(), vec![]);
            self.method_by_name
                .entry(name.clone())
                .or_default()
                .push(id.clone());
            self.method_by_type
                .entry((owner_last.clone(), name.clone()))
                .or_default()
                .push(id.clone());
            Some(owner_last)
        } else {
            None
        };

        pend.push(PendingFn {
            id,
            source: src,
            block,
            module_join: module_join.to_string(),
            owner_type: owner_last,
        });

        if let Some(block) = block {
            let mut child_scope = scope.to_vec();
            child_scope.push(name);
            self.walk(
                block,
                file_id,
                module_join,
                &child_scope,
                true,
                src,
                li,
                pend,
            );
        }
    }

    fn handle_constant(
        &mut self,
        name: &str,
        is_local: bool,
        stmt: &Node,
        file_id: &str,
        module_join: &str,
        li: &LineIndex,
    ) {
        let line = li.line_col(stmt.span.start).line;
        let id = format!("const::{}", qual_name(module_join, &[], name));
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            name.to_string(),
            vec![
                (
                    "binding",
                    Json::str(if is_local { "local_var" } else { "global_var" }),
                ),
                ("language", Json::str("lua")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
    }

    /// Emit the `IMPORTS` edge for one `require`d module, plus the
    /// `ExternalDependency`/`DEPENDS_ON` pair when the module is not project-local.
    fn emit_require(&mut self, file_id: &str, module: &str) {
        if module.is_empty() {
            return;
        }
        let root = module
            .split(['.', '/'])
            .next()
            .unwrap_or(module)
            .to_string();
        if self.local_roots.contains(&root) {
            let id = format!("mod::{root}");
            self.g.upsert_node(
                id.clone(),
                ont::MODULE,
                root,
                vec![("language", Json::str("lua"))],
            );
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                id,
                vec![
                    ("path", Json::str(module.to_string())),
                    ("external", Json::Bool(false)),
                ],
            );
        } else {
            let dep_id = format!("ext::{root}");
            self.g.upsert_node(
                dep_id.clone(),
                ont::EXTERNAL_DEPENDENCY,
                root,
                vec![
                    ("external", Json::Bool(true)),
                    ("source", Json::str("require")),
                ],
            );
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                dep_id.clone(),
                vec![
                    ("path", Json::str(module.to_string())),
                    ("external", Json::Bool(true)),
                ],
            );
            self.g
                .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
        }
    }

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        if call.qualified {
            // `self:m()` resolves against the enclosing table.
            if call.colon && call.receiver.as_deref() == Some("self") {
                if let Some(owner) = &ctx.owner_type {
                    let c = self.methods_of(owner, &call.name);
                    if !c.is_empty() {
                        return mk(c, "receiver");
                    }
                }
            }
            // `T:m()` / `T.m()` where the receiver is a known table name.
            if let Some(recv) = &call.receiver {
                let c = self.methods_of(recv, &call.name);
                if !c.is_empty() {
                    return mk(c, "receiver");
                }
            }
            // Unknown receiver type (no inference). The honest candidate set is
            // every same-name method PLUS every same-name free function — a Lua
            // member call reaches any function stored in a table (`t.f()`),
            // including plain locals assigned as fields.
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
            ("qualified", Json::Bool(call.qualified)),
            ("method", Json::Bool(call.colon)),
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
    if !name.is_empty() {
        parts.push(name.to_string());
    }
    parts.join(".")
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

/// Name path + method flag from a `FuncName` node, or `None` when anonymous.
fn funcname_info(func: &Node, src: &str) -> Option<(Vec<String>, bool)> {
    let fname = func.child(cst::FUNC_NAME)?;
    let mut segs = Vec::new();
    let mut is_method = false;
    for t in fname.tokens() {
        let txt = t.span.text(src);
        if t.kind == tk::NAME && !is_keyword(txt) {
            segs.push(txt.to_string());
        } else if txt == ":" {
            is_method = true;
        }
    }
    if segs.is_empty() {
        None
    } else {
        Some((segs, is_method))
    }
}

/// Whether a function definition's name path used the `:` colon form.
fn method_flag(func: &Node, src: &str) -> bool {
    func.child(cst::FUNC_NAME)
        .map(|n| n.tokens().any(|t| t.span.text(src) == ":"))
        .unwrap_or(false)
}

fn name_start(func: &Node) -> u32 {
    func.child(cst::FUNC_NAME)
        .map(|n| n.span.start)
        .unwrap_or(func.span.start)
}

/// The assignment target of a statement: the dotted name path before the first
/// top-level `=`, plus whether it is a `local` and whether an `=` is present.
/// Conservative — a comma (multi-assignment), an index group, or any non-name
/// token in the target clears the path so we never mis-name.
struct Lhs {
    path: Vec<String>,
    is_local: bool,
    has_eq: bool,
}

fn analyze_lhs(stmt: &Node, src: &str) -> Lhs {
    let mut path = Vec::new();
    let mut clean = true;
    let mut has_eq = false;
    let mut is_local = false;
    for ch in &stmt.children {
        match ch {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => {
                let txt = t.span.text(src);
                if txt == "=" {
                    has_eq = true;
                    break;
                } else if txt == "local" {
                    is_local = true;
                } else if t.kind == tk::NAME && !is_keyword(txt) {
                    path.push(txt.to_string());
                } else if txt == "." {
                    // dotted-name separator: fine
                } else {
                    clean = false;
                }
            }
            // A node (group/function) before `=` means a complex target.
            Child::Node(_) => {
                clean = false;
                break;
            }
        }
    }
    if !clean {
        path.clear();
    }
    Lhs {
        path,
        is_local,
        has_eq,
    }
}

// --- scanning over the lossless token tree ----------------------------------

enum El<'a> {
    Tok { text: &'a str, kind: &'static str },
    Grp(&'a Node),
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

fn el_tok_text<'a>(e: &El<'a>) -> Option<&'a str> {
    match e {
        El::Tok { text, .. } => Some(text),
        El::Grp(_) => None,
    }
}

fn el_is_name(e: &El) -> bool {
    matches!(e, El::Tok { kind, .. } if *kind == tk::NAME)
}

/// Whether `e` can be a Lua call argument: `(...)`, `{...}`, or a string literal
/// (the `f "x"` / `f{...}` call sugar).
fn el_is_call_arg(e: &El) -> bool {
    match e {
        El::Grp(n) => n.kind == cst::PAREN || n.kind == cst::BRACE,
        El::Tok { kind, .. } => *kind == tk::STRING,
    }
}

/// Detect call sites over the real token tree: `name args`, `recv.name args`,
/// and `recv:name args`, where `args` is `(...)`, `{...}`, or a string literal.
/// Keywords are excluded, as is `require` (handled as an import). Recurses into
/// groups and nested non-function nodes, but never into nested `Function` nodes
/// (those are scanned as their own pending functions).
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        // Qualified call: `.`/`:` name args.
        let sep = el_tok_text(&els[i]);
        if matches!(sep, Some(".") | Some(":")) {
            if i + 2 < n && el_is_name(&els[i + 1]) && el_is_call_arg(&els[i + 2]) {
                let name = el_tok_text(&els[i + 1]).unwrap_or("");
                if !is_keyword(name) {
                    let receiver = if i > 0 {
                        match &els[i - 1] {
                            El::Tok { text, kind } if *kind == tk::NAME => Some(text.to_string()),
                            _ => None,
                        }
                    } else {
                        None
                    };
                    out.push(Call {
                        name: name.to_string(),
                        qualified: true,
                        colon: sep == Some(":"),
                        receiver,
                    });
                    i += 3;
                    continue;
                }
            }
            i += 1;
            continue;
        }
        // Bare call: name args, not preceded by `.`/`:`.
        if el_is_name(&els[i]) {
            let text = el_tok_text(&els[i]).unwrap_or("");
            let prev = if i > 0 {
                el_tok_text(&els[i - 1])
            } else {
                None
            };
            let after_sep = matches!(prev, Some(".") | Some(":"));
            if !after_sep
                && !is_keyword(text)
                && text != "require"
                && i + 1 < n
                && el_is_call_arg(&els[i + 1])
            {
                out.push(Call {
                    name: text.to_string(),
                    qualified: false,
                    colon: false,
                    receiver: None,
                });
            }
        }
        i += 1;
    }
    for e in &els {
        if let El::Grp(g) = e {
            if g.kind != cst::FUNCTION {
                scan_calls(g, src, out);
            }
        }
    }
}

/// Collect `require`d module names anywhere in the tree: `require "m"`,
/// `require('m')`, `require[[m]]`. Recurses into every node (requires may appear
/// inside functions). The module name is read from the first string literal of
/// the argument, never guessed.
fn scan_requires(node: &Node, src: &str, out: &mut Vec<String>) {
    let els = significant_children(node, src);
    let n = els.len();
    for i in 0..n {
        if let El::Tok { text, kind } = &els[i] {
            if *kind == tk::NAME && *text == "require" {
                let prev = if i > 0 {
                    el_tok_text(&els[i - 1])
                } else {
                    None
                };
                if matches!(prev, Some(".") | Some(":")) {
                    continue; // a field named `require`, not the global
                }
                if i + 1 < n {
                    if let Some(m) = require_arg_module(&els[i + 1], src) {
                        out.push(m);
                    }
                }
            }
        }
    }
    for e in &els {
        if let El::Grp(g) = e {
            scan_requires(g, src, out);
        }
    }
}

/// Extract a module name from a `require` argument element: a string literal, or
/// a parenthesized group whose first child is a string literal.
fn require_arg_module(e: &El, src: &str) -> Option<String> {
    match e {
        El::Tok { text, kind } if *kind == tk::STRING => Some(strip_string_literal(text)),
        El::Grp(n) if n.kind == cst::PAREN => {
            for c in &n.children {
                if let Child::Token(t) = c {
                    if t.kind == tk::STRING {
                        return Some(strip_string_literal(t.span.text(src)));
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// Strip the delimiters from a Lua string literal: `"…"`/`'…'` or a long bracket
/// `[[…]]` / `[=[…]=]`.
fn strip_string_literal(text: &str) -> String {
    let bytes = text.as_bytes();
    if bytes.first() == Some(&b'[') {
        // Long bracket: `[` `=`* `[` … `]` `=`* `]`.
        let mut level = 0;
        let mut idx = 1;
        while bytes.get(idx) == Some(&b'=') {
            level += 1;
            idx += 1;
        }
        if bytes.get(idx) == Some(&b'[') {
            let open = level + 2;
            let close = level + 2;
            if text.len() >= open + close {
                return text[open..text.len() - close].to_string();
            }
        }
        return text.to_string();
    }
    let first = text.chars().next();
    if matches!(first, Some('"') | Some('\'')) && text.len() >= 2 {
        return text[1..text.len() - 1].to_string();
    }
    text.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::lua::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("mod.lua", src);
        let file = SourceFile {
            rel_path: "mod.lua".to_string(),
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
    fn emits_function_and_module_nodes() {
        let g = graph_for("local function f()\nend\n\nfunction g()\nend\n");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "f + g");
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "module mod");
    }

    #[test]
    fn dotted_function_makes_table_type_with_method() {
        let g = graph_for("function M.new()\nend\n");
        let ty = g
            .nodes()
            .find(|n| n.kind == ont::TYPE)
            .expect("a Type node for table M");
        assert_eq!(ty.props.get("type_kind"), Some(&Json::str("table")));
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD));
    }

    #[test]
    fn colon_method_is_flagged() {
        let g = graph_for("function Account:deposit(n)\nend\n");
        let m = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "deposit")
            .expect("the method");
        assert_eq!(m.props.get("is_method"), Some(&Json::Bool(true)));
    }

    #[test]
    fn resolves_unique_local_call() {
        let g = graph_for(
            "local function add(a, b)\n  return a + b\nend\n\nfunction run()\n  add(1, 2)\nend\n",
        );
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
        let g = graph_for("function P.a(self)\n  self:b()\nend\n\nfunction P:b()\nend\n");
        let calls = call_edges(&g);
        let recv = calls
            .iter()
            .find(|e| e.props.get("resolution") == Some(&Json::str("receiver")));
        assert!(recv.is_some(), "self:b() should resolve via receiver scope");
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for("function run()\n  mystery()\nend\n");
        let calls = call_edges(&g);
        assert_eq!(calls.len(), 1);
        assert_eq!(
            calls[0].props.get("resolution"),
            Some(&Json::str("external"))
        );
        assert!(g.has_node("unresolved::mystery"));
    }

    #[test]
    fn require_creates_dependency() {
        let g = graph_for("local json = require('cjson')\nlocal x = require \"socket\"\n");
        assert!(g.has_node("ext::cjson"));
        assert!(g.has_node("ext::socket"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::cjson"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn string_arg_call_is_detected() {
        let g = graph_for("function run()\n  log 'hello'\nend\n");
        let calls = call_edges(&g);
        assert!(
            calls
                .iter()
                .any(|e| e.props.get("callee") == Some(&Json::str("log"))),
            "f 'str' call sugar should be detected"
        );
    }

    #[test]
    fn top_level_assignment_is_constant() {
        let g = graph_for("VERSION = '1.0'\nfunction f()\n  local inner = 1\nend\n");
        // VERSION is a module-level Constant; `inner` (function local) is not.
        let consts: Vec<&str> = g
            .nodes()
            .filter(|n| n.kind == ont::CONSTANT)
            .map(|n| n.name.as_str())
            .collect();
        assert_eq!(consts, vec!["VERSION"]);
    }

    #[test]
    fn assigned_function_is_named() {
        let g = graph_for("local M = {}\nM.handler = function(e)\nend\n");
        assert!(
            g.nodes()
                .any(|n| n.kind == ont::FUNCTION && n.name == "handler"),
            "M.handler = function should be a named Function"
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src = "local function helper()\nend\nfunction M.run()\n  helper()\nend\nreturn M\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
