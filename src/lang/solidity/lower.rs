//! Lower the Solidity CST into the canonical graph.
//!
//! This mirrors the Java lowering ([`crate::lang::java::lower`]) — same
//! conservative principles, same shared ontology — adapted to Solidity's surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to
//!    a concrete project definition only when a scope level yields exactly one
//!    candidate; several candidates are emitted as an ambiguous edge with the full
//!    `candidates` set; none resolves to an explicit external/unresolved node.
//! 2. **Everything comes from real tokens.** Calls, `is` bases, imports, and type
//!    uses are read off the lossless tree, never guessed. There is no LLM in the
//!    airgapped runtime to fill gaps.
//!
//! Resolution uses a deterministic **scope ladder** (most specific first; the
//! first level with any candidate decides): receiver (`this`/`super`) →
//! enclosing-contract functions → global functions. Each edge records which level
//! resolved it, so the call graph stays auditable.
//!
//! Honest mappings (see the IR Atlas):
//!   - `contract`/`interface`/`library` → `Type` distinguished by a `type_kind`.
//!   - `struct`/`enum` → `Type` (`type_kind` `struct`/`enum`).
//!   - `event`/`error` definitions → `Type` (`type_kind` `event`/`error`). These
//!     are honest *named declarations* with a parameter list, so they read as
//!     `Type` rather than `Constant`; there is no dedicated event/error node kind
//!     in the ontology, and inventing one is out of scope (see `docs/ir-atlas.md`).
//!   - `function`/`constructor`/`modifier`/`receive`/`fallback` → `Function`
//!     (distinguished by a `function_kind` property), with `HAS_METHOD` from the
//!     enclosing contract `Type`.
//!   - state variables / `constant` / `immutable` → `Constant` (a value binding,
//!     distinguished by a `binding` property).
//!   - `contract X is Y` → `EXTENDS` when `Y` is a (uniquely resolved) project
//!     contract/library, `IMPLEMENTS` when `Y` is a project `interface`; an
//!     unresolved base defaults to `EXTENDS` against an `UnresolvedSymbol`.
//!   - `import "…"` → `IMPORTS` (relative paths are intra-project `Module`s;
//!     non-relative roots like `@openzeppelin` create an `ExternalDependency` plus
//!     a `DEPENDS_ON`).
//!   - calls and `new Type(...)` → `CALLS`.
//!
//! Punted (parsed losslessly, no edges emitted): `using … for …` directives,
//! struct-field and enum-variant members (the struct/enum body is kept as a token
//! tree but its fields are not broken out into `Constant`s).

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::solidity::lexer::{is_keyword, kind as tk};
use crate::lang::solidity::parser::node as cst;

/// Lower a whole project's worth of Solidity files into a graph. `manifest_deps`
/// is unused for Solidity (the pipeline's manifest reader is Cargo-only);
/// dependencies are discovered from `import` statements instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        fn_by_name: BTreeMap::new(),
        fn_by_type: BTreeMap::new(),
        type_by_name: BTreeMap::new(),
        interface_ids: BTreeSet::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("solidity"))],
    );

    // Pass B: create definition nodes + structural edges and build symbol tables.
    // `is` bases are deferred to pass C so a base declared later still resolves.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_bases: Vec<PendingBase> = Vec::new();
    for f in files {
        let li = LineIndex::new(f.source);
        let module_join = f.module_path.join(".");
        let leaf = lo.ensure_modules(&f.module_path);
        let file_id = format!("file::{}", f.rel_path);
        lo.g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("solidity")),
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
            &mut pend_bases,
        );
    }

    // Pass C: resolve calls (scope ladder), type usages, and `is` bases against
    // the now-complete symbol tables.
    for pf in &pend_fns {
        let ctx = Ctx {
            owner_type: pf.owner_type.clone(),
        };
        if let Some(block) = pf.item.child(cst::BLOCK) {
            let mut calls = Vec::new();
            scan_calls(block, pf.source, &mut calls);
            for call in &calls {
                let res = lo.resolve(call, &ctx);
                lo.emit_call(&pf.id, call, res);
            }
        }
        lo.emit_type_uses(&pf.id, pf.item, pf.source);
    }
    for pb in &pend_bases {
        lo.emit_base(pb);
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    /// Simple name → all function node ids (global call level).
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// (contract_name, fn_name) → function ids (receiver / same-contract level).
    fn_by_type: BTreeMap<(String, String), Vec<String>>,
    /// Simple name → type node ids.
    type_by_name: BTreeMap<String, Vec<String>>,
    /// Type ids whose `type_kind` is `interface` (decides EXTENDS vs IMPLEMENTS).
    interface_ids: BTreeSet<String>,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    item: &'a Node,
    owner_type: Option<String>,
}

/// A deferred `is` base link, resolved in pass C.
struct PendingBase {
    type_id: String,
    base_name: String,
}

/// The enclosing contract while walking, for functions (`HAS_METHOD`, receiver
/// scope).
struct Owner {
    name: String,
    id: String,
}

/// A detected call site over the lossless tree.
struct Call {
    /// The called name (final member or bare name; the type for a constructor).
    name: String,
    /// True for `recv.name(...)` member calls.
    method: bool,
    /// Immediate receiver identifier (`this`, `super`, a variable).
    receiver: Option<String>,
    /// True for `new Type(...)` constructor calls.
    constructor: bool,
}

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
    /// module id (or the package id for a file at the project root).
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
                vec![("language", Json::str("solidity"))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    /// Walk a declaration container (a `SourceUnit` or `ItemBlock`), creating
    /// definition nodes and recursing into contract bodies. `owner` is the
    /// enclosing contract (the receiver scope for functions).
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
        pend_bases: &mut Vec<PendingBase>,
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
                    pend_bases,
                );
                continue;
            }
            match item.kind {
                cst::FUNCTION => self.handle_function(
                    item,
                    file_id,
                    module_join,
                    scope,
                    owner,
                    src,
                    li,
                    pend_fns,
                ),
                cst::STATE_VAR => self.handle_state_var(item, file_id, module_join, scope, src, li),
                cst::IMPORT => self.handle_import(item, file_id, src),
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
        pend_bases: &mut Vec<PendingBase>,
    ) {
        let name = name_text(item, src).unwrap_or("<anonymous>").to_string();
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(module_join, scope, &name);
        let id = format!("type::{qual}");
        let type_kind = match item.kind {
            cst::CONTRACT => "contract",
            cst::INTERFACE => "interface",
            cst::LIBRARY => "library",
            cst::STRUCT => "struct",
            cst::ENUM => "enum",
            cst::EVENT => "event",
            cst::ERROR_DEF => "error",
            _ => "type",
        };
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str(type_kind)),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("solidity")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());
        if item.kind == cst::INTERFACE {
            self.interface_ids.insert(id.clone());
        }

        // `is` bases (deferred to pass C). Only contract-like types have them.
        for base in bases(item, src) {
            pend_bases.push(PendingBase {
                type_id: id.clone(),
                base_name: base,
            });
        }

        // Recurse only into contract-like bodies; struct/enum/event/error have no
        // sub-definitions broken out.
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
                pend_bases,
            );
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_function<'a>(
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
        let fkind = function_kind(item, src);
        let (name, name_start) = function_name(item, src, fkind);
        let line = li.line_col(name_start).line;
        let qual = qual_name(module_join, scope, &name);
        let id = format!("fn::{qual}#{line}");
        let block = item.child(cst::BLOCK);
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("solidity")),
            ("function_kind", Json::str(fkind)),
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
        if let Some(o) = owner {
            self.fn_by_type
                .entry((o.name.clone(), name.clone()))
                .or_default()
                .push(id.clone());
            self.g
                .add_edge(o.id.clone(), edge::HAS_METHOD, id.clone(), vec![]);
            // A constructor resolves `new Owner(...)`: index it under the contract
            // name so the constructor scope ladder can find it.
            if fkind == "constructor" {
                self.fn_by_type
                    .entry((o.name.clone(), o.name.clone()))
                    .or_default()
                    .push(id.clone());
                self.fn_by_name
                    .entry(o.name.clone())
                    .or_default()
                    .push(id.clone());
            }
        }

        pend_fns.push(PendingFn {
            id,
            source: src,
            item,
            owner_type: owner.map(|o| o.name.clone()),
        });
    }

    fn handle_state_var(
        &mut self,
        item: &Node,
        file_id: &str,
        module_join: &str,
        scope: &[String],
        src: &str,
        li: &LineIndex,
    ) {
        let (name, start) = match state_var_name(item, src) {
            Some(n) => n,
            None => return, // malformed / nameless declaration; still in the tree
        };
        let binding = state_var_binding(item, src);
        let line = li.line_col(start).line;
        let qual = qual_name(module_join, scope, &name);
        let id = format!("const::{qual}");
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            name,
            vec![
                ("binding", Json::str(binding)),
                ("language", Json::str("solidity")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
    }

    /// `import "path";` / `import {X} from "path";` / `import * as N from "path";`
    /// → an `IMPORTS` edge. Relative paths (`./`, `../`) are intra-project
    /// `Module`s; a non-relative root (e.g. `@openzeppelin`) creates an
    /// `ExternalDependency` plus a `DEPENDS_ON`.
    fn handle_import(&mut self, item: &Node, file_id: &str, src: &str) {
        let header = match item.child(cst::HEADER) {
            Some(h) => h,
            None => return,
        };
        // The import target is the (first) string literal in the directive.
        let path = match header
            .tokens()
            .find(|t| t.kind == tk::STRING)
            .map(|t| unquote(t.span.text(src)))
        {
            Some(p) if !p.is_empty() => p,
            _ => return,
        };
        if is_relative_import(&path) {
            let mod_id = format!("mod::{}", normalize_import(&path));
            self.g.upsert_node(
                mod_id.clone(),
                ont::MODULE,
                import_stem(&path),
                vec![("language", Json::str("solidity"))],
            );
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                mod_id,
                vec![("path", Json::str(path)), ("external", Json::Bool(false))],
            );
        } else {
            let root = import_root(&path);
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
                vec![("path", Json::str(path)), ("external", Json::Bool(true))],
            );
            self.g
                .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
        }
    }

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        if call.constructor {
            // Constructors are indexed under the contract name.
            let c = self.fns_of(&call.name, &call.name);
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
            // Receiver scope: `this.m()` / `super.m()` → enclosing contract's fns.
            if matches!(call.receiver.as_deref(), Some("this") | Some("super")) {
                if let Some(owner) = &ctx.owner_type {
                    let c = self.fns_of(owner, &call.name);
                    if !c.is_empty() {
                        return mk(c, "receiver");
                    }
                }
            }
            // Other receivers have an unknown type (no inference): fall back to a
            // global match, preserving any ambiguity.
            let c = self.global_fns(&call.name);
            return if c.is_empty() {
                Resolution {
                    outcome: Outcome::None,
                    level: "external",
                }
            } else {
                mk(c, "global_method")
            };
        }
        // Bare call `m(...)`: same-contract function first, then any project fn.
        if let Some(owner) = &ctx.owner_type {
            let c = self.fns_of(owner, &call.name);
            if !c.is_empty() {
                return mk(c, "receiver");
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

    /// Resolve a deferred `is` base into a concrete edge: `IMPLEMENTS` when the
    /// base is a (uniquely resolved) project `interface`, otherwise `EXTENDS`
    /// (Solidity has true contract inheritance). An unresolvable base points at an
    /// explicit `UnresolvedSymbol`.
    fn emit_base(&mut self, pb: &PendingBase) {
        let (target, kind) = match self.unique_type(&pb.base_name) {
            Some(id) => {
                let kind = if self.interface_ids.contains(&id) {
                    edge::IMPLEMENTS
                } else {
                    edge::EXTENDS
                };
                (id, kind)
            }
            None => {
                let id = unresolved_id(&pb.base_name);
                self.ensure_unresolved(&id, &pb.base_name, "base");
                (id, edge::EXTENDS)
            }
        };
        self.g.add_edge(
            pb.type_id.clone(),
            kind,
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

    fn fns_of(&self, type_name: &str, fn_name: &str) -> Vec<String> {
        self.fn_by_type
            .get(&(type_name.to_string(), fn_name.to_string()))
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

    /// Add `USES_TYPE` edges for identifiers in a function's signature regions
    /// (params, `returns`, modifier invocations) that name a unique project type.
    /// Bodies are deliberately excluded — parity with the Java lowering.
    fn emit_type_uses(&mut self, from_id: &str, item: &Node, src: &str) {
        let mut seen: Vec<String> = Vec::new();
        for region in [cst::PARAMS, cst::HEADER] {
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

// --- pure helpers -----------------------------------------------------------

/// `module.scope….name` — the dotted qualified name and basis for node ids.
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

/// Strip a leading/trailing single or double quote from a string-literal text.
fn unquote(s: &str) -> String {
    let bytes = s.as_bytes();
    if bytes.len() >= 2 {
        let first = bytes[0];
        let last = bytes[bytes.len() - 1];
        if (first == b'"' || first == b'\'') && last == first {
            return s[1..s.len() - 1].to_string();
        }
    }
    s.to_string()
}

/// A relative import path (`./x`, `../x`) is intra-project.
fn is_relative_import(path: &str) -> bool {
    path.starts_with("./") || path.starts_with("../") || path.starts_with('.')
}

/// Normalize a relative import path into a dotted module id segment (drop the
/// `.sol` suffix and the leading `./`, keep directory structure).
fn normalize_import(path: &str) -> String {
    let trimmed = path
        .trim_start_matches("./")
        .trim_end_matches(".sol")
        .trim_matches('/');
    trimmed.replace('/', ".")
}

/// The file stem of an import path (last path segment without `.sol`).
fn import_stem(path: &str) -> String {
    let last = path
        .trim_end_matches('/')
        .rsplit('/')
        .next()
        .unwrap_or(path);
    last.trim_end_matches(".sol").to_string()
}

/// The dependency root of a non-relative import: `@scope/pkg` for a scoped
/// package, otherwise the first path segment.
fn import_root(path: &str) -> String {
    let mut segs = path.split('/');
    let first = segs.next().unwrap_or(path);
    if first.starts_with('@') {
        match segs.next() {
            Some(second) => format!("{first}/{second}"),
            None => first.to_string(),
        }
    } else {
        first.to_string()
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

/// Classify a function declaration from its leading keyword.
fn function_kind(item: &Node, src: &str) -> &'static str {
    for t in item.tokens() {
        match t.span.text(src) {
            "function" => return "function",
            "constructor" => return "constructor",
            "modifier" => return "modifier",
            "receive" => return "receive",
            "fallback" => return "fallback",
            _ => {}
        }
    }
    "function"
}

/// The function's name and byte offset. A named declaration uses its `Name`
/// child; an anonymous `constructor`/`receive`/`fallback` is named by its kind.
fn function_name(item: &Node, src: &str, fkind: &'static str) -> (String, u32) {
    if let Some(nm) = item.child(cst::NAME) {
        if let Some(t) = nm.tokens().next() {
            return (t.span.text(src).to_string(), t.span.start);
        }
    }
    (fkind.to_string(), item.span.start)
}

/// The declared state-variable name and offset: the last top-level (paren/bracket
/// depth 0) non-keyword identifier in the `Signature` region. For
/// `mapping(address => uint) public balances;` the inner `address`/`uint` live in
/// a child group (excluded from `tokens()`), so the name is `balances`.
fn state_var_name(item: &Node, src: &str) -> Option<(String, u32)> {
    let sig = item.child(cst::SIGNATURE)?;
    let mut last: Option<(String, u32)> = None;
    for t in sig.tokens() {
        let text = t.span.text(src);
        if t.kind == tk::IDENT && !is_keyword(text) {
            last = Some((text.to_string(), t.span.start));
        }
    }
    last
}

/// Classify a state variable's binding from its modifier keywords.
fn state_var_binding(item: &Node, src: &str) -> &'static str {
    let mut is_const = false;
    let mut is_immutable = false;
    if let Some(sig) = item.child(cst::SIGNATURE) {
        for t in sig.tokens() {
            match t.span.text(src) {
                "constant" => is_const = true,
                "immutable" => is_immutable = true,
                _ => {}
            }
        }
    }
    if is_const {
        "constant"
    } else if is_immutable {
        "immutable"
    } else {
        "state_var"
    }
}

/// Simple base names from a contract's `is` clause (the last identifier of each
/// base, comma-separated). Base constructor arguments live in a child `Paren`
/// group, so they are naturally excluded from the header's direct tokens.
fn bases(item: &Node, src: &str) -> Vec<String> {
    let header = match item.child(cst::HEADER) {
        Some(h) => h,
        None => return Vec::new(),
    };
    let mut out: Vec<String> = Vec::new();
    let mut collecting = false;
    let mut last: Option<String> = None;
    for t in header.tokens() {
        let text = t.span.text(src);
        match text {
            "is" => collecting = true,
            "," => {
                if let Some(n) = last.take() {
                    if collecting {
                        out.push(n);
                    }
                }
            }
            "." => {} // qualified base `Lib.Base`: keep collecting last segment
            _ if t.kind == tk::IDENT && !is_keyword(text) => {
                if collecting {
                    last = Some(text.to_string());
                }
            }
            _ => {}
        }
    }
    if let Some(n) = last.take() {
        if collecting {
            out.push(n);
        }
    }
    out
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
/// definitions. Keywords (which include built-ins like `require`/`address`) and
/// definition names are excluded.
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
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
        // Bare call `name(...)` or constructor `new Type(...)`, not preceded by a
        // `.` (member) or a definition keyword.
        if is_ident_el(&els[i]) {
            let prev = if i > 0 { tok_text(&els[i - 1]) } else { None };
            let text = tok_text(&els[i]).unwrap_or("");
            let is_def = matches!(
                prev,
                Some("contract")
                    | Some("interface")
                    | Some("library")
                    | Some("struct")
                    | Some("enum")
                    | Some("event")
                    | Some("error")
                    | Some("function")
                    | Some("modifier")
            );
            if prev != Some(".") && !is_def && !is_keyword(text) && i + 1 < n {
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
    // Recurse into groups, but never into nested definitions.
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
        cst::CONTRACT
            | cst::INTERFACE
            | cst::LIBRARY
            | cst::STRUCT
            | cst::ENUM
            | cst::EVENT
            | cst::ERROR_DEF
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::solidity::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("Demo.sol", src);
        let file = SourceFile {
            rel_path: "contracts/Demo.sol".to_string(),
            module_path: vec!["contracts".to_string()],
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    fn call_edges(g: &Graph) -> Vec<&crate::graph::GraphEdge> {
        g.edges().filter(|e| e.kind == edge::CALLS).collect()
    }

    #[test]
    fn emits_type_function_module_nodes() {
        let g = graph_for("contract C {\n  function m() public {}\n  function f() public {}\n}");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "m + f");
        assert_eq!(g.count_nodes_of(ont::TYPE), 1, "contract C is a Type");
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "directory module");
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD));
    }

    #[test]
    fn type_kinds_are_honest() {
        for (src, kind) in [
            ("contract C {}", "contract"),
            ("interface I {}", "interface"),
            ("library L {}", "library"),
            ("struct S { uint x; }", "struct"),
            ("enum E { A }", "enum"),
            ("event Ev(uint x);", "event"),
            ("error Er(uint y);", "error"),
        ] {
            let g = graph_for(src);
            let ty = g
                .nodes()
                .find(|n| n.kind == ont::TYPE)
                .expect("a Type node");
            assert_eq!(
                ty.props.get("type_kind"),
                Some(&Json::str(kind)),
                "for {src}"
            );
            assert_eq!(ty.props.get("language"), Some(&Json::str("solidity")));
        }
    }

    #[test]
    fn resolves_same_contract_call() {
        let g = graph_for(
            "contract C {\n  function run() public { helper(); }\n  function helper() public {}\n}",
        );
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
        let g = graph_for(
            "contract P {\n  function a() public { this.b(); }\n  function b() public {}\n}",
        );
        let recv = call_edges(&g)
            .into_iter()
            .find(|e| e.props.get("resolution") == Some(&Json::str("receiver")));
        assert!(recv.is_some(), "this.b() resolves via receiver scope");
    }

    #[test]
    fn constructor_call_resolves() {
        let g = graph_for(
            "contract Widget {\n  constructor() {}\n}\ncontract Factory {\n  function make() public { new Widget(); }\n}",
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
        let g = graph_for("contract C { function run() public { mystery(); } }");
        let calls = call_edges(&g);
        assert!(calls
            .iter()
            .any(|e| e.props.get("resolution") == Some(&Json::str("external"))));
        assert!(g.has_node("unresolved::mystery"));
    }

    #[test]
    fn external_import_creates_dependency() {
        let g = graph_for(
            "import {IERC20} from \"@openzeppelin/contracts/token/IERC20.sol\";\ncontract C {}",
        );
        assert!(g.has_node("ext::@openzeppelin/contracts"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::@openzeppelin/contracts"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn relative_import_is_internal() {
        let g = graph_for("import \"./Helper.sol\";\ncontract C {}");
        let imp = g
            .edges()
            .find(|e| e.kind == edge::IMPORTS)
            .expect("an import edge");
        assert_eq!(imp.props.get("external"), Some(&Json::Bool(false)));
    }

    #[test]
    fn extends_and_implements_are_distinct() {
        let g = graph_for("interface I {}\ncontract Base {}\ncontract Derived is Base, I {}");
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
        assert!(imp.to.contains("type::") && imp.to.contains('I'));
    }

    #[test]
    fn state_vars_become_constants() {
        let g = graph_for(
            "contract C {\n  uint256 public constant CAP = 10;\n  address immutable owner;\n  uint256 count;\n}",
        );
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 3);
        let cap = g.nodes().find(|n| n.name == "CAP").expect("the CAP var");
        assert_eq!(cap.props.get("binding"), Some(&Json::str("constant")));
        let owner = g.nodes().find(|n| n.name == "owner").expect("owner");
        assert_eq!(owner.props.get("binding"), Some(&Json::str("immutable")));
        let count = g.nodes().find(|n| n.name == "count").expect("count");
        assert_eq!(count.props.get("binding"), Some(&Json::str("state_var")));
    }

    #[test]
    fn mapping_state_var_name_is_extracted() {
        let g = graph_for("contract C { mapping(address => uint256) public balances; }");
        assert!(
            g.nodes()
                .any(|n| n.kind == ont::CONSTANT && n.name == "balances"),
            "the mapping declares `balances`"
        );
    }

    #[test]
    fn receive_and_fallback_are_functions() {
        let g = graph_for("contract C { receive() external payable {} fallback() external {} }");
        let names: BTreeSet<String> = g
            .nodes()
            .filter(|n| n.kind == ont::FUNCTION)
            .map(|n| n.name.clone())
            .collect();
        assert!(
            names.contains("receive") && names.contains("fallback"),
            "got {names:?}"
        );
    }

    #[test]
    fn modifier_is_a_function_with_kind() {
        let g = graph_for("contract C { modifier onlyOwner() { _; } }");
        let m = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "onlyOwner")
            .expect("the modifier");
        assert_eq!(m.props.get("function_kind"), Some(&Json::str("modifier")));
    }

    #[test]
    fn type_use_in_signature() {
        let g = graph_for(
            "contract Widget {}\ncontract Factory {\n  function build(Widget w) public {}\n}",
        );
        assert!(
            g.edges()
                .any(|e| e.kind == edge::USES_TYPE && e.to.contains("Widget")),
            "parameter type should create USES_TYPE"
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src = "import \"./Base.sol\";\ncontract Base {}\ncontract C is Base {\n  function m() public { helper(); }\n  function helper() public {}\n}";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
