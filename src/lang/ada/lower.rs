//! Lower the Ada CST into the canonical graph.
//!
//! Honest mapping into the shared ontology:
//! - `package` / `package body` → [`MODULE`] (a scope); nested packages nest.
//! - `procedure` / `function` / `entry` → [`FUNCTION`].
//! - `type X is …` / `subtype X is …` → [`TYPE`] (distinguished by `type_kind`).
//! - `X : constant … := …` → [`CONSTANT`] (plain variables have no ontology node
//!   and are not emitted; their type references are still scanned).
//! - `with A.B.C;` → [`IMPORTS`] to an [`EXTERNAL_DEPENDENCY`] (+ a package
//!   `DEPENDS_ON`), unless the withed unit names a `Module` we built in this
//!   batch, in which case the import is internal.
//! - `X : T` declarations and subprogram signatures → [`USES_TYPE`] when `T`
//!   names a unique project type.
//!
//! Two conservative principles, identical to the other front ends:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to
//!    a concrete project subprogram only when a scope level yields candidates;
//!    several candidates → an ambiguous edge carrying the full `candidates` set.
//! 2. **The call/index ambiguity is never guessed.** Ada writes a subprogram
//!    call `P (args)` and an array index `A (i)` with the *same* syntax, and
//!    there is no `call` keyword to mark the former (unlike Fortran). So — as the
//!    Fortran front end does for that exact ambiguity — a `name (…)` reference is
//!    emitted as `CALLS` **only** when its name resolves to a known project
//!    subprogram; an unresolved reference is left out rather than fabricated.
//!    (This is why calls to library routines such as `Put_Line` produce no edge.)

use std::collections::BTreeMap;

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::ada::lexer::kind as tk;
use crate::lang::ada::parser::node as cst;
use crate::lang::frontend::SourceFile;

/// Lower a whole project's worth of Ada files into a graph.
pub fn lower(package: &str, files: &[SourceFile<'_>], manifest_deps: &[String]) -> Graph {
    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        fn_by_name: BTreeMap::new(),
        fn_by_scope: BTreeMap::new(),
        type_by_name: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id.clone(),
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("ada"))],
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

    let mut pend_calls: Vec<PendCall> = Vec::new();
    let mut pend_uses: Vec<PendUse> = Vec::new();
    let mut pend_withs: Vec<PendWith> = Vec::new();

    // Pass B: definition nodes + structural edges; build symbol tables.
    for f in files {
        let li = LineIndex::new(f.source);
        let file_id = format!("file::{}", f.rel_path);
        lo.g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("ada")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(pkg_id.clone(), edge::CONTAINS, file_id.clone(), vec![]);
        lo.walk_items(
            f.root,
            &file_id,
            &file_id,
            &[],
            f.source,
            &li,
            &mut pend_calls,
            &mut pend_uses,
            &mut pend_withs,
        );
    }

    // Pass C: imports (now every module node exists), calls, and type uses.
    for w in &pend_withs {
        lo.emit_with(w);
    }
    for pc in &pend_calls {
        let mut calls = Vec::new();
        scan_calls(pc.node, pc.source, &mut calls);
        for call in &calls {
            if let Some(res) = lo.resolve(call, &pc.scope) {
                lo.emit_call(&pc.from, call, res);
            }
        }
    }
    for pu in &pend_uses {
        lo.emit_type_uses(&pu.from, pu.node, pu.source);
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    /// Simple name (lowercase) → subprogram node ids (global level).
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// (scope_join_lc, name_lc) → subprogram node ids (local / qualified levels).
    fn_by_scope: BTreeMap<(String, String), Vec<String>>,
    /// Simple name (lowercase) → type node ids.
    type_by_name: BTreeMap<String, Vec<String>>,
}

struct PendCall<'a> {
    from: String,
    node: &'a Node,
    source: &'a str,
    scope: String,
}

struct PendUse<'a> {
    from: String,
    node: &'a Node,
    source: &'a str,
}

struct PendWith {
    file_id: String,
    full: String,
}

/// A detected `name (…)` / `pkg.name (…)` reference (call-or-index, resolved
/// conservatively against the subprogram tables).
struct Call {
    name: String,
    path: Vec<String>,
}

enum Outcome {
    One(String),
    Many(Vec<String>),
}

struct Resolution {
    outcome: Outcome,
    level: &'static str,
}

impl Lowerer {
    fn pkg_id(&self) -> String {
        format!("pkg::{}", self.package)
    }

    #[allow(clippy::too_many_arguments)]
    fn walk_items<'a>(
        &mut self,
        parent: &'a Node,
        file_id: &str,
        container_id: &str,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_calls: &mut Vec<PendCall<'a>>,
        pend_uses: &mut Vec<PendUse<'a>>,
        pend_withs: &mut Vec<PendWith>,
    ) {
        for item in parent.child_nodes() {
            match item.kind {
                cst::WITH_CLAUSE => {
                    if let Some(full) = dotted_clause_name(item, src) {
                        pend_withs.push(PendWith {
                            file_id: file_id.to_string(),
                            full,
                        });
                    }
                }
                cst::USE_CLAUSE => { /* visibility only — noted, no graph edge */ }
                cst::PACKAGE => self.handle_package(
                    item,
                    file_id,
                    container_id,
                    scope,
                    src,
                    li,
                    pend_calls,
                    pend_uses,
                    pend_withs,
                ),
                cst::PROCEDURE | cst::FUNCTION | cst::ENTRY => self.handle_subprogram(
                    item,
                    file_id,
                    container_id,
                    scope,
                    src,
                    li,
                    pend_calls,
                    pend_uses,
                    pend_withs,
                ),
                cst::TASK | cst::PROTECTED => self.handle_task_protected(
                    item,
                    file_id,
                    container_id,
                    scope,
                    src,
                    li,
                    pend_calls,
                    pend_uses,
                    pend_withs,
                ),
                cst::TYPE_DECL | cst::SUBTYPE_DECL => {
                    self.handle_type(item, container_id, scope, src, li, pend_uses)
                }
                cst::OBJECT_DECL => {
                    self.handle_object(item, container_id, scope, src, li, pend_uses)
                }
                cst::GENERIC => {
                    // The generic formals + the generic unit are lowered in place
                    // (no separate Generic node in the ontology).
                    self.walk_items(
                        item,
                        file_id,
                        container_id,
                        scope,
                        src,
                        li,
                        pend_calls,
                        pend_uses,
                        pend_withs,
                    )
                }
                _ => {}
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_package<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        container_id: &str,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_calls: &mut Vec<PendCall<'a>>,
        pend_uses: &mut Vec<PendUse<'a>>,
        pend_withs: &mut Vec<PendWith>,
    ) {
        let (display, segs) = match name_of(item, src) {
            Some(v) => v,
            None => return,
        };
        let mut child_scope = scope.to_vec();
        for s in &segs {
            child_scope.push(s.clone());
        }
        let mod_id = format!("mod::{}", scope_join_lc(&child_scope));
        self.g.upsert_node(
            mod_id.clone(),
            ont::MODULE,
            display,
            vec![("language", Json::str("ada"))],
        );
        self.g
            .add_edge(container_id, edge::CONTAINS, mod_id.clone(), vec![]);
        self.walk_items(
            item,
            file_id,
            &mod_id,
            &child_scope,
            src,
            li,
            pend_calls,
            pend_uses,
            pend_withs,
        );
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_task_protected<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        container_id: &str,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_calls: &mut Vec<PendCall<'a>>,
        pend_uses: &mut Vec<PendUse<'a>>,
        pend_withs: &mut Vec<PendWith>,
    ) {
        let (display, segs) = match name_of(item, src) {
            Some(v) => v,
            None => return,
        };
        let mut child_scope = scope.to_vec();
        for s in &segs {
            child_scope.push(s.clone());
        }
        let mod_id = format!("mod::{}", scope_join_lc(&child_scope));
        let kind = if item.kind == cst::TASK {
            "task"
        } else {
            "protected"
        };
        self.g.upsert_node(
            mod_id.clone(),
            ont::MODULE,
            display,
            vec![
                ("language", Json::str("ada")),
                ("module_kind", Json::str(kind)),
            ],
        );
        self.g
            .add_edge(container_id, edge::CONTAINS, mod_id.clone(), vec![]);
        self.walk_items(
            item,
            file_id,
            &mod_id,
            &child_scope,
            src,
            li,
            pend_calls,
            pend_uses,
            pend_withs,
        );
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_subprogram<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        container_id: &str,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_calls: &mut Vec<PendCall<'a>>,
        pend_uses: &mut Vec<PendUse<'a>>,
        pend_withs: &mut Vec<PendWith>,
    ) {
        let (display, mut segs) = match name_of(item, src) {
            Some(v) => v,
            None => return,
        };
        // A dotted child-unit name (`procedure Parent.Child`) contributes its
        // leading segments to the enclosing scope.
        let name = segs.pop().unwrap_or_else(|| display.clone());
        let name_lc = name.to_ascii_lowercase();
        let mut def_scope = scope.to_vec();
        for s in &segs {
            def_scope.push(s.clone());
        }
        // The scope in which this subprogram is *declared* (where its siblings
        // live) — this is also the resolution scope for its body, so a call to a
        // sibling subprogram resolves at the `local` level.
        let scope_join = scope_join_lc(&def_scope);
        let line = li.line_col(name_span_start(item)).line;
        let qual = if scope_join.is_empty() {
            name_lc.clone()
        } else {
            format!("{scope_join}.{name_lc}")
        };
        let id = format!("fn::{qual}#{line}");
        let kind = match item.kind {
            cst::FUNCTION => "function",
            cst::ENTRY => "entry",
            _ => "procedure",
        };
        let has_body = item.child(cst::BLOCK).is_some();
        self.g.upsert_node(
            id.clone(),
            ont::FUNCTION,
            name,
            vec![
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("ada")),
                ("subprogram_kind", Json::str(kind)),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
                ("has_body", Json::Bool(has_body)),
            ],
        );
        self.g
            .add_edge(container_id, edge::DECLARES, id.clone(), vec![]);
        self.fn_by_name
            .entry(name_lc.clone())
            .or_default()
            .push(id.clone());
        self.fn_by_scope
            .entry((scope_join.clone(), name_lc.clone()))
            .or_default()
            .push(id.clone());

        // Signature type uses.
        if let Some(sig) = item.child(cst::SIGNATURE) {
            pend_uses.push(PendUse {
                from: id.clone(),
                node: sig,
                source: src,
            });
        }
        // Call scan over the whole subprogram (nested definitions are skipped by
        // the scanner so their calls are attributed to them, not to this one).
        // Calls resolve against the enclosing scope (siblings) first, then
        // globally; the declarative part is a nested scope of its own.
        pend_calls.push(PendCall {
            from: id.clone(),
            node: item,
            source: src,
            scope: scope_join,
        });

        // Nested declarations (declarative part) are first-class, scoped under
        // this subprogram's own name.
        let mut body_scope = def_scope.clone();
        body_scope.push(name_lc);
        self.walk_items(
            item,
            file_id,
            &id,
            &body_scope,
            src,
            li,
            pend_calls,
            pend_uses,
            pend_withs,
        );
    }

    fn handle_type<'a>(
        &mut self,
        item: &'a Node,
        container_id: &str,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_uses: &mut Vec<PendUse<'a>>,
    ) {
        let (display, segs) = match name_of(item, src) {
            Some(v) => v,
            None => return,
        };
        let name = segs.last().cloned().unwrap_or_else(|| display.clone());
        let name_lc = name.to_ascii_lowercase();
        let scope_join = scope_join_lc(scope);
        let line = li.line_col(name_span_start(item)).line;
        let qual = if scope_join.is_empty() {
            name_lc.clone()
        } else {
            format!("{scope_join}.{name_lc}")
        };
        let id = format!("type::{qual}");
        let type_kind = if item.kind == cst::SUBTYPE_DECL {
            "subtype"
        } else {
            "type"
        };
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name,
            vec![
                ("type_kind", Json::str(type_kind)),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("ada")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
            ],
        );
        self.g
            .add_edge(container_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name
            .entry(name_lc)
            .or_default()
            .push(id.clone());
        if let Some(h) = item.child(cst::HEADER) {
            pend_uses.push(PendUse {
                from: id,
                node: h,
                source: src,
            });
        }
    }

    fn handle_object<'a>(
        &mut self,
        item: &'a Node,
        container_id: &str,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_uses: &mut Vec<PendUse<'a>>,
    ) {
        let (names, is_constant) = object_names(item, src);
        let scope_join = scope_join_lc(scope);
        let line = li.line_col(item.span.start).line;
        for name in names {
            if !is_constant {
                continue; // plain variables have no ontology node
            }
            let name_lc = name.to_ascii_lowercase();
            let qual = if scope_join.is_empty() {
                name_lc.clone()
            } else {
                format!("{scope_join}.{name_lc}")
            };
            let id = format!("const::{qual}");
            self.g.upsert_node(
                id.clone(),
                ont::CONSTANT,
                name,
                vec![
                    ("binding", Json::str("constant")),
                    ("language", Json::str("ada")),
                    ("line", Json::U64(line as u64)),
                ],
            );
            self.g
                .add_edge(container_id, edge::DECLARES, id.clone(), vec![]);
            pend_uses.push(PendUse {
                from: id,
                node: item,
                source: src,
            });
        }
    }

    // --- imports ------------------------------------------------------------

    fn emit_with(&mut self, w: &PendWith) {
        let full_lc = w.full.to_ascii_lowercase();
        let internal_id = format!("mod::{full_lc}");
        if self.g.has_node(&internal_id) {
            self.g.add_edge(
                w.file_id.clone(),
                edge::IMPORTS,
                internal_id,
                vec![
                    ("path", Json::str(w.full.clone())),
                    ("external", Json::Bool(false)),
                ],
            );
        } else {
            let dep_id = ext_id(&w.full);
            self.g.upsert_node(
                dep_id.clone(),
                ont::EXTERNAL_DEPENDENCY,
                w.full.clone(),
                vec![
                    ("external", Json::Bool(true)),
                    ("source", Json::str("with")),
                ],
            );
            self.g.add_edge(
                w.file_id.clone(),
                edge::IMPORTS,
                dep_id.clone(),
                vec![
                    ("path", Json::str(w.full.clone())),
                    ("external", Json::Bool(true)),
                ],
            );
            self.g
                .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
        }
    }

    // --- resolution ladder --------------------------------------------------

    /// Resolve a `name (…)` reference. Returns `None` when no project subprogram
    /// matches — the conservative signal that this is array indexing, a type
    /// conversion, or a call into a library (never fabricated as a call).
    fn resolve(&self, call: &Call, scope_join: &str) -> Option<Resolution> {
        let name_lc = call.name.to_ascii_lowercase();
        if call.path.is_empty() {
            if let Some(c) = self.fns_in_scope(scope_join, &name_lc) {
                return Some(mk(c, "local"));
            }
        } else {
            let q = call
                .path
                .iter()
                .map(|s| s.to_ascii_lowercase())
                .collect::<Vec<_>>()
                .join(".");
            if let Some(c) = self.fns_in_scope(&q, &name_lc) {
                return Some(mk(c, "qualified"));
            }
            let nested = if scope_join.is_empty() {
                q
            } else {
                format!("{scope_join}.{q}")
            };
            if let Some(c) = self.fns_in_scope(&nested, &name_lc) {
                return Some(mk(c, "qualified"));
            }
        }
        match self.fn_by_name.get(&name_lc) {
            Some(c) if !c.is_empty() => Some(mk(
                c.clone(),
                if call.path.is_empty() {
                    "global"
                } else {
                    "qualified"
                },
            )),
            _ => None,
        }
    }

    fn fns_in_scope(&self, scope_join: &str, name_lc: &str) -> Option<Vec<String>> {
        self.fn_by_scope
            .get(&(scope_join.to_string(), name_lc.to_string()))
            .filter(|c| !c.is_empty())
            .cloned()
    }

    fn emit_call(&mut self, caller_id: &str, call: &Call, res: Resolution) {
        let mut props = vec![
            ("callee", Json::str(call.name.clone())),
            ("resolution", Json::str(res.level)),
        ];
        if !call.path.is_empty() {
            props.push(("qualifier", Json::str(call.path.join("."))));
        }
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

    /// Add `USES_TYPE` edges for identifiers in `region` naming a unique project
    /// type (excluding the using node itself).
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

    fn unique_type(&self, name: &str) -> Option<String> {
        match self.type_by_name.get(&name.to_ascii_lowercase()) {
            Some(ids) if ids.len() == 1 => Some(ids[0].clone()),
            _ => None,
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

fn scope_join_lc(scope: &[String]) -> String {
    scope
        .iter()
        .map(|s| s.to_ascii_lowercase())
        .collect::<Vec<_>>()
        .join(".")
}

fn ext_id(name: &str) -> String {
    format!("ext::{name}")
}

fn unresolved_id(name: &str) -> String {
    format!("unresolved::{}", name.to_ascii_lowercase())
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

/// `(display_name, segments)` of a declaration's `Name` child. The display name
/// is the original-case dotted text; segments are the identifier parts (an
/// operator-string name yields a single segment).
fn name_of(item: &Node, src: &str) -> Option<(String, Vec<String>)> {
    let name = item.child(cst::NAME)?;
    let mut segs = Vec::new();
    let mut display = String::new();
    for t in name.tokens() {
        let text = t.span.text(src);
        match t.kind {
            tk::IDENT => {
                segs.push(text.to_string());
                display.push_str(text);
            }
            tk::STRING => {
                segs.push(text.to_string());
                display.push_str(text);
            }
            _ => display.push_str(text), // the dotted '.'
        }
    }
    if segs.is_empty() {
        None
    } else {
        Some((display, segs))
    }
}

fn name_span_start(item: &Node) -> u32 {
    item.child(cst::NAME)
        .map(|n| n.span.start)
        .unwrap_or(item.span.start)
}

/// From an `ObjectDecl`, the declared object names (the identifiers before the
/// first `:` that is not `:=`) and whether the declaration is `constant`.
fn object_names(item: &Node, src: &str) -> (Vec<String>, bool) {
    let mut names = Vec::new();
    let mut before_colon = true;
    let mut is_constant = false;
    for c in &item.children {
        let t = match c {
            Child::Token(t) if !t.trivia => t,
            _ => continue, // groups / trivia
        };
        let text = t.span.text(src);
        if before_colon {
            if t.kind == tk::IDENT {
                names.push(text.to_string());
            } else if text == ":" {
                before_colon = false;
            }
            // commas between names are skipped implicitly
        } else if t.kind == tk::IDENT && text.eq_ignore_ascii_case("constant") {
            is_constant = true;
        }
    }
    (names, is_constant)
}

/// The dotted unit name in a `with`/`use` clause (e.g. `Ada.Text_IO`).
fn dotted_clause_name(item: &Node, src: &str) -> Option<String> {
    let mut out = String::new();
    for t in item.tokens() {
        let text = t.span.text(src);
        if t.kind == tk::IDENT {
            if text.eq_ignore_ascii_case("with")
                || text.eq_ignore_ascii_case("use")
                || text.eq_ignore_ascii_case("type")
                || text.eq_ignore_ascii_case("all")
            {
                continue;
            }
            out.push_str(text);
        } else if text == "." {
            out.push('.');
        } else if text == "," || text == ";" {
            // First named unit only (multiple `with`s are rare; keep the first).
            break;
        }
    }
    let trimmed = out.trim_matches('.');
    if trimmed.is_empty() {
        None
    } else {
        Some(trimmed.to_string())
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

fn is_def_kind(k: &str) -> bool {
    matches!(
        k,
        cst::PACKAGE
            | cst::PROCEDURE
            | cst::FUNCTION
            | cst::TASK
            | cst::PROTECTED
            | cst::ENTRY
            | cst::GENERIC
    )
}

/// Detect `name (…)` and `prefix.name (…)` references over the real token tree.
/// A reference whose name is preceded by an attribute tick `'` or by `.` (i.e. a
/// continuation) is not started here; the qualifier chain is built only over `.`
/// connectors so an attribute never joins it. Recurses into every child node
/// except nested definitions (whose calls belong to their own scope).
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        if is_ident_el(&els[i]) {
            let prev = if i > 0 { tok_text(&els[i - 1]) } else { None };
            if prev != Some(".") && prev != Some("'") {
                let mut segs = vec![tok_text(&els[i]).unwrap_or("").to_string()];
                let mut j = i;
                while j + 2 < n && tok_text(&els[j + 1]) == Some(".") && is_ident_el(&els[j + 2]) {
                    segs.push(tok_text(&els[j + 2]).unwrap_or("").to_string());
                    j += 2;
                }
                if j + 1 < n {
                    if let El::Grp(g) = &els[j + 1] {
                        if g.kind == cst::PAREN {
                            let name = segs.pop().unwrap();
                            out.push(Call { name, path: segs });
                        }
                    }
                }
                i = j + 1;
                continue;
            }
        }
        i += 1;
    }
    for ch in node.child_nodes() {
        if !is_def_kind(ch.kind) {
            scan_calls(ch, src, out);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::ada::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("test.adb", src);
        let file = SourceFile {
            rel_path: "test.adb".to_string(),
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
    fn package_becomes_module_with_members() {
        let g = graph_for(
            "package P is\n   type T is range 1 .. 10;\n   K : constant T := 1;\n   \
             procedure Q;\nend P;\n",
        );
        assert!(g.has_node("mod::p"));
        assert!(g.has_node("type::p.t"));
        assert!(g.has_node("const::p.k"));
        assert!(g.nodes().any(|n| n.kind == ont::FUNCTION && n.name == "Q"));
    }

    #[test]
    fn resolved_local_call() {
        let g = graph_for(
            "package body P is\n   function A (X : Integer) return Integer is \
             begin return X; end A;\n   \
             function B (Y : Integer) return Integer is begin return A (Y); end B;\nend P;\n",
        );
        let calls = call_edges(&g);
        let a = calls
            .iter()
            .find(|e| e.to.starts_with("fn::p.a"))
            .expect("A (Y) should resolve to A");
        assert_eq!(a.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(a.props.get("resolution"), Some(&Json::str("local")));
    }

    #[test]
    fn array_index_is_not_a_call() {
        // `Arr (I)` resolves to no subprogram, so no CALLS edge is fabricated.
        let g = graph_for(
            "procedure P is\n   Arr : array (1 .. 3) of Integer;\n   I : Integer := 1;\n\
             begin\n   Arr (I) := 0;\nend P;\n",
        );
        assert!(
            call_edges(&g).is_empty(),
            "array indexing must not become a CALLS edge"
        );
    }

    #[test]
    fn with_clause_creates_external_dependency() {
        let g = graph_for("with Ada.Text_IO;\npackage P is end P;\n");
        assert!(g.has_node("ext::Ada.Text_IO"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::Ada.Text_IO"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::IMPORTS && e.to == "ext::Ada.Text_IO"));
    }

    #[test]
    fn signature_uses_project_type() {
        let g = graph_for(
            "package P is\n   type Money is digits 6;\n   \
             function Tax (Amount : Money) return Money;\nend P;\n",
        );
        let uses: Vec<_> = g.edges().filter(|e| e.kind == edge::USES_TYPE).collect();
        assert!(
            uses.iter().any(|e| e.to == "type::p.money"),
            "Tax's signature should USES_TYPE Money: {uses:?}"
        );
    }

    #[test]
    fn ambiguous_call_keeps_candidates() {
        // Two procedures named Go in different packages → global ambiguity.
        let g = graph_for(
            "package body P is\n   \
             procedure Go (A : Integer) is begin null; end Go;\n   \
             procedure Go (A : Float) is begin null; end Go;\n   \
             procedure Run is begin Go (1); end Run;\nend P;\n",
        );
        let amb = call_edges(&g)
            .into_iter()
            .find(|e| e.props.get("ambiguous") == Some(&Json::Bool(true)));
        assert!(amb.is_some(), "Go (1) is ambiguous across two overloads");
        assert_eq!(
            amb.unwrap().props.get("candidate_count"),
            Some(&Json::U64(2))
        );
    }
}
