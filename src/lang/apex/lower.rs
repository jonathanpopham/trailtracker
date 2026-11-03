//! Lower the Apex CST into the canonical graph. Forked from the Java lowering
//! ([`crate::lang::java::lower`]) — same conservative scope-ladder resolution and
//! shared ontology — adapted for Apex:
//!
//! Honest mappings:
//!   `class`/`interface`/`enum`/`@interface` → `Type` (distinguished by a
//!   `type_kind`); a `method`/constructor → `Function` (with `HAS_METHOD` from
//!   its enclosing `Type`); a field/property/enum-constant → `Constant`;
//!   `extends` → `EXTENDS`; `implements` → `IMPLEMENTS`. Annotations are recorded
//!   as an `annotations` property; a method annotated `@InvocableMethod` also
//!   gains `invocable: true` (so the TT-62 linker can resolve flow `actionCalls`
//!   to it).
//!
//! Apex-specific overlays:
//! - **Triggers** (`trigger T on SObject (…) { … }`) → a `Function` with
//!   `type_kind: "trigger"` plus a `USES_TYPE` edge to the `on` SObject. Its body
//!   is scanned for calls and inline SOQL like any method.
//! - **Inline SOQL/SOSL.** A second pass over the bracketed token trees inside
//!   each method/trigger body reads the `FROM`/`RETURNING` SObject and emits a
//!   `USES_TYPE` edge from the enclosing function to an `sobject::<Name>` node.
//!   That node id and kind match [`crate::lang::salesforce::lower`] exactly, so
//!   Apex and Salesforce metadata resolve to the **same** SObject node — the
//!   basis for cross-provider linking.

use std::collections::BTreeMap;

use crate::core::cst::{Child, Node, Token};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::apex::lexer::{is_keyword, kind as tk};
use crate::lang::apex::parser::node as cst;
use crate::lang::frontend::SourceFile;

/// Lower a whole project's worth of Apex files into a graph. `manifest_deps` is
/// unused for Apex (no Cargo-style manifest); Apex has a flat namespace.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        method_by_name: BTreeMap::new(),
        method_by_type: BTreeMap::new(),
        type_by_name: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("apex"))],
    );

    // Pass B: create definition nodes + structural edges and build symbol tables.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_ext: Vec<PendingSuper> = Vec::new();
    let mut pend_impl: Vec<PendingSuper> = Vec::new();
    for f in files {
        let li = LineIndex::new(f.source);
        let file_id = format!("file::{}", f.rel_path);
        lo.g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("apex")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(lo.pkg_id(), edge::CONTAINS, file_id.clone(), vec![]);
        lo.walk(
            f.root,
            &file_id,
            &[],
            None,
            f.source,
            &li,
            &mut pend_fns,
            &mut pend_ext,
            &mut pend_impl,
        );
    }

    // Pass C: resolve calls (scope ladder), type usages, inline SOQL/SOSL, and
    // supertypes against the now-complete symbol tables.
    for pf in &pend_fns {
        // Local variable types (params + body declarations) power both the
        // instance-call receiver ladder and DML SObject inference.
        let ctx = Ctx {
            owner_type: pf.owner_type.clone(),
            var_types: collect_var_types(pf.item, pf.source),
        };
        if let Some(block) = pf.item.child(cst::BLOCK) {
            let mut calls = Vec::new();
            scan_calls(block, pf.source, &mut calls);
            for call in &calls {
                let res = lo.resolve(call, &ctx);
                lo.emit_call(&pf.id, call, res);
            }
            lo.emit_soql_uses(&pf.id, block, pf.source);
            lo.emit_dml_uses(&pf.id, block, pf.source, &ctx);
        }
        lo.emit_type_uses(&pf.id, pf.item, pf.source);
    }
    for pe in &pend_ext {
        lo.emit_super(pe, edge::EXTENDS, "supertype");
    }
    for pe in &pend_impl {
        lo.emit_super(pe, edge::IMPLEMENTS, "interface");
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    method_by_name: BTreeMap<String, Vec<String>>,
    method_by_type: BTreeMap<(String, String), Vec<String>>,
    type_by_name: BTreeMap<String, Vec<String>>,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    item: &'a Node,
    owner_type: Option<String>,
}

struct PendingSuper {
    type_id: String,
    base_name: String,
}

struct Owner {
    name: String,
    id: String,
}

struct Call {
    name: String,
    method: bool,
    receiver: Option<String>,
    constructor: bool,
}

struct Ctx {
    owner_type: Option<String>,
    /// Local variable / parameter name → its declared (element) type name. Used
    /// to resolve `instance.method()` receivers and to infer the SObject a DML
    /// statement operates on.
    var_types: BTreeMap<String, String>,
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

    /// Ensure an `sobject::<Name>` node exists, byte-identical to the one the
    /// Salesforce metadata front end emits ([`crate::lang::salesforce::lower`]),
    /// so Apex references and metadata definitions resolve to the *same* node.
    fn ensure_sobject(&mut self, name: &str) -> String {
        let id = format!("sobject::{name}");
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.to_string(),
            vec![
                ("type_kind", Json::str("sobject")),
                ("language", Json::str("salesforce-metadata")),
            ],
        );
        id
    }

    #[allow(clippy::too_many_arguments)]
    fn walk<'a>(
        &mut self,
        container: &'a Node,
        file_id: &str,
        scope: &[String],
        owner: Option<&Owner>,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_ext: &mut Vec<PendingSuper>,
        pend_impl: &mut Vec<PendingSuper>,
    ) {
        for item in container.child_nodes() {
            if is_type_decl(item.kind) {
                self.handle_type(item, file_id, scope, src, li, pend_fns, pend_ext, pend_impl);
                continue;
            }
            match item.kind {
                cst::METHOD => self.handle_method(item, file_id, scope, owner, src, li, pend_fns),
                cst::FIELD => self.handle_field(item, file_id, scope, src, li),
                cst::TRIGGER => self.handle_trigger(item, file_id, src, li, pend_fns),
                _ => {}
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_type<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        scope: &[String],
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_ext: &mut Vec<PendingSuper>,
        pend_impl: &mut Vec<PendingSuper>,
    ) {
        let name = name_text(item, src).unwrap_or("<anonymous>").to_string();
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(scope, &name);
        let id = format!("type::{qual}");
        let type_kind = match item.kind {
            cst::CLASS => "class",
            cst::INTERFACE => "interface",
            cst::ENUM => "enum",
            _ => "annotation",
        };
        let mut props = vec![
            ("type_kind", Json::str(type_kind)),
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("apex")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
        ];
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

        let (extends, implements) = supertypes(item, src);
        for base in extends {
            pend_ext.push(PendingSuper {
                type_id: id.clone(),
                base_name: base,
            });
        }
        for iface in implements {
            pend_impl.push(PendingSuper {
                type_id: id.clone(),
                base_name: iface,
            });
        }

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
                &child_scope,
                Some(&owner),
                src,
                li,
                pend_fns,
                pend_ext,
                pend_impl,
            );
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_method<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        scope: &[String],
        owner: Option<&Owner>,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
    ) {
        let (name, name_start) = match method_name(item, src) {
            Some(n) => n,
            None => ("<anonymous>".to_string(), item.span.start),
        };
        let line = li.line_col(name_start).line;
        let qual = qual_name(scope, &name);
        let id = format!("fn::{qual}#{line}");
        let block = item.child(cst::BLOCK);
        let is_ctor = owner.map(|o| o.name == name).unwrap_or(false);
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("apex")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            ("has_body", Json::Bool(block.is_some())),
        ];
        if is_ctor {
            props.push(("is_constructor", Json::Bool(true)));
        }
        if has_modifier(item, src, "static") {
            props.push(("is_static", Json::Bool(true)));
        }
        if let Some(o) = owner {
            props.push(("receiver_type", Json::str(o.name.clone())));
            props.push(("is_method", Json::Bool(true)));
        }
        if let Some(a) = annotations(item, src) {
            props.push(("annotations", a));
        }
        // `@InvocableMethod`s are what flow `actionCalls` resolve to (TT-62).
        if has_annotation(item, src, "InvocableMethod") {
            props.push(("invocable", Json::Bool(true)));
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, name.clone(), props);
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);

        self.method_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());
        if let Some(o) = owner {
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
            item,
            owner_type: owner.map(|o| o.name.clone()),
        });
    }

    /// `trigger Name on SObject (events) { body }` → a `Function` with
    /// `type_kind: "trigger"`, a `USES_TYPE` to its SObject, and a body scanned
    /// for calls + inline SOQL in pass C.
    fn handle_trigger<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
    ) {
        let name = name_text(item, src).unwrap_or("<anonymous>").to_string();
        let line = li.line_col(name_span_start(item)).line;
        let id = format!("fn::{name}#{line}");
        let block = item.child(cst::BLOCK);
        let sobject = trigger_sobject(item, src);
        let mut props = vec![
            ("type_kind", Json::str("trigger")),
            ("qualified_name", Json::str(name.clone())),
            ("language", Json::str("apex")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            ("has_body", Json::Bool(block.is_some())),
        ];
        if let Some(obj) = &sobject {
            props.push(("sobject", Json::str(obj.clone())));
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, name.clone(), props);
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.method_by_name
            .entry(name.clone())
            .or_default()
            .push(id.clone());

        // The trigger's target object is a data dependency.
        if let Some(obj) = &sobject {
            let target = self.ensure_sobject(obj);
            self.g.add_edge(
                id.clone(),
                edge::USES_TYPE,
                target,
                vec![("via", Json::str("trigger_on"))],
            );
        }

        pend_fns.push(PendingFn {
            id,
            source: src,
            item,
            owner_type: None,
        });
    }

    fn handle_field(
        &mut self,
        item: &Node,
        file_id: &str,
        scope: &[String],
        src: &str,
        li: &LineIndex,
    ) {
        let binding = field_binding(item, src);
        for (name, start) in field_names(item, src) {
            let line = li.line_col(start).line;
            let qual = qual_name(scope, &name);
            let id = format!("const::{qual}");
            self.g.upsert_node(
                id.clone(),
                ont::CONSTANT,
                name,
                vec![
                    ("binding", Json::str(binding)),
                    ("language", Json::str("apex")),
                    ("line", Json::U64(line as u64)),
                ],
            );
            self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
        }
    }

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        if call.constructor {
            let c = self.methods_of(&call.name, &call.name);
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
            if matches!(call.receiver.as_deref(), Some("this") | Some("super")) {
                if let Some(owner) = &ctx.owner_type {
                    let c = self.methods_of(owner, &call.name);
                    if !c.is_empty() {
                        return mk(c, "receiver");
                    }
                }
            }
            // `OtherClass.method()` (static) or `instance.method()`: when the
            // receiver names a project type — directly, or via a local variable's
            // declared type — resolve against that type's methods. This is the
            // inter-class call edge.
            if let Some(recv) = &call.receiver {
                let c = self.methods_of(recv, &call.name);
                if !c.is_empty() {
                    return mk(c, "receiver_type");
                }
                if let Some(ty) = ctx.var_types.get(recv) {
                    let c = self.methods_of(ty, &call.name);
                    if !c.is_empty() {
                        return mk(c, "receiver_type");
                    }
                }
            }
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
        if let Some(owner) = &ctx.owner_type {
            let c = self.methods_of(owner, &call.name);
            if !c.is_empty() {
                return mk(c, "receiver");
            }
        }
        let c = self.global_methods(&call.name);
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

    fn emit_super(&mut self, pe: &PendingSuper, kind: &'static str, role: &'static str) {
        let target = match self.unique_type(&pe.base_name) {
            Some(id) => id,
            None => {
                let id = unresolved_id(&pe.base_name);
                self.ensure_unresolved(&id, &pe.base_name, role);
                id
            }
        };
        self.g.add_edge(
            pe.type_id.clone(),
            kind,
            target,
            vec![("base_name", Json::str(pe.base_name.clone()))],
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

    fn global_methods(&self, name: &str) -> Vec<String> {
        self.method_by_name.get(name).cloned().unwrap_or_default()
    }

    fn unique_type(&self, name: &str) -> Option<String> {
        match self.type_by_name.get(name) {
            Some(ids) if ids.len() == 1 => Some(ids[0].clone()),
            _ => None,
        }
    }

    /// `USES_TYPE` edges for identifiers in a method's signature regions naming a
    /// unique project type. Bodies are excluded — parity with the Java lowering.
    fn emit_type_uses(&mut self, from_id: &str, item: &Node, src: &str) {
        let mut seen: Vec<String> = Vec::new();
        for region in [cst::SIGNATURE, cst::PARAMS, cst::HEADER] {
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

    /// Second pass: walk the bracketed token trees in a method/trigger body,
    /// read the SObject each inline SOQL/SOSL query targets, and emit a
    /// `USES_TYPE` edge from the enclosing function to its `sobject::` node.
    fn emit_soql_uses(&mut self, from_id: &str, block: &Node, src: &str) {
        let mut seen: Vec<(String, &'static str)> = Vec::new();
        for n in block.walk() {
            if n.kind != cst::BRACKET {
                continue;
            }
            for (obj, via) in soql_sobjects(n, src) {
                if seen.iter().any(|(o, v)| o == &obj && *v == via) {
                    continue;
                }
                seen.push((obj.clone(), via));
                let target = self.ensure_sobject(&obj);
                self.g.add_edge(
                    from_id.to_string(),
                    edge::USES_TYPE,
                    target,
                    vec![("via", Json::str(via)), ("sobject", Json::str(obj))],
                );
            }
        }
    }

    /// DML pass: scan the body for `insert`/`update`/`delete`/`upsert` statements
    /// and `Database.insert(…)`-style calls, infer the SObject each operates on
    /// (from a `new Contact(…)` literal or a typed local/parameter), and emit a
    /// `USES_TYPE` edge from the enclosing function to the shared `sobject::<Name>`
    /// node with `op="insert"|"update"|"delete"|"upsert"`. Targets whose SObject
    /// cannot be determined are skipped — never fabricated.
    fn emit_dml_uses(&mut self, from_id: &str, block: &Node, src: &str, ctx: &Ctx) {
        let mut sites: Vec<(&'static str, String)> = Vec::new();
        scan_dml(block, src, &ctx.var_types, &mut sites);
        let mut seen: Vec<(&'static str, String)> = Vec::new();
        for (op, obj) in sites {
            if seen.iter().any(|(o, s)| *o == op && s == &obj) {
                continue;
            }
            seen.push((op, obj.clone()));
            let target = self.ensure_sobject(&obj);
            self.g.add_edge(
                from_id.to_string(),
                edge::USES_TYPE,
                target,
                vec![
                    ("op", Json::str(op)),
                    ("sobject", Json::str(obj)),
                    ("via", Json::str("dml")),
                ],
            );
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

/// `scope….name` — the dotted qualified name (Apex has a flat file namespace, so
/// the scope is just the enclosing-type chain).
fn qual_name(scope: &[String], name: &str) -> String {
    let mut parts: Vec<String> = scope.to_vec();
    parts.push(name.to_string());
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

fn name_text<'a>(item: &'a Node, src: &'a str) -> Option<&'a str> {
    let nm = item.child(cst::NAME)?;
    nm.tokens().next().map(|t| t.span.text(src))
}

fn name_span_start(item: &Node) -> u32 {
    item.child(cst::NAME)
        .map(|n| n.span.start)
        .unwrap_or(item.span.start)
}

/// True if a member carries a given top-level modifier keyword (case-insensitive).
fn has_modifier(item: &Node, src: &str, kw: &str) -> bool {
    item.tokens()
        .any(|t| t.span.text(src).eq_ignore_ascii_case(kw))
}

/// The SObject a trigger fires on: the identifier following `on` in the header.
fn trigger_sobject(item: &Node, src: &str) -> Option<String> {
    let header = item.child(cst::HEADER)?;
    let mut saw_on = false;
    for t in header.tokens() {
        let text = t.span.text(src);
        if saw_on && t.kind == tk::IDENT {
            return Some(text.to_string());
        }
        if text.eq_ignore_ascii_case("on") {
            saw_on = true;
        }
    }
    None
}

/// The method/constructor name and its byte offset: the last top-level identifier
/// in the `Signature`.
fn method_name(item: &Node, src: &str) -> Option<(String, u32)> {
    let sig = item.child(cst::SIGNATURE)?;
    let mut last: Option<(String, u32)> = None;
    let mut angle: i32 = 0;
    for t in sig.tokens() {
        let text = t.span.text(src);
        if angle == 0 && t.kind == tk::IDENT && !is_keyword(text) {
            last = Some((text.to_string(), t.span.start));
        }
        angle += angle_delta(text);
        if angle < 0 {
            angle = 0;
        }
    }
    last
}

/// Declared field names (and offsets) from a member's `Signature`.
fn field_names(item: &Node, src: &str) -> Vec<(String, u32)> {
    match item.child(cst::SIGNATURE) {
        Some(sig) => decl_names(sig, src),
        None => Vec::new(),
    }
}

fn decl_names(node: &Node, src: &str) -> Vec<(String, u32)> {
    let toks: Vec<&Token> = node
        .children
        .iter()
        .filter_map(|c| match c {
            Child::Token(t) if !t.trivia => Some(t),
            _ => None,
        })
        .collect();
    let mut out = Vec::new();
    let mut angle: i32 = 0;
    for (k, t) in toks.iter().enumerate() {
        let text = t.span.text(src);
        if angle == 0 && t.kind == tk::IDENT && !is_keyword(text) {
            let is_name = matches!(
                toks.get(k + 1).map(|n| n.span.text(src)),
                None | Some(",") | Some("=") | Some("[") | Some(")")
            );
            if is_name {
                out.push((text.to_string(), t.span.start));
            }
        }
        angle += angle_delta(text);
        if angle < 0 {
            angle = 0;
        }
    }
    out
}

/// Classify a field/property's value binding from its modifiers.
fn field_binding(item: &Node, src: &str) -> &'static str {
    let is_static = has_modifier(item, src, "static");
    let is_final = has_modifier(item, src, "final");
    match (is_static, is_final) {
        (true, true) => "constant",
        (true, false) => "static_field",
        (false, true) => "final_field",
        (false, false) => "field",
    }
}

/// Annotation simple names attached to a declaration, as a JSON array property,
/// or `None` when there are none.
fn annotations(item: &Node, src: &str) -> Option<Json> {
    let mut names: Vec<Json> = Vec::new();
    for ann in item.children_of(cst::ANNOTATION) {
        if let Some(n) = annotation_name(ann, src) {
            names.push(Json::str(n.to_string()));
        }
    }
    if names.is_empty() {
        None
    } else {
        Some(Json::Array(names))
    }
}

/// The simple name of a single annotation (last non-keyword identifier).
fn annotation_name<'a>(ann: &'a Node, src: &'a str) -> Option<&'a str> {
    let mut last: Option<&str> = None;
    for t in ann.tokens() {
        if t.kind == tk::IDENT && !is_keyword(t.span.text(src)) {
            last = Some(t.span.text(src));
        }
    }
    last
}

/// Whether a declaration carries an annotation with the given simple name
/// (case-insensitive).
fn has_annotation(item: &Node, src: &str, name: &str) -> bool {
    item.children_of(cst::ANNOTATION)
        .filter_map(|a| annotation_name(a, src))
        .any(|n| n.eq_ignore_ascii_case(name))
}

/// Simple supertype names from a type's `Header`: `(extends, implements)`.
/// Keyword matching is case-insensitive (Apex). Angle-bracket depth keeps a
/// generic argument from being read as structure.
fn supertypes(item: &Node, src: &str) -> (Vec<String>, Vec<String>) {
    let mut ext: Vec<String> = Vec::new();
    let mut impls: Vec<String> = Vec::new();
    let header = match item.child(cst::HEADER) {
        Some(h) => h,
        None => return (ext, impls),
    };
    let mut mode = 0i32; // 0 none, 1 extends, 2 implements
    let mut angle: i32 = 0;
    let mut last: Option<String> = None;
    for t in header.tokens() {
        let text = t.span.text(src);
        if angle == 0 {
            if text.eq_ignore_ascii_case("extends") {
                commit(&mut last, mode, &mut ext, &mut impls);
                mode = 1;
            } else if text.eq_ignore_ascii_case("implements") {
                commit(&mut last, mode, &mut ext, &mut impls);
                mode = 2;
            } else if text == "," {
                commit(&mut last, mode, &mut ext, &mut impls);
            } else if t.kind == tk::IDENT && !is_keyword(text) {
                last = Some(text.to_string());
            }
        }
        angle += angle_delta(text);
        if angle < 0 {
            angle = 0;
        }
    }
    commit(&mut last, mode, &mut ext, &mut impls);
    (ext, impls)
}

fn commit(last: &mut Option<String>, mode: i32, ext: &mut Vec<String>, impls: &mut Vec<String>) {
    if let Some(n) = last.take() {
        match mode {
            1 => ext.push(n),
            2 => impls.push(n),
            _ => {}
        }
    }
}

fn angle_delta(text: &str) -> i32 {
    let mut d = 0i32;
    for c in text.chars() {
        match c {
            '<' => d += 1,
            '>' => d -= 1,
            _ => {}
        }
    }
    d
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

/// The SObject(s) an inline SOQL/SOSL query targets. A `Bracket` group starting
/// with `SELECT` is SOQL (object follows a top-level `FROM`, plus the FROM of
/// any semi-join sub-select in the WHERE clause — see [`select_from_targets`]);
/// one starting with `FIND` is SOSL (objects follow `RETURNING`, each as
/// `Object(fields)`). Any other bracket (array/list indexing) yields nothing.
fn soql_sobjects(bracket: &Node, src: &str) -> Vec<(String, &'static str)> {
    let els = significant_children(bracket, src);
    // Skip the `[`/`]` delimiter tokens: the query keyword is the first *ident*.
    let first = els.iter().filter(|e| is_ident_el(e)).find_map(tok_text);
    match first {
        Some(t) if t.eq_ignore_ascii_case("select") => {
            let mut out = Vec::new();
            select_from_targets(&els, src, &mut out);
            out.into_iter().map(|o| (o, "soql")).collect()
        }
        Some(t) if t.eq_ignore_ascii_case("find") => {
            let mut out = Vec::new();
            let mut after = false;
            for i in 0..els.len() {
                if tok_text(&els[i])
                    .map(|t| t.eq_ignore_ascii_case("returning"))
                    .unwrap_or(false)
                {
                    after = true;
                    continue;
                }
                if after && is_ident_el(&els[i]) {
                    let followed_by_paren = els
                        .get(i + 1)
                        .and_then(grp)
                        .map(|g| g.kind == cst::PAREN)
                        .unwrap_or(false);
                    if followed_by_paren {
                        out.push((tok_text(&els[i]).unwrap_or("").to_string(), "sosl"));
                    }
                }
            }
            out
        }
        _ => Vec::new(),
    }
}

/// The SObject names a SELECT token stream queries. The identifier after each
/// top-level `FROM` is one. Parenthesized sub-selects are position-sensitive:
/// *before* the top-level `FROM` (i.e. in the field list) they are
/// child-relationship queries whose FROM names a **relationship** (`Contacts`),
/// not an SObject — never lifted, never guessed. *After* it (WHERE/HAVING) they
/// are semi-joins whose FROM names a real SObject — recursed into, same rule
/// applying at each depth.
fn select_from_targets(els: &[El], src: &str, out: &mut Vec<String>) {
    let mut after_from = false;
    for i in 0..els.len() {
        if tok_text(&els[i])
            .map(|t| t.eq_ignore_ascii_case("from"))
            .unwrap_or(false)
        {
            after_from = true;
            if let Some(next) = els.get(i + 1) {
                if is_ident_el(next) {
                    out.push(tok_text(next).unwrap_or("").to_string());
                }
            }
        } else if after_from {
            if let Some(g) = grp(&els[i]) {
                if g.kind == cst::PAREN {
                    let inner = significant_children(g, src);
                    let head = inner.iter().filter(|e| is_ident_el(e)).find_map(tok_text);
                    if head
                        .map(|t| t.eq_ignore_ascii_case("select"))
                        .unwrap_or(false)
                    {
                        select_from_targets(&inner, src, out);
                    }
                }
            }
        }
    }
}

/// Detect `name(...)`, `recv.name(...)`, and `new Type(...)` call sites over the
/// real token tree, recursing into nested groups but **not** into nested
/// type/method definitions or inline SOQL/SOSL brackets (those are handled by the
/// dedicated SOQL pass, so aggregate functions like `COUNT()` are not mistaken
/// for calls).
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        if tok_text(&els[i]) == Some(".") {
            // A keyword after `.` is never a method name — notably `Database.insert(…)`
            // (DML, handled by the DML pass), not a call to a method named `insert`.
            let callee_kw = els
                .get(i + 1)
                .and_then(tok_text)
                .map(is_keyword)
                .unwrap_or(false);
            if i + 2 < n && is_ident_el(&els[i + 1]) && !callee_kw {
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
        if is_ident_el(&els[i]) {
            let prev = if i > 0 { tok_text(&els[i - 1]) } else { None };
            let text = tok_text(&els[i]).unwrap_or("");
            let is_def = matches!(
                prev.map(|p| p.to_ascii_lowercase()).as_deref(),
                Some("class") | Some("interface") | Some("enum")
            );
            let is_new = prev.map(|p| p.eq_ignore_ascii_case("new")).unwrap_or(false);
            if prev != Some(".") && prev != Some("@") && !is_def && !is_keyword(text) && i + 1 < n {
                if let Some(g) = grp(&els[i + 1]) {
                    if g.kind == cst::PAREN {
                        out.push(Call {
                            name: text.to_string(),
                            method: false,
                            receiver: None,
                            constructor: is_new,
                        });
                    }
                }
            }
        }
        i += 1;
    }
    for e in &els {
        if let Some(g) = grp(e) {
            if !is_definition_node(g.kind) && g.kind != cst::BRACKET {
                scan_calls(g, src, out);
            }
        }
    }
}

fn is_definition_node(kind: &str) -> bool {
    is_type_decl(kind) || kind == cst::METHOD || kind == cst::TRIGGER
}

fn is_type_decl(kind: &str) -> bool {
    matches!(
        kind,
        cst::CLASS | cst::INTERFACE | cst::ENUM | cst::ANNOTATION_TYPE
    )
}

// --- local variable typing + DML detection ----------------------------------

/// Build a `variable → declared (element) type` map for one method/trigger from
/// its parameter list and body declarations. For a collection the *element* type
/// is stored (`List<Case> cases` → `Case`), since that is what DML operates on
/// and what a for-each variable ranges over. First declaration of a name wins.
fn collect_var_types(item: &Node, src: &str) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    if let Some(params) = item.child(cst::PARAMS) {
        collect_decls(params, src, &mut out);
    }
    if let Some(block) = item.child(cst::BLOCK) {
        collect_decls(block, src, &mut out);
    }
    out
}

/// Walk a group's token stream (recursing into nested `{…}`/`(…)` but not into
/// SOQL brackets or nested definitions) collecting `Type var` declarations at
/// statement boundaries — locals, for-each variables, and parameters.
fn collect_decls(node: &Node, src: &str, out: &mut BTreeMap<String, String>) {
    let els = significant_children(node, src);
    let mut boundary = true;
    for i in 0..els.len() {
        if boundary {
            if let Some((var, ty)) = decl_at(&els, i) {
                out.entry(var).or_insert(ty);
            }
        }
        boundary = is_stmt_boundary(&els[i]);
    }
    for e in &els {
        if let Some(g) = grp(e) {
            if !is_definition_node(g.kind) && g.kind != cst::BRACKET {
                collect_decls(g, src, out);
            }
        }
    }
}

/// A token that opens a new statement/clause, so the identifier after it may be a
/// declarator. A nested block (`{…}`) also ends the previous statement.
fn is_stmt_boundary(e: &El) -> bool {
    match e {
        El::Tok { text, .. } => matches!(*text, ";" | "{" | "}" | "," | "("),
        El::Grp(n) => n.kind == cst::BRACE,
    }
}

/// Parse a `Type var` declaration starting at `els[i]`: an identifier type head
/// (with an optional `<…>` generic), then an identifier variable name, then a
/// declaration terminator (`=`, `;`, `:`, `,`, or end). Returns `(var, type)`
/// where `type` is the last identifier of the type expression (the element type
/// of a collection). `None` when the shape is not a declaration.
fn decl_at(els: &[El], i: usize) -> Option<(String, String)> {
    let head = els.get(i)?;
    if !is_ident_el(head) {
        return None;
    }
    let head_text = tok_text(head)?;
    if is_keyword(head_text) {
        return None;
    }
    let mut last_type = head_text.to_string();
    let mut j = i + 1;
    // Optional generic `<…>`: track angle depth over tokens; the last identifier
    // inside becomes the element type (`List<Case>` → `Case`).
    if els.get(j).and_then(tok_text) == Some("<") {
        let mut depth = 0i32;
        while j < els.len() {
            let t = tok_text(&els[j])?; // a group inside a type is not a declaration
            depth += angle_delta(t);
            if is_ident_el(&els[j]) && !is_keyword(t) {
                last_type = t.to_string();
            }
            j += 1;
            if depth <= 0 {
                break;
            }
        }
    }
    let var = els.get(j)?;
    if !is_ident_el(var) {
        return None;
    }
    let var_text = tok_text(var)?;
    if is_keyword(var_text) {
        return None;
    }
    let term_ok = match els.get(j + 1).and_then(tok_text) {
        None => els.get(j + 1).is_none(), // true only at genuine end-of-group
        Some(t) => matches!(t, "=" | ";" | ":" | "," | ")"),
    };
    if !term_ok {
        return None;
    }
    Some((var_text.to_string(), last_type))
}

/// The canonical DML op for a token, or `None` when it is not a DML keyword.
fn dml_op(text: &str) -> Option<&'static str> {
    ["insert", "update", "delete", "upsert"]
        .into_iter()
        .find(|op| text.eq_ignore_ascii_case(op))
}

/// Scan a body for DML — statement forms (`insert x;`) and `Database.<op>(arg)`
/// calls — inferring the SObject each operates on into `out` as `(op, sobject)`.
/// Recurses into nested groups but not SOQL brackets or nested definitions.
fn scan_dml(
    node: &Node,
    src: &str,
    vars: &BTreeMap<String, String>,
    out: &mut Vec<(&'static str, String)>,
) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        // `Database.<op>( arg, … )`.
        if is_ident_el(&els[i])
            && tok_text(&els[i]).is_some_and(|t| t.eq_ignore_ascii_case("Database"))
            && els.get(i + 1).and_then(tok_text) == Some(".")
        {
            if let Some(op) = els.get(i + 2).and_then(tok_text).and_then(dml_op) {
                if let Some(g) = els.get(i + 3).and_then(grp) {
                    if g.kind == cst::PAREN {
                        let args = significant_children(g, src);
                        if let Some(obj) = infer_sobject(first_arg_slice(&args), vars) {
                            out.push((op, obj));
                        }
                        i += 4;
                        continue;
                    }
                }
            }
        }
        // Statement DML: `insert x;` (the keyword not part of `Database.insert`).
        if let Some(op) = tok_text(&els[i]).and_then(dml_op) {
            let prev = if i > 0 { tok_text(&els[i - 1]) } else { None };
            if prev != Some(".") {
                let mut j = i + 1;
                while j < n && tok_text(&els[j]) != Some(";") {
                    j += 1;
                }
                if let Some(obj) = infer_sobject(&els[i + 1..j], vars) {
                    out.push((op, obj));
                }
                i = j;
                continue;
            }
        }
        i += 1;
    }
    for e in &els {
        if let Some(g) = grp(e) {
            if !is_definition_node(g.kind) && g.kind != cst::BRACKET {
                scan_dml(g, src, vars, out);
            }
        }
    }
}

/// The first argument of a delimited group's flattened children: skip the leading
/// `(` delimiter and stop at the first top-level `,` or the closing `)`.
fn first_arg_slice<'a, 'b>(args: &'b [El<'a>]) -> &'b [El<'a>] {
    let start = usize::from(args.first().and_then(tok_text) == Some("("));
    let mut end = start;
    while end < args.len() {
        match tok_text(&args[end]) {
            Some(")") | Some(",") => break,
            _ => end += 1,
        }
    }
    &args[start..end]
}

/// Infer the SObject a DML operand targets: `new Contact(…)` / `new List<Contact>{…}`
/// → the last type identifier before the group; a lone variable → its declared
/// type from `vars`. `None` when it cannot be determined (never fabricated).
fn infer_sobject(operand: &[El], vars: &BTreeMap<String, String>) -> Option<String> {
    let first = operand.first()?;
    let ftext = tok_text(first)?;
    if ftext.eq_ignore_ascii_case("new") {
        let mut last: Option<String> = None;
        for e in &operand[1..] {
            if grp(e).is_some() {
                break;
            }
            if is_ident_el(e) {
                if let Some(t) = tok_text(e) {
                    if !is_keyword(t) {
                        last = Some(t.to_string());
                    }
                }
            }
        }
        return last;
    }
    if is_ident_el(first) && !is_keyword(ftext) {
        let lone = operand.len() == 1 || operand.get(1).and_then(tok_text) != Some(".");
        if lone {
            return vars.get(ftext).cloned();
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::apex::parser::parse;

    fn graph_for(src: &str) -> Graph {
        graph_for_path("classes/Demo.cls", src)
    }

    fn graph_for_path(rel: &str, src: &str) -> Graph {
        let tree = parse(rel, src);
        let file = SourceFile {
            rel_path: rel.to_string(),
            module_path: Vec::new(),
            source: &tree.source,
            root: &tree.root,
        };
        lower("apexorg", std::slice::from_ref(&file), &[])
    }

    fn call_edges(g: &Graph) -> Vec<&crate::graph::GraphEdge> {
        g.edges().filter(|e| e.kind == edge::CALLS).collect()
    }

    #[test]
    fn class_and_method_are_lowered() {
        let g = graph_for(
            "public with sharing class C {\n  public void m() {}\n  public void f() {}\n}",
        );
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "m + f");
        assert_eq!(g.count_nodes_of(ont::TYPE), 1, "class C is a Type");
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD));
        let ty = g.nodes().find(|n| n.kind == ont::TYPE).unwrap();
        assert_eq!(ty.props.get("type_kind"), Some(&Json::str("class")));
        assert_eq!(ty.props.get("language"), Some(&Json::str("apex")));
    }

    #[test]
    fn type_kinds_are_honest() {
        for (src, kind) in [
            ("class C {}", "class"),
            ("interface I {}", "interface"),
            ("enum E { A }", "enum"),
        ] {
            let g = graph_for(src);
            let ty = g.nodes().find(|n| n.kind == ont::TYPE).expect("a Type");
            assert_eq!(
                ty.props.get("type_kind"),
                Some(&Json::str(kind)),
                "for {src}"
            );
        }
    }

    #[test]
    fn trigger_is_parsed_and_lowered() {
        let g = graph_for_path(
            "triggers/CaseTrigger.trigger",
            "trigger CaseTrigger on Case (before insert, after update) {\n  System.debug('hi');\n}",
        );
        let trig = g
            .nodes()
            .find(|n| n.props.get("type_kind") == Some(&Json::str("trigger")))
            .expect("a trigger Function node");
        assert_eq!(trig.kind, ont::FUNCTION);
        assert_eq!(trig.name, "CaseTrigger");
        // The `on Case` target becomes an sobject USES_TYPE edge.
        assert!(g.has_node("sobject::Case"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::USES_TYPE && e.to == "sobject::Case"));
    }

    #[test]
    fn inline_soql_emits_uses_type_to_sobject() {
        let g = graph_for(
            "public class C {\n  public void run() {\n    List<Contact> cs = [SELECT Id FROM Contact WHERE Name = 'x'];\n  }\n}",
        );
        // The sobject node id matches the Salesforce provider's convention.
        assert!(
            g.has_node("sobject::Contact"),
            "sobject::Contact must exist"
        );
        let sobj = g.nodes().find(|n| n.id == "sobject::Contact").unwrap();
        assert_eq!(sobj.kind, ont::TYPE);
        assert_eq!(sobj.props.get("type_kind"), Some(&Json::str("sobject")));
        let uses: Vec<_> = g
            .edges()
            .filter(|e| e.kind == edge::USES_TYPE && e.to == "sobject::Contact")
            .collect();
        assert_eq!(uses.len(), 1, "one SOQL USES_TYPE edge");
        assert_eq!(uses[0].props.get("via"), Some(&Json::str("soql")));
    }

    #[test]
    fn soql_with_where_bind_and_custom_object() {
        let g = graph_for(
            "public class C {\n  public void run(Id pid) {\n    List<Case__c> cs = [SELECT Id FROM Case__c WHERE Patient__c = :pid AND Status__c != 'Closed'];\n  }\n}",
        );
        assert!(g.has_node("sobject::Case__c"), "custom __c object lifted");
        assert!(g.edges().any(|e| e.kind == edge::USES_TYPE
            && e.to == "sobject::Case__c"
            && e.props.get("via") == Some(&Json::str("soql"))));
    }

    #[test]
    fn soql_from_with_alias() {
        let g = graph_for(
            "public class C {\n  public void run() {\n    Integer n = [SELECT COUNT() FROM Opportunity o WHERE o.StageName = 'Won'];\n  }\n}",
        );
        assert!(g.has_node("sobject::Opportunity"), "aliased FROM lifted");
    }

    #[test]
    fn soql_multiline_query_is_lifted() {
        let g = graph_for(
            "public class C {\n  public void run() {\n    List<Referral__c> rs = [\n      SELECT Id, Patient__c\n      FROM Referral__c\n      WHERE Status__c = 'New'\n      ORDER BY CreatedDate DESC\n      LIMIT 10\n    ];\n  }\n}",
        );
        assert!(g.has_node("sobject::Referral__c"));
    }

    #[test]
    fn child_relationship_subquery_is_not_an_sobject() {
        // `(SELECT … FROM Contacts)` in the field list names a *relationship*,
        // not an SObject — only the outer `FROM Account` may be lifted.
        let g = graph_for(
            "public class C {\n  public void run() {\n    List<Account> a = [SELECT Id, (SELECT LastName FROM Contacts) FROM Account];\n  }\n}",
        );
        assert!(g.has_node("sobject::Account"), "outer object lifted");
        assert!(
            !g.has_node("sobject::Contacts"),
            "relationship name must never be minted as an sobject"
        );
    }

    #[test]
    fn semi_join_subquery_lifts_inner_sobject() {
        // A WHERE-clause sub-select names a real SObject — both are lifted.
        let g = graph_for(
            "public class C {\n  public void run() {\n    List<Account> a = [SELECT Id FROM Account WHERE Id IN (SELECT AccountId FROM Contact WHERE Active__c = true)];\n  }\n}",
        );
        assert!(g.has_node("sobject::Account"));
        assert!(g.has_node("sobject::Contact"), "semi-join inner object");
        for obj in ["sobject::Account", "sobject::Contact"] {
            assert!(
                g.edges().any(|e| e.kind == edge::USES_TYPE
                    && e.to == obj
                    && e.props.get("via") == Some(&Json::str("soql"))),
                "USES_TYPE via soql to {obj}"
            );
        }
    }

    #[test]
    fn invocable_method_is_flagged() {
        let g = graph_for(
            "public class Handler {\n  @InvocableMethod(label='Go')\n  public static void go(List<Id> ids) {\n    List<Contact> cs = [SELECT Id FROM Contact];\n  }\n}",
        );
        let go = g.nodes().find(|n| n.name == "go").expect("the go method");
        assert_eq!(go.props.get("invocable"), Some(&Json::Bool(true)));
        // Annotations are recorded too.
        assert!(go.props.contains_key("annotations"));
        // And its inline SOQL still resolves to the shared sobject node.
        assert!(g.has_node("sobject::Contact"));
    }

    #[test]
    fn array_index_is_not_soql() {
        let g = graph_for("public class C { public void m() { Integer x = arr[0]; } }");
        assert!(
            !g.nodes().any(|n| n.id.starts_with("sobject::")),
            "list/array indexing must not create sobject nodes"
        );
    }

    #[test]
    fn fields_become_constants() {
        let g = graph_for(
            "public class C {\n  static final Integer MAX = 10;\n  private Integer count;\n}",
        );
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 2);
        let max = g.nodes().find(|n| n.name == "MAX").expect("MAX");
        assert_eq!(max.props.get("binding"), Some(&Json::str("constant")));
    }

    #[test]
    fn extends_and_implements_are_distinct() {
        let g = graph_for(
            "public interface I {}\npublic virtual class Base {}\npublic class Derived extends Base implements I {}",
        );
        assert!(g
            .edges()
            .any(|e| e.kind == edge::EXTENDS && e.to.contains("Base")));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::IMPLEMENTS && e.to.contains("I")));
    }

    #[test]
    fn resolves_same_type_call() {
        let g = graph_for("public class C {\n  void run() { helper(); }\n  void helper() {}\n}");
        let h = call_edges(&g)
            .into_iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("helper")))
            .expect("a call to helper");
        assert_eq!(h.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(h.props.get("resolution"), Some(&Json::str("receiver")));
    }

    #[test]
    fn resolves_cross_class_static_call() {
        // `B.work()` from class A resolves to B's method via the receiver-type
        // rung of the ladder — an inter-class CALLS edge.
        let g = graph_for(
            "public class A {\n  void go() { B.work(); }\n}\npublic class B {\n  public static void work() {}\n}",
        );
        let e = call_edges(&g)
            .into_iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("work")))
            .expect("a call to work");
        assert_eq!(e.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(e.props.get("resolution"), Some(&Json::str("receiver_type")));
        assert!(e.to.contains("B.work"), "targets B's method: {}", e.to);
    }

    #[test]
    fn resolves_cross_class_instance_call() {
        // `b.work()` where `b` is a `B`-typed local resolves through the variable's
        // declared type.
        let g = graph_for(
            "public class A {\n  void go() { B b = new B(); b.work(); }\n}\npublic class B {\n  public void work() {}\n}",
        );
        let e = call_edges(&g)
            .into_iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("work")))
            .expect("a call to work");
        assert_eq!(e.props.get("resolution"), Some(&Json::str("receiver_type")));
        assert!(e.to.contains("B.work"), "targets B's method: {}", e.to);
    }

    #[test]
    fn dml_insert_new_emits_uses_type_op_insert() {
        let g = graph_for(
            "public class C {\n  public void m() {\n    insert new Contact(LastName = 'x');\n  }\n}",
        );
        assert!(g.has_node("sobject::Contact"));
        let dml: Vec<_> = g
            .edges()
            .filter(|e| e.kind == edge::USES_TYPE && e.to == "sobject::Contact")
            .filter(|e| e.props.get("via") == Some(&Json::str("dml")))
            .collect();
        assert_eq!(dml.len(), 1, "one DML USES_TYPE edge");
        assert_eq!(dml[0].props.get("op"), Some(&Json::str("insert")));
    }

    #[test]
    fn dml_update_typed_variable_emits_op_update() {
        // `k` is declared as a `Case`; `update k;` resolves to sobject::Case.
        let g = graph_for("public class C {\n  public void m(Case k) {\n    update k;\n  }\n}");
        assert!(g.has_node("sobject::Case"));
        let dml = g
            .edges()
            .find(|e| {
                e.kind == edge::USES_TYPE
                    && e.to == "sobject::Case"
                    && e.props.get("via") == Some(&Json::str("dml"))
            })
            .expect("a DML update edge to sobject::Case");
        assert_eq!(dml.props.get("op"), Some(&Json::str("update")));
    }

    #[test]
    fn dml_database_call_emits_uses_type() {
        // `Database.insert(c)` (c: Contact) is DML, not a call to a `insert` method.
        let g = graph_for(
            "public class C {\n  public void m() {\n    Contact c = new Contact();\n    Database.insert(c);\n  }\n}",
        );
        let dml = g
            .edges()
            .find(|e| {
                e.kind == edge::USES_TYPE
                    && e.to == "sobject::Contact"
                    && e.props.get("via") == Some(&Json::str("dml"))
            })
            .expect("a DML edge to sobject::Contact");
        assert_eq!(dml.props.get("op"), Some(&Json::str("insert")));
        // And no spurious CALLS edge to an `insert` method.
        assert!(
            !call_edges(&g)
                .iter()
                .any(|e| e.props.get("callee") == Some(&Json::str("insert"))),
            "Database.insert must not be a method call"
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src = "public class C {\n  @InvocableMethod public static void m(List<Id> ids) { List<Contact> cs = [SELECT Id FROM Contact]; }\n  void helper() {}\n}";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
