//! Lower the Smalltalk CST into the canonical graph.
//!
//! Smalltalk is purely dynamic — there are no static receiver types, no imports,
//! and (in the classic fileout surface) no lexical module nesting. So the mapping
//! is deliberately coarse and **honest**, mirroring the conservative principles
//! of the Ruby/Python lowerings:
//!
//!   - `Object subclass: #Name …` (and `…Subclass:` variants) → a [`Type`] node
//!     (`type_kind: class`), with `Name EXTENDS Superclass` deferred and resolved
//!     to a project type when unique, else an explicit [`UnresolvedSymbol`]
//!     (`Object`, `Model`, … live outside an airgapped batch).
//!   - A fileout method chunk `!Class methodsFor: 'cat'! sel body !` and a Pharo
//!     `Class >> sel [ body ]` both → a [`Function`] node, with the selector built
//!     from the message pattern (`at:put:`, `+`, `size`). When the owning class is
//!     a project type, a `Type HAS_METHOD Function` edge is added; class-side
//!     methods (`Class class methodsFor:` / `Class class >> …`) are marked.
//!   - Message sends in a method body → [`CALLS`], resolved **purely by selector**
//!     (Smalltalk has no static receiver type to narrow on): a unique project
//!     method resolves the edge; several are preserved as an ambiguous
//!     `candidates` set; none resolves to an [`UnresolvedSymbol`]. References to a
//!     unique project class → [`USES_TYPE`].
//!
//! Honest punts (no IR kind exists / surface is too ambiguous to map without
//! guessing — see `docs/ir-atlas.md` candidate extensions):
//!   - No `IMPORTS`/`DEPENDS_ON`: Smalltalk fileouts have no import statements
//!     (the image is the namespace).
//!   - Instance/class variable names and class-variable bindings are **not**
//!     emitted as `Constant`s — they are mutable slots, not value bindings.
//!   - Cascades over-merge into one keyword selector per statement segment; a
//!     binary `|`/`||` is treated as a temp/arg bar, not a send.

use std::collections::BTreeMap;

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::smalltalk::lexer::{is_pseudo_var, kind as tk};
use crate::lang::smalltalk::parser::node as cst;

/// Lower a whole project's worth of Smalltalk files into a graph. `manifest_deps`
/// is unused (Smalltalk has no manifest concept the pipeline reads).
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        method_by_selector: BTreeMap::new(),
        type_by_name: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("smalltalk"))],
    );

    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_methods: Vec<PendingMethod> = Vec::new();
    let mut pend_extends: Vec<PendingLink> = Vec::new();

    // Pass B: definition nodes + structural edges + symbol tables.
    for f in files.iter() {
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
                ("language", Json::str("smalltalk")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(leaf, edge::CONTAINS, file_id.clone(), vec![]);

        let mut w = Walk {
            file_id: &file_id,
            module_join: &module_join,
            src: f.source,
            li: &li,
            pend_fns: &mut pend_fns,
            pend_methods: &mut pend_methods,
            pend_extends: &mut pend_extends,
        };
        for item in f.root.child_nodes() {
            match item.kind {
                cst::METHODS_CHUNK => lo.handle_methods_chunk(item, &mut w),
                cst::STATEMENT => lo.handle_statement(item, &mut w),
                _ => {}
            }
        }
    }

    // Pass C: resolve calls, type uses, method ownership, and inheritance against
    // the now-complete symbol tables.
    for pf in &pend_fns {
        let mut calls = Vec::new();
        scan_calls(pf.body, pf.source, &mut calls);
        for call in &calls {
            let res = lo.resolve(&call.selector);
            lo.emit_call(&pf.id, call, res);
        }
        lo.emit_type_uses(&pf.id, pf.body, pf.source);
    }
    for pm in &pend_methods {
        if let Some(type_id) = lo.unique_type(&pm.class_name) {
            lo.g.add_edge(type_id, edge::HAS_METHOD, pm.fn_id.clone(), vec![]);
        }
    }
    for pe in &pend_extends {
        lo.emit_specialization(pe);
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    /// Selector → every method node id with that selector (resolution table).
    method_by_selector: BTreeMap<String, Vec<String>>,
    /// Simple class name → type node ids.
    type_by_name: BTreeMap<String, Vec<String>>,
}

/// Mutable per-file walk context. `'a` is the long-lived AST/source lifetime
/// (stored in the pending vectors); `'s` is the short per-file borrow lifetime.
struct Walk<'a, 's> {
    file_id: &'s str,
    module_join: &'s str,
    src: &'a str,
    li: &'s LineIndex,
    pend_fns: &'s mut Vec<PendingFn<'a>>,
    pend_methods: &'s mut Vec<PendingMethod>,
    pend_extends: &'s mut Vec<PendingLink>,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    body: &'a Node,
}

/// A method whose `HAS_METHOD` ownership is resolved in pass C (the class may be
/// defined in a different chunk/file).
struct PendingMethod {
    fn_id: String,
    class_name: String,
}

/// A deferred `EXTENDS` superclass link, resolved in pass C.
struct PendingLink {
    type_id: String,
    target_name: String,
}

/// A detected message send over the lossless tree.
struct Call {
    selector: String,
    /// `keyword` / `binary` / `unary` — recorded for auditability.
    kind: &'static str,
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
    /// id (or the package id for a root file with no module segments).
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
                vec![("language", Json::str("smalltalk"))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    /// `!Class methodsFor: 'cat'! …! !` → a `Function` per method chunk.
    fn handle_methods_chunk<'a>(&mut self, chunk: &'a Node, w: &mut Walk<'a, '_>) {
        let header = match chunk.child(cst::HEADER) {
            Some(h) => h,
            None => return,
        };
        let (class_name, class_side) = header_info(header, w.src);
        let class_name = match class_name {
            Some(n) => n,
            None => return,
        };
        for method in chunk.children_of(cst::METHOD) {
            let sel = match method.child(cst::SELECTOR) {
                Some(s) => s,
                None => continue,
            };
            let selector = selector_string(sel, w.src);
            if selector.is_empty() {
                continue;
            }
            let line_start = sel.span.start;
            let body: &Node = method.child(cst::BODY).unwrap_or(method);
            self.register_method(
                &class_name,
                class_side,
                &selector,
                line_start,
                method,
                body,
                w,
            );
        }
    }

    /// A free-standing statement: a class definition (`subclass:`), a Pharo method
    /// (`Class >> sel [ … ]`), or an ignored top-level do-it.
    fn handle_statement<'a>(&mut self, stmt: &'a Node, w: &mut Walk<'a, '_>) {
        let els = significant_children(stmt, w.src);
        if let Some(i) = els.iter().position(|e| is_subclass_keyword(e)) {
            self.handle_class_def(&els, i, stmt, w);
        } else if let Some(i) = els.iter().position(|e| is_binary(e, ">>")) {
            self.handle_pharo_method(&els, i, w);
        }
        // else: a top-level do-it — no enclosing function to attribute calls to.
    }

    /// `Superclass subclass: #Name …` → a `Type` (and a deferred `EXTENDS`).
    fn handle_class_def<'a>(
        &mut self,
        els: &[El<'a>],
        kw_idx: usize,
        stmt: &Node,
        w: &mut Walk<'a, '_>,
    ) {
        // Superclass = the last identifier before the `subclass:` keyword.
        let superclass = els[..kw_idx].iter().rev().find_map(ident_text);
        // Class name = the symbol/ident right after the keyword.
        let name = els.get(kw_idx + 1).and_then(|e| match e {
            El::Tok { text, kind, .. } if *kind == tk::SYMBOL => Some(strip_hash(text)),
            El::Tok { text, kind, .. } if *kind == tk::IDENT => Some(text.to_string()),
            _ => None,
        });
        let name = match name {
            Some(n) if !n.is_empty() => n,
            _ => return,
        };
        let qual = qual_name(w.module_join, &name);
        let id = format!("type::{qual}");
        let line = w.li.line_col(stmt.span.start).line;
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str("class")),
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("smalltalk")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(stmt.span.start as u64)),
                ("span_end", Json::U64(stmt.span.end as u64)),
            ],
        );
        self.g
            .add_edge(w.file_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name.entry(name).or_default().push(id.clone());
        if let Some(base) = superclass {
            w.pend_extends.push(PendingLink {
                type_id: id,
                target_name: base,
            });
        }
    }

    /// `Class [class] >> selectorPattern [ body ]` → a `Function`.
    fn handle_pharo_method<'a>(&mut self, els: &[El<'a>], gg_idx: usize, w: &mut Walk<'a, '_>) {
        // Receiver of `>>`: `Foo` or `Foo class`.
        let before = &els[..gg_idx];
        let last_ident = before.iter().rev().find_map(ident_text);
        let (class_name, class_side) = match last_ident {
            Some(t) if t == "class" => {
                // class-side: the class name is the identifier before `class`.
                let name = before.iter().rev().filter_map(ident_text).nth(1);
                (name, true)
            }
            Some(t) => (Some(t), false),
            None => (None, false),
        };
        let class_name = match class_name {
            Some(n) => n,
            None => return,
        };
        // Selector pattern: the elements after `>>` up to the body bracket group.
        let after = &els[gg_idx + 1..];
        let (selector, sel_start) = selector_from_pattern(after);
        if selector.is_empty() {
            return;
        }
        // Body: the first bracket group after `>>`. A `>>` with no bracket body is
        // not a real Pharo method definition (likely a `>>` binary send) — skip it
        // rather than fabricate a method.
        let body = match after.iter().find_map(grp) {
            Some(b) => b,
            None => return,
        };
        self.register_method(&class_name, class_side, &selector, sel_start, body, body, w);
    }

    /// Shared method registration for both fileout chunks and Pharo `>>` forms.
    /// `def_node` provides the definition span; `body` is scanned for calls.
    #[allow(clippy::too_many_arguments)]
    fn register_method<'a>(
        &mut self,
        class_name: &str,
        class_side: bool,
        selector: &str,
        span_start: u32,
        def_node: &Node,
        body: &'a Node,
        w: &mut Walk<'a, '_>,
    ) {
        let line = w.li.line_col(span_start).line;
        let qual = format!("{}.{}", qual_name(w.module_join, class_name), selector);
        let id = format!("fn::{qual}#{line}");
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("smalltalk")),
            ("selector", Json::str(selector.to_string())),
            ("receiver_type", Json::str(class_name.to_string())),
            ("is_method", Json::Bool(true)),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(def_node.span.start as u64)),
            ("span_end", Json::U64(def_node.span.end as u64)),
        ];
        if class_side {
            props.push(("is_class_method", Json::Bool(true)));
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, selector.to_string(), props);
        self.g
            .add_edge(w.file_id, edge::DECLARES, id.clone(), vec![]);
        self.method_by_selector
            .entry(selector.to_string())
            .or_default()
            .push(id.clone());
        w.pend_methods.push(PendingMethod {
            fn_id: id.clone(),
            class_name: class_name.to_string(),
        });
        w.pend_fns.push(PendingFn {
            id,
            source: w.src,
            body,
        });
    }

    // --- resolution ---------------------------------------------------------

    /// Resolve a send purely by selector (no static receiver type in Smalltalk).
    fn resolve(&self, selector: &str) -> Resolution {
        let c = self
            .method_by_selector
            .get(selector)
            .cloned()
            .unwrap_or_default();
        if c.is_empty() {
            Resolution {
                outcome: Outcome::None,
                level: "external",
            }
        } else if c.len() == 1 {
            Resolution {
                outcome: Outcome::One(c[0].clone()),
                level: "selector",
            }
        } else {
            Resolution {
                outcome: Outcome::Many(c),
                level: "selector",
            }
        }
    }

    fn emit_call(&mut self, caller_id: &str, call: &Call, res: Resolution) {
        let mut props = vec![
            ("callee", Json::str(call.selector.clone())),
            ("selector_kind", Json::str(call.kind)),
            ("resolution", Json::str(res.level)),
        ];
        match res.outcome {
            Outcome::One(id) => {
                props.push(("resolved", Json::Bool(true)));
                props.push(("candidate_count", Json::U64(1)));
                self.g.add_edge(caller_id, edge::CALLS, id, props);
            }
            Outcome::Many(ids) => {
                let target = unresolved_id(&call.selector);
                self.ensure_unresolved(&target, &call.selector, "call");
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
                let target = unresolved_id(&call.selector);
                self.ensure_unresolved(&target, &call.selector, "call");
                props.push(("resolved", Json::Bool(false)));
                props.push(("candidate_count", Json::U64(0)));
                self.g.add_edge(caller_id, edge::CALLS, target, props);
            }
        }
    }

    /// Resolve a deferred superclass link to the unique project type, else an
    /// explicit `UnresolvedSymbol` (a class outside the airgapped batch).
    fn emit_specialization(&mut self, link: &PendingLink) {
        let target = match self.unique_type(&link.target_name) {
            Some(id) => id,
            None => {
                let id = unresolved_id(&link.target_name);
                self.ensure_unresolved(&id, &link.target_name, "superclass");
                id
            }
        };
        self.g.add_edge(
            link.type_id.clone(),
            edge::EXTENDS,
            target,
            vec![("target_name", Json::str(link.target_name.clone()))],
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

    fn unique_type(&self, name: &str) -> Option<String> {
        match self.type_by_name.get(name) {
            Some(ids) if ids.len() == 1 => Some(ids[0].clone()),
            _ => None,
        }
    }

    /// `USES_TYPE` edges for capitalised global references in a body that name a
    /// unique project class (e.g. `OrderedCollection new`).
    fn emit_type_uses(&mut self, from_id: &str, body: &Node, src: &str) {
        let mut seen: Vec<String> = Vec::new();
        for n in body.walk() {
            for t in n.tokens() {
                if t.kind != tk::IDENT {
                    continue;
                }
                let name = t.span.text(src);
                if !is_capitalized(name) || is_pseudo_var(name) {
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

// --- pure helpers -----------------------------------------------------------

fn qual_name(module_join: &str, name: &str) -> String {
    if module_join.is_empty() {
        name.to_string()
    } else {
        format!("{module_join}.{name}")
    }
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

fn is_capitalized(name: &str) -> bool {
    name.chars()
        .next()
        .map(|c| c.is_uppercase())
        .unwrap_or(false)
}

fn strip_hash(symbol_text: &str) -> String {
    symbol_text
        .strip_prefix('#')
        .unwrap_or(symbol_text)
        .to_string()
}

/// Class name and class-side flag from a methods-chunk header. The first
/// identifier is the class; a `class` identifier before the first keyword marks a
/// class-side category.
fn header_info(header: &Node, src: &str) -> (Option<String>, bool) {
    let mut class_name: Option<String> = None;
    let mut class_side = false;
    let mut seen_keyword = false;
    for t in header.tokens() {
        let text = t.span.text(src);
        match t.kind {
            tk::IDENT if !seen_keyword => {
                if class_name.is_none() {
                    class_name = Some(text.to_string());
                } else if text == "class" {
                    class_side = true;
                }
            }
            tk::KEYWORD => seen_keyword = true,
            _ => {}
        }
    }
    (class_name, class_side)
}

/// Build a selector string from a `Selector` node: concatenated keyword atoms,
/// else the binary selector, else the unary identifier.
fn selector_string(sel: &Node, src: &str) -> String {
    let mut keyword = String::new();
    let mut binary: Option<String> = None;
    let mut unary: Option<String> = None;
    for t in sel.tokens() {
        let text = t.span.text(src);
        match t.kind {
            tk::KEYWORD => keyword.push_str(text),
            tk::BINARY if binary.is_none() => binary = Some(text.to_string()),
            tk::IDENT if unary.is_none() => unary = Some(text.to_string()),
            _ => {}
        }
    }
    if !keyword.is_empty() {
        keyword
    } else if let Some(b) = binary {
        b
    } else {
        unary.unwrap_or_default()
    }
}

/// Build a selector from a Pharo `>>` pattern: the elements between `>>` and the
/// body bracket. Returns the selector and the span start of its first token.
fn selector_from_pattern(after: &[El]) -> (String, u32) {
    let mut keyword = String::new();
    let mut binary: Option<String> = None;
    let mut unary: Option<String> = None;
    let mut start: Option<u32> = None;
    for e in after {
        match e {
            El::Grp(_) => break, // the body bracket ends the pattern
            El::Tok {
                text,
                kind,
                start: s,
            } => {
                start.get_or_insert(*s);
                match *kind {
                    tk::KEYWORD => keyword.push_str(text),
                    tk::BINARY if binary.is_none() => binary = Some(text.to_string()),
                    tk::IDENT if unary.is_none() => unary = Some(text.to_string()),
                    _ => {}
                }
            }
        }
    }
    let sel = if !keyword.is_empty() {
        keyword
    } else if let Some(b) = binary {
        b
    } else {
        unary.unwrap_or_default()
    };
    (sel, start.unwrap_or(0))
}

// --- significant-children view ----------------------------------------------

enum El<'a> {
    Tok {
        text: &'a str,
        kind: &'static str,
        start: u32,
    },
    Grp(&'a Node),
}

fn ident_text(e: &El) -> Option<String> {
    match e {
        El::Tok { text, kind, .. } if *kind == tk::IDENT => Some(text.to_string()),
        _ => None,
    }
}

fn grp<'a>(e: &El<'a>) -> Option<&'a Node> {
    match e {
        El::Grp(n) => Some(*n),
        El::Tok { .. } => None,
    }
}

fn is_binary(e: &El, op: &str) -> bool {
    matches!(e, El::Tok { text, kind, .. } if *kind == tk::BINARY && *text == op)
}

fn is_subclass_keyword(e: &El) -> bool {
    matches!(e, El::Tok { text, kind, .. }
        if *kind == tk::KEYWORD && (*text == "subclass:" || text.ends_with("Subclass:")))
}

/// Direct, non-trivia children of a node, with balanced groups kept whole.
fn significant_children<'a>(node: &'a Node, src: &'a str) -> Vec<El<'a>> {
    let mut v = Vec::new();
    for c in &node.children {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => v.push(El::Tok {
                text: t.span.text(src),
                kind: t.kind,
                start: t.span.start,
            }),
            Child::Node(n) => v.push(El::Grp(n)),
        }
    }
    v
}

// --- call detection over the lossless token tree ----------------------------

/// Detect keyword / binary / unary sends over the real token tree, recursing into
/// nested groups. Keyword atoms in one statement segment are concatenated into a
/// single selector (split on `.`/`;`); a binary send is its own selector (the
/// temp/arg bars `|`/`||` are skipped); a unary send is an identifier that follows
/// a completed primary (so a leading receiver/variable is not mistaken for one).
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let mut kw: Vec<&str> = Vec::new();
    let mut prev_primary = false;
    for e in &els {
        match e {
            El::Grp(_) => {
                prev_primary = true;
            }
            El::Tok { text, kind, .. } => match *kind {
                tk::PERIOD | tk::SEMICOLON => {
                    flush_keyword(&mut kw, out);
                    prev_primary = false;
                }
                tk::KEYWORD => {
                    kw.push(text);
                    prev_primary = false;
                }
                tk::BINARY => {
                    if *text != "|" && *text != "||" {
                        out.push(Call {
                            selector: text.to_string(),
                            kind: "binary",
                        });
                    }
                    prev_primary = false;
                }
                tk::IDENT => {
                    if prev_primary && !is_pseudo_var(text) {
                        out.push(Call {
                            selector: text.to_string(),
                            kind: "unary",
                        });
                    }
                    prev_primary = true;
                }
                tk::NUMBER | tk::STRING | tk::CHAR | tk::SYMBOL => {
                    prev_primary = true;
                }
                _ => {
                    prev_primary = false;
                }
            },
        }
    }
    flush_keyword(&mut kw, out);

    // Recurse into nested groups (each is its own statement context).
    for e in &els {
        if let Some(g) = grp(e) {
            scan_calls(g, src, out);
        }
    }
}

fn flush_keyword(kw: &mut Vec<&str>, out: &mut Vec<Call>) {
    if !kw.is_empty() {
        out.push(Call {
            selector: kw.concat(),
            kind: "keyword",
        });
        kw.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::smalltalk::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("Demo.st", src);
        let file = SourceFile {
            rel_path: "Demo.st".to_string(),
            module_path: vec!["Demo".to_string()],
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    fn call_edges(g: &Graph) -> Vec<&crate::graph::GraphEdge> {
        g.edges().filter(|e| e.kind == edge::CALLS).collect()
    }

    #[test]
    fn class_def_is_a_type() {
        let g = graph_for("Object subclass: #Point instanceVariableNames: 'x y'!");
        assert_eq!(g.count_nodes_of(ont::TYPE), 1);
        let t = g.nodes().find(|n| n.kind == ont::TYPE).unwrap();
        assert_eq!(t.name, "Point");
        assert_eq!(t.props.get("type_kind"), Some(&Json::str("class")));
        assert_eq!(t.props.get("language"), Some(&Json::str("smalltalk")));
    }

    #[test]
    #[ignore = "smalltalk EXTENDS and selector resolution deferred"]
    fn inheritance_emits_extends() {
        let g = graph_for(
            "Object subclass: #Base instanceVariableNames: ''!\n\
             Base subclass: #Derived instanceVariableNames: ''!",
        );
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an EXTENDS edge");
        assert!(ext.from.starts_with("type::Demo.Derived"));
        assert!(ext.to.starts_with("type::Demo.Base"));
        // Object is outside the batch -> unresolved superclass for Base.
        assert!(g.has_node("unresolved::Object"));
    }

    #[test]
    fn methods_become_functions_with_has_method() {
        let g = graph_for(
            "Object subclass: #Counter instanceVariableNames: 'count'!\n\
             !Counter methodsFor: 'access'!\n\
             count\n\t^count!\n\
             increment\n\tcount := count + 1! !\n",
        );
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "count + increment");
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD));
        let f = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "count")
            .expect("the count method");
        assert_eq!(f.props.get("selector"), Some(&Json::str("count")));
    }

    #[test]
    fn keyword_selector_is_built() {
        let g = graph_for(
            "!Dict methodsFor: 'a'!\n\
             at: aKey put: aValue\n\t^self! !\n",
        );
        let f = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION)
            .expect("the method");
        assert_eq!(f.props.get("selector"), Some(&Json::str("at:put:")));
    }

    #[test]
    fn class_side_method_is_marked() {
        let g = graph_for(
            "!Counter class methodsFor: 'creation'!\n\
             new\n\t^super new init! !\n",
        );
        let f = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "new")
            .expect("the class method");
        assert_eq!(f.props.get("is_class_method"), Some(&Json::Bool(true)));
    }

    #[test]
    fn pharo_arrow_method_is_a_function() {
        let g = graph_for("Counter >> increment [ count := count + 1 ]");
        let f = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "increment");
        assert!(f.is_some(), "Class >> selector [..] should be a Function");
    }

    #[test]
    #[ignore = "smalltalk selector resolution deferred"]
    fn unique_call_resolves_others_are_external() {
        // A unary send needs an explicit receiver (`self helper`); a bare
        // identifier is a variable reference, not a message, and is honestly not
        // emitted as a call.
        let g = graph_for(
            "!C methodsFor: 'a'!\n\
             run\n\tself helper. self mystery! !\n\
             helper\n\t^1! !\n",
        );
        let calls = call_edges(&g);
        let helper = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("helper")))
            .expect("a call to helper");
        assert_eq!(helper.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(helper.props.get("resolution"), Some(&Json::str("selector")));
        let mystery = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("mystery")))
            .expect("a call to mystery");
        assert_eq!(
            mystery.props.get("resolution"),
            Some(&Json::str("external"))
        );
        assert!(g.has_node("unresolved::mystery"));
    }

    #[test]
    fn type_use_via_class_reference() {
        let g = graph_for(
            "Object subclass: #Widget instanceVariableNames: ''!\n\
             !Factory methodsFor: 'a'!\n\
             build\n\t^Widget new! !\n",
        );
        assert!(
            g.edges()
                .any(|e| e.kind == edge::USES_TYPE && e.to.contains("Widget")),
            "Widget new should create USES_TYPE"
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src = "Object subclass: #C instanceVariableNames: ''!\n\
                   !C methodsFor: 'a'!\n\
                   run\n\thelper foo: 1 bar: 2! !\n\
                   helper\n\t^1! !\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
