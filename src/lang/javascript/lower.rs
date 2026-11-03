//! Lower the JavaScript CST into the canonical graph.
//!
//! This mirrors the Python lowering ([`crate::lang::python::lower`]) — same
//! conservative principles, same shared ontology — adapted to JavaScript's
//! surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to
//!    a concrete project definition only when a scope level yields exactly one
//!    candidate; several candidates are emitted as an ambiguous edge with the full
//!    `candidates` set; none resolves to an explicit `UnresolvedSymbol` node.
//! 2. **Everything comes from real tokens.** Calls, base classes, imports, and
//!    method names are read off the lossless tree, never guessed. There is no LLM
//!    in the airgapped runtime to invent edges.
//!
//! Honest mappings (see the IR Atlas):
//!   `function` → `Function`; a class method → `Function` plus `HAS_METHOD` from
//!   its enclosing class; `class` → `Type` (`type_kind: class`); top-level
//!   `const`/`let`/`var` binding → `Constant`; `class C extends B` → `C EXTENDS B`
//!   (the substrate's [`edge::EXTENDS`], reserved for inheritance languages);
//!   `import …`/`export … from …` → `IMPORTS` (plus `ExternalDependency` /
//!   `DEPENDS_ON` for bare npm specifiers). A relative specifier (`./x`, `../y`)
//!   is treated as an intra-project module; a bare specifier (`react`,
//!   `@scope/pkg`) as an external dependency. Decorators are recorded as a
//!   `decorators` property — no `DECORATES` edge constant exists yet, so we do not
//!   fabricate one (a candidate IR extension, see `docs/ir-atlas.md`).
//!
//! Breadth gaps (honest, never lies): function/arrow/class *expressions* assigned
//! to variables are not themselves defined as `Function`/`Type` nodes (their
//! bodies live inside opaque brace groups), matching how the Rust front end treats
//! nested fn bodies. Calls inside template-literal interpolations are not
//! extracted (the literal is one opaque token, as with Python f-strings).

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::javascript::lexer::{is_keyword, kind as tk};
use crate::lang::javascript::parser::node as cst;

/// Lower a whole project's worth of JavaScript files into a graph. `manifest_deps`
/// is unused (the pipeline's manifest reader is Cargo-only); dependencies are
/// discovered from `import` specifiers instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    // Project-local module roots: the package plus every module-path segment. A
    // relative specifier is always internal; a bare specifier is external unless
    // its root names one of these.
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
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("javascript"))],
    );

    // Pass B: create definition nodes + structural edges and build symbol tables.
    // Inheritance is deferred to pass C so a base class defined later still
    // resolves.
    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_extends: Vec<PendingExtends> = Vec::new();
    for f in files {
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
                ("language", Json::str("javascript")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(leaf, edge::CONTAINS, file_id.clone(), vec![]);

        for item in f.root.child_nodes() {
            lo.walk_item(
                item,
                &file_id,
                &module_join,
                f.source,
                &li,
                &mut pend_fns,
                &mut pend_extends,
            );
        }
    }

    // Pass C: resolve calls (scope ladder) and inheritance against the now-
    // complete symbol tables.
    for pf in &pend_fns {
        let ctx = Ctx {
            module_join: pf.module_join.clone(),
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
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    block: Option<&'a Node>,
    module_join: String,
    owner_type: Option<String>,
}

/// A deferred `class C extends Base` link, resolved in pass C.
struct PendingExtends {
    type_id: String,
    base_name: String,
}

/// The enclosing class while walking, for methods (`HAS_METHOD`, receiver scope).
struct Owner {
    name: String,
    id: String,
}

/// Parameters for emitting a synthesized `Function` (an arrow/function expression
/// bound to a name: a var initializer, class field, object method, or member
/// assignment). `'o` is the borrow of the owning class (if any); `'a` the source.
struct SynthFn<'o, 'a> {
    name: &'o str,
    line: u32,
    span_start: u32,
    span_end: u32,
    block: Option<&'a Node>,
    is_async: bool,
    is_generator: bool,
    exported: bool,
    /// The `binding` property: `const`/`let`/`var`, `field`, `object_method`, or
    /// `assignment`.
    binding: &'o str,
    /// The enclosing class, for a function-valued field (`HAS_METHOD`, receiver).
    owner: Option<&'o Owner>,
    /// Index into the global-method table even without a class owner (object
    /// methods and member assignments are invoked as `recv.name(...)`).
    method_like: bool,
    /// A textual receiver path for context (`exports`, `Foo.prototype`), recorded
    /// as a `receiver` property; never used to fabricate a `HAS_METHOD` edge.
    receiver: Option<&'o str>,
}

/// A function-shaped initializer's body block, plus async/generator flags.
struct FieldFn<'a> {
    block: Option<&'a Node>,
    is_async: bool,
    is_generator: bool,
}

/// A detected call site over the lossless tree.
struct Call {
    /// The called name (final member or bare name).
    name: String,
    /// True for `recv.name(...)` / `recv?.name(...)` member calls.
    method: bool,
    /// Immediate receiver identifier for member calls (`this`, a variable).
    receiver: Option<String>,
}

/// Resolution context for one enclosing function/method.
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
    /// module id (or the package id for a root file with no module segments, e.g.
    /// a top-level `index.js`).
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
                vec![("language", Json::str("javascript"))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    #[allow(clippy::too_many_arguments)]
    fn walk_item<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        module_join: &str,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_extends: &mut Vec<PendingExtends>,
    ) {
        match item.kind {
            cst::FUNCTION => {
                self.handle_fn(item, file_id, module_join, None, src, li, pend_fns);
            }
            cst::CLASS => {
                self.handle_class(item, file_id, module_join, src, li, pend_fns, pend_extends);
            }
            cst::IMPORT => self.handle_import(item, file_id, src),
            cst::VAR_DECL => self.handle_var(item, file_id, module_join, src, li, pend_fns),
            cst::STATEMENT => self.handle_statement(item, file_id, module_join, src, li, pend_fns),
            _ => {}
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_fn<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        module_join: &str,
        owner: Option<&Owner>,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
    ) {
        let name = name_text(item, src).unwrap_or("<anonymous>").to_string();
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(module_join, &name);
        let id = format!("fn::{qual}#{line}");
        let block = item.child(cst::BLOCK);
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("javascript")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            ("has_body", Json::Bool(block.is_some())),
        ];
        append_export_props(&mut props, item, src);
        if has_token(item, src, "async") {
            props.push(("is_async", Json::Bool(true)));
        }
        if has_token(item, src, "*") {
            props.push(("is_generator", Json::Bool(true)));
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
            module_join: module_join.to_string(),
            owner_type: owner.map(|o| o.name.clone()),
        });
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_class<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        module_join: &str,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
        pend_extends: &mut Vec<PendingExtends>,
    ) {
        let name = name_text(item, src).unwrap_or("<anonymous>").to_string();
        let line = li.line_col(name_span_start(item)).line;
        let qual = qual_name(module_join, &name);
        let id = format!("type::{qual}");
        let mut props = vec![
            ("type_kind", Json::str("class")),
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("javascript")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
        ];
        append_export_props(&mut props, item, src);
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

        if let Some(base) = extends_base(item, src) {
            pend_extends.push(PendingExtends {
                type_id: id.clone(),
                base_name: base,
            });
        }

        if let Some(body) = item.child(cst::CLASS_BODY) {
            let owner = Owner {
                name: name.clone(),
                id: id.clone(),
            };
            for member in body.child_nodes() {
                match member.kind {
                    // A named method `m() { … }`. Computed members (`[expr]() {}`)
                    // have no clear name and are skipped, never fabricated.
                    cst::METHOD if member.child(cst::NAME).is_some() => {
                        self.handle_fn(
                            member,
                            file_id,
                            module_join,
                            Some(&owner),
                            src,
                            li,
                            pend_fns,
                        );
                    }
                    // A function-valued class field (`handler = () => {}`) is a
                    // method in all but syntax.
                    cst::FIELD => {
                        if let (Some(fname), Some(decl)) =
                            (name_text(member, src), function_valued_field(member, src))
                        {
                            let fname = fname.to_string();
                            let line = li.line_col(name_span_start(member)).line;
                            self.emit_synth_fn(
                                SynthFn {
                                    name: &fname,
                                    line,
                                    span_start: member.span.start,
                                    span_end: member.span.end,
                                    block: decl.block,
                                    is_async: decl.is_async,
                                    is_generator: decl.is_generator,
                                    exported: false,
                                    binding: "field",
                                    owner: Some(&owner),
                                    method_like: true,
                                    receiver: None,
                                },
                                file_id,
                                module_join,
                                src,
                                pend_fns,
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    /// `import … from "spec"` / `import "spec"` / `export … from "spec"`. The
    /// specifier is the last string literal in the node; relative specifiers map
    /// to an intra-project `Module`, bare specifiers to an `ExternalDependency`.
    fn handle_import(&mut self, item: &Node, file_id: &str, src: &str) {
        let spec = match last_string_literal(item, src) {
            Some(s) => s,
            None => return, // e.g. `export { a }` with no `from` — no dependency
        };
        let inner = strip_quotes(spec);
        if inner.is_empty() {
            return;
        }
        let reexport = tree_has_token(item, src, "export") && tree_has_token(item, src, "from");
        let reexport_all = reexport && tree_has_token(item, src, "*");
        if inner.starts_with('.') || inner.starts_with('/') {
            // Relative / absolute path: intra-project module.
            let mod_id = format!("mod::{inner}");
            self.g.upsert_node(
                mod_id.clone(),
                ont::MODULE,
                inner.to_string(),
                vec![("language", Json::str("javascript"))],
            );
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                mod_id,
                import_edge_props(inner, false, reexport, reexport_all),
            );
        } else {
            let root = package_root(inner);
            let internal = self.local_roots.contains(&root);
            if internal {
                let mod_id = format!("mod::{root}");
                self.g.upsert_node(
                    mod_id.clone(),
                    ont::MODULE,
                    root.clone(),
                    vec![("language", Json::str("javascript"))],
                );
                self.g.add_edge(
                    file_id,
                    edge::IMPORTS,
                    mod_id,
                    import_edge_props(inner, false, reexport, reexport_all),
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
                    import_edge_props(inner, true, reexport, reexport_all),
                );
                self.g
                    .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
            }
        }
    }

    /// Top-level `const|let|var …`. Each plain single-name declarator is a
    /// `Constant`, *unless* its initializer is an arrow/function expression
    /// (`const f = () => …` / `const f = function () {}`), in which case it is a
    /// `Function` named by the binding. Destructuring binders are still skipped
    /// (no single clear name). If a declarator's initializer is an object literal,
    /// the binding stays a `Constant` and its function-valued properties/methods
    /// are emitted as `Function`s named by the property (`const api = { run() {} }`).
    fn handle_var<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        module_join: &str,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
    ) {
        let exported = has_token(item, src, "export");
        let binding = item
            .tokens()
            .map(|t| t.span.text(src))
            .find(|text| matches!(*text, "const" | "let" | "var"))
            .unwrap_or("var")
            .to_string();
        let header = match item.child(cst::HEADER) {
            Some(h) => h,
            None => return,
        };
        for decl in split_declarators(header, src) {
            let name = match decl.name {
                Some(n) => n.to_string(),
                None => continue, // destructuring / computed binder
            };
            let line = li.line_col(decl.name_start).line;
            if init_is_function(&decl.init, src) {
                let block = first_brace(&decl.init);
                let is_async = init_has_token(&decl.init, src, "async");
                let is_generator = init_has_token(&decl.init, src, "*");
                self.emit_synth_fn(
                    SynthFn {
                        name: &name,
                        line,
                        span_start: item.span.start,
                        span_end: item.span.end,
                        block,
                        is_async,
                        is_generator,
                        exported,
                        binding: &binding,
                        owner: None,
                        method_like: false,
                        receiver: None,
                    },
                    file_id,
                    module_join,
                    src,
                    pend_fns,
                );
                continue;
            }
            // Ordinary value binding → Constant.
            let id = format!("const::{}", qual_name(module_join, &name));
            let mut props = vec![
                ("binding", Json::str(binding.clone())),
                ("language", Json::str("javascript")),
                ("line", Json::U64(line as u64)),
            ];
            if exported {
                props.push(("exported", Json::Bool(true)));
            }
            self.g
                .upsert_node(id.clone(), ont::CONSTANT, name.clone(), props);
            self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
            // `const obj = { foo() {}, bar: () => {} }` → emit the object's
            // function-valued members as named Functions.
            if let Some(brace) = single_brace(&decl.init) {
                self.emit_object_methods(
                    brace,
                    file_id,
                    module_join,
                    Some(&name),
                    false,
                    src,
                    li,
                    pend_fns,
                );
            }
        }
    }

    /// A top-level expression statement. The only definition forms recovered here
    /// are member assignments whose right-hand side is a function or object
    /// literal: `exports.NAME = function () {}`, `module.exports.NAME = () => …`,
    /// `Receiver.prototype.NAME = function () {}`, `app.get = function () {}`, and
    /// `module.exports = { foo() {}, bar: () => {} }`. The name always comes from a
    /// real member token — anonymous right-hand sides are never invented.
    fn handle_statement<'a>(
        &mut self,
        item: &'a Node,
        file_id: &str,
        module_join: &str,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
    ) {
        // The collected statement body lives in an inner Statement node (header).
        let content = item.child(cst::STATEMENT).unwrap_or(item);
        let elems: Vec<&Child> = sig_children(content);
        // First top-level plain `=` (assignment, not `==`/`===`/`=>`/`+=`/…).
        let eq = match elems
            .iter()
            .position(|c| matches!(c, Child::Token(t) if t.span.text(src) == "="))
        {
            Some(i) => i,
            None => return,
        };
        let lhs = &elems[..eq];
        let rhs = &elems[eq + 1..];

        // A plain dotted member chain on the left (`a.b.c`), else not a def we name.
        let chain = match member_chain(lhs, src) {
            Some(c) if !c.is_empty() => c,
            _ => return,
        };
        let commonjs_export = is_commonjs_export_member(&chain);

        if init_is_function(rhs, src) {
            let name = chain.last().unwrap().clone();
            let receiver = if chain.len() >= 2 {
                Some(chain[..chain.len() - 1].join("."))
            } else {
                None
            };
            let line = li
                .line_col(name_start(lhs, src).unwrap_or(item.span.start))
                .line;
            let block = first_brace(rhs);
            let is_async = init_has_token(rhs, src, "async");
            let is_generator = init_has_token(rhs, src, "*");
            self.emit_synth_fn(
                SynthFn {
                    name: &name,
                    line,
                    span_start: item.span.start,
                    span_end: item.span.end,
                    block,
                    is_async,
                    is_generator,
                    exported: commonjs_export,
                    binding: "assignment",
                    owner: None,
                    method_like: chain.len() >= 2,
                    receiver: receiver.as_deref(),
                },
                file_id,
                module_join,
                src,
                pend_fns,
            );
            return;
        }

        // `X.Y = { foo() {}, bar: () => {} }` → object-literal members.
        if let Some(brace) = single_brace(rhs) {
            let receiver = chain.join(".");
            self.emit_object_methods(
                brace,
                file_id,
                module_join,
                Some(&receiver),
                chain.as_slice() == ["module", "exports"],
                src,
                li,
                pend_fns,
            );
        }
    }

    /// Emit `Function`s for the function-valued members of an object literal:
    /// shorthand methods (`foo() {}`, `async foo() {}`, `get foo() {}`,
    /// `*foo() {}`) and function-valued properties (`bar: () => …`,
    /// `baz: function () {}`). Data properties are ignored. Nested object literals
    /// are not descended into (kept conservative; matches the brace-group breadth
    /// gap elsewhere).
    #[allow(clippy::too_many_arguments)]
    fn emit_object_methods<'a>(
        &mut self,
        brace: &'a Node,
        file_id: &str,
        module_join: &str,
        receiver: Option<&str>,
        exported: bool,
        src: &'a str,
        li: &LineIndex,
        pend_fns: &mut Vec<PendingFn<'a>>,
    ) {
        for entry in object_entries(brace, src) {
            if let Some(m) = object_member(&entry, src) {
                let line = li.line_col(m.name_start).line;
                self.emit_synth_fn(
                    SynthFn {
                        name: &m.name,
                        line,
                        span_start: m.span_start,
                        span_end: m.span_end,
                        block: m.block,
                        is_async: m.is_async,
                        is_generator: m.is_generator,
                        exported,
                        binding: "object_method",
                        owner: None,
                        method_like: true,
                        receiver,
                    },
                    file_id,
                    module_join,
                    src,
                    pend_fns,
                );
            }
        }
    }

    /// Create a `Function` node for a synthesized definition (var/field/object/
    /// assignment form), wire its `DECLARES` edge, index it for call resolution,
    /// and queue its body for the call-scanning pass.
    fn emit_synth_fn<'a>(
        &mut self,
        f: SynthFn<'_, 'a>,
        file_id: &str,
        module_join: &str,
        src: &'a str,
        pend_fns: &mut Vec<PendingFn<'a>>,
    ) {
        let qual = qual_name(module_join, f.name);
        let id = format!("fn::{qual}#{}", f.line);
        let mut props = vec![
            ("qualified_name", Json::str(qual)),
            ("language", Json::str("javascript")),
            ("line", Json::U64(f.line as u64)),
            ("span_start", Json::U64(f.span_start as u64)),
            ("span_end", Json::U64(f.span_end as u64)),
            ("has_body", Json::Bool(f.block.is_some())),
            ("binding", Json::str(f.binding.to_string())),
        ];
        if f.exported {
            props.push(("exported", Json::Bool(true)));
        }
        if f.is_async {
            props.push(("is_async", Json::Bool(true)));
        }
        if f.is_generator {
            props.push(("is_generator", Json::Bool(true)));
        }
        if let Some(o) = f.owner {
            props.push(("receiver_type", Json::str(o.name.clone())));
            props.push(("is_method", Json::Bool(true)));
        } else if let Some(r) = f.receiver {
            props.push(("receiver", Json::str(r.to_string())));
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, f.name.to_string(), props);
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);

        self.fn_by_name
            .entry(f.name.to_string())
            .or_default()
            .push(id.clone());
        self.fn_by_module
            .entry((module_join.to_string(), f.name.to_string()))
            .or_default()
            .push(id.clone());
        if let Some(o) = f.owner {
            self.method_by_name
                .entry(f.name.to_string())
                .or_default()
                .push(id.clone());
            self.method_by_type
                .entry((o.name.clone(), f.name.to_string()))
                .or_default()
                .push(id.clone());
            self.g
                .add_edge(o.id.clone(), edge::HAS_METHOD, id.clone(), vec![]);
        } else if f.method_like {
            // Called as `recv.name(...)`; eligible for the global-method fallback,
            // but with no class owner we never fabricate a HAS_METHOD edge.
            self.method_by_name
                .entry(f.name.to_string())
                .or_default()
                .push(id.clone());
        }

        pend_fns.push(PendingFn {
            id,
            source: src,
            block: f.block,
            module_join: module_join.to_string(),
            owner_type: f.owner.map(|o| o.name.clone()),
        });
    }

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, ctx: &Ctx) -> Resolution {
        if call.method {
            // Receiver scope: `this.m()` → enclosing class's methods.
            if call.receiver.as_deref() == Some("this") {
                if let Some(owner) = &ctx.owner_type {
                    let c = self.methods_of(owner, &call.name);
                    if !c.is_empty() {
                        return mk(c, "receiver");
                    }
                }
            }
            // Unknown receiver type (no inference). The honest candidate set is
            // every same-name method PLUS every same-name free function — a JS
            // member call can reach namespace imports (`ns.f()`) and functions
            // stored as object properties. `mk` resolves a singleton and
            // preserves any wider set as an explicit ambiguity; it never guesses.
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
        // Global (project-wide).
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

    /// Resolve a deferred `class C extends Base` link into a concrete `EXTENDS`
    /// edge, pointing at the project type when unique, otherwise an explicit
    /// `UnresolvedSymbol` (a host/third-party base invisible in an airgap).
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

    fn unique_type(&self, name: &str) -> Option<String> {
        match self.type_by_name.get(name) {
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

/// Dotted module-join for a file's module path: `["a","b"]` → `"a.b"`, `[]` → "".
fn mod_join(path: &[String]) -> String {
    path.join(".")
}

/// `module.name` — the dotted qualified name and the basis for node ids.
fn qual_name(module_join: &str, name: &str) -> String {
    if module_join.is_empty() {
        name.to_string()
    } else {
        format!("{module_join}.{name}")
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

/// The npm package root of a bare specifier: `@scope/pkg/sub` → `@scope/pkg`,
/// `pkg/sub` → `pkg`, `pkg` → `pkg`.
fn package_root(spec: &str) -> String {
    let mut parts = spec.split('/');
    let first = parts.next().unwrap_or("");
    if first.starts_with('@') {
        match parts.next() {
            Some(second) => format!("{first}/{second}"),
            None => first.to_string(),
        }
    } else {
        first.to_string()
    }
}

/// Strip a single matching pair of surrounding quotes (`'…'`, `"…"`, `` `…` ``).
fn strip_quotes(s: &str) -> &str {
    let bytes = s.as_bytes();
    if bytes.len() >= 2 {
        let first = bytes[0];
        let last = bytes[bytes.len() - 1];
        if (first == b'\'' || first == b'"' || first == b'`') && first == last {
            return &s[1..s.len() - 1];
        }
    }
    s
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

/// True if a direct, non-trivia token with the given text appears in the node's
/// own header tokens (used for `async`/`*` modifier detection on a definition).
fn has_token(item: &Node, src: &str, text: &str) -> bool {
    item.tokens().any(|t| t.span.text(src) == text)
}

fn tree_has_token(item: &Node, src: &str, text: &str) -> bool {
    item.walk()
        .any(|node| node.tokens().any(|token| token.span.text(src) == text))
}

fn import_edge_props(
    spec: &str,
    external: bool,
    reexport: bool,
    reexport_all: bool,
) -> Vec<(&'static str, Json)> {
    let mut props = vec![
        ("path", Json::str(spec.to_string())),
        ("external", Json::Bool(external)),
    ];
    if reexport {
        props.push(("reexport", Json::Bool(true)));
    }
    if reexport_all {
        props.push(("reexport_all", Json::Bool(true)));
    }
    props
}

fn append_export_props(props: &mut Vec<(&'static str, Json)>, item: &Node, src: &str) {
    if has_token(item, src, "export") {
        props.push(("exported", Json::Bool(true)));
        if has_token(item, src, "default") {
            props.push(("default_export", Json::Bool(true)));
        }
    }
}

fn is_commonjs_export_member(chain: &[String]) -> bool {
    matches!(chain, [root, _] if root == "exports")
        || matches!(chain, [module, exports, _] if module == "module" && exports == "exports")
}

/// The last string-literal token text in an import/export subtree — the module
/// specifier (it follows the `from` keyword, or is the only literal in
/// `import "x"`).
fn last_string_literal<'a>(item: &'a Node, src: &'a str) -> Option<&'a str> {
    let mut found = None;
    for n in item.walk() {
        for t in n.tokens() {
            if t.kind == tk::STRING {
                found = Some(t.span.text(src));
            }
        }
    }
    found
}

/// One `const`/`let`/`var` declarator: its bound name (None for a destructuring/
/// computed binder) plus the children of its initializer (after the first `=`).
struct Declarator<'a> {
    name: Option<&'a str>,
    name_start: u32,
    init: Vec<&'a Child>,
}

/// Split a variable `Header` into declarators on top-level commas. Nested commas
/// (inside `(…)`, `[…]`, `{…}`) are already collapsed into group nodes by the
/// parser, so a top-level `,` token always separates declarators.
fn split_declarators<'a>(header: &'a Node, src: &'a str) -> Vec<Declarator<'a>> {
    let mut decls = Vec::new();
    let mut cur: Vec<&'a Child> = Vec::new();
    for ch in &header.children {
        if let Child::Token(t) = ch {
            if !t.trivia && t.span.text(src) == "," {
                if let Some(d) = build_declarator(&cur, src) {
                    decls.push(d);
                }
                cur.clear();
                continue;
            }
            if t.trivia {
                continue;
            }
        }
        cur.push(ch);
    }
    if let Some(d) = build_declarator(&cur, src) {
        decls.push(d);
    }
    decls
}

/// Build one [`Declarator`]: the name is the leading identifier; the initializer
/// is every child after the first top-level `=`. A binder that begins with a
/// group (`{a}`, `[a]`) is destructuring → no single name.
fn build_declarator<'a>(children: &[&'a Child], src: &'a str) -> Option<Declarator<'a>> {
    if children.is_empty() {
        return None;
    }
    // A destructuring binder starts with a group node, not a name token.
    if matches!(children.first(), Some(Child::Node(_))) {
        return None;
    }
    let mut name = None;
    let mut name_start = 0u32;
    let mut eq_idx = None;
    for (idx, ch) in children.iter().enumerate() {
        if let Child::Token(t) = ch {
            let text = t.span.text(src);
            if name.is_none() && t.kind == tk::NAME && !is_keyword(text) {
                name = Some(text);
                name_start = t.span.start;
            }
            if text == "=" && eq_idx.is_none() {
                eq_idx = Some(idx);
            }
        }
    }
    let init: Vec<&'a Child> = match eq_idx {
        Some(i) => children[i + 1..].to_vec(),
        None => Vec::new(),
    };
    Some(Declarator {
        name,
        name_start,
        init,
    })
}

/// True if an initializer (the direct children after `=`) is an arrow or function
/// expression: a top-level `=>` or `function` token. The token must be *direct*
/// (not buried in a group) so a callback argument like `arr.map(x => x)` — whose
/// `=>` lives inside the `(…)` group — is never mistaken for a definition.
fn init_is_function(init: &[&Child], src: &str) -> bool {
    init.iter().any(|c| match c {
        Child::Token(t) if !t.trivia => {
            let x = t.span.text(src);
            x == "=>" || x == "function"
        }
        _ => false,
    })
}

/// True if a direct (non-group) token with `text` appears in the initializer —
/// used for the `async` / `*` modifiers of a function expression.
fn init_has_token(init: &[&Child], src: &str, text: &str) -> bool {
    init.iter()
        .any(|c| matches!(c, Child::Token(t) if !t.trivia && t.span.text(src) == text))
}

/// The first direct `{…}` brace group in an initializer (a function body, or an
/// object literal). Params `(…)` are never returned here.
fn first_brace<'a>(init: &[&'a Child]) -> Option<&'a Node> {
    for &c in init {
        if let Child::Node(n) = c {
            if n.kind == cst::BRACE {
                return Some(n);
            }
        }
    }
    None
}

/// If an initializer is exactly one `{…}` brace group (an object literal binding,
/// `const o = { … }`), return it; otherwise `None` (anything other than a lone
/// object literal — a call, ternary, etc. — is just data).
fn single_brace<'a>(init: &[&'a Child]) -> Option<&'a Node> {
    let mut found: Option<&'a Node> = None;
    for &c in init {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(_) => return None, // a stray token besides the brace
            Child::Node(n) => {
                if found.is_some() {
                    return None; // more than one group
                }
                found = Some(n);
            }
        }
    }
    match found {
        Some(n) if n.kind == cst::BRACE => Some(n),
        _ => None,
    }
}

/// Function-shaped class field (`handler = () => {}` / `h = function () {}`),
/// reading the `Header` after the `=`. `None` for an ordinary data field.
fn function_valued_field<'a>(member: &'a Node, src: &'a str) -> Option<FieldFn<'a>> {
    let header = member.child(cst::HEADER)?;
    let mut after_eq = false;
    let mut init: Vec<&'a Child> = Vec::new();
    for ch in &header.children {
        if let Child::Token(t) = ch {
            if t.trivia {
                continue;
            }
            if !after_eq {
                if t.span.text(src) == "=" {
                    after_eq = true;
                }
                continue;
            }
        }
        if after_eq {
            init.push(ch);
        }
    }
    if !init_is_function(&init, src) {
        return None;
    }
    Some(FieldFn {
        block: first_brace(&init),
        is_async: init_has_token(&init, src, "async"),
        is_generator: init_has_token(&init, src, "*"),
    })
}

/// The non-trivia direct children of a node, in order.
fn sig_children(node: &Node) -> Vec<&Child> {
    node.children
        .iter()
        .filter(|c| !matches!(c, Child::Token(t) if t.trivia))
        .collect()
}

/// A plain dotted member chain (`a`, `a.b`, `module.exports.foo`) read off the
/// left of an assignment: every element is a bare identifier joined by `.`. Any
/// call, index, computed member, or non-name token makes it `None` (we only name
/// honest member targets).
fn member_chain(lhs: &[&Child], src: &str) -> Option<Vec<String>> {
    let mut names = Vec::new();
    let mut expect_name = true;
    for ch in lhs {
        match ch {
            Child::Token(t) => {
                let text = t.span.text(src);
                if expect_name {
                    // Reserved words are valid member-path segments in JS
                    // (`app.delete`, `res.get`, `this.x`), so keywords are allowed
                    // here — this is an assignment LHS, never a keyword statement.
                    if t.kind == tk::NAME {
                        names.push(text.to_string());
                        expect_name = false;
                    } else {
                        return None;
                    }
                } else if text == "." {
                    expect_name = true;
                } else {
                    return None; // e.g. `?.`, `=`, an operator → not a plain chain
                }
            }
            Child::Node(_) => return None, // a group: call args, index, etc.
        }
    }
    if expect_name {
        // Trailing `.` with no final name.
        None
    } else {
        Some(names)
    }
}

/// The byte offset of the final name token in an assignment's left-hand member
/// chain (the function's own name), for line attribution.
fn name_start(lhs: &[&Child], _src: &str) -> Option<u32> {
    lhs.iter().rev().find_map(|c| match c {
        Child::Token(t) if t.kind == tk::NAME => Some(t.span.start),
        _ => None,
    })
}

/// Split an object-literal `{…}` brace group into its top-level entries (one per
/// property), dropping the outer braces. Nested groups are single elements, so a
/// top-level `,` always separates entries.
fn object_entries<'a>(brace: &'a Node, src: &'a str) -> Vec<Vec<&'a Child>> {
    let mut entries = Vec::new();
    let mut cur: Vec<&'a Child> = Vec::new();
    for ch in &brace.children {
        if let Child::Token(t) = ch {
            if t.trivia {
                continue;
            }
            let text = t.span.text(src);
            if text == "{" || text == "}" {
                continue; // outer delimiters
            }
            if text == "," {
                if !cur.is_empty() {
                    entries.push(std::mem::take(&mut cur));
                }
                continue;
            }
        }
        cur.push(ch);
    }
    if !cur.is_empty() {
        entries.push(cur);
    }
    entries
}

/// A function-valued object member discovered in an entry.
struct ObjectMember<'a> {
    name: String,
    name_start: u32,
    span_start: u32,
    span_end: u32,
    block: Option<&'a Node>,
    is_async: bool,
    is_generator: bool,
}

/// Detect a function-valued object-literal entry: a shorthand method
/// (`foo() {}`, `async foo() {}`, `get foo() {}`, `*foo() {}`) or a function-
/// valued property (`bar: () => …`, `baz: function () {}`). Data properties and
/// computed/spread entries return `None` (no honest name).
fn object_member<'a>(entry: &[&'a Child], src: &'a str) -> Option<ObjectMember<'a>> {
    let mut i = 0;
    let mut is_async = false;
    let mut is_generator = false;
    // Leading modifiers. `get`/`set`/`async` are modifiers only when a real name
    // follows; `get() {}` / `async: 1` keep the word as the property name.
    while i < entry.len() {
        if let Child::Token(t) = entry[i] {
            let text = t.span.text(src);
            if text == "*" {
                is_generator = true;
                i += 1;
                continue;
            }
            if matches!(text, "async" | "get" | "set") {
                let next = entry.get(i + 1).and_then(|c| match c {
                    Child::Token(t) => Some(t.span.text(src)),
                    Child::Node(_) => None,
                });
                if matches!(next, Some(":") | Some("(") | None) {
                    break; // the word is the property name, not a modifier
                }
                if text == "async" {
                    is_async = true;
                }
                i += 1;
                continue;
            }
        }
        break;
    }
    // The key: a bare identifier (reserved words are valid property keys, e.g.
    // `{ get: fn, delete: fn }`) or a string-literal key.
    let key_tok = match entry.get(i)? {
        Child::Token(t) if t.kind == tk::NAME => t,
        Child::Token(t) if t.kind == tk::STRING => t,
        _ => return None, // computed `[expr]`, spread `...`, number key, etc.
    };
    let name = if key_tok.kind == tk::STRING {
        strip_quotes(key_tok.span.text(src)).to_string()
    } else {
        key_tok.span.text(src).to_string()
    };
    if name.is_empty() {
        return None;
    }
    let name_start = key_tok.span.start;
    let span_end = entry
        .last()
        .map(|c| match c {
            Child::Token(t) => t.span.end,
            Child::Node(n) => n.span.end,
        })
        .unwrap_or(key_tok.span.end);

    match entry.get(i + 1) {
        // Shorthand method: `name (params) { … }`.
        Some(Child::Node(n)) if n.kind == cst::PAREN => Some(ObjectMember {
            name,
            name_start,
            span_start: name_start,
            span_end,
            block: first_brace(&entry[i + 2..]),
            is_async,
            is_generator,
        }),
        // Property: `name : <init>` where the init is an arrow/function.
        Some(Child::Token(t)) if t.span.text(src) == ":" => {
            let init = &entry[i + 2..];
            if !init_is_function(init, src) {
                return None;
            }
            Some(ObjectMember {
                name,
                name_start,
                span_start: name_start,
                span_end,
                block: first_brace(init),
                is_async: is_async || init_has_token(init, src, "async"),
                is_generator: is_generator || init_has_token(init, src, "*"),
            })
        }
        _ => None,
    }
}

/// The base-class simple name from a `class C extends Base …` header: the final
/// identifier of the `extends` clause (`Base` from `extends a.Base`), stopping at
/// `implements` / a group / end.
fn extends_base(item: &Node, src: &str) -> Option<String> {
    let header = item.child(cst::HEADER)?;
    let mut after_extends = false;
    let mut last: Option<String> = None;
    for ch in &header.children {
        match ch {
            Child::Token(t) if t.trivia => continue,
            Child::Token(t) => {
                let text = t.span.text(src);
                if text == "extends" {
                    after_extends = true;
                    last = None;
                } else if text == "implements" {
                    break;
                } else if after_extends && t.kind == tk::NAME && !is_keyword(text) {
                    last = Some(text.to_string());
                } else if after_extends && text != "." && last.is_some() {
                    // A non-dot, non-name token (e.g. `<` of generics) ends the
                    // simple-name case; keep whatever name we have.
                    break;
                }
            }
            Child::Node(_) => {
                if after_extends && last.is_some() {
                    break;
                }
            }
        }
    }
    last
}

/// Decorator names attached to a definition, as a JSON array (the last top-level
/// identifier of each `@expr`, e.g. `route` from `@app.route(...)`), or `None`.
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
                ident: t.kind == tk::NAME,
            }),
            Child::Node(n) => v.push(El::Grp(n)),
        }
    }
    v
}

/// Detect `name(...)` and `recv.name(...)` / `recv?.name(...)` call sites over the
/// real token tree, recursing into nested groups. Keywords are excluded, as is the
/// name in a `function`/`class` expression header.
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        // Member call: `.`/`?.` name `(...)`.
        if matches!(tok_text(&els[i]), Some(".") | Some("?.")) {
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
                        let name = tok_text(&els[i + 1]).unwrap_or("").to_string();
                        if !is_keyword(&name) {
                            out.push(Call {
                                name,
                                method: true,
                                receiver,
                            });
                        }
                        i += 3;
                        continue;
                    }
                }
            }
            i += 1;
            continue;
        }
        // Bare call: name `(...)`, not preceded by a member operator or a
        // `function`/`class` keyword (a definition, not a call).
        if is_ident_el(&els[i]) {
            let prev = if i > 0 { tok_text(&els[i - 1]) } else { None };
            let text = tok_text(&els[i]).unwrap_or("");
            let is_def = matches!(prev, Some("function") | Some("class"));
            let is_member = matches!(prev, Some(".") | Some("?."));
            if !is_member && !is_def && !is_keyword(text) && i + 1 < n {
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
    // Recurse into nested groups (never into nested definition nodes, which are
    // lowered as their own functions/methods).
    for e in &els {
        if let Some(g) = grp(e) {
            if g.kind != cst::FUNCTION && g.kind != cst::CLASS && g.kind != cst::METHOD {
                scan_calls(g, src, out);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::javascript::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("mod.js", src);
        let file = SourceFile {
            rel_path: "mod.js".to_string(),
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
        let g = graph_for("class C {\n  m() {}\n}\nfunction f() {}\n");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "f + C.m");
        assert_eq!(g.count_nodes_of(ont::TYPE), 1, "class C is a Type");
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "module mod");
        assert!(g.edges().any(|e| e.kind == edge::HAS_METHOD));
    }

    #[test]
    fn class_type_kind_is_class() {
        let g = graph_for("class C {}\n");
        let ty = g
            .nodes()
            .find(|n| n.kind == ont::TYPE)
            .expect("a Type node");
        assert_eq!(ty.props.get("type_kind"), Some(&Json::str("class")));
        assert_eq!(ty.props.get("language"), Some(&Json::str("javascript")));
    }

    #[test]
    fn resolves_unique_local_call() {
        let g = graph_for("function add(a, b) { return a + b; }\nfunction run() { add(1, 2); }\n");
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
    fn this_method_resolves_via_receiver() {
        let g = graph_for("class P {\n  a() { this.b(); }\n  b() {}\n}\n");
        let calls = call_edges(&g);
        let recv = calls
            .iter()
            .find(|e| e.props.get("resolution") == Some(&Json::str("receiver")));
        assert!(recv.is_some(), "this.b() should resolve via receiver scope");
        assert_eq!(recv.unwrap().props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for("function run() { mystery(); }\n");
        let calls = call_edges(&g);
        assert_eq!(calls.len(), 1);
        assert_eq!(
            calls[0].props.get("resolution"),
            Some(&Json::str("external"))
        );
        assert!(g.has_node("unresolved::mystery"));
    }

    #[test]
    fn external_and_relative_imports() {
        let g = graph_for("import React from 'react';\nimport { x } from './local';\n");
        assert!(g.has_node("ext::react"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::react"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::IMPORTS && e.to == "mod::./local"));
    }

    #[test]
    fn reexport_import_edges_match_typescript_props() {
        let g = graph_for("export { value } from './named';\nexport * from '@scope/pkg/all';\n");
        let named = g
            .edges()
            .find(|e| e.kind == edge::IMPORTS && e.props.get("path") == Some(&Json::str("./named")))
            .expect("named reexport edge");
        assert_eq!(named.props.get("reexport"), Some(&Json::Bool(true)));
        assert_eq!(named.props.get("reexport_all"), None);

        let all = g
            .edges()
            .find(|e| {
                e.kind == edge::IMPORTS && e.props.get("path") == Some(&Json::str("@scope/pkg/all"))
            })
            .expect("star reexport edge");
        assert_eq!(all.props.get("reexport"), Some(&Json::Bool(true)));
        assert_eq!(all.props.get("reexport_all"), Some(&Json::Bool(true)));
    }

    #[test]
    fn scoped_package_root() {
        let g = graph_for("import { z } from '@scope/pkg/sub';\n");
        assert!(g.has_node("ext::@scope/pkg"), "scoped pkg root collapsed");
    }

    #[test]
    fn inheritance_emits_extends() {
        let g = graph_for("class Base {}\nclass Derived extends Base {}\n");
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an EXTENDS edge");
        assert!(ext.from.starts_with("type::mod.Derived"));
        assert!(ext.to.starts_with("type::mod.Base"));
    }

    #[test]
    fn top_level_const_is_constant() {
        let g = graph_for("const VERSION = '1.0';\nclass C {}\n");
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 1);
        let c = g
            .nodes()
            .find(|n| n.kind == ont::CONSTANT)
            .expect("a constant");
        assert_eq!(c.name, "VERSION");
        assert_eq!(c.props.get("binding"), Some(&Json::str("const")));
    }

    #[test]
    fn decorator_recorded_as_property() {
        let g = graph_for("@sealed\nclass C {}\n");
        let ty = g
            .nodes()
            .find(|n| n.kind == ont::TYPE && n.name == "C")
            .expect("the decorated class");
        assert_eq!(
            ty.props.get("decorators"),
            Some(&Json::Array(vec![Json::str("sealed")]))
        );
    }

    #[test]
    fn output_is_deterministic() {
        let src = "import os from 'os';\nclass C extends Base {\n  m() { helper(); }\n}\nfunction helper() {}\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }

    // --- modern JS definition forms -----------------------------------------

    /// All `Function` node names in the graph.
    fn fn_names(g: &Graph) -> Vec<String> {
        let mut v: Vec<String> = g
            .nodes()
            .filter(|n| n.kind == ont::FUNCTION)
            .map(|n| n.name.clone())
            .collect();
        v.sort();
        v
    }

    fn function_named<'a>(g: &'a Graph, name: &str) -> &'a crate::graph::GraphNode {
        g.nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == name)
            .unwrap_or_else(|| panic!("expected a Function named {name}; got {:?}", fn_names(g)))
    }

    #[test]
    fn arrow_assigned_const_is_a_function() {
        let g = graph_for("const greet = (who) => { return who; };\n");
        let f = function_named(&g, "greet");
        assert_eq!(f.props.get("binding"), Some(&Json::str("const")));
        assert_eq!(f.props.get("has_body"), Some(&Json::Bool(true)));
        // Not also emitted as a Constant.
        assert_eq!(
            g.count_nodes_of(ont::CONSTANT),
            0,
            "greet is a fn, not a const"
        );
    }

    #[test]
    fn function_expression_assigned_is_a_function() {
        let g = graph_for("let make = function inner() {};\nvar gen = function* () {};\n");
        assert!(fn_names(&g).contains(&"make".to_string()));
        let gen = function_named(&g, "gen");
        assert_eq!(gen.props.get("is_generator"), Some(&Json::Bool(true)));
        assert_eq!(gen.props.get("binding"), Some(&Json::str("var")));
    }

    #[test]
    fn async_arrow_records_is_async() {
        let g = graph_for("const load = async () => { await x(); };\n");
        let f = function_named(&g, "load");
        assert_eq!(f.props.get("is_async"), Some(&Json::Bool(true)));
    }

    #[test]
    fn expression_bodied_arrow_has_no_body() {
        let g = graph_for("const id = x => x;\n");
        let f = function_named(&g, "id");
        assert_eq!(f.props.get("has_body"), Some(&Json::Bool(false)));
    }

    #[test]
    fn object_literal_methods_are_functions() {
        let g = graph_for(
            "const api = {\n  run() { return 1; },\n  stop: () => {},\n  load: function () {},\n  size: 42,\n};\n",
        );
        let names = fn_names(&g);
        assert!(
            names.contains(&"run".to_string()),
            "shorthand method: {names:?}"
        );
        assert!(
            names.contains(&"stop".to_string()),
            "arrow property: {names:?}"
        );
        assert!(
            names.contains(&"load".to_string()),
            "fn-expr property: {names:?}"
        );
        assert!(
            !names.contains(&"size".to_string()),
            "data prop is not a fn"
        );
        // The binding itself is still a Constant (the object value).
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::CONSTANT && n.name == "api"));
        // Object methods carry their containing binding as a textual receiver.
        let run = function_named(&g, "run");
        assert_eq!(run.props.get("receiver"), Some(&Json::str("api")));
        assert_eq!(run.props.get("binding"), Some(&Json::str("object_method")));
    }

    #[test]
    fn class_field_assigned_function_is_a_method() {
        let g = graph_for("class C {\n  handler = () => { return 1; };\n  data = 7;\n}\n");
        let f = function_named(&g, "handler");
        assert_eq!(f.props.get("is_method"), Some(&Json::Bool(true)));
        assert_eq!(f.props.get("receiver_type"), Some(&Json::str("C")));
        assert_eq!(f.props.get("binding"), Some(&Json::str("field")));
        // HAS_METHOD links the class to the field-function.
        assert!(g
            .edges()
            .any(|e| e.kind == edge::HAS_METHOD && e.to == f.id));
        // The data field is not a function.
        assert!(!fn_names(&g).contains(&"data".to_string()));
    }

    #[test]
    fn exports_member_assignment_is_a_function() {
        let g = graph_for(
            "exports.send = function () {};\nmodule.exports.json = () => {};\nObj.prototype.run = function () {};\n",
        );
        let names = fn_names(&g);
        assert!(
            names.contains(&"send".to_string()),
            "exports.send: {names:?}"
        );
        assert!(
            names.contains(&"json".to_string()),
            "module.exports.json: {names:?}"
        );
        assert!(
            names.contains(&"run".to_string()),
            "prototype.run: {names:?}"
        );
        let run = function_named(&g, "run");
        assert_eq!(run.props.get("receiver"), Some(&Json::str("Obj.prototype")));
        assert_eq!(run.props.get("binding"), Some(&Json::str("assignment")));
    }

    #[test]
    fn module_exports_object_methods_are_functions() {
        let g = graph_for("module.exports = {\n  foo() {},\n  bar: () => {},\n};\n");
        let names = fn_names(&g);
        assert!(names.contains(&"foo".to_string()), "{names:?}");
        assert!(names.contains(&"bar".to_string()), "{names:?}");
    }

    #[test]
    fn reserved_words_are_valid_member_and_property_names() {
        // `get`/`set`/`delete` are reserved words but legal as property keys and
        // member-access names in JS (express defines `app.set`, `res.get`, and
        // object routes `{ get: fn, delete: fn }`). They must still be extracted.
        let g = graph_for(
            "app.set = function set() {};\nres.get = function () {};\nvar users = {\n  get: function () {},\n  delete: function () {},\n};\n",
        );
        let names = fn_names(&g);
        for n in ["set", "get", "delete"] {
            assert!(names.contains(&n.to_string()), "missing {n}: {names:?}");
        }
    }

    #[test]
    fn anonymous_callbacks_are_not_definitions() {
        // The `=>` lives inside the call-argument group, never a top-level binding.
        let g = graph_for(
            "const items = list.map(x => x + 1);\nrun(() => doThing());\narr.forEach(function (e) { use(e); });\n",
        );
        assert_eq!(
            g.count_nodes_of(ont::FUNCTION),
            0,
            "no anonymous callback may become a Function: {:?}",
            fn_names(&g)
        );
        // `items` is still recorded as a plain data Constant.
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::CONSTANT && n.name == "items"));
    }

    #[test]
    fn plain_const_stays_constant() {
        let g = graph_for("const MAX = 10;\nconst cfg = { a: 1, b: 2 };\n");
        assert_eq!(g.count_nodes_of(ont::FUNCTION), 0);
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 2);
    }

    #[test]
    fn arrow_const_body_calls_are_scanned() {
        // The arrow's body must be scanned for calls, attributed to `run`.
        let g = graph_for("function helper() {}\nconst run = () => { helper(); };\n");
        let calls = call_edges(&g);
        let call = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("helper")))
            .expect("run() should call helper");
        assert_eq!(call.props.get("resolved"), Some(&Json::Bool(true)));
        let run = function_named(&g, "run");
        assert_eq!(call.from, run.id);
    }

    #[test]
    fn multiple_declarators_each_classified() {
        let g = graph_for("const a = () => {}, b = 2, c = function () {};\n");
        let names = fn_names(&g);
        assert!(names.contains(&"a".to_string()), "{names:?}");
        assert!(names.contains(&"c".to_string()), "{names:?}");
        assert!(!names.contains(&"b".to_string()));
        assert!(g.nodes().any(|n| n.kind == ont::CONSTANT && n.name == "b"));
    }
    #[test]
    fn esm_exports_mark_only_exported_declarations() {
        let g = graph_for(
            "export function exported_fn() {}\n\
             function private_fn() {}\n\
             export class ExportedClass {}\n\
             class PrivateClass {}\n\
             export const EXPORTED_CONST = 1;\n\
             const PRIVATE_CONST = 1;\n\
             export default function chosen() {}\n",
        );
        for name in ["exported_fn", "ExportedClass", "EXPORTED_CONST", "chosen"] {
            let node = g
                .nodes()
                .find(|n| n.name == name)
                .unwrap_or_else(|| panic!("expected node named {name}"));
            assert_eq!(
                node.props.get("exported"),
                Some(&Json::Bool(true)),
                "{name}"
            );
        }
        for name in ["private_fn", "PrivateClass", "PRIVATE_CONST"] {
            let node = g
                .nodes()
                .find(|n| n.name == name)
                .unwrap_or_else(|| panic!("expected node named {name}"));
            assert_eq!(node.props.get("exported"), None, "{name}");
        }
        let default = function_named(&g, "chosen");
        assert_eq!(default.props.get("default_export"), Some(&Json::Bool(true)));
    }

    #[test]
    fn commonjs_export_shapes_mark_only_public_functions() {
        let g = graph_for(
            "exports.send = function () {};\n\
             module.exports.json = () => {};\n\
             module.exports = { foo() {}, bar: () => {} };\n\
             Obj.prototype.run = function () {};\n",
        );
        for name in ["send", "json", "foo", "bar"] {
            let node = function_named(&g, name);
            assert_eq!(
                node.props.get("exported"),
                Some(&Json::Bool(true)),
                "{name}"
            );
        }
        assert_eq!(function_named(&g, "run").props.get("exported"), None);
    }
}
