//! Lower the Perl CST into the canonical graph.
//!
//! This mirrors the Ruby lowering ([`crate::lang::ruby::lower`]) — same
//! conservative principles, same shared ontology — adapted to Perl's surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to a
//!    concrete project definition only when a scope level yields exactly one
//!    candidate; several candidates are emitted as an ambiguous edge with the full
//!    `candidates` set; none resolves to an explicit `UnresolvedSymbol` node.
//! 2. **Everything comes from real tokens.** Calls, imports, parent classes, and
//!    constants are read off the lossless tree, never guessed.
//!
//! Honest mappings (see the IR Atlas):
//!   `sub name { … }` → `Function`; `package Foo;` / `package Foo { … }` →
//!   `Module` (a Perl package is a namespace — the honest fit; its subs are
//!   `DECLARES`d by the namespace as well as the file); `use`/`require`/`no` →
//!   `IMPORTS` (plus `ExternalDependency` / `DEPENDS_ON` for CPAN/core modules);
//!   `use parent`/`use base` → `EXTENDS` from the current package to its base
//!   (cheap and idiomatic — Perl OO inheritance is exactly an `@ISA` push);
//!   `use constant NAME => …` and top-level `our`/`my` declarations → `Constant`;
//!   `name(...)`, `&name`, and `->method(...)` → `CALLS`.
//!
//! Resolution uses a deterministic **scope ladder** (most specific first): a bare
//! call resolves against the enclosing package's subs, then the global sub table;
//! a `->method` has an unknown receiver type (no inference in an airgap), so it
//! resolves against the global table by simple name, preserving any ambiguity.
//!
//! Notes / coarseness (honest): Perl has no static types, so no `USES_TYPE` edges
//! are emitted; method receivers are not resolved to a concrete package; and a
//! `package Foo;` namespace is assumed to extend to the end of the file (the usual
//! single-package-per-file convention), which the in-order sibling walk models.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::perl::lexer::{is_keyword, kind as tk};
use crate::lang::perl::parser::node as cst;

/// Lower a whole project's worth of Perl files into a graph. `manifest_deps` is
/// unused (the pipeline's manifest reader is Cargo-only); dependencies are
/// discovered from `use`/`require` statements instead.
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
        fn_by_scope: BTreeMap::new(),
        pkg_by_name: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("perl"))],
    );

    let mut pend_fns: Vec<PendingFn> = Vec::new();
    let mut pend_extends: Vec<PendingLink> = Vec::new();

    for f in files.iter() {
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
                ("language", Json::str("perl")),
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
            pend_extends: &mut pend_extends,
        };
        lo.walk_stmts(f.root, None, false, &mut w);
    }

    // Pass C: resolve calls and parent-class links against the complete tables.
    for pf in &pend_fns {
        let mut calls = Vec::new();
        scan_calls(pf.body, pf.source, &mut calls);
        for call in &calls {
            let res = lo.resolve(call, &pf.scope_key);
            lo.emit_call(&pf.id, call, res);
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
    /// Simple sub name → all function node ids (global level).
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// (scope_key, simple_name) → function ids (local-package level). `scope_key`
    /// is the enclosing package name, or the file's module-join when there is none.
    fn_by_scope: BTreeMap<(String, String), Vec<String>>,
    /// Package simple/qualified name → namespace module node id.
    pkg_by_name: BTreeMap<String, String>,
}

struct Walk<'a, 's> {
    file_id: &'s str,
    module_join: &'s str,
    src: &'a str,
    li: &'s LineIndex,
    pend_fns: &'s mut Vec<PendingFn<'a>>,
    pend_extends: &'s mut Vec<PendingLink>,
}

struct PendingFn<'a> {
    id: String,
    source: &'a str,
    body: &'a Node,
    scope_key: String,
}

/// A deferred `EXTENDS` link (`use parent`/`use base`), resolved in pass C.
struct PendingLink {
    from_id: String,
    target_name: String,
}

struct Call {
    name: String,
    method: bool,
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
                vec![("language", Json::str("perl"))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    /// Walk a statement container in order. `cur_pkg` is the active `package`
    /// namespace (a bare `package Foo;` updates it for the following siblings; a
    /// `package Foo { … }` scopes it to the block). `in_sub` gates `Constant`
    /// emission to top-level declarations only.
    fn walk_stmts<'a>(
        &mut self,
        container: &'a Node,
        cur_pkg: Option<&str>,
        in_sub: bool,
        w: &mut Walk<'a, '_>,
    ) {
        let mut pkg: Option<String> = cur_pkg.map(|s| s.to_string());
        for item in container.child_nodes() {
            match item.kind {
                cst::PACKAGE => {
                    let name = name_of(item, w.src);
                    if let Some(name) = name {
                        let ns_id = self.declare_package(&name, w);
                        if let Some(block) = item.child(cst::BLOCK) {
                            self.walk_pkg_block(block, &name, &ns_id, w);
                        } else {
                            // Namespace applies to the following siblings.
                            pkg = Some(name);
                        }
                    }
                }
                cst::SUB => {
                    self.handle_sub(item, pkg.as_deref(), w);
                }
                cst::USE => {
                    self.handle_use(item, pkg.as_deref(), in_sub, w);
                }
                cst::BLOCK => {
                    // A bare block: same package, not a constant scope.
                    self.walk_stmts(item, pkg.as_deref(), in_sub, w);
                }
                cst::EXPR_STMT => {
                    if !in_sub {
                        self.handle_const_decl(item, pkg.as_deref(), w);
                    }
                }
                _ => {}
            }
        }
    }

    /// Walk a `package Foo { … }` block body with `Foo` as the active package.
    fn walk_pkg_block<'a>(
        &mut self,
        block: &'a Node,
        pkg_name: &str,
        ns_id: &str,
        w: &mut Walk<'a, '_>,
    ) {
        for item in block.child_nodes() {
            match item.kind {
                cst::SUB => self.handle_sub(item, Some(pkg_name), w),
                cst::USE => self.handle_use(item, Some(pkg_name), false, w),
                cst::EXPR_STMT => self.handle_const_decl(item, Some(pkg_name), w),
                cst::PACKAGE | cst::BLOCK => {
                    self.walk_stmts(item, Some(pkg_name), false, w);
                }
                _ => {}
            }
        }
        let _ = ns_id;
    }

    /// Declare a `package` namespace as a `Module` node and return its id.
    fn declare_package(&mut self, name: &str, w: &mut Walk<'_, '_>) -> String {
        let id = format!("ns::{name}");
        let simple = name.rsplit("::").next().unwrap_or(name).to_string();
        self.g.upsert_node(
            id.clone(),
            ont::MODULE,
            simple,
            vec![
                ("type_kind", Json::str("package")),
                ("qualified_name", Json::str(name.to_string())),
                ("language", Json::str("perl")),
            ],
        );
        self.g
            .add_edge(w.file_id, edge::DECLARES, id.clone(), vec![]);
        self.pkg_by_name
            .entry(name.to_string())
            .or_insert(id.clone());
        id
    }

    fn handle_sub<'a>(&mut self, item: &'a Node, cur_pkg: Option<&str>, w: &mut Walk<'a, '_>) {
        let raw_name = match name_of(item, w.src) {
            Some(n) => n,
            None => return,
        };
        // A fully-qualified `sub Foo::bar` carries its own package.
        let (scope_pkg, simple) = match raw_name.rsplit_once("::") {
            Some((p, s)) => (Some(p.to_string()), s.to_string()),
            None => (cur_pkg.map(|s| s.to_string()), raw_name.clone()),
        };
        let (display_qual, scope_key) = match &scope_pkg {
            Some(p) => (format!("{p}::{simple}"), p.clone()),
            None => (
                qual_name(w.module_join, &simple),
                if w.module_join.is_empty() {
                    self.package.clone()
                } else {
                    w.module_join.to_string()
                },
            ),
        };
        let line = w.li.line_col(name_span_start(item)).line;
        let id = format!("fn::{display_qual}#{line}");
        let has_body = item.child(cst::BLOCK).is_some();
        let mut props = vec![
            ("qualified_name", Json::str(display_qual)),
            ("language", Json::str("perl")),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            ("has_body", Json::Bool(has_body)),
        ];
        if let Some(p) = &scope_pkg {
            props.push(("package", Json::str(p.clone())));
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, simple.clone(), props);
        self.g
            .add_edge(w.file_id, edge::DECLARES, id.clone(), vec![]);
        // A sub inside a package is also declared by that namespace module.
        if let Some(p) = &scope_pkg {
            if let Some(ns) = self.pkg_by_name.get(p) {
                self.g
                    .add_edge(ns.clone(), edge::DECLARES, id.clone(), vec![]);
            }
        }

        self.fn_by_name
            .entry(simple.clone())
            .or_default()
            .push(id.clone());
        self.fn_by_scope
            .entry((scope_key.clone(), simple.clone()))
            .or_default()
            .push(id.clone());

        let body: &Node = item.child(cst::BLOCK).unwrap_or(item);
        w.pend_fns.push(PendingFn {
            id,
            source: w.src,
            body,
            scope_key,
        });

        // Recurse the body for nested named subs (closures defining subs).
        if let Some(block) = item.child(cst::BLOCK) {
            self.walk_stmts(block, cur_pkg, true, w);
        }
    }

    /// `use`/`no`/`require` → imports, parent-class links, or constants.
    fn handle_use<'a>(
        &mut self,
        item: &'a Node,
        cur_pkg: Option<&str>,
        in_sub: bool,
        w: &mut Walk<'a, '_>,
    ) {
        let toks = flat_tokens(item, w.src);
        // toks[0] is the keyword (use/no/require).
        let modtok = match toks.get(1) {
            Some(t) => t,
            None => return,
        };
        if modtok.kind == tk::STRING {
            // `require "file.pl";`
            let path = strip_quotes(modtok.text);
            self.emit_import(w.file_id, &path, &path);
            return;
        }
        if modtok.kind != tk::IDENT {
            return; // e.g. `use 5.010;` version
        }
        let name = modtok.text.to_string();
        match name.as_str() {
            "constant" => {
                if !in_sub {
                    self.emit_use_constants(&toks, cur_pkg, w);
                }
            }
            "parent" | "base" => {
                // The pragma itself is a core dependency.
                self.emit_import(w.file_id, &name, &name);
                if let Some(pkg) = cur_pkg {
                    if let Some(from_id) = self.pkg_by_name.get(pkg).cloned() {
                        for base in parent_names(&toks) {
                            w.pend_extends.push(PendingLink {
                                from_id: from_id.clone(),
                                target_name: base,
                            });
                        }
                    }
                }
            }
            _ => {
                let root = name.split("::").next().unwrap_or(&name).to_string();
                self.emit_import_named(w.file_id, &name, &root);
            }
        }
    }

    /// Emit `Constant` nodes for `use constant NAME => …` / `use constant { … }`.
    fn emit_use_constants(&mut self, toks: &[Tok<'_>], cur_pkg: Option<&str>, w: &Walk<'_, '_>) {
        let base = const_base(cur_pkg, w.module_join);
        for (i, t) in toks.iter().enumerate() {
            if t.kind != tk::IDENT {
                continue;
            }
            if i == 0 || t.text == "constant" {
                continue;
            }
            if toks.get(i + 1).map(|n| n.text) == Some("=>") {
                self.emit_constant(&base, t.text, t.text, t.span_start, w);
            }
        }
    }

    /// `my`/`our`/`local`/`state` top-level variable declaration → `Constant`(s).
    fn handle_const_decl(&mut self, item: &Node, cur_pkg: Option<&str>, w: &Walk<'_, '_>) {
        let toks = flat_tokens(item, w.src);
        let first = match toks.first() {
            Some(t) => t,
            None => return,
        };
        if !matches!(first.text, "my" | "our" | "local" | "state") {
            return;
        }
        let base = const_base(cur_pkg, w.module_join);
        for t in toks.iter().skip(1) {
            if t.text == "=" || t.text == ";" {
                break;
            }
            if matches!(t.kind, tk::SCALAR_VAR | tk::ARRAY_VAR | tk::HASH_VAR) {
                let bare = t.text.trim_start_matches(['$', '@', '%']);
                if !bare.is_empty() {
                    self.emit_constant(&base, t.text, bare, t.span_start, w);
                }
            }
        }
    }

    fn emit_constant(
        &mut self,
        base: &str,
        display_name: &str,
        bare: &str,
        span_start: u32,
        w: &Walk<'_, '_>,
    ) {
        let id = if base.is_empty() {
            format!("const::{bare}")
        } else {
            format!("const::{base}::{bare}")
        };
        let line = w.li.line_col(span_start).line;
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            display_name.to_string(),
            vec![
                ("binding", Json::str("constant")),
                ("language", Json::str("perl")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(w.file_id, edge::DECLARES, id, vec![]);
    }

    /// Emit `IMPORTS` for a `require "path"` style import (no module root).
    fn emit_import(&mut self, file_id: &str, path: &str, root: &str) {
        if path.is_empty() {
            return;
        }
        let dep_id = ext_id(root);
        self.g.upsert_node(
            dep_id.clone(),
            ont::EXTERNAL_DEPENDENCY,
            root.to_string(),
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
                ("path", Json::str(path.to_string())),
                ("external", Json::Bool(true)),
            ],
        );
        self.g
            .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
    }

    /// Emit `IMPORTS` for a `use Module` import, internal or external by root.
    fn emit_import_named(&mut self, file_id: &str, full: &str, root: &str) {
        if self.local_roots.contains(root) {
            let mod_id = format!("mod::{root}");
            self.g.upsert_node(
                mod_id.clone(),
                ont::MODULE,
                root.to_string(),
                vec![("language", Json::str("perl"))],
            );
            self.g.add_edge(
                file_id,
                edge::IMPORTS,
                mod_id,
                vec![
                    ("path", Json::str(full.to_string())),
                    ("external", Json::Bool(false)),
                ],
            );
        } else {
            self.emit_import(file_id, full, root);
        }
    }

    fn emit_extends(&mut self, link: &PendingLink) {
        let target = match self.pkg_by_name.get(&link.target_name) {
            Some(id) => id.clone(),
            None => {
                let id = unresolved_id(&link.target_name);
                if !self.g.has_node(&id) {
                    self.g.upsert_node(
                        id.clone(),
                        ont::UNRESOLVED,
                        link.target_name.clone(),
                        vec![
                            ("unresolved", Json::Bool(true)),
                            ("role", Json::str("parent")),
                        ],
                    );
                }
                id
            }
        };
        self.g.add_edge(
            link.from_id.clone(),
            edge::EXTENDS,
            target,
            vec![("target_name", Json::str(link.target_name.clone()))],
        );
    }

    // --- resolution ladder --------------------------------------------------

    fn resolve(&self, call: &Call, scope_key: &str) -> Resolution {
        if call.method {
            // Unknown receiver type: resolve globally by simple name.
            let c = self.fn_by_name.get(&call.name).cloned().unwrap_or_default();
            return if c.is_empty() {
                Resolution {
                    outcome: Outcome::None,
                    level: "external",
                }
            } else {
                mk(c, "global_method")
            };
        }
        // Bare call: enclosing package first, then global.
        let c = self
            .fn_by_scope
            .get(&(scope_key.to_string(), call.name.clone()))
            .cloned()
            .unwrap_or_default();
        if !c.is_empty() {
            return mk(c, "local");
        }
        let c = self.fn_by_name.get(&call.name).cloned().unwrap_or_default();
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

fn qual_name(module_join: &str, name: &str) -> String {
    if module_join.is_empty() {
        name.to_string()
    } else {
        format!("{module_join}.{name}")
    }
}

fn const_base(cur_pkg: Option<&str>, module_join: &str) -> String {
    match cur_pkg {
        Some(p) => p.to_string(),
        None => module_join.to_string(),
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

/// The first identifier of a `Name` child (a sub or package name).
fn name_of(item: &Node, src: &str) -> Option<String> {
    let nm = item.child(cst::NAME)?;
    nm.tokens()
        .find(|t| t.kind == tk::IDENT)
        .map(|t| t.span.text(src).to_string())
}

fn name_span_start(item: &Node) -> u32 {
    item.child(cst::NAME)
        .map(|n| n.span.start)
        .unwrap_or(item.span.start)
}

fn strip_quotes(s: &str) -> String {
    let bytes = s.as_bytes();
    if bytes.len() >= 2 {
        let first = bytes[0];
        let last = bytes[bytes.len() - 1];
        if (first == b'"' || first == b'\'' || first == b'`') && last == first {
            return s[1..s.len() - 1].to_string();
        }
    }
    s.to_string()
}

/// Parent class names from a `use parent`/`use base` statement: barewords, quoted
/// strings, and `qw(...)` word lists, skipping the `-norequire` flag.
fn parent_names(toks: &[Tok<'_>]) -> Vec<String> {
    let mut names = Vec::new();
    for (i, t) in toks.iter().enumerate().skip(2) {
        // Skip flags like `-norequire` (a `-` immediately precedes the bareword).
        let preceded_by_dash = toks.get(i - 1).map(|p| p.text) == Some("-");
        match t.kind {
            tk::IDENT => {
                if !is_keyword(t.text) && !preceded_by_dash {
                    names.push(t.text.to_string());
                }
            }
            tk::STRING => {
                if let Some(words) = qw_words(t.text) {
                    names.extend(words);
                } else {
                    let s = strip_quotes(t.text);
                    if !s.is_empty() && s != "-norequire" {
                        names.push(s);
                    }
                }
            }
            _ => {}
        }
    }
    names
}

/// Split a `qw(a b c)` literal into its words, or `None` if not a `qw` literal.
fn qw_words(s: &str) -> Option<Vec<String>> {
    if !s.starts_with("qw") {
        return None;
    }
    let inner = &s[2..];
    let mut chars = inner.chars();
    let open = chars.next()?;
    let close = match open {
        '(' => ')',
        '[' => ']',
        '{' => '}',
        '<' => '>',
        other => other,
    };
    let body = inner
        .strip_prefix(open)
        .and_then(|b| b.strip_suffix(close))
        .unwrap_or("");
    Some(body.split_whitespace().map(|w| w.to_string()).collect())
}

/// A flat token (text + kind + start) for the small token-list helpers.
#[derive(Clone, Copy)]
struct Tok<'a> {
    text: &'a str,
    kind: &'static str,
    span_start: u32,
}

/// All non-trivia tokens of a node subtree, in source order.
fn flat_tokens<'a>(node: &'a Node, src: &'a str) -> Vec<Tok<'a>> {
    let mut out = Vec::new();
    collect_tokens(node, src, &mut out);
    out
}

fn collect_tokens<'a>(node: &'a Node, src: &'a str, out: &mut Vec<Tok<'a>>) {
    for c in &node.children {
        match c {
            Child::Token(t) if !t.trivia => out.push(Tok {
                text: t.span.text(src),
                kind: t.kind,
                span_start: t.span.start,
            }),
            Child::Token(_) => {}
            Child::Node(n) => collect_tokens(n, src, out),
        }
    }
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

fn is_ident_el(e: &El) -> bool {
    matches!(e, El::Tok { kind, .. } if *kind == tk::IDENT)
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

fn is_def_node(kind: &str) -> bool {
    matches!(kind, cst::SUB | cst::PACKAGE)
}

/// Detect `name(...)`, `&name`, and `recv->method(...)`/`recv->method` call sites
/// over the real token tree, recursing into groups/blocks but **not** into nested
/// definitions (those are scanned as their own functions). Keywords are excluded.
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        // `&foo` / `&$code` sub-call sigil.
        if let El::Tok { text, kind } = &els[i] {
            if *kind == tk::AMP_VAR {
                let name = text.trim_start_matches(['&', '$']);
                if !name.is_empty() && !is_keyword(name) {
                    out.push(Call {
                        name: name.to_string(),
                        method: false,
                    });
                }
                i += 1;
                continue;
            }
        }
        // Method call: `->` name (optionally followed by `(...)`).
        if tok_text(&els[i]) == Some("->") {
            if i + 1 < n && is_ident_el(&els[i + 1]) {
                let name = tok_text(&els[i + 1]).unwrap_or("");
                if !is_keyword(name) {
                    out.push(Call {
                        name: name.to_string(),
                        method: true,
                    });
                }
                i += 2;
                continue;
            }
            i += 1;
            continue;
        }
        // Bare call: name `(...)`, not preceded by `->`/`sub`, not a keyword.
        if is_ident_el(&els[i]) {
            let prev = if i > 0 { tok_text(&els[i - 1]) } else { None };
            let text = tok_text(&els[i]).unwrap_or("");
            if prev != Some("->") && prev != Some("sub") && !is_keyword(text) && i + 1 < n {
                if let Some(g) = grp(&els[i + 1]) {
                    if g.kind == cst::PAREN {
                        out.push(Call {
                            name: text.to_string(),
                            method: false,
                        });
                    }
                }
            }
        }
        i += 1;
    }
    for e in &els {
        if let Some(g) = grp(e) {
            if !is_def_node(g.kind) {
                scan_calls(g, src, out);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::perl::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("app.pl", src);
        let file = SourceFile {
            rel_path: "app.pl".to_string(),
            module_path: vec!["app".to_string()],
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
        let g = graph_for("package C;\nsub m { 1 }\nsub f { 2 }\n");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "m + f");
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "package C is a Module");
        // The package namespace declares its subs.
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DECLARES && e.from.starts_with("ns::C")));
    }

    #[test]
    fn package_is_module_kind() {
        let g = graph_for("package Geo::Point;\nsub new { }\n");
        let m = g
            .nodes()
            .find(|n| n.kind == ont::MODULE && n.id == "ns::Geo::Point")
            .expect("a package module");
        assert_eq!(m.props.get("type_kind"), Some(&Json::str("package")));
        assert_eq!(m.props.get("language"), Some(&Json::str("perl")));
    }

    #[test]
    fn resolves_unique_local_call() {
        let g = graph_for("sub add { $_[0] + $_[1] }\nsub run { add(1, 2) }\n");
        let calls = call_edges(&g);
        let add = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("add")))
            .expect("a call to add");
        assert!(add.to.starts_with("fn::app.add"));
        assert_eq!(add.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(add.props.get("resolution"), Some(&Json::str("local")));
    }

    #[test]
    fn method_call_resolves_globally() {
        let g =
            graph_for("package P;\nsub greet { 1 }\nsub run { my $o = P->new; $o->greet(); }\n");
        let calls = call_edges(&g);
        let greet = calls.iter().find(|e| {
            e.props.get("callee") == Some(&Json::str("greet"))
                && e.props.get("method") == Some(&Json::Bool(true))
        });
        assert!(greet.is_some(), "->greet should be a method call");
    }

    #[test]
    fn amp_call_detected() {
        let g = graph_for("sub helper { 1 }\nsub run { &helper(); }\n");
        let calls = call_edges(&g);
        assert!(calls
            .iter()
            .any(|e| e.props.get("callee") == Some(&Json::str("helper"))));
    }

    #[test]
    fn unknown_call_is_external() {
        let g = graph_for("sub run { mystery(); }\n");
        let calls = call_edges(&g);
        assert!(calls
            .iter()
            .any(|e| e.props.get("resolution") == Some(&Json::str("external"))));
        assert!(g.has_node("unresolved::mystery"));
    }

    #[test]
    fn use_creates_dependency() {
        let g = graph_for("use strict;\nuse List::Util;\n");
        assert!(g.has_node("ext::strict"));
        assert!(g.has_node("ext::List"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::strict"));
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
    }

    #[test]
    fn use_parent_emits_extends() {
        let g = graph_for(
            "package Base;\nsub b { }\npackage Derived;\nuse parent -norequire, 'Base';\n",
        );
        let ext = g
            .edges()
            .find(|e| e.kind == edge::EXTENDS)
            .expect("an EXTENDS edge");
        assert!(ext.from.starts_with("ns::Derived"));
        assert!(ext.to.starts_with("ns::Base"));
    }

    #[test]
    fn use_constant_is_constant() {
        let g = graph_for("use constant PI => 3.14;\n");
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 1);
        let c = g
            .nodes()
            .find(|n| n.kind == ont::CONSTANT)
            .expect("a constant");
        assert_eq!(c.name, "PI");
    }

    #[test]
    fn our_declaration_is_constant() {
        let g = graph_for("our $VERSION = '1.0';\nsub f { my $local = 1; }\n");
        // VERSION is top-level; the in-sub $local is not.
        let consts: Vec<&str> = g
            .nodes()
            .filter(|n| n.kind == ont::CONSTANT)
            .map(|n| n.name.as_str())
            .collect();
        assert!(consts.contains(&"$VERSION"));
        assert!(!consts.contains(&"$local"));
    }

    #[test]
    fn output_is_deterministic() {
        let src =
            "use strict;\npackage P;\nuse parent 'Base';\nsub m { helper() }\nsub helper { 1 }\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
