//! Lower the WebAssembly text format CST into the canonical graph.
//!
//! Conservative, honest mappings (see the IR Atlas). A *form* is a parenthesized
//! list whose first keyword names the section/operator:
//!
//!   - `(module $name? …)`                      → `Module` (an explicit module; a
//!     file may also carry top-level fields with no `module` wrapper, which become
//!     one implicit module for the file)
//!   - `(func $name …)`                          → `Function`
//!   - `(type $name …)`                          → `Type` (`type_kind: func_type`)
//!   - `(global $name …)`                        → `Constant` (`binding: global`)
//!   - `(import "mod" "field" (func $n …))`     → `IMPORTS` + an `ExternalDependency`
//!     named `"mod.field"` (+ `DEPENDS_ON` from the package). An imported func with
//!     an `$id` is registered so calls to it resolve to the external dependency.
//!   - `(export "name" (func $x))`              → marks the referenced func (or
//!     global) `exported`. Inline `(func $f (export "name") …)` is also honored.
//!   - `(call $x)` / `call $x` (folded or flat) → `CALLS` to the referenced func.
//!   - `(call_indirect …)`                       → `CALLS` to an `UnresolvedSymbol`
//!     (the callee is dynamic, dispatched through a table at runtime).
//!
//! Principles carried over from the Rust/Clojure lowerings:
//!   1. **No fabricated targets.** A `CALLS` edge resolves to a concrete `Function`
//!      only when its `$id` names a func defined in (or imported into) the same
//!      module — WASM calls are module-scoped. An unknown `$id`, a numeric function
//!      index, or an indirect call resolves to an explicit `UnresolvedSymbol`
//!      instead of being guessed or dropped.
//!   2. **Everything comes from real tokens.** Names, module/field strings, and
//!      call targets are read off the lossless tree, never invented.
//!
//! Honest coverage gaps (documented, not hidden):
//!   - Numeric references (`(call 3)`, `(export "x" (func 0))`) are left
//!     **unresolved** rather than resolved against the func index space (which
//!     would require modeling imported-vs-defined index ordering).
//!   - `memory` / `table` / `data` / `elem` / `start` / `tag` sections and their
//!     exports are not modeled.
//!   - `.wast` script directives (`assert_*`, `invoke`, `register`) and
//!     `(module binary …)` / `(module quote …)` encoded modules are recognised but
//!     not lowered beyond a `Module` node.
//!   - Type signatures are not turned into `USES_TYPE` edges.

use std::collections::BTreeMap;

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::wasm::lexer::kind as tk;
use crate::lang::wasm::lexer::{is_close_delim, is_open_delim};
use crate::lang::wasm::parser::node as cst;

const LANG: &str = "wasm";

/// Lower a whole project's worth of WAT/WAST files into a graph. `manifest_deps`
/// is unused (the pipeline's manifest reader is Cargo-only); dependencies are
/// discovered from `import` forms instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id.clone(),
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str(LANG))],
    );

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
        lo.g.add_edge(pkg_id.clone(), edge::CONTAINS, file_id.clone(), vec![]);
        lo.process_file(f, &file_id, &li);
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
}

/// A call site discovered in a function body.
enum CallTarget {
    /// `(call $id)` / `call $id`.
    Named(String),
    /// `(call 3)` — a numeric function index (left unresolved).
    Index(String),
    /// `call_indirect` — dispatched dynamically through a table.
    Indirect,
}

impl Lowerer {
    fn pkg_id(&self) -> String {
        format!("pkg::{}", self.package)
    }

    /// Split a file's top-level forms into explicit `(module …)` declarations and
    /// loose fields (which form one implicit module for the file).
    fn process_file(&mut self, f: &SourceFile<'_>, file_id: &str, li: &LineIndex) {
        let src = f.source;
        let rel = f.rel_path.as_str();
        let stem = f
            .module_path
            .last()
            .cloned()
            .unwrap_or_else(|| stem_of(rel));

        let mut implicit: Vec<&Node> = Vec::new();
        let mut mod_idx = 0usize;
        for top in f.root.children_of(cst::SEXPR) {
            let tfs = forms(top, src);
            match head_kw(&tfs) {
                Some("module") => {
                    self.process_module(top, file_id, src, li, &stem, &mut mod_idx, rel)
                }
                Some(k) if is_field_kw(k) => implicit.push(top),
                _ => {} // a `.wast` directive (assert_*, invoke, register, …): punted
            }
        }

        if !implicit.is_empty() {
            let module_id = format!("mod::{rel}");
            let module_qual = rel.to_string();
            self.process_module_fields(
                &implicit,
                &module_id,
                &module_qual,
                &stem,
                file_id,
                src,
                li,
            );
        }
    }

    /// Build a `Module` for an explicit `(module …)` form and lower its fields.
    #[allow(clippy::too_many_arguments)]
    fn process_module(
        &mut self,
        m: &Node,
        file_id: &str,
        src: &str,
        li: &LineIndex,
        stem: &str,
        mod_idx: &mut usize,
        rel: &str,
    ) {
        let mfs = forms(m, src);
        let name_opt = first_id(&mfs);
        let (display, module_id) = match name_opt {
            Some((n, _)) => (
                n.trim_start_matches('$').to_string(),
                format!("mod::{rel}::{n}"),
            ),
            None => (stem.to_string(), format!("mod::{rel}#{}", *mod_idx)),
        };
        *mod_idx += 1;

        // `(module binary "…")` / `(module quote "…")` carry no lowerable fields.
        let encoded = mfs.iter().any(|e| {
            matches!(e, El::Tok { kind, text, .. }
                if *kind == tk::KEYWORD && (*text == "binary" || *text == "quote"))
        });
        if encoded {
            self.g.upsert_node(
                module_id.clone(),
                ont::MODULE,
                display,
                vec![("language", Json::str(LANG)), ("encoded", Json::Bool(true))],
            );
            self.g.add_edge(file_id, edge::CONTAINS, module_id, vec![]);
            return;
        }

        let module_qual = module_id
            .strip_prefix("mod::")
            .unwrap_or(&module_id)
            .to_string();
        let fields: Vec<&Node> = mfs
            .iter()
            .filter_map(|e| match e {
                El::Grp(g) => Some(*g),
                _ => None,
            })
            .collect();
        self.process_module_fields(
            &fields,
            &module_id,
            &module_qual,
            &display,
            file_id,
            src,
            li,
        );
    }

    /// Lower the field forms of one module: create the `Module` node, then run two
    /// phases — declarations (build the per-module symbol table) and references
    /// (resolve exports + calls against it).
    #[allow(clippy::too_many_arguments)]
    fn process_module_fields<'a>(
        &mut self,
        fields: &[&'a Node],
        module_id: &str,
        module_qual: &str,
        display: &str,
        file_id: &str,
        src: &'a str,
        li: &LineIndex,
    ) {
        self.g.upsert_node(
            module_id.to_string(),
            ont::MODULE,
            display.to_string(),
            vec![("language", Json::str(LANG))],
        );
        self.g
            .add_edge(file_id, edge::CONTAINS, module_id.to_string(), vec![]);

        // Per-module symbol tables (WASM references are module-scoped).
        let mut fn_by_name: BTreeMap<String, String> = BTreeMap::new();
        let mut const_by_name: BTreeMap<String, String> = BTreeMap::new();
        let mut imported_fn: BTreeMap<String, String> = BTreeMap::new();
        let mut def_idx = 0usize;
        let mut type_idx = 0usize;
        let mut glob_idx = 0usize;
        let mut exports: Vec<&Node> = Vec::new();
        let mut pending: Vec<(String, &'a Node)> = Vec::new();

        // --- phase 1: declarations ------------------------------------------
        for &fl in fields {
            let ffs = forms(fl, src);
            match head_kw(&ffs) {
                Some("func") => {
                    // An inline `(func (import "m" "n") …)` is an imported func.
                    if let Some(imp) = find_child_grp(&ffs, "import", src) {
                        let ifs = forms(imp, src);
                        let ext_id =
                            self.emit_external(module_id, nth_string(&ifs, 0), nth_string(&ifs, 1));
                        if let Some((n, _)) = first_id(&ffs) {
                            imported_fn.entry(n.to_string()).or_insert(ext_id);
                        }
                        continue;
                    }
                    let name_opt = first_id(&ffs);
                    let key = match name_opt {
                        Some((n, _)) => n.to_string(),
                        None => {
                            let k = format!("#{def_idx}");
                            def_idx += 1;
                            k
                        }
                    };
                    let line = li
                        .line_col(name_opt.map(|(_, s)| s).unwrap_or(fl.span.start))
                        .line;
                    let func_id = format!("fn::{module_qual}::{key}");
                    let mut props = vec![
                        ("qualified_name", Json::str(format!("{module_qual}::{key}"))),
                        ("language", Json::str(LANG)),
                        ("line", Json::U64(line as u64)),
                        ("span_start", Json::U64(fl.span.start as u64)),
                        ("span_end", Json::U64(fl.span.end as u64)),
                    ];
                    if let Some((ename, exp)) = inline_export(&ffs, src) {
                        props.push(("exported", Json::Bool(true)));
                        props.push(("export_name", Json::str(ename)));
                        let _ = exp;
                    }
                    self.g
                        .upsert_node(func_id.clone(), ont::FUNCTION, key.clone(), props);
                    self.g
                        .add_edge(module_id, edge::DECLARES, func_id.clone(), vec![]);
                    if let Some((n, _)) = name_opt {
                        fn_by_name.entry(n.to_string()).or_insert(func_id.clone());
                    }
                    pending.push((func_id, fl));
                }
                Some("type") => {
                    let name_opt = first_id(&ffs);
                    let key = match name_opt {
                        Some((n, _)) => n.to_string(),
                        None => {
                            let k = format!("#{type_idx}");
                            type_idx += 1;
                            k
                        }
                    };
                    let line = li
                        .line_col(name_opt.map(|(_, s)| s).unwrap_or(fl.span.start))
                        .line;
                    let type_id = format!("type::{module_qual}::{key}");
                    self.g.upsert_node(
                        type_id.clone(),
                        ont::TYPE,
                        key.clone(),
                        vec![
                            ("type_kind", Json::str("func_type")),
                            ("qualified_name", Json::str(format!("{module_qual}::{key}"))),
                            ("language", Json::str(LANG)),
                            ("line", Json::U64(line as u64)),
                        ],
                    );
                    self.g.add_edge(module_id, edge::DECLARES, type_id, vec![]);
                }
                Some("global") => {
                    // A `(global (import "m" "n") …)` is an imported global.
                    if let Some(imp) = find_child_grp(&ffs, "import", src) {
                        let ifs = forms(imp, src);
                        self.emit_external(module_id, nth_string(&ifs, 0), nth_string(&ifs, 1));
                        continue;
                    }
                    let name_opt = first_id(&ffs);
                    let key = match name_opt {
                        Some((n, _)) => n.to_string(),
                        None => {
                            let k = format!("#{glob_idx}");
                            glob_idx += 1;
                            k
                        }
                    };
                    let line = li
                        .line_col(name_opt.map(|(_, s)| s).unwrap_or(fl.span.start))
                        .line;
                    let mutable = find_child_grp(&ffs, "mut", src).is_some();
                    let const_id = format!("const::{module_qual}::{key}");
                    let mut props = vec![
                        ("binding", Json::str("global")),
                        ("qualified_name", Json::str(format!("{module_qual}::{key}"))),
                        ("language", Json::str(LANG)),
                        ("line", Json::U64(line as u64)),
                        ("mutable", Json::Bool(mutable)),
                    ];
                    if let Some((ename, _)) = inline_export(&ffs, src) {
                        props.push(("exported", Json::Bool(true)));
                        props.push(("export_name", Json::str(ename)));
                    }
                    self.g
                        .upsert_node(const_id.clone(), ont::CONSTANT, key.clone(), props);
                    self.g
                        .add_edge(module_id, edge::DECLARES, const_id.clone(), vec![]);
                    if let Some((n, _)) = name_opt {
                        const_by_name.entry(n.to_string()).or_insert(const_id);
                    }
                }
                Some("import") => {
                    let ext_id =
                        self.emit_external(module_id, nth_string(&ffs, 0), nth_string(&ffs, 1));
                    // An imported func with an `$id` becomes a resolvable call target.
                    if let Some(desc) = ffs.iter().find_map(|e| match e {
                        El::Grp(g) => Some(*g),
                        _ => None,
                    }) {
                        let dfs = forms(desc, src);
                        if head_kw(&dfs) == Some("func") {
                            if let Some((n, _)) = first_id(&dfs) {
                                imported_fn.entry(n.to_string()).or_insert(ext_id);
                            }
                        }
                    }
                }
                Some("export") => exports.push(fl),
                _ => {} // memory/table/data/elem/start/tag/rec: punted (see header)
            }
        }

        // --- phase 2: exports + calls ---------------------------------------
        for &e in &exports {
            self.handle_export(e, src, &fn_by_name, &const_by_name);
        }
        for (caller_id, node) in &pending {
            let node: &Node = node;
            let mut calls = Vec::new();
            scan_calls(node, src, &mut calls);
            for c in &calls {
                self.emit_call(caller_id, c, &fn_by_name, &imported_fn);
            }
        }
    }

    /// `(export "name" (func $x))` / `(export "name" (global $g))` — mark the
    /// referenced definition `exported`. Memory/table exports and numeric targets
    /// are punted (no node to attribute deterministically).
    fn handle_export(
        &mut self,
        fl: &Node,
        src: &str,
        fn_by_name: &BTreeMap<String, String>,
        const_by_name: &BTreeMap<String, String>,
    ) {
        let ffs = forms(fl, src);
        let ename = nth_string(&ffs, 0).map(unquote).unwrap_or_default();
        let desc = match ffs.iter().find_map(|e| match e {
            El::Grp(g) => Some(*g),
            _ => None,
        }) {
            Some(g) => g,
            None => return,
        };
        let dfs = forms(desc, src);
        let target = match first_id(&dfs) {
            Some((t, _)) => t,
            None => return, // numeric export target: punted
        };
        let (table, kind): (&BTreeMap<String, String>, &'static str) = match head_kw(&dfs) {
            Some("func") => (fn_by_name, ont::FUNCTION),
            Some("global") => (const_by_name, ont::CONSTANT),
            _ => return, // memory/table export: punted
        };
        if let Some(id) = table.get(target) {
            self.g.upsert_node(
                id.clone(),
                kind,
                String::new(),
                vec![
                    ("exported", Json::Bool(true)),
                    ("export_name", Json::str(ename)),
                ],
            );
        }
    }

    /// Emit an `ExternalDependency` for an `import` target plus the
    /// `IMPORTS` / `DEPENDS_ON` edge pair. The dependency is named `"mod.field"`.
    fn emit_external(&mut self, module_id: &str, m: Option<&str>, fld: Option<&str>) -> String {
        let mm = m.map(unquote).unwrap_or_default();
        let ff = fld.map(unquote).unwrap_or_default();
        let dotted = if ff.is_empty() {
            mm.clone()
        } else {
            format!("{mm}.{ff}")
        };
        let ext_id = format!("ext::{dotted}");
        self.g.upsert_node(
            ext_id.clone(),
            ont::EXTERNAL_DEPENDENCY,
            dotted.clone(),
            vec![
                ("external", Json::Bool(true)),
                ("source", Json::str("import")),
                ("module", Json::str(mm)),
                ("field", Json::str(ff)),
            ],
        );
        self.g.add_edge(
            module_id,
            edge::IMPORTS,
            ext_id.clone(),
            vec![("path", Json::str(dotted)), ("external", Json::Bool(true))],
        );
        self.g
            .add_edge(self.pkg_id(), edge::DEPENDS_ON, ext_id.clone(), vec![]);
        ext_id
    }

    /// Emit a `CALLS` edge. A `$id` matching a local func resolves to it; one
    /// matching an imported func resolves to its `ExternalDependency`; anything
    /// else (unknown id, numeric index, indirect dispatch) resolves to an explicit
    /// `UnresolvedSymbol` — honest about what could not be pinned down.
    fn emit_call(
        &mut self,
        caller: &str,
        t: &CallTarget,
        fn_by_name: &BTreeMap<String, String>,
        imported_fn: &BTreeMap<String, String>,
    ) {
        match t {
            CallTarget::Named(n) => {
                if let Some(fid) = fn_by_name.get(n) {
                    self.g.add_edge(
                        caller,
                        edge::CALLS,
                        fid.clone(),
                        vec![
                            ("callee", Json::str(n.clone())),
                            ("resolved", Json::Bool(true)),
                            ("call_kind", Json::str("direct")),
                        ],
                    );
                } else if let Some(ext) = imported_fn.get(n) {
                    self.g.add_edge(
                        caller,
                        edge::CALLS,
                        ext.clone(),
                        vec![
                            ("callee", Json::str(n.clone())),
                            ("resolved", Json::Bool(true)),
                            ("external", Json::Bool(true)),
                            ("call_kind", Json::str("import")),
                        ],
                    );
                } else {
                    let u = format!("unresolved::{n}");
                    self.upsert_unresolved(&u, n, "unknown function identifier");
                    self.g.add_edge(
                        caller,
                        edge::CALLS,
                        u,
                        vec![
                            ("callee", Json::str(n.clone())),
                            ("resolved", Json::Bool(false)),
                        ],
                    );
                }
            }
            CallTarget::Index(i) => {
                let name = format!("func[{i}]");
                let u = format!("unresolved::{name}");
                self.upsert_unresolved(&u, &name, "numeric function index (unresolved)");
                self.g.add_edge(
                    caller,
                    edge::CALLS,
                    u,
                    vec![
                        ("resolved", Json::Bool(false)),
                        ("index", Json::str(i.clone())),
                        ("call_kind", Json::str("numeric")),
                    ],
                );
            }
            CallTarget::Indirect => {
                let u = "unresolved::call_indirect".to_string();
                self.upsert_unresolved(&u, "call_indirect", "indirect call through a table");
                self.g.add_edge(
                    caller,
                    edge::CALLS,
                    u,
                    vec![
                        ("resolved", Json::Bool(false)),
                        ("indirect", Json::Bool(true)),
                        ("call_kind", Json::str("indirect")),
                    ],
                );
            }
        }
    }

    fn upsert_unresolved(&mut self, id: &str, name: &str, reason: &'static str) {
        if !self.g.has_node(id) {
            self.g.upsert_node(
                id.to_string(),
                ont::UNRESOLVED,
                name.to_string(),
                vec![
                    ("unresolved", Json::Bool(true)),
                    ("role", Json::str("call")),
                    ("reason", Json::str(reason)),
                ],
            );
        }
    }
}

// --- element model over the lossless tree -----------------------------------

/// A significant child of a form: a flat token or a nested `(…)` group. Trivia and
/// the `(`/`)` delimiter tokens are filtered out.
enum El<'a> {
    Tok {
        kind: &'static str,
        text: &'a str,
        start: u32,
    },
    Grp(&'a Node),
}

/// The significant elements of a node: non-trivia, non-delimiter tokens plus child
/// group nodes, in source order.
fn forms<'a>(node: &'a Node, src: &'a str) -> Vec<El<'a>> {
    let mut v = Vec::new();
    for c in &node.children {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) if is_open_delim(t.kind) || is_close_delim(t.kind) => {}
            Child::Token(t) => v.push(El::Tok {
                kind: t.kind,
                text: t.span.text(src),
                start: t.span.start,
            }),
            Child::Node(n) => v.push(El::Grp(n)),
        }
    }
    v
}

/// The head keyword of a list: its first element, only if a bare keyword token.
fn head_kw<'a>(fs: &[El<'a>]) -> Option<&'a str> {
    match fs.first() {
        Some(El::Tok { kind, text, .. }) if *kind == tk::KEYWORD => Some(*text),
        _ => None,
    }
}

/// The first identifier (`$id`) token in `fs`, with its byte offset.
fn first_id<'a>(fs: &[El<'a>]) -> Option<(&'a str, u32)> {
    fs.iter().find_map(|e| match e {
        El::Tok { kind, text, start } if *kind == tk::IDENTIFIER => Some((*text, *start)),
        _ => None,
    })
}

/// The `n`-th string-literal token text in `fs` (raw, including quotes).
fn nth_string<'a>(fs: &[El<'a>], n: usize) -> Option<&'a str> {
    fs.iter()
        .filter_map(|e| match e {
            El::Tok { kind, text, .. } if *kind == tk::STRING => Some(*text),
            _ => None,
        })
        .nth(n)
}

/// The first child group of `fs` whose head keyword is `head`.
fn find_child_grp<'a>(fs: &[El<'a>], head: &str, src: &'a str) -> Option<&'a Node> {
    fs.iter().find_map(|e| match e {
        El::Grp(g) if head_kw(&forms(g, src)) == Some(head) => Some(*g),
        _ => None,
    })
}

/// An inline `(export "name")` clause inside a `func`/`global` form, if present:
/// the export name and the clause node.
fn inline_export<'a>(fs: &[El<'a>], src: &'a str) -> Option<(String, &'a Node)> {
    let g = find_child_grp(fs, "export", src)?;
    let efs = forms(g, src);
    let name = nth_string(&efs, 0).map(unquote)?;
    Some((name, g))
}

// --- call detection over the lossless token tree ----------------------------

/// Collect call sites from a function form (recursively). Handles both folded
/// (`(call $x)`) and flat (`call $x`) instruction syntax uniformly: within any
/// list, a `call` keyword takes the next atom as its target, and `call_indirect`
/// is recorded as a dynamic call.
fn scan_calls(list: &Node, src: &str, out: &mut Vec<CallTarget>) {
    let fs = forms(list, src);
    for (i, el) in fs.iter().enumerate() {
        if let El::Tok { kind, text, .. } = el {
            if *kind == tk::KEYWORD {
                match *text {
                    "call" => {
                        if let Some(t) = next_call_target(&fs, i + 1) {
                            out.push(t);
                        }
                    }
                    "call_indirect" => out.push(CallTarget::Indirect),
                    _ => {}
                }
            }
        }
    }
    for el in &fs {
        if let El::Grp(g) = el {
            scan_calls(g, src, out);
        }
    }
}

/// The operand of a `call`: the next identifier or number atom. A group means the
/// next operand is folded (no static target token here), so no target is read.
fn next_call_target(fs: &[El<'_>], from: usize) -> Option<CallTarget> {
    for el in &fs[from.min(fs.len())..] {
        match el {
            El::Tok { kind, text, .. } if *kind == tk::IDENTIFIER => {
                return Some(CallTarget::Named(text.to_string()))
            }
            El::Tok { kind, text, .. } if *kind == tk::NUMBER => {
                return Some(CallTarget::Index(text.to_string()))
            }
            El::Grp(_) => return None,
            _ => continue,
        }
    }
    None
}

// --- pure helpers -----------------------------------------------------------

/// Strip surrounding `"` quotes from a string-literal token (escapes left as-is,
/// which is fine for a dependency/export name).
fn unquote(s: &str) -> String {
    let t = s.strip_prefix('"').unwrap_or(s);
    let t = t.strip_suffix('"').unwrap_or(t);
    t.to_string()
}

/// True for the module-field keywords that may appear at file top level (an
/// implicit, unwrapped module).
fn is_field_kw(k: &str) -> bool {
    matches!(
        k,
        "func"
            | "type"
            | "global"
            | "import"
            | "export"
            | "memory"
            | "table"
            | "data"
            | "elem"
            | "start"
            | "tag"
            | "rec"
    )
}

/// The file stem (no directory, no extension) — the implicit module name.
fn stem_of(rel: &str) -> String {
    let file = rel.rsplit('/').next().unwrap_or(rel);
    match file.rsplit_once('.') {
        Some((stem, _)) if !stem.is_empty() => stem.to_string(),
        _ => file.to_string(),
    }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::wasm::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("demo.wat", src);
        let file = SourceFile {
            rel_path: "demo.wat".to_string(),
            module_path: vec!["demo".to_string()],
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    fn call_edges(g: &Graph) -> Vec<&crate::graph::GraphEdge> {
        g.edges().filter(|e| e.kind == edge::CALLS).collect()
    }

    #[test]
    fn emits_function_module_type_constant() {
        let g = graph_for(
            "(module $m\n  (type $t (func (param i32)))\n  (global $g i32 (i32.const 1))\n  (func $f (result i32) (i32.const 0)))\n",
        );
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "module");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 1, "func");
        assert_eq!(g.count_nodes_of(ont::TYPE), 1, "type");
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 1, "global -> constant");
        let f = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "$f")
            .expect("$f");
        assert_eq!(f.props.get("language"), Some(&Json::str("wasm")));
    }

    #[test]
    fn implicit_module_without_wrapper() {
        let g = graph_for("(func $f (result i32) (i32.const 7))\n");
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "implicit module");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 1, "func still found");
    }

    #[test]
    fn import_is_external_dependency() {
        let g = graph_for("(module (import \"env\" \"log\" (func $log (param i32))))\n");
        assert!(g.has_node("ext::env.log"), "named mod.field external");
        let dep = g.nodes().find(|n| n.id == "ext::env.log").unwrap();
        assert_eq!(dep.kind, ont::EXTERNAL_DEPENDENCY);
        assert_eq!(dep.name, "env.log");
        assert!(
            g.edges()
                .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::env.log"),
            "DEPENDS_ON external"
        );
        assert!(
            g.edges().any(|e| e.kind == edge::IMPORTS),
            "an IMPORTS edge exists"
        );
    }

    #[test]
    fn export_marks_function() {
        let g =
            graph_for("(module (func $f (result i32) (i32.const 0)) (export \"go\" (func $f)))\n");
        let f = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "$f")
            .expect("$f");
        assert_eq!(f.props.get("exported"), Some(&Json::Bool(true)));
        assert_eq!(f.props.get("export_name"), Some(&Json::str("go")));
    }

    #[test]
    fn inline_export_marks_function() {
        let g = graph_for("(module (func $f (export \"go\") (result i32) (i32.const 0)))\n");
        let f = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "$f")
            .expect("$f");
        assert_eq!(f.props.get("exported"), Some(&Json::Bool(true)));
    }

    #[test]
    fn resolves_direct_call_folded_and_flat() {
        // folded `(call $h)` and flat `call $h` must both resolve.
        let g = graph_for(
            "(module (func $h (result i32) (i32.const 1))\n  (func $run (result i32) (call $h))\n  (func $run2 (result i32) call $h))\n",
        );
        let resolved: Vec<_> = call_edges(&g)
            .into_iter()
            .filter(|e| {
                e.props.get("resolved") == Some(&Json::Bool(true)) && e.to.starts_with("fn::")
            })
            .collect();
        assert!(resolved.len() >= 2, "two resolved direct calls to $h");
    }

    #[test]
    fn call_to_import_resolves_to_external() {
        let g = graph_for(
            "(module (import \"env\" \"log\" (func $log (param i32)))\n  (func $f (call $log)))\n",
        );
        let e = call_edges(&g)
            .into_iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("$log")))
            .expect("call to $log");
        assert_eq!(e.to, "ext::env.log");
        assert_eq!(e.props.get("external"), Some(&Json::Bool(true)));
    }

    #[test]
    fn numeric_and_indirect_calls_are_unresolved() {
        let g = graph_for("(module (func $f (call 3))\n  (func $g (call_indirect (type $t))))\n");
        assert!(
            g.has_node("unresolved::func[3]"),
            "numeric index unresolved"
        );
        assert!(
            g.has_node("unresolved::call_indirect"),
            "indirect call unresolved"
        );
        assert!(call_edges(&g)
            .iter()
            .any(|e| e.props.get("indirect") == Some(&Json::Bool(true))));
    }

    #[test]
    fn output_is_deterministic() {
        let src = "(module $m (import \"env\" \"log\" (func $log))\n  (func $a (call $b))\n  (func $b (call $log)))\n";
        let x = graph_for(src).to_jsonl();
        let y = graph_for(src).to_jsonl();
        assert_eq!(x, y, "graph output must be byte-identical across runs");
    }
}
