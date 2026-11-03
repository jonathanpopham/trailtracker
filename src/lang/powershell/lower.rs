//! Lower the PowerShell CST into the canonical graph.
//!
//! This mirrors the Rust, C#, and Bash lowerings — same conservative principles,
//! same shared ontology — adapted to PowerShell's surface:
//!
//! 1. **No fabricated targets, ambiguity preserved.** A `CALLS` edge resolves to a
//!    concrete project function/method only when the name yields exactly one
//!    definition; several definitions become an ambiguous edge carrying the full
//!    `candidates` set; an unknown command (a cmdlet or external program) resolves
//!    to an explicit `UnresolvedSymbol`. There is no LLM in the airgap to guess.
//! 2. **Everything comes from real tokens.** Calls, assignments, base lists, and
//!    `using` / `Import-Module` imports are read off the lossless tree, never
//!    invented.
//!
//! Honest mappings (see the IR Atlas):
//!   - `function Name { … }` / `filter Name { … }` → `Function`;
//!   - `class Name { … }` → `Type` (`type_kind = "class"`); `enum` → `Type`
//!     (`type_kind = "enum"`);
//!   - a method inside a class → `Function` (+ `HAS_METHOD` from the type, with
//!     `is_method`/`receiver_type`; a same-named member is `is_constructor`);
//!   - `class C : B` → `EXTENDS` (base class) / `IMPLEMENTS` (interface, resolved
//!     as such or by the `IPascal` naming convention when external);
//!   - a top-level `$script:`/`$global:` (or plain script-scope) assignment, and a
//!     class property, → `Constant`;
//!   - `using module|namespace …` and `Import-Module …` → `IMPORTS` (+ an
//!     `ExternalDependency` and a `DEPENDS_ON`, since modules live outside the
//!     analyzed project);
//!   - a command/function call and a `recv.Method(...)` / `[T]::Method(...)` call
//!     → `CALLS`, resolved against the project's function/method tables.
//!
//! Coverage notes (honest): function and method *bodies* are captured as token
//! trees, so a `function` *nested inside another function's body* is not lifted to
//! its own `Function` node (top-level and class members are). Receiver types of
//! `$x.Method()` calls are not inferred, so a member call resolves by method name
//! only (unique → resolved, several → ambiguous, none → external).

use std::collections::BTreeMap;

use crate::core::cst::{Child, Node, Token};
use crate::core::json::Json;
use crate::core::span::{ByteSpan, LineIndex};
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::powershell::lexer::{is_keyword, kind as tk};
use crate::lang::powershell::parser::node as cst;

const LANG: &str = "powershell";

/// Lower a whole project's worth of PowerShell files into a graph. `manifest_deps`
/// is unused for PowerShell (there is no manifest concept); dependencies are
/// discovered from `using` / `Import-Module` imports and unresolved command
/// invocations instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        fn_by_name: BTreeMap::new(),
        method_by_name: BTreeMap::new(),
        type_by_name: BTreeMap::new(),
        type_kind_by_id: BTreeMap::new(),
        pend_extends: Vec::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id.clone(),
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("powershell"))],
    );

    // Pass A: file nodes + every definition (functions, classes, enums, methods,
    // properties), so a call to something defined later still resolves.
    for f in files {
        let li = LineIndex::new(f.source);
        let fid = file_id(&f.rel_path);
        lo.g.upsert_node(
            fid.clone(),
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
        lo.g.add_edge(pkg_id.clone(), edge::CONTAINS, fid.clone(), vec![]);
        lo.declare_file(f, &fid, &li);
    }

    // Resolve deferred base-type links now that every type is known.
    let pending: Vec<PendingExtends> = std::mem::take(&mut lo.pend_extends);
    for pe in &pending {
        lo.emit_extends(pe);
    }

    // Pass B: imports, top-level assignments (Constants), and call sites (CALLS)
    // resolved against the now-complete function/method tables.
    for f in files {
        let li = LineIndex::new(f.source);
        let fid = file_id(&f.rel_path);
        lo.analyze_file(f, &fid, &li);
    }

    lo.g
}

/// A deferred base-type link, resolved into `EXTENDS`/`IMPLEMENTS` in pass A's tail.
struct PendingExtends {
    type_id: String,
    base_name: String,
}

struct Lowerer {
    g: Graph,
    package: String,
    /// Simple function name → all free-function node ids.
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// Simple method name → all class-method node ids.
    method_by_name: BTreeMap<String, Vec<String>>,
    /// Simple type name → all type node ids.
    type_by_name: BTreeMap<String, Vec<String>>,
    /// Type node id → its `type_kind` (for interface-vs-class base resolution).
    type_kind_by_id: BTreeMap<String, &'static str>,
    pend_extends: Vec<PendingExtends>,
}

/// A detected call site over the lossless token tree.
struct Call {
    /// The called name (cmdlet/function, or the final member name).
    name: String,
    /// True for `recv.Method(...)` / `[T]::Method(...)` member calls.
    method: bool,
    /// Text of the first argument element, when it is a single token (used to
    /// resolve `Import-Module <name>`); `None` otherwise.
    arg: Option<String>,
}

impl Lowerer {
    fn pkg_id(&self) -> String {
        format!("pkg::{}", self.package)
    }

    // --- pass A: declarations ----------------------------------------------

    fn declare_file(&mut self, f: &SourceFile<'_>, file_id: &str, li: &LineIndex) {
        for item in f.root.child_nodes() {
            match item.kind {
                cst::FUNCTION => self.declare_function(item, file_id, &f.rel_path, f.source, li),
                cst::CLASS => self.declare_class(item, file_id, &f.rel_path, f.source, li),
                cst::ENUM => self.declare_enum(item, file_id, &f.rel_path, f.source, li),
                _ => {}
            }
        }
    }

    fn declare_function(
        &mut self,
        item: &Node,
        file_id: &str,
        rel: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let name = match name_text(item, src) {
            Some(n) => n.to_string(),
            None => return,
        };
        let line = li.line_col(name_span_start(item)).line;
        let id = fn_id(rel, &name, line);
        self.g.upsert_node(
            id.clone(),
            ont::FUNCTION,
            name.clone(),
            vec![
                ("qualified_name", Json::str(name.clone())),
                ("language", Json::str(LANG)),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
                ("has_body", Json::Bool(item.child(cst::BLOCK).is_some())),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.fn_by_name.entry(name).or_default().push(id);
    }

    fn declare_class(&mut self, item: &Node, file_id: &str, rel: &str, src: &str, li: &LineIndex) {
        let name = match name_text(item, src) {
            Some(n) => n.to_string(),
            None => return,
        };
        let line = li.line_col(name_span_start(item)).line;
        let id = type_id(rel, &name);
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str("class")),
                ("qualified_name", Json::str(name.clone())),
                ("language", Json::str(LANG)),
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
        self.type_kind_by_id.insert(id.clone(), "class");

        // Base list → deferred EXTENDS / IMPLEMENTS.
        if let Some(header) = item.child(cst::HEADER) {
            for base in base_names(header, src) {
                self.pend_extends.push(PendingExtends {
                    type_id: id.clone(),
                    base_name: base,
                });
            }
        }

        // Members.
        if let Some(block) = item.child(cst::ITEM_BLOCK) {
            for m in block.child_nodes() {
                match m.kind {
                    cst::METHOD => self.declare_method(m, &name, &id, file_id, rel, src, li),
                    cst::PROPERTY => self.declare_property(m, file_id, rel, src, li),
                    _ => {}
                }
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn declare_method(
        &mut self,
        item: &Node,
        class_name: &str,
        type_id: &str,
        file_id: &str,
        rel: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let name = member_name(item, src).unwrap_or_else(|| "<anonymous>".to_string());
        let line = li.line_col(item.span.start).line;
        let id = method_id(rel, class_name, &name, line);
        let mut props = vec![
            ("qualified_name", Json::str(format!("{class_name}.{name}"))),
            ("language", Json::str(LANG)),
            ("line", Json::U64(line as u64)),
            ("span_start", Json::U64(item.span.start as u64)),
            ("span_end", Json::U64(item.span.end as u64)),
            ("has_body", Json::Bool(item.child(cst::BLOCK).is_some())),
            ("is_method", Json::Bool(true)),
            ("receiver_type", Json::str(class_name.to_string())),
        ];
        if name.eq_ignore_ascii_case(class_name) {
            props.push(("is_constructor", Json::Bool(true)));
        }
        if member_has_modifier(item, src, "static") {
            props.push(("is_static", Json::Bool(true)));
        }
        self.g
            .upsert_node(id.clone(), ont::FUNCTION, name.clone(), props);
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.g
            .add_edge(type_id, edge::HAS_METHOD, id.clone(), vec![]);
        self.method_by_name.entry(name).or_default().push(id);
    }

    fn declare_property(
        &mut self,
        item: &Node,
        file_id: &str,
        rel: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let name = match property_name(item, src) {
            Some(n) => n,
            None => return,
        };
        let line = li.line_col(item.span.start).line;
        let id = const_id(rel, &format!("property:{name}"));
        let binding = if member_has_modifier(item, src, "static") {
            "static_property"
        } else {
            "property"
        };
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            name,
            vec![
                ("binding", Json::str(binding)),
                ("language", Json::str(LANG)),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
    }

    fn declare_enum(&mut self, item: &Node, file_id: &str, rel: &str, src: &str, li: &LineIndex) {
        let name = match name_text(item, src) {
            Some(n) => n.to_string(),
            None => return,
        };
        let line = li.line_col(name_span_start(item)).line;
        let id = type_id(rel, &name);
        self.g.upsert_node(
            id.clone(),
            ont::TYPE,
            name.clone(),
            vec![
                ("type_kind", Json::str("enum")),
                ("qualified_name", Json::str(name.clone())),
                ("language", Json::str(LANG)),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(item.span.start as u64)),
                ("span_end", Json::U64(item.span.end as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.type_by_name.entry(name).or_default().push(id.clone());
        self.type_kind_by_id.insert(id, "enum");
    }

    /// Resolve a deferred base-type link. An interface base (resolved as such, or
    /// matching the `IPascal` convention when external) becomes `IMPLEMENTS`; any
    /// other base becomes `EXTENDS`. The target is a unique project type when
    /// known, else an explicit `UnresolvedSymbol` (a framework/third-party base we
    /// cannot see in an airgap).
    fn emit_extends(&mut self, pe: &PendingExtends) {
        let (target, is_interface, heuristic) = match self.unique_type(&pe.base_name) {
            Some(id) => {
                let kind = self.type_kind_by_id.get(&id).copied().unwrap_or("class");
                (id, kind == "interface", false)
            }
            None => {
                let id = unresolved_id(&pe.base_name);
                self.ensure_unresolved(&id, &pe.base_name, "base_type");
                (id, looks_like_interface(&pe.base_name), true)
            }
        };
        let edge_kind = if is_interface {
            edge::IMPLEMENTS
        } else {
            edge::EXTENDS
        };
        let mut props = vec![("base_name", Json::str(pe.base_name.clone()))];
        if heuristic {
            props.push(("inference", Json::str("naming_convention")));
        }
        self.g
            .add_edge(pe.type_id.clone(), edge_kind, target, props);
    }

    // --- pass B: imports, assignments, calls -------------------------------

    fn analyze_file(&mut self, f: &SourceFile<'_>, file_id: &str, li: &LineIndex) {
        for item in f.root.child_nodes() {
            match item.kind {
                cst::FUNCTION => {
                    if let (Some(name), Some(block)) =
                        (name_text(item, f.source), item.child(cst::BLOCK))
                    {
                        let line = li.line_col(name_span_start(item)).line;
                        let caller = fn_id(&f.rel_path, name, line);
                        self.scan_block(block, &caller, file_id, f.source);
                    }
                }
                cst::CLASS => {
                    let class_name = name_text(item, f.source).unwrap_or("").to_string();
                    if let Some(block) = item.child(cst::ITEM_BLOCK) {
                        for m in block.child_nodes() {
                            if m.kind == cst::METHOD {
                                if let Some(body) = m.child(cst::BLOCK) {
                                    let name = member_name(m, f.source)
                                        .unwrap_or_else(|| "<anonymous>".to_string());
                                    let line = li.line_col(m.span.start).line;
                                    let caller = method_id(&f.rel_path, &class_name, &name, line);
                                    self.scan_block(body, &caller, file_id, f.source);
                                }
                            }
                        }
                    }
                }
                cst::STATEMENT => self.process_statement(item, file_id, f.source, li),
                cst::USING => self.handle_using(item, file_id, f.source),
                _ => {}
            }
        }
    }

    /// Scan a function/method body (a token tree) for call sites and attribute
    /// them to `caller`.
    fn scan_block(&mut self, block: &Node, caller: &str, file_id: &str, src: &str) {
        let mut calls = Vec::new();
        scan_calls(block, src, true, &mut calls);
        for c in calls {
            self.emit_call_or_import(caller, file_id, c);
        }
    }

    /// A top-level statement: a leading `$name = …` assignment becomes a
    /// `Constant`, and every call inside is attributed to the file.
    fn process_statement(&mut self, stmt: &Node, file_id: &str, src: &str, li: &LineIndex) {
        if let Some(var) = leading_assignment(stmt, src) {
            let text = var.span.text(src);
            let name = var_name(text);
            if !name.is_empty() {
                let line = li.line_col(var.span.start).line;
                let id = const_id_path(file_id, &name);
                self.g.upsert_node(
                    id.clone(),
                    ont::CONSTANT,
                    name,
                    vec![
                        ("binding", Json::str(binding_of(text))),
                        ("language", Json::str(LANG)),
                        ("line", Json::U64(line as u64)),
                    ],
                );
                self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
            }
        }
        let mut calls = Vec::new();
        scan_calls(stmt, src, true, &mut calls);
        for c in calls {
            self.emit_call_or_import(file_id, file_id, c);
        }
    }

    fn emit_call_or_import(&mut self, caller: &str, file_id: &str, call: Call) {
        if !call.method && call.name.eq_ignore_ascii_case("import-module") {
            if let Some(arg) = &call.arg {
                self.emit_import(file_id, arg, "import-module", None);
            }
            return;
        }
        self.emit_call(caller, &call);
    }

    fn emit_call(&mut self, caller: &str, call: &Call) {
        let candidates = if call.method {
            self.method_by_name.get(&call.name).cloned()
        } else {
            self.fn_by_name.get(&call.name).cloned()
        }
        .unwrap_or_default();
        let role = if call.method { "method" } else { "command" };
        let mut props = vec![
            ("callee", Json::str(call.name.clone())),
            ("method", Json::Bool(call.method)),
        ];
        match candidates.len() {
            1 => {
                props.push(("resolved", Json::Bool(true)));
                props.push(("resolution", Json::str("project")));
                props.push(("candidate_count", Json::U64(1)));
                self.g
                    .add_edge(caller, edge::CALLS, candidates[0].clone(), props);
            }
            0 => {
                let target = unresolved_id(&call.name);
                self.ensure_unresolved(&target, &call.name, role);
                props.push(("resolved", Json::Bool(false)));
                props.push(("resolution", Json::str("external")));
                props.push(("candidate_count", Json::U64(0)));
                self.g.add_edge(caller, edge::CALLS, target, props);
            }
            n => {
                let target = unresolved_id(&call.name);
                self.ensure_unresolved(&target, &call.name, role);
                props.push(("resolved", Json::Bool(false)));
                props.push(("resolution", Json::str("ambiguous")));
                props.push(("ambiguous", Json::Bool(true)));
                props.push(("candidate_count", Json::U64(n as u64)));
                props.push((
                    "candidates",
                    Json::Array(candidates.into_iter().map(Json::Str).collect()),
                ));
                self.g.add_edge(caller, edge::CALLS, target, props);
            }
        }
    }

    /// `using module|namespace …` directive → an `IMPORTS` edge to an external
    /// module dependency.
    fn handle_using(&mut self, item: &Node, file_id: &str, src: &str) {
        let header = match item.child(cst::HEADER) {
            Some(h) => h,
            None => return,
        };
        // Direct significant tokens: `module`/`namespace`/`assembly` then the name.
        let toks: Vec<&Token> = header
            .children
            .iter()
            .filter_map(|c| match c {
                Child::Token(t) if !t.trivia => Some(t),
                _ => None,
            })
            .collect();
        if toks.is_empty() {
            return;
        }
        let (kind, name) = if toks.len() >= 2 {
            (toks[0].span.text(src), toks[1].span.text(src))
        } else {
            ("module", toks[0].span.text(src))
        };
        self.emit_import(file_id, name, "using", Some(kind));
    }

    /// Emit an `IMPORTS` edge to an `ExternalDependency` (modules live outside the
    /// analyzed project) plus a package-level `DEPENDS_ON`.
    fn emit_import(&mut self, file_id: &str, raw: &str, source: &str, kind: Option<&str>) {
        let cleaned = strip_quotes(raw);
        if cleaned.is_empty() {
            return;
        }
        let base = module_base(cleaned);
        let dep_id = ext_id(&base);
        self.g.upsert_node(
            dep_id.clone(),
            ont::EXTERNAL_DEPENDENCY,
            base,
            vec![
                ("external", Json::Bool(true)),
                ("source", Json::str(source.to_string())),
            ],
        );
        let mut props = vec![
            ("path", Json::str(cleaned.to_string())),
            ("external", Json::Bool(true)),
        ];
        if let Some(k) = kind {
            props.push(("using_kind", Json::str(k.to_string())));
        }
        self.g
            .add_edge(file_id, edge::IMPORTS, dep_id.clone(), props);
        let pkg = self.pkg_id();
        self.g.add_edge(pkg, edge::DEPENDS_ON, dep_id, vec![]);
    }

    fn ensure_unresolved(&mut self, id: &str, name: &str, role: &str) {
        if !self.g.has_node(id) {
            self.g.upsert_node(
                id.to_string(),
                ont::UNRESOLVED,
                name.to_string(),
                vec![
                    ("unresolved", Json::Bool(true)),
                    ("role", Json::str(role.to_string())),
                ],
            );
        }
    }

    fn unique_type(&self, name: &str) -> Option<String> {
        match self.type_by_name.get(name) {
            Some(ids) if ids.len() == 1 => Some(ids[0].clone()),
            _ => None,
        }
    }
}

// --- call detection over the lossless token tree ----------------------------

/// Command-position starter tokens: an identifier immediately after one of these
/// (or at the start of a script block) is in command position.
const STARTERS: &[&str] = &["|", "||", "&&", ";", "{", "(", "&", "="];

enum El<'a> {
    Tok {
        text: &'a str,
        kind: &'static str,
        span: ByteSpan,
    },
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
                span: t.span,
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

fn el_is_ident(e: &El) -> bool {
    matches!(e, El::Tok { kind, .. } if *kind == tk::IDENT)
}

fn el_span(e: &El) -> ByteSpan {
    match e {
        El::Tok { span, .. } => *span,
        El::Grp(n) => n.span,
    }
}

/// True if a token text is a pipeline / statement separator that ends an argument.
fn is_separator(text: &str) -> bool {
    matches!(text, "|" | "||" | "&&" | ";")
}

/// Capture the first whitespace-delimited "word" starting at element `from`, by
/// joining elements whose spans are byte-contiguous (so a path like
/// `./tools/Build.psm1`, lexed as many tokens, is reassembled). Stops at a
/// whitespace gap, a newline, a separator, or end.
fn capture_word(els: &[El], from: usize, src: &str) -> Option<String> {
    let first = els.get(from)?;
    let start = el_span(first).start;
    let mut end = el_span(first).end;
    let mut k = from;
    while let Some(next) = els.get(k + 1) {
        let cont = match next {
            El::Tok { kind, .. } if *kind == tk::NEWLINE => false,
            El::Tok { .. } => {
                let t = el_tok_text(next).unwrap_or("");
                !is_separator(t) && el_span(next).start == end
            }
            El::Grp(_) => false,
        };
        if !cont {
            break;
        }
        end = el_span(next).end;
        k += 1;
    }
    src.get(start as usize..end as usize).map(|s| s.to_string())
}

fn el_paren<'a>(e: &El<'a>) -> Option<&'a Node> {
    match e {
        El::Grp(n) if n.kind == cst::PAREN => Some(n),
        _ => None,
    }
}

/// Detect call sites over the real token tree:
///   - `recv . Method ( … )` and `[T] :: Method ( … )` → member calls;
///   - an identifier in command position (cmdlet / function invocation) → a call.
///
/// Recurses into `( )`, `{ }`/`Block`, and `Signature` groups (where commands can
/// appear); a `[ ]` group's leading element is never treated as command position.
fn scan_calls(node: &Node, src: &str, allow_start: bool, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        // Member / static call: `.`/`::` ident `(...)`.
        if matches!(el_tok_text(&els[i]), Some(".") | Some("::")) {
            if i + 2 < n && el_is_ident(&els[i + 1]) && el_paren(&els[i + 2]).is_some() {
                out.push(Call {
                    name: el_tok_text(&els[i + 1]).unwrap_or("").to_string(),
                    method: true,
                    arg: None,
                });
                i += 3;
                continue;
            }
            i += 1;
            continue;
        }
        // Command / function call: an identifier in command position.
        if el_is_ident(&els[i]) {
            let text = el_tok_text(&els[i]).unwrap_or("");
            let cmd_pos = match i.checked_sub(1).map(|p| &els[p]) {
                None => allow_start,
                Some(El::Tok { text, kind, .. }) => STARTERS.contains(text) || *kind == tk::NEWLINE,
                Some(El::Grp(_)) => false,
            };
            let next_is_eq = els.get(i + 1).and_then(el_tok_text) == Some("=");
            if cmd_pos && !next_is_eq && !is_keyword(text) {
                let arg = capture_word(&els, i + 1, src);
                out.push(Call {
                    name: text.to_string(),
                    method: false,
                    arg,
                });
            }
            i += 1;
            continue;
        }
        i += 1;
    }
    for e in &els {
        if let El::Grp(g) = e {
            let allow = g.kind == cst::BRACE
                || g.kind == cst::BLOCK
                || g.kind == cst::PAREN
                || g.kind == cst::SIGNATURE;
            scan_calls(g, src, allow, out);
        }
    }
}

// --- pure helpers -----------------------------------------------------------

/// The leading `$var` of a `$var = …` assignment statement (the next significant
/// child must be a literal `=`), or `None`.
fn leading_assignment<'a>(stmt: &'a Node, src: &'a str) -> Option<&'a Token> {
    let mut sig = stmt.children.iter().filter(|c| !is_trivia_child(c));
    let first = sig.next()?;
    let var = match first {
        Child::Token(t) if t.kind == tk::VARIABLE => t,
        _ => return None,
    };
    match sig.next()? {
        Child::Token(t) if t.span.text(src) == "=" => Some(var),
        _ => None,
    }
}

fn is_trivia_child(c: &Child) -> bool {
    matches!(c, Child::Token(t) if t.trivia)
}

/// Bare name of a variable token: strips the leading `$`, any `${…}` braces, and a
/// recognized scope/drive qualifier (`$script:foo` → `foo`).
fn var_name(text: &str) -> String {
    let s = text.strip_prefix('$').unwrap_or(text);
    let s = if s.len() >= 2 && s.starts_with('{') && s.ends_with('}') {
        &s[1..s.len() - 1]
    } else {
        s
    };
    if let Some((scope, rest)) = s.split_once(':') {
        if is_scope(scope) {
            return rest.to_string();
        }
    }
    s.to_string()
}

/// Binding kind for a `$var = …` assignment, from its scope qualifier.
fn binding_of(text: &str) -> &'static str {
    let lower = text.to_ascii_lowercase();
    if lower.starts_with("$global:") {
        "global"
    } else if lower.starts_with("$script:") {
        "script"
    } else {
        "script_var"
    }
}

fn is_scope(s: &str) -> bool {
    matches!(
        s.to_ascii_lowercase().as_str(),
        "script" | "global" | "local" | "private" | "env" | "using" | "variable"
    )
}

/// Heuristic: a `.NET`-style interface name starts with `I` followed by an
/// upper-case letter (`IDisposable`, `IComparable`).
fn looks_like_interface(name: &str) -> bool {
    let mut chars = name.chars();
    matches!(chars.next(), Some('I')) && matches!(chars.next(), Some(c) if c.is_uppercase())
}

/// Comma-separated base-type names from a `class` header `: Base, IFace` (the
/// final identifier of each comma-separated segment, ignoring keywords).
fn base_names(header: &Node, src: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut seen_colon = false;
    let mut current: Option<String> = None;
    for c in &header.children {
        let t = match c {
            Child::Token(t) if !t.trivia => t,
            _ => continue,
        };
        let text = t.span.text(src);
        if !seen_colon {
            if text == ":" {
                seen_colon = true;
            }
            continue;
        }
        match text {
            ":" => {}
            "," => {
                if let Some(name) = current.take() {
                    out.push(name);
                }
            }
            "." => {} // dotted name: keep the most recent identifier segment
            _ if t.kind == tk::IDENT && !is_keyword(text) => current = Some(text.to_string()),
            _ => {}
        }
    }
    if let Some(name) = current.take() {
        out.push(name);
    }
    out
}

/// The method/constructor name: the last non-keyword identifier among the *direct*
/// tokens of the member header (return-type identifiers live inside `[ ]` groups
/// and are skipped).
fn member_name(item: &Node, src: &str) -> Option<String> {
    let header = item.child(cst::HEADER)?;
    let mut name = None;
    for c in &header.children {
        if let Child::Token(t) = c {
            if !t.trivia && t.kind == tk::IDENT {
                let text = t.span.text(src);
                if !is_keyword(text) {
                    name = Some(text.to_string());
                }
            }
        }
    }
    name
}

/// The property/field name: the last variable among the *direct* tokens of the
/// member header (`[int]$Count` → `Count`), falling back to the last identifier.
fn property_name(item: &Node, src: &str) -> Option<String> {
    let header = item.child(cst::HEADER)?;
    let mut var = None;
    let mut ident = None;
    for c in &header.children {
        if let Child::Token(t) = c {
            if t.trivia {
                continue;
            }
            let text = t.span.text(src);
            if t.kind == tk::VARIABLE {
                var = Some(var_name(text));
            } else if t.kind == tk::IDENT && !is_keyword(text) {
                ident = Some(text.to_string());
            }
        }
    }
    var.or(ident)
}

/// True if any *direct* identifier token of the member header equals `modifier`
/// (case-insensitively).
fn member_has_modifier(item: &Node, src: &str, modifier: &str) -> bool {
    item.child(cst::HEADER)
        .map(|h| {
            h.children.iter().any(|c| match c {
                Child::Token(t) if !t.trivia => t.span.text(src).eq_ignore_ascii_case(modifier),
                _ => false,
            })
        })
        .unwrap_or(false)
}

fn strip_quotes(s: &str) -> &str {
    let b = s.as_bytes();
    if b.len() >= 2 && (b[0] == b'\'' || b[0] == b'"') && b[b.len() - 1] == b[0] {
        &s[1..s.len() - 1]
    } else {
        s
    }
}

/// Module base name for an import target: the bare file name without a directory
/// or a `.psm1`/`.psd1`/`.dll` extension (so `./lib/Foo.psm1` → `Foo`).
fn module_base(s: &str) -> String {
    let base = s.rsplit(['/', '\\']).next().unwrap_or(s);
    match base.rsplit_once('.') {
        Some((stem, ext))
            if matches!(
                ext.to_ascii_lowercase().as_str(),
                "psm1" | "psd1" | "ps1" | "dll"
            ) =>
        {
            stem.to_string()
        }
        _ => base.to_string(),
    }
}

fn fn_id(rel: &str, name: &str, line: u32) -> String {
    format!("fn::{rel}:{name}#{line}")
}

fn method_id(rel: &str, class: &str, name: &str, line: u32) -> String {
    format!("fn::{rel}:{class}.{name}#{line}")
}

fn type_id(rel: &str, name: &str) -> String {
    format!("type::{rel}:{name}")
}

fn const_id(rel: &str, name: &str) -> String {
    format!("const::{rel}:{name}")
}

fn const_id_path(file_id: &str, name: &str) -> String {
    let rel = file_id.strip_prefix("file::").unwrap_or(file_id);
    format!("const::{rel}:{name}")
}

fn file_id(rel: &str) -> String {
    format!("file::{rel}")
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::powershell::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("script.ps1", src);
        let file = SourceFile {
            rel_path: "script.ps1".to_string(),
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
    fn emits_function_and_file_nodes() {
        let g = graph_for("function Get-Foo {\n  Write-Host hi\n}\nfilter Test-Bar {\n  $_\n}\n");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "Get-Foo + Test-Bar");
        assert_eq!(g.count_nodes_of(ont::FILE), 1);
        assert_eq!(g.count_nodes_of(ont::PACKAGE), 1);
    }

    #[test]
    fn function_node_has_powershell_language_tag() {
        let g = graph_for("function Get-Foo { 'hi' }\n");
        let f = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION)
            .expect("a function");
        assert_eq!(f.props.get("language"), Some(&Json::str("powershell")));
    }

    #[test]
    fn resolves_call_to_project_function() {
        let g = graph_for("function Greet { 'hi' }\nfunction Run {\n  Greet\n}\n");
        let calls = call_edges(&g);
        let to_greet = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("Greet")))
            .expect("a call to Greet");
        assert!(to_greet.to.starts_with("fn::script.ps1:Greet"));
        assert_eq!(to_greet.props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn unknown_cmdlet_is_external() {
        let g = graph_for("function Run {\n  Get-ChildItem\n}\n");
        let calls = call_edges(&g);
        let ext = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("Get-ChildItem")))
            .expect("a call to Get-ChildItem");
        assert_eq!(ext.props.get("resolution"), Some(&Json::str("external")));
        assert!(g.has_node("unresolved::Get-ChildItem"));
    }

    #[test]
    fn class_is_a_type_with_methods() {
        let g = graph_for(
            "class Animal {\n  [string]$Name\n  Animal() {}\n  [void] Speak() { Write-Host 'hi' }\n}\n",
        );
        assert_eq!(g.count_nodes_of(ont::TYPE), 1);
        let t = g.nodes().find(|n| n.kind == ont::TYPE).unwrap();
        assert_eq!(t.props.get("type_kind"), Some(&Json::str("class")));
        // Constructor + Speak are methods linked by HAS_METHOD.
        assert!(g.count_edges_of(edge::HAS_METHOD) >= 2);
        // The [string]$Name property is a Constant.
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::CONSTANT && n.name == "Name"));
    }

    #[test]
    fn enum_is_a_type() {
        let g = graph_for("enum Color { Red; Green; Blue }\n");
        let t = g.nodes().find(|n| n.kind == ont::TYPE).expect("a type");
        assert_eq!(t.props.get("type_kind"), Some(&Json::str("enum")));
    }

    #[test]
    fn base_class_emits_extends_and_interface_implements() {
        let g = graph_for("class Base {}\nclass Derived : Base, IComparable {}\n");
        assert!(
            g.edges().any(|e| e.kind == edge::EXTENDS),
            "Base should produce an EXTENDS edge"
        );
        let impl_edge = g
            .edges()
            .find(|e| e.kind == edge::IMPLEMENTS && e.to == "unresolved::IComparable")
            .expect("interface base by naming convention");
        assert_eq!(
            impl_edge.props.get("inference"),
            Some(&Json::str("naming_convention"))
        );
    }

    #[test]
    fn script_scope_assignment_is_constant() {
        let g = graph_for("$script:Config = 'prod'\n$global:Flag = $true\n$local = 1\n");
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 3);
        let cfg = g
            .nodes()
            .find(|n| n.kind == ont::CONSTANT && n.name == "Config")
            .expect("Config constant");
        assert_eq!(cfg.props.get("binding"), Some(&Json::str("script")));
    }

    #[test]
    fn using_and_import_module_emit_imports() {
        let g = graph_for("using module Pester\nImport-Module ./tools/Build.psm1\n");
        assert!(g.has_node("ext::Pester"));
        assert!(g.has_node("ext::Build"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::IMPORTS && e.to == "ext::Pester"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::Build"));
        // Import-Module is recorded as an import, not a CALLS edge.
        assert!(!call_edges(&g)
            .iter()
            .any(|e| e.props.get("callee") == Some(&Json::str("Import-Module"))));
    }

    #[test]
    fn pipeline_segments_each_yield_a_call() {
        let g = graph_for("function Run {\n  Get-Thing | Format-Table\n}\n");
        let callees: Vec<String> = call_edges(&g)
            .iter()
            .filter_map(|e| e.props.get("callee"))
            .filter_map(|j| match j {
                Json::Str(s) => Some(s.clone()),
                _ => None,
            })
            .collect();
        assert!(callees.contains(&"Get-Thing".to_string()));
        assert!(callees.contains(&"Format-Table".to_string()));
    }

    #[test]
    fn output_is_deterministic() {
        let src =
            "using module M\nclass C : B { M() { Helper } }\nfunction Helper {}\n$script:X = 1\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
