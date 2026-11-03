//! Lower the coarse assembly CST into the canonical graph.
//!
//! Assembly has no type system, no scopes beyond the file, and no portable notion
//! of "definition" other than a **label**. The mapping is therefore deliberately
//! coarse and honest about how much it punts:
//!
//!   - A label definition `name:` (and NASM-local `.name:`) → [`Function`]. A code
//!     label is the closest thing assembly has to a defined, callable symbol: it
//!     is a branch/call entry point. Data labels (`msg: db 0`) also become
//!     `Function` under this one rule — coarse, but lossless and documented.
//!   - `.global` / `.globl` / `global` / `public` NAME → the matching label
//!     `Function` is flagged `exported: true` (collected project-wide first).
//!   - `.extern` / `extern` NAME → [`ExternalDependency`] (`ext::NAME`) +
//!     [`IMPORTS`] (file→ext) + [`DEPENDS_ON`] (package→ext); the name is also
//!     remembered so a later `call NAME` resolves to that external symbol.
//!   - `.include` / `%include` / `#include "file"` → [`ExternalDependency`] for
//!     the included file + [`IMPORTS`] + [`DEPENDS_ON`].
//!   - `equ` / `.equ` / `.set` / `=` / `%define` / `#define` NAME → [`Constant`].
//!   - A branch/call instruction (`call`, `jmp`, `bl`, `b`, `je`, `jal`, …) whose
//!     operand is a bare label name → [`CALLS`] to that symbol. The caller is the
//!     most recent preceding label `Function` (labels delimit code regions in
//!     assembly), or the file when no label has appeared yet. Targets resolve to a
//!     known label when unique, to a declared `extern` external dependency, and
//!     otherwise to an explicit [`UnresolvedSymbol`] — never fabricated.
//!
//! ## Heavy punts (coarse by design)
//!   - **Section/segment directives** (`.text`, `.data`, `section`, `segment`),
//!     data directives (`db`/`dd`/…), alignment, and ordinary instructions emit
//!     no graph node of their own — they remain in the lossless CST only.
//!   - **No register model.** A branch through a register (`call rax`,
//!     `call [rax]`) is either skipped (bracketed/indirect, `%`-prefixed AT&T) or,
//!     for a bare Intel register operand, emitted as an unresolved `CALLS` — coarse
//!     noise we accept rather than maintain a per-dialect register table.
//!   - **Relocation suffixes** (`printf@PLT`) are stripped to the base symbol for
//!     resolution. Macros, conditional assembly, and expression evaluation are not
//!     modeled.
//!
//! Everything comes from real tokens on the lossless tree; nothing is guessed.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::asm::lexer::kind as tk;
use crate::lang::asm::parser::node as cst;
use crate::lang::frontend::SourceFile;

/// Lower a whole project's worth of assembly files into a graph. `manifest_deps`
/// is unused (assembly has no manifest the pipeline reads); dependencies are
/// discovered from `extern`/`include` directives instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        label_by_name: BTreeMap::new(),
        exported_names: BTreeSet::new(),
        extern_names: BTreeSet::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("asm"))],
    );

    // Pass A: structure (modules + file nodes), and project-wide collection of
    // exported / extern names plus emission of import edges. Done for all files
    // first so a `.global` in any file is visible before any label is emitted.
    for f in files {
        let leaf = lo.ensure_modules(&f.module_path);
        let file_id = format!("file::{}", f.rel_path);
        lo.g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("asm")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(leaf, edge::CONTAINS, file_id.clone(), vec![]);

        for item in f.root.child_nodes() {
            if item.kind == cst::DIRECTIVE {
                match classify_directive(item, f.source) {
                    Dir::Export(names) => {
                        for n in names {
                            lo.exported_names.insert(n);
                        }
                    }
                    Dir::Extern(names) => {
                        for n in names {
                            lo.extern_names.insert(n.clone());
                            lo.emit_extern(&file_id, &n);
                        }
                    }
                    Dir::Include(path) => {
                        if let Some(p) = path {
                            lo.emit_include(&file_id, &p);
                        }
                    }
                    Dir::Define(_) | Dir::Other => {}
                }
            }
        }
    }

    // Pass B: emit label Functions + Constants, build the label table, and record
    // call sites attributed to the enclosing label (or file).
    let mut pending: Vec<PendingCall> = Vec::new();
    for f in files {
        let li = LineIndex::new(f.source);
        let module_join = mod_join(&f.module_path);
        let file_id = format!("file::{}", f.rel_path);
        let mut current_owner = file_id.clone();

        for item in f.root.child_nodes() {
            match item.kind {
                cst::LABEL => {
                    if let Some((name, start)) = label_name(item, f.source) {
                        let line = li.line_col(start).line;
                        let qual = qual_name(&module_join, &name);
                        let id = format!("fn::{qual}#{line}");
                        let local = name.starts_with('.');
                        let exported = lo.exported_names.contains(&name);
                        lo.g.upsert_node(
                            id.clone(),
                            ont::FUNCTION,
                            name.clone(),
                            vec![
                                ("symbol_kind", Json::str("label")),
                                ("qualified_name", Json::str(qual)),
                                ("language", Json::str("asm")),
                                ("line", Json::U64(line as u64)),
                                ("local", Json::Bool(local)),
                                ("exported", Json::Bool(exported)),
                                ("span_start", Json::U64(item.span.start as u64)),
                                ("span_end", Json::U64(item.span.end as u64)),
                            ],
                        );
                        lo.g.add_edge(file_id.as_str(), edge::DECLARES, id.clone(), vec![]);
                        lo.label_by_name.entry(name).or_default().push(id.clone());
                        current_owner = id;
                    }
                }
                cst::DIRECTIVE => {
                    if let Dir::Define(name) = classify_directive(item, f.source) {
                        let line = li.line_col(item.span.start).line;
                        let qual = qual_name(&module_join, &name);
                        let id = format!("const::{qual}");
                        lo.g.upsert_node(
                            id.clone(),
                            ont::CONSTANT,
                            name,
                            vec![
                                ("binding", Json::str("equ")),
                                ("language", Json::str("asm")),
                                ("line", Json::U64(line as u64)),
                            ],
                        );
                        lo.g.add_edge(file_id.as_str(), edge::DECLARES, id, vec![]);
                    }
                }
                cst::INSTRUCTION => {
                    if let Some(target) = call_target(item, f.source) {
                        pending.push(PendingCall {
                            caller: current_owner.clone(),
                            target,
                        });
                    }
                }
                _ => {}
            }
        }
    }

    // Pass C: resolve and emit call edges against the complete tables.
    for call in &pending {
        lo.emit_call(&call.caller, &call.target);
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    /// Simple label name → defining `Function` node ids (call targets).
    label_by_name: BTreeMap<String, Vec<String>>,
    /// Names declared exported via `.global`/`.globl`/`global`/`public`.
    exported_names: BTreeSet<String>,
    /// Names declared external via `.extern`/`extern`.
    extern_names: BTreeSet<String>,
}

struct PendingCall {
    caller: String,
    target: String,
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
                vec![("language", Json::str("asm"))],
            );
            self.g.add_edge(parent, edge::CONTAINS, id.clone(), vec![]);
            parent = id;
        }
        parent
    }

    fn emit_extern(&mut self, file_id: &str, name: &str) {
        let dep_id = format!("ext::{name}");
        self.g.upsert_node(
            dep_id.clone(),
            ont::EXTERNAL_DEPENDENCY,
            name.to_string(),
            vec![
                ("external", Json::Bool(true)),
                ("source", Json::str("extern")),
            ],
        );
        self.g.add_edge(
            file_id,
            edge::IMPORTS,
            dep_id.clone(),
            vec![("external", Json::Bool(true))],
        );
        self.g
            .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
    }

    fn emit_include(&mut self, file_id: &str, path: &str) {
        let base = path.rsplit('/').next().unwrap_or(path).to_string();
        let dep_id = format!("ext::{base}");
        self.g.upsert_node(
            dep_id.clone(),
            ont::EXTERNAL_DEPENDENCY,
            base,
            vec![
                ("external", Json::Bool(true)),
                ("source", Json::str("include")),
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

    fn emit_call(&mut self, caller_id: &str, target: &str) {
        // A declared-external target resolves to its ExternalDependency node.
        if self.extern_names.contains(target) {
            let dep = format!("ext::{target}");
            self.g.add_edge(
                caller_id,
                edge::CALLS,
                dep,
                vec![
                    ("callee", Json::str(target.to_string())),
                    ("resolution", Json::str("external")),
                    ("resolved", Json::Bool(true)),
                ],
            );
            return;
        }
        let cands = self.label_by_name.get(target).cloned().unwrap_or_default();
        let mut props = vec![("callee", Json::str(target.to_string()))];
        match cands.len() {
            1 => {
                props.push(("resolution", Json::str("local")));
                props.push(("resolved", Json::Bool(true)));
                props.push(("candidate_count", Json::U64(1)));
                self.g
                    .add_edge(caller_id, edge::CALLS, cands[0].clone(), props);
            }
            0 => {
                let unresolved = format!("unresolved::{target}");
                self.ensure_unresolved(&unresolved, target);
                props.push(("resolution", Json::str("external")));
                props.push(("resolved", Json::Bool(false)));
                props.push(("candidate_count", Json::U64(0)));
                self.g.add_edge(caller_id, edge::CALLS, unresolved, props);
            }
            n => {
                let unresolved = format!("unresolved::{target}");
                self.ensure_unresolved(&unresolved, target);
                props.push(("resolution", Json::str("ambiguous")));
                props.push(("resolved", Json::Bool(false)));
                props.push(("ambiguous", Json::Bool(true)));
                props.push(("candidate_count", Json::U64(n as u64)));
                props.push((
                    "candidates",
                    Json::Array(cands.into_iter().map(Json::Str).collect()),
                ));
                self.g.add_edge(caller_id, edge::CALLS, unresolved, props);
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

// --- directive classification -----------------------------------------------

enum Dir {
    Export(Vec<String>),
    Extern(Vec<String>),
    Include(Option<String>),
    Define(String),
    Other,
}

/// Top-level significant tokens of a node as `(text, kind)` pairs (group nodes
/// are skipped — directive arguments are flat in every dialect we handle).
fn sig_texts<'a>(node: &'a Node, src: &'a str) -> Vec<(&'a str, &'static str)> {
    let mut v = Vec::new();
    for c in &node.children {
        match c {
            Child::Token(t) if t.trivia => {}
            Child::Token(t) => v.push((t.span.text(src), t.kind)),
            Child::Node(_) => {}
        }
    }
    v
}

fn is_equ_word(t: &str) -> bool {
    t.eq_ignore_ascii_case("equ") || t == "=" || t.eq_ignore_ascii_case("textequ")
}

fn classify_directive(node: &Node, src: &str) -> Dir {
    let toks = sig_texts(node, src);
    if toks.is_empty() {
        return Dir::Other;
    }
    // Named-definition form: `NAME equ ...` / `NAME = ...`.
    if toks.len() >= 2 && toks[0].1 == tk::IDENT && is_equ_word(toks[1].0) {
        return Dir::Define(toks[0].0.to_string());
    }
    // Determine the directive keyword and where its arguments begin.
    let (kw, argstart) = if toks[0].0 == "#" {
        (toks.get(1).map(|t| t.0).unwrap_or(""), 2)
    } else {
        (toks[0].0, 1)
    };
    let bare = kw.trim_start_matches(['.', '%', '#']).to_ascii_lowercase();
    let args = &toks[argstart.min(toks.len())..];
    match bare.as_str() {
        "global" | "globl" | "public" => Dir::Export(idents(args)),
        "extern" | "extrn" => Dir::Extern(idents(args)),
        "include" => Dir::Include(path_arg(args)),
        "equ" | "set" | "define" => match idents(args).into_iter().next() {
            Some(n) => Dir::Define(n),
            None => Dir::Other,
        },
        _ => Dir::Other,
    }
}

/// Identifier-kind argument texts (separators like `,` are dropped).
fn idents(args: &[(&str, &'static str)]) -> Vec<String> {
    args.iter()
        .filter(|(_, k)| *k == tk::IDENT)
        .map(|(t, _)| (*t).to_string())
        .collect()
}

/// The path argument of an `include`: the first string literal (quotes stripped),
/// else the first identifier (MASM `include file.inc` form).
fn path_arg(args: &[(&str, &'static str)]) -> Option<String> {
    if let Some((s, _)) = args.iter().find(|(_, k)| *k == tk::STRING) {
        return Some(strip_quotes(s));
    }
    args.iter()
        .find(|(_, k)| *k == tk::IDENT)
        .map(|(t, _)| (*t).to_string())
}

// --- call-site detection ----------------------------------------------------

/// The branch/call target of an instruction, if its mnemonic is a recognized
/// control-transfer op and its operand is a bare label name. Returns `None` for
/// non-branch instructions, register/indirect targets, and bracketed operands.
fn call_target(instr: &Node, src: &str) -> Option<String> {
    let toks = sig_texts(instr, src);
    let (mnem, mkind) = *toks.first()?;
    if mkind != tk::IDENT || !is_branch(&mnem.to_ascii_lowercase()) {
        return None;
    }
    for (text, kind) in &toks[1..] {
        if *kind == tk::IDENT {
            if text.starts_with('%') {
                return None; // AT&T register / indirect target — not a label
            }
            // Skip operand size / pointer / addressing qualifiers so the real
            // target is found (`call near foo`, `jmp short .l`, `call rel printf`).
            if is_operand_qualifier(&text.to_ascii_lowercase()) {
                continue;
            }
            let base = text.split('@').next().unwrap_or(text); // strip @PLT/@GOT
            if base.is_empty() {
                return None;
            }
            return Some(base.to_string());
        }
    }
    None
}

/// Operand prefix keywords that decorate a branch target without being it.
fn is_operand_qualifier(t: &str) -> bool {
    matches!(
        t,
        "byte"
            | "word"
            | "dword"
            | "qword"
            | "tbyte"
            | "ptr"
            | "near"
            | "far"
            | "short"
            | "offset"
            | "rel"
            | "strict"
    )
}

/// Recognized branch/call mnemonics across x86, ARM/ARM64, RISC-V, and MIPS.
/// Coarse and curated — an unlisted branch mnemonic simply yields no `CALLS`
/// edge. ARM64 conditional branches (`b.eq`, `b.ne`, …) are caught by prefix.
fn is_branch(m: &str) -> bool {
    if let Some(rest) = m.strip_prefix("b.") {
        return !rest.is_empty(); // b.eq, b.ne, b.lt, …
    }
    matches!(
        m,
        // x86 call / unconditional / conditional jumps + loops
        "call" | "callq" | "calll" | "jmp" | "jmpq" | "jmpf"
            | "je" | "jne" | "jz" | "jnz" | "jg" | "jng" | "jge" | "jnge"
            | "jl" | "jnl" | "jle" | "jnle" | "ja" | "jna" | "jae" | "jnae"
            | "jb" | "jnb" | "jbe" | "jnbe" | "jc" | "jnc" | "jo" | "jno"
            | "js" | "jns" | "jp" | "jpe" | "jnp" | "jpo"
            | "jcxz" | "jecxz" | "jrcxz" | "loop" | "loope" | "loopne"
            | "loopz" | "loopnz"
            // ARM / Thumb
            | "b" | "bl" | "blx" | "bx" | "bxj" | "blr" | "br"
            | "beq" | "bne" | "bgt" | "blt" | "bge" | "ble" | "bhi" | "bls"
            | "bcs" | "bcc" | "bmi" | "bpl" | "bvs" | "bvc" | "bal"
            | "cbz" | "cbnz" | "tbz" | "tbnz"
            // RISC-V / MIPS
            | "j" | "jal" | "jalr" | "tail" | "bltu" | "bgeu" | "blez"
            | "bgtz" | "bltz" | "bgez" | "bnez" | "beqz"
    )
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

/// The name and name-token byte offset of a `Label` item (`name:`).
fn label_name(item: &Node, src: &str) -> Option<(String, u32)> {
    let nm = item.child(cst::NAME)?;
    let t = nm.tokens().next()?;
    Some((t.span.text(src).to_string(), t.span.start))
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

fn strip_quotes(text: &str) -> String {
    let t = text.trim();
    if t.len() >= 2
        && ((t.starts_with('"') && t.ends_with('"')) || (t.starts_with('\'') && t.ends_with('\'')))
    {
        t[1..t.len() - 1].to_string()
    } else {
        t.to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::asm::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("prog.s", src);
        let file = SourceFile {
            rel_path: "prog.s".to_string(),
            module_path: vec!["prog".to_string()],
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    fn call_edges(g: &Graph) -> Vec<&crate::graph::GraphEdge> {
        g.edges().filter(|e| e.kind == edge::CALLS).collect()
    }

    #[test]
    fn label_becomes_function() {
        let g = graph_for("_start:\n  ret\n");
        let f = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "_start")
            .expect("a Function for the label");
        assert_eq!(f.props.get("symbol_kind"), Some(&Json::str("label")));
        assert!(g.edges().any(|e| e.kind == edge::DECLARES && e.to == f.id));
    }

    #[test]
    fn global_marks_export() {
        let g = graph_for("global _start\n_start:\n  ret\n");
        let f = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION && n.name == "_start")
            .expect("the label");
        assert_eq!(f.props.get("exported"), Some(&Json::Bool(true)));
    }

    #[test]
    fn extern_and_include_create_dependencies() {
        let g = graph_for("extern printf\n%include \"defs.inc\"\n");
        assert!(g.has_node("ext::printf"), "extern -> ExternalDependency");
        assert!(g.has_node("ext::defs.inc"), "include -> ExternalDependency");
        assert!(g.edges().any(|e| e.kind == edge::IMPORTS));
        assert!(g.edges().any(|e| e.kind == edge::DEPENDS_ON));
    }

    #[test]
    fn call_resolves_to_local_label() {
        let g = graph_for("helper:\n  ret\nmain:\n  call helper\n");
        let c = call_edges(&g)
            .into_iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("helper")))
            .expect("a call to helper");
        assert_eq!(c.props.get("resolved"), Some(&Json::Bool(true)));
        assert!(c.to.starts_with("fn::"));
    }

    #[test]
    fn call_to_extern_resolves_external() {
        let g = graph_for("extern printf\nmain:\n  call printf@PLT\n");
        let c = call_edges(&g)
            .into_iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("printf")))
            .expect("a call to printf");
        assert_eq!(c.props.get("resolution"), Some(&Json::str("external")));
        assert_eq!(c.to, "ext::printf");
    }

    #[test]
    fn unknown_branch_target_is_unresolved() {
        let g = graph_for("main:\n  jmp nowhere\n");
        let c = call_edges(&g)
            .into_iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("nowhere")))
            .expect("a branch to nowhere");
        assert_eq!(c.props.get("resolved"), Some(&Json::Bool(false)));
        assert!(g.has_node("unresolved::nowhere"));
    }

    #[test]
    fn equ_is_constant() {
        let g = graph_for("WIDTH equ 8\n.set HEIGHT, 4\n");
        let names: Vec<&str> = g
            .nodes()
            .filter(|n| n.kind == ont::CONSTANT)
            .map(|n| n.name.as_str())
            .collect();
        assert!(names.contains(&"WIDTH"), "NAME equ -> Constant: {names:?}");
        assert!(names.contains(&"HEIGHT"), ".set -> Constant: {names:?}");
    }

    #[test]
    fn output_is_deterministic() {
        let src = "global main\nextern printf\nmain:\n  call printf\n  jmp .loop\n.loop:\n  ret\nN equ 3\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
