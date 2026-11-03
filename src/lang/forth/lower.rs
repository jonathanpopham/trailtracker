//! Lower the Forth CST into the canonical graph.
//!
//! Forth is a tiny-syntax stack language, so the mapping is deliberately coarse
//! and honest (see the IR Atlas design principle: map honestly, never force-fit):
//!
//!   - a colon definition `: name … ;` → `Function`;
//!   - a `CONSTANT` / `VARIABLE` / `VALUE` (and the `2`/`F` and `CREATE` cousins)
//!     defining word → `Constant` (a named binding);
//!   - `INCLUDE` / `REQUIRE file` and `s" file" INCLUDED/REQUIRED` → `IMPORTS`
//!     (to the project file when the path resolves, else an `ExternalDependency`
//!     + `DEPENDS_ON`);
//!   - a word reference inside a definition body → `CALLS`, resolved to a known
//!     project definition (case-insensitively, as Forth convention dictates) or
//!     an explicit `UnresolvedSymbol` for the kernel/library word it must be.
//!
//! No fabricated targets: a `CALLS` edge resolves to a concrete `Function` only
//! when the name yields exactly one definition; several become an ambiguous edge
//! carrying the full `candidates` set; an unknown word resolves to an explicit
//! `UnresolvedSymbol`. There is no LLM in the airgap to guess.
//!
//! Heavy, deliberate punts (lossless parsing is the primary guarantee; the graph
//! is best-effort):
//!   - Control-flow words (`if`/`then`/`begin`/…) and immediate syntax
//!     (`does>`, `[`, `]`, `recurse`) are not treated as calls.
//!   - Only top-level `CONSTANT`/`VARIABLE`/… and includes are recognized; those
//!     written inside a definition (defining-word factories) are not.
//!   - Stack effect comments, vocabularies/wordlists, and `'`/`[']` execution
//!     tokens are not modeled. Forth has no class/struct/interface constructs, so
//!     this front end emits **no** `Type`/`HAS_METHOD`/`IMPLEMENTS`/`EXTENDS`.

use std::collections::BTreeMap;

use crate::core::cst::Node;
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::forth::lexer::kind as tk;
use crate::lang::forth::parser::node as cst;
use crate::lang::frontend::SourceFile;

/// Lower a whole project's worth of Forth files into a graph. `manifest_deps` is
/// unused (Forth has no manifest concept); dependencies are discovered from
/// `INCLUDE`/`REQUIRE` and unresolved word references.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
        fn_by_name: BTreeMap::new(),
        file_id_by_rel: BTreeMap::new(),
        files_by_base: BTreeMap::new(),
    };

    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id.clone(),
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("forth"))],
    );

    // Pre-index files so includes can resolve to a concrete project file.
    for f in files {
        let id = file_id(&f.rel_path);
        let norm = f.rel_path.trim_start_matches("./").to_string();
        lo.file_id_by_rel.insert(norm, id.clone());
        lo.files_by_base
            .entry(file_name(&f.rel_path))
            .or_default()
            .push(id);
    }

    // Pass A: file nodes + every colon definition (so a call to a word defined
    // later in the project still resolves; Forth words are file-global once the
    // batch is in hand).
    for f in files {
        let li = LineIndex::new(f.source);
        let fid = file_id(&f.rel_path);
        lo.g.upsert_node(
            fid.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("forth")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        lo.g.add_edge(pkg_id.clone(), edge::CONTAINS, fid.clone(), vec![]);
        lo.collect_definitions(f.root, &fid, &f.rel_path, f.source, &li);
    }

    // Pass B: top-level constants/includes + call sites inside each definition,
    // resolved against the now-complete word table.
    for f in files {
        let li = LineIndex::new(f.source);
        let fid = file_id(&f.rel_path);
        lo.scan_top_level(f.root, &fid, &f.rel_path, f.source, &li);
        lo.scan_calls(f.root, &fid, &f.rel_path, f.source, &li);
    }

    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
    /// Lowercased word name → all function node ids defining it.
    fn_by_name: BTreeMap<String, Vec<String>>,
    /// Normalized rel-path → file node id (for include resolution).
    file_id_by_rel: BTreeMap<String, String>,
    /// File basename → file node ids (for include basename resolution).
    files_by_base: BTreeMap<String, Vec<String>>,
}

impl Lowerer {
    fn pkg_id(&self) -> String {
        format!("pkg::{}", self.package)
    }

    // --- pass A: definitions ------------------------------------------------

    fn collect_definitions(
        &mut self,
        root: &Node,
        file_id: &str,
        rel_path: &str,
        src: &str,
        li: &LineIndex,
    ) {
        for child in root.child_nodes() {
            if child.kind == cst::DEFINITION {
                self.declare_definition(child, file_id, rel_path, src, li);
            }
        }
    }

    fn declare_definition(
        &mut self,
        def: &Node,
        file_id: &str,
        rel_path: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let (name, name_start) = match name_of(def, src) {
            Some(n) => n,
            None => return, // anonymous (`: ;`) — nothing to declare
        };
        let line = li.line_col(name_start).line;
        let id = fn_id(rel_path, &name, line);
        self.g.upsert_node(
            id.clone(),
            ont::FUNCTION,
            name.clone(),
            vec![
                ("qualified_name", Json::str(name.clone())),
                ("language", Json::str("forth")),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(def.span.start as u64)),
                ("span_end", Json::U64(def.span.end as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id.clone(), vec![]);
        self.fn_by_name
            .entry(name.to_ascii_lowercase())
            .or_default()
            .push(id);
    }

    // --- pass B: top-level constants and includes ---------------------------

    /// Scan the file's *top-level* token stream (direct token children of the
    /// SourceFile — i.e. outside any definition) for defining words and includes.
    fn scan_top_level(
        &mut self,
        root: &Node,
        file_id: &str,
        rel_path: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let toks = direct_tokens(root, src);
        for i in 0..toks.len() {
            let lower = toks[i].text.to_ascii_lowercase();
            if is_defining_word(&lower) {
                // `<value> CONSTANT NAME` / `VARIABLE NAME` — name follows.
                if let Some(name_tok) = toks.get(i + 1) {
                    let line = li.line_col(name_tok.start).line;
                    self.emit_constant(name_tok.text, &lower, file_id, rel_path, line);
                }
            } else if lower == "include" || lower == "require" {
                // Path is the following word.
                if let Some(arg) = toks.get(i + 1) {
                    self.emit_include(file_id, arg.text);
                }
            } else if lower == "included" || lower == "required" {
                // Path is the preceding `s" …"` string.
                if i > 0 && toks[i - 1].kind == tk::STRING {
                    let path = string_content(toks[i - 1].text);
                    self.emit_include(file_id, &path);
                }
            }
        }
    }

    fn emit_constant(
        &mut self,
        name: &str,
        defining_word: &str,
        file_id: &str,
        rel_path: &str,
        line: u32,
    ) {
        let id = format!("const::{rel_path}:{name}");
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            name.to_string(),
            vec![
                ("binding", Json::str(defining_word.to_string())),
                ("language", Json::str("forth")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(file_id, edge::DECLARES, id, vec![]);
    }

    /// `INCLUDE`/`REQUIRE`/`s" …" INCLUDED`: an `IMPORTS` edge to the project file
    /// when the path resolves, else an `ExternalDependency` (+ `DEPENDS_ON`).
    fn emit_include(&mut self, file_id: &str, raw: &str) {
        let cleaned = raw.trim();
        let norm = cleaned.trim_start_matches("./");
        if !cleaned.is_empty() {
            if let Some(target) = self.file_id_by_rel.get(norm).cloned() {
                self.g.add_edge(
                    file_id,
                    edge::IMPORTS,
                    target,
                    vec![
                        ("path", Json::str(cleaned.to_string())),
                        ("external", Json::Bool(false)),
                    ],
                );
                return;
            }
            if let Some(ids) = self.files_by_base.get(&file_name(cleaned)) {
                if ids.len() == 1 {
                    let target = ids[0].clone();
                    self.g.add_edge(
                        file_id,
                        edge::IMPORTS,
                        target,
                        vec![
                            ("path", Json::str(cleaned.to_string())),
                            ("external", Json::Bool(false)),
                        ],
                    );
                    return;
                }
            }
        }
        let base = if cleaned.is_empty() {
            "include".to_string()
        } else {
            file_name(cleaned)
        };
        let dep_id = ext_id(&base);
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
                ("path", Json::str(raw.to_string())),
                ("external", Json::Bool(true)),
            ],
        );
        let pkg = self.pkg_id();
        self.g.add_edge(pkg, edge::DEPENDS_ON, dep_id, vec![]);
    }

    // --- pass B: call sites -------------------------------------------------

    /// For each colon definition, attribute every word reference in its body to a
    /// `CALLS` edge from the function.
    fn scan_calls(
        &mut self,
        root: &Node,
        _file_id: &str,
        rel_path: &str,
        src: &str,
        li: &LineIndex,
    ) {
        for def in root.children_of(cst::DEFINITION) {
            let (name, name_start) = match name_of(def, src) {
                Some(n) => n,
                None => continue,
            };
            let line = li.line_col(name_start).line;
            let caller = fn_id(rel_path, &name, line);
            let body = match def.child(cst::BODY) {
                Some(b) => b,
                None => continue,
            };
            let mut callees = Vec::new();
            collect_call_words(body, src, &mut callees);
            for callee in callees {
                self.emit_call(&caller, &callee);
            }
        }
    }

    /// Resolve a word to a project definition (case-insensitively) or an explicit
    /// unresolved node, then emit the `CALLS` edge.
    fn emit_call(&mut self, caller: &str, name: &str) {
        let key = name.to_ascii_lowercase();
        let candidates = self.fn_by_name.get(&key).cloned().unwrap_or_default();
        let mut props = vec![("callee", Json::str(name.to_string()))];
        match candidates.len() {
            1 => {
                props.push(("resolved", Json::Bool(true)));
                props.push(("resolution", Json::str("project")));
                props.push(("candidate_count", Json::U64(1)));
                self.g
                    .add_edge(caller, edge::CALLS, candidates[0].clone(), props);
            }
            0 => {
                let target = unresolved_id(&key);
                self.ensure_unresolved(&target, &key);
                props.push(("resolved", Json::Bool(false)));
                props.push(("resolution", Json::str("external")));
                props.push(("candidate_count", Json::U64(0)));
                self.g.add_edge(caller, edge::CALLS, target, props);
            }
            n => {
                let target = unresolved_id(&key);
                self.ensure_unresolved(&target, &key);
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

    fn ensure_unresolved(&mut self, id: &str, name: &str) {
        if !self.g.has_node(id) {
            self.g.upsert_node(
                id.to_string(),
                ont::UNRESOLVED,
                name.to_string(),
                vec![
                    ("unresolved", Json::Bool(true)),
                    ("role", Json::str("word")),
                ],
            );
        }
    }
}

// --- pure helpers -----------------------------------------------------------

/// A flat view of a non-trivia token (text + kind + byte span).
#[derive(Clone, Copy)]
struct TokInfo<'a> {
    text: &'a str,
    kind: &'static str,
    start: u32,
}

/// Direct, non-trivia child tokens of `node`, in source order. (Does not descend
/// into child nodes — used to read the file's top-level word stream.)
fn direct_tokens<'a>(node: &'a Node, src: &'a str) -> Vec<TokInfo<'a>> {
    node.tokens()
        .map(|t| TokInfo {
            text: t.span.text(src),
            kind: t.kind,
            start: t.span.start,
        })
        .collect()
}

/// Collect, in source order, every body word that counts as a call target:
/// `word`-kind tokens (numbers/strings/comments excluded) that are not
/// control-flow or immediate syntax. Descends recursively through `Control`
/// groups so nested call sites are not missed.
fn collect_call_words(node: &Node, src: &str, out: &mut Vec<String>) {
    for child in &node.children {
        match child {
            crate::core::cst::Child::Token(t) => {
                if !t.trivia && t.kind == tk::WORD {
                    let text = t.span.text(src);
                    if !is_syntax_word(&text.to_ascii_lowercase()) {
                        out.push(text.to_string());
                    }
                }
            }
            crate::core::cst::Child::Node(n) => collect_call_words(n, src, out),
        }
    }
}

/// Defining words whose *following* token names a `Constant`-like binding.
fn is_defining_word(lower: &str) -> bool {
    matches!(
        lower,
        "constant"
            | "2constant"
            | "fconstant"
            | "variable"
            | "2variable"
            | "fvariable"
            | "value"
            | "2value"
            | "fvalue"
            | "create"
    )
}

/// Control-flow and immediate-syntax words that are *not* calls.
fn is_syntax_word(lower: &str) -> bool {
    matches!(
        lower,
        "if" | "else"
            | "then"
            | "begin"
            | "while"
            | "repeat"
            | "until"
            | "again"
            | "do"
            | "?do"
            | "loop"
            | "+loop"
            | "leave"
            | "case"
            | "of"
            | "endof"
            | "endcase"
            | "aft"
            | "recurse"
            | "does>"
            | "["
            | "]"
    )
}

/// Name (original case) and its byte-start of a colon definition, if any.
fn name_of<'a>(def: &'a Node, src: &'a str) -> Option<(String, u32)> {
    let nm = def.child(cst::NAME)?;
    let t = nm.tokens().next()?;
    Some((t.span.text(src).to_string(), t.span.start))
}

/// Body of a `." …"` / `s" …"` string token: strip the opener, the leading
/// space, and the closing quote.
fn string_content(token_text: &str) -> String {
    let trimmed = token_text
        .strip_prefix("s\"")
        .or_else(|| token_text.strip_prefix("S\""))
        .or_else(|| token_text.strip_prefix(".\""))
        .unwrap_or(token_text);
    let inner = trimmed.strip_suffix('"').unwrap_or(trimmed);
    inner.trim().to_string()
}

fn fn_id(rel_path: &str, name: &str, line: u32) -> String {
    format!("fn::{rel_path}:{name}#{line}")
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::forth::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("prog.fth", src);
        let file = SourceFile {
            rel_path: "prog.fth".to_string(),
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
    fn emits_function_file_and_package_nodes() {
        let g = graph_for(": square dup * ;\n: cube dup square * ;\n");
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "square + cube");
        assert_eq!(g.count_nodes_of(ont::FILE), 1);
        assert_eq!(g.count_nodes_of(ont::PACKAGE), 1);
        // Forth has no class-like constructs.
        assert_eq!(g.count_nodes_of(ont::TYPE), 0);
    }

    #[test]
    fn function_has_forth_language_tag() {
        let g = graph_for(": square dup * ;\n");
        let f = g
            .nodes()
            .find(|n| n.kind == ont::FUNCTION)
            .expect("a function");
        assert_eq!(f.props.get("language"), Some(&Json::str("forth")));
    }

    #[test]
    fn resolves_call_to_project_word_case_insensitively() {
        // `cube` calls `SQUARE` though it was defined as `square`.
        let g = graph_for(": square dup * ;\n: cube dup SQUARE * ;\n");
        let calls = call_edges(&g);
        let to_square = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("SQUARE")))
            .expect("a call to SQUARE");
        assert!(to_square.to.starts_with("fn::prog.fth:square"));
        assert_eq!(to_square.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(
            to_square.props.get("resolution"),
            Some(&Json::str("project"))
        );
    }

    #[test]
    fn unknown_word_is_external() {
        let g = graph_for(": f notaword ;\n");
        let calls = call_edges(&g);
        let ext = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("notaword")))
            .expect("a call to notaword");
        assert_eq!(ext.props.get("resolution"), Some(&Json::str("external")));
        assert!(g.has_node("unresolved::notaword"));
    }

    #[test]
    fn control_words_are_not_calls() {
        let g = graph_for(": f dup 0 < if drop then ;\n");
        let callees: Vec<String> = call_edges(&g)
            .iter()
            .filter_map(|e| e.props.get("callee"))
            .filter_map(|j| match j {
                Json::Str(s) => Some(s.clone()),
                _ => None,
            })
            .collect();
        assert!(callees.contains(&"dup".to_string()));
        assert!(callees.contains(&"drop".to_string()));
        assert!(!callees.contains(&"if".to_string()), "if is syntax");
        assert!(!callees.contains(&"then".to_string()), "then is syntax");
    }

    #[test]
    fn constant_and_variable_are_constants() {
        let g = graph_for("42 CONSTANT ANSWER\nVARIABLE COUNTER\n");
        assert_eq!(g.count_nodes_of(ont::CONSTANT), 2);
        let names: std::collections::BTreeSet<&str> = g
            .nodes()
            .filter(|n| n.kind == ont::CONSTANT)
            .map(|n| n.name.as_str())
            .collect();
        assert!(names.contains("ANSWER"));
        assert!(names.contains("COUNTER"));
    }

    #[test]
    fn include_word_is_import_dependency() {
        let g = graph_for("include extra.fth\n");
        assert!(g.has_node("ext::extra.fth"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::IMPORTS && e.to == "ext::extra.fth"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::extra.fth"));
    }

    #[test]
    fn required_string_is_import() {
        let g = graph_for("s\" lib.fth\" required\n");
        assert!(g.has_node("ext::lib.fth"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::IMPORTS && e.to == "ext::lib.fth"));
    }

    #[test]
    fn output_is_deterministic() {
        let src = "42 constant answer\n: square dup * ;\n: cube dup square * ;\ninclude x.fth\n";
        let a = graph_for(src).to_jsonl();
        let b = graph_for(src).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
