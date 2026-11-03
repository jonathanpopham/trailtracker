//! Lower the COBOL CST into the canonical graph.
//!
//! Same conservative principles as the other front ends, adapted to COBOL's
//! surface. The mapping is deliberately **coarse but honest** — COBOL's program
//! structure does not line up cleanly with the lambda-rooted ontology, so the
//! lowering states plainly what it does and does not model:
//!
//!   - `PROGRAM-ID. name` → [`Module`] (a `unit` = `program` property). One module
//!     per `PROGRAM-ID`; in a multi-program source the most recent program owns
//!     the paragraphs/data that follow it.
//!   - PROCEDURE DIVISION **paragraphs** and **sections** → [`Function`] — a
//!     paragraph is COBOL's callable unit (a `paragraph_kind` property records
//!     paragraph vs section). Procedure statements appearing before the first
//!     paragraph are attributed to a synthesised program-entry [`Function`]
//!     (`paragraph_kind` = `program`), flagged so it is never mistaken for a
//!     real named paragraph.
//!   - `PERFORM para` and `GO TO para` → [`CALLS`] resolved against the program's
//!     paragraph table (ambiguity preserved as a `candidates` set; unknown targets
//!     become an [`UnresolvedSymbol`]). Inline `PERFORM … UNTIL/VARYING/n TIMES`
//!     with no paragraph operand is a loop, not a call — none is emitted.
//!   - `CALL "prog"` → [`CALLS`] to an [`ExternalDependency`] (+ [`DEPENDS_ON`]);
//!     `CALL data-name` (dynamic) → [`CALLS`] to an [`UnresolvedSymbol`].
//!   - `COPY text` → [`IMPORTS`] to an [`ExternalDependency`] copybook
//!     (+ [`DEPENDS_ON`]).
//!   - `01`/`77`-level data items and `88` condition names → [`Constant`]
//!     (loosely — COBOL data items are storage, mapped to the value/binding kind;
//!     a `level`/`binding` property keeps it honest). Sub-fields (`05`, `10`, …)
//!     are not emitted as their own constants.
//!
//! What COBOL honestly has no clean home for here, and how it is handled:
//!   - **DML / verbs** (MOVE, COMPUTE, INSPECT, file I/O, EXEC SQL, …) carry no
//!     graph fact in this coarse model; they remain in the lossless CST as
//!     `Sentence` tokens but emit no node/edge.
//!   - **PIC clauses** are not interpreted; they round-trip as ordinary tokens.
//!   - **`SELECT … ASSIGN`** file definitions and the REPORT/SCREEN sections are
//!     not modelled.
//!
//! Everything comes from real tokens on the lossless tree; nothing is guessed.
//! COBOL is case-insensitive, so all name *keys* (symbol tables, ids) are
//! lowercased while the displayed `name` preserves the source spelling.

use std::collections::BTreeMap;

use crate::core::cst::{Child, Node};
use crate::core::json::Json;
use crate::core::span::LineIndex;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::cobol::lexer::{is_keyword, kind as tk};
use crate::lang::cobol::parser::node as cst;
use crate::lang::frontend::SourceFile;

/// Lower a whole project's worth of COBOL files into a graph. `manifest_deps`
/// is unused (the pipeline reads no COBOL manifest); dependencies are discovered
/// from `CALL`/`COPY` instead.
pub fn lower(package: &str, files: &[SourceFile<'_>], _manifest_deps: &[String]) -> Graph {
    let mut lo = Lowerer {
        g: Graph::new(),
        package: package.to_string(),
    };
    let pkg_id = lo.pkg_id();
    lo.g.upsert_node(
        pkg_id,
        ont::PACKAGE,
        package.to_string(),
        vec![("ecosystem", Json::str("cobol"))],
    );
    for f in files {
        lo.lower_file(f);
    }
    lo.g
}

struct Lowerer {
    g: Graph,
    package: String,
}

/// A detected call/transfer site.
struct Call {
    /// Simple name of the callee, lowercased for resolution.
    name: String,
    /// Original spelling for display.
    display: String,
    /// How the transfer was stated.
    via: &'static str, // "perform" | "goto" | "call" | "call-dynamic"
}

impl Lowerer {
    fn pkg_id(&self) -> String {
        format!("pkg::{}", self.package)
    }

    fn lower_file(&mut self, f: &SourceFile<'_>) {
        let li = LineIndex::new(f.source);
        let file_id = format!("file::{}", f.rel_path);
        self.g.upsert_node(
            file_id.clone(),
            ont::FILE,
            file_name(&f.rel_path),
            vec![
                ("path", Json::str(f.rel_path.clone())),
                ("language", Json::str("cobol")),
                ("extension", Json::str(extension(&f.rel_path))),
                ("bytes", Json::U64(f.source.len() as u64)),
                ("lines", Json::U64(line_count(f.source) as u64)),
            ],
        );
        self.g
            .add_edge(self.pkg_id(), edge::CONTAINS, file_id.clone(), vec![]);

        let sentences: Vec<&Node> = f.root.child_nodes().collect();

        // Walk state.
        let mut division = String::new();
        let mut progkey = file_stem(&f.rel_path);
        let mut container = file_id.clone();
        let mut current_fn: Option<String> = None;
        // name_lc → paragraph/section function ids (within the current program).
        let mut para_table: BTreeMap<String, Vec<String>> = BTreeMap::new();
        // (fn_id, sentence) pairs to scan for calls once the table is complete.
        let mut bodies: Vec<(String, &Node)> = Vec::new();

        for (i, &s) in sentences.iter().enumerate() {
            // COPY may appear in any division (it is most common in DATA).
            self.handle_copy(s, f.source, &file_id);

            if s.kind == cst::DIVISION {
                division = first_sig_word_lc(s, f.source);
                current_fn = None;
            } else if s.kind == cst::SECTION {
                if division == "procedure" {
                    if let Some(name) = first_name(s, f.source) {
                        let id = self.make_fn(&progkey, &name, s, &li, "section");
                        self.g
                            .add_edge(&container, edge::DECLARES, id.clone(), vec![]);
                        para_table
                            .entry(name.to_ascii_lowercase())
                            .or_default()
                            .push(id.clone());
                        current_fn = Some(id);
                    }
                }
            } else if s.kind == cst::PARAGRAPH
                || (s.kind == cst::DATA_ENTRY && division == "procedure")
            {
                // A paragraph head, or a numeric paragraph label inside the
                // procedure division (classified DATA_ENTRY by its leading int).
                if division == "procedure" {
                    if let Some(name) = first_name(s, f.source) {
                        let id = self.make_fn(&progkey, &name, s, &li, "paragraph");
                        self.g
                            .add_edge(&container, edge::DECLARES, id.clone(), vec![]);
                        para_table
                            .entry(name.to_ascii_lowercase())
                            .or_default()
                            .push(id.clone());
                        current_fn = Some(id);
                    }
                }
            } else if s.kind == cst::DATA_ENTRY {
                self.handle_data_entry(s, &container, &progkey, f.source, &li);
            } else if s.kind == cst::SENTENCE {
                let w0 = first_sig_word_lc(s, f.source);
                if w0 == "program-id" {
                    let name =
                        program_name(&sentences, i, f.source).unwrap_or_else(|| progkey.clone());
                    let name_lc = name.to_ascii_lowercase();
                    progkey = name_lc.clone();
                    let mod_id = format!("mod::{name_lc}");
                    self.g.upsert_node(
                        mod_id.clone(),
                        ont::MODULE,
                        name,
                        vec![
                            ("language", Json::str("cobol")),
                            ("unit", Json::str("program")),
                        ],
                    );
                    self.g
                        .add_edge(file_id.clone(), edge::CONTAINS, mod_id.clone(), vec![]);
                    container = mod_id;
                    current_fn = None;
                    para_table.clear();
                } else if division == "procedure" {
                    // An ordinary statement in the procedure division belongs to
                    // the current paragraph, or to a synthesised program entry if
                    // there is none yet.
                    let fn_id = match current_fn.clone() {
                        Some(id) => id,
                        None => {
                            let id = self.make_entry_fn(&progkey, s, &li);
                            self.g
                                .add_edge(&container, edge::DECLARES, id.clone(), vec![]);
                            current_fn = Some(id.clone());
                            id
                        }
                    };
                    bodies.push((fn_id, s));
                }
            }
        }

        // Resolve calls against the now-complete paragraph table.
        for (fn_id, node) in bodies {
            let mut calls = Vec::new();
            scan_calls(node, f.source, &mut calls);
            for call in &calls {
                self.emit_call(&fn_id, call, &para_table);
            }
        }
    }

    fn make_fn(
        &mut self,
        progkey: &str,
        name: &str,
        node: &Node,
        li: &LineIndex,
        paragraph_kind: &'static str,
    ) -> String {
        let name_lc = name.to_ascii_lowercase();
        let line = li.line_col(node.span.start).line;
        let qual = format!("{progkey}::{name_lc}");
        let id = format!("fn::{qual}#{line}");
        self.g.upsert_node(
            id.clone(),
            ont::FUNCTION,
            name.to_string(),
            vec![
                ("qualified_name", Json::str(qual)),
                ("language", Json::str("cobol")),
                ("paragraph_kind", Json::str(paragraph_kind)),
                ("line", Json::U64(line as u64)),
                ("span_start", Json::U64(node.span.start as u64)),
                ("span_end", Json::U64(node.span.end as u64)),
            ],
        );
        id
    }

    /// Synthesise the program-entry function for procedure-division statements
    /// that precede the first paragraph. Flagged `paragraph_kind = program` and
    /// `synthesized = true` so it is honest about not being a source paragraph.
    fn make_entry_fn(&mut self, progkey: &str, node: &Node, li: &LineIndex) -> String {
        let line = li.line_col(node.span.start).line;
        let id = format!("fn::{progkey}#{line}");
        self.g.upsert_node(
            id.clone(),
            ont::FUNCTION,
            progkey.to_string(),
            vec![
                ("qualified_name", Json::str(progkey.to_string())),
                ("language", Json::str("cobol")),
                ("paragraph_kind", Json::str("program")),
                ("synthesized", Json::Bool(true)),
                ("line", Json::U64(line as u64)),
            ],
        );
        id
    }

    fn handle_data_entry(
        &mut self,
        node: &Node,
        container: &str,
        progkey: &str,
        src: &str,
        li: &LineIndex,
    ) {
        let els = significant_children(node, src);
        let level: u32 = match els.first() {
            Some(El::Tok { text, kind }) if *kind == tk::INT => text.parse().unwrap_or(0),
            _ => return,
        };
        // Only top-level items + condition names map to constants.
        if !matches!(level, 1 | 77 | 88) {
            return;
        }
        let name = els.iter().skip(1).find_map(|e| match e {
            El::Tok { text, kind } if *kind == tk::IDENT => Some((*text).to_string()),
            _ => None,
        });
        let name = match name {
            Some(n) if !n.eq_ignore_ascii_case("filler") => n,
            _ => return,
        };
        let name_lc = name.to_ascii_lowercase();
        let line = li.line_col(node.span.start).line;
        let id = format!("const::{progkey}::{name_lc}");
        let binding = if level == 88 {
            "condition-name"
        } else {
            "data-item"
        };
        self.g.upsert_node(
            id.clone(),
            ont::CONSTANT,
            name,
            vec![
                ("binding", Json::str(binding)),
                ("level", Json::U64(level as u64)),
                ("language", Json::str("cobol")),
                ("line", Json::U64(line as u64)),
            ],
        );
        self.g.add_edge(container, edge::DECLARES, id, vec![]);
    }

    fn handle_copy(&mut self, node: &Node, src: &str, file_id: &str) {
        let els = significant_children(node, src);
        for k in 0..els.len() {
            if let El::Tok { text, .. } = &els[k] {
                if !text.eq_ignore_ascii_case("copy") {
                    continue;
                }
                let name = match els.get(k + 1) {
                    Some(El::Tok { text: t, kind }) if *kind == tk::STRING => strip_quotes(t),
                    Some(El::Tok { text: t, kind }) if *kind == tk::IDENT => (*t).to_string(),
                    _ => continue,
                };
                if name.is_empty() {
                    continue;
                }
                let name_lc = name.to_ascii_lowercase();
                let dep_id = format!("ext::copy::{name_lc}");
                self.g.upsert_node(
                    dep_id.clone(),
                    ont::EXTERNAL_DEPENDENCY,
                    name.clone(),
                    vec![
                        ("external", Json::Bool(true)),
                        ("source", Json::str("copy")),
                    ],
                );
                self.g.add_edge(
                    file_id,
                    edge::IMPORTS,
                    dep_id.clone(),
                    vec![("path", Json::str(name)), ("external", Json::Bool(true))],
                );
                self.g
                    .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id, vec![]);
            }
        }
    }

    fn emit_call(
        &mut self,
        caller_id: &str,
        call: &Call,
        para_table: &BTreeMap<String, Vec<String>>,
    ) {
        match call.via {
            "perform" | "goto" => {
                let cands = para_table.get(&call.name).cloned().unwrap_or_default();
                let mut props = vec![
                    ("callee", Json::str(call.display.clone())),
                    ("via", Json::str(call.via)),
                ];
                if cands.len() == 1 {
                    props.push(("resolved", Json::Bool(true)));
                    props.push(("resolution", Json::str("paragraph")));
                    props.push(("candidate_count", Json::U64(1)));
                    self.g
                        .add_edge(caller_id, edge::CALLS, cands[0].clone(), props);
                } else if cands.len() > 1 {
                    let target = unresolved_id(&call.name);
                    self.ensure_unresolved(&target, &call.display, "paragraph");
                    props.push(("resolved", Json::Bool(false)));
                    props.push(("ambiguous", Json::Bool(true)));
                    props.push(("candidate_count", Json::U64(cands.len() as u64)));
                    props.push((
                        "candidates",
                        Json::Array(cands.into_iter().map(Json::Str).collect()),
                    ));
                    self.g.add_edge(caller_id, edge::CALLS, target, props);
                } else {
                    let target = unresolved_id(&call.name);
                    self.ensure_unresolved(&target, &call.display, "paragraph");
                    props.push(("resolved", Json::Bool(false)));
                    props.push(("resolution", Json::str("unresolved")));
                    props.push(("candidate_count", Json::U64(0)));
                    self.g.add_edge(caller_id, edge::CALLS, target, props);
                }
            }
            "call" => {
                let dep_id = format!("ext::{}", call.name);
                self.g.upsert_node(
                    dep_id.clone(),
                    ont::EXTERNAL_DEPENDENCY,
                    call.display.clone(),
                    vec![
                        ("external", Json::Bool(true)),
                        ("source", Json::str("call")),
                    ],
                );
                self.g
                    .add_edge(self.pkg_id(), edge::DEPENDS_ON, dep_id.clone(), vec![]);
                self.g.add_edge(
                    caller_id,
                    edge::CALLS,
                    dep_id,
                    vec![
                        ("callee", Json::str(call.display.clone())),
                        ("via", Json::str("call")),
                        ("resolved", Json::Bool(false)),
                        ("external", Json::Bool(true)),
                        ("resolution", Json::str("external")),
                    ],
                );
            }
            _ => {
                // Dynamic CALL via a data name — target is a runtime value.
                let target = unresolved_id(&call.name);
                self.ensure_unresolved(&target, &call.display, "call");
                self.g.add_edge(
                    caller_id,
                    edge::CALLS,
                    target,
                    vec![
                        ("callee", Json::str(call.display.clone())),
                        ("via", Json::str("call")),
                        ("resolved", Json::Bool(false)),
                        ("dynamic", Json::Bool(true)),
                        ("resolution", Json::str("dynamic")),
                    ],
                );
            }
        }
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
}

// --- call scanning over the lossless token tree -----------------------------

/// Detect call/transfer sites over the real token tree: `CALL "prog"` /
/// `CALL data-name`, `PERFORM para [THRU para2]`, and `GO TO para` / `GOTO para`.
/// Recurses into balanced groups.
fn scan_calls(node: &Node, src: &str, out: &mut Vec<Call>) {
    let els = significant_children(node, src);
    let n = els.len();
    let mut i = 0;
    while i < n {
        if let El::Tok { text, .. } = &els[i] {
            match text.to_ascii_lowercase().as_str() {
                "call" => {
                    match els.get(i + 1) {
                        Some(El::Tok { text: t, kind }) if *kind == tk::STRING => {
                            let name = strip_quotes(t);
                            out.push(Call {
                                name: name.to_ascii_lowercase(),
                                display: name,
                                via: "call",
                            });
                        }
                        Some(El::Tok { text: t, kind }) if *kind == tk::IDENT && !is_keyword(t) => {
                            out.push(Call {
                                name: t.to_ascii_lowercase(),
                                display: (*t).to_string(),
                                via: "call-dynamic",
                            });
                        }
                        _ => {}
                    }
                    i += 2;
                    continue;
                }
                "perform" => {
                    if let Some(El::Tok { text: t, kind }) = els.get(i + 1) {
                        if *kind == tk::IDENT && !is_keyword(t) {
                            out.push(Call {
                                name: t.to_ascii_lowercase(),
                                display: (*t).to_string(),
                                via: "perform",
                            });
                            // `PERFORM a THRU b` — the range end is also a target.
                            if let Some(El::Tok { text: th, .. }) = els.get(i + 2) {
                                if th.eq_ignore_ascii_case("thru")
                                    || th.eq_ignore_ascii_case("through")
                                {
                                    if let Some(El::Tok { text: t2, kind: k2 }) = els.get(i + 3) {
                                        if *k2 == tk::IDENT && !is_keyword(t2) {
                                            out.push(Call {
                                                name: t2.to_ascii_lowercase(),
                                                display: (*t2).to_string(),
                                                via: "perform",
                                            });
                                        }
                                    }
                                }
                            }
                        }
                    }
                    i += 1;
                    continue;
                }
                "go" => {
                    if let Some(El::Tok { text: to_, .. }) = els.get(i + 1) {
                        if to_.eq_ignore_ascii_case("to") {
                            if let Some(El::Tok { text: t, kind }) = els.get(i + 2) {
                                if *kind == tk::IDENT && !is_keyword(t) {
                                    out.push(Call {
                                        name: t.to_ascii_lowercase(),
                                        display: (*t).to_string(),
                                        via: "goto",
                                    });
                                }
                            }
                        }
                    }
                    i += 1;
                    continue;
                }
                "goto" => {
                    if let Some(El::Tok { text: t, kind }) = els.get(i + 1) {
                        if *kind == tk::IDENT && !is_keyword(t) {
                            out.push(Call {
                                name: t.to_ascii_lowercase(),
                                display: (*t).to_string(),
                                via: "goto",
                            });
                        }
                    }
                    i += 1;
                    continue;
                }
                _ => {}
            }
        }
        i += 1;
    }
    for e in &els {
        if let El::Grp(g) = e {
            scan_calls(g, src, out);
        }
    }
}

// --- pure helpers -----------------------------------------------------------

fn unresolved_id(name: &str) -> String {
    format!("unresolved::{}", name.to_ascii_lowercase())
}

fn file_name(rel: &str) -> String {
    rel.rsplit('/').next().unwrap_or(rel).to_string()
}

fn file_stem(rel: &str) -> String {
    let base = rel.rsplit('/').next().unwrap_or(rel);
    let stem = base.rsplit_once('.').map(|(s, _)| s).unwrap_or(base);
    stem.to_ascii_lowercase()
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

fn strip_quotes(s: &str) -> String {
    let bytes = s.as_bytes();
    if bytes.len() >= 2 {
        let first = bytes[0] as char;
        let last = bytes[bytes.len() - 1] as char;
        if (first == '\'' || first == '"') && last == first {
            return s[1..s.len() - 1].to_string();
        }
    }
    s.to_string()
}

/// First significant (non-trivia, non-period) leaf word of a sentence, lowercased.
fn first_sig_word_lc(node: &Node, src: &str) -> String {
    significant_children(node, src)
        .into_iter()
        .find_map(|e| match e {
            El::Tok { text, .. } if text != "." => Some(text.to_ascii_lowercase()),
            _ => None,
        })
        .unwrap_or_default()
}

/// First significant leaf token that is an identifier or integer label (the name
/// of a paragraph/section header), preserving source spelling.
fn first_name(node: &Node, src: &str) -> Option<String> {
    significant_children(node, src)
        .into_iter()
        .find_map(|e| match e {
            El::Tok { text, kind } if kind == tk::IDENT || kind == tk::INT => {
                Some(text.to_string())
            }
            _ => None,
        })
}

/// Program name for a `PROGRAM-ID` sentence at `idx`: the identifier/literal
/// after the `PROGRAM-ID` keyword, looking into the following sentence if the
/// name sits past a period.
fn program_name(sentences: &[&Node], idx: usize, src: &str) -> Option<String> {
    let els = significant_children(sentences[idx], src);
    if let Some(p) = els
        .iter()
        .position(|e| matches!(e, El::Tok { text, .. } if text.eq_ignore_ascii_case("program-id")))
    {
        for e in els.iter().skip(p + 1) {
            match e {
                El::Tok { text, kind } if *kind == tk::IDENT => return Some((*text).to_string()),
                El::Tok { text, kind } if *kind == tk::STRING => return Some(strip_quotes(text)),
                _ => continue,
            }
        }
    }
    if let Some(next) = sentences.get(idx + 1) {
        for e in significant_children(next, src) {
            match e {
                El::Tok { text, kind } if kind == tk::IDENT => return Some(text.to_string()),
                El::Tok { text, kind } if kind == tk::STRING => return Some(strip_quotes(text)),
                _ => continue,
            }
        }
    }
    None
}

// --- scanning over the lossless token tree ----------------------------------

enum El<'a> {
    Tok { text: &'a str, kind: &'static str },
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
            }),
            Child::Node(n) => v.push(El::Grp(n)),
        }
    }
    v
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::cobol::parser::parse;

    fn graph_for(src: &str) -> Graph {
        let tree = parse("demo.cob", src);
        let file = SourceFile {
            rel_path: "demo.cob".to_string(),
            module_path: vec![],
            source: &tree.source,
            root: &tree.root,
        };
        lower("demo", std::slice::from_ref(&file), &[])
    }

    fn call_edges(g: &Graph) -> Vec<&crate::graph::GraphEdge> {
        g.edges().filter(|e| e.kind == edge::CALLS).collect()
    }

    const PROG: &str = "\
       IDENTIFICATION DIVISION.
       PROGRAM-ID. PAYROLL.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 WS-COUNT PIC 9(4) VALUE 0.
       88 WS-DONE  VALUE 100.
       05 WS-SUB   PIC 9(2).
       PROCEDURE DIVISION.
       MAIN-PARA.
           DISPLAY \"START\".
           PERFORM WORK-PARA.
           CALL \"EXTSUB\" USING WS-COUNT.
           STOP RUN.
       WORK-PARA.
           ADD 1 TO WS-COUNT.
           GO TO MAIN-PARA.
";

    #[test]
    fn emits_program_module_and_paragraph_functions() {
        let g = graph_for(PROG);
        assert!(g.count_nodes_of(ont::MODULE) >= 1, "program module");
        assert!(
            g.nodes()
                .any(|n| n.kind == ont::MODULE && n.name == "PAYROLL"),
            "module named after PROGRAM-ID"
        );
        // MAIN-PARA and WORK-PARA become functions.
        assert!(g.count_nodes_of(ont::FUNCTION) >= 2, "two paragraphs");
    }

    #[test]
    fn level_01_and_88_are_constants_but_not_05() {
        let g = graph_for(PROG);
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::CONSTANT && n.name == "WS-COUNT"));
        assert!(g
            .nodes()
            .any(|n| n.kind == ont::CONSTANT && n.name == "WS-DONE"));
        // Sub-field 05-level item is not emitted as a constant.
        assert!(!g
            .nodes()
            .any(|n| n.kind == ont::CONSTANT && n.name == "WS-SUB"));
    }

    #[test]
    fn perform_resolves_to_paragraph() {
        let g = graph_for(PROG);
        let calls = call_edges(&g);
        let work = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("WORK-PARA")))
            .expect("a PERFORM of WORK-PARA");
        assert!(
            work.to.starts_with("fn::payroll::work-para"),
            "to = {}",
            work.to
        );
        assert_eq!(work.props.get("resolved"), Some(&Json::Bool(true)));
        assert_eq!(work.props.get("via"), Some(&Json::str("perform")));
    }

    #[test]
    fn goto_resolves_to_paragraph() {
        let g = graph_for(PROG);
        let calls = call_edges(&g);
        let go = calls
            .iter()
            .find(|e| e.props.get("via") == Some(&Json::str("goto")))
            .expect("a GO TO edge");
        assert!(
            go.to.starts_with("fn::payroll::main-para"),
            "to = {}",
            go.to
        );
    }

    #[test]
    fn call_literal_is_external_dependency() {
        let g = graph_for(PROG);
        assert!(g.has_node("ext::extsub"), "external program node");
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::extsub"));
        let calls = call_edges(&g);
        assert!(calls
            .iter()
            .any(|e| e.to == "ext::extsub" && e.props.get("via") == Some(&Json::str("call"))));
    }

    #[test]
    fn copy_is_an_import_dependency() {
        let g = graph_for(
            "       DATA DIVISION.\n       WORKING-STORAGE SECTION.\n       COPY CUSTREC.\n",
        );
        assert!(g.has_node("ext::copy::custrec"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::IMPORTS && e.to == "ext::copy::custrec"));
        assert!(g
            .edges()
            .any(|e| e.kind == edge::DEPENDS_ON && e.to == "ext::copy::custrec"));
    }

    #[test]
    fn dynamic_call_is_unresolved() {
        let g = graph_for(
            "       PROCEDURE DIVISION.\n       MAIN.\n           CALL WS-PROGNAME.\n           STOP RUN.\n",
        );
        let calls = call_edges(&g);
        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].props.get("dynamic"), Some(&Json::Bool(true)));
        assert!(g.has_node("unresolved::ws-progname"));
    }

    #[test]
    fn inline_perform_is_not_a_call() {
        let g = graph_for(
            "       PROCEDURE DIVISION.\n       MAIN.\n           PERFORM UNTIL WS-DONE\n               ADD 1 TO WS-COUNT\n           END-PERFORM.\n           STOP RUN.\n",
        );
        assert!(
            call_edges(&g).is_empty(),
            "an inline PERFORM UNTIL has no paragraph operand"
        );
    }

    #[test]
    fn statements_before_first_paragraph_get_program_entry() {
        // No paragraph between PROCEDURE DIVISION and the first statement.
        let g = graph_for(
            "       IDENTIFICATION DIVISION.\n       PROGRAM-ID. TINY.\n       PROCEDURE DIVISION.\n           CALL \"SUB\".\n           STOP RUN.\n",
        );
        assert!(
            g.nodes().any(|n| n.kind == ont::FUNCTION
                && n.props.get("synthesized") == Some(&Json::Bool(true))),
            "a synthesised program-entry function owns the leading statements"
        );
        assert!(call_edges(&g).iter().any(|e| e.to == "ext::sub"));
    }

    #[test]
    fn case_insensitive_resolution() {
        let g = graph_for(
            "       PROCEDURE DIVISION.\n       Foo.\n           DISPLAY \"X\".\n       BAR.\n           PERFORM FOO.\n",
        );
        let calls = call_edges(&g);
        let foo = calls
            .iter()
            .find(|e| e.props.get("callee") == Some(&Json::str("FOO")))
            .expect("a PERFORM of FOO");
        assert_eq!(foo.props.get("resolved"), Some(&Json::Bool(true)));
    }

    #[test]
    fn output_is_deterministic() {
        let a = graph_for(PROG).to_jsonl();
        let b = graph_for(PROG).to_jsonl();
        assert_eq!(a, b, "graph output must be byte-identical across runs");
    }
}
