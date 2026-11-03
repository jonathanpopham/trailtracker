//! Coarse, dialect-agnostic assembly parser producing the language-neutral
//! lossless CST.
//!
//! Assembly is **line-oriented**: a statement is one source line (the lexer emits
//! newlines as their own trivia kind so we can find the boundaries). This parser
//! makes a single coarse pass that splits each line into one of four item kinds —
//! `Label`, `Directive`, `Instruction`, or `ErrorItem` — and captures bracketed
//! operands (`(...)`, `[...]`, `{...}`) as balanced token-tree groups. It never
//! tries to understand a specific instruction set or assembler grammar; the graph
//! facts (calls, exports, imports, constants) are extracted from these real
//! tokens in the lowering pass, never invented.
//!
//! Classification (coarse):
//!   - `name:` (and NASM-local `.name:`) → **Label**. A line may begin with
//!     several labels; each `name:` is its own statement, so `loop: mov eax,1`
//!     yields a `Label` then an `Instruction`.
//!   - first token is a directive marker (`.xxx`, `%xxx`, a line-leading `#`, or a
//!     known bare directive word like `section`/`global`/`db`), **or** the second
//!     token is a definition directive (`NAME equ 5`, `msg db 0`) → **Directive**.
//!   - first token is any other identifier (a mnemonic) → **Instruction**.
//!   - anything else at line start → **ErrorItem** (still holds its tokens).
//!
//! Statement separation is **newline only** — `;` is always a comment (NASM/Intel
//! reading), so the GAS `;`-as-separator convention is a documented punt.
//!
//! The recursion (only via bracket nesting) is depth-guarded at [`MAX_DEPTH`]
//! against hostile input — a `catch_unwind` cannot catch a stack overflow, so the
//! guard is the real defense. Every statement consumes at least one significant
//! token, so the top-level loop always makes progress.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::asm::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const LABEL: &str = "Label";
    pub const DIRECTIVE: &str = "Directive";
    pub const INSTRUCTION: &str = "Instruction";
    pub const ERROR_ITEM: &str = "ErrorItem";

    pub const NAME: &str = "Name";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum bracket-nesting depth before the parser stops recursing and consumes
/// the remainder as a flat balanced run. Mirrors the Rust/Verilog parsers' guard.
const MAX_DEPTH: usize = 256;

/// Bare directive words (no `.`/`%` sigil) recognized at the start of a line.
/// Matched case-insensitively (MASM is case-insensitive). Coarse and not
/// exhaustive — an unrecognized word simply parses as an `Instruction`, which the
/// lowering treats as a (possibly call-bearing) mnemonic. Includes the data /
/// definition directives so a leading `db`/`equ` line is classified correctly.
const DIRECTIVE_WORDS: &[&str] = &[
    "section", "segment", "global", "globl", "extern", "extrn", "public", "include", "import",
    "export", "equ", "set", "org", "align", "times", "default", "bits", "use16", "use32", "use64",
    "cpu", "proc", "endp", "macro", "endmacro", "endm", "struc", "endstruc", "end", "title",
    "name", "assume", "db", "dw", "dd", "dq", "dt", "do", "ddq", "resb", "resw", "resd", "resq",
    "rest", "byte", "word", "dword", "qword", "tbyte", "textequ", "label",
];

/// Definition directives that appear as the *second* token of a `NAME <dir> ...`
/// line (MASM/NASM named-data and constant syntax). Matched case-insensitively.
const DEF_DIRECTIVES: &[&str] = &[
    "equ", "=", "db", "dw", "dd", "dq", "dt", "do", "ddq", "resb", "resw", "resd", "resq", "rest",
    "textequ", "proc", "label", "struc", "record",
];

fn eq_ascii_ci(a: &str, set: &[&str]) -> bool {
    set.iter().any(|s| a.eq_ignore_ascii_case(s))
}

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = AsmParser {
        src: source,
        toks,
        i: 0,
        diags: Vec::new(),
        depth: 0,
    };
    let root = p.parse_source_file();
    ParseTree {
        source_id: SourceId::from_path(path),
        path: path.to_string(),
        source: source.to_string(),
        root,
        diagnostics: p.diags,
    }
}

struct AsmParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current bracket-nesting depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> AsmParser<'s> {
    // --- cursor primitives --------------------------------------------------

    /// Append the current token (trivia or not) to `out` and advance.
    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading trivia tokens into `out`.
    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
        }
    }

    /// Kind of the n-th significant (non-trivia) token from the cursor.
    fn peek_kind_n(&self, n: usize) -> Option<&'static str> {
        let mut count = 0;
        for t in &self.toks[self.i..] {
            if t.trivia {
                continue;
            }
            if count == n {
                return Some(t.kind);
            }
            count += 1;
        }
        None
    }

    fn peek_kind(&self) -> Option<&'static str> {
        self.peek_kind_n(0)
    }

    /// Text of the n-th significant token from the cursor.
    fn peek_n_text(&self, n: usize) -> Option<&str> {
        let mut count = 0;
        for t in &self.toks[self.i..] {
            if t.trivia {
                continue;
            }
            if count == n {
                return Some(t.span.text(self.src));
            }
            count += 1;
        }
        None
    }

    fn peek_text(&self) -> Option<&str> {
        self.peek_n_text(0)
    }

    fn at(&self, s: &str) -> bool {
        self.peek_text() == Some(s)
    }

    fn at_ident(&self) -> bool {
        self.peek_kind() == Some(tk::IDENT)
    }

    fn at_open(&self) -> bool {
        self.at("(") || self.at("[") || self.at("{")
    }

    /// True if a newline appears in the trivia between the cursor and the next
    /// significant token — the basis for line-boundary detection.
    fn newline_before_next(&self) -> bool {
        for t in &self.toks[self.i..] {
            if !t.trivia {
                return false;
            }
            if t.kind == tk::NEWLINE {
                return true;
            }
        }
        false
    }

    fn cur_offset(&self) -> usize {
        self.toks
            .get(self.i)
            .map(|t| t.span.start as usize)
            .unwrap_or(self.src.len())
    }

    fn make_node(&self, kind: &'static str, children: Vec<Child>) -> Node {
        let span =
            children_span(&children).unwrap_or_else(|| ByteSpan::empty_at(self.cur_offset()));
        Node::new(kind, span, children)
    }

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "asm.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; group flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }

    // --- top level ----------------------------------------------------------

    fn parse_source_file(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c); // leading trivia: blank lines, comments, indentation
            if self.peek_kind().is_none() {
                break;
            }
            let item = self.parse_statement();
            c.push(Child::Node(item));
        }
        self.make_node(node::SOURCE_FILE, c)
    }

    /// Parse exactly one statement (one logical item). Always consumes at least
    /// one significant token, so the caller's loop is guaranteed to progress.
    fn parse_statement(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);

        // Label: `name:` (the next significant token after an identifier is `:`,
        // not `::`). Each label is its own statement; the rest of the line parses
        // fresh on the next iteration.
        if self.at_ident() && self.peek_n_text(1) == Some(":") {
            let n = self.name_node();
            c.push(Child::Node(n));
            self.ws(&mut c);
            if self.at(":") {
                self.eat(&mut c);
            }
            return self.make_node(node::LABEL, c);
        }

        let kind = self.classify_line();
        self.consume_line(&mut c);
        if kind == node::ERROR_ITEM {
            self.diags.push(Diagnostic {
                code: "asm.unrecognized_line",
                message: "line did not start with a label, directive, or mnemonic".to_string(),
                span: children_span(&c).unwrap_or_else(|| ByteSpan::empty_at(self.cur_offset())),
            });
        }
        self.make_node(kind, c)
    }

    /// Decide the kind of a non-label line from its first one or two significant
    /// tokens. Coarse — see the module docs.
    fn classify_line(&self) -> &'static str {
        match (self.peek_kind(), self.peek_text()) {
            // Line-leading `#` directive marker (emitted as punct by the lexer).
            (Some(tk::PUNCT), Some("#")) => node::DIRECTIVE,
            (Some(tk::IDENT), Some(t)) => {
                // `.xxx` / `%xxx` sigil directive, or a known bare directive word.
                if t.starts_with('.') || t.starts_with('%') || eq_ascii_ci(t, DIRECTIVE_WORDS) {
                    return node::DIRECTIVE;
                }
                // `NAME equ ...` / `msg db 0` — second token is a def directive.
                if let Some(second) = self.peek_n_text(1) {
                    if eq_ascii_ci(second, DEF_DIRECTIVES) {
                        return node::DIRECTIVE;
                    }
                }
                node::INSTRUCTION
            }
            (Some(_), _) => node::ERROR_ITEM,
            (None, _) => node::ERROR_ITEM,
        }
    }

    /// Consume the rest of the current source line into `out`, descending into
    /// balanced bracket groups. Eats the first significant token unconditionally
    /// (progress guarantee), then continues until a newline or EOF. The newline
    /// itself stays as leading trivia for the next statement.
    fn consume_line(&mut self, out: &mut Vec<Child>) {
        // First significant token (guaranteed progress).
        self.ws(out);
        if self.peek_kind().is_some() {
            if self.at_open() {
                let g = self.parse_delimited();
                out.push(Child::Node(g));
            } else {
                self.eat(out);
            }
        }
        loop {
            if self.peek_kind().is_none() || self.newline_before_next() {
                break;
            }
            self.ws(out); // intra-line trivia only (no newline ahead)
            if self.peek_kind().is_none() {
                break;
            }
            if self.at_open() {
                let g = self.parse_delimited();
                out.push(Child::Node(g));
            } else {
                self.eat(out);
            }
        }
    }

    // --- shared helpers -----------------------------------------------------

    fn name_node(&mut self) -> Node {
        let mut c = Vec::new();
        self.eat(&mut c); // the identifier (cursor is at it after caller ws)
        self.make_node(node::NAME, c)
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`. Cursor is at
    /// (or before trivia preceding) the opener. Depth-guarded.
    fn parse_delimited(&mut self) -> Node {
        let mut g = Vec::new();
        self.ws(&mut g);
        let (close, label) = match self.peek_text() {
            Some("(") => (")", node::PAREN),
            Some("[") => ("]", node::BRACKET),
            Some("{") => ("}", node::BRACE),
            _ => return self.make_node(node::ERROR_ITEM, g),
        };
        self.eat(&mut g); // opener
        loop {
            self.ws(&mut g);
            match self.peek_text() {
                None => break, // unterminated; still lossless
                Some(t) if t == close => {
                    self.eat(&mut g);
                    break;
                }
                Some("(") | Some("[") | Some("{") => {
                    if self.depth < MAX_DEPTH {
                        self.depth += 1;
                        let inner = self.parse_delimited();
                        self.depth -= 1;
                        g.push(Child::Node(inner));
                    } else {
                        self.eat(&mut g); // opener
                        self.consume_balanced_flat(&mut g);
                        self.note_depth_limit();
                    }
                }
                Some(_) => self.eat(&mut g),
            }
        }
        self.make_node(label, g)
    }

    /// Iteratively consume a balanced delimiter run (opener already eaten),
    /// appending every token as a flat leaf. Used at the depth cap so arbitrarily
    /// deep nesting is handled without further recursion.
    fn consume_balanced_flat(&mut self, out: &mut Vec<Child>) {
        let mut balance: i32 = 1;
        while balance > 0 {
            self.ws(out);
            match self.peek_text() {
                None => break,
                Some("(") | Some("[") | Some("{") => balance += 1,
                Some(")") | Some("]") | Some("}") => balance -= 1,
                _ => {}
            }
            self.eat(out);
        }
    }
}

fn children_span(children: &[Child]) -> Option<ByteSpan> {
    let mut it = children.iter().map(child_span);
    let first = it.next()?;
    Some(it.fold(first, |a, b| a.merge(b)))
}

fn child_span(c: &Child) -> ByteSpan {
    match c {
        Child::Node(n) => n.span,
        Child::Token(t) => t.span,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_and_is_lossless() {
        let src = "\
; a NASM-flavored file
section .data
msg:    db \"hello\", 0
len     equ $-msg

section .text
global  _start
extern  printf

_start:
    mov     eax, 1
    lea     rdi, [rel msg]
    call    printf
    jmp     .done
.done:
    ret
";
        let tree = parse("hello.asm", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn classifies_line_kinds() {
        let src = "_start:\n  mov eax, 1\n  .global foo\n  len equ 4\n";
        let tree = parse("t.s", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::LABEL));
        assert!(kinds.contains(&node::INSTRUCTION));
        assert!(kinds.contains(&node::DIRECTIVE));
    }

    #[test]
    fn label_and_instruction_on_one_line() {
        let src = "loop: mov eax, 1\n";
        let tree = parse("t.s", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert_eq!(kinds, vec![node::LABEL, node::INSTRUCTION]);
    }

    #[test]
    fn nasm_local_label_is_label() {
        let src = ".loop:\n  ret\n";
        let tree = parse("t.asm", src);
        let first = tree.root.child_nodes().next().expect("an item");
        assert_eq!(first.kind, node::LABEL);
        let name = first.child(node::NAME).expect("a name");
        assert_eq!(
            name.tokens().next().map(|t| t.span.text(src)),
            Some(".loop")
        );
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let depth = 10_000;
        let src = format!("mov eax, {}{}\n", "[".repeat(depth), "]".repeat(depth));
        let tree = parse("deep.s", &src);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics.iter().any(|d| d.code == "asm.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }

    #[test]
    fn edge_inputs_round_trip() {
        for src in [
            "",
            "\n\n   \n; only comments\n",
            "mov eax, [unterminated\n", // unterminated bracket
            "db \"unterminated\n",      // unterminated string
            "/* open block comment",    // unterminated comment
            "λ = '☃'  ; unicode\n",     // multi-byte
            "1234\n",                   // line starting with a number -> ErrorItem
            "ret",                      // no trailing newline
        ] {
            let tree = parse("edge.s", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
