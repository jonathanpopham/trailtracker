//! Fortran parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Julia/Lua parsers (Fortran is likewise keyword-block
//! delimited rather than whitespace-significant). Program-unit and definition
//! *headers* are parsed precisely — we always know a `subroutine`/`function`'s
//! header line, a `module`/`program` name, a derived-`type` header, an
//! `interface` block — while statement bodies are captured line-by-line as
//! `SimpleStmt` nodes whose `()`/`[]` regions are real balanced token groups.
//! Graph facts (calls, type uses, imports, constants) are extracted from these
//! real tokens in the lowering pass, never invented.
//!
//! Fortran is **case-insensitive** and has **no reserved words**, so the parser
//! classifies a statement by examining the lowercased leading tokens of its
//! *logical line* (physical lines joined across a trailing `&` free-form
//! continuation). The program units that open a `… end …` block are:
//! `program … end [program]`, `module … end [module]`,
//! `subroutine … end [subroutine]`, `function … end [function]` (with any
//! prefix: `pure`, `recursive`, `elemental`, `real(8)`, `type(t)`, `module`, …),
//! `type[, attrs] :: Name … end [type]` (a derived type), and
//! `[abstract] interface … end [interface]`. Control constructs (`do`/`if
//! then`/`select`/`where`/`block`/`associate`) are deliberately *not* parsed as
//! blocks — they are kept as flat `SimpleStmt` lines (their `end do`/`end if`
//! lines too), which is lossless and keeps the unit-terminator logic simple:
//! a `BLOCK` ends only at a bare `end` or an `end <unit>` line.
//!
//! Anything unrecognised still lands in the tree as its exact tokens, so the
//! result always round-trips. Recursion is depth-guarded at [`MAX_DEPTH`]
//! against hostile nesting (deeply nested program units *or* brackets) — a
//! `catch_unwind` cannot catch a stack overflow, so the guard is the real
//! defense.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::fortran::lexer::{kind as tk, lex, Form};

/// CST node-kind labels. The lowering interprets these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const PROGRAM: &str = "Program";
    pub const MODULE: &str = "Module";
    pub const SUBROUTINE: &str = "Subroutine";
    pub const FUNCTION: &str = "Function";
    pub const TYPE_DEF: &str = "TypeDef";
    pub const INTERFACE: &str = "Interface";

    pub const BLOCK: &str = "Block";
    pub const HEADER: &str = "Header";
    pub const END: &str = "End";
    pub const SIMPLE_STMT: &str = "SimpleStmt";
    pub const ERROR_STMT: &str = "ErrorStmt";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat run. Mirrors the Rust/Julia/Lua guard exactly.
const MAX_DEPTH: usize = 256;

/// Derive the source form from a repo-relative path. `.f`/`.for` are fixed form;
/// everything else this front end claims (`.f90`/`.f95`/`.f03`) is free form.
pub fn form_for_path(path: &str) -> Form {
    let ext = path.rsplit('.').next().unwrap_or("").to_ascii_lowercase();
    match ext.as_str() {
        "f" | "for" => Form::Fixed,
        _ => Form::Free,
    }
}

pub fn parse(path: &str, source: &str) -> ParseTree {
    let form = form_for_path(path);
    let toks = lex(source, form);
    let mut p = FortranParser {
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

struct FortranParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> FortranParser<'s> {
    // --- cursor primitives --------------------------------------------------

    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading trivia (whitespace, newlines, comments) into
    /// `out`.
    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
        }
    }

    /// Eat every remaining token (flush trailing trivia at end of input).
    fn flush(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() {
            self.eat(out);
        }
    }

    fn at_eof(&self) -> bool {
        let mut j = self.i;
        while j < self.toks.len() {
            if !self.toks[j].trivia {
                return false;
            }
            j += 1;
        }
        true
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
            code: "fortran.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; region flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }

    /// The significant tokens (kind + lowercased text) of the logical line that
    /// begins at the cursor. Physical lines are joined across a trailing free-form
    /// `&` continuation; the continuation `&` itself is omitted. Pure peek — does
    /// not move the cursor.
    fn line_sig(&self) -> Vec<(&'static str, String)> {
        let mut out = Vec::new();
        let mut last_amp = false;
        let mut j = self.i;
        while let Some(t) = self.toks.get(j) {
            if t.trivia {
                if t.kind == tk::NEWLINE {
                    if last_amp {
                        j += 1;
                        continue;
                    }
                    break;
                }
                j += 1;
                continue;
            }
            let txt = t.span.text(self.src);
            if txt == "&" {
                last_amp = true;
                j += 1;
                continue;
            }
            out.push((t.kind, txt.to_ascii_lowercase()));
            last_amp = false;
            j += 1;
        }
        out
    }

    // --- top level ----------------------------------------------------------

    fn parse_source_file(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            if self.at_eof() {
                self.flush(&mut c);
                break;
            }
            let s = self.parse_statement();
            c.push(Child::Node(s));
        }
        self.make_node(node::SOURCE_FILE, c)
    }

    /// Parse a unit body: statements until a unit terminator (`end` / `end
    /// <unit>`) or EOF. The terminator line is **not** consumed — the caller owns
    /// it. Depth-guarded.
    fn parse_block(&mut self) -> Node {
        if self.depth >= MAX_DEPTH {
            let mut c = Vec::new();
            self.consume_block_flat(&mut c);
            self.note_depth_limit();
            return self.make_node(node::BLOCK, c);
        }
        self.depth += 1;
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            if self.at_eof() {
                self.flush(&mut c);
                break;
            }
            let sig = self.line_sig();
            if sig.is_empty() {
                // Defensive: guarantee progress on a stray non-classifiable token.
                self.eat(&mut c);
                continue;
            }
            if is_unit_end(&sig) {
                break;
            }
            let s = self.parse_statement();
            c.push(Child::Node(s));
        }
        let block = self.make_node(node::BLOCK, c);
        self.depth -= 1;
        block
    }

    /// At the depth cap, swallow a unit body as flat tokens up to (not including)
    /// a unit terminator, without recursing.
    fn consume_block_flat(&mut self, out: &mut Vec<Child>) {
        loop {
            self.ws(out);
            if self.at_eof() {
                self.flush(out);
                break;
            }
            let sig = self.line_sig();
            if !sig.is_empty() && is_unit_end(&sig) {
                break;
            }
            // Consume one logical line of tokens flatly.
            self.consume_line(out);
            // Eat the line-terminating newline so progress is guaranteed.
            self.ws_one_newline(out);
        }
    }

    /// Eat trivia up to and including the next newline (if any), to advance past a
    /// flat-consumed line.
    fn ws_one_newline(&mut self, out: &mut Vec<Child>) {
        while let Some(t) = self.toks.get(self.i) {
            if !t.trivia {
                break;
            }
            let is_nl = t.kind == tk::NEWLINE;
            self.eat(out);
            if is_nl {
                break;
            }
        }
    }

    // --- statements ---------------------------------------------------------

    fn parse_statement(&mut self) -> Node {
        let sig = self.line_sig();
        if sig.is_empty() {
            let mut c = Vec::new();
            self.eat(&mut c);
            return self.make_node(node::ERROR_STMT, c);
        }
        let t0 = sig[0].1.as_str();
        let t1 = sig.get(1).map(|s| s.1.as_str());

        // A leading end-form at statement position (only reached at top level, or
        // for a malformed body) is consumed as a simple line so the loop advances.
        if is_unit_end(&sig) {
            return self.finish_simple();
        }

        // Subprogram definition (any prefix): `… function NAME(…)` / `… subroutine
        // NAME(…)`. Checked before the `type`/`module` branches so a prefixed
        // `type(t) function f()` or `module function f()` is classified honestly.
        if let Some(kw) = detect_subprogram(&sig) {
            let label = if kw == "function" {
                node::FUNCTION
            } else {
                node::SUBROUTINE
            };
            return self.finish_unit(label);
        }

        match t0 {
            "program" => self.finish_unit(node::PROGRAM),
            "module" if t1 == Some("procedure") => self.finish_simple(),
            "module" => self.finish_unit(node::MODULE),
            "interface" => self.finish_unit(node::INTERFACE),
            "abstract" if t1 == Some("interface") => self.finish_unit(node::INTERFACE),
            "type" if is_type_def(&sig) => self.finish_unit(node::TYPE_DEF),
            _ => self.finish_simple(),
        }
    }

    /// A program unit: header line, body block, and the matching `end` line.
    fn finish_unit(&mut self, label: &'static str) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);

        let mut h = Vec::new();
        self.consume_line(&mut h);
        if h.is_empty() {
            // Guarantee progress even on a pathological header.
            self.eat(&mut h);
        }
        c.push(Child::Node(self.make_node(node::HEADER, h)));

        let body = self.parse_block();
        c.push(Child::Node(body));

        self.ws(&mut c);
        if !self.at_eof() && is_unit_end(&self.line_sig()) {
            let mut e = Vec::new();
            self.consume_line(&mut e);
            c.push(Child::Node(self.make_node(node::END, e)));
        } else {
            self.diags.push(Diagnostic {
                code: "fortran.missing_end",
                message: "program unit not closed by a matching end".to_string(),
                span: ByteSpan::empty_at(self.cur_offset()),
            });
        }
        self.make_node(label, c)
    }

    /// One ordinary statement (a logical line), with `()`/`[]` regions as balanced
    /// groups. Always consumes at least one token so the parse loop advances.
    fn finish_simple(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.consume_line(&mut c);
        if c.iter()
            .all(|child| matches!(child, Child::Token(t) if t.trivia))
        {
            // Nothing significant consumed — force progress.
            self.eat(&mut c);
        }
        self.make_node(node::SIMPLE_STMT, c)
    }

    /// Consume the tokens of one logical line into `out`, descending into balanced
    /// `()`/`[]` groups, joining physical lines across a trailing free-form `&`
    /// continuation. The line-terminating newline is left for the caller's `ws`.
    fn consume_line(&mut self, out: &mut Vec<Child>) {
        let mut last_amp = false;
        while let Some(t) = self.toks.get(self.i) {
            if t.trivia {
                if t.kind == tk::NEWLINE {
                    if last_amp {
                        self.eat(out); // continuation: keep going
                        continue;
                    }
                    break; // end of logical line; leave the newline for the parent
                }
                self.eat(out);
                continue;
            }
            let txt = t.span.text(self.src);
            if txt == "(" || txt == "[" {
                let g = self.parse_delimited();
                out.push(Child::Node(g));
                last_amp = false;
                continue;
            }
            if txt == "&" {
                self.eat(out);
                last_amp = true;
                continue;
            }
            self.eat(out);
            last_amp = false;
        }
    }

    /// Parse a balanced `(...)` or `[...]` group. Newlines inside are ordinary
    /// trivia. Depth-guarded against hostile nesting.
    fn parse_delimited(&mut self) -> Node {
        let mut g = Vec::new();
        self.ws(&mut g);
        let (close, label) = match self.toks.get(self.i).map(|t| t.span.text(self.src)) {
            Some("(") => (")", node::PAREN),
            Some("[") => ("]", node::BRACKET),
            _ => return self.make_node(node::ERROR_STMT, g),
        };
        self.eat(&mut g); // opener
        while let Some(t) = self.toks.get(self.i) {
            if t.trivia {
                self.eat(&mut g);
                continue;
            }
            let txt = t.span.text(self.src);
            if txt == close {
                self.eat(&mut g);
                break;
            }
            if txt == "(" || txt == "[" {
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
            } else {
                self.eat(&mut g);
            }
        }
        self.make_node(label, g)
    }

    /// Iteratively consume a balanced delimiter run (opener already eaten),
    /// appending every token as a flat leaf. Used at the depth cap.
    fn consume_balanced_flat(&mut self, out: &mut Vec<Child>) {
        let mut balance: i32 = 1;
        while balance > 0 {
            let txt = match self.toks.get(self.i) {
                Some(t) => t.span.text(self.src),
                None => break,
            };
            match txt {
                "(" | "[" => balance += 1,
                ")" | "]" => balance -= 1,
                _ => {}
            }
            self.eat(out);
        }
    }
}

// --- classification helpers -------------------------------------------------

/// Is this logical line a program-unit terminator (`end` / `end <unit>` /
/// `endsubroutine` …)? Control-construct ends (`end do`, `end if`, `end select`,
/// `endif`, …) are *not* unit terminators.
fn is_unit_end(sig: &[(&'static str, String)]) -> bool {
    if sig.is_empty() {
        return false;
    }
    let t0 = sig[0].1.as_str();
    if matches!(
        t0,
        "endprogram" | "endmodule" | "endsubroutine" | "endfunction" | "endtype" | "endinterface"
    ) {
        return true;
    }
    if t0 == "end" {
        return match sig.get(1).map(|s| s.1.as_str()) {
            None => true, // bare `end` (this logical line is just `end`)
            Some("program") | Some("module") | Some("subroutine") | Some("function")
            | Some("type") | Some("interface") => true,
            Some(_) => false, // `end do`, `end if`, `end select`, `end block`, …
        };
    }
    false
}

/// Detect a subprogram definition: a top-level `function`/`subroutine` keyword
/// (delimiter depth 0) immediately followed by an identifier name. Returns the
/// keyword (`"function"` / `"subroutine"`). Any prefix is allowed.
fn detect_subprogram(sig: &[(&'static str, String)]) -> Option<&'static str> {
    let mut depth: i32 = 0;
    for k in 0..sig.len() {
        let txt = sig[k].1.as_str();
        match txt {
            "(" | "[" => depth += 1,
            ")" | "]" => {
                depth -= 1;
                if depth < 0 {
                    depth = 0;
                }
            }
            _ => {}
        }
        if depth == 0 && (txt == "function" || txt == "subroutine") {
            if let Some((kind, _)) = sig.get(k + 1) {
                if *kind == tk::IDENT {
                    return Some(if txt == "function" {
                        "function"
                    } else {
                        "subroutine"
                    });
                }
            }
        }
    }
    None
}

/// Is a `type …` line a derived-type *definition* (a block), as opposed to a
/// `type(foo) :: x` variable declaration or a `type is (…)` select guard?
fn is_type_def(sig: &[(&'static str, String)]) -> bool {
    match sig.get(1).map(|s| s.1.as_str()) {
        Some("(") => false,  // type(foo) :: x  — a declaration
        Some("is") => false, // type is (foo)   — a select-type guard
        Some(_) => true,     // type :: Name / type Name / type, attrs :: Name
        None => false,
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
! a module
module geometry
  implicit none
  real, parameter :: pi = 3.14159

  type :: circle
     real :: radius
  end type circle

contains

  function area(c) result(a)
     type(circle), intent(in) :: c
     real :: a
     a = pi * c%radius ** 2
  end function area

  subroutine grow(c, k)
     type(circle), intent(inout) :: c
     real :: k
     c%radius = c%radius * k
  end subroutine grow
end module geometry
";
        let tree = parse("geometry.f90", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_units() {
        let src =
            "module m\nend module\nsubroutine s\nend subroutine\nfunction f()\nend function\n";
        let tree = parse("t.f90", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::MODULE), "{kinds:?}");
        assert!(kinds.contains(&node::SUBROUTINE), "{kinds:?}");
        assert!(kinds.contains(&node::FUNCTION), "{kinds:?}");
    }

    #[test]
    fn prefixed_function_is_a_unit() {
        let src = "pure real function sq(x)\n  real :: x\n  sq = x*x\nend function sq\n";
        let tree = parse("t.f90", src);
        assert!(tree.root.children_of(node::FUNCTION).count() == 1);
    }

    #[test]
    fn control_end_is_not_a_unit_end() {
        // The do/if `end` lines must stay inside the subroutine body, not close it.
        let src = "subroutine s\n  do i = 1, 10\n    if (i > 0) then\n      call f(i)\n    end if\n  end do\nend subroutine s\n";
        let tree = parse("t.f90", src);
        let sub = tree
            .root
            .children_of(node::SUBROUTINE)
            .next()
            .expect("a subroutine");
        let body = sub.child(node::BLOCK).expect("a body block");
        // Body should hold several statements including the do/if/end do/end if.
        assert!(body.children_of(node::SIMPLE_STMT).count() >= 5);
    }

    #[test]
    fn derived_type_vs_declaration() {
        let src = "type :: point\n  real :: x\nend type point\n";
        let tree = parse("t.f90", src);
        assert_eq!(tree.root.children_of(node::TYPE_DEF).count(), 1);

        // A `type(foo) :: v` line is a plain declaration, not a TypeDef block.
        let src2 = "subroutine s\n  type(point) :: v\nend subroutine\n";
        let tree2 = parse("t.f90", src2);
        assert_eq!(
            tree2
                .root
                .walk()
                .filter(|n| n.kind == node::TYPE_DEF)
                .count(),
            0
        );
    }

    #[test]
    fn free_form_continuation_joins_lines() {
        let src = "x = foo(a, &\n        b, &\n        c)\nprint *, x\n";
        let tree = parse("t.f90", src);
        // The continued assignment is one statement; the print is another.
        assert_eq!(tree.root.children_of(node::SIMPLE_STMT).count(), 2);
        assert!(tree.is_lossless());
    }

    #[test]
    fn fixed_form_round_trips() {
        let src = "C     a fixed-form program\n      program main\n      call foo(1)\n      end\n";
        let tree = parse("legacy.f", src);
        assert!(tree.is_lossless());
        assert_eq!(tree.root.children_of(node::PROGRAM).count(), 1);
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let deep_brackets = format!("x = {}{}\n", "(".repeat(10_000), ")".repeat(10_000));
        let mut deep_units = String::new();
        for k in 0..2_000 {
            deep_units.push_str(&format!("module m{k}\n"));
        }
        for _ in 0..2_000 {
            deep_units.push_str("end module\n");
        }
        for src in [deep_brackets, deep_units] {
            let tree = parse("deep.f90", &src);
            assert!(tree.is_lossless(), "deeply nested input must round-trip");
            assert!(
                tree.diagnostics
                    .iter()
                    .any(|d| d.code == "fortran.depth_limit"),
                "depth limit should be reported, not silent"
            );
        }
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "x = (1, 2\n",           // unterminated paren
            "s = 'open\n",           // unterminated string
            "α = 1  ! unicode\n",    // multi-byte identifier (lexes as error, covered)
            "",                      // empty file
            "\n\n   \n! trailing\n", // only blanks and comments
            "subroutine s\n",        // unterminated unit (missing end)
        ] {
            let tree = parse("edge.f90", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
