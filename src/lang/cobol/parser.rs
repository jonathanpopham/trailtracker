//! COBOL parser producing the language-neutral lossless CST.
//!
//! COBOL is organised into a strict hierarchy — program → divisions → sections →
//! paragraphs → sentences → statements — but precise paragraph segmentation in
//! true fixed form depends on the Area-A/Area-B column distinction, which is lost
//! in free form. Rather than gamble on columns, this parser uses a **flat,
//! sentence-oriented CST** (the same robust strategy the Fortran parser uses for
//! statement bodies): the file is a sequence of *sentences*, where a sentence is
//! the run of tokens up to and including a terminating period. Each sentence is
//! then *classified* from its leading significant tokens into one of a few CST
//! kinds the lowering interprets:
//!
//!   - [`node::DIVISION`]  — `<word> DIVISION …` (e.g. `PROCEDURE DIVISION.`);
//!   - [`node::SECTION`]   — `<word> SECTION …` (e.g. `WORKING-STORAGE SECTION.`);
//!   - [`node::PARAGRAPH`] — in the procedure division, a sentence that is a lone
//!     user word (or a numeric paragraph label) followed by a period;
//!   - [`node::DATA_ENTRY`] — outside the procedure division, a sentence whose
//!     first token is an integer level number (`01`, `05`, `77`, `88`, …);
//!   - [`node::SENTENCE`]  — every other statement/clause.
//!
//! The COBOL **period separator rule** is honoured precisely: a period ends a
//! sentence only when it is followed by whitespace, end-of-line, or end-of-file —
//! an editing period inside a PIC string such as `ZZ9.99` (followed immediately
//! by a digit) is *not* a terminator. Because the lexer also only treats `.` as a
//! decimal point when a digit follows, numeric literals and sentence terminators
//! never collide.
//!
//! Whatever is unrecognised still lands in the tree as its exact tokens, so the
//! result always round-trips. Recursion (into balanced `(…)` groups) is
//! depth-guarded at [`MAX_DEPTH`] — a `catch_unwind` cannot catch a stack
//! overflow, so the guard is the real defense.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::cobol::lexer::{is_keyword, kind as tk, lex, Form};

/// CST node-kind labels. The lowering interprets these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const DIVISION: &str = "Division";
    pub const SECTION: &str = "Section";
    pub const PARAGRAPH: &str = "Paragraph";
    pub const DATA_ENTRY: &str = "DataEntry";
    pub const SENTENCE: &str = "Sentence";

    pub const PAREN: &str = "Paren";
    pub const ERROR_STMT: &str = "ErrorStmt";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remainder as a flat balanced run. Mirrors the Rust/Fortran guard exactly.
const MAX_DEPTH: usize = 256;

/// Derive the source form from a repo-relative path. All three claimed
/// extensions (`.cob`/`.cbl`/`.cpy`) are treated as fixed form by default — the
/// historically dominant layout — while free-form `*>` comments remain supported
/// regardless, and the column-7 comment rule only fires over a genuine sequence
/// area, so a free-form file is handled correctly in practice too.
pub fn form_for_path(_path: &str) -> Form {
    Form::Fixed
}

pub fn parse(path: &str, source: &str) -> ParseTree {
    let form = form_for_path(path);
    let toks = lex(source, form);
    let mut p = CobolParser {
        src: source,
        toks,
        i: 0,
        diags: Vec::new(),
        depth: 0,
        in_procedure: false,
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

struct CobolParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current bracket recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
    /// True once a `PROCEDURE DIVISION` header has been seen — switches paragraph
    /// vs data-entry classification.
    in_procedure: bool,
}

impl<'s> CobolParser<'s> {
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
            code: "cobol.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; region flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
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
            let s = self.parse_sentence();
            // Track the procedure-division boundary for subsequent classification.
            if let Child::Node(n) = &s {
                if n.kind == node::DIVISION && division_word_is(n, self.src, "procedure") {
                    self.in_procedure = true;
                } else if n.kind == node::DIVISION {
                    self.in_procedure = false;
                }
            }
            c.push(s);
        }
        self.make_node(node::SOURCE_FILE, c)
    }

    /// Parse one sentence: trivia, then tokens up to and including a terminating
    /// period (descending into balanced `(…)` groups), then classify. Always
    /// consumes at least one token so the parse loop advances.
    fn parse_sentence(&mut self) -> Child {
        let mut c = Vec::new();
        self.ws(&mut c);
        self.consume_sentence(&mut c);
        if c.iter()
            .all(|child| matches!(child, Child::Token(t) if t.trivia))
        {
            // Nothing significant consumed — force progress.
            self.eat(&mut c);
        }
        let kind = self.classify(&c);
        Child::Node(self.make_node(kind, c))
    }

    /// Consume the tokens of one sentence into `out`, up to and including the
    /// terminating period. A period terminates only when followed by trivia or
    /// EOF (the COBOL separator rule); otherwise it is an ordinary token (e.g. an
    /// editing period inside a PIC string).
    fn consume_sentence(&mut self, out: &mut Vec<Child>) {
        while let Some(t) = self.toks.get(self.i) {
            if t.trivia {
                self.eat(out);
                continue;
            }
            let txt = t.span.text(self.src);
            if txt == "(" {
                let g = self.parse_delimited();
                out.push(Child::Node(g));
                continue;
            }
            if txt == "." && self.period_is_separator() {
                self.eat(out); // include the terminating period
                break;
            }
            self.eat(out);
        }
    }

    /// True if the period at the cursor is a sentence separator: the next token is
    /// trivia (whitespace/newline/comment) or there is no next token.
    fn period_is_separator(&self) -> bool {
        match self.toks.get(self.i + 1) {
            None => true,
            Some(t) => t.trivia,
        }
    }

    /// Parse a balanced `(...)` group. Newlines inside are ordinary trivia.
    /// Depth-guarded against hostile nesting.
    fn parse_delimited(&mut self) -> Node {
        let mut g = Vec::new();
        self.eat(&mut g); // opener `(`
        while let Some(t) = self.toks.get(self.i) {
            if t.trivia {
                self.eat(&mut g);
                continue;
            }
            let txt = t.span.text(self.src);
            if txt == ")" {
                self.eat(&mut g);
                break;
            }
            if txt == "(" {
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
        self.make_node(node::PAREN, g)
    }

    /// Iteratively consume a balanced `()` run (opener already eaten), appending
    /// every token as a flat leaf. Used at the depth cap.
    fn consume_balanced_flat(&mut self, out: &mut Vec<Child>) {
        let mut balance: i32 = 1;
        while balance > 0 {
            let txt = match self.toks.get(self.i) {
                Some(t) => t.span.text(self.src),
                None => break,
            };
            match txt {
                "(" => balance += 1,
                ")" => balance -= 1,
                _ => {}
            }
            self.eat(out);
        }
    }

    // --- classification -----------------------------------------------------

    /// Classify a consumed sentence from its leading significant tokens.
    fn classify(&self, children: &[Child]) -> &'static str {
        let sig = sig_tokens(children, self.src);
        if sig.is_empty() {
            return node::SENTENCE;
        }
        if let Some(w1) = sig.get(1) {
            if w1.text == "division" {
                return node::DIVISION;
            }
            if w1.text == "section" {
                return node::SECTION;
            }
        }
        if self.in_procedure {
            // A lone user word (non-verb) or a numeric label is a paragraph head.
            if sig.len() == 1 {
                let w0 = &sig[0];
                if (w0.kind == tk::IDENT && !is_keyword(&w0.text)) || w0.kind == tk::INT {
                    return node::PARAGRAPH;
                }
            }
            node::SENTENCE
        } else {
            if sig[0].kind == tk::INT {
                return node::DATA_ENTRY;
            }
            node::SENTENCE
        }
    }
}

// --- classification helpers -------------------------------------------------

/// A significant (non-trivia, non-period) leaf token: its kind and lowercased
/// text. Group nodes and the terminating period are omitted.
struct Sig {
    kind: &'static str,
    text: String,
}

fn sig_tokens(children: &[Child], src: &str) -> Vec<Sig> {
    let mut out = Vec::new();
    for c in children {
        if let Child::Token(t) = c {
            if t.trivia {
                continue;
            }
            let txt = t.span.text(src);
            if txt == "." {
                continue;
            }
            out.push(Sig {
                kind: t.kind,
                text: txt.to_ascii_lowercase(),
            });
        }
    }
    out
}

/// Is the first significant word of a division header equal to `word`
/// (case-insensitive)?
fn division_word_is(n: &Node, src: &str, word: &str) -> bool {
    n.children.iter().find_map(|c| match c {
        Child::Token(t) if !t.trivia && t.span.text(src) != "." => {
            Some(t.span.text(src).eq_ignore_ascii_case(word))
        }
        _ => None,
    }) == Some(true)
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
      *> a small program
       IDENTIFICATION DIVISION.
       PROGRAM-ID. HELLO-WORLD.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 WS-COUNT PIC 9(4) VALUE 0.
       88 WS-DONE  VALUE 100.
       PROCEDURE DIVISION.
       MAIN-PARA.
           DISPLAY \"HELLO\".
           PERFORM SUB-PARA.
           CALL \"OTHER\" USING WS-COUNT.
           STOP RUN.
       SUB-PARA.
           ADD 1 TO WS-COUNT.
";
        let tree = parse("hello.cob", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_divisions_and_paragraphs() {
        let src = "\
       IDENTIFICATION DIVISION.
       PROGRAM-ID. P.
       PROCEDURE DIVISION.
       MAIN-PARA.
           DISPLAY \"X\".
       SUB-PARA.
           DISPLAY \"Y\".
";
        let tree = parse("p.cbl", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::DIVISION), "{kinds:?}");
        assert!(kinds.contains(&node::PARAGRAPH), "{kinds:?}");
        assert_eq!(
            tree.root.children_of(node::PARAGRAPH).count(),
            2,
            "two paragraphs: {kinds:?}"
        );
    }

    #[test]
    fn data_entry_vs_paragraph_by_division() {
        // `88` outside procedure division → DataEntry; a numeric label inside
        // procedure division → Paragraph.
        let src = "\
       DATA DIVISION.
       01 REC.
       88 IS-OK VALUE 1.
       PROCEDURE DIVISION.
       100-MAIN.
           DISPLAY \"X\".
";
        let tree = parse("p.cob", src);
        assert!(tree.root.children_of(node::DATA_ENTRY).count() >= 2);
        assert_eq!(tree.root.children_of(node::PARAGRAPH).count(), 1);
    }

    #[test]
    fn editing_period_in_pic_does_not_split() {
        // The `.` in `ZZ9.99` is followed by a digit, so it is not a separator;
        // the data entry stays one sentence.
        let src = "\
       DATA DIVISION.
       01 WS-AMT PIC ZZ9.99 VALUE ZERO.
";
        let tree = parse("p.cob", src);
        assert!(tree.is_lossless());
        assert_eq!(tree.root.children_of(node::DATA_ENTRY).count(), 1);
    }

    #[test]
    fn sections_recognised() {
        let src = "\
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 X PIC 9.
       PROCEDURE DIVISION.
       100-MAIN SECTION.
           DISPLAY \"X\".
";
        let tree = parse("p.cob", src);
        assert_eq!(tree.root.children_of(node::SECTION).count(), 2);
    }

    #[test]
    fn fixed_form_round_trips() {
        let src = "000100 IDENTIFICATION DIVISION.\n000200 PROGRAM-ID. LEGACY.\n000300* a comment\n000400 PROCEDURE DIVISION.\n000500 MAIN.\n000600     STOP RUN.\n";
        let tree = parse("legacy.cob", src);
        assert!(tree.is_lossless());
        assert!(tree.root.children_of(node::DIVISION).count() >= 2);
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        let deep = format!(
            "       COMPUTE X = {}1{}.\n",
            "(".repeat(10_000),
            ")".repeat(10_000)
        );
        let tree = parse("deep.cob", &deep);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics
                .iter()
                .any(|d| d.code == "cobol.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }

    #[test]
    fn edge_cases_round_trip() {
        for src in [
            "       COMPUTE X = (1 + 2\n", // unterminated paren
            "       MOVE 'open\n",         // unterminated string
            "       MÖVE 1 TO X.\n",       // multi-byte char (lexes as error, covered)
            "",                            // empty file
            "\n\n   \n      * trailing\n", // only blanks and a comment
            "       PROGRAM-ID. P\n",      // missing terminating period
        ] {
            let tree = parse("edge.cob", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }
}
