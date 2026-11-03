//! Tcl parser producing the language-neutral lossless CST.
//!
//! Strategy mirrors the Bash parser: a Tcl script is a sequence of *commands*,
//! each a run of words terminated by a `newline` or `;`. The parser captures each
//! command as a flat run of the real, lossless tokens — graph facts (proc
//! definitions, namespace scopes, calls, includes) are read off those tokens in
//! the lowering pass, never invented.
//!
//! The one place the parser adds structure is **body descent**. In Tcl a script
//! body is just a brace word whose contents are evaluated later as a script
//! (`proc name args body`, `namespace eval ns body`, the trailing body of a
//! control command, …). For those commands the parser takes the command's *last*
//! brace word, re-lexes its interior, and parses it as a nested [`node::SCRIPT`],
//! splicing `{` + Script + `}` in place of the single brace-word token. This is
//! how nested procs and calls inside a body become visible — and because only the
//! final brace word is descended into, list literals and `expr` condition braces
//! (e.g. `{a b c}`, `{$x > 0}`) are left untouched rather than mis-parsed as code.
//!
//! Anything unrecognized still lands in the tree as its exact tokens, so the
//! result always round-trips byte-for-byte. Body descent is depth-guarded at
//! [`MAX_DEPTH`] against hostile nesting (deeply nested proc bodies), because a
//! `catch_unwind` cannot catch a stack overflow.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::tcl::lexer::{kind as tk, lex};

/// CST node-kind labels. Typed views and the lowering interpret these.
pub mod node {
    pub const SCRIPT: &str = "Script";
    pub const COMMAND: &str = "Command";
}

/// Maximum body-descent depth before the parser stops expanding brace bodies and
/// leaves the remaining brace word as a flat token. Mirrors the Rust/Bash/Python
/// guard exactly — a `catch_unwind` cannot catch a stack overflow, so the guard is
/// the real defense against hostile nesting.
const MAX_DEPTH: usize = 256;

/// Commands whose *last* brace-word argument is a script body the parser descends
/// into. For `namespace`, descent additionally requires the `eval` subcommand
/// (checked in [`TclParser::parse_command`]).
const BODY_COMMANDS: &[&str] = &[
    "proc",
    "namespace",
    "while",
    "for",
    "foreach",
    "if",
    "elseif",
    "else",
    "catch",
    "try",
    "finally",
    "eval",
    "uplevel",
    "time",
];

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = TclParser {
        src: source,
        toks,
        i: 0,
        diags: Vec::new(),
        depth: 0,
    };
    let root = p.parse_script();
    ParseTree {
        source_id: SourceId::from_path(path),
        path: path.to_string(),
        source: source.to_string(),
        root,
        diagnostics: p.diags,
    }
}

struct TclParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current body-descent depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> TclParser<'s> {
    // --- cursor primitives --------------------------------------------------

    /// Append the current token (trivia or not) to `out` and advance.
    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Kind of the token at the cursor (no trivia skipping).
    fn cur_kind(&self) -> Option<&'static str> {
        self.toks.get(self.i).map(|t| t.kind)
    }

    /// Text of the token at the cursor.
    fn cur_text(&self) -> Option<&str> {
        self.toks.get(self.i).map(|t| t.span.text(self.src))
    }

    fn cur_is_trivia(&self) -> bool {
        self.toks.get(self.i).map(|t| t.trivia).unwrap_or(false)
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

    // --- top level ----------------------------------------------------------

    fn parse_script(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.eat_separators(&mut c);
            if self.cur_kind().is_none() {
                break;
            }
            let cmd = self.parse_command();
            c.push(Child::Node(cmd));
        }
        self.make_node(node::SCRIPT, c)
    }

    /// Eat leading trivia plus command separators (`newline`, `;`) into `out`,
    /// leaving the cursor on the next real word token or end of input.
    fn eat_separators(&mut self, out: &mut Vec<Child>) {
        loop {
            while self.cur_is_trivia() {
                self.eat(out);
            }
            match self.cur_kind() {
                Some(tk::NEWLINE) | Some(tk::SEMICOLON) => self.eat(out),
                _ => break,
            }
        }
    }

    // --- commands -----------------------------------------------------------

    /// One command: a run of words up to a `newline`/`;`/end. Always makes
    /// progress (the caller guarantees the cursor is on a real token). If the
    /// command is body-bearing, its last brace word is expanded into a nested
    /// script in place.
    fn parse_command(&mut self) -> Node {
        let mut c: Vec<Child> = Vec::new();
        let mut at_word_start = true;
        let mut words_seen = 0usize;
        let mut first_word: Option<String> = None;
        let mut second_word: Option<String> = None;
        let mut last_brace_pos: Option<usize> = None;

        loop {
            // Word-separating trivia (whitespace, line continuations, comments).
            while self.cur_is_trivia() {
                self.eat(&mut c);
                at_word_start = true;
            }
            match self.cur_kind() {
                None | Some(tk::NEWLINE) | Some(tk::SEMICOLON) => break,
                _ => {}
            }
            let kind = self.cur_kind().unwrap();
            if at_word_start {
                words_seen += 1;
                let txt = self.cur_text().unwrap_or("").to_string();
                if words_seen == 1 {
                    first_word = Some(txt);
                } else if words_seen == 2 {
                    second_word = Some(txt);
                }
            }
            if kind == tk::BRACE_WORD {
                last_brace_pos = Some(c.len());
            }
            self.eat(&mut c);
            at_word_start = false;
        }

        if let Some(pos) = last_brace_pos {
            if should_descend(first_word.as_deref(), second_word.as_deref()) {
                if self.depth < MAX_DEPTH {
                    if let Some(Child::Token(tok)) = c.get(pos).cloned() {
                        let expansion = self.expand_body(&tok);
                        c.splice(pos..=pos, expansion);
                    }
                } else {
                    self.note_depth_limit();
                }
            }
        }

        self.make_node(node::COMMAND, c)
    }

    /// Replace a brace-word token with `{` + nested [`node::SCRIPT`] + `}`. The
    /// interior is re-lexed and re-parsed with spans offset back into the original
    /// source, so the three children cover exactly the same bytes as the brace
    /// word — losslessness is preserved.
    fn expand_body(&mut self, tok: &Token) -> Vec<Child> {
        let s = tok.span.start as usize;
        let e = tok.span.end as usize;
        // A BRACE_WORD is always terminated, so e >= s + 2 (`{}` at minimum).
        let inner_start = s + 1;
        let inner_end = e - 1;
        let open = Token {
            kind: tk::BRACE_OPEN,
            span: ByteSpan::new(s, inner_start),
            trivia: false,
        };
        let close = Token {
            kind: tk::BRACE_CLOSE,
            span: ByteSpan::new(inner_end, e),
            trivia: false,
        };
        let inner_src = &self.src[inner_start..inner_end];
        let mut inner_toks = lex(inner_src);
        for t in &mut inner_toks {
            t.span = ByteSpan::new(
                t.span.start as usize + inner_start,
                t.span.end as usize + inner_start,
            );
        }
        let mut sub = TclParser {
            src: self.src,
            toks: inner_toks,
            i: 0,
            diags: Vec::new(),
            depth: self.depth + 1,
        };
        let mut script = sub.parse_script();
        // Anchor the script span to the brace interior even when it is empty.
        script.span = ByteSpan::new(inner_start, inner_end);
        self.diags.append(&mut sub.diags);
        vec![Child::Token(open), Child::Node(script), Child::Token(close)]
    }

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "tcl.depth_limit",
            message: format!("body nesting depth limit ({MAX_DEPTH}) reached; region flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }
}

/// Whether a command's last brace word is a script body to descend into, given
/// its first and second words.
fn should_descend(first: Option<&str>, second: Option<&str>) -> bool {
    match first {
        Some("namespace") => second == Some("eval"),
        Some(w) => BODY_COMMANDS.contains(&w),
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
# a Tcl script
package require Tk 8.6

set NAME \"world\"

proc greet {name} {
    set msg \"hello, $name\"
    puts $msg
}

namespace eval ::app {
    variable count 0
    proc tick {} {
        incr ::app::count
    }
}

if {$NAME ne \"\"} {
    greet $NAME
} else {
    greet stranger
}

foreach x {a b c} {
    puts $x
}

source ./lib.tcl
greet world
";
        let tree = parse("script.tcl", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_commands() {
        let src = "set a 1\nputs $a\n";
        let tree = parse("t.tcl", src);
        let cmds = tree.root.children_of(node::COMMAND).count();
        assert_eq!(cmds, 2);
    }

    #[test]
    fn proc_body_is_descended_into() {
        let src = "proc outer {} {\n  proc inner {} {\n    puts hi\n  }\n}\n";
        let tree = parse("t.tcl", src);
        // The nested `proc inner` lives inside the outer proc's body Script.
        let nested = tree.root.walk().filter(|n| n.kind == node::SCRIPT).count();
        assert!(nested >= 2, "outer + inner body scripts should both exist");
        assert!(tree.is_lossless());
    }

    #[test]
    fn list_literal_brace_is_not_descended() {
        // `set` is not a body command, so `{a b c}` stays a single brace token.
        let src = "set L {a b c}\n";
        let tree = parse("t.tcl", src);
        let scripts = tree.root.walk().filter(|n| n.kind == node::SCRIPT).count();
        assert_eq!(scripts, 1, "only the top-level script; no body descent");
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        // Deeply nested proc bodies, far beyond MAX_DEPTH; must not stack-overflow
        // and must stay lossless.
        let mut src = String::new();
        for _ in 0..5_000 {
            src.push_str("proc p {} {");
        }
        src.push_str("puts hi");
        for _ in 0..5_000 {
            src.push('}');
        }
        src.push('\n');

        let tree = parse("deep.tcl", &src);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics.iter().any(|d| d.code == "tcl.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }

    #[test]
    fn unterminated_and_unicode_round_trip() {
        for src in [
            "set s \"oops\n",           // unterminated string
            "proc f {body\n",           // unterminated brace
            "λ {set ☃ €}  # unicode\n", // multi-byte words
            "",                         // empty file
            "\n\n   \n# trailing\n",    // only blanks and comments
        ] {
            let tree = parse("edge.tcl", src);
            assert!(tree.is_lossless(), "must round-trip: {src:?}");
        }
    }

    #[test]
    fn output_is_deterministic() {
        let src = "proc f {} { g }\nnamespace eval ns { proc g {} { puts hi } }\nsource ./x.tcl\n";
        let a = parse("d.tcl", src);
        let b = parse("d.tcl", src);
        assert_eq!(a.to_json().to_line(), b.to_json().to_line());
    }
}
