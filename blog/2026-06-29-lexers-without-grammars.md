# 28 lossless lexers, zero grammars, and why I didn't believe my own tool

*2026-06-29*

I'm building a thing called TrailTracker. The short version: a local, offline code
intelligence engine — point it at a repo and it builds a graph of every function,
type, call, and import. Think of it as a map of a codebase you can actually query.
No cloud, no LLM in the runtime, no external dependencies. One std-only Rust binary
you can drop on an airgapped box and trust.

That last part — "no external dependencies" — is the constraint that makes the rest
of this post interesting. Because the normal way to parse 30 languages is to pull in
[tree-sitter](https://tree-sitter.github.io/) and its grammar packages. That's a
dependency. So it was off the table. Which left me hand-writing a lexer and parser
for every language I wanted to support.

It went suspiciously well. That's not a brag — "suspiciously" is the operative word,
and the back half of this post is about how I stopped trusting it and what I found.

## First: what a lexer even is

Before structure, before "this is a function and that's a class," there's a dumber
job: chop the raw bytes into **tokens**. `def foo(x):` isn't yet a function to a
lexer — it's the tokens `def`, `foo`, `(`, `x`, `)`, `:`. The lexer is the thing that
does that chopping.

In TrailTracker a token is deliberately tiny:

```rust
pub struct Token {
    pub kind: &'static str,   // "name", "int_literal", "comment", "punct", "error", …
    pub span: ByteSpan,       // { start: u32, end: u32 } — offsets into the source
    pub trivia: bool,         // whitespace/comments: parser skips, but we keep them
}
```

Notice a token doesn't *contain* the text. It's a label plus a `(start, end)` range
pointing back into the original source string. That detail matters a lot in a minute.

## The entire lexer is one loop

Here's the actual core of the Python lexer. This is not a simplified version for the
blog — this is the code:

```rust
fn run(mut self) -> Vec<Token> {
    while self.pos < self.bytes.len() {
        let start = self.pos;
        let c = self.peek();                                  // current character
        match c {
            '\n' => { self.bump(); self.push(NEWLINE, start, self.pos, false); }
            ' ' | '\t' => { self.eat_while(|c| c==' '||c=='\t'); self.push(WHITESPACE, …, true); }
            '#'  => { let end = self.find_line_end(start); self.pos = end; self.push(COMMENT, …, true); }
            '"' | '\'' => self.string(start, 0),
            c if is_ident_start(c) => self.name(start),       // letter/_ → identifier
            c if c.is_ascii_digit() => self.number(start),    // digit → number
            c if SINGLE_PUNCT.contains(c) => self.punct(start),
            _ => { self.bump(); self.push(ERROR, start, self.pos, false); }   // anything else
        }
    }
    self.tokens
}
```

That's the whole engine. A cursor walks from byte 0 to the end of the file. At each
step it looks at **one character**, decides what kind of token *starts* there, and a
little handler eats a contiguous run and emits one token. `name()` is "keep going
while it's a letter/digit/underscore." `number()` is "digits, maybe a dot, maybe an
exponent." `string()` is "a quote, then bytes until the matching quote." That's it.

## Why this needs no grammar — the part people get stuck on

When I describe this, the question I always get is: *shouldn't you have a grammar?*

Here's the thing I had to internalize: **lexing and parsing are different problems,
and only parsing needs a grammar.**

Tokens are *regular*. Every token kind is recognizable by purely **local** rules —
the current character plus maybe one of lookahead, then "keep going while a simple
predicate holds." A number is a digit followed by more digits. An identifier is a
letter followed by letters/digits/underscores. You do not need to know anything about
the surrounding code to tokenize. You can lex a file whose structure you don't
understand at all. So a lexer is just a big "what does this character begin?" switch.
Knowing the *token shapes* of a language is enough — and those barely change across
decades.

A **grammar** earns its keep one layer up, in the **parser**, which decides
*structure*: "a function is `def` NAME `(` params `)` `:` then an indented block; a
block is a sequence of statements; statements nest." That's recursive and
context-dependent. That's the part a formal grammar (BNF, tree-sitter) precisely
pins down, and that's the part where writing it by hand from memory is genuinely
risky.

So "no grammar in the lexer" isn't a corner I cut. Lexing legitimately doesn't need
one. The risk lives in the parser. Hold that thought.

## Lossless, and why that word is doing less work than it sounds

The lexer makes one strong promise: **lossless**. Concatenate every token's slice of
the source, in order, and you get the original file back, byte for byte. Whitespace,
comments, weird Unicode, a stray control character — all of it is covered by exactly
one token.

This isn't a hope; it's mechanical. Two invariants in that loop guarantee it:

1. **Contiguity.** Every handler emits a token whose span is exactly `[start, pos)`,
   and the next iteration starts at `pos`. The tokens tile the file — no gaps, no
   overlaps.
2. **Total coverage.** That last `_ =>` arm turns *any* byte nothing else matched into
   a one-character `error` token. Nothing is ever skipped or dropped.

So reconstruction is just arithmetic. The tool literally asserts
`reconstruct(tree) == source` on every file.

And here's the trap I want to be honest about: **lossless is the easy 80%.** It proves
I didn't *lose* anything. It says nothing about whether I *understood* anything. A
tokenizer that emits every byte as a token is perfectly lossless and perfectly
useless. Lossless is necessary, not sufficient. I kept catching myself reading "100%
lossless on a 200MB repo" as if it meant "correct." It doesn't.

## So I stopped trusting it

By this point I had 28 languages. Every one passed the gate: compiles, no warnings,
deterministic output, 100% lossless on real repos like Django, PostHog, and Next.js,
with plausible-looking counts (Django: ~32k functions, ~11k classes).

Plausible. Looking. Those are the words that should make you nervous. The whole thing
was graded by tests the same system wrote for itself. That's not verification, that's
a vibe.

So I did the obvious thing I should have done sooner: compare the output to a parser
nobody can argue with. For Python, that's `ast` — the parser that *ships inside
Python*. I parsed all ~2,900 Python files in Django with `ast`, pulled out every
function and class definition with its exact line number, and diffed that set against
what TrailTracker found. Not aggregate counts — the exact `(name, line)` set, per
file. Every definition the official parser sees that mine doesn't is either a bug or
something I can explain. Zero unexplained diffs, or it's not a source of truth.

First run: 99.8% of functions, 98.1% of classes.

If you've been paying attention to the tone of this post, you know 99.8% was a
*failure*. "Close" is meaningless when the whole point is to be ground truth. So I
chased the diff down to the exact symbols.

## Two real bugs the lossless gate never would have caught

**Bug one: collisions.** Functions had a line number baked into their node id; classes
didn't. So when a test redefined a fixture class — same name, same scope, a few lines
apart — the second one silently overwrote the first. 200-odd classes across Django,
gone, and the tool happily reported 100% lossless the whole time. One-line fix: put
the line in the class id too.

**Bug two: a panic that ate entire files.** One function checked for string prefixes
(the `r` in `r"raw"`, the `f` in `f"…"`) by slicing the first couple *bytes* of a
string. Fine for ASCII. But Django has a class literally named `Héllo`, and `é` is two
bytes, so the slice landed in the middle of a character and Rust panicked. The panic
was caught and isolated per-file — which sounds nice until you realize it meant *the
entire file* produced nothing, silently. Any file with a Unicode identifier just
vanished from the graph. Rewrote the check to work character-by-character.

After both fixes I reran the full diff across all 2,923 files:

```
ALL DJANGO (2923 files):
  FUNCTIONS missed=0 extra=0   CLASSES missed=0 extra=0
  files with ANY diff: 0
```

Zero. Every function, every class, exactly matching Python's own parser, across a
real production codebase. *That's* a source of truth. Not before.

## What I actually learned

- **The lexer was never the scary part.** Tokenizing is local and regular; hand-writing
  it is reliable, and losslessness is mechanically provable. The grammar question is a
  red herring at this layer.
- **The parser is where correctness lives or dies**, and it's exactly where both bugs
  were. Writing structure from memory is the part that needs a net.
- **Lossless is not correct.** It's a great floor and a terrible finish line. Both bugs
  sailed straight through the lossless gate.
- **If it's a source of truth, the bar is zero unexplained diffs — not a high
  percentage.** Diff the exact symbols against a parser you can't argue with, account
  for every entry, fix or explain each one.

Python is verified now. The other 27 languages are lossless and plausible — which, as
established, means *unverified*. They're next, each against its own canonical parser.
I'll write that up when there's something honest to report.
