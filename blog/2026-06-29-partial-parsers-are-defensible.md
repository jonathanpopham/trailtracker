# I only parse 20% of your code on purpose

*2026-06-29*

[Last post](2026-06-29-lexers-without-grammars.md) was about the lexer — the easy,
mechanical layer — and ended on a cliffhanger: the lexer was never the scary part, the
parser is. This is the parser post. And I'll be honest about the part I was actually
afraid of, because for a while I thought I'd built a house of cards.

Here's the decision that scared me: **TrailTracker does not fully parse any language.**
For each of the 28 languages, I parse maybe 20% of the grammar precisely and
*deliberately ignore the other 80%.* When I say it out loud it sounds like exactly the
kind of corner you pay for later. So I want to lay out the argument that talked me
down — and the one structural property that makes it actually hold, not just feel okay.

## The hard part of a grammar isn't what you'd guess

When people picture "parsing a language," they picture the declarations — functions,
classes, imports. Those are the *easy* part. They start with dead-obvious signposts:
`def`, `class`, `fn`, `struct`, `import`. A five-year-old could find them.

The *hard* 80% of any real grammar is **expressions**: `a + b * c.d().e[f]`, operator
precedence, associativity, the infinite ways things nest. That's where grammar files
get enormous and where hand-writing a parser turns into a research project.

And here's the thing: **I don't care about any of it.** A code map doesn't need to know
what `a + b * c.d()` *evaluates to*. It needs to know where the functions are, what
they're named, what they call, what they import. The brutal 80% of the grammar buys me
nothing.

## So I parse the signposts and blind-skip the rest

Here's the actual dispatch — the parser's "grammar," written as code instead of a
grammar file:

```rust
if self.at("fn")        { self.finish_fn(c) }
else if self.at("struct"){ self.finish_struct_like(c, STRUCT) }
else if self.at("enum")  { self.finish_enum(c) }
else if self.at("trait") { self.finish_trait(c) }
else if self.at("impl")  { self.finish_impl(c) }
else if self.at("use")   { self.finish_use(c) }
…
else { self.finish_error_item(c) }
```

Each `finish_*` parses one declaration's *header* precisely — we always come out
knowing the name. The **body** of a function, the inside of an expression — those get
captured as a lossless **token-tree**: a balanced `{…}`/`(…)` blob we keep but don't
interpret.

Think of it like indexing a 500-page book. You don't read the book to list its chapter
titles. You flip through, grab the headings, skip the paragraphs. Diagramming the
grammar of every sentence to produce a table of contents would be insane.

## "But how doesn't that just fall apart?"

This was my first real objection to my own design. If you don't understand the body,
how do you reliably know where it *ends* so you can get to the next declaration?

The answer is almost embarrassingly simple: **you can skip anything you don't
understand by matching brackets.** See `{`? Count up. See `}`? Count down. Stop at
zero. That's a counter, not a grammar. See an indented Python block? Grab lines until
the indentation drops. You can *always* find the exact end of a region you're ignoring,
mechanically, without understanding one byte of its contents.

So the loop is: parse the signpost precisely → blind-match the body to its closing
delimiter → keep the body's raw tokens → move on. It doesn't fall apart because the
parts I skip are fenced by delimiters I can match blind.

## The fear, named

Even with all that, I was nervous. "Parse 20%, skip 80%" pattern-matches to *technical
debt* — the kind of shortcut that's fine until the day a feature needs the part you
skipped, and then you're rewriting the foundation under a live system.

That fear is correct in general. It's just wrong *here*, for one specific reason.

## The property that kills the fear: nothing is ever thrown away

The corner-cutting failure mode — the one that forces a rewrite — requires that you
**destroyed information.** You parsed loosely, dropped what you didn't need, and now
it's gone.

I never drop anything. The bodies I "skip" are kept as **lossless token-trees** — the
raw material is *physically still in the tree*. I haven't *discarded* the 80%, I've
*deferred interpreting* it.

That single distinction flips the entire risk profile. Extending this architecture is
**never** "rewrite the parser." It's always "write a new pass that reads tokens I
already kept." Need richer call data tomorrow? The tokens are there. Need to recognize
a weird new declaration form? Add one arm to that `match`. Growth is *additive*,
permanently, because there's no lost information to go back and recover.

That's the actual test of whether an architecture is a house of cards: **can you grow
it without rewrites?** Here, yes — and not by luck, but because losslessness
*guarantees* the raw material is always still on disk in the tree.

## Where I genuinely might need "more" — and why it's not a parser problem

I'll name the soft spot, because pretending it doesn't exist would undercut everything
else. It's **call resolution.** Finding a call *site* — `foo()` — is trivial and the
partial parse nails it. Knowing *which* `foo`, especially for `obj.method()` where you
need to know `obj`'s type, is hard. Today it's name-based, with ambiguity preserved
honestly as candidates rather than guessed.

But here's why that isn't an indictment of partial parsing: **resolving calls is not a
parsing problem. It's semantic analysis.** Even a full grammar, a perfect complete
parse, doesn't resolve calls — you'd need a type-checker, a whole separate layer above
the parser. So a fuller grammar wouldn't help. If I ever need precise resolution, it
bolts on top of the graph I already have. Additive. Again.

So the real answer to "do we need more or less?" is: for *finding definitions*, we're
at exactly the right altitude — and I can prove it, which is the next part. For
*resolving calls*, we might want more someday, but that's a different layer, not a
deeper grammar.

## Why I can say "defensible" instead of "I hope so"

The honest weakness in all of this is that it's only as trustworthy as the
verification. So "is the partial grammar *enough* for language X?" can't be left as an
opinion. It has to be a measurement.

And it is. I diff TrailTracker's output against each language's *canonical* parser — the
one that ships inside the language. For Python that's `ast`. Across all ~2,900 Python
files in Django: **zero missed, zero extra** — every function, every class, exactly
matching the official parser. The partial grammar turned out to be *complete enough* to
match a full parser, exactly, on a real production codebase. That's not a vibe. That's a
diff with nothing in it.

It also tells me precisely *where* the partial approach falls short, when it does —
getting Python to zero surfaced two real bugs first (a node-identity collision and a
Unicode panic; see the last post). Every language I drive to zero is another brick in
the argument. And if some language ever *can't* be driven to zero by adding a case to
that dispatch, I find out cheaply, on that one language, instead of discovering it as a
systemic collapse.

## So, am I still scared of it?

No — and not because anyone reassured me. Because the design has two properties that
together make the fear unfounded:

1. **Lossless.** Nothing is thrown away, so every future need is reachable by adding a
   pass, never by a rewrite.
2. **Verifiable.** "Is partial enough here?" is an empirical, per-language question I can
   answer against ground truth — and where I've asked it, the answer is yes, exactly.

The risk was never the architecture. The risk is whether I do the verification work.
That's the thing worth being nervous about — and it's the thing I'm doing next, one
language at a time.
