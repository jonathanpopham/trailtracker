//! ADR-0008 conformance checker: the retrieval-safe verbalization grammar.
//!
//! The verbalizer (V1, epic E-V) renders the recovered graph as deterministic
//! sentences. This module is the quality bar those sentences must pass:
//! every rule of [ADR-0008](../../docs/decisions/0008-verbalization-grammar.md)
//! enforced mechanically, with the same finding discipline as `doctor` and
//! `arch-verify` (rule id + span + fix hint).
//!
//! The checker is a pure function of its inputs: same sentences, same
//! glossary, same violations in the same order. Backticks mark code spans;
//! anything inside them is exempt from the lexical rules. Unquoted tokens
//! that are structurally code-shaped (contain `_`, `/`, `::`, `#`, an
//! internal `.`, mixed case, or letters+digits) are treated as identifiers.
//!
//! Mechanical approximations (documented in the ADR): predicate counting
//! uses subject-verb adjacency (a registered verb directly after a handle,
//! name, or identifier); "one `and` joining values, never facts" is enforced
//! as a conjunction budget plus the predicate budget; R5 checks the
//! enforceable subset of the ordering principle.

use crate::core::json::Json;
use std::collections::BTreeMap;

/// R8: maximum sentence length in Unicode scalar values.
pub const MAX_SENTENCE_CHARS: usize = 160;

/// Sentinel `sentence` index for violations that belong to the declared
/// glossary rather than to any sentence (e.g. bad handle grammar, numbering
/// gaps). Sorts after all real sentence indices.
pub const GLOSSARY_SENTENCE: usize = usize::MAX;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// One glossary entry: a short stable handle and its full expansion, in
/// assignment order (assignment order = value ranking, per ADR-0008 R3/R5).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Handle {
    /// The handle: one ASCII uppercase letter + 1-4 digits, no leading zero
    /// (`D1`, `F3`, `C12`).
    pub handle: String,
    /// The full expansion, e.g. ``"the `parse` domain (3,392 nodes)"``.
    pub expansion: String,
}

impl Handle {
    pub fn new(handle: impl Into<String>, expansion: impl Into<String>) -> Handle {
        Handle {
            handle: handle.into(),
            expansion: expansion.into(),
        }
    }
}

/// Which ADR-0008 rule a violation belongs to. Declaration order is the
/// deterministic tie-break order in reports.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum RuleId {
    /// Standalone sentences: no pronouns, no deixis.
    R1Standalone,
    /// One fact per sentence: conjunction + predicate budget, no semicolons.
    R2OneFact,
    /// Handle discipline: glossary-introduced, deterministic grammar.
    R3Handles,
    /// Numbers carry denominators or units.
    R4Numbers,
    /// Deterministic ordering: dense glossary numbering, define-before-reference,
    /// domain-major body order.
    R5Ordering,
    /// Facts only: no quality adjectives, hedges, or imperatives.
    R6FactsOnly,
    /// Vocabulary closure: every plain word comes from the registered vocabulary.
    R7Vocabulary,
    /// Length budget per sentence.
    R8Length,
    /// Encoding and shape safety: single-line UTF-8, no bidi/zero-width,
    /// balanced backticks.
    R9Encoding,
}

impl RuleId {
    /// Short rule code, stable across releases (`"R1"` .. `"R9"`).
    pub fn code(self) -> &'static str {
        match self {
            RuleId::R1Standalone => "R1",
            RuleId::R2OneFact => "R2",
            RuleId::R3Handles => "R3",
            RuleId::R4Numbers => "R4",
            RuleId::R5Ordering => "R5",
            RuleId::R6FactsOnly => "R6",
            RuleId::R7Vocabulary => "R7",
            RuleId::R8Length => "R8",
            RuleId::R9Encoding => "R9",
        }
    }

    /// Human-readable rule title.
    pub fn title(self) -> &'static str {
        match self {
            RuleId::R1Standalone => "standalone sentences",
            RuleId::R2OneFact => "one fact per sentence",
            RuleId::R3Handles => "handle discipline",
            RuleId::R4Numbers => "numbers carry denominators or units",
            RuleId::R5Ordering => "deterministic ordering",
            RuleId::R6FactsOnly => "facts only",
            RuleId::R7Vocabulary => "vocabulary closure",
            RuleId::R8Length => "length budget",
            RuleId::R9Encoding => "encoding and shape safety",
        }
    }
}

/// Byte span within one sentence (`start..end`). Empty (`0..0`) for findings
/// that have no meaningful in-sentence location.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

/// One conformance finding: which rule fired, where, what happened, and how
/// to fix it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Violation {
    pub rule: RuleId,
    /// Index into the `sentences` slice, or [`GLOSSARY_SENTENCE`].
    pub sentence: usize,
    /// Byte span within that sentence.
    pub span: Span,
    pub message: String,
    pub hint: String,
}

impl Violation {
    /// Deterministic JSON shape (sorted keys), matching the finding
    /// discipline of `arch-verify`.
    pub fn to_json(&self) -> Json {
        Json::obj([
            ("rule", Json::str(self.rule.code())),
            ("title", Json::str(self.rule.title())),
            (
                "sentence",
                if self.sentence == GLOSSARY_SENTENCE {
                    Json::str("glossary")
                } else {
                    Json::from(self.sentence)
                },
            ),
            ("start", Json::from(self.span.start)),
            ("end", Json::from(self.span.end)),
            ("message", Json::str(&self.message)),
            ("hint", Json::str(&self.hint)),
        ])
    }
}

/// The declared ordering key for the R5 body-order check.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum OrderingKey {
    /// Body sentences that lead with a handle must be non-decreasing per
    /// handle prefix (all `D1` facts before `D2` facts). The default.
    #[default]
    DomainMajor,
    /// Disable the body-order check. Glossary checks (dense numbering,
    /// declaration-order prelude, define-before-reference) still run.
    None,
}

// ---------------------------------------------------------------------------
// Registered vocabulary (R7) and rule lexicons
// ---------------------------------------------------------------------------

/// Function words and factual adjectives of the template scaffold.
const SCAFFOLD: &[&str] = &[
    "a",
    "across",
    "all",
    "an",
    "and",
    "are",
    "as",
    "at",
    "between",
    "both",
    "by",
    "dead",
    "deepest",
    "direct",
    "each",
    "empty",
    "equal",
    "every",
    "external",
    "fewer",
    "first",
    "for",
    "from",
    "greater",
    "has",
    "have",
    "highest",
    "in",
    "indirect",
    "internal",
    "into",
    "is",
    "largest",
    "last",
    "least",
    "less",
    "local",
    "longest",
    "lowest",
    "means",
    "more",
    "most",
    "no",
    "none",
    "not",
    "of",
    "on",
    "one",
    "only",
    "or",
    "over",
    "per",
    "private",
    "public",
    "resolved",
    "shortest",
    "single",
    "smallest",
    "static",
    "than",
    "that",
    "the",
    "three",
    "through",
    "to",
    "top",
    "transitive",
    "two",
    "under",
    "unique",
    "unresolved",
    "unused",
    "via",
    "when",
    "where",
    "which",
    "whose",
    "with",
    "within",
    "without",
    "zero",
];

/// Registered predicate verbs, present tense, active voice. A verb directly
/// following a subject (handle, name, or identifier) counts against the R2
/// predicate budget.
const VERBS: &[&str] = &[
    "assign",
    "assigns",
    "belong",
    "belongs",
    "call",
    "calls",
    "cluster",
    "clusters",
    "contain",
    "contains",
    "declare",
    "declares",
    "define",
    "defines",
    "depend",
    "depends",
    "emit",
    "emits",
    "exceed",
    "exceeds",
    "export",
    "exports",
    "expose",
    "exposes",
    "extend",
    "extends",
    "group",
    "groups",
    "hold",
    "holds",
    "implement",
    "implements",
    "import",
    "imports",
    "include",
    "includes",
    "introduce",
    "introduces",
    "link",
    "links",
    "match",
    "matches",
    "omit",
    "omits",
    "override",
    "overrides",
    "own",
    "owns",
    "place",
    "places",
    "provide",
    "provides",
    "reach",
    "reaches",
    "read",
    "reads",
    "reference",
    "references",
    "require",
    "requires",
    "resolve",
    "resolves",
    "return",
    "returns",
    "span",
    "spans",
    "target",
    "targets",
    "total",
    "totals",
    "touch",
    "touches",
    "use",
    "uses",
    "write",
    "writes",
];

/// Unit nouns that anchor a number when they directly follow it (R4).
const UNIT_WORDS: &[&str] = &[
    "archetype",
    "archetypes",
    "argument",
    "arguments",
    "branch",
    "branches",
    "byte",
    "bytes",
    "call",
    "callee",
    "callees",
    "caller",
    "callers",
    "calls",
    "case",
    "cases",
    "char",
    "character",
    "characters",
    "chars",
    "class",
    "classes",
    "cluster",
    "clusters",
    "commit",
    "commits",
    "constant",
    "constants",
    "cycle",
    "cycles",
    "declaration",
    "declarations",
    "definition",
    "definitions",
    "dependencies",
    "dependency",
    "dependent",
    "dependents",
    "directories",
    "directory",
    "domain",
    "domains",
    "edge",
    "edges",
    "entries",
    "entry",
    "enum",
    "enums",
    "error",
    "errors",
    "export",
    "exports",
    "fact",
    "facts",
    "field",
    "fields",
    "file",
    "files",
    "function",
    "functions",
    "graph",
    "graphs",
    "group",
    "groups",
    "handle",
    "handles",
    "hop",
    "hops",
    "identifier",
    "identifiers",
    "import",
    "imports",
    "instance",
    "instances",
    "interface",
    "interfaces",
    "keyword",
    "keywords",
    "language",
    "languages",
    "layer",
    "layers",
    "leaf",
    "leaves",
    "level",
    "levels",
    "line",
    "lines",
    "member",
    "members",
    "method",
    "methods",
    "metric",
    "metrics",
    "module",
    "modules",
    "name",
    "names",
    "node",
    "nodes",
    "number",
    "numbers",
    "occurrence",
    "occurrences",
    "package",
    "packages",
    "parameter",
    "parameters",
    "path",
    "paths",
    "percent",
    "point",
    "points",
    "prefix",
    "prefixes",
    "reference",
    "references",
    "repositories",
    "repository",
    "root",
    "roots",
    "rule",
    "rules",
    "scope",
    "scopes",
    "sentence",
    "sentences",
    "signature",
    "signatures",
    "site",
    "sites",
    "source",
    "sources",
    "span",
    "spans",
    "statement",
    "statements",
    "struct",
    "structs",
    "subdomain",
    "subdomains",
    "symbol",
    "symbols",
    "target",
    "targets",
    "test",
    "tests",
    "time",
    "times",
    "token",
    "tokens",
    "trait",
    "traits",
    "type",
    "types",
    "unit",
    "units",
    "value",
    "values",
    "variable",
    "variables",
    "violation",
    "violations",
    "warning",
    "warnings",
    "word",
    "words",
];

/// Metric/label words that anchor a number when they directly precede it (R4).
const NUMBER_LEADERS: &[&str] = &[
    "budget",
    "code",
    "column",
    "count",
    "coverage",
    "depth",
    "exit",
    "f1-score",
    "fan-in",
    "fan-out",
    "id",
    "index",
    "level",
    "line",
    "lines",
    "of",
    "page",
    "port",
    "precision",
    "priority",
    "rank",
    "recall",
    "row",
    "score",
    "size",
    "status",
    "threshold",
    "total",
    "version",
    "weight",
];

/// Words that anchor a numeric range (`10-25`) when they directly precede it.
const RANGE_LEADERS: &[&str] = &[
    "bytes", "chars", "columns", "line", "lines", "rows", "span", "spans",
];

/// R1: pronouns and deictic words that point outside the sentence.
const PRONOUNS_AND_DEIXIS: &[&str] = &[
    "above",
    "aforementioned",
    "below",
    "earlier",
    "follows",
    "following",
    "former",
    "he",
    "her",
    "hers",
    "here",
    "him",
    "his",
    "i",
    "it",
    "its",
    "itself",
    "later",
    "latter",
    "me",
    "mine",
    "my",
    "previously",
    "she",
    "their",
    "theirs",
    "them",
    "themselves",
    "there",
    "these",
    "they",
    "this",
    "those",
    "us",
    "we",
    "you",
    "your",
    "yours",
];

/// R2: words that join or qualify whole facts (forbidden outright).
const FACT_JOINERS: &[&str] = &[
    "additionally",
    "also",
    "although",
    "because",
    "besides",
    "but",
    "furthermore",
    "hence",
    "however",
    "meanwhile",
    "moreover",
    "plus",
    "since",
    "so",
    "then",
    "therefore",
    "though",
    "thus",
    "whereas",
    "while",
];

/// R6: adjectives of quality and vague magnitude (unfalsifiable opinions).
const QUALITY_WORDS: &[&str] = &[
    "bad",
    "beautiful",
    "beautifully",
    "big",
    "clean",
    "cleanly",
    "clever",
    "cleverly",
    "elegant",
    "elegantly",
    "excellent",
    "extremely",
    "fairly",
    "good",
    "graceful",
    "gracefully",
    "great",
    "huge",
    "importantly",
    "impressive",
    "impressively",
    "interestingly",
    "large",
    "massive",
    "neat",
    "neatly",
    "nice",
    "nicely",
    "notably",
    "poor",
    "poorly",
    "powerful",
    "quite",
    "rather",
    "remarkably",
    "robust",
    "significant",
    "significantly",
    "simple",
    "simply",
    "small",
    "surprisingly",
    "terrible",
    "tiny",
    "unfortunately",
    "very",
];

/// R6: hedges, modals, and vague quantifiers (facts become non-facts).
const HEDGES: &[&str] = &[
    "about",
    "almost",
    "apparently",
    "appear",
    "appears",
    "approximately",
    "arguably",
    "around",
    "basically",
    "can",
    "cannot",
    "could",
    "essentially",
    "few",
    "generally",
    "likely",
    "many",
    "may",
    "maybe",
    "might",
    "must",
    "nearly",
    "numerous",
    "often",
    "perhaps",
    "possibly",
    "presumably",
    "probably",
    "roughly",
    "seem",
    "seemingly",
    "seems",
    "several",
    "should",
    "some",
    "sometimes",
    "typically",
    "unlikely",
    "usually",
    "various",
    "would",
];

/// R6: imperative openers — forbidden as the first token of a sentence only
/// (mid-sentence, words like `use` are ordinary predicate verbs).
const IMPERATIVE_OPENERS: &[&str] = &[
    "assume", "avoid", "beware", "check", "consider", "ensure", "imagine", "note", "notice",
    "observe", "recall", "remember", "see", "suppose", "try",
];

/// Membership in the registered vocabulary (R7).
fn in_vocabulary(word: &str) -> bool {
    SCAFFOLD.contains(&word)
        || VERBS.contains(&word)
        || UNIT_WORDS.contains(&word)
        || NUMBER_LEADERS.contains(&word)
        || RANGE_LEADERS.contains(&word)
}

/// The full registered vocabulary, sorted and deduplicated. This is the
/// enumerable scaffold language of ADR-0008 R7: every plain lowercase word a
/// conforming sentence may contain.
pub fn vocabulary() -> Vec<&'static str> {
    let mut all: Vec<&'static str> = SCAFFOLD
        .iter()
        .chain(VERBS)
        .chain(UNIT_WORDS)
        .chain(NUMBER_LEADERS)
        .chain(RANGE_LEADERS)
        .copied()
        .collect();
    all.sort_unstable();
    all.dedup();
    all
}

// ---------------------------------------------------------------------------
// Tokenizer
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    /// Plain lowercase word (subject to lexicons and vocabulary closure).
    Word,
    /// Capitalized proper name of a code entity (`Ordering`).
    Name,
    /// Code identifier, path, backtick span, or acronym — exempt from
    /// lexical rules.
    Code,
    /// Glossary handle (`D1`).
    Handle,
    /// Number (`365`, `18,155`, `0.906`, `45%`).
    Number,
    /// Numeric range (`481-488`).
    Range,
    /// Version-like dotted number (`1.2.3`) — self-anchoring, exempt.
    Version,
}

#[derive(Clone, Debug)]
struct Tok<'a> {
    text: &'a str,
    start: usize,
    end: usize,
    kind: Kind,
    /// The token carried a trailing `%` (self-anchoring for R4).
    percented: bool,
}

fn is_word_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// One ASCII uppercase letter + 1-4 digits, no leading zero unless the
/// number is a single digit (`D1`, `F3`, `C12`; not `D01`, not `SHA1`).
fn is_handle_token(t: &str) -> bool {
    let b = t.as_bytes();
    if b.len() < 2 || b.len() > 5 {
        return false;
    }
    if !b[0].is_ascii_uppercase() || !b[1..].iter().all(u8::is_ascii_digit) {
        return false;
    }
    b.len() == 2 || b[1] != b'0'
}

fn classify(raw: &str) -> Kind {
    let text = raw.strip_suffix('%').unwrap_or(raw);
    if is_handle_token(text) {
        return Kind::Handle;
    }
    let has_alpha = text.chars().any(char::is_alphabetic);
    let has_digit = text.chars().any(|c| c.is_ascii_digit());
    if has_digit && !has_alpha {
        if text.matches('.').count() >= 2 {
            return Kind::Version;
        }
        if text.contains('-') {
            return Kind::Range;
        }
        return Kind::Number;
    }
    if text.contains('_')
        || text.contains('/')
        || text.contains(':')
        || text.contains('#')
        || text.contains('.')
        || (has_digit && has_alpha)
    {
        return Kind::Code;
    }
    if text.contains('-') {
        // Hyphenated: a plain word only when every segment is lowercase
        // alphabetic (`fan-in`); anything else is code-shaped.
        let plain = text.split('-').all(|seg| {
            !seg.is_empty() && seg.chars().all(|c| c.is_alphabetic() && c.is_lowercase())
        });
        return if plain { Kind::Word } else { Kind::Code };
    }
    // Pure alphabetic.
    let first_upper = text.chars().next().is_some_and(char::is_uppercase);
    let any_lower = text.chars().any(char::is_lowercase);
    let rest_has_upper = text.chars().skip(1).any(char::is_uppercase);
    if first_upper && !any_lower && text.chars().count() >= 2 {
        return Kind::Code; // acronym (UTF, IT-the-department)
    }
    if rest_has_upper {
        return Kind::Code; // CamelCase / camelCase
    }
    if first_upper {
        return Kind::Name;
    }
    Kind::Word
}

/// Split a sentence into tokens with byte spans. Backtick spans become one
/// `Code` token; `/ . # -` join word characters (paths, ranges, hyphenated
/// words); `::` joins identifiers; `,` joins digits (`18,155`); a trailing
/// `%` is absorbed after a digit.
fn tokenize(s: &str) -> Vec<Tok<'_>> {
    let chars: Vec<(usize, char)> = s.char_indices().collect();
    let n = chars.len();
    let mut toks = Vec::new();
    let mut i = 0;
    while i < n {
        let (bi, c) = chars[i];
        if c == '`' {
            let mut j = i + 1;
            while j < n && chars[j].1 != '`' {
                j += 1;
            }
            let (end_byte, next) = if j < n {
                (chars[j].0 + chars[j].1.len_utf8(), j + 1)
            } else {
                (s.len(), n)
            };
            toks.push(Tok {
                text: &s[bi..end_byte],
                start: bi,
                end: end_byte,
                kind: Kind::Code,
                percented: false,
            });
            i = next;
            continue;
        }
        if !is_word_char(c) {
            i += 1;
            continue;
        }
        let start_char = i;
        let mut j = i;
        loop {
            while j < n && is_word_char(chars[j].1) {
                j += 1;
            }
            if j >= n {
                break;
            }
            let cc = chars[j].1;
            let joins = match cc {
                '/' | '.' | '#' | '-' => j + 1 < n && is_word_char(chars[j + 1].1),
                ':' => j + 2 < n && chars[j + 1].1 == ':' && is_word_char(chars[j + 2].1),
                ',' => {
                    chars[j - 1].1.is_ascii_digit() && j + 1 < n && chars[j + 1].1.is_ascii_digit()
                }
                _ => false,
            };
            if !joins {
                break;
            }
            j += if cc == ':' { 2 } else { 1 };
        }
        let mut percented = false;
        if j < n && chars[j].1 == '%' && chars[j - 1].1.is_ascii_digit() {
            percented = true;
            j += 1;
        }
        let end_byte = if j < n { chars[j].0 } else { s.len() };
        let text = &s[chars[start_char].0..end_byte];
        toks.push(Tok {
            text,
            start: bi,
            end: end_byte,
            kind: classify(text),
            percented,
        });
        i = j;
    }
    toks
}

// ---------------------------------------------------------------------------
// The checker
// ---------------------------------------------------------------------------

/// Check `sentences` against ADR-0008 with the default ordering key
/// ([`OrderingKey::DomainMajor`]). `glossary` is the declared handle prelude
/// in assignment order. Returns all violations, deterministically sorted by
/// (sentence, span, rule, message).
pub fn check(sentences: &[&str], glossary: &[Handle]) -> Vec<Violation> {
    check_with(sentences, glossary, OrderingKey::default())
}

/// [`check`] with an explicit R5 body-ordering key.
pub fn check_with(
    sentences: &[&str],
    glossary: &[Handle],
    ordering: OrderingKey,
) -> Vec<Violation> {
    let mut out: Vec<Violation> = Vec::new();
    let declared = check_glossary(glossary, &mut out);

    let toks: Vec<Vec<Tok>> = sentences.iter().map(|s| tokenize(s)).collect();

    // In-stream glossary definition lines: handle -> sentence index.
    let mut intro: BTreeMap<&str, usize> = BTreeMap::new();
    for (i, s) in sentences.iter().enumerate() {
        if let Some(h) = glossary_def(s, &toks[i]) {
            intro.entry(h).or_insert(i);
        }
    }

    // R5: in-stream glossary lines must appear in declaration order.
    let mut prev_intro: Option<(usize, &str)> = None;
    for h in glossary {
        let Some(&i) = intro.get(h.handle.as_str()) else {
            continue;
        };
        if let Some((pi, ph)) = prev_intro {
            if i < pi {
                let t0 = &toks[i][0];
                out.push(Violation {
                    rule: RuleId::R5Ordering,
                    sentence: i,
                    span: Span {
                        start: t0.start,
                        end: t0.end,
                    },
                    message: format!(
                        "glossary line for {} appears before the glossary line for {}, \
                         but {} is declared first",
                        h.handle, ph, ph
                    ),
                    hint: "emit glossary lines in declaration order (assignment order = value ranking)"
                        .to_string(),
                });
            }
        }
        prev_intro = Some((i, h.handle.as_str()));
    }

    // Per-sentence checks + R5 body order.
    let mut lead: BTreeMap<char, (u32, String)> = BTreeMap::new();
    for (i, s) in sentences.iter().enumerate() {
        let ts = &toks[i];
        check_wellformed(i, s, &mut out);
        check_tokens(i, ts, &declared, &intro, &mut out);

        if ordering == OrderingKey::DomainMajor && glossary_def(s, ts).is_none() {
            if let Some(t0) = ts.first() {
                if t0.kind == Kind::Handle {
                    let prefix = t0.text.chars().next().unwrap_or('?');
                    let num: u32 = t0.text[1..].parse().unwrap_or(0);
                    if let Some((last, last_h)) = lead.get(&prefix) {
                        if num < *last {
                            out.push(Violation {
                                rule: RuleId::R5Ordering,
                                sentence: i,
                                span: Span {
                                    start: t0.start,
                                    end: t0.end,
                                },
                                message: format!(
                                    "sentence subject {} appears after {}: domain-major order \
                                     requires non-decreasing handles per prefix",
                                    t0.text, last_h
                                ),
                                hint: "group sentences by handle in assignment order (all D1 \
                                       facts before D2 facts)"
                                    .to_string(),
                            });
                        }
                    }
                    let advance = lead.get(&prefix).is_none_or(|(l, _)| num >= *l);
                    if advance {
                        lead.insert(prefix, (num, t0.text.to_string()));
                    }
                }
            }
        }
    }

    out.sort_by(|a, b| {
        (a.sentence, a.span.start, a.span.end, a.rule, &a.message).cmp(&(
            b.sentence,
            b.span.start,
            b.span.end,
            b.rule,
            &b.message,
        ))
    });
    out.dedup();
    out
}

/// Structural checks on the declared glossary (R3 grammar, R5 dense
/// numbering). Returns the set of validly declared handles.
fn check_glossary<'g>(
    glossary: &'g [Handle],
    out: &mut Vec<Violation>,
) -> BTreeMap<&'g str, usize> {
    let mut declared: BTreeMap<&'g str, usize> = BTreeMap::new();
    let mut next_num: BTreeMap<char, u32> = BTreeMap::new();
    for (gi, h) in glossary.iter().enumerate() {
        if !is_handle_token(&h.handle) {
            out.push(glossary_violation(
                RuleId::R3Handles,
                format!(
                    "declared handle '{}' does not match the handle grammar \
                     (one ASCII uppercase letter + 1-4 digits, no leading zero)",
                    h.handle
                ),
                "rename the handle, e.g. D1 or F3",
            ));
            continue;
        }
        if declared.insert(h.handle.as_str(), gi).is_some() {
            out.push(glossary_violation(
                RuleId::R3Handles,
                format!("handle {} is declared more than once", h.handle),
                "each handle gets exactly one glossary entry",
            ));
            continue;
        }
        if h.expansion.trim().is_empty() {
            out.push(glossary_violation(
                RuleId::R3Handles,
                format!("handle {} has an empty expansion", h.handle),
                "every glossary entry names its referent in full",
            ));
        }
        let prefix = h.handle.chars().next().unwrap_or('?');
        let num: u32 = h.handle[1..].parse().unwrap_or(0);
        let expect = next_num.entry(prefix).or_insert(1);
        if num != *expect {
            out.push(glossary_violation(
                RuleId::R5Ordering,
                format!(
                    "glossary numbering for prefix {}: expected {}{}, found {}",
                    prefix, prefix, expect, h.handle
                ),
                "assign handles densely in value-ranking order (D1, D2, D3, ...)",
            ));
        }
        *expect = num + 1;
    }
    declared
}

fn glossary_violation(rule: RuleId, message: String, hint: &str) -> Violation {
    Violation {
        rule,
        sentence: GLOSSARY_SENTENCE,
        span: Span { start: 0, end: 0 },
        message,
        hint: hint.to_string(),
    }
}

/// Recognize an in-stream glossary definition line: a handle as the first
/// token, followed by `=`.
fn glossary_def<'a>(s: &str, ts: &[Tok<'a>]) -> Option<&'a str> {
    let t0 = ts.first()?;
    if t0.kind != Kind::Handle || !s[..t0.start].trim().is_empty() {
        return None;
    }
    let after_end = ts.get(1).map_or(s.len(), |t| t.start);
    if s[t0.end..after_end].trim_start().starts_with('=') {
        Some(t0.text)
    } else {
        None
    }
}

/// R9 (shape/encoding), R8 (length), and the raw-text part of R2 (semicolons
/// outside code spans).
fn check_wellformed(i: usize, s: &str, out: &mut Vec<Violation>) {
    if s.trim().is_empty() {
        out.push(Violation {
            rule: RuleId::R9Encoding,
            sentence: i,
            span: Span {
                start: 0,
                end: s.len(),
            },
            message: "empty sentence".to_string(),
            hint: "every sentence states one fact; drop empty lines".to_string(),
        });
        return;
    }
    for (bi, c) in s.char_indices() {
        if c.is_control() {
            out.push(Violation {
                rule: RuleId::R9Encoding,
                sentence: i,
                span: Span {
                    start: bi,
                    end: bi + c.len_utf8(),
                },
                message: format!("control character U+{:04X}", c as u32),
                hint: "sentences are single-line plain text: no tabs, newlines, or control codes"
                    .to_string(),
            });
        } else if is_invisible_or_bidi(c) {
            out.push(Violation {
                rule: RuleId::R9Encoding,
                sentence: i,
                span: Span {
                    start: bi,
                    end: bi + c.len_utf8(),
                },
                message: format!("invisible or bidi control character U+{:04X}", c as u32),
                hint: "strip zero-width and bidirectional control codepoints (injection surface)"
                    .to_string(),
            });
        }
    }
    if s.matches('`').count() % 2 == 1 {
        let pos = s.rfind('`').unwrap_or(0);
        out.push(Violation {
            rule: RuleId::R9Encoding,
            sentence: i,
            span: Span {
                start: pos,
                end: pos + 1,
            },
            message: "unpaired backtick".to_string(),
            hint: "close the code span; backticks delimit code and must balance".to_string(),
        });
    }
    let n_chars = s.chars().count();
    if n_chars > MAX_SENTENCE_CHARS {
        out.push(Violation {
            rule: RuleId::R8Length,
            sentence: i,
            span: Span {
                start: 0,
                end: s.len(),
            },
            message: format!(
                "sentence is {} chars (budget {})",
                n_chars, MAX_SENTENCE_CHARS
            ),
            hint: "split into more sentences or introduce glossary handles for long names"
                .to_string(),
        });
    }
    let mut in_code = false;
    for (bi, c) in s.char_indices() {
        if c == '`' {
            in_code = !in_code;
        } else if c == ';' && !in_code {
            out.push(Violation {
                rule: RuleId::R2OneFact,
                sentence: i,
                span: Span {
                    start: bi,
                    end: bi + 1,
                },
                message: "semicolon joins two facts".to_string(),
                hint: "one fact per sentence: split at the semicolon".to_string(),
            });
        }
    }
}

fn is_invisible_or_bidi(c: char) -> bool {
    matches!(
        c,
        '\u{200B}'..='\u{200F}' | '\u{202A}'..='\u{202E}' | '\u{2066}'..='\u{2069}' | '\u{FEFF}'
    )
}

/// Token-level rules: R1, R2 (conjunction + predicate budget), R3, R4, R6, R7.
fn check_tokens(
    i: usize,
    ts: &[Tok],
    declared: &BTreeMap<&str, usize>,
    intro: &BTreeMap<&str, usize>,
    out: &mut Vec<Violation>,
) {
    let mut joins = 0u32;
    let mut predicates = 0u32;
    for (ti, t) in ts.iter().enumerate() {
        let span = Span {
            start: t.start,
            end: t.end,
        };
        match t.kind {
            Kind::Code | Kind::Version => {}
            Kind::Handle => {
                if !declared.contains_key(t.text) {
                    out.push(Violation {
                        rule: RuleId::R3Handles,
                        sentence: i,
                        span,
                        message: format!("handle {} is not declared in the glossary", t.text),
                        hint: format!(
                            "add a glossary entry ('{} = <full name>') before use, or write the \
                             full name",
                            t.text
                        ),
                    });
                } else if let Some(&g) = intro.get(t.text) {
                    if i < g {
                        out.push(Violation {
                            rule: RuleId::R3Handles,
                            sentence: i,
                            span,
                            message: format!(
                                "handle {} is used before its glossary line (sentence {})",
                                t.text, g
                            ),
                            hint: "move the glossary line ahead of the first use".to_string(),
                        });
                    }
                }
            }
            Kind::Number => {
                if !number_justified(ts, ti, t.percented) {
                    out.push(Violation {
                        rule: RuleId::R4Numbers,
                        sentence: i,
                        span,
                        message: format!("bare number {}: no unit or denominator", t.text),
                        hint: format!(
                            "attach a unit ('{} files'), a denominator ('{} of N nodes'), or \
                             backtick it as a code literal",
                            t.text, t.text
                        ),
                    });
                }
            }
            Kind::Range => {
                if !range_justified(ts, ti) {
                    out.push(Violation {
                        rule: RuleId::R4Numbers,
                        sentence: i,
                        span,
                        message: format!("bare range {}: no span anchor", t.text),
                        hint: format!("anchor the range ('lines {}')", t.text),
                    });
                }
            }
            Kind::Word | Kind::Name => {
                let lower = t.text.to_lowercase();
                let lc = lower.as_str();
                if PRONOUNS_AND_DEIXIS.contains(&lc) {
                    out.push(Violation {
                        rule: RuleId::R1Standalone,
                        sentence: i,
                        span,
                        message: format!("pronoun or deictic word '{}'", t.text),
                        hint: "name the referent in full or by glossary handle; every sentence \
                               must stand alone"
                            .to_string(),
                    });
                } else if lc == "and" || lc == "or" {
                    joins += 1;
                    if joins > 1 {
                        out.push(Violation {
                            rule: RuleId::R2OneFact,
                            sentence: i,
                            span,
                            message: format!(
                                "conjunction budget exceeded: second '{}' in one sentence",
                                t.text
                            ),
                            hint: "at most one 'and'/'or' joining values; split into two \
                                   sentences"
                                .to_string(),
                        });
                    }
                } else if FACT_JOINERS.contains(&lc) {
                    out.push(Violation {
                        rule: RuleId::R2OneFact,
                        sentence: i,
                        span,
                        message: format!("'{}' joins or qualifies facts", t.text),
                        hint: "one fact per sentence: state each fact in its own sentence"
                            .to_string(),
                    });
                } else if QUALITY_WORDS.contains(&lc) {
                    out.push(Violation {
                        rule: RuleId::R6FactsOnly,
                        sentence: i,
                        span,
                        message: format!("quality or vague-magnitude adjective '{}'", t.text),
                        hint: "state the measured value instead of an opinion".to_string(),
                    });
                } else if HEDGES.contains(&lc) {
                    out.push(Violation {
                        rule: RuleId::R6FactsOnly,
                        sentence: i,
                        span,
                        message: format!("hedge or vague quantifier '{}'", t.text),
                        hint: "state the exact count or omit the claim; hedged facts are \
                               non-facts"
                            .to_string(),
                    });
                } else if ti == 0 && IMPERATIVE_OPENERS.contains(&lc) {
                    out.push(Violation {
                        rule: RuleId::R6FactsOnly,
                        sentence: i,
                        span,
                        message: format!("imperative opener '{}'", t.text),
                        hint: "sentences report facts; they do not address a reader".to_string(),
                    });
                } else {
                    if VERBS.contains(&lc)
                        && ti > 0
                        && matches!(ts[ti - 1].kind, Kind::Handle | Kind::Name | Kind::Code)
                    {
                        predicates += 1;
                        if predicates > 1 {
                            out.push(Violation {
                                rule: RuleId::R2OneFact,
                                sentence: i,
                                span: Span {
                                    start: t.start,
                                    end: t.end,
                                },
                                message: format!("second predicate '{}' in one sentence", t.text),
                                hint: "one fact per sentence: one subject-verb pair; split the \
                                       second fact into its own sentence"
                                    .to_string(),
                            });
                        }
                    }
                    if t.kind == Kind::Word && !in_vocabulary(lc) {
                        out.push(Violation {
                            rule: RuleId::R7Vocabulary,
                            sentence: i,
                            span: Span {
                                start: t.start,
                                end: t.end,
                            },
                            message: format!(
                                "word '{}' is outside the registered vocabulary",
                                t.text
                            ),
                            hint: "register the word in the vocabulary (reviewed edit) or mark \
                                   it as a code identifier with backticks"
                                .to_string(),
                        });
                    }
                }
            }
        }
    }
}

/// R4: a number is anchored by a leader before it (`fan-in 365`, `line 42`,
/// `of 18,155`), a unit or `of` after it (`12 files`, `365 of`), or a
/// trailing percent sign.
fn number_justified(ts: &[Tok], ti: usize, percented: bool) -> bool {
    if percented {
        return true;
    }
    if ti > 0 {
        let p = &ts[ti - 1];
        if matches!(p.kind, Kind::Word | Kind::Name | Kind::Code) {
            let lp = p.text.trim_matches('`').to_lowercase();
            if NUMBER_LEADERS.contains(&lp.as_str()) {
                return true;
            }
        }
    }
    if let Some(nx) = ts.get(ti + 1) {
        if matches!(nx.kind, Kind::Word | Kind::Name) {
            let ln = nx.text.to_lowercase();
            if ln == "of" || UNIT_WORDS.contains(&ln.as_str()) {
                return true;
            }
        }
    }
    false
}

/// R4: a range (`481-488`) is anchored by a span word before it (`lines`) or
/// a unit after it.
fn range_justified(ts: &[Tok], ti: usize) -> bool {
    if ti > 0 {
        let p = &ts[ti - 1];
        if matches!(p.kind, Kind::Word | Kind::Name) {
            let lp = p.text.to_lowercase();
            if RANGE_LEADERS.contains(&lp.as_str()) {
                return true;
            }
        }
    }
    if let Some(nx) = ts.get(ti + 1) {
        if matches!(nx.kind, Kind::Word | Kind::Name) {
            let ln = nx.text.to_lowercase();
            if UNIT_WORDS.contains(&ln.as_str()) {
                return true;
            }
        }
    }
    false
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn gl(pairs: &[(&str, &str)]) -> Vec<Handle> {
        pairs.iter().map(|(h, e)| Handle::new(*h, *e)).collect()
    }

    fn codes(vs: &[Violation]) -> Vec<&'static str> {
        vs.iter().map(|v| v.rule.code()).collect()
    }

    fn has_rule(vs: &[Violation], code: &str) -> bool {
        vs.iter().any(|v| v.rule.code() == code)
    }

    fn std_glossary() -> Vec<Handle> {
        gl(&[
            ("D1", "the `parse` domain (3,392 nodes)"),
            ("D2", "the `lang` domain (1,596 nodes)"),
            (
                "F1",
                "the function `crate::arch::verify` (src/arch.rs, line 481)",
            ),
        ])
    }

    // -- the golden positive: a full conforming document ---------------------

    #[test]
    fn clean_document_passes_every_rule() {
        let glossary = std_glossary();
        let sentences = [
            "D1 = the `parse` domain (3,392 nodes)",
            "D2 = the `lang` domain (1,596 nodes)",
            "F1 = the function `crate::arch::verify` (src/arch.rs, line 481)",
            "D1 contains 3,392 nodes of 7,340 nodes.",
            "D1 imports 12 files from D2.",
            "D2 defines 1,596 nodes.",
            "F1 has fan-in 9 of 18,155 edges.",
            "F1 spans lines 481-488.",
        ];
        let vs = check(&sentences, &glossary);
        assert!(vs.is_empty(), "expected no violations, got: {vs:?}");
    }

    // -- R1: standalone sentences --------------------------------------------

    #[test]
    fn r1_flags_pronouns_and_deixis() {
        let vs = check(&["It imports 3 files from D1."], &std_glossary());
        assert!(has_rule(&vs, "R1"), "sentence-initial 'It': {vs:?}");

        let vs = check(&["D1 imports the former."], &std_glossary());
        assert!(has_rule(&vs, "R1"), "'former' is deixis: {vs:?}");

        let vs = check(&["D1 exports the following types."], &std_glossary());
        assert!(has_rule(&vs, "R1"), "'following' is forward deixis: {vs:?}");
    }

    #[test]
    fn r1_spares_identifiers_paths_and_acronyms_containing_pronouns() {
        let glossary = std_glossary();
        let vs = check(
            &["The module src/it/mod.rs contains 3 functions."],
            &glossary,
        );
        assert!(!has_rule(&vs, "R1"), "'it' inside a path is code: {vs:?}");

        let vs = check(
            &["The function `commit_it` has fan-in 2 of 9 nodes."],
            &glossary,
        );
        assert!(
            !has_rule(&vs, "R1"),
            "'it' inside a backticked identifier: {vs:?}"
        );

        let vs = check(&["The IT department owns 3 repositories."], &glossary);
        assert!(
            !has_rule(&vs, "R1"),
            "all-caps acronym IT is not a pronoun: {vs:?}"
        );
    }

    // -- R2: one fact per sentence -------------------------------------------

    #[test]
    fn r2_allows_one_and_joining_values() {
        let vs = check(&["D1 imports 12 files and 3 types."], &std_glossary());
        assert!(
            vs.is_empty(),
            "one 'and' joining values is within budget: {vs:?}"
        );
    }

    #[test]
    fn r2_flags_second_conjunction() {
        let vs = check(
            &["D1 imports 12 files and 3 types and 2 constants."],
            &std_glossary(),
        );
        assert!(
            has_rule(&vs, "R2"),
            "second 'and' exceeds the budget: {vs:?}"
        );
    }

    #[test]
    fn r2_flags_two_predicates_fact_joiners_and_semicolons() {
        let g = std_glossary();
        let vs = check(&["D1 imports 12 files and D2 exports 4 files."], &g);
        assert!(
            has_rule(&vs, "R2"),
            "two subject-verb pairs = two facts: {vs:?}"
        );

        let vs = check(&["D1 imports 12 files, however D2 imports none."], &g);
        assert!(has_rule(&vs, "R2"), "'however' joins facts: {vs:?}");

        let vs = check(&["D1 imports 12 files; D2 exports 4 files."], &g);
        assert!(has_rule(&vs, "R2"), "semicolon joins facts: {vs:?}");
    }

    #[test]
    fn r2_spares_and_inside_identifiers_and_code_spans() {
        let g = std_glossary();
        let vs = check(
            &["The file src/ops/and_or.rs defines 2 types and 1 trait."],
            &g,
        );
        assert!(
            !has_rule(&vs, "R2"),
            "'and' inside a path does not count against the budget: {vs:?}"
        );

        let vs = check(
            &["The function `check_and_fix` has fan-out 4 of 20 edges."],
            &g,
        );
        assert!(
            !has_rule(&vs, "R2"),
            "'and' inside backticks is code: {vs:?}"
        );
    }

    // -- R3: handle discipline ------------------------------------------------

    #[test]
    fn r3_flags_undeclared_handle() {
        let vs = check(&["D9 exports 4 types."], &std_glossary());
        assert!(has_rule(&vs, "R3"), "D9 has no glossary entry: {vs:?}");
    }

    #[test]
    fn r3_flags_use_before_glossary_line() {
        let sentences = [
            "D1 = the `parse` domain (3,392 nodes)",
            "D2 contains 1,596 nodes of 7,340 nodes.",
            "D2 = the `lang` domain (1,596 nodes)",
        ];
        let vs = check(&sentences, &std_glossary());
        assert!(
            has_rule(&vs, "R3"),
            "D2 used in sentence 1, introduced in sentence 2: {vs:?}"
        );
    }

    #[test]
    fn r3_flags_bad_declared_handle_grammar_and_duplicates() {
        let vs = check(&[], &gl(&[("SHA1", "a hash"), ("D01", "zero-padded")]));
        assert_eq!(codes(&vs), ["R3", "R3"], "{vs:?}");

        let vs = check(&[], &gl(&[("D1", "the first"), ("D1", "again")]));
        assert!(has_rule(&vs, "R3"), "duplicate declaration: {vs:?}");
    }

    #[test]
    fn r3_allows_declared_handle_after_its_line() {
        let sentences = [
            "D1 = the `parse` domain (3,392 nodes)",
            "D1 contains 3,392 nodes of 7,340 nodes.",
        ];
        let vs = check(&sentences, &std_glossary());
        assert!(vs.is_empty(), "{vs:?}");
    }

    // -- R4: numbers carry denominators or units ------------------------------

    #[test]
    fn r4_flags_bare_numbers_and_bare_ranges() {
        let g = std_glossary();
        let vs = check(&["F1 has fan-in 365."], &g);
        assert!(vs.is_empty(), "metric leader 'fan-in' anchors 365: {vs:?}");

        let vs = check(&["F1 reaches 365."], &g);
        assert!(has_rule(&vs, "R4"), "365 of what? {vs:?}");

        let vs = check(&["F1 reaches 481-488."], &g);
        assert!(
            has_rule(&vs, "R4"),
            "bare range without a span anchor: {vs:?}"
        );
    }

    #[test]
    fn r4_accepts_units_denominators_spans_percents_and_versions() {
        let g = std_glossary();
        let ok = [
            "F1 has fan-in 365 of 18,155 nodes.",
            "D1 contains 12 files.",
            "F1 spans lines 481-488.",
            "The `parse` domain holds 46% of 7,340 nodes.",
            "The package `serde` has version 1.0.219.",
        ];
        for s in ok {
            let vs = check(&[s], &g);
            assert!(!has_rule(&vs, "R4"), "expected no R4 in {s:?}: {vs:?}");
        }
    }

    // -- R5: deterministic ordering --------------------------------------------

    #[test]
    fn r5_flags_glossary_numbering_gap() {
        let vs = check(&[], &gl(&[("D1", "first"), ("D3", "gap")]));
        assert!(
            has_rule(&vs, "R5"),
            "D2 is missing: numbering must be dense: {vs:?}"
        );
    }

    #[test]
    fn r5_flags_glossary_lines_out_of_declaration_order() {
        let sentences = [
            "D2 = the `lang` domain (1,596 nodes)",
            "D1 = the `parse` domain (3,392 nodes)",
        ];
        let vs = check(&sentences, &std_glossary());
        assert!(has_rule(&vs, "R5"), "D2's line precedes D1's: {vs:?}");
    }

    #[test]
    fn r5_flags_domain_revisited_and_respects_ordering_key() {
        let sentences = [
            "D1 = the `parse` domain (3,392 nodes)",
            "D2 = the `lang` domain (1,596 nodes)",
            "D2 defines 1,596 nodes.",
            "D1 contains 3,392 nodes of 7,340 nodes.",
        ];
        let vs = check(&sentences, &std_glossary());
        assert!(has_rule(&vs, "R5"), "D1 subject after D2 subject: {vs:?}");

        let vs = check_with(&sentences, &std_glossary(), OrderingKey::None);
        assert!(
            !has_rule(&vs, "R5"),
            "OrderingKey::None disables the body check: {vs:?}"
        );
    }

    #[test]
    fn r5_allows_domain_major_order_across_prefixes() {
        let sentences = [
            "D1 = the `parse` domain (3,392 nodes)",
            "D2 = the `lang` domain (1,596 nodes)",
            "F1 = the function `crate::arch::verify` (src/arch.rs, line 481)",
            "D1 contains 3,392 nodes of 7,340 nodes.",
            "D2 defines 1,596 nodes.",
            "F1 has fan-in 9 of 18,155 edges.",
        ];
        let vs = check(&sentences, &std_glossary());
        assert!(vs.is_empty(), "{vs:?}");
    }

    // -- R6: facts only ----------------------------------------------------------

    #[test]
    fn r6_flags_quality_adjectives_hedges_and_imperatives() {
        let g = std_glossary();
        let vs = check(&["D1 has a clean structure of 12 files."], &g);
        assert!(has_rule(&vs, "R6"), "'clean' is an opinion: {vs:?}");

        let vs = check(&["D1 probably imports 12 files."], &g);
        assert!(has_rule(&vs, "R6"), "'probably' hedges the fact: {vs:?}");

        let vs = check(&["Note the fan-in 9 of 18,155 edges."], &g);
        assert!(has_rule(&vs, "R6"), "imperative opener 'Note': {vs:?}");
    }

    #[test]
    fn r6_allows_measured_superlatives_and_mid_sentence_use() {
        let g = std_glossary();
        let vs = check(
            &["D1 is the largest domain: 3,392 nodes of 7,340 nodes."],
            &g,
        );
        assert!(
            !has_rule(&vs, "R6"),
            "'largest' over a measured value is a fact: {vs:?}"
        );

        let vs = check(&["D1 files use 3 types from D2."], &g);
        assert!(
            !has_rule(&vs, "R6"),
            "mid-sentence 'use' is a predicate verb: {vs:?}"
        );
    }

    // -- R7: vocabulary closure ---------------------------------------------------

    #[test]
    fn r7_flags_words_outside_the_registered_vocabulary() {
        let vs = check(&["D1 frobnicates the graph."], &std_glossary());
        assert!(
            has_rule(&vs, "R7"),
            "'frobnicates' is not registered: {vs:?}"
        );
    }

    #[test]
    fn r7_exempts_identifiers_names_numbers_and_paths() {
        let vs = check(
            &["The type `OrderService` in src/ordering/service.rs has 4 methods."],
            &std_glossary(),
        );
        assert!(vs.is_empty(), "{vs:?}");
    }

    #[test]
    fn vocabulary_is_enumerable_and_disjoint_from_banned_lexicons() {
        let vocab = vocabulary();
        assert!(
            vocab.windows(2).all(|w| w[0] < w[1]),
            "sorted + deduplicated"
        );
        for banned in [PRONOUNS_AND_DEIXIS, FACT_JOINERS, QUALITY_WORDS, HEDGES] {
            for w in banned {
                assert!(
                    !in_vocabulary(w),
                    "'{w}' is both banned and registered: the language must be unambiguous"
                );
            }
        }
    }

    // -- R8: length budget -----------------------------------------------------------

    #[test]
    fn r8_flags_sentences_over_the_budget() {
        let long = format!("D1 contains {} nodes of 7,340 nodes.", "9".repeat(160));
        let vs = check(&[long.as_str()], &std_glossary());
        assert!(has_rule(&vs, "R8"), "{vs:?}");

        let exact = "x".repeat(MAX_SENTENCE_CHARS);
        let vs = check(&[exact.as_str()], &[]);
        assert!(!has_rule(&vs, "R8"), "exactly at budget passes R8: {vs:?}");
    }

    // -- R9: encoding and shape safety ----------------------------------------------

    #[test]
    fn r9_flags_control_bidi_unpaired_backtick_and_empty() {
        let g = std_glossary();
        let vs = check(&["D1 contains\t12 files."], &g);
        assert!(has_rule(&vs, "R9"), "tab is a control character: {vs:?}");

        let vs = check(&["D1 contains \u{202E}12 files."], &g);
        assert!(
            has_rule(&vs, "R9"),
            "bidi override is an injection surface: {vs:?}"
        );

        let vs = check(&["D1 contains `broken 12 files."], &g);
        assert!(has_rule(&vs, "R9"), "unpaired backtick: {vs:?}");

        let vs = check(&["   "], &g);
        assert!(has_rule(&vs, "R9"), "empty sentence: {vs:?}");
    }

    // -- torture fixture ---------------------------------------------------------------

    #[test]
    fn torture_tricky_sentences_produce_exactly_the_planned_findings() {
        let glossary = gl(&[
            ("D1", "the `parse` domain (3,392 nodes)"),
            (
                "F1",
                "the function `crate::arch::verify` (src/arch.rs, line 481)",
            ),
        ]);
        let sentences = [
            // 0: identifiers containing 'it', paths with 'and' -> clean.
            "The module src/it/handlers_and_hooks.rs contains 3 functions.",
            // 1: range in a span, path -> clean.
            "F1 spans lines 481-488 of src/arch.rs.",
            // 2: percent + thousands separator + denominator -> clean.
            "F1 holds 46% of 18,155 edges.",
            // 3: pronoun + hedge + bare number -> R1, R6, R4.
            "It probably reaches 365.",
            // 4: undeclared handle + fact joiner + second predicate -> R3, R2, R2.
            "D9 exports 4 types, however D1 imports none.",
            // 5: out-of-vocabulary editorializing -> R6, R7 (x2).
            "The `parse` domain elegantly frobnicates the dependency situation.",
        ];
        let vs = check(&sentences, &glossary);
        let got: Vec<(usize, &'static str)> =
            vs.iter().map(|v| (v.sentence, v.rule.code())).collect();
        assert_eq!(
            got,
            vec![
                (3, "R1"), // It
                (3, "R6"), // probably
                (3, "R4"), // 365
                (4, "R3"), // D9
                (4, "R2"), // however
                (4, "R2"), // second predicate 'imports'
                (5, "R6"), // elegantly
                (5, "R7"), // frobnicates
                (5, "R7"), // situation
            ],
            "full findings: {vs:#?}"
        );
        // Sentences 0-2 are the sworn-clean half of the fixture.
        assert!(vs.iter().all(|v| v.sentence >= 3), "{vs:#?}");
    }

    // -- checker determinism -------------------------------------------------------------

    #[test]
    fn checker_is_deterministic() {
        let glossary = std_glossary();
        let sentences = [
            "D2 defines 1,596 nodes.",
            "It probably frobnicates 365 and 12 and 9.",
            "D1 = the `parse` domain (3,392 nodes)",
            "D9 exports 4 types; D1 imports none.",
        ];
        let a = check(&sentences, &glossary);
        let b = check(&sentences, &glossary);
        assert_eq!(a, b, "same input, same violations, same order");
        assert!(!a.is_empty());
        let lines_a: Vec<String> = a.iter().map(|v| v.to_json().to_line()).collect();
        let lines_b: Vec<String> = b.iter().map(|v| v.to_json().to_line()).collect();
        assert_eq!(lines_a, lines_b, "JSON emission is byte-stable");
        // Sorted by (sentence, span.start, span.end, rule, message).
        let mut sorted = a.clone();
        sorted.sort_by(|x, y| {
            (x.sentence, x.span.start, x.span.end, x.rule, &x.message).cmp(&(
                y.sentence,
                y.span.start,
                y.span.end,
                y.rule,
                &y.message,
            ))
        });
        assert_eq!(a, sorted, "output arrives pre-sorted");
    }

    #[test]
    fn violation_spans_point_at_the_offending_bytes() {
        let s = "It imports 12 files.";
        let vs = check(&[s], &std_glossary());
        let v = vs.iter().find(|v| v.rule == RuleId::R1Standalone).unwrap();
        assert_eq!(&s[v.span.start..v.span.end], "It");
    }
}
