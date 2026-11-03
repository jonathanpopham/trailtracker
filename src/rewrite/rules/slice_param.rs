//! Rule 6: `slice-param` v1 — generalize a borrowed owning parameter to the
//! borrowed view it is only ever used as: `&Vec<T>` → `&[T]` and
//! `&String` → `&str`.
//!
//! The rewrite is strictly call-site compatible: every expression that
//! coerced to `&Vec<T>` / `&String` at a direct call site coerces to
//! `&[T]` / `&str` at the same site (deref coercion, `Vec<T>: Deref<Target
//! = [T]>`, `String: Deref<Target = str>`), and the new type additionally
//! accepts callers that only hold a slice — the signature becomes strictly
//! more general.
//!
//! HONESTLY SCOPED (v1). Recognized parameter shapes (silent otherwise):
//!
//! - `name: &Vec<T>` / `name: &'a Vec<T>`   → `name: &[T]` / `name: &'a [T]`
//! - `name: &String` / `name: &'a String`   → `name: &str` / `name: &'a str`
//!
//! `&mut` borrows are NOT candidates (`&mut Vec<T>` grants growth/shrink
//! rights `&mut [T]` does not), nor are by-value params, path-qualified
//! `std::vec::Vec`, or pattern parameters.
//!
//! A recognized parameter is REWRITTEN only when every occurrence of its
//! name in the function is one of the licensed use forms — anything else is
//! a machine-readable rejection, never a guess:
//!
//! - `name.method(…)` with `method` in the slice-safe (resp. str-safe)
//!   vocabulary: methods that resolve on `&Vec<T>` / `&String` THROUGH
//!   `Deref` to the very same `[T]` / `str` implementation the rewritten
//!   parameter calls directly — identical observable function before and
//!   after. A method outside the vocabulary (e.g. `capacity`, `clone`,
//!   `to_owned`) is `param_method_not_slice_compatible`.
//! - `name[…]` indexing (`Index` forwards through the same deref);
//! - `for PAT in name` iteration (`&Vec<T>` and `&[T]` both iterate `&T`) —
//!   `Vec` parameters only.
//!
//! Every other occurrence — passing `name` as an argument (the callee
//! expects the OLD type), `&name`, macro arguments, rebinding, returning —
//! is `param_use_not_slice_compatible`.
//!
//! One file-level guard: if the enclosing function's NAME occurs anywhere in
//! the file other than its definition or a direct call `name(…)`, the
//! function may be taken as a first-class value (fn-pointer/closure
//! position), where a parameter-type change is not coercion-compatible —
//! every candidate parameter of that function is refused
//! (`function_used_as_value`).

use crate::core::cst::{Node, Token};
use crate::core::span::ByteSpan;
use crate::ir::cpg::{elems, flat_tokens, Stmt, StmtKind, E};
use crate::ir::ontology::edge;
use crate::lang::rust::lexer::{kind as tk, lex};
use crate::lang::rust::parser::node as cst;
use crate::rewrite::proposal::{ProposedEdit, Rejection};
use crate::rewrite::rules::{
    edge_prop, line_of, text_of, FileCpg, FnUnit, Rule, RuleOptions, RuleOutcome,
};

pub struct SliceParam;

impl Rule for SliceParam {
    fn id(&self) -> &'static str {
        "slice-param"
    }

    fn version(&self) -> &'static str {
        "1"
    }

    fn summary(&self) -> &'static str {
        "Generalize `&Vec<T>`/`&String` parameters to `&[T]`/`&str` when every use in \
         the body is a slice/str-safe operation: strictly more general for callers \
         (deref coercion covers every existing direct call site)."
    }

    fn shapes(&self) -> &'static [&'static str] {
        &[
            "fn f(v: &Vec<T>)    => fn f(v: &[T])    (every use of `v` slice-safe: \
             allowlisted method, indexing, or `for … in v`)",
            "fn f(s: &String)    => fn f(s: &str)    (every use of `s` str-safe: \
             allowlisted method or indexing)",
            "fn f(v: &'a Vec<T>) => fn f(v: &'a [T]) (the lifetime is reused verbatim)",
        ]
    }

    fn propose(&self, file: &FileCpg<'_>, _opts: &RuleOptions) -> Result<RuleOutcome, String> {
        let mut out = RuleOutcome::default();
        let src = file.src;
        for f in &file.fns {
            let sites = recognized_param_sites(f, src);
            if sites.is_empty() {
                continue;
            }
            // File-level guard, computed once per function with candidates.
            let value_use = fn_value_use(src, &f.name);
            for site in sites {
                if let Some(off) = value_use {
                    out.rejections.push(Rejection {
                        span: site.span,
                        reason: "function_used_as_value".to_string(),
                        detail: format!(
                            "`{}` is used as a first-class value at line {} (not a direct \
                             call); a fn-pointer/closure position is not coercion-compatible \
                             with the changed parameter type",
                            f.name,
                            line_of(src, off)
                        ),
                    });
                    continue;
                }
                match licensed_uses(f, src, &site) {
                    Ok(use_facts) => out.edits.push(build_edit(file, f, &site, use_facts)),
                    Err((reason, detail)) => out.rejections.push(Rejection {
                        span: site.span,
                        reason: reason.to_string(),
                        detail,
                    }),
                }
            }
        }
        out.edits.sort_by_key(|e| (e.span.start, e.span.end));
        out.rejections.sort_by_key(|r| (r.span.start, r.span.end));
        Ok(out)
    }
}

// ---------------------------------------------------------------------------
// Shape recognizer: which parameters have the recognized type?
// ---------------------------------------------------------------------------

/// Which owning type the parameter borrows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Flavor {
    VecT,
    StringT,
}

impl Flavor {
    fn owned(self) -> &'static str {
        match self {
            Flavor::VecT => "Vec<T>",
            Flavor::StringT => "String",
        }
    }

    fn view(self) -> &'static str {
        match self {
            Flavor::VecT => "[T]",
            Flavor::StringT => "str",
        }
    }
}

/// One recognized parameter site: the exact type span and its licensed
/// replacement. Shape-level only — the body-use analysis decides edit vs
/// rejection. Also consumed by the certifier (ADR-0007) to re-derive sites
/// from the before tree.
#[derive(Clone, Debug)]
pub(crate) struct ParamSite {
    pub(crate) name: String,
    /// The full type span: from `&` through the final `>` / `String`.
    pub(crate) span: ByteSpan,
    /// The licensed replacement text (`&[T]` / `&'a [T]` / `&str` / `&'a str`).
    pub(crate) after: String,
    pub(crate) flavor: Flavor,
}

/// Recognize every `name: &[lifetime] Vec<T>` / `name: &[lifetime] String`
/// parameter of one function's signature. Everything else is silent — an
/// ordinary parameter is not a near-miss.
pub(crate) fn recognized_param_sites(f: &FnUnit<'_>, src: &str) -> Vec<ParamSite> {
    let Some(sig) = f.sig else {
        return Vec::new();
    };
    let Some(params) = param_group(sig, src) else {
        return Vec::new();
    };
    let inner = paren_inner(params, src);
    let mut out = Vec::new();
    for part in split_commas(&inner, src) {
        if let Some(site) = classify_param(part, src) {
            out.push(site);
        }
    }
    out
}

/// The signature's parameter list: the first depth-0 paren group before any
/// `->`, outside generic-parameter angle regions (mirrors the CPG's
/// `param_names` walk).
fn param_group<'a>(sig: &'a Node, src: &str) -> Option<&'a Node> {
    let els = elems(sig);
    let mut angle: i32 = 0;
    for e in &els {
        match e {
            E::T(t) => {
                let text = t.span.text(src);
                if text == "->" {
                    return None; // return type follows; params were before it
                }
                for ch in text.chars() {
                    if ch == '<' {
                        angle += 1;
                    } else if ch == '>' {
                        angle -= 1;
                    }
                }
                if angle < 0 {
                    angle = 0;
                }
            }
            E::G(n) => {
                if angle == 0 && n.kind == cst::PAREN {
                    return Some(n);
                }
            }
        }
    }
    None
}

/// Classify one comma-separated parameter against the recognized grammar.
fn classify_param(part: &[E<'_>], src: &str) -> Option<ParamSite> {
    let colon = crate::ir::cpg::top_index(part, ":", src)?;
    // Pattern side: exactly `[mut] IDENT` — pattern parameters are silent.
    let pat = &part[..colon];
    let idx = usize::from(pat.first().and_then(|e| e.text(src)) == Some("mut"));
    let name = match pat.get(idx) {
        Some(E::T(t))
            if (t.kind == tk::IDENT || t.kind == tk::RAW_IDENT)
                && pat.len() == idx + 1
                && !crate::lang::rust::lexer::is_keyword(t.span.text(src)) =>
        {
            t.span.text(src).to_string()
        }
        _ => return None,
    };
    // Type side: `&` [LIFETIME] (`Vec` <angle region> | `String`), nothing else.
    let ty = &part[colon + 1..];
    let E::T(amp) = ty.first()? else { return None };
    if amp.span.text(src) != "&" {
        return None;
    }
    let mut k = 1;
    let lifetime = match ty.get(k) {
        Some(E::T(t)) if t.kind == tk::LIFETIME => {
            k += 1;
            Some(t.span.text(src))
        }
        _ => None,
    };
    let head = match ty.get(k) {
        Some(E::T(t)) if t.kind == tk::IDENT => t.span.text(src),
        _ => return None, // includes `&mut …`: mutation rights differ, silent
    };
    let lt_prefix = lifetime.map(|l| format!("{l} ")).unwrap_or_default();
    match head {
        "String" if k + 1 == ty.len() => Some(ParamSite {
            name,
            span: ByteSpan::new(amp.span.start as usize, ty[k].span().end as usize),
            after: format!("&{lt_prefix}str"),
            flavor: Flavor::StringT,
        }),
        "Vec" => {
            let (lt, gt) = angle_region(&ty[k + 1..], src)?;
            let inner = src[lt + 1..gt].trim();
            if inner.is_empty() {
                return None;
            }
            Some(ParamSite {
                name,
                span: ByteSpan::new(amp.span.start as usize, gt + 1),
                after: format!("&{lt_prefix}[{inner}]"),
                flavor: Flavor::VecT,
            })
        }
        _ => None,
    }
}

/// The byte positions of the opening `<` and the matching closing `>` of a
/// generic-argument region that must span EXACTLY `els` (no trailing
/// elements). Character-level, because the lexer merges `>>` (and `<<`) into
/// one token; `->` tokens (Fn-sugar return types) carry no angle depth.
fn angle_region(els: &[E<'_>], src: &str) -> Option<(usize, usize)> {
    let mut depth: i32 = 0;
    let mut lt: Option<usize> = None;
    let mut gt: Option<usize> = None;
    for e in els {
        if gt.is_some() {
            return None; // trailing elements after the close
        }
        match e {
            // A balanced group (parens/brackets) is opaque: its own angle
            // characters, if any, are internal to a complete subtree.
            E::G(_) => {
                lt?;
            }
            E::T(t) => {
                let text = t.span.text(src);
                if text == "->" {
                    lt?;
                    continue;
                }
                for (i, ch) in text.char_indices() {
                    if gt.is_some() {
                        return None; // chars after the close inside one token
                    }
                    match ch {
                        '<' => {
                            if lt.is_none() {
                                lt = Some(t.span.start as usize + i);
                            }
                            depth += 1;
                        }
                        '>' => {
                            depth -= 1;
                            if depth < 0 {
                                return None;
                            }
                            if depth == 0 {
                                gt = Some(t.span.start as usize + i);
                            }
                        }
                        _ => {
                            lt?;
                        }
                    }
                }
            }
        }
    }
    Some((lt?, gt?))
}

// ---------------------------------------------------------------------------
// Use analysis: is every occurrence of the parameter slice/str-safe?
// ---------------------------------------------------------------------------

/// Methods callable on `&Vec<T>` that resolve THROUGH `Deref` to the very
/// same `[T]` implementation a `&[T]` parameter calls directly. Sorted;
/// additions must preserve the identical-resolution property.
const VEC_SLICE_SAFE: &[&str] = &[
    "binary_search",
    "chunks",
    "concat",
    "contains",
    "ends_with",
    "first",
    "get",
    "is_empty",
    "iter",
    "join",
    "last",
    "len",
    "split_first",
    "split_last",
    "starts_with",
    "windows",
];

/// Methods callable on `&String` that resolve THROUGH `Deref` to the very
/// same `str` implementation a `&str` parameter calls directly.
const STRING_STR_SAFE: &[&str] = &[
    "as_bytes",
    "bytes",
    "char_indices",
    "chars",
    "contains",
    "ends_with",
    "find",
    "get",
    "is_empty",
    "len",
    "lines",
    "parse",
    "rfind",
    "split",
    "split_whitespace",
    "splitn",
    "starts_with",
    "trim",
    "trim_end",
    "trim_start",
];

fn method_vocabulary(flavor: Flavor) -> &'static [&'static str] {
    match flavor {
        Flavor::VecT => VEC_SLICE_SAFE,
        Flavor::StringT => STRING_STR_SAFE,
    }
}

/// Check every occurrence of `site.name` in the function body against the
/// licensed use forms. `Ok` carries one human-auditable fact per occurrence;
/// `Err` is the machine-readable refusal for the FIRST offending occurrence.
pub(crate) fn licensed_uses(
    f: &FnUnit<'_>,
    src: &str,
    site: &ParamSite,
) -> Result<Vec<String>, (&'static str, String)> {
    let mut facts = Vec::new();
    let mut err: Option<(&'static str, String)> = None;
    crate::rewrite::rules::walk_stmts(&f.stmts, &mut |s| {
        if err.is_some() {
            return;
        }
        let header = flat_tokens(&s.header);
        if let Err(e) = check_tokens(&header, s, true, src, site, &mut facts) {
            err = Some(e);
            return;
        }
        for arm in &s.arms {
            for els in [&arm.pattern, &arm.expr] {
                let toks = flat_tokens(els);
                if let Err(e) = check_tokens(&toks, s, false, src, site, &mut facts) {
                    err = Some(e);
                    return;
                }
            }
        }
    });
    match err {
        Some(e) => Err(e),
        None => Ok(facts),
    }
}

/// Classify each occurrence of the parameter in one token run.
fn check_tokens(
    toks: &[&Token],
    s: &Stmt<'_>,
    is_header: bool,
    src: &str,
    site: &ParamSite,
    facts: &mut Vec<String>,
) -> Result<(), (&'static str, String)> {
    let name = site.name.as_str();
    for (k, t) in toks.iter().enumerate() {
        if (t.kind != tk::IDENT && t.kind != tk::RAW_IDENT) || t.span.text(src) != name {
            continue;
        }
        let prev = k.checked_sub(1).map(|i| toks[i].span.text(src));
        if prev == Some(".") || prev == Some("::") {
            continue; // a member/path projection, not this parameter
        }
        let line = line_of(src, t.span.start as usize);
        let next = toks.get(k + 1).map(|t| t.span.text(src));
        match next {
            Some(".") => {
                let method = match toks.get(k + 2) {
                    Some(m) if m.kind == tk::IDENT => m.span.text(src),
                    _ => {
                        return Err(not_slice_compatible(site, line, "a non-method `.` access"));
                    }
                };
                if toks.get(k + 3).map(|t| t.span.text(src)) != Some("(") {
                    return Err(not_slice_compatible(
                        site,
                        line,
                        "a `.` access that is not a direct method call",
                    ));
                }
                if !method_vocabulary(site.flavor).contains(&method) {
                    return Err((
                        "param_method_not_slice_compatible",
                        format!(
                            "`{name}.{method}(…)` (line {line}) is not in the {}-safe method \
                             vocabulary; `{method}` may be specific to `{}` (or resolve \
                             differently on `&{}`), so the rewrite could change what the \
                             call means",
                            site.flavor.view(),
                            site.flavor.owned(),
                            site.flavor.view(),
                        ),
                    ));
                }
                facts.push(format!(
                    "line {line}: `{name}.{method}(…)` — `{method}` resolves on \
                     `&{}` through Deref to the identical `{}` implementation a \
                     `&{}` receiver calls directly",
                    site.flavor.owned(),
                    site.flavor.view(),
                    site.flavor.view(),
                ));
            }
            Some("[") => {
                facts.push(format!(
                    "line {line}: `{name}[…]` — `Index` forwards through the same deref \
                     on both `&{}` and `&{}`",
                    site.flavor.owned(),
                    site.flavor.view(),
                ));
            }
            _ if site.flavor == Flavor::VecT
                && is_header
                && s.kind == StmtKind::For
                && k + 1 == toks.len()
                && prev == Some("in") =>
            {
                facts.push(format!(
                    "line {line}: `for … in {name}` — `&Vec<T>` and `&[T]` both iterate \
                     `&T` (`IntoIterator` through the same slice iterator)",
                ));
            }
            _ => {
                return Err(not_slice_compatible(
                    site,
                    line,
                    "not an allowlisted method call, indexing, or `for … in` iteration \
                     (passing the parameter onward would hand a callee the OLD type)",
                ));
            }
        }
    }
    Ok(())
}

fn not_slice_compatible(site: &ParamSite, line: usize, what: &str) -> (&'static str, String) {
    (
        "param_use_not_slice_compatible",
        format!(
            "`{}` is used at line {line} as {what}; only uses identical on `&{}` and \
             `&{}` are licensed",
            site.name,
            site.flavor.owned(),
            site.flavor.view(),
        ),
    )
}

/// First byte offset where `fn_name` occurs as anything OTHER than its
/// definition (`fn NAME`) or a direct call (`NAME(`): the function may be
/// taken as a first-class value there. Whole-file token scan — conservative
/// by construction (an unrelated same-named binding also refuses).
pub(crate) fn fn_value_use(src: &str, fn_name: &str) -> Option<usize> {
    if fn_name == "<anon>" {
        return None;
    }
    let all = lex(src);
    let toks: Vec<&Token> = all.iter().filter(|t| !t.trivia).collect();
    for (k, t) in toks.iter().enumerate() {
        if (t.kind != tk::IDENT && t.kind != tk::RAW_IDENT) || t.span.text(src) != fn_name {
            continue;
        }
        if k.checked_sub(1).map(|i| toks[i].span.text(src)) == Some("fn") {
            continue; // the definition itself
        }
        if toks.get(k + 1).map(|t| t.span.text(src)) == Some("(") {
            continue; // a direct call — coercion applies argument-wise
        }
        return Some(t.span.start as usize);
    }
    None
}

// ---------------------------------------------------------------------------
// Emitter
// ---------------------------------------------------------------------------

fn build_edit(
    file: &FileCpg<'_>,
    f: &FnUnit<'_>,
    site: &ParamSite,
    use_facts: Vec<String>,
) -> ProposedEdit {
    let src = file.src;
    let name = &site.name;
    let line = line_of(src, site.span.start as usize);
    // The parameter's readers in the real CPG: DATA_DEP edges var=name whose
    // def site is the function node itself (def=param).
    let readers: Vec<String> = file
        .graph
        .edges()
        .filter(|e| {
            e.kind == edge::DATA_DEP
                && e.to == f.fn_id
                && edge_prop(e, "var") == Some(name)
                && edge_prop(e, "def") == Some("param")
        })
        .map(|e| format!("DATA_DEP var={name} def=param: {} -> {}", e.from, e.to))
        .collect();

    let mut facts = vec![format!(
        "{}: parameter `{name}: {}` at bytes {}..{} (line {line})",
        f.fn_id,
        text_of(src, site.span),
        site.span.start,
        site.span.end,
    )];
    facts.extend(readers);
    if use_facts.is_empty() {
        facts.push(format!(
            "`{name}` has no occurrence in the function body — the generalization is \
             vacuously behavior-preserving"
        ));
    } else {
        facts.extend(use_facts);
    }
    facts.push(format!(
        "`{}` is never taken as a first-class value in this file: every occurrence is \
         the definition or a direct call, and deref coercion (`{}` → `{}`) covers every \
         direct call site",
        f.name,
        site.flavor.owned(),
        site.flavor.view(),
    ));

    ProposedEdit {
        span: site.span,
        before: text_of(src, site.span).to_string(),
        after: site.after.clone(),
        why_safe: format!(
            "every use of `{name}` resolves identically on `&{}` and `&{}` (allowlisted \
             deref-forwarded methods, indexing, iteration), and every existing direct \
             call site coerces to the new type (deref coercion), so the signature is \
             strictly more general and the body's behavior is unchanged",
            site.flavor.owned(),
            site.flavor.view(),
        ),
        cpg_facts: facts,
    }
}

/// A paren group's depth-0 elements without the `(` `)` delimiters.
fn paren_inner<'a>(group: &'a Node, src: &str) -> Vec<E<'a>> {
    let mut v = elems(group);
    if v.first().and_then(|e| e.text(src)) == Some("(") {
        v.remove(0);
    }
    if v.last().and_then(|e| e.text(src)) == Some(")") {
        v.pop();
    }
    v
}

/// Split depth-0 elements on `,`.
fn split_commas<'e, 'a>(els: &'e [E<'a>], src: &str) -> Vec<&'e [E<'a>]> {
    let mut out = Vec::new();
    let mut start = 0;
    for (i, e) in els.iter().enumerate() {
        if e.text(src) == Some(",") {
            out.push(&els[start..i]);
            start = i + 1;
        }
    }
    out.push(&els[start..]);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::rust::parser::parse;
    use crate::rewrite::edit::{apply_edits, SpanEdit};
    use crate::rewrite::rules::analyze_file;

    fn run(src: &str) -> (String, RuleOutcome) {
        let tree = parse("t.rs", src);
        assert!(tree.is_lossless());
        let file = analyze_file(&tree);
        let out = SliceParam.propose(&file, &RuleOptions::default()).unwrap();
        let edits: Vec<SpanEdit> = out
            .edits
            .iter()
            .map(|e| SpanEdit {
                span: e.span,
                replacement: e.after.clone(),
            })
            .collect();
        (apply_edits(src, &edits).unwrap(), out)
    }

    fn only_rejection(out: &RuleOutcome) -> &Rejection {
        assert!(out.edits.is_empty(), "expected no edits: {:?}", out.edits);
        assert_eq!(out.rejections.len(), 1, "{:?}", out.rejections);
        &out.rejections[0]
    }

    // --- accepted shapes ------------------------------------------------------

    #[test]
    fn vec_param_with_slice_safe_method_is_generalized() {
        let src = "fn f(v: &Vec<i32>) {\n    use_len(v.len());\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1, "{:?}", o.rejections);
        assert_eq!(out, "fn f(v: &[i32]) {\n    use_len(v.len());\n}\n");
        assert_eq!(o.edits[0].before, "&Vec<i32>");
        assert_eq!(o.edits[0].after, "&[i32]");
        assert!(parse("t.rs", &out).is_lossless());
    }

    #[test]
    fn string_param_with_str_safe_methods_is_generalized() {
        let src = "fn g(s: &String) {\n    if s.is_empty() {\n        log(s.len());\n    }\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1, "{:?}", o.rejections);
        assert_eq!(
            out,
            "fn g(s: &str) {\n    if s.is_empty() {\n        log(s.len());\n    }\n}\n"
        );
    }

    #[test]
    fn nested_generic_reuses_inner_type_verbatim() {
        // `Vec<Vec<u8>>` closes with a merged `>>` token — the span must end
        // INSIDE that token, character-precise.
        let src = "fn f(v: &Vec<Vec<u8>>) {\n    use_len(v.len());\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1, "{:?}", o.rejections);
        assert_eq!(out, "fn f(v: &[Vec<u8>]) {\n    use_len(v.len());\n}\n");
    }

    #[test]
    fn lifetime_is_reused_verbatim() {
        let src = "fn f<'a>(v: &'a Vec<i32>) -> usize {\n    v.len()\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1, "{:?}", o.rejections);
        assert!(out.contains("(v: &'a [i32])"), "{out}");
    }

    #[test]
    fn indexing_and_iteration_are_licensed() {
        let src = "fn f(v: &Vec<i32>) {\n    use_it(v[0]);\n    for x in v {\n        use_it(x);\n    }\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1, "{:?}", o.rejections);
        assert!(out.starts_with("fn f(v: &[i32]) {"), "{out}");
    }

    #[test]
    fn unused_param_is_vacuously_licensed() {
        let src = "fn f(v: &Vec<i32>) {\n    done();\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1, "{:?}", o.rejections);
        assert!(out.starts_with("fn f(v: &[i32]) {"), "{out}");
        let facts = o.edits[0].cpg_facts.join("\n");
        assert!(facts.contains("no occurrence"), "{facts}");
    }

    #[test]
    fn each_parameter_is_its_own_site() {
        let src =
            "fn f(a: &Vec<i32>, b: &String) {\n    use_it(a.len());\n    use_it(b.len());\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 2, "{:?}", o.rejections);
        assert!(out.contains("(a: &[i32], b: &str)"), "{out}");
    }

    #[test]
    fn rejected_param_does_not_block_the_other() {
        let src = "fn f(a: &Vec<i32>, b: &Vec<i32>) {\n    use_it(a.len());\n    use_it(b.capacity());\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1, "{:?}", o.edits);
        assert_eq!(o.rejections.len(), 1, "{:?}", o.rejections);
        assert!(out.contains("(a: &[i32], b: &Vec<i32>)"), "{out}");
        assert_eq!(o.rejections[0].reason, "param_method_not_slice_compatible");
    }

    #[test]
    fn why_safe_cites_param_edges_and_use_facts() {
        let src = "fn f(v: &Vec<i32>) {\n    use_len(v.len());\n}\n";
        let (_, o) = run(src);
        let e = &o.edits[0];
        assert!(e.why_safe.contains("deref coercion"), "{}", e.why_safe);
        assert!(
            e.why_safe.contains("strictly more general"),
            "{}",
            e.why_safe
        );
        let facts = e.cpg_facts.join("\n");
        assert!(facts.contains("fn::f#1"), "{facts}");
        assert!(facts.contains("DATA_DEP var=v def=param"), "{facts}");
        assert!(facts.contains("`v.len(…)`"), "{facts}");
    }

    // --- rejected shapes (machine-readable reasons) ---------------------------

    #[test]
    fn vec_specific_method_is_rejected() {
        let src = "fn f(v: &Vec<i32>) {\n    log(v.capacity());\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        let r = only_rejection(&o);
        assert_eq!(r.reason, "param_method_not_slice_compatible");
        assert!(r.detail.contains("capacity"), "{}", r.detail);
    }

    #[test]
    fn clone_on_the_param_is_rejected() {
        // `v.clone()` on `&Vec<T>` produces `Vec<T>`; on `&[T]` it copies the
        // REFERENCE — resolution differs, so `clone` is not in the vocabulary.
        let src = "fn f(v: &Vec<i32>) {\n    let w = v.clone();\n    use_it(w);\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert_eq!(
            only_rejection(&o).reason,
            "param_method_not_slice_compatible"
        );
    }

    #[test]
    fn param_passed_onward_is_rejected() {
        let src = "fn f(v: &Vec<i32>) {\n    helper(v);\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        let r = only_rejection(&o);
        assert_eq!(r.reason, "param_use_not_slice_compatible");
        assert!(r.detail.contains("line 2"), "{}", r.detail);
    }

    #[test]
    fn reborrow_is_rejected() {
        let src = "fn f(s: &String) {\n    takes(&s);\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert_eq!(only_rejection(&o).reason, "param_use_not_slice_compatible");
    }

    #[test]
    fn macro_argument_use_is_rejected() {
        let src = "fn f(v: &Vec<i32>) {\n    println!(\"{:?}\", v);\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert_eq!(only_rejection(&o).reason, "param_use_not_slice_compatible");
    }

    #[test]
    fn string_iteration_is_rejected() {
        // `for c in s` does not compile for `&String`, but a match-shaped
        // occurrence must still refuse for the String flavor, never license.
        let src = "fn f(s: &String) {\n    for c in s {\n        use_it(c);\n    }\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        assert_eq!(only_rejection(&o).reason, "param_use_not_slice_compatible");
    }

    #[test]
    fn function_used_as_value_is_rejected() {
        let src =
            "fn f(v: &Vec<i32>) {\n    use_len(v.len());\n}\n\nfn caller() {\n    register(f);\n}\n";
        let (out, o) = run(src);
        assert_eq!(out, src);
        let r = only_rejection(&o);
        assert_eq!(r.reason, "function_used_as_value");
        assert!(r.detail.contains("line 6"), "{}", r.detail);
    }

    #[test]
    fn direct_calls_do_not_trip_the_value_guard() {
        let src = "fn f(v: &Vec<i32>) {\n    use_len(v.len());\n}\n\nfn caller(xs: Vec<i32>) {\n    f(&xs);\n}\n";
        let (out, o) = run(src);
        assert_eq!(o.edits.len(), 1, "{:?}", o.rejections);
        assert!(out.contains("fn f(v: &[i32])"), "{out}");
    }

    // --- silence (not candidates) ---------------------------------------------

    #[test]
    fn non_candidates_are_silent() {
        for src in [
            // &mut grants growth rights &mut [T] does not
            "fn f(v: &mut Vec<i32>) {\n    v.push(1);\n}\n",
            // by-value ownership
            "fn f(v: Vec<i32>) {\n    use_it(v);\n}\n",
            // already a slice / str
            "fn f(v: &[i32], s: &str) {\n    use_it(v.len() + s.len());\n}\n",
            // other generics
            "fn f(m: &HashMap<i32, i32>) {\n    use_it(m.len());\n}\n",
            // path-qualified Vec (v1 recognizes the bare token only)
            "fn f(v: &std::vec::Vec<i32>) {\n    use_it(v.len());\n}\n",
            // pattern parameter
            "fn f((a, b): (&Vec<i32>, i32)) {\n    use_it(b);\n}\n",
        ] {
            let (out, o) = run(src);
            assert_eq!(out, src, "{src}");
            assert!(o.edits.is_empty(), "{src}: {:?}", o.edits);
            assert!(o.rejections.is_empty(), "{src}: {:?}", o.rejections);
        }
    }

    #[test]
    fn proposal_is_deterministic() {
        let src =
            "fn f(v: &Vec<i32>, s: &String) {\n    use_it(v.len());\n    use_it(s.chars());\n}\n";
        let (a, oa) = run(src);
        let (b, ob) = run(src);
        assert_eq!(a, b);
        assert_eq!(oa.edits, ob.edits);
        assert_eq!(oa.rejections, ob.rejections);
    }
}
