//! Span-edit machinery over the lossless source (ADR-0006, M1).
//!
//! The one primitive the rewrite engine is allowed to perform: given a source
//! buffer and a set of `(byte range, replacement)` edits, produce the new
//! source. The safety invariant — every byte OUTSIDE the edited ranges is
//! byte-identical in the output — holds by construction (the output is
//! spliced from the original's untouched slices) and is re-provable per edit
//! set via [`reverse_edits`] round-trips.
//!
//! Deterministic ordering: edits are validated in ascending span order and
//! applied left-to-right in one pass. Overlapping, unordered-ambiguous,
//! out-of-bounds, or non-UTF-8-boundary spans are hard errors, never a silent
//! reorder or truncation.

use crate::core::span::ByteSpan;

/// One byte-span replacement: `span` addresses the ORIGINAL source.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpanEdit {
    pub span: ByteSpan,
    pub replacement: String,
}

/// Why an edit set was refused. Every variant names the offending span(s) so
/// the error is actionable without re-deriving anything.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EditError {
    /// A span reaches past the end of the source.
    OutOfBounds { span: ByteSpan, source_len: usize },
    /// A span endpoint falls inside a UTF-8 code point. CST-derived spans are
    /// token spans and can never trigger this; it defends hand-built input.
    NotCharBoundary { span: ByteSpan },
    /// Two spans overlap, or two empty spans target the same offset (their
    /// application order would be ambiguous).
    Overlap { first: ByteSpan, second: ByteSpan },
}

impl std::fmt::Display for EditError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EditError::OutOfBounds { span, source_len } => write!(
                f,
                "edit span {}..{} exceeds source length {}",
                span.start, span.end, source_len
            ),
            EditError::NotCharBoundary { span } => write!(
                f,
                "edit span {}..{} does not fall on UTF-8 character boundaries",
                span.start, span.end
            ),
            EditError::Overlap { first, second } => write!(
                f,
                "edit spans {}..{} and {}..{} overlap",
                first.start, first.end, second.start, second.end
            ),
        }
    }
}

/// Apply `edits` to `source`, producing the new text. The edits may be given
/// in any order; they are sorted by span deterministically. An empty edit set
/// returns the source unchanged (byte-identical).
pub fn apply_edits(source: &str, edits: &[SpanEdit]) -> Result<String, EditError> {
    let sorted = validate(source, edits)?;
    let grow: usize = sorted.iter().map(|e| e.replacement.len()).sum();
    let mut out = String::with_capacity(source.len() + grow);
    let mut cursor = 0usize;
    for e in &sorted {
        let (s, t) = (e.span.start as usize, e.span.end as usize);
        out.push_str(&source[cursor..s]);
        out.push_str(&e.replacement);
        cursor = t;
    }
    out.push_str(&source[cursor..]);
    Ok(out)
}

/// The inverse edit set: applied to `apply_edits(source, edits)`, it
/// reconstructs `source` byte-for-byte. Exists so tests (and audits) can
/// prove the outside-span identity invariant on any edit set.
pub fn reverse_edits(source: &str, edits: &[SpanEdit]) -> Result<Vec<SpanEdit>, EditError> {
    let sorted = validate(source, edits)?;
    let mut delta: i64 = 0;
    let mut out = Vec::with_capacity(sorted.len());
    for e in &sorted {
        let (s, t) = (e.span.start as usize, e.span.end as usize);
        let new_start = (s as i64 + delta) as usize;
        let new_end = new_start + e.replacement.len();
        out.push(SpanEdit {
            span: ByteSpan::new(new_start, new_end),
            replacement: source[s..t].to_string(),
        });
        delta += e.replacement.len() as i64 - (t - s) as i64;
    }
    Ok(out)
}

/// Sort by span and enforce every invariant. Returns the sorted copy.
fn validate(source: &str, edits: &[SpanEdit]) -> Result<Vec<SpanEdit>, EditError> {
    let mut sorted: Vec<SpanEdit> = edits.to_vec();
    sorted.sort_by_key(|e| (e.span.start, e.span.end));
    for e in &sorted {
        let (s, t) = (e.span.start as usize, e.span.end as usize);
        if t > source.len() || s > t {
            return Err(EditError::OutOfBounds {
                span: e.span,
                source_len: source.len(),
            });
        }
        if !source.is_char_boundary(s) || !source.is_char_boundary(t) {
            return Err(EditError::NotCharBoundary { span: e.span });
        }
    }
    for pair in sorted.windows(2) {
        let (a, b) = (&pair[0], &pair[1]);
        // Touching is fine (a.end == b.start); overlap is not. Two empty
        // spans at one offset are ambiguous — also rejected.
        let ambiguous_empty = a.span.start == b.span.start && a.span.end == b.span.end;
        if b.span.start < a.span.end || ambiguous_empty {
            return Err(EditError::Overlap {
                first: a.span,
                second: b.span,
            });
        }
    }
    Ok(sorted)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn edit(start: usize, end: usize, replacement: &str) -> SpanEdit {
        SpanEdit {
            span: ByteSpan::new(start, end),
            replacement: replacement.to_string(),
        }
    }

    #[test]
    fn empty_edit_set_is_byte_identical() {
        let src = "fn main() { let x = 1; }\n";
        assert_eq!(apply_edits(src, &[]).unwrap(), src);
    }

    #[test]
    fn single_replacement_touches_only_its_span() {
        let src = "aaa bbb ccc";
        let out = apply_edits(src, &[edit(4, 7, "XY")]).unwrap();
        assert_eq!(out, "aaa XY ccc");
    }

    #[test]
    fn edits_apply_in_span_order_regardless_of_input_order() {
        let src = "0123456789";
        let out = apply_edits(src, &[edit(8, 9, "B"), edit(1, 2, "A")]).unwrap();
        assert_eq!(out, "0A234567B9");
    }

    #[test]
    fn insertion_and_deletion() {
        let src = "abcdef";
        // Insert at 3, delete 5..6.
        let out = apply_edits(src, &[edit(3, 3, "XX"), edit(5, 6, "")]).unwrap();
        assert_eq!(out, "abcXXde");
    }

    #[test]
    fn touching_spans_are_allowed() {
        let src = "abcdef";
        let out = apply_edits(src, &[edit(0, 2, "1"), edit(2, 4, "2")]).unwrap();
        assert_eq!(out, "12ef");
    }

    #[test]
    fn overlapping_spans_are_rejected() {
        let src = "abcdef";
        let err = apply_edits(src, &[edit(0, 3, "x"), edit(2, 4, "y")]).unwrap_err();
        assert!(matches!(err, EditError::Overlap { .. }), "{err}");
    }

    #[test]
    fn duplicate_empty_spans_are_rejected_as_ambiguous() {
        let src = "abc";
        let err = apply_edits(src, &[edit(1, 1, "x"), edit(1, 1, "y")]).unwrap_err();
        assert!(matches!(err, EditError::Overlap { .. }), "{err}");
    }

    #[test]
    fn out_of_bounds_is_rejected() {
        let err = apply_edits("abc", &[edit(2, 9, "x")]).unwrap_err();
        assert!(matches!(err, EditError::OutOfBounds { .. }), "{err}");
    }

    #[test]
    fn non_char_boundary_is_rejected() {
        let src = "aöb"; // ö is two bytes: offsets 1..3
        let err = apply_edits(src, &[edit(2, 3, "x")]).unwrap_err();
        assert!(matches!(err, EditError::NotCharBoundary { .. }), "{err}");
    }

    #[test]
    fn apply_then_revert_is_byte_identical() {
        let src = "fn f() {\n    if true { a(); } else { b(); }\n    done();\n}\n";
        let edits = vec![edit(13, 44, "a();"), edit(49, 56, "finish();")];
        let applied = apply_edits(src, &edits).unwrap();
        assert_ne!(applied, src);
        let reverse = reverse_edits(src, &edits).unwrap();
        let restored = apply_edits(&applied, &reverse).unwrap();
        assert_eq!(restored, src, "revert must reconstruct the original bytes");
    }

    #[test]
    fn revert_round_trip_with_growth_and_shrink() {
        let src = "0123456789";
        let edits = vec![edit(0, 1, "LONGER"), edit(4, 8, ""), edit(9, 9, "+")];
        let applied = apply_edits(src, &edits).unwrap();
        assert_eq!(applied, "LONGER1238+9");
        let reverse = reverse_edits(src, &edits).unwrap();
        assert_eq!(apply_edits(&applied, &reverse).unwrap(), src);
    }

    #[test]
    fn outside_span_bytes_are_identical_slices() {
        // Direct statement of the invariant: bytes before the first span and
        // after the last are the same slices of memory content.
        let src = "prefix MIDDLE suffix";
        let out = apply_edits(src, &[edit(7, 13, "CENTER")]).unwrap();
        assert_eq!(&out[..7], &src[..7]);
        assert_eq!(&out[out.len() - 7..], &src[src.len() - 7..]);
    }
}
