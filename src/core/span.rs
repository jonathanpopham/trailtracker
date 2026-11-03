//! Source identity and byte-accurate spans.
//!
//! Spans are half-open byte ranges `[start, end)` into the original UTF-8
//! source buffer. Byte offsets are the lossless ground truth; line/column are
//! derived on demand from a [`LineIndex`] so the hot path stays cheap.

/// Stable identifier for a single source file within a run.
///
/// Computed deterministically from the file's path so the same repository
/// always yields the same identifiers (airgap reproducibility requirement).
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct SourceId(pub u64);

impl SourceId {
    /// Derive a stable id from a path using a fixed FNV-1a hash. No external
    /// crates, no randomness, identical across machines.
    pub fn from_path(path: &str) -> Self {
        SourceId(fnv1a_64(path.as_bytes()))
    }
}

/// Deterministic 64-bit FNV-1a, std-only so the shipped runtime carries no
/// hashing dependency.
pub fn fnv1a_64(bytes: &[u8]) -> u64 {
    const OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
    const PRIME: u64 = 0x0000_0100_0000_01b3;
    let mut hash = OFFSET;
    for &b in bytes {
        hash ^= b as u64;
        hash = hash.wrapping_mul(PRIME);
    }
    hash
}

/// Half-open byte range into a source buffer.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ByteSpan {
    pub start: u32,
    pub end: u32,
}

impl ByteSpan {
    pub fn new(start: usize, end: usize) -> Self {
        debug_assert!(start <= end, "span start must not exceed end");
        ByteSpan {
            start: start as u32,
            end: end as u32,
        }
    }

    pub fn empty_at(offset: usize) -> Self {
        ByteSpan::new(offset, offset)
    }

    pub fn len(&self) -> usize {
        (self.end - self.start) as usize
    }

    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }

    /// Smallest span covering both inputs.
    pub fn merge(self, other: ByteSpan) -> ByteSpan {
        ByteSpan {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }

    /// Slice the original source. Returns `""` if the span is out of bounds
    /// rather than panicking — conservative failure mode for defense code.
    pub fn text<'s>(&self, source: &'s str) -> &'s str {
        let (s, e) = (self.start as usize, self.end as usize);
        source.get(s..e).unwrap_or("")
    }
}

/// 1-based human-facing location.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LineCol {
    pub line: u32,
    pub column: u32,
}

/// Precomputed line-start offsets for O(log n) byte → line/column lookup.
pub struct LineIndex {
    /// Byte offset of the start of each line. Always begins with 0.
    line_starts: Vec<u32>,
}

impl LineIndex {
    pub fn new(source: &str) -> Self {
        let mut line_starts = Vec::with_capacity(source.len() / 32 + 1);
        line_starts.push(0);
        for (i, b) in source.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push((i + 1) as u32);
            }
        }
        LineIndex { line_starts }
    }

    /// 1-based line/column for a byte offset. Column counts UTF-8 bytes from
    /// the line start (stable and cheap); callers needing grapheme columns can
    /// layer that on top without changing the ground truth.
    pub fn line_col(&self, offset: u32) -> LineCol {
        // Largest line_start <= offset.
        let line = match self.line_starts.binary_search(&offset) {
            Ok(idx) => idx,
            Err(idx) => idx - 1,
        };
        let column = offset - self.line_starts[line];
        LineCol {
            line: (line + 1) as u32,
            column: column + 1,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fnv_is_stable() {
        assert_eq!(fnv1a_64(b""), 0xcbf2_9ce4_8422_2325);
        assert_eq!(fnv1a_64(b"a"), fnv1a_64(b"a"));
        assert_ne!(fnv1a_64(b"a"), fnv1a_64(b"b"));
    }

    #[test]
    fn line_col_maps_offsets() {
        let src = "ab\ncde\nf";
        let idx = LineIndex::new(src);
        assert_eq!(idx.line_col(0), LineCol { line: 1, column: 1 });
        assert_eq!(idx.line_col(1), LineCol { line: 1, column: 2 });
        assert_eq!(idx.line_col(3), LineCol { line: 2, column: 1 });
        assert_eq!(idx.line_col(7), LineCol { line: 3, column: 1 });
    }

    #[test]
    fn span_text_is_bounds_safe() {
        let span = ByteSpan::new(0, 100);
        assert_eq!(span.text("short"), "");
        assert_eq!(ByteSpan::new(0, 3).text("hello"), "hel");
    }
}
