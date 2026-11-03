//! Minimal, deterministic, std-only JSON value + writer.
//!
//! Determinism is a hard requirement: the same graph must serialize
//! byte-for-byte identically across runs and machines. Object keys are stored
//! in a `BTreeMap` so emission order is always sorted, and floats are written
//! with a fixed strategy. No `serde`, no external crates.

use std::collections::BTreeMap;
use std::io::{self, Write};

#[derive(Clone, Debug, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    I64(i64),
    U64(u64),
    F64(f64),
    Str(String),
    Array(Vec<Json>),
    /// Sorted-key object for deterministic output.
    Object(BTreeMap<String, Json>),
}

impl Json {
    pub fn str(value: impl Into<String>) -> Json {
        Json::Str(value.into())
    }

    /// Build an object from key/value pairs without ceremony at call sites.
    pub fn obj(pairs: impl IntoIterator<Item = (&'static str, Json)>) -> Json {
        let mut map = BTreeMap::new();
        for (k, v) in pairs {
            map.insert(k.to_string(), v);
        }
        Json::Object(map)
    }

    /// Compact single-line serialization, used for JSONL records.
    pub fn to_line(&self) -> String {
        let mut buf = Vec::new();
        write_json(&mut buf, self).expect("writing to Vec is infallible");
        // Writer only emits valid UTF-8.
        String::from_utf8(buf).expect("json writer emits utf-8")
    }
}

impl From<&str> for Json {
    fn from(v: &str) -> Json {
        Json::Str(v.to_string())
    }
}
impl From<String> for Json {
    fn from(v: String) -> Json {
        Json::Str(v)
    }
}
impl From<bool> for Json {
    fn from(v: bool) -> Json {
        Json::Bool(v)
    }
}
impl From<u32> for Json {
    fn from(v: u32) -> Json {
        Json::U64(v as u64)
    }
}
impl From<u64> for Json {
    fn from(v: u64) -> Json {
        Json::U64(v)
    }
}
impl From<usize> for Json {
    fn from(v: usize) -> Json {
        Json::U64(v as u64)
    }
}
impl From<i64> for Json {
    fn from(v: i64) -> Json {
        Json::I64(v)
    }
}

/// Write a JSON value to any `Write` sink in compact form.
pub fn write_json<W: Write>(w: &mut W, value: &Json) -> io::Result<()> {
    match value {
        Json::Null => w.write_all(b"null"),
        Json::Bool(true) => w.write_all(b"true"),
        Json::Bool(false) => w.write_all(b"false"),
        Json::I64(n) => write!(w, "{n}"),
        Json::U64(n) => write!(w, "{n}"),
        Json::F64(n) => {
            if n.is_finite() {
                write!(w, "{n}")
            } else {
                // JSON has no NaN/Infinity; emit null to stay valid.
                w.write_all(b"null")
            }
        }
        Json::Str(s) => write_json_string(w, s),
        Json::Array(items) => {
            w.write_all(b"[")?;
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    w.write_all(b",")?;
                }
                write_json(w, item)?;
            }
            w.write_all(b"]")
        }
        Json::Object(map) => {
            w.write_all(b"{")?;
            for (i, (k, v)) in map.iter().enumerate() {
                if i > 0 {
                    w.write_all(b",")?;
                }
                write_json_string(w, k)?;
                w.write_all(b":")?;
                write_json(w, v)?;
            }
            w.write_all(b"}")
        }
    }
}

fn write_json_string<W: Write>(w: &mut W, s: &str) -> io::Result<()> {
    w.write_all(b"\"")?;
    for c in s.chars() {
        match c {
            '"' => w.write_all(b"\\\"")?,
            '\\' => w.write_all(b"\\\\")?,
            '\n' => w.write_all(b"\\n")?,
            '\r' => w.write_all(b"\\r")?,
            '\t' => w.write_all(b"\\t")?,
            '\u{08}' => w.write_all(b"\\b")?,
            '\u{0C}' => w.write_all(b"\\f")?,
            c if (c as u32) < 0x20 => write!(w, "\\u{:04x}", c as u32)?,
            c => {
                let mut buf = [0u8; 4];
                w.write_all(c.encode_utf8(&mut buf).as_bytes())?;
            }
        }
    }
    w.write_all(b"\"")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn object_keys_are_sorted_deterministically() {
        let v = Json::obj([("b", 1u64.into()), ("a", 2u64.into())]);
        assert_eq!(v.to_line(), "{\"a\":2,\"b\":1}");
    }

    #[test]
    fn strings_are_escaped() {
        assert_eq!(Json::str("a\"\n\t\\b").to_line(), "\"a\\\"\\n\\t\\\\b\"");
    }

    #[test]
    fn control_chars_use_unicode_escape() {
        assert_eq!(Json::str("\u{01}").to_line(), "\"\\u0001\"");
    }
}

/// A deliberately tiny, defensive JSON **reader** for *external* inputs only:
/// enrichment backend replies and human-authored `.trailtracker-arch.json`
/// specs. The crate keeps a writer-only JSON policy for its own deterministic
/// output ([`Json`] above); nothing parsed here is ever re-emitted
/// byte-for-byte.
pub mod read {
    /// A parsed JSON value. Object keys keep reply order (duplicates keep the
    /// first occurrence on lookup).
    #[derive(Clone, Debug, PartialEq)]
    pub enum V {
        Null,
        Bool(bool),
        Num(f64),
        Str(String),
        Arr(Vec<V>),
        Obj(Vec<(String, V)>),
    }

    /// Parse `text` as exactly one JSON value (trailing garbage is an error).
    pub fn parse(text: &str) -> Result<V, String> {
        let chars: Vec<char> = text.chars().collect();
        let mut i = 0;
        let v = value(&chars, &mut i)?;
        skip_ws(&chars, &mut i);
        if i != chars.len() {
            return Err(format!("trailing data at char {i}"));
        }
        Ok(v)
    }

    fn skip_ws(c: &[char], i: &mut usize) {
        while *i < c.len() && c[*i].is_whitespace() {
            *i += 1;
        }
    }

    fn value(c: &[char], i: &mut usize) -> Result<V, String> {
        skip_ws(c, i);
        match c.get(*i) {
            Some('{') => {
                *i += 1;
                let mut pairs = Vec::new();
                skip_ws(c, i);
                if c.get(*i) == Some(&'}') {
                    *i += 1;
                    return Ok(V::Obj(pairs));
                }
                loop {
                    skip_ws(c, i);
                    let V::Str(key) = value(c, i)? else {
                        return Err("object key is not a string".into());
                    };
                    skip_ws(c, i);
                    if c.get(*i) != Some(&':') {
                        return Err(format!("expected ':' at char {i}"));
                    }
                    *i += 1;
                    pairs.push((key, value(c, i)?));
                    skip_ws(c, i);
                    match c.get(*i) {
                        Some(',') => *i += 1,
                        Some('}') => {
                            *i += 1;
                            return Ok(V::Obj(pairs));
                        }
                        other => return Err(format!("expected ',' or '}}', got {other:?}")),
                    }
                }
            }
            Some('[') => {
                *i += 1;
                let mut items = Vec::new();
                skip_ws(c, i);
                if c.get(*i) == Some(&']') {
                    *i += 1;
                    return Ok(V::Arr(items));
                }
                loop {
                    items.push(value(c, i)?);
                    skip_ws(c, i);
                    match c.get(*i) {
                        Some(',') => *i += 1,
                        Some(']') => {
                            *i += 1;
                            return Ok(V::Arr(items));
                        }
                        other => return Err(format!("expected ',' or ']', got {other:?}")),
                    }
                }
            }
            Some('"') => {
                *i += 1;
                let mut s = String::new();
                loop {
                    match c.get(*i) {
                        Some('"') => {
                            *i += 1;
                            return Ok(V::Str(s));
                        }
                        Some('\\') => {
                            *i += 1;
                            match c.get(*i) {
                                Some('n') => s.push('\n'),
                                Some('t') => s.push('\t'),
                                Some('r') => s.push('\r'),
                                Some('b') => s.push('\u{08}'),
                                Some('f') => s.push('\u{0C}'),
                                Some('u') => {
                                    if *i + 4 >= c.len() {
                                        return Err("truncated \\u escape".into());
                                    }
                                    let hex: String = c[*i + 1..*i + 5].iter().collect();
                                    let n = u32::from_str_radix(&hex, 16)
                                        .map_err(|e| format!("bad \\u escape: {e}"))?;
                                    // Surrogates in replies degrade to U+FFFD
                                    // rather than failing the whole parse.
                                    s.push(char::from_u32(n).unwrap_or('\u{FFFD}'));
                                    *i += 4;
                                }
                                Some(other) => s.push(*other),
                                None => return Err("unterminated escape".into()),
                            }
                            *i += 1;
                        }
                        Some(ch) => {
                            s.push(*ch);
                            *i += 1;
                        }
                        None => return Err("unterminated string".into()),
                    }
                }
            }
            Some(ch) if *ch == '-' || ch.is_ascii_digit() => {
                let start = *i;
                *i += 1;
                while matches!(
                    c.get(*i),
                    Some(d) if d.is_ascii_digit() || matches!(d, '.' | 'e' | 'E' | '+' | '-')
                ) {
                    *i += 1;
                }
                let raw: String = c[start..*i].iter().collect();
                raw.parse::<f64>()
                    .map(V::Num)
                    .map_err(|e| format!("bad number '{raw}': {e}"))
            }
            Some('t') if c[*i..].starts_with(&['t', 'r', 'u', 'e']) => {
                *i += 4;
                Ok(V::Bool(true))
            }
            Some('f') if c[*i..].starts_with(&['f', 'a', 'l', 's', 'e']) => {
                *i += 5;
                Ok(V::Bool(false))
            }
            Some('n') if c[*i..].starts_with(&['n', 'u', 'l', 'l']) => {
                *i += 4;
                Ok(V::Null)
            }
            other => Err(format!("unexpected {other:?} at char {i}")),
        }
    }
}
