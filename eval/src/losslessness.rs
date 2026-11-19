//! Shared input domain for exhaustive execution and the optional symbolic proof.
//! Neither checker samples or narrows this alphabet or maximum length.

pub const ALPHABET: &[u8] = b"(){}[]\"'/*# \n;:a0";
pub const MAX_LEN: usize = 5;
