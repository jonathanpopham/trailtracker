//! A tiny, std-only tokenizer for the Salesforce formula DSL (TT-64).
//!
//! Salesforce formulas appear on validation rules (`errorConditionFormula`),
//! formula fields (`<formula>`), default values, and in-flow formulas. This is
//! **not** an evaluator: it scans the expression and collects the *names it
//! references* so the graph can carry honest `USES_TYPE` edges from a rule /
//! field to the SObject fields it depends on. The parsed reference list also
//! feeds the workflow-spec serializer (TT-79), replacing the previously opaque
//! `formula` property.
//!
//! What it distinguishes, and why:
//! - **Function calls** (`ISBLANK(`, `TEXT(`, `NOT(`, `AND(`, `OR(`…): an
//!   identifier immediately followed by `(` is a function head, *not* a field.
//!   Skipped.
//! - **Bare identifiers** (`Severity__c`, `Amount`): a field on the owning
//!   object. Collected as a resolvable field candidate (`bare_fields`) — these
//!   are what get `sobject_field::<Obj>.<Field>` edges.
//! - **Dotted paths** (`Contact.Email`, `Account.Owner.Name`): a relationship
//!   traversal. Only the *head* is collected (into `refs`, not `bare_fields`):
//!   the head names a relationship/object we can list but not resolve to a
//!   single field on the owning object, so no edge is fabricated for it.
//! - **`$`-prefixed system references** (`$Permission.Bypass`, `$User.Id`):
//!   global variables, not fields of the owning object. Captured *separately*
//!   in `system_refs` so they never masquerade as field dependencies.
//! - **String literals** (`'...'`, and defensively `"..."`), **numbers**, and
//!   **operators** (`&&`, `||`, `+`, `-`, `==`, …): skipped.
//! - **Boolean / null literals** (`TRUE`, `FALSE`, `NULL`, case-insensitive):
//!   skipped so they don't pollute the reference list.
//!
//! Robustness is a hard requirement: unknown or malformed input yields whatever
//! could be recovered and **never panics**. The scanner only ever advances, so
//! it always terminates.

use std::collections::BTreeSet;

/// Field / object references recovered from a formula expression. All lists are
/// sorted and de-duplicated (they come out of `BTreeSet`s), so identical input
/// always produces byte-identical output.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct FormulaRefs {
    /// Every non-system reference: bare identifiers plus the *heads* of dotted
    /// paths. This is the human-facing `formula_refs` list.
    pub refs: Vec<String>,
    /// `$`-prefixed system references (global variables), full dotted path kept
    /// (e.g. `$Permission.Bypass`). Never mixed into `refs`.
    pub system_refs: Vec<String>,
    /// The subset of `refs` that appeared as a *bare* identifier (no dotted
    /// path) — the resolvable `sobject_field::<Obj>.<Field>` candidates.
    pub bare_fields: Vec<String>,
}

fn is_ident_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

fn is_ident_part(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

/// `TRUE` / `FALSE` / `NULL` are language literals, not field references.
fn is_literal(word: &str) -> bool {
    ["TRUE", "FALSE", "NULL"]
        .iter()
        .any(|w| word.eq_ignore_ascii_case(w))
}

/// Scan a formula string and collect the names it references. Never panics.
pub fn extract(formula: &str) -> FormulaRefs {
    let chars: Vec<char> = formula.chars().collect();
    let n = chars.len();
    let mut i = 0usize;

    let mut refs: BTreeSet<String> = BTreeSet::new();
    let mut bare: BTreeSet<String> = BTreeSet::new();
    let mut system: BTreeSet<String> = BTreeSet::new();

    while i < n {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
        } else if c == '\'' || c == '"' {
            // String literal: skip to the matching quote, honoring backslash
            // escapes. An unterminated literal is consumed to end-of-input.
            let quote = c;
            i += 1;
            while i < n {
                if chars[i] == '\\' {
                    i += 2;
                    continue;
                }
                if chars[i] == quote {
                    i += 1;
                    break;
                }
                i += 1;
            }
        } else if c == '$' {
            // System reference: $Ident(.Ident)*  → captured whole, separately.
            let start = i;
            i += 1;
            while i < n && is_ident_part(chars[i]) {
                i += 1;
            }
            i = consume_dotted_tail(&chars, i);
            // Guard against a lone `$` with no name following it.
            if i > start + 1 {
                system.insert(chars[start..i].iter().collect());
            }
        } else if is_ident_start(c) {
            let start = i;
            i += 1;
            while i < n && is_ident_part(chars[i]) {
                i += 1;
            }
            let head: String = chars[start..i].iter().collect();
            // Look past whitespace to classify: `(` → function, `.` → dotted.
            let mut k = i;
            while k < n && chars[k].is_whitespace() {
                k += 1;
            }
            if k < n && chars[k] == '(' {
                // Function call head: not a field. Skip (args scanned next).
            } else if k < n && chars[k] == '.' {
                // Dotted path: head is a field/object ref (list, don't resolve).
                if !is_literal(&head) {
                    refs.insert(head);
                }
                // Consume the trailing `.segment.segment…` so its segments are
                // not re-collected as bare identifiers.
                i = consume_dotted_tail(&chars, k);
            } else if !is_literal(&head) {
                // Bare identifier: a resolvable field candidate.
                refs.insert(head.clone());
                bare.insert(head);
            }
        } else if c.is_ascii_digit() {
            // Number: digits with optional decimal points. Skipped.
            i += 1;
            while i < n && (chars[i].is_ascii_digit() || chars[i] == '.') {
                i += 1;
            }
        } else {
            // Operator / punctuation / stray char: advance one.
            i += 1;
        }
    }

    FormulaRefs {
        refs: refs.into_iter().collect(),
        system_refs: system.into_iter().collect(),
        bare_fields: bare.into_iter().collect(),
    }
}

/// Starting at `i` (positioned on a `.` or just past an identifier), consume any
/// `.<ident>` continuation and return the index just past the whole dotted
/// tail. Whitespace around the dots is tolerated. Always makes progress bounded
/// by the input length, so it terminates.
fn consume_dotted_tail(chars: &[char], mut i: usize) -> usize {
    let n = chars.len();
    loop {
        // Skip whitespace before a possible dot.
        let mut j = i;
        while j < n && chars[j].is_whitespace() {
            j += 1;
        }
        if j < n && chars[j] == '.' {
            j += 1;
            while j < n && chars[j].is_whitespace() {
                j += 1;
            }
            if j < n && is_ident_start(chars[j]) {
                j += 1;
                while j < n && is_ident_part(chars[j]) {
                    j += 1;
                }
                i = j;
                continue;
            }
            // A dot not followed by an identifier: stop before consuming it, so
            // the caller's main loop handles it as punctuation.
        }
        break;
    }
    i
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extracts_bare_field_and_skips_function_names() {
        // The sforg validation rule formula.
        let r = extract("ISBLANK(TEXT(Severity__c)) && NOT($Permission.Bypass)");
        assert_eq!(r.refs, vec!["Severity__c".to_string()]);
        assert_eq!(r.bare_fields, vec!["Severity__c".to_string()]);
        assert_eq!(r.system_refs, vec!["$Permission.Bypass".to_string()]);
    }

    #[test]
    fn dotted_ref_collects_only_the_head_not_a_bare_field() {
        let r = extract("Contact.Email <> ''");
        assert_eq!(r.refs, vec!["Contact".to_string()]);
        // A relationship head is listed but is NOT a resolvable field candidate.
        assert!(r.bare_fields.is_empty());
    }

    #[test]
    fn deep_dotted_path_keeps_head_and_does_not_leak_segments() {
        let r = extract("Account.Owner.Manager.Email = 'x'");
        assert_eq!(r.refs, vec!["Account".to_string()]);
        assert!(r.bare_fields.is_empty());
    }

    #[test]
    fn ignores_string_and_numeric_literals() {
        let r = extract("Amount__c > 3.14 && Name = 'ISBLANK(not a call)'");
        assert_eq!(r.refs, vec!["Amount__c".to_string(), "Name".to_string()]);
        assert_eq!(
            r.bare_fields,
            vec!["Amount__c".to_string(), "Name".to_string()]
        );
        assert!(r.system_refs.is_empty());
    }

    #[test]
    fn boolean_and_null_literals_are_not_references() {
        let r = extract("IsActive__c = TRUE || Other__c = NULL || X = false");
        assert_eq!(
            r.refs,
            vec![
                "IsActive__c".to_string(),
                "Other__c".to_string(),
                "X".to_string()
            ]
        );
    }

    #[test]
    fn functions_with_space_before_paren_still_skipped() {
        let r = extract("ISBLANK (Field__c)");
        assert_eq!(r.refs, vec!["Field__c".to_string()]);
    }

    #[test]
    fn multiple_system_refs_captured_separately_and_deduped() {
        let r = extract("$User.Id <> $User.Id && $Setup.MyCS__c.Flag__c");
        assert_eq!(
            r.system_refs,
            vec!["$Setup.MyCS__c.Flag__c".to_string(), "$User.Id".to_string()]
        );
        assert!(r.refs.is_empty());
    }

    #[test]
    fn output_is_sorted_and_deduplicated() {
        let r = extract("Zeta__c + Alpha__c + Zeta__c + Mid__c");
        assert_eq!(
            r.refs,
            vec![
                "Alpha__c".to_string(),
                "Mid__c".to_string(),
                "Zeta__c".to_string()
            ]
        );
    }

    #[test]
    fn does_not_panic_on_garbage() {
        for src in [
            "",
            "   ",
            "$",
            "$$$.$.",
            "'unterminated string",
            "\"also unterminated",
            "Field__c.",
            ".",
            "...",
            "((((",
            "))))",
            "&& || ++ -- == != <= >=",
            "1.2.3.4.5",
            "A.B.C.",
            "ISBLANK(",
            "日本語 && Field__c",
            "\\\\\\",
            "A(",
        ] {
            // The contract is only "no panic"; any recovered refs are fine.
            let _ = extract(src);
        }
    }

    #[test]
    fn mixed_realistic_formula() {
        let r =
            extract("AND(NOT(ISBLANK(Patient__c)), Status__c = 'Open', $Profile.Name = 'Admin')");
        assert_eq!(
            r.refs,
            vec!["Patient__c".to_string(), "Status__c".to_string()]
        );
        assert_eq!(r.system_refs, vec!["$Profile.Name".to_string()]);
    }
}
