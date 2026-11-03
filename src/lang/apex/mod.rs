//! Apex front end: lossless lexer + CST parser + lowering, wired to the shared
//! IR through the [`LanguageFrontEnd`] seam.
//!
//! Apex is Java-derived, so this front end is a fork of the Java one
//! ([`crate::lang::java`]) with the Apex adaptations: case-insensitive keywords,
//! `with`/`without`/`inherited sharing` class modifiers, `trigger` declarations,
//! Apex annotations (`@AuraEnabled`, `@InvocableMethod`, `@isTest`, `@future`,
//! `@TestVisible`), and inline SOQL/SOSL (`[SELECT … FROM SObject …]`) captured
//! as bracketed token trees. The lowering maps `class`/`interface`/`enum` →
//! `Type`, methods → `Function` (`HAS_METHOD` from the type), fields/properties →
//! `Constant`, and — in a second pass — reads each inline query's SObject to a
//! `USES_TYPE` edge into an `sobject::<Name>` node whose id matches the Salesforce
//! metadata front end, so Apex and metadata resolve to the same SObject.
//!
//! It claims the `.cls` (class) and `.trigger` (trigger) file extensions.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Apex language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct ApexFrontEnd;

impl LanguageFrontEnd for ApexFrontEnd {
    fn name(&self) -> &'static str {
        "apex"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["cls", "trigger"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn front_end_identity() {
        let fe = ApexFrontEnd;
        assert_eq!(fe.name(), "apex");
        assert_eq!(fe.extensions(), &["cls", "trigger"]);
    }

    #[test]
    fn claims_cls_and_trigger() {
        let fe = ApexFrontEnd;
        assert!(fe.claims("classes/AccountService.cls"));
        assert!(fe.claims("triggers/CaseTrigger.trigger"));
        assert!(!fe.claims("Foo.java"));
        assert!(!fe.claims("Bar.txt"));
    }

    #[test]
    fn lossless_round_trip() {
        let src = "\
// a service class
@RestResource(urlMapping='/x')
public with sharing class ContactService implements Callable {
    private static final Integer LIMIT_N = 50;
    public String label { get; set; }

    @AuraEnabled(cacheable=true)
    public static List<Contact> recent() {
        return [SELECT Id, Name FROM Contact ORDER BY Name LIMIT 10];
    }

    @InvocableMethod(label='Verify')
    public static void verify(List<Id> ids) {
        List<Contact> cs = [SELECT Id FROM Contact WHERE Id IN :ids];
    }
}
";
        let tree = parser::parse("ContactService.cls", src);
        assert!(
            tree.is_lossless(),
            "Apex front end must reconstruct source byte-for-byte"
        );
        // Lowering is deterministic.
        let file = crate::lang::frontend::SourceFile {
            rel_path: "classes/ContactService.cls".to_string(),
            module_path: Vec::new(),
            source: &tree.source,
            root: &tree.root,
        };
        let g1 = lower::lower("apexorg", std::slice::from_ref(&file), &[]);
        let g2 = lower::lower("apexorg", std::slice::from_ref(&file), &[]);
        assert_eq!(g1.to_jsonl(), g2.to_jsonl());
    }
}
