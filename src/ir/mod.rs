//! The intermediate representation: the language-neutral ontology vocabulary
//! (`ontology`) plus the lowering passes (`lower`) that map each language's
//! lossless CST into it.

pub mod cpg;
pub mod lower;
pub mod ontology;
