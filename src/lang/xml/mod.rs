//! Shared lossless XML layer: lexer + element-tree parser + reading API.
//!
//! **Not a registered front end.** XML on its own carries no code semantics;
//! this module is infrastructure that XML-carried formats build on — the
//! Salesforce metadata front end today (`crate::lang::salesforce`), MSBuild
//! project grammars later (backlog TT-21). A future generic `.xml` front end
//! could lower `File` nodes only, but none is registered yet, so plain `.xml`
//! files remain unclaimed and dispatch behavior for every existing language is
//! untouched.

pub mod lexer;
pub mod parser;
