//! SQL front end: lossless lexer + CST parser + lowering, wired to the shared IR
//! through the [`LanguageFrontEnd`] seam.
//!
//! SQL is a multi-dialect statement family. The lexer stays purely lossless:
//! every byte is covered, `--` / `/* */` comments and whitespace are trivia,
//! strings (`'...'` with `''` escape), the three quoted-identifier forms, and
//! Postgres dollar-quoted bodies are single tokens, and anything unclassifiable
//! is an `error` token. The parser splits the file into `;`-terminated
//! statements, parsing the DDL headers it maps precisely and keeping everything
//! else as lossless generic statements.
//!
//! The lowering maps `CREATE TABLE` → `Type` (`type_kind table`, with a `columns`
//! property), `CREATE [MATERIALIZED] VIEW` → `Type`, `CREATE FUNCTION`/`PROCEDURE`
//! → `Function`, `CREATE SCHEMA` → `Module`, `FOREIGN KEY … REFERENCES` →
//! `USES_TYPE`, and tokenisable function-body calls → `CALLS`. `CREATE INDEX`/
//! `TRIGGER` and non-DDL statements are kept lossless but emit no graph node
//! (no honest ontology kind). See [`lower`] for the full, honest mapping.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The SQL language front end. Zero-sized: all state lives in the parse trees and
/// the lowering pass.
pub struct SqlFrontEnd;

impl LanguageFrontEnd for SqlFrontEnd {
    fn name(&self) -> &'static str {
        "sql"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["sql"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn module_path(&self, rel_path: &str) -> Vec<String> {
        module_path_for(rel_path)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once to resolve foreign keys and calls by name); merge it
        // into the shared graph the pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

/// Map a repo-relative `.sql` path to its scope segments: the directory
/// components plus the file stem (without the `.sql` extension). A leading `src/`
/// or `sql/` layout root is stripped if present. Each script file is its own leaf
/// scope (SQL has no file→directory module collapse).
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = rel
        .strip_prefix("src/")
        .or_else(|| rel.strip_prefix("sql/"))
        .unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file.strip_suffix(".sql").unwrap_or(file);
    let mut module: Vec<String> = parts.iter().map(|s| s.to_string()).collect();
    module.push(stem.to_string());
    module
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn front_end_identity() {
        let fe = SqlFrontEnd;
        assert_eq!(fe.name(), "sql");
        assert_eq!(fe.extensions(), &["sql"]);
    }

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("schema.sql"), vec!["schema"]);
        assert_eq!(module_path_for("a/b/c.sql"), vec!["a", "b", "c"]);
        assert_eq!(
            module_path_for("sql/migrations/001.sql"),
            vec!["migrations", "001"]
        );
        assert_eq!(module_path_for("src/init.sql"), vec!["init"]);
    }

    /// Lossless round-trip on a representative SQL script exercising line and
    /// block comments, all string/quoted-identifier forms, a dollar-quoted
    /// function body (whose internal `;` must not split the statement), numbers,
    /// Postgres operators, a schema, a table with inline and table-level foreign
    /// keys, a materialized view, an index, and a plain `SELECT`.
    #[test]
    fn parse_round_trips_byte_for_byte() {
        let src = "\
-- trailtracker SQL front-end self-test
/* block /* nested */ comment */
CREATE SCHEMA app AUTHORIZATION admin;

CREATE TABLE app.orgs (
    id    integer PRIMARY KEY,
    name  text NOT NULL
);

CREATE TABLE app.\"User\" (
    id      integer PRIMARY KEY,
    email   text NOT NULL UNIQUE,
    org_id  integer REFERENCES app.orgs (id),
    tags    text DEFAULT 'a,b''c',
    CONSTRAINT fk_org FOREIGN KEY (org_id) REFERENCES app.orgs (id)
);

CREATE MATERIALIZED VIEW app.active AS
    SELECT id, email FROM app.\"User\" WHERE tags @> 'x' AND id < 0xFF;

CREATE OR REPLACE FUNCTION app.greet(name text) RETURNS text AS $body$
    -- body has its own ; and keywords
    SELECT 'hello, ' || name || E'\\n';
$body$ LANGUAGE sql;

CREATE INDEX user_email_idx ON app.\"User\" (email);

SELECT now(), $1, count(*) FROM app.orgs;
";
        let fe = SqlFrontEnd;
        let tree = fe.parse("selftest.sql", src);
        assert!(
            tree.is_lossless(),
            "SQL front end must reconstruct source byte-for-byte"
        );
        let mut rebuilt = String::new();
        tree.root.reconstruct(&tree.source, &mut rebuilt);
        assert_eq!(rebuilt, src);
    }
}
