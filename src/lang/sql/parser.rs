//! SQL parser producing the language-neutral lossless CST.
//!
//! Strategy (honest, breadth-growable): SQL is a statement stream terminated by
//! `;`. We parse statement *headers* precisely for the DDL we map into the
//! ontology — `CREATE TABLE`, `CREATE VIEW`, `CREATE FUNCTION`/`PROCEDURE`,
//! `CREATE SCHEMA`, and (named, but not graph-mapped) `CREATE INDEX`/`TRIGGER` —
//! capturing the object name, the parenthesised column/parameter list as a
//! balanced token-tree group, and the remaining body region. Every other
//! statement is captured as a generic `Statement` node: still a precise,
//! lossless run of its real tokens, just not interpreted.
//!
//! Because the lexer tokenises `'...'` strings and `$tag$...$tag$` dollar-quoted
//! bodies as single tokens, the `;` that ends a `CREATE FUNCTION ... $$...$$;`
//! is found at the correct top level even though the body text contains its own
//! `;`. Bodies written with a bare `BEGIN ... END` and internal `;` (the MySQL /
//! T-SQL `DELIMITER` situation) are *not* handled — they split into multiple
//! statements; this is a documented punt and stays fully lossless.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::sql::lexer::{kind as tk, lex};

/// CST node-kind labels. The lowering pass interprets these.
pub mod node {
    pub const SOURCE_FILE: &str = "SourceFile";
    pub const CREATE_TABLE: &str = "CreateTable";
    pub const CREATE_VIEW: &str = "CreateView";
    pub const CREATE_FUNCTION: &str = "CreateFunction";
    pub const CREATE_INDEX: &str = "CreateIndex";
    pub const CREATE_TRIGGER: &str = "CreateTrigger";
    pub const CREATE_SCHEMA: &str = "CreateSchema";
    pub const STATEMENT: &str = "Statement";

    pub const NAME: &str = "Name";
    pub const HEADER: &str = "Header";
    pub const COLUMN_LIST: &str = "ColumnList";
    pub const PARAMS: &str = "Params";
    pub const BODY: &str = "Body";

    pub const PAREN: &str = "Paren";
    pub const BRACKET: &str = "Bracket";
    pub const BRACE: &str = "Brace";
}

/// Maximum nesting depth before the parser stops recursing and consumes the
/// remaining group iteratively. A `catch_unwind` cannot catch a stack overflow,
/// so this guard is the real defense against hostile delimiter nesting. Mirrors
/// the Rust front end's cap.
const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = SqlParser {
        src: source,
        toks,
        i: 0,
        diags: Vec::new(),
        depth: 0,
    };
    let root = p.parse_source_file();
    ParseTree {
        source_id: SourceId::from_path(path),
        path: path.to_string(),
        source: source.to_string(),
        root,
        diagnostics: p.diags,
    }
}

struct SqlParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    /// Current structural recursion depth, capped at [`MAX_DEPTH`].
    depth: usize,
}

impl<'s> SqlParser<'s> {
    // --- cursor primitives --------------------------------------------------

    /// Append the current token (trivia or not) to `out` and advance.
    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    /// Move consecutive leading trivia tokens into `out`.
    fn ws(&mut self, out: &mut Vec<Child>) {
        while self.i < self.toks.len() && self.toks[self.i].trivia {
            self.eat(out);
        }
    }

    /// Kind of the next significant token (no borrow of source).
    fn peek_kind(&self) -> Option<&'static str> {
        self.peek_kind_n(0)
    }

    fn peek_kind_n(&self, n: usize) -> Option<&'static str> {
        let mut j = self.i;
        let mut count = 0;
        while j < self.toks.len() {
            if self.toks[j].trivia {
                j += 1;
                continue;
            }
            if count == n {
                return Some(self.toks[j].kind);
            }
            count += 1;
            j += 1;
        }
        None
    }

    /// Text of the n-th significant token from the cursor.
    fn peek_n_text(&self, n: usize) -> Option<&str> {
        let mut j = self.i;
        let mut count = 0;
        while j < self.toks.len() {
            if self.toks[j].trivia {
                j += 1;
                continue;
            }
            if count == n {
                return Some(self.toks[j].span.text(self.src));
            }
            count += 1;
            j += 1;
        }
        None
    }

    /// Case-insensitive match of the next significant token's text (SQL keywords
    /// and bare identifiers are case-insensitive; punctuation matches verbatim).
    fn at(&self, s: &str) -> bool {
        match self.peek_n_text(0) {
            Some(t) => t.eq_ignore_ascii_case(s),
            None => false,
        }
    }

    fn at_n(&self, n: usize, s: &str) -> bool {
        match self.peek_n_text(n) {
            Some(t) => t.eq_ignore_ascii_case(s),
            None => false,
        }
    }

    fn at_any(&self, options: &[&str]) -> bool {
        options.iter().any(|s| self.at(s))
    }

    fn at_open(&self) -> bool {
        self.at("(") || self.at("[") || self.at("{")
    }

    fn at_name_token(&self) -> bool {
        matches!(self.peek_kind(), Some(k) if k == tk::IDENT || k == tk::QUOTED_IDENT)
    }

    fn name_token_at(&self, n: usize) -> bool {
        matches!(self.peek_kind_n(n), Some(k) if k == tk::IDENT || k == tk::QUOTED_IDENT)
    }

    fn cur_offset(&self) -> usize {
        self.toks
            .get(self.i)
            .map(|t| t.span.start as usize)
            .unwrap_or(self.src.len())
    }

    fn make_node(&self, kind: &'static str, children: Vec<Child>) -> Node {
        let span =
            children_span(&children).unwrap_or_else(|| ByteSpan::empty_at(self.cur_offset()));
        Node::new(kind, span, children)
    }

    // --- top level ----------------------------------------------------------

    fn parse_source_file(&mut self) -> Node {
        let mut c = Vec::new();
        loop {
            self.ws(&mut c);
            if self.peek_kind().is_none() {
                break;
            }
            let stmt = self.parse_statement();
            c.push(Child::Node(stmt));
        }
        self.make_node(node::SOURCE_FILE, c)
    }

    fn parse_statement(&mut self) -> Node {
        let mut c = Vec::new();
        self.ws(&mut c);
        if self.at("create") {
            return self.parse_create(c);
        }
        // Any other statement: a precise, lossless run of its tokens, terminated
        // by the next top-level `;` (or EOF). Always consumes ≥1 significant
        // token, so the source-file loop is guaranteed to make progress.
        self.collect_until_semicolon(&mut c);
        self.make_node(node::STATEMENT, c)
    }

    fn parse_create(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // CREATE

        // Optional modifiers in any order: OR REPLACE, TEMP[ORARY], UNIQUE,
        // MATERIALIZED, GLOBAL/LOCAL, UNLOGGED, RECURSIVE.
        loop {
            self.ws(&mut c);
            if self.at_any(&[
                "or",
                "replace",
                "temp",
                "temporary",
                "unique",
                "materialized",
                "global",
                "local",
                "unlogged",
                "recursive",
            ]) {
                self.eat(&mut c);
            } else {
                break;
            }
        }

        self.ws(&mut c);
        if self.at("table") {
            self.finish_create_table(c)
        } else if self.at("view") {
            self.finish_create_view(c)
        } else if self.at("function") || self.at("procedure") {
            self.finish_create_function(c)
        } else if self.at("schema") {
            self.finish_create_schema(c)
        } else if self.at("index") {
            self.finish_named_stmt(c, node::CREATE_INDEX)
        } else if self.at("trigger") {
            self.finish_named_stmt(c, node::CREATE_TRIGGER)
        } else {
            // Unknown CREATE … target — keep it lossless as a generic statement.
            self.collect_until_semicolon(&mut c);
            self.make_node(node::STATEMENT, c)
        }
    }

    fn finish_create_table(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // TABLE
        self.skip_if_not_exists(&mut c);
        self.ws(&mut c);
        if let Some(name) = self.qualified_name() {
            c.push(Child::Node(name));
        }
        self.ws(&mut c);
        if self.at("(") {
            let cols = self.parse_delimited(Some(node::COLUMN_LIST));
            c.push(Child::Node(cols));
        }
        // Trailing table options (e.g. `WITH (...)`, `AS SELECT …`) until `;`.
        if let Some(h) = self.collect_region(node::HEADER, &[";"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::CREATE_TABLE, c)
    }

    fn finish_create_view(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // VIEW
        self.skip_if_not_exists(&mut c);
        self.ws(&mut c);
        if let Some(name) = self.qualified_name() {
            c.push(Child::Node(name));
        }
        // Optional explicit column list `(a, b)`.
        self.ws(&mut c);
        if self.at("(") {
            let g = self.parse_delimited(Some(node::PAREN));
            c.push(Child::Node(g));
        }
        // The `AS SELECT …` body, up to the terminating `;`.
        if let Some(b) = self.collect_region(node::BODY, &[";"]) {
            c.push(Child::Node(b));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::CREATE_VIEW, c)
    }

    fn finish_create_function(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // FUNCTION | PROCEDURE
        self.skip_if_not_exists(&mut c);
        self.ws(&mut c);
        if let Some(name) = self.qualified_name() {
            c.push(Child::Node(name));
        }
        self.ws(&mut c);
        if self.at("(") {
            let params = self.parse_delimited(Some(node::PARAMS));
            c.push(Child::Node(params));
        }
        // Everything up to the top-level `;` (dollar-quoted / single-quoted
        // bodies keep their own `;` inside a single string token).
        if let Some(b) = self.collect_region(node::BODY, &[";"]) {
            c.push(Child::Node(b));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::CREATE_FUNCTION, c)
    }

    fn finish_create_schema(&mut self, mut c: Vec<Child>) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // SCHEMA
        self.skip_if_not_exists(&mut c);
        self.ws(&mut c);
        if let Some(name) = self.qualified_name() {
            c.push(Child::Node(name));
        }
        // `AUTHORIZATION user`, etc., up to `;`. (The rare standard form where a
        // schema embeds element statements without intervening `;` is punted —
        // those split into following statements, still lossless.)
        if let Some(h) = self.collect_region(node::HEADER, &[";"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(node::CREATE_SCHEMA, c)
    }

    /// `CREATE [UNIQUE] INDEX name ON …` / `CREATE TRIGGER name …` — a named DDL
    /// statement the lowering keeps lossless but does not map to an ontology node
    /// (there is no honest Index/Trigger kind).
    fn finish_named_stmt(&mut self, mut c: Vec<Child>, label: &'static str) -> Node {
        self.ws(&mut c);
        self.eat(&mut c); // INDEX | TRIGGER
        self.skip_if_not_exists(&mut c);
        self.ws(&mut c);
        if let Some(name) = self.qualified_name() {
            c.push(Child::Node(name));
        }
        if let Some(h) = self.collect_region(node::HEADER, &[";"]) {
            c.push(Child::Node(h));
        }
        self.ws(&mut c);
        if self.at(";") {
            self.eat(&mut c);
        }
        self.make_node(label, c)
    }

    // --- shared helpers -----------------------------------------------------

    fn skip_if_not_exists(&mut self, c: &mut Vec<Child>) {
        if self.at("if") && self.at_n(1, "not") && self.at_n(2, "exists") {
            self.ws(c);
            self.eat(c); // IF
            self.ws(c);
            self.eat(c); // NOT
            self.ws(c);
            self.eat(c); // EXISTS
        }
    }

    /// Parse a possibly schema-qualified name `ident ( . ident )*` (each segment
    /// may be a quoted identifier) into a `Name` node. The caller has already
    /// moved leading trivia into its own child list, so the cursor sits on the
    /// first name token. Returns `None` if not at a name token.
    fn qualified_name(&mut self) -> Option<Node> {
        if !self.at_name_token() {
            return None;
        }
        let mut c = Vec::new();
        self.eat(&mut c); // first segment
        loop {
            if self.at(".") && self.name_token_at(1) {
                self.ws(&mut c);
                self.eat(&mut c); // .
                self.ws(&mut c);
                self.eat(&mut c); // segment
            } else {
                break;
            }
        }
        Some(self.make_node(node::NAME, c))
    }

    /// Collect tokens (descending into balanced groups) until a significant stop
    /// token at delimiter depth 0. Used for header/body regions.
    fn collect_region(&mut self, label: &'static str, stops: &[&str]) -> Option<Node> {
        let mut c = Vec::new();
        loop {
            if self.peek_kind().is_none() {
                break;
            }
            if stops.iter().any(|s| self.at(s)) {
                break;
            }
            if self.at_open() {
                self.ws(&mut c);
                let inner = self.parse_delimited(None);
                c.push(Child::Node(inner));
            } else {
                self.ws(&mut c);
                self.eat(&mut c);
            }
        }
        if c.is_empty() {
            None
        } else {
            Some(self.make_node(label, c))
        }
    }

    /// Consume a run of tokens (descending into balanced groups) up to and
    /// including the next top-level `;` (or EOF). Always advances on a non-empty
    /// significant stream.
    fn collect_until_semicolon(&mut self, c: &mut Vec<Child>) {
        loop {
            self.ws(c);
            match self.peek_kind() {
                None => break,
                Some(_) if self.at(";") => {
                    self.eat(c);
                    break;
                }
                Some(_) if self.at_open() => {
                    let g = self.parse_delimited(None);
                    c.push(Child::Node(g));
                }
                Some(_) => self.eat(c),
            }
        }
    }

    /// Parse a balanced delimiter group `(...)`, `[...]`, or `{...}`. (In SQL the
    /// lexer captures `[...]` as a quoted-identifier token, so in practice only
    /// `(` opens a group here; the others are supported defensively.)
    fn parse_delimited(&mut self, label_override: Option<&'static str>) -> Node {
        let mut g = Vec::new();
        self.ws(&mut g);
        let (close, default_label) = if self.at("(") {
            (")", node::PAREN)
        } else if self.at("[") {
            ("]", node::BRACKET)
        } else if self.at("{") {
            ("}", node::BRACE)
        } else {
            // Defensive: not actually at an opener.
            return self.make_node(label_override.unwrap_or(node::STATEMENT), g);
        };
        let label = label_override.unwrap_or(default_label);
        self.eat(&mut g); // opener
        loop {
            self.ws(&mut g);
            if self.peek_kind().is_none() {
                break; // unterminated; still lossless
            }
            if self.at(close) {
                self.eat(&mut g);
                break;
            }
            if self.at_open() {
                if self.depth < MAX_DEPTH {
                    self.depth += 1;
                    let inner = self.parse_delimited(None);
                    self.depth -= 1;
                    g.push(Child::Node(inner));
                } else {
                    // Depth cap: flatten the nested group into this one rather
                    // than recursing. Lossless; protects against stack overflow.
                    self.eat(&mut g); // opener
                    self.consume_balanced_flat(&mut g);
                    self.note_depth_limit();
                }
            } else {
                self.eat(&mut g);
            }
        }
        self.make_node(label, g)
    }

    /// Iteratively consume a balanced delimiter run (the opener already eaten),
    /// appending every token as a flat leaf. Used at the depth cap so arbitrarily
    /// deep nesting is handled without further recursion.
    fn consume_balanced_flat(&mut self, out: &mut Vec<Child>) {
        let mut balance: i32 = 1;
        while balance > 0 {
            self.ws(out);
            if self.peek_kind().is_none() {
                break;
            }
            if self.at("(") || self.at("[") || self.at("{") {
                balance += 1;
            } else if self.at(")") || self.at("]") || self.at("}") {
                balance -= 1;
            }
            self.eat(out);
        }
    }

    fn note_depth_limit(&mut self) {
        self.diags.push(Diagnostic {
            code: "sql.depth_limit",
            message: format!("nesting depth limit ({MAX_DEPTH}) reached; group flattened"),
            span: ByteSpan::empty_at(self.cur_offset()),
        });
    }
}

fn children_span(children: &[Child]) -> Option<ByteSpan> {
    let mut it = children.iter().map(child_span);
    let first = it.next()?;
    Some(it.fold(first, |a, b| a.merge(b)))
}

fn child_span(c: &Child) -> ByteSpan {
    match c {
        Child::Node(n) => n.span,
        Child::Token(t) => t.span,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_and_is_lossless() {
        let src = "\
-- schema setup
CREATE SCHEMA app;

CREATE TABLE app.users (
    id      integer PRIMARY KEY,
    email   text NOT NULL UNIQUE,
    org_id  integer REFERENCES app.orgs (id)
);

CREATE MATERIALIZED VIEW active_users AS
    SELECT id, email FROM app.users WHERE active = true;

CREATE OR REPLACE FUNCTION app.greet(name text) RETURNS text AS $$
    SELECT 'hello, ' || name;
$$ LANGUAGE sql;

CREATE INDEX users_email_idx ON app.users (email);
";
        let tree = parse("schema.sql", src);
        assert!(tree.is_lossless(), "tree must reconstruct source");
    }

    #[test]
    fn finds_top_level_statements() {
        let src = "CREATE TABLE t (id int); CREATE VIEW v AS SELECT 1; \
                   CREATE FUNCTION f() RETURNS int AS $$ SELECT 1 $$ LANGUAGE sql; \
                   CREATE SCHEMA s; SELECT 1;";
        let tree = parse("t.sql", src);
        let kinds: Vec<&str> = tree.root.child_nodes().map(|n| n.kind).collect();
        assert!(kinds.contains(&node::CREATE_TABLE));
        assert!(kinds.contains(&node::CREATE_VIEW));
        assert!(kinds.contains(&node::CREATE_FUNCTION));
        assert!(kinds.contains(&node::CREATE_SCHEMA));
        assert!(kinds.contains(&node::STATEMENT));
    }

    #[test]
    fn table_name_and_column_list_captured() {
        let tree = parse("t.sql", "CREATE TABLE public.t (a int, b text);");
        let table = tree
            .root
            .child_nodes()
            .find(|n| n.kind == node::CREATE_TABLE)
            .expect("a table statement");
        let name = table.child(node::NAME).expect("a name");
        // Qualified name keeps both segments (`public` and `t`).
        let name_text: String = name
            .tokens()
            .map(|t| t.span.text(&tree.source).to_string())
            .collect();
        assert_eq!(name_text, "public.t");
        assert!(table.child(node::COLUMN_LIST).is_some());
    }

    #[test]
    fn pathological_nesting_does_not_overflow() {
        // Far deeper than MAX_DEPTH; must not stack-overflow and must stay lossless.
        let depth = 10_000;
        let src = format!(
            "CREATE TABLE t (x int CHECK ({}{}));",
            "(".repeat(depth),
            ")".repeat(depth)
        );
        let tree = parse("deep.sql", &src);
        assert!(tree.is_lossless(), "deeply nested input must round-trip");
        assert!(
            tree.diagnostics.iter().any(|d| d.code == "sql.depth_limit"),
            "depth limit should be reported, not silent"
        );
    }
}
