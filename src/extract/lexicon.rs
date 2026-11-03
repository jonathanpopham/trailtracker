//! The lexicon extractor: recover the **vocabulary** of a codebase from the
//! base graph.
//!
//! The Lexicon is the keystone semantic ontology (roadmap tier 4): archetype
//! detection and domain classification both stand on it. Before either can
//! exist, TrailTracker needs to know *which words this codebase speaks* — the
//! tokens hiding inside its identifiers, and whether each token names a
//! structural **role** (`service`, `repository`, `handler`, …) or a domain
//! **concept** (`order`, `basket`, `payment`, …).
//!
//! The pass:
//!
//! - **Tokenize** every symbol identifier — [`Type`], [`Function`] and
//!   [`Constant`] node names, plus [`File`] stems — splitting PascalCase,
//!   camelCase, snake_case, kebab-case, acronym runs (`HTTPServer` →
//!   `http`/`server`) and letter↔digit boundaries into lowercase subtokens. A
//!   leading interface `I` before an uppercase letter is stripped
//!   (`IOrderRepository` → `order`, `repository`). Tokens shorter than two
//!   characters, pure digits, and [`STOPWORDS`] are dropped.
//! - **Count** token frequency across the whole graph.
//! - **Classify** each token into one of **three classes**: **role** if it
//!   appears in the curated [`ROLE_TOKENS`] table, else **generic** if it
//!   appears in the curated [`GENERIC_TOKENS`] table (programming-language
//!   filler like `async`/`id`/`type`/`status` that names neither a role nor a
//!   domain thing), else **concept**. All tables are `const` data — extending
//!   the vocabulary is an edit to a sorted table, never new code.
//! - **Emit** a derived token-table graph: one node per distinct token (kind
//!   [`Constant`], tagged `view: "lexicon"`) with `token`, `count` and
//!   `token_class` (`"role"` | `"generic"` | `"concept"`) properties. No
//!   edges — a clean, loadable word list.
//!
//! The three-way split exists because domain seeding consumes the `concept`
//! class: on real corpora (eShop), two-class output let `async`, `id`,
//! `type`, `name`, `status`, `changed`, `create` outrank genuine domain
//! nouns like `order`, `catalog`, `basket` and `buyer`. Generic tokens are
//! still counted and emitted — they are simply never domain evidence.
//!
//! Like every extractor, this is a pure, deterministic function of the base
//! graph: it walks the `BTreeMap`-ordered node iterator, counts into a
//! `BTreeMap`, and writes through the sorted, de-duplicating [`Graph`] API, so
//! the output is byte-stable across runs. Curated tables only; **never an
//! LLM** (see `docs/lexicon.md`).
//!
//! [`Type`]: crate::ir::ontology::node::TYPE
//! [`Function`]: crate::ir::ontology::node::FUNCTION
//! [`Constant`]: crate::ir::ontology::node::CONSTANT
//! [`File`]: crate::ir::ontology::node::FILE

use std::collections::BTreeMap;

use crate::core::json::Json;
use crate::graph::Graph;
use crate::ir::ontology::node as ont;

use super::Extractor;

/// Property key marking a node as belonging to the lexicon view.
const VIEW: &str = "lexicon";

/// Tokens that carry no vocabulary signal: bare accessors/mutators, glue
/// particles, and structural filler (including throwaway file stems such as
/// `mod` and `index`). **Must stay sorted and unique** — membership is a
/// binary search, and a test enforces the invariant. Extend by inserting in
/// order.
const STOPWORDS: &[&str] = &[
    "add", "and", "at", "base", "by", "do", "for", "from", "get", "has", "impl", "in", "index",
    "is", "lib", "main", "mod", "new", "not", "of", "on", "remove", "set", "src", "the", "to",
    "with",
];

/// Tokens naming a structural **role** — how a symbol participates in the
/// architecture rather than what domain thing it is about. Checked first
/// during classification; everything not here falls through to
/// [`GENERIC_TOKENS`] and then to **concept**. **Must stay sorted and
/// unique** (binary-searched, test-enforced). Extend by inserting in order.
const ROLE_TOKENS: &[&str] = &[
    "aggregate",
    "api",
    "attribute",
    "builder",
    "client",
    "command",
    "config",
    "configuration",
    "context",
    "controller",
    "controllerbase",
    "dto",
    "entity",
    "event",
    "exception",
    "extension",
    "extensions",
    "factory",
    "filter",
    "handler",
    "helper",
    "hub",
    "job",
    "listener",
    "manager",
    "mapper",
    "middleware",
    "mock",
    "model",
    "module",
    "options",
    "provider",
    "query",
    "repository",
    "request",
    "response",
    "service",
    "store",
    "test",
    "tests",
    "util",
    "utils",
    "validator",
    "valueobject",
    "view",
    "viewmodel",
    "worker",
];

/// Language/programming-**generic** tokens: identifier filler that names
/// neither a structural role nor a domain concept — CRUD/mutation verbs
/// (`create`, `changed`), type-system noise (`type`, `enum`, `abstract`),
/// bare attribute words (`id`, `name`, `status`, `value`), collection words
/// (`list`, `map`, `keys`) and language keywords (`async`, `await`,
/// `sealed`, `partial`). Evidenced on eShop: without this class, `async`,
/// `id`, `type`, `status` and `changed` outranked real domain nouns.
/// The cross-language corpus (Q-LEX-1) added per-language keyword noise:
/// Python (`init` from `__init__`, `self`, `cls`, `def`, `lambda`, `none`),
/// Rust (`mut`, `pub`, `fn`, `trait`, `dyn`), Go (`func`, `nil`, `chan`),
/// JS/TS (`constructor`, `exports`, `returns`, `throws`, `undefined`,
/// `prototype`), plus `no`, `new` and `dispose` — all leaked as top
/// "concepts" on django/hugo/alacritty/nest before this table caught them.
///
/// Curation rules: true domain nouns stay OUT (`order`, `basket`, `item`,
/// `buyer` are concepts, even though the plural `items` is usually list
/// plumbing); tokens already in [`ROLE_TOKENS`] stay out (role wins — a
/// disjointness test enforces it). Some entries duplicate [`STOPWORDS`]
/// (`get`, `add`, `to`, …) on purpose: `tokenize` drops those before
/// classification, but [`classify_token`] is public and must answer sensibly
/// for raw tokens that never went through `tokenize`. **Must stay sorted and
/// unique** (binary-searched, test-enforced). Extend by inserting in order.
const GENERIC_TOKENS: &[&str] = &[
    "a",
    "abstract",
    "add",
    "an",
    "and",
    "args",
    "async",
    "await",
    "base",
    "bool",
    "chan",
    "change",
    "changed",
    "class",
    "cls",
    "constructor",
    "count",
    "create",
    "created",
    "data",
    "def",
    "default",
    "delete",
    "deleted",
    "disable",
    "dispose",
    "dyn",
    "enable",
    "enum",
    "exports",
    "false",
    "fn",
    "from",
    "func",
    "get",
    "has",
    "id",
    "ids",
    "impl",
    "index",
    "info",
    "init",
    "int",
    "interface",
    "is",
    "items",
    "key",
    "keys",
    "lambda",
    "list",
    "map",
    "models",
    "mut",
    "name",
    "names",
    "new",
    "nil",
    "no",
    "none",
    "null",
    "object",
    "of",
    "or",
    "param",
    "params",
    "partial",
    "prototype",
    "pub",
    "remove",
    "result",
    "results",
    "returns",
    "sealed",
    "self",
    "set",
    "status",
    "string",
    "struct",
    "the",
    "throws",
    "to",
    "trait",
    "true",
    "type",
    "types",
    "undefined",
    "update",
    "updated",
    "value",
    "values",
    "views",
    "void",
];

/// Recover the codebase's vocabulary: a classified, counted token table.
pub struct LexiconExtractor;

impl Extractor for LexiconExtractor {
    fn name(&self) -> &'static str {
        "lexicon"
    }

    fn extract(&self, graph: &Graph) -> Graph {
        // Count token frequency over every symbol identifier. `BTreeMap`
        // keeps the table sorted; counting is order-independent, so the
        // result is a pure function of the node set.
        let mut counts: BTreeMap<String, u64> = BTreeMap::new();
        for n in graph.nodes() {
            let name: &str = match n.kind {
                ont::TYPE | ont::FUNCTION | ont::CONSTANT => &n.name,
                ont::FILE => file_stem(&n.name),
                _ => continue,
            };
            for token in tokenize(name) {
                *counts.entry(token).or_insert(0) += 1;
            }
        }

        // Emit one node per distinct token. The base graph is never mutated;
        // the derived graph is a clean token table with no edges.
        let mut out = Graph::new();
        for (token, count) in &counts {
            let class = classify_token(token);
            out.upsert_node(
                format!("token::{token}"),
                ont::CONSTANT,
                token.clone(),
                vec![
                    ("view", Json::str(VIEW)),
                    ("token", Json::str(token.clone())),
                    ("count", Json::U64(*count)),
                    ("token_class", Json::str(class)),
                ],
            );
        }
        out
    }
}

/// Split an identifier into lowercase subtokens.
///
/// Non-alphanumeric characters (`_`, `-`, `.`, `::`, spaces, …) separate
/// segments; each segment is then split on case and digit boundaries
/// (PascalCase, camelCase, acronym runs, letter↔digit). A leading interface
/// `I` before an uppercase letter is stripped per segment. Tokens shorter
/// than two characters, pure digits, and [`STOPWORDS`] are dropped.
pub fn tokenize(name: &str) -> Vec<String> {
    let mut out = Vec::new();
    for segment in name.split(|c: char| !c.is_ascii_alphanumeric()) {
        if segment.is_empty() {
            continue;
        }
        for word in split_case_boundaries(strip_interface_prefix(segment)) {
            let token = word.to_ascii_lowercase();
            if token.len() < 2
                || token.bytes().all(|b| b.is_ascii_digit())
                || STOPWORDS.binary_search(&token.as_str()).is_ok()
            {
                continue;
            }
            out.push(token);
        }
    }
    out
}

/// Classify a token (already lowercased, as produced by [`tokenize`]) into
/// one of the three lexicon classes: `"role"` if it names a structural role,
/// `"generic"` if it is language/programming filler, `"concept"` otherwise.
/// Role wins over generic — the tables are disjoint and a test enforces it.
/// Public so downstream passes (domain seeding, archetype detection) reuse
/// the exact same judgment instead of re-deriving it.
pub fn classify_token(token: &str) -> &'static str {
    if ROLE_TOKENS.binary_search(&token).is_ok() {
        "role"
    } else if GENERIC_TOKENS.binary_search(&token).is_ok() {
        "generic"
    } else {
        "concept"
    }
}

/// Strip a leading interface `I` when it prefixes an uppercase letter
/// (`IOrderRepository` → `OrderRepository`). Two-character segments such as
/// `IO` or `ID` are left intact — a bare acronym is not an interface marker.
fn strip_interface_prefix(segment: &str) -> &str {
    let b = segment.as_bytes();
    if b.len() >= 3 && b[0] == b'I' && b[1].is_ascii_uppercase() {
        &segment[1..]
    } else {
        segment
    }
}

/// Split an ASCII-alphanumeric segment on case and digit boundaries:
/// lower→Upper (`orderService`), acronym end (`HTTPServer` → `HTTP`/`Server`),
/// and letter↔digit transitions (`json2xml` → `json`/`2`/`xml`).
fn split_case_boundaries(segment: &str) -> Vec<&str> {
    let b = segment.as_bytes();
    let mut words = Vec::new();
    let mut start = 0;
    for i in 1..b.len() {
        let (prev, cur) = (b[i - 1], b[i]);
        let next_is_lower = b.get(i + 1).is_some_and(|c| c.is_ascii_lowercase());
        let boundary = (prev.is_ascii_lowercase() && cur.is_ascii_uppercase())
            || (prev.is_ascii_digit() && cur.is_ascii_alphabetic())
            || (prev.is_ascii_alphabetic() && cur.is_ascii_digit())
            || (prev.is_ascii_uppercase() && cur.is_ascii_uppercase() && next_is_lower);
        if boundary {
            words.push(&segment[start..i]);
            start = i;
        }
    }
    words.push(&segment[start..]);
    words
}

/// The stem of a file path: the final path component with the **last**
/// extension removed (`src/Basket/BasketService.cs` → `BasketService`).
///
/// Only the final `.ext` is treated as extension so multi-dot conventions
/// keep their vocabulary: `order.service.rs` → `order.service`, whose inner
/// dot [`tokenize`] then splits into `order` + `service` (role evidence the
/// old first-dot truncation silently dropped — UBS audit C5). Dotfiles
/// (`.gitignore`) still stem to `""` as before.
fn file_stem(path: &str) -> &str {
    let base = path.rsplit(['/', '\\']).next().unwrap_or(path);
    match base.rfind('.') {
        Some(dot) => &base[..dot],
        None => base,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tables_are_sorted_and_unique() {
        for (name, table) in [
            ("STOPWORDS", STOPWORDS),
            ("ROLE_TOKENS", ROLE_TOKENS),
            ("GENERIC_TOKENS", GENERIC_TOKENS),
        ] {
            for pair in table.windows(2) {
                assert!(
                    pair[0] < pair[1],
                    "{name} must stay sorted+unique: {:?} !< {:?}",
                    pair[0],
                    pair[1]
                );
            }
        }
    }

    #[test]
    fn role_and_generic_tables_are_disjoint() {
        // Role wins during classification, so a token in both tables would be
        // a dead GENERIC_TOKENS entry — a curation bug, not a tie-break.
        for token in GENERIC_TOKENS {
            assert!(
                ROLE_TOKENS.binary_search(token).is_err(),
                "{token:?} is in both ROLE_TOKENS and GENERIC_TOKENS"
            );
        }
    }

    #[test]
    fn tokenizes_interface_prefix() {
        assert_eq!(tokenize("IOrderRepository"), ["order", "repository"]);
        // A bare two-letter acronym is not an interface marker.
        assert_eq!(tokenize("IO"), ["io"]);
    }

    #[test]
    fn tokenizes_pascal_case_keeping_crud_verbs() {
        // Decision: CRUD verbs (`create`, `update`, `delete`) survive
        // `tokenize` — they are countable vocabulary — but they classify as
        // `generic`, not `concept`: a CreateOrderCommand is *about* orders,
        // and "create" must never seed a domain. Bare accessors (`get`/`set`)
        // remain stopwords and are dropped outright.
        assert_eq!(
            tokenize("CreateOrderCommandHandler"),
            ["create", "order", "command", "handler"]
        );
    }

    #[test]
    fn tokenizes_snake_case_dropping_stopwords_and_short_tokens() {
        assert_eq!(tokenize("get_user_id"), ["user", "id"]);
        // Single characters and pure digits are dropped.
        assert_eq!(tokenize("x_42_y"), Vec::<String>::new());
    }

    #[test]
    fn tokenizes_kebab_acronyms_and_digit_boundaries() {
        assert_eq!(tokenize("order-service"), ["order", "service"]);
        assert_eq!(tokenize("HTTPServer"), ["http", "server"]);
        assert_eq!(tokenize("json2Xml"), ["json", "xml"]);
    }

    #[test]
    fn file_stem_strips_only_the_last_extension() {
        // UBS audit C5: first-dot truncation dropped role vocabulary from
        // multi-dot conventions (`*.service.ts`, `*.controller.ts`, …).
        assert_eq!(file_stem("dots/src/order.service.rs"), "order.service");
        assert_eq!(file_stem("src/foo.controller.ts"), "foo.controller");
        assert_eq!(file_stem("a.b.c.py"), "a.b.c");
        assert_eq!(file_stem("src/plain.rs"), "plain");
        assert_eq!(file_stem("noext"), "noext");
        assert_eq!(file_stem("src\\win\\Basket.Service.cs"), "Basket.Service");
        // Dotfiles keep the old behavior: empty stem, no tokens.
        assert_eq!(file_stem(".gitignore"), "");
    }

    #[test]
    fn multi_dot_file_stems_keep_role_evidence() {
        // End-to-end through the extractor: `order.service.rs` must yield
        // both `order` (concept) and `service` (role).
        let mut g = Graph::new();
        g.upsert_node(
            "file::src/order.service.rs",
            ont::FILE,
            "src/order.service.rs",
            vec![],
        );
        let derived = LexiconExtractor.extract(&g);
        assert_eq!(class_and_count(&derived, "order"), ("concept".into(), 1));
        assert_eq!(class_and_count(&derived, "service"), ("role".into(), 1));
        // The extension itself never becomes a token.
        assert!(!derived.has_node("token::rs"));
    }

    #[test]
    fn classifies_roles_generics_and_concepts() {
        for role in ["service", "repository", "command", "event"] {
            assert_eq!(classify_token(role), "role", "{role} must be a role");
        }
        for generic in [
            "async", "id", "type", "status", "create", "name", "changed", "items", "value", "data",
            "info", "result",
        ] {
            assert_eq!(
                classify_token(generic),
                "generic",
                "{generic} must be generic"
            );
        }
        for concept in [
            "order", "catalog", "basket", "buyer", "item", "payment", "identity", "webhook",
        ] {
            assert_eq!(
                classify_token(concept),
                "concept",
                "{concept} must be a concept"
            );
        }
    }

    #[test]
    fn cross_language_keywords_are_generic_not_concepts() {
        // Q-LEX-1: these leaked as top "concepts" on the cross-language
        // corpus (django `init`/`no`, alacritty `mut`, nest `constructor`,
        // Radarr `exports`, bitwarden `returns`/`throws`).
        for generic in [
            "init",
            "mut",
            "constructor",
            "exports",
            "no",
            "impl",
            "fn",
            "pub",
            "def",
            "func",
            "self",
            "cls",
            "async",
            "await",
            "new",
            "dispose",
            "returns",
            "throws",
            "none",
            "nil",
            "trait",
            "lambda",
            "undefined",
            "prototype",
        ] {
            assert_eq!(
                classify_token(generic),
                "generic",
                "{generic} must be generic"
            );
        }
        // Real domain nouns from the explore repos stay concepts.
        for concept in ["page", "cursor", "registry", "field", "selection"] {
            assert_eq!(
                classify_token(concept),
                "concept",
                "{concept} must stay a concept"
            );
        }
    }

    /// A hand-built base graph shaped like eShop: interface + service +
    /// command + integration-event types, a file whose stem repeats a type
    /// name, and a Package node that must NOT contribute tokens.
    fn eshop_base() -> Graph {
        let mut g = Graph::new();
        for (id, name) in [
            ("type::IOrderRepository", "IOrderRepository"),
            ("type::OrderingService", "OrderingService"),
            ("type::CreateOrderCommand", "CreateOrderCommand"),
            (
                "type::OrderPlacedIntegrationEvent",
                "OrderPlacedIntegrationEvent",
            ),
            ("type::CatalogItem", "CatalogItem"),
            ("type::BasketService", "BasketService"),
        ] {
            g.upsert_node(id, ont::TYPE, name, vec![]);
        }
        g.upsert_node(
            "file::src/Basket/BasketService.cs",
            ont::FILE,
            "src/Basket/BasketService.cs",
            vec![],
        );
        // Packages are not symbol identifiers: contributes nothing.
        g.upsert_node(
            "pkg::PaymentGateway",
            ont::PACKAGE,
            "PaymentGateway",
            vec![],
        );
        g
    }

    /// Look up a token node and return (token_class, count).
    fn class_and_count(derived: &Graph, token: &str) -> (String, u64) {
        let n = derived
            .nodes()
            .find(|n| n.id == format!("token::{token}"))
            .unwrap_or_else(|| panic!("token::{token} must be emitted"));
        assert_eq!(n.kind, ont::CONSTANT);
        assert_eq!(n.props.get("view"), Some(&Json::str(VIEW)));
        assert_eq!(n.props.get("token"), Some(&Json::str(token)));
        let Some(Json::Str(class)) = n.props.get("token_class") else {
            panic!("token::{token} must carry token_class");
        };
        let Some(Json::U64(count)) = n.props.get("count") else {
            panic!("token::{token} must carry count");
        };
        (class.clone(), *count)
    }

    #[test]
    fn emits_classified_counted_token_table_for_eshop_graph() {
        let base = eshop_base();
        let derived = LexiconExtractor.extract(&base);

        // Concepts: `order` from IOrderRepository + CreateOrderCommand +
        // OrderPlacedIntegrationEvent; `basket` from the type and the file
        // stem; `catalog` and `item` from CatalogItem.
        assert_eq!(class_and_count(&derived, "order"), ("concept".into(), 3));
        assert_eq!(class_and_count(&derived, "basket"), ("concept".into(), 2));
        assert_eq!(class_and_count(&derived, "catalog"), ("concept".into(), 1));
        assert_eq!(class_and_count(&derived, "item"), ("concept".into(), 1));

        // Generic: `create` from CreateOrderCommand is counted but marked
        // generic — it must never rank as a domain concept.
        assert_eq!(class_and_count(&derived, "create"), ("generic".into(), 1));

        // Roles: `service` from OrderingService + BasketService + the file
        // stem; the rest appear once each.
        assert_eq!(class_and_count(&derived, "service"), ("role".into(), 3));
        assert_eq!(class_and_count(&derived, "repository"), ("role".into(), 1));
        assert_eq!(class_and_count(&derived, "command"), ("role".into(), 1));
        assert_eq!(class_and_count(&derived, "event"), ("role".into(), 1));

        // The Package node contributed nothing.
        assert!(!derived.has_node("token::payment"));
        assert!(!derived.has_node("token::gateway"));

        // A clean token table: every node is a lexicon Constant, no edges,
        // and the base graph was not touched.
        assert_eq!(derived.node_count(), derived.count_nodes_of(ont::CONSTANT));
        assert_eq!(derived.edge_count(), 0);
        assert_eq!(base.node_count(), 8);
    }

    #[test]
    fn deterministic_across_runs() {
        let base = eshop_base();
        let a = LexiconExtractor.extract(&base).to_jsonl();
        let b = LexiconExtractor.extract(&base).to_jsonl();
        assert_eq!(a, b);
        assert!(!a.is_empty());
    }
}
