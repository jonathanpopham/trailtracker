//! The archetype extractor: classify every symbol into an **architectural
//! archetype** — the extensible mindmap of *what kinds of things* live in a
//! codebase.
//!
//! Every [`Type`] and [`Function`] node in the base graph is classified by an
//! ordered **rule table** ([`RULES`]): a flat list of `{archetype, predicate}`
//! entries evaluated top to bottom, **first match wins**, falling back to
//! [`UNCLASSIFIED`]. The table is the whole design: adding a new archetype is
//! adding one row (or, for callers with their own vocabulary, passing a custom
//! slice to [`classify_with`]) — no code restructuring, no new pass.
//!
//! The seed vocabulary merges DDD and web-application archetypes: Controller,
//! Service, Repository, Aggregate, Entity, ValueObject, DomainEvent, Command,
//! Query, Handler, Factory, Dto, Interface, Configuration, Middleware,
//! Extension, Migration, Test, Mock, EntryPoint, Client, Enum, Exception,
//! Attribute, Unclassified — plus five **method roles** for Function-kind
//! nodes (Q-ARCH-1): Constructor, Accessor, EventHandler, QueryMethod,
//! MutationMethod. Method-role rules sit dead last in the table, so they only
//! claim functions no stronger signal wanted; test *methods* reuse the Test
//! archetype, while the five new roles carry no layer vote.
//!
//! Predicates combine four signal families, computed once per node into a
//! [`SymbolFacts`]:
//!
//! - **name** — suffix/prefix/infix conventions (`*Controller`, `*Handler`,
//!   `I*` interfaces, `Mock*`, …);
//! - **structure** — node props: `entrypoint == true`, `type_kind`
//!   (`"interface"`, `"enum"`, `"trait"`), the node's `language` and
//!   `qualified_name` (gating the language-scoped idiom rules: Python
//!   Model/View/Serializer/Manager, Go Handler/Server/Store/`New*`
//!   constructors, Rust trait/Builder/Error/`mod tests`), a generated marker;
//! - **path** — the symbol's own `path` prop, else the path of the [`File`]
//!   that `DECLARES` it (`/Controllers/`, `/Migrations/`, test projects,
//!   mocks, DDD aggregate folders like `/AggregatesModel/OrderAggregate/`);
//! - **inheritance** — the names of the symbol's base types: the targets of
//!   its `EXTENDS` and `IMPLEMENTS` edges. This is what catches DDD symbols
//!   named by *concept* rather than by role suffix: `Order : Entity,
//!   IAggregateRoot` and `Buyer` carry no `*Aggregate` name, but their base
//!   list and aggregate-folder path say exactly what they are.
//!
//! The table is ordered specific-before-general: structural facts (EntryPoint,
//! Interface, Enum) come first, then location facts (Migration, Mock, Test),
//! then inheritance facts (AggregateRoot/ValueObject/Entity bases — structure
//! beats naming), then name conventions with longer suffixes before their
//! prefixes — `*CommandHandler`/`*Handler` matches **Handler** before the
//! `*Command` rule can claim it, and `IOrderRepository` is an **Interface**
//! before the `*Repository` rule sees it. A weak domain-path fallback (a
//! field-carrying `Type` in a `.Domain` unit) sits at the very end, just above
//! [`UNCLASSIFIED`].
//!
//! The derived view contains, per archetype present in the codebase, one
//! summary node (kind [`Type`], tagged `view: "archetypes"`, props
//! `{archetype, count}`) with a [`CONTAINS`] edge to each classified member
//! symbol; the members are carried into the view (their base kind kept,
//! tagged with their `archetype`) so the graph loads standalone in Ontoloom.
//!
//! Pure and deterministic: a function of the base graph only, walking the
//! `BTreeMap`-ordered iterators and writing through the sorted, de-duplicating
//! [`Graph`] API — the same base graph always linearizes byte-identically.
//! The base graph is never mutated.
//!
//! [`Type`]: crate::ir::ontology::node::TYPE
//! [`Function`]: crate::ir::ontology::node::FUNCTION
//! [`File`]: crate::ir::ontology::node::FILE
//! [`CONTAINS`]: crate::ir::ontology::edge::CONTAINS

use std::collections::{BTreeMap, BTreeSet};

use crate::core::json::Json;
use crate::graph::{Graph, GraphNode};
use crate::ir::ontology::{edge, node as ont};

use super::Extractor;

/// Property key marking a node as belonging to the archetypes view.
const VIEW: &str = "archetypes";

/// The seed archetype vocabulary (DDD + web, merged).
pub mod archetype {
    pub const CONTROLLER: &str = "Controller";
    pub const SERVICE: &str = "Service";
    pub const REPOSITORY: &str = "Repository";
    pub const AGGREGATE: &str = "Aggregate";
    pub const ENTITY: &str = "Entity";
    pub const VALUE_OBJECT: &str = "ValueObject";
    pub const DOMAIN_EVENT: &str = "DomainEvent";
    pub const COMMAND: &str = "Command";
    pub const QUERY: &str = "Query";
    pub const HANDLER: &str = "Handler";
    pub const FACTORY: &str = "Factory";
    pub const DTO: &str = "Dto";
    pub const INTERFACE: &str = "Interface";
    pub const CONFIGURATION: &str = "Configuration";
    pub const MIDDLEWARE: &str = "Middleware";
    pub const EXTENSION: &str = "Extension";
    pub const MIGRATION: &str = "Migration";
    pub const TEST: &str = "Test";
    pub const MOCK: &str = "Mock";
    pub const ENTRY_POINT: &str = "EntryPoint";
    pub const CLIENT: &str = "Client";
    pub const ENUM: &str = "Enum";
    pub const EXCEPTION: &str = "Exception";
    pub const ATTRIBUTE: &str = "Attribute";
    // Method/function roles (Q-ARCH-1): archetypes for Function-kind nodes
    // whose *name verb* carries a clear role. They deliberately carry no
    // layer information — `layers::layer_of_archetype` abstains on them, so
    // a unit's layer is still decided by its type-level archetype mix.
    // EventHandler in particular must NOT reuse Handler: event-driven
    // codebases put `Handle*`/`On*` methods in every layer, and letting them
    // vote Application flipped whole Domain units (Radarr, dubbo, alacritty).
    pub const CONSTRUCTOR: &str = "Constructor";
    pub const ACCESSOR: &str = "Accessor";
    pub const EVENT_HANDLER: &str = "EventHandler";
    pub const QUERY_METHOD: &str = "QueryMethod";
    pub const MUTATION_METHOD: &str = "MutationMethod";
    pub const UNCLASSIFIED: &str = "Unclassified";
}

use archetype::*;

/// The classification-relevant facts about one symbol, computed once so every
/// rule predicate reads from the same cheap, borrowed view.
///
/// `path` is the *effective* path: the node's own `path` prop when present,
/// else the path of the `File` that `DECLARES` the node, else `""`.
#[derive(Clone, Copy, Debug)]
pub struct SymbolFacts<'a> {
    /// Ontology node kind (`Type`, `Function`, …).
    pub kind: &'a str,
    /// Simple name (`OrderingController`).
    pub name: &'a str,
    /// Effective source path (`src/Ordering.API/Controllers/...`), or `""`.
    pub path: &'a str,
    /// The node's `type_kind` prop (`"interface"`, `"enum"`, …), or `""`.
    pub type_kind: &'a str,
    /// The node's `language` prop (`"python"`, `"go"`, `"rust"`, …), or
    /// `""`. Gates the language-scoped rules: a Python `*View` is a
    /// Controller, a C# `*View` is not.
    pub language: &'a str,
    /// The node's `qualified_name` prop (`crate::grid::tests::scroll`), or
    /// `""`. Carries container context names alone lack — Rust `mod tests`
    /// test functions are only visible here.
    pub qualified: &'a str,
    /// The node's `entrypoint` prop, defaulting to `false`.
    pub entrypoint: bool,
    /// The node's `generated`/`is_generated` prop, defaulting to `false`.
    pub generated: bool,
    /// Names of the symbol's base types: the targets of its `EXTENDS` and
    /// `IMPLEMENTS` edges (sorted, de-duplicated). Marker interfaces count —
    /// `IAggregateRoot` is as strong a DDD signal as an `AggregateRoot` base
    /// class. Empty when the caller has no graph context ([`classify`]).
    pub bases: &'a [String],
    /// Whether the symbol's declaring file also `DECLARES` value bindings
    /// (`Constant` nodes — fields/properties in class-language frontends).
    /// The closest IR proxy for "this type carries fields"; `false` when the
    /// caller has no graph context.
    pub has_fields: bool,
}

impl<'a> SymbolFacts<'a> {
    /// Extract the facts from a base-graph node. The effective path is the
    /// node's own `path` prop when present, else `declared_path` (the path of
    /// the `File` that `DECLARES` the node, when the caller knows it).
    /// Structural graph facts ([`Self::bases`], [`Self::has_fields`]) are
    /// empty — use [`Self::with_structure`] when the caller knows them.
    pub fn of(node: &'a GraphNode, declared_path: Option<&'a str>) -> SymbolFacts<'a> {
        let prop_str = |key: &str| node.props.get(key).and_then(as_str).unwrap_or("");
        let prop_bool = |key: &str| node.props.get(key) == Some(&Json::Bool(true));
        let own_path = prop_str("path");
        SymbolFacts {
            kind: node.kind,
            name: node.name.as_str(),
            path: if own_path.is_empty() {
                declared_path.unwrap_or("")
            } else {
                own_path
            },
            type_kind: prop_str("type_kind"),
            language: prop_str("language"),
            qualified: prop_str("qualified_name"),
            entrypoint: prop_bool("entrypoint"),
            generated: prop_bool("generated") || prop_bool("is_generated"),
            bases: &[],
            has_fields: false,
        }
    }

    /// [`Self::of`], enriched with the structural graph facts the extractor
    /// computes once per pass: the symbol's base-type names (from `EXTENDS`/
    /// `IMPLEMENTS` edges) and whether its declaring file carries fields.
    pub fn with_structure(
        node: &'a GraphNode,
        declared_path: Option<&'a str>,
        bases: &'a [String],
        has_fields: bool,
    ) -> SymbolFacts<'a> {
        SymbolFacts {
            bases,
            has_fields,
            ..SymbolFacts::of(node, declared_path)
        }
    }

    fn ends(&self, suffix: &str) -> bool {
        self.name.ends_with(suffix)
    }

    fn ends_any(&self, suffixes: &[&str]) -> bool {
        suffixes.iter().any(|s| self.name.ends_with(s))
    }

    fn path_has(&self, needle: &str) -> bool {
        self.path.contains(needle)
    }

    /// Language gate for the language-scoped rules: only fire on symbols the
    /// frontend tagged with this `language`.
    fn lang(&self, language: &str) -> bool {
        self.language == language
    }

    /// Any base type whose name ends with any of `suffixes` — the
    /// inheritance analogue of [`Self::ends_any`].
    fn base_ends_any(&self, suffixes: &[&str]) -> bool {
        suffixes.iter().any(|s| self.base_ends(s))
    }

    /// Any base type named exactly `name`.
    fn base_is(&self, name: &str) -> bool {
        self.bases.iter().any(|b| b == name)
    }

    /// Any base type whose name ends with `suffix` (`AggregateRoot` matches
    /// both an `AggregateRoot` base class and an `IAggregateRoot` marker
    /// interface).
    fn base_ends(&self, suffix: &str) -> bool {
        self.bases.iter().any(|b| b.ends_with(suffix))
    }

    /// The DDD aggregate-folder convention: the symbol lives under an
    /// aggregates folder (`/AggregatesModel/` or `/Aggregates/`) **and** is
    /// the aggregate root — its innermost directory names it, either exactly
    /// (`Aggregates/Order/Order.cs`) or with the `Aggregate` suffix
    /// (`AggregatesModel/OrderAggregate/Order.cs`). Child entities in the
    /// same folder (`OrderAggregate/OrderItem.cs`) do NOT match.
    fn is_aggregate_root_by_path(&self) -> bool {
        if !(self.path_has("/AggregatesModel/") || self.path_has("/Aggregates/")) {
            return false;
        }
        let mut components = self.path.rsplit('/');
        let _file = components.next();
        match components.next() {
            Some(dir) => dir == self.name || dir.strip_suffix("Aggregate") == Some(self.name),
            None => false,
        }
    }

    /// A `.Domain` project/unit or a `/Domain/` folder — where DDD keeps its
    /// model types.
    fn in_domain_unit(&self) -> bool {
        self.path_has(".Domain/") || self.path_has("/Domain/") || self.path_has("/domain/")
    }

    /// Is this a `Function`-kind node? Gates the method-role rules so a Type
    /// named `GetOpts` or `NewFeature` is never claimed by a verb rule.
    fn is_fn(&self) -> bool {
        self.kind == ont::FUNCTION
    }

    /// The name begins with `stem` as a whole verb word — the stem alone, or
    /// followed by `_` or an uppercase letter — in snake_case, lowerCamel, or
    /// UpperCamel form: `get`, `get_area`, `getArea`, and `GetArea` all match
    /// stem `"get"`; `getter`, `settings`, `island`, and `once` never match
    /// their look-alike stems. `stem` must be lowercase ASCII.
    fn verb(&self, stem: &str) -> bool {
        let word_boundary = |rest: &str| {
            rest.is_empty()
                || rest.starts_with('_')
                || rest.chars().next().is_some_and(|c| c.is_ascii_uppercase())
        };
        if let Some(rest) = self.name.strip_prefix(stem) {
            if word_boundary(rest) {
                return true;
            }
        }
        // UpperCamel: the stem with its first letter capitalized.
        let Some(stem_first) = stem.chars().next() else {
            return false;
        };
        self.name
            .strip_prefix(stem_first.to_ascii_uppercase())
            .and_then(|rest| rest.strip_prefix(&stem[1..]))
            .is_some_and(word_boundary)
    }

    /// The name begins with any of `stems` as a whole verb word.
    fn verb_any(&self, stems: &[&str]) -> bool {
        stems.iter().any(|s| self.verb(s))
    }

    /// The `IFoo` interface-naming convention: leading `I` followed by another
    /// uppercase letter (`IOrderRepository`, but not `Intake` or `IPod`… well,
    /// `IPod` matches — the convention is the convention).
    fn i_prefixed(&self) -> bool {
        let mut chars = self.name.chars();
        chars.next() == Some('I') && chars.next().is_some_and(|c| c.is_ascii_uppercase())
    }
}

/// One row of the classification table: the archetype awarded when the
/// predicate holds. `Copy` so callers can splice [`RULES`] into their own
/// extended tables.
#[derive(Clone, Copy)]
pub struct Rule {
    /// The archetype this rule awards.
    pub archetype: &'static str,
    /// Does the rule claim this symbol?
    pub predicate: fn(&SymbolFacts) -> bool,
}

/// The ordered rule table. **First match wins**; extend by adding a row (or by
/// passing a custom slice to [`classify_with`]). Ordering discipline:
///
/// 1. structural facts (EntryPoint, Interface, Enum) — strongest signals;
/// 2. location facts (Migration, Mock, Test) — where a symbol lives;
/// 3. language-scoped idioms (gated on [`SymbolFacts::language`]) — Python
///    Model/View/Serializer/Manager, Go Handler/Server/Store/`New*`, Rust
///    trait/Builder/Error/`mod tests`; before the generic name conventions so
///    the language's own meaning wins (a go `*Handler` is a Controller, not a
///    C#-style Handler), and never firing outside their language;
/// 4. inheritance facts (AggregateRoot / ValueObject / Entity bases, the DDD
///    aggregate-folder root) — what a symbol *is* structurally beats what its
///    name suggests; Aggregate precedes Entity because a root typically
///    extends `Entity` **and** implements `IAggregateRoot`;
/// 5. name conventions, longest/most-specific suffix first — Handler before
///    Command (`CreateOrderCommandHandler`), Attribute/Exception/Middleware
///    before the broad web/DDD suffixes, Dto-ish suffixes near the end;
/// 6. the weak domain-unit fallback (a field-carrying `Type` in a `.Domain`
///    unit is an Entity) — just above the method roles;
/// 7. method/function roles (test methods, Constructor, Accessor,
///    EventHandler, QueryMethod, MutationMethod) — Function-kind only,
///    verb-prefix driven, dead last so they never steal a type-level or
///    suffix classification.
pub static RULES: &[Rule] = &[
    // -- structural signals -------------------------------------------------
    Rule {
        archetype: ENTRY_POINT,
        predicate: |f| f.entrypoint,
    },
    Rule {
        archetype: INTERFACE,
        predicate: |f| f.type_kind == "interface" || (f.kind == ont::TYPE && f.i_prefixed()),
    },
    Rule {
        archetype: ENUM,
        predicate: |f| f.type_kind == "enum",
    },
    // -- location signals ---------------------------------------------------
    Rule {
        archetype: MIGRATION,
        predicate: |f| f.path_has("/Migrations/") || f.path_has("/migrations/") || f.generated,
    },
    Rule {
        archetype: MOCK,
        predicate: |f| f.name.starts_with("Mock") || f.ends("Mock") || f.path_has("Mock"),
    },
    Rule {
        archetype: TEST,
        predicate: |f| {
            f.ends_any(&["Test", "Tests"])
                || f.path_has("Tests/")
                || f.path_has(".Test")
                || f.path_has("/tests/")
                || f.path_has("/test/")
                || f.path.starts_with("tests/")
                || f.path.starts_with("test/")
        },
    },
    // -- language-scoped rules: per-language idioms ---------------------------
    // Each rule is gated on the node's `language` prop, so a Python `*View`
    // is a Controller while a C# `*View` is untouched. Placed after the
    // location signals (a mock/test stays a mock/test in any language) and
    // before the DDD inheritance block and the C#-flavored name conventions,
    // so the language idiom beats the generic suffix (`go *Handler` is a
    // Controller before the generic `*Handler` rule can call it a Handler).
    //
    // Python (django-style web): tests, then the framework base classes —
    // inheritance catches concept-named symbols (`class Article(Model)`).
    Rule {
        archetype: TEST,
        predicate: |f| f.lang("python") && (f.name.starts_with("test_") || f.base_ends("TestCase")),
    },
    Rule {
        archetype: MIDDLEWARE,
        predicate: |f| f.lang("python") && f.base_ends("Middleware"),
    },
    Rule {
        archetype: DTO,
        predicate: |f| {
            f.lang("python")
                && (f.ends_any(&["Serializer", "Form"]) || f.base_ends_any(&["Serializer", "Form"]))
        },
    },
    Rule {
        archetype: CONTROLLER,
        predicate: |f| {
            f.lang("python")
                && (f.ends_any(&["ViewSet", "View", "Admin"])
                    || f.base_ends_any(&["ViewSet", "View", "Admin"]))
        },
    },
    Rule {
        archetype: REPOSITORY,
        predicate: |f| {
            f.lang("python")
                && (f.ends_any(&["Manager", "QuerySet"])
                    || f.base_ends_any(&["Manager", "QuerySet"]))
        },
    },
    Rule {
        archetype: ENTITY,
        predicate: |f| {
            f.lang("python") && !f.ends("ViewModel") && (f.ends("Model") || f.base_ends("Model"))
        },
    },
    // Go: `_test.go` files, constructor functions (`NewServer`), and the
    // net/http vocabulary — a go `*Handler` is the presentation edge.
    Rule {
        archetype: TEST,
        predicate: |f| f.lang("go") && f.path.ends_with("_test.go"),
    },
    Rule {
        archetype: FACTORY,
        predicate: |f| {
            f.lang("go")
                && f.kind == crate::ir::ontology::node::FUNCTION
                && f.name
                    .strip_prefix("New")
                    .is_some_and(|rest| rest.chars().next().is_some_and(|c| c.is_ascii_uppercase()))
        },
    },
    Rule {
        archetype: CONTROLLER,
        predicate: |f| f.lang("go") && f.ends("Handler"),
    },
    Rule {
        archetype: SERVICE,
        predicate: |f| f.lang("go") && f.ends("Server"),
    },
    Rule {
        archetype: REPOSITORY,
        predicate: |f| f.lang("go") && f.ends("Store"),
    },
    // Rust: `mod tests` test functions (visible via the qualified name),
    // traits as the interface archetype, builders and error enums. `impl`
    // blocks need no rule — methods carry their receiver type.
    Rule {
        archetype: TEST,
        predicate: |f| {
            f.lang("rust")
                && (f.qualified.contains("::tests::")
                    || f.qualified.contains("::test::")
                    || f.name.starts_with("test_"))
        },
    },
    Rule {
        archetype: INTERFACE,
        predicate: |f| f.lang("rust") && f.type_kind == "trait",
    },
    Rule {
        archetype: FACTORY,
        predicate: |f| f.lang("rust") && f.ends("Builder"),
    },
    Rule {
        archetype: EXCEPTION,
        predicate: |f| f.lang("rust") && f.ends("Error"),
    },
    // -- inheritance signals: DDD bases and marker interfaces ----------------
    // Aggregate before Entity: a root extends `Entity` AND implements
    // `IAggregateRoot`; the stronger claim must win.
    Rule {
        archetype: AGGREGATE,
        predicate: |f| f.base_ends("AggregateRoot") || f.is_aggregate_root_by_path(),
    },
    Rule {
        archetype: VALUE_OBJECT,
        predicate: |f| f.base_is("ValueObject"),
    },
    Rule {
        archetype: ENTITY,
        predicate: |f| f.base_ends("Entity") || f.base_is("EntityBase"),
    },
    // -- name conventions: specific before general --------------------------
    Rule {
        archetype: ATTRIBUTE,
        predicate: |f| f.ends("Attribute"),
    },
    Rule {
        archetype: EXCEPTION,
        predicate: |f| f.ends("Exception"),
    },
    Rule {
        archetype: MIDDLEWARE,
        predicate: |f| f.ends("Middleware"),
    },
    Rule {
        archetype: EXTENSION,
        predicate: |f| f.ends_any(&["Extensions", "Extension"]),
    },
    Rule {
        archetype: CONFIGURATION,
        predicate: |f| f.ends_any(&["Options", "Config", "Configuration", "Settings"]),
    },
    // Handler must precede Command: `CreateOrderCommandHandler` is a Handler.
    Rule {
        archetype: HANDLER,
        predicate: |f| f.ends("Handler"),
    },
    Rule {
        archetype: COMMAND,
        predicate: |f| f.ends("Command"),
    },
    Rule {
        archetype: QUERY,
        predicate: |f| f.ends_any(&["Query", "Queries"]),
    },
    Rule {
        archetype: DOMAIN_EVENT,
        predicate: |f| f.ends("Event"),
    },
    Rule {
        archetype: FACTORY,
        predicate: |f| f.ends("Factory"),
    },
    Rule {
        archetype: CONTROLLER,
        predicate: |f| f.ends("Controller") || f.path_has("/Controllers/"),
    },
    Rule {
        archetype: SERVICE,
        predicate: |f| f.ends_any(&["Service", "Services"]),
    },
    Rule {
        archetype: REPOSITORY,
        predicate: |f| f.ends("Repository"),
    },
    Rule {
        archetype: CLIENT,
        predicate: |f| f.ends("Client"),
    },
    Rule {
        archetype: DTO,
        predicate: |f| f.ends_any(&["Dto", "DTO", "Request", "Response"]),
    },
    Rule {
        archetype: VALUE_OBJECT,
        predicate: |f| f.ends_any(&["ViewModel", "ValueObject"]),
    },
    Rule {
        archetype: AGGREGATE,
        predicate: |f| f.ends_any(&["Aggregate", "AggregateRoot"]),
    },
    Rule {
        archetype: ENTITY,
        predicate: |f| f.ends("Entity"),
    },
    // -- weak fallback: concept-named domain model types ---------------------
    // A Type living in a `.Domain` unit / `/Domain/` folder that nothing above
    // claimed, but whose declaring file carries field bindings, is a domain
    // entity named by concept (`PaymentMethod`, `CardType`).
    Rule {
        archetype: ENTITY,
        predicate: |f| f.kind == ont::TYPE && f.has_fields && f.in_domain_unit(),
    },
    // -- method/function roles (Q-ARCH-1) ------------------------------------
    // Function-kind nodes only, dead last in the table: these rules claim
    // only functions no stronger signal above (structure, location, language
    // idiom, name suffix) already wanted, so every type-level classification
    // is untouched and a `CreateOrderCommand` function is still a Command.
    // Test methods reuse the Test archetype (voting Test in the layer pass,
    // exactly like type-level tests); every other method role is a new name
    // the layer vote abstains on — a class full of getters, `new`s, or
    // `on_*` callbacks must not drag its unit anywhere. (EventHandler
    // deliberately does NOT reuse Handler: letting `Handle*`/`On*` methods
    // vote Application flipped whole Domain units on event-driven repos.)
    //
    // Test methods: the `test` verb prefix (JUnit `testCreate`, pytest/rust
    // `test_create`) for frontends whose test files carry no path signal.
    Rule {
        archetype: TEST,
        predicate: |f| {
            f.is_fn()
                && f.name.strip_prefix("test").is_some_and(|rest| {
                    rest.starts_with('_')
                        || rest.chars().next().is_some_and(|c| c.is_ascii_uppercase())
                })
        },
    },
    // Event/message handler methods: `HandleOrderPlaced`, `handle_key`,
    // `OnClick`, `onModuleInit`.
    Rule {
        archetype: EVENT_HANDLER,
        predicate: |f| f.is_fn() && f.verb_any(&["handle", "on"]),
    },
    // Constructors and factory methods: rust `new`/`with_capacity`, python
    // `__init__`/`__new__`, the create/make verb family everywhere.
    Rule {
        archetype: CONSTRUCTOR,
        predicate: |f| {
            f.is_fn()
                && (f.name == "__init__"
                    || f.name == "__new__"
                    || f.verb_any(&["new", "create", "make", "with"]))
        },
    },
    // Accessors: the get/set/is/has verb families — one archetype, not four.
    Rule {
        archetype: ACCESSOR,
        predicate: |f| f.is_fn() && f.verb_any(&["get", "set", "is", "has"]),
    },
    // Query methods (read side): find/list/query. `get*` belongs to Accessor
    // above; `*Query` types belong to the Query suffix rule far above.
    Rule {
        archetype: QUERY_METHOD,
        predicate: |f| f.is_fn() && f.verb_any(&["find", "list", "query"]),
    },
    // Mutation methods (write side): save/update/delete/add/remove.
    Rule {
        archetype: MUTATION_METHOD,
        predicate: |f| f.is_fn() && f.verb_any(&["save", "update", "delete", "add", "remove"]),
    },
];

/// Classify a base-graph node against the built-in [`RULES`], using only the
/// facts the node itself carries (its own `path` prop when present). Other
/// passes (domains, layers) reuse this directly; the extractor itself calls
/// [`SymbolFacts::of`] with the declaring file's path for the richer signal.
pub fn classify(node: &GraphNode) -> &'static str {
    classify_with(RULES, &SymbolFacts::of(node, None))
}

/// Classify pre-computed facts against an arbitrary ordered rule table —
/// first match wins, falling back to [`UNCLASSIFIED`]. This is the extension
/// point: splice extra rows around [`RULES`] to grow the vocabulary.
pub fn classify_with(rules: &[Rule], facts: &SymbolFacts) -> &'static str {
    rules
        .iter()
        .find(|r| (r.predicate)(facts))
        .map(|r| r.archetype)
        .unwrap_or(UNCLASSIFIED)
}

/// Classify every `Type`/`Function` symbol into an architectural archetype.
pub struct ArchetypeExtractor;

impl Extractor for ArchetypeExtractor {
    fn name(&self) -> &'static str {
        "archetypes"
    }

    fn extract(&self, graph: &Graph) -> Graph {
        let mut out = Graph::new();

        // symbol id -> declaring File's path, so name-less signals like
        // `/Migrations/` or test projects reach symbols that don't carry their
        // own `path` prop. First declaring file wins (deterministic: edges are
        // iterated in stable signature order).
        let file_paths: BTreeMap<&str, &str> = graph
            .nodes()
            .filter(|n| n.kind == ont::FILE)
            .filter_map(|n| {
                n.props
                    .get("path")
                    .and_then(as_str)
                    .map(|p| (n.id.as_str(), p))
            })
            .collect();
        // While walking DECLARES edges, also record each symbol's declaring
        // File id and which files declare value bindings (`Constant` nodes —
        // fields/properties): the `has_fields` signal for the weak
        // domain-entity fallback.
        let constants: BTreeSet<&str> = graph
            .nodes()
            .filter(|n| n.kind == ont::CONSTANT)
            .map(|n| n.id.as_str())
            .collect();
        let mut declared_in: BTreeMap<&str, &str> = BTreeMap::new();
        let mut declaring_file: BTreeMap<&str, &str> = BTreeMap::new();
        let mut files_with_fields: BTreeSet<&str> = BTreeSet::new();
        for e in graph.edges().filter(|e| e.kind == edge::DECLARES) {
            if let Some(path) = file_paths.get(e.from.as_str()) {
                declared_in.entry(e.to.as_str()).or_insert(path);
                declaring_file
                    .entry(e.to.as_str())
                    .or_insert(e.from.as_str());
            }
            if constants.contains(e.to.as_str()) {
                files_with_fields.insert(e.from.as_str());
            }
        }

        // symbol id -> names of its base types: the targets of its EXTENDS and
        // IMPLEMENTS edges, by target-node name (falling back to the edge's
        // `base_name` prop for a target missing from the graph). Sorted and
        // de-duplicated, so the fact is deterministic regardless of edge order.
        let name_of: BTreeMap<&str, &str> = graph
            .nodes()
            .map(|n| (n.id.as_str(), n.name.as_str()))
            .collect();
        let mut bases_of: BTreeMap<&str, Vec<String>> = BTreeMap::new();
        for e in graph
            .edges()
            .filter(|e| e.kind == edge::EXTENDS || e.kind == edge::IMPLEMENTS)
        {
            let base = name_of
                .get(e.to.as_str())
                .copied()
                .or_else(|| e.props.get("base_name").and_then(as_str));
            if let Some(base) = base {
                bases_of
                    .entry(e.from.as_str())
                    .or_default()
                    .push(base.to_string());
            }
        }
        for bases in bases_of.values_mut() {
            bases.sort();
            bases.dedup();
        }
        const NO_BASES: &[String] = &[];

        // Classify every symbol, grouping members per archetype. BTreeMap keys
        // give sorted archetypes; node iteration order gives sorted member ids.
        let mut members: BTreeMap<&'static str, Vec<&GraphNode>> = BTreeMap::new();
        for n in graph
            .nodes()
            .filter(|n| n.kind == ont::TYPE || n.kind == ont::FUNCTION)
        {
            let has_fields = declaring_file
                .get(n.id.as_str())
                .is_some_and(|f| files_with_fields.contains(f));
            let facts = SymbolFacts::with_structure(
                n,
                declared_in.get(n.id.as_str()).copied(),
                bases_of
                    .get(n.id.as_str())
                    .map(Vec::as_slice)
                    .unwrap_or(NO_BASES),
                has_fields,
            );
            members
                .entry(classify_with(RULES, &facts))
                .or_default()
                .push(n);
        }

        // One summary node per archetype present, CONTAINS-linked to each
        // member; members are carried into the view so it loads standalone.
        for (arch, nodes) in &members {
            let summary_id = format!("archetype::{arch}");
            out.upsert_node(
                summary_id.clone(),
                ont::TYPE,
                *arch,
                vec![
                    ("view", Json::str(VIEW)),
                    ("archetype", Json::str(*arch)),
                    ("count", Json::U64(nodes.len() as u64)),
                ],
            );
            for n in nodes {
                let mut props = vec![("view", Json::str(VIEW)), ("archetype", Json::str(*arch))];
                for key in ["type_kind", "language"] {
                    if let Some(v) = n.props.get(key) {
                        props.push((key, v.clone()));
                    }
                }
                out.upsert_node(n.id.clone(), n.kind, n.name.clone(), props);
                out.add_edge(summary_id.clone(), edge::CONTAINS, n.id.clone(), vec![]);
            }
        }

        out
    }
}

/// Borrow a JSON string value, if the value is a string.
fn as_str(v: &Json) -> Option<&str> {
    match v {
        Json::Str(s) => Some(s.as_str()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ty(g: &mut Graph, id: &str, name: &str, props: Vec<(&'static str, Json)>) {
        g.upsert_node(id, ont::TYPE, name, props);
    }

    /// A hand-built, eShop-shaped base graph exercising every signal family.
    fn sample_base() -> Graph {
        let mut g = Graph::new();
        ty(
            &mut g,
            "ty::OrderingController",
            "OrderingController",
            vec![],
        );
        ty(&mut g, "ty::IOrderRepository", "IOrderRepository", vec![]);
        ty(&mut g, "ty::OrderRepository", "OrderRepository", vec![]);
        ty(
            &mut g,
            "ty::CreateOrderCommand",
            "CreateOrderCommand",
            vec![],
        );
        ty(
            &mut g,
            "ty::CreateOrderCommandHandler",
            "CreateOrderCommandHandler",
            vec![],
        );
        ty(
            &mut g,
            "ty::OrderPlacedIntegrationEvent",
            "OrderPlacedIntegrationEvent",
            vec![],
        );
        ty(
            &mut g,
            "ty::OrderStatus",
            "OrderStatus",
            vec![("type_kind", Json::str("enum"))],
        );
        ty(&mut g, "ty::CatalogServices", "CatalogServices", vec![]);
        g.upsert_node(
            "fn::Program.Main",
            ont::FUNCTION,
            "Main",
            vec![("entrypoint", Json::Bool(true))],
        );
        // A migration symbol with no name signal: only its declaring file's
        // path says what it is.
        g.upsert_node(
            "file::src/Ordering.Infrastructure/Migrations/20240101_Init.cs",
            ont::FILE,
            "20240101_Init.cs",
            vec![(
                "path",
                Json::str("src/Ordering.Infrastructure/Migrations/20240101_Init.cs"),
            )],
        );
        ty(&mut g, "ty::Init", "Init", vec![]);
        g.add_edge(
            "file::src/Ordering.Infrastructure/Migrations/20240101_Init.cs",
            edge::DECLARES,
            "ty::Init",
            vec![],
        );
        g
    }

    fn archetype_of<'a>(derived: &'a Graph, member_id: &str) -> &'a str {
        derived
            .nodes()
            .find(|n| n.id == member_id)
            .unwrap_or_else(|| panic!("{member_id} missing from derived view"))
            .props
            .get("archetype")
            .and_then(as_str)
            .expect("member carries archetype prop")
    }

    #[test]
    fn classifies_eshop_shaped_symbols() {
        let derived = ArchetypeExtractor.extract(&sample_base());
        for (id, want) in [
            ("ty::OrderingController", CONTROLLER),
            ("ty::IOrderRepository", INTERFACE), // I-prefix beats *Repository
            ("ty::OrderRepository", REPOSITORY),
            ("ty::CreateOrderCommand", COMMAND),
            ("ty::CreateOrderCommandHandler", HANDLER), // Handler beats Command
            ("ty::OrderPlacedIntegrationEvent", DOMAIN_EVENT),
            ("ty::OrderStatus", ENUM),
            ("ty::CatalogServices", SERVICE),
            ("fn::Program.Main", ENTRY_POINT),
            ("ty::Init", MIGRATION), // via the declaring file's /Migrations/ path
        ] {
            assert_eq!(archetype_of(&derived, id), want, "{id}");
        }
    }

    #[test]
    fn emits_summary_nodes_with_counts_and_contains_edges() {
        let derived = ArchetypeExtractor.extract(&sample_base());

        let controller = derived
            .nodes()
            .find(|n| n.id == "archetype::Controller")
            .expect("Controller summary node");
        assert_eq!(controller.kind, ont::TYPE);
        assert_eq!(controller.props.get("view"), Some(&Json::str(VIEW)));
        assert_eq!(controller.props.get("count"), Some(&Json::U64(1)));

        // Every member hangs off its summary node.
        let contains: Vec<_> = derived
            .edges()
            .filter(|e| e.kind == edge::CONTAINS)
            .collect();
        assert_eq!(contains.len(), 10, "one CONTAINS per classified symbol");
        assert!(contains
            .iter()
            .any(|e| e.from == "archetype::Handler" && e.to == "ty::CreateOrderCommandHandler"));
        assert!(contains
            .iter()
            .any(|e| e.from == "archetype::Migration" && e.to == "ty::Init"));

        // The File node itself is not classified — only Type/Function symbols.
        assert!(!derived.has_node("file::src/Ordering.Infrastructure/Migrations/20240101_Init.cs"));
    }

    #[test]
    fn unmatched_symbols_fall_back_to_unclassified() {
        let mut g = Graph::new();
        ty(&mut g, "ty::Order", "Order", vec![]);
        let derived = ArchetypeExtractor.extract(&g);
        assert_eq!(archetype_of(&derived, "ty::Order"), UNCLASSIFIED);
        let summary = derived
            .nodes()
            .find(|n| n.id == "archetype::Unclassified")
            .expect("Unclassified summary node");
        assert_eq!(summary.props.get("count"), Some(&Json::U64(1)));
    }

    #[test]
    fn rule_order_is_respected() {
        // Handler precedes Command in the table, so the combined suffix
        // resolves to Handler (`*Handler` and `*Command` cannot both match one
        // name, but the specific-first ordering is what keeps this stable if a
        // broader Command predicate ever lands).
        let handler = SymbolFacts {
            kind: ont::TYPE,
            name: "CreateOrderCommandHandler",
            path: "",
            type_kind: "",
            language: "",
            qualified: "",
            entrypoint: false,
            generated: false,
            bases: &[],
            has_fields: false,
        };
        assert_eq!(classify_with(RULES, &handler), HANDLER);

        // IOrderRepository fires BOTH the Interface rule (I-prefix) and the
        // Repository rule (suffix). Interface wins only because its row comes
        // first; reversing the table flips the answer — classification is
        // table-order-driven, not hard-coded.
        let iface = SymbolFacts {
            name: "IOrderRepository",
            ..handler
        };
        assert_eq!(classify_with(RULES, &iface), INTERFACE);

        let mut reversed: Vec<Rule> = RULES.to_vec();
        reversed.reverse();
        assert_eq!(classify_with(&reversed, &iface), REPOSITORY);
    }

    #[test]
    fn table_is_extensible_a_new_rule_changes_a_classification() {
        let facts = SymbolFacts {
            kind: ont::TYPE,
            name: "OrderSaga",
            path: "",
            type_kind: "",
            language: "",
            qualified: "",
            entrypoint: false,
            generated: false,
            bases: &[],
            has_fields: false,
        };
        // Stock table: no rule claims *Saga.
        assert_eq!(classify_with(RULES, &facts), UNCLASSIFIED);

        // Splice one new row in front of the stock table: vocabulary grown.
        let mut extended = vec![Rule {
            archetype: "Saga",
            predicate: |f| f.ends("Saga"),
        }];
        extended.extend_from_slice(RULES);
        assert_eq!(classify_with(&extended, &facts), "Saga");
        // …and everything else still classifies as before.
        let handler = SymbolFacts {
            name: "CreateOrderCommandHandler",
            ..facts
        };
        assert_eq!(classify_with(&extended, &handler), HANDLER);
    }

    #[test]
    fn python_idioms_classify_only_for_python() {
        let base = SymbolFacts {
            kind: ont::TYPE,
            name: "",
            path: "",
            type_kind: "",
            language: "python",
            qualified: "",
            entrypoint: false,
            generated: false,
            bases: &[],
            has_fields: false,
        };
        let model_base = ["Model".to_string()];
        let testcase_base = ["TestCase".to_string()];
        let view_base = ["ListView".to_string()];
        for (name, bases, want) in [
            ("ArticleModel", &[][..], ENTITY),
            ("Article", &model_base[..], ENTITY), // concept-named django model
            ("ArticleForm", &[][..], DTO),
            ("ArticleSerializer", &[][..], DTO),
            ("ArticleView", &[][..], CONTROLLER),
            ("ArticleViewSet", &[][..], CONTROLLER),
            ("ArticleAdmin", &[][..], CONTROLLER),
            ("ArticleDetail", &view_base[..], CONTROLLER), // CBV by base
            ("ArticleManager", &[][..], REPOSITORY),
            ("ArticleQuerySet", &[][..], REPOSITORY),
            ("ArticleTests", &testcase_base[..], TEST),
        ] {
            let f = SymbolFacts {
                name,
                bases,
                ..base
            };
            assert_eq!(classify_with(RULES, &f), want, "{name}");
        }
        // test_* functions are tests.
        let f = SymbolFacts {
            kind: ont::FUNCTION,
            name: "test_create_article",
            ..base
        };
        assert_eq!(classify_with(RULES, &f), TEST);
        // The same names in C# (or untagged) do NOT fire the python rules.
        for (name, want) in [
            ("ArticleModel", UNCLASSIFIED),
            ("ArticleView", UNCLASSIFIED),
            ("ArticleAdmin", UNCLASSIFIED),
        ] {
            let f = SymbolFacts {
                name,
                language: "csharp",
                ..base
            };
            assert_eq!(classify_with(RULES, &f), want, "csharp {name}");
        }
    }

    #[test]
    fn go_idioms_classify_only_for_go() {
        let base = SymbolFacts {
            kind: ont::TYPE,
            name: "",
            path: "",
            type_kind: "",
            language: "go",
            qualified: "",
            entrypoint: false,
            generated: false,
            bases: &[],
            has_fields: false,
        };
        // A go *Handler is the presentation edge — Controller, not Handler.
        for (name, want) in [
            ("pageHandler", CONTROLLER),
            ("fileServer", SERVICE),
            ("pageStore", REPOSITORY),
        ] {
            let f = SymbolFacts { name, ..base };
            assert_eq!(classify_with(RULES, &f), want, "{name}");
        }
        // Constructor functions are factories; the next rune must be upper.
        let ctor = SymbolFacts {
            kind: ont::FUNCTION,
            name: "NewServer",
            ..base
        };
        assert_eq!(classify_with(RULES, &ctor), FACTORY);
        let newsletter = SymbolFacts {
            kind: ont::FUNCTION,
            name: "Newsletter",
            ..base
        };
        assert_eq!(classify_with(RULES, &newsletter), UNCLASSIFIED);
        // Symbols in _test.go files are tests, whatever their name.
        let tf = SymbolFacts {
            kind: ont::FUNCTION,
            name: "TestPageRender",
            path: "hugolib/page_test.go",
            ..base
        };
        assert_eq!(classify_with(RULES, &tf), TEST);
        // Outside go, *Handler keeps the generic Handler archetype.
        let cs = SymbolFacts {
            name: "CreateOrderHandler",
            language: "csharp",
            ..base
        };
        assert_eq!(classify_with(RULES, &cs), HANDLER);
    }

    #[test]
    fn rust_idioms_classify_only_for_rust() {
        let base = SymbolFacts {
            kind: ont::TYPE,
            name: "",
            path: "",
            type_kind: "",
            language: "rust",
            qualified: "",
            entrypoint: false,
            generated: false,
            bases: &[],
            has_fields: false,
        };
        let tr = SymbolFacts {
            name: "EventListener",
            type_kind: "trait",
            ..base
        };
        assert_eq!(classify_with(RULES, &tr), INTERFACE);
        for (name, want) in [("WindowBuilder", FACTORY), ("ParseError", EXCEPTION)] {
            let f = SymbolFacts { name, ..base };
            assert_eq!(classify_with(RULES, &f), want, "{name}");
        }
        // `mod tests` functions are visible via the qualified name.
        let tf = SymbolFacts {
            kind: ont::FUNCTION,
            name: "scroll_up",
            qualified: "crate::grid::tests::scroll_up",
            ..base
        };
        assert_eq!(classify_with(RULES, &tf), TEST);
        // A C# *Error is untouched (no generic Error rule exists).
        let cs = SymbolFacts {
            name: "ParseError",
            language: "csharp",
            ..base
        };
        assert_eq!(classify_with(RULES, &cs), UNCLASSIFIED);
    }

    /// eShop's Ordering.Domain shape: concept-named aggregates/entities with
    /// NO role suffixes — only inheritance and path signals say what they are.
    fn ddd_base() -> Graph {
        let mut g = Graph::new();

        // Marker bases. `Entity` resolves in-project; `IAggregateRoot` and
        // `ValueObject` are framework symbols an airgapped frontend leaves as
        // explicit UnresolvedSymbol nodes.
        ty(&mut g, "ty::SeedWork.Entity", "Entity", vec![]);
        g.upsert_node(
            "unresolved::IAggregateRoot",
            ont::UNRESOLVED,
            "IAggregateRoot",
            vec![],
        );
        g.upsert_node(
            "unresolved::ValueObject",
            ont::UNRESOLVED,
            "ValueObject",
            vec![],
        );

        fn declare(g: &mut Graph, path: &str, sym: &str) {
            let fid = format!("file::{path}");
            let name = path.rsplit('/').next().unwrap().to_string();
            g.upsert_node(
                fid.clone(),
                ont::FILE,
                name,
                vec![("path", Json::str(path))],
            );
            g.add_edge(fid, edge::DECLARES, sym, vec![]);
        }

        // Order: aggregate root by BOTH signals — implements IAggregateRoot
        // and is the root file of /AggregatesModel/OrderAggregate/.
        ty(&mut g, "ty::Order", "Order", vec![]);
        declare(
            &mut g,
            "src/Ordering.Domain/AggregatesModel/OrderAggregate/Order.cs",
            "ty::Order",
        );
        g.add_edge("ty::Order", edge::EXTENDS, "ty::SeedWork.Entity", vec![]);
        g.add_edge(
            "ty::Order",
            edge::IMPLEMENTS,
            "unresolved::IAggregateRoot",
            vec![],
        );

        // Buyer: root by folder alone — extends only Entity.
        ty(&mut g, "ty::Buyer", "Buyer", vec![]);
        declare(
            &mut g,
            "src/Ordering.Domain/AggregatesModel/BuyerAggregate/Buyer.cs",
            "ty::Buyer",
        );
        g.add_edge("ty::Buyer", edge::EXTENDS, "ty::SeedWork.Entity", vec![]);

        // OrderItem: a child entity INSIDE the aggregate folder — Entity via
        // its base, never Aggregate (the folder names Order, not OrderItem).
        ty(&mut g, "ty::OrderItem", "OrderItem", vec![]);
        declare(
            &mut g,
            "src/Ordering.Domain/AggregatesModel/OrderAggregate/OrderItem.cs",
            "ty::OrderItem",
        );
        g.add_edge(
            "ty::OrderItem",
            edge::EXTENDS,
            "ty::SeedWork.Entity",
            vec![],
        );

        // Address: ValueObject by base, no path/name signal at all.
        ty(&mut g, "ty::Address", "Address", vec![]);
        g.add_edge(
            "ty::Address",
            edge::EXTENDS,
            "unresolved::ValueObject",
            vec![],
        );

        // PaymentMethod: no base edge, no name signal — but a field-carrying
        // Type in the .Domain unit: the weak Entity fallback.
        ty(&mut g, "ty::PaymentMethod", "PaymentMethod", vec![]);
        declare(
            &mut g,
            "src/Ordering.Domain/PaymentMethod.cs",
            "ty::PaymentMethod",
        );
        g.upsert_node(
            "const::PaymentMethod.Alias",
            ont::CONSTANT,
            "Alias",
            vec![("binding", Json::str("field"))],
        );
        g.add_edge(
            "file::src/Ordering.Domain/PaymentMethod.cs",
            edge::DECLARES,
            "const::PaymentMethod.Alias",
            vec![],
        );

        // Tag: a bare domain type with no fields — stays Unclassified; the
        // weak fallback demands field evidence.
        ty(&mut g, "ty::Tag", "Tag", vec![]);
        declare(&mut g, "src/Ordering.Domain/Tag.cs", "ty::Tag");

        g
    }

    #[test]
    fn structural_signals_classify_concept_named_ddd_symbols() {
        let base = ddd_base();
        let derived = ArchetypeExtractor.extract(&base);
        for (id, want) in [
            ("ty::Order", AGGREGATE),  // IAggregateRoot base + folder root
            ("ty::Buyer", AGGREGATE),  // folder root alone
            ("ty::OrderItem", ENTITY), // Entity base, not the folder root
            ("ty::Address", VALUE_OBJECT),
            ("ty::PaymentMethod", ENTITY), // weak fallback: .Domain + fields
            ("ty::Tag", UNCLASSIFIED),     // .Domain but no fields
        ] {
            assert_eq!(archetype_of(&derived, id), want, "{id}");
        }

        // Same graph, same answers — the structural facts are deterministic.
        assert_eq!(
            derived.to_jsonl(),
            ArchetypeExtractor.extract(&base).to_jsonl()
        );

        // The base graph came through untouched.
        assert_eq!(base.to_jsonl(), ddd_base().to_jsonl());
    }

    #[test]
    fn classify_without_graph_context_uses_empty_structural_facts() {
        // `classify(&node)` has no EXTENDS/DECLARES context: a concept-named
        // node with no props resolves exactly as before this signal existed.
        let mut g = Graph::new();
        ty(&mut g, "ty::Order", "Order", vec![]);
        let node = g.nodes().next().unwrap();
        assert_eq!(classify(node), UNCLASSIFIED);
    }

    #[test]
    fn aggregate_base_precedes_entity_base_and_name_rules_still_win_first() {
        let facts = SymbolFacts {
            kind: ont::TYPE,
            name: "Order",
            path: "",
            type_kind: "",
            language: "",
            qualified: "",
            entrypoint: false,
            generated: false,
            bases: &[],
            has_fields: false,
        };
        // A root extends Entity AND implements IAggregateRoot: Aggregate wins
        // because its row precedes the Entity-base row.
        let bases = vec!["Entity".to_string(), "IAggregateRoot".to_string()];
        let root = SymbolFacts {
            bases: &bases,
            ..facts
        };
        assert_eq!(classify_with(RULES, &root), AGGREGATE);

        // Entity-base alone.
        let entity_base = vec!["Entity".to_string()];
        let child = SymbolFacts {
            name: "OrderItem",
            bases: &entity_base,
            ..facts
        };
        assert_eq!(classify_with(RULES, &child), ENTITY);

        // Structural rules do not steal earlier claims: an entrypoint or a
        // Mock keeps its archetype even with a DDD base.
        let mock = SymbolFacts {
            name: "MockOrder",
            bases: &entity_base,
            ..facts
        };
        assert_eq!(classify_with(RULES, &mock), MOCK);
    }

    #[test]
    fn method_roles_classify_function_verbs() {
        let base = SymbolFacts {
            kind: ont::FUNCTION,
            name: "",
            path: "",
            type_kind: "",
            language: "",
            qualified: "",
            entrypoint: false,
            generated: false,
            bases: &[],
            has_fields: false,
        };
        for (name, want) in [
            // Constructors/factory methods, across naming styles.
            ("new", CONSTRUCTOR),
            ("new_with_capacity", CONSTRUCTOR),
            ("with_context", CONSTRUCTOR),
            ("__init__", CONSTRUCTOR),
            ("__new__", CONSTRUCTOR),
            ("createOrder", CONSTRUCTOR),
            ("CreateInstance", CONSTRUCTOR),
            ("make_current", CONSTRUCTOR),
            // Accessors: get/set/is/has, one archetype.
            ("get_area", ACCESSOR),
            ("getArea", ACCESSOR),
            ("GetOrders", ACCESSOR),
            ("set_title", ACCESSOR),
            ("is_empty", ACCESSOR),
            ("hasNext", ACCESSOR),
            // Test methods: the `test` verb, any language.
            ("test_scroll", TEST),
            ("testCreateOrder", TEST),
            // Handler-shaped methods get the abstaining EventHandler role.
            ("handle_key", EVENT_HANDLER),
            ("HandleOrderPlaced", EVENT_HANDLER),
            ("onModuleInit", EVENT_HANDLER),
            ("OnClick", EVENT_HANDLER),
            // Query/mutation verbs.
            ("find_by_id", QUERY_METHOD),
            ("ListBuckets", QUERY_METHOD),
            ("query_rows", QUERY_METHOD),
            ("save_changes", MUTATION_METHOD),
            ("UpdateStatus", MUTATION_METHOD),
            ("delete_all", MUTATION_METHOD),
            ("addListener", MUTATION_METHOD),
            ("remove_node", MUTATION_METHOD),
        ] {
            let f = SymbolFacts { name, ..base };
            assert_eq!(classify_with(RULES, &f), want, "{name}");
        }
    }

    #[test]
    fn verb_rules_respect_word_boundaries_and_stay_judicious() {
        let base = SymbolFacts {
            kind: ont::FUNCTION,
            name: "",
            path: "",
            type_kind: "",
            language: "",
            qualified: "",
            entrypoint: false,
            generated: false,
            bases: &[],
            has_fields: false,
        };
        // Look-alike prefixes must NOT fire: genuinely generic functions stay
        // Unclassified rather than being forced into a role.
        for name in [
            "newest",
            "settings",
            "setup",
            "island",
            "hash",
            "once",
            "online",
            "getter",
            "listen",
            "handler_count",
            "added",
            "updater",
            "address",
            "test",
            "withdraw",
            "render",
            "flush",
            "resolve",
        ] {
            let f = SymbolFacts { name, ..base };
            assert_eq!(classify_with(RULES, &f), UNCLASSIFIED, "{name}");
        }
        // Verb rules are Function-gated: a Type with a verb-shaped name is
        // never claimed by a method role.
        for name in ["GetOpts", "NewFeature", "SetOnce", "UpdateInfo"] {
            let f = SymbolFacts {
                kind: ont::TYPE,
                name,
                ..base
            };
            assert_eq!(classify_with(RULES, &f), UNCLASSIFIED, "type {name}");
        }
    }

    #[test]
    fn method_roles_never_steal_earlier_claims() {
        let base = SymbolFacts {
            kind: ont::FUNCTION,
            name: "",
            path: "",
            type_kind: "",
            language: "",
            qualified: "",
            entrypoint: false,
            generated: false,
            bases: &[],
            has_fields: false,
        };
        // Suffix conventions still win over verb prefixes.
        let f = SymbolFacts {
            name: "CreateOrderCommand",
            ..base
        };
        assert_eq!(classify_with(RULES, &f), COMMAND);
        let f = SymbolFacts {
            name: "GetOrdersQuery",
            ..base
        };
        assert_eq!(classify_with(RULES, &f), QUERY);
        // The go constructor idiom still lands on Factory, not Constructor.
        let f = SymbolFacts {
            name: "NewServer",
            language: "go",
            ..base
        };
        assert_eq!(classify_with(RULES, &f), FACTORY);
        // …while the same shape outside go is a Constructor.
        let f = SymbolFacts {
            name: "NewServer",
            ..base
        };
        assert_eq!(classify_with(RULES, &f), CONSTRUCTOR);
        // Location signals still beat verbs: a getter in a test tree is Test.
        let f = SymbolFacts {
            name: "get_fixture",
            path: "tests/support/fixtures.rs",
            ..base
        };
        assert_eq!(classify_with(RULES, &f), TEST);
        // Entrypoints stay entrypoints.
        let f = SymbolFacts {
            name: "main",
            entrypoint: true,
            ..base
        };
        assert_eq!(classify_with(RULES, &f), ENTRY_POINT);
    }

    #[test]
    fn classify_uses_the_nodes_own_facts() {
        let mut g = Graph::new();
        ty(
            &mut g,
            "ty::OrderState",
            "OrderState",
            vec![("type_kind", Json::str("enum"))],
        );
        let node = g.nodes().next().unwrap();
        assert_eq!(classify(node), ENUM);
    }

    #[test]
    fn deterministic_across_runs() {
        let base = sample_base();
        let a = ArchetypeExtractor.extract(&base).to_jsonl();
        let b = ArchetypeExtractor.extract(&base).to_jsonl();
        assert_eq!(a, b);
        assert!(!a.is_empty());
    }

    #[test]
    fn never_mutates_the_base_graph() {
        let base = sample_base();
        let before = base.to_jsonl();
        let _ = ArchetypeExtractor.extract(&base);
        assert_eq!(base.to_jsonl(), before);
    }
}
