#!/usr/bin/env python3
"""TrailTracker MCP server — stdio JSON-RPC 2.0, Python stdlib only.

Exposes TrailTracker's deterministic code-understanding extractors as MCP
tools so an agent can load only the relevant subgraph of a codebase instead
of stuffing files into context.

Design (see mcp/README.md):
  - Pure orchestration: every tool shells out to the existing `trailtracker`
    binary. No LLM, no network, no state. Deterministic and airgap-pure.
  - Newline-delimited JSON-RPC 2.0 on stdio (MCP stdio transport).
  - Structured, actionable JSON-RPC errors (type / hint / data payloads).
  - Large-output safety: JSONL tools return a paginated envelope with a
    documented `limit`/`offset` (a 20k-node graph never lands in context
    unless explicitly requested with limit=0).

Environment:
  TRAILTRACKER_BIN            explicit path to the trailtracker binary
  TRAILTRACKER_TIMEOUT_SECS   per-call subprocess timeout (default 300)
  TRAILTRACKER_MCP_LOG        "debug" for request/response logging on stderr

Zero-install: python3 only. Run: python3 mcp/trailtracker_mcp.py
"""

import json
import os
import subprocess
import sys
import time
from pathlib import Path

SERVER_NAME = "trailtracker"
SERVER_VERSION = "0.1.0"
SUPPORTED_PROTOCOL_VERSIONS = ("2024-11-05", "2025-03-26", "2025-06-18")
LATEST_PROTOCOL_VERSION = "2025-06-18"

WORKTREE_ROOT = Path(__file__).resolve().parent.parent


def _timeout_from_env(raw, default=300):
    """Validated TRAILTRACKER_TIMEOUT_SECS (UBS audit C4): a non-numeric or
    non-positive value falls back to the default with a stderr warning
    instead of crashing the server at import (`5m` -> ValueError) or making
    every call fail instantly (`-1` -> subprocess.run(timeout=-1))."""
    if raw is None:
        return default
    try:
        value = int(str(raw).strip())
    except ValueError:
        sys.stderr.write(
            "[trailtracker-mcp] warning: TRAILTRACKER_TIMEOUT_SECS=%r is not an "
            "integer; using default %ds\n" % (raw, default)
        )
        return default
    if value <= 0:
        sys.stderr.write(
            "[trailtracker-mcp] warning: TRAILTRACKER_TIMEOUT_SECS=%r must be a "
            "positive number of seconds; using default %ds\n" % (raw, default)
        )
        return default
    return value


DEFAULT_TIMEOUT = _timeout_from_env(os.environ.get("TRAILTRACKER_TIMEOUT_SECS"))
DEBUG = os.environ.get("TRAILTRACKER_MCP_LOG", "").lower() == "debug"

DEFAULT_LIMIT = 2000  # JSONL records per page; 0 = unlimited (documented)

SEARCH_DEFAULT_LIMIT = 20  # search results per call
SEARCH_MAX_LIMIT = 200  # hard cap; search results are small, no pagination

NAV_DEFAULT_BUDGET = 20000  # chars; mirrors the CLI default (no tokenizer!)
NAV_DEFAULT_DEPTH = 2
NAV_MAX_DEPTH = 8  # the neighborhood grows exponentially
NAV_DIRECTIONS = ("callers", "callees", "both")
NAV_FORMATS = ("json", "prose")  # MCP surface; the CLI also has a human text view

# JSON-RPC error codes. -326xx are protocol-reserved; -320xx are ours.
PARSE_ERROR = -32700
INVALID_REQUEST = -32600
METHOD_NOT_FOUND = -32601
INVALID_PARAMS = -32602
E_BINARY_MISSING = -32000
E_ANALYSIS_FAILED = -32001
E_TIMEOUT = -32002
E_OUTPUT_UNPARSEABLE = -32003

# tool name (agent-facing, snake_case) -> binary extractor name (kebab-case)
EXTRACTOR_TOOLS = {
    "domains": "domains",
    "archetypes": "archetypes",
    "layers": "layers",
    "lexicon": "lexicon",
    "hierarchy": "hierarchy",
    "data_ontology": "data-ontology",
    "workflow_spec": "workflow-spec",
}

_PLACEHOLDER_MARKERS = ("<", ">", "your_", "$repo", "$project", "/path/to")


def log(msg):
    sys.stderr.write("[trailtracker-mcp] %s\n" % msg)
    sys.stderr.flush()


def debug(msg):
    if DEBUG:
        log(msg)


# --------------------------------------------------------------------------
# Errors
# --------------------------------------------------------------------------

class ToolError(Exception):
    """Structured tool failure -> JSON-RPC error with actionable data."""

    def __init__(self, code, error_type, message, data=None):
        super().__init__(message)
        self.code = code
        self.error_type = error_type
        self.data = dict(data or {})
        self.data["type"] = error_type


# --------------------------------------------------------------------------
# Binary resolution + invocation
# --------------------------------------------------------------------------

def resolve_binary():
    """env TRAILTRACKER_BIN -> <worktree>/target/release -> ~/geist/trailtracker."""
    candidates = []
    env_bin = os.environ.get("TRAILTRACKER_BIN")
    if env_bin:
        candidates.append(Path(env_bin).expanduser())
    candidates.append(WORKTREE_ROOT / "target" / "release" / "trailtracker")
    candidates.append(
        Path.home() / "geist" / "trailtracker" / "target" / "release" / "trailtracker"
    )
    for c in candidates:
        if c.is_file() and os.access(c, os.X_OK):
            return str(c)
    raise ToolError(
        E_BINARY_MISSING,
        "BINARY_MISSING",
        "trailtracker binary not found. Searched: %s"
        % ", ".join(str(c) for c in candidates),
        {
            "hint": (
                "Build it with `cargo build --release` in the trailtracker repo, "
                "or set TRAILTRACKER_BIN to an existing binary."
            ),
            "searched": [str(c) for c in candidates],
        },
    )


def run_binary(args, timeout=DEFAULT_TIMEOUT):
    """Run the trailtracker binary; return stdout or raise a structured error."""
    binary = resolve_binary()
    cmd = [binary] + args
    debug("exec: %s" % " ".join(cmd))
    started = time.monotonic()
    try:
        proc = subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout
        )
    except subprocess.TimeoutExpired:
        raise ToolError(
            E_TIMEOUT,
            "TIMEOUT",
            "trailtracker timed out after %ss on: %s" % (timeout, " ".join(args)),
            {
                "hint": (
                    "Very large repos can exceed the default timeout. Raise "
                    "TRAILTRACKER_TIMEOUT_SECS in the server env, or point "
                    "repo_path at a subdirectory."
                ),
                "timeout_secs": timeout,
            },
        )
    elapsed = time.monotonic() - started
    debug("exit=%d in %.2fs, stdout=%dB" % (proc.returncode, elapsed, len(proc.stdout)))
    if proc.returncode != 0:
        detail = (proc.stderr or "").strip() or "(no stderr)"
        raise ToolError(
            E_ANALYSIS_FAILED,
            "ANALYSIS_FAILED",
            "trailtracker failed (exit %d): %s" % (proc.returncode, detail),
            {
                "hint": (
                    "Check that repo_path points at a source directory the "
                    "server process can read."
                ),
                "argv": args,
                "stderr": detail,
            },
        )
    return proc.stdout


def run_binary_status(args, timeout=DEFAULT_TIMEOUT):
    """Like run_binary, but returns (returncode, stdout, stderr) instead of
    raising on a non-zero exit. Used by tools whose CLI exit codes carry
    meaning (`explain`: 2 = ambiguous target, 3 = target not found) so they
    can map each outcome to its own structured error instead of a generic
    ANALYSIS_FAILED. Binary-missing and timeout still raise, same as
    run_binary."""
    binary = resolve_binary()
    cmd = [binary] + args
    debug("exec: %s" % " ".join(cmd))
    started = time.monotonic()
    try:
        proc = subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout
        )
    except subprocess.TimeoutExpired:
        raise ToolError(
            E_TIMEOUT,
            "TIMEOUT",
            "trailtracker timed out after %ss on: %s" % (timeout, " ".join(args)),
            {
                "hint": (
                    "Very large repos can exceed the default timeout. Raise "
                    "TRAILTRACKER_TIMEOUT_SECS in the server env, or point "
                    "repo_path at a subdirectory."
                ),
                "timeout_secs": timeout,
            },
        )
    elapsed = time.monotonic() - started
    debug("exit=%d in %.2fs, stdout=%dB" % (proc.returncode, elapsed, len(proc.stdout)))
    return proc.returncode, proc.stdout, proc.stderr


def run_target_json(argv, target):
    """Run a target-resolving CLI command (`explain`, `nav expand`) and parse
    its JSON stdout. Maps the CLI's exit-code contract to structured errors:
    2 = ambiguous target (stderr carries the candidate list), 3 = target not
    found (stderr carries search suggestions), other non-zero = analysis
    failure. Shared by every tool that resolves a node id/path/name."""
    stdout = run_target_text(argv, target)
    try:
        return json.loads(stdout)
    except ValueError as exc:
        raise ToolError(
            E_OUTPUT_UNPARSEABLE,
            "OUTPUT_UNPARSEABLE",
            "trailtracker %s emitted non-JSON output: %s" % (argv[0], exc),
            {"hint": "This is a trailtracker bug, not a usage error.",
             "output": stdout[:200]},
        )


def run_target_text(argv, target):
    """Run a target-resolving CLI command and return its raw stdout (the
    prose format is plain sentences, not JSON). Same exit-code mapping as
    [`run_target_json`]."""
    rc, stdout, stderr = run_binary_status(argv)
    detail = (stderr or "").strip() or "(no stderr)"
    if rc == 2:
        raise ToolError(
            INVALID_PARAMS,
            "AMBIGUOUS_TARGET",
            detail,
            {
                "hint": (
                    "Several nodes share that name. Retry with one exact "
                    "node id from the candidate list in the message."
                ),
                "target": target,
            },
        )
    if rc == 3:
        raise ToolError(
            INVALID_PARAMS,
            "TARGET_NOT_FOUND",
            detail,
            {
                "hint": (
                    "Nothing matches that id, path, or name. Try one of "
                    "the suggestions in the message, or find the right "
                    "name with the `search` tool first."
                ),
                "target": target,
            },
        )
    if rc != 0:
        raise ToolError(
            E_ANALYSIS_FAILED,
            "ANALYSIS_FAILED",
            "trailtracker failed (exit %d): %s" % (rc, detail),
            {
                "hint": (
                    "Check that repo_path points at a source directory the "
                    "server process can read."
                ),
                "argv": argv,
                "stderr": detail,
            },
        )
    return stdout


# --------------------------------------------------------------------------
# Input validation (forgive by default, educate on failure)
# --------------------------------------------------------------------------

def validate_repo_path(arguments):
    raw = arguments.get("repo_path")
    if not raw or not isinstance(raw, str):
        raise ToolError(
            INVALID_PARAMS,
            "MISSING_REPO_PATH",
            "repo_path is required: the absolute path of the directory to analyze.",
            {"hint": "Use the absolute path of the repo you are working in (e.g. from `pwd`)."},
        )
    lowered = raw.lower()
    if any(m in lowered for m in _PLACEHOLDER_MARKERS):
        raise ToolError(
            INVALID_PARAMS,
            "PLACEHOLDER_PATH",
            "repo_path '%s' looks like a placeholder, not a real directory." % raw,
            {"hint": "Replace it with the actual absolute path of the repository."},
        )
    path = Path(raw).expanduser()
    if not path.is_absolute():
        path = (Path.cwd() / path).resolve()
    if not path.is_dir():
        raise ToolError(
            INVALID_PARAMS,
            "REPO_PATH_NOT_FOUND",
            "repo_path '%s' is not an existing directory (resolved to '%s')."
            % (raw, path),
            {
                "hint": (
                    "Pass an absolute path. Relative paths resolve against the "
                    "MCP server's working directory (%s), which is usually not "
                    "what you want." % Path.cwd()
                ),
                "resolved": str(path),
            },
        )
    return str(path)


def validate_query(arguments):
    query = arguments.get("query")
    if not isinstance(query, str) or not query.strip():
        raise ToolError(
            INVALID_PARAMS,
            "MISSING_QUERY",
            "query is required: a non-empty string of words to search for.",
            {
                "hint": (
                    'Pass the concept, name fragment, or phrase you are looking '
                    'for, e.g. {"repo_path": "/abs/repo", "query": "basket '
                    'repository"}.'
                )
            },
        )
    return query


def validate_target(arguments):
    target = arguments.get("target")
    if not isinstance(target, str) or not target.strip():
        raise ToolError(
            INVALID_PARAMS,
            "MISSING_TARGET",
            "target is required: a node id, file path, or symbol name.",
            {
                "hint": (
                    'Pass the thing to explain, e.g. {"repo_path": "/abs/repo", '
                    '"target": "IBasketRepository"} — a symbol name, a file path '
                    "like src/parser.rs, or an exact node id from `search`/`graph`."
                )
            },
        )
    return target


def validate_search_limit(arguments):
    v = arguments.get("limit", SEARCH_DEFAULT_LIMIT)
    if isinstance(v, bool):
        v = SEARCH_DEFAULT_LIMIT
    if isinstance(v, str) and v.strip().isdigit():
        v = int(v)  # forgive "10" for 10
    if isinstance(v, float) and v.is_integer():
        v = int(v)
    if not isinstance(v, int) or v < 0:
        raise ToolError(
            INVALID_PARAMS,
            "INVALID_LIMIT",
            "limit must be a non-negative integer (got %r)." % (arguments.get("limit"),),
            {"hint": "Omit limit for the default of %d; max %d."
             % (SEARCH_DEFAULT_LIMIT, SEARCH_MAX_LIMIT)},
        )
    return min(v, SEARCH_MAX_LIMIT)


def validate_nav_int(arguments, name, default, maximum=None):
    """Non-negative integer argument with a default (forgiving "10" and 10.0),
    optionally capped. Used by nav_pack/nav_expand for budget/depth/cursor."""
    v = arguments.get(name, default)
    if isinstance(v, bool):
        v = default
    if isinstance(v, str) and v.strip().isdigit():
        v = int(v)
    if isinstance(v, float) and v.is_integer():
        v = int(v)
    if not isinstance(v, int) or v < 0:
        raise ToolError(
            INVALID_PARAMS,
            "INVALID_%s" % name.upper(),
            "%s must be a non-negative integer (got %r)." % (name, arguments.get(name)),
            {"hint": "Omit %s for the default of %d." % (name, default)},
        )
    if maximum is not None:
        v = min(v, maximum)
    return v


def validate_direction(arguments):
    v = arguments.get("direction", "both")
    if not isinstance(v, str) or v not in NAV_DIRECTIONS:
        raise ToolError(
            INVALID_PARAMS,
            "INVALID_DIRECTION",
            "direction must be one of %s (got %r)."
            % ("/".join(NAV_DIRECTIONS), arguments.get("direction")),
            {"hint": "callers = who depends on it; callees = what it depends on."},
        )
    return v


def validate_format(arguments):
    v = arguments.get("format", "json")
    if not isinstance(v, str) or v not in NAV_FORMATS:
        raise ToolError(
            INVALID_PARAMS,
            "INVALID_FORMAT",
            "format must be one of %s (got %r)."
            % ("/".join(NAV_FORMATS), arguments.get("format")),
            {"hint": "json = the exact machine object; prose = ADR-0008 "
                     "sentences for feeding a model directly."},
        )
    return v


def validate_paging(arguments):
    def coerce(name, default):
        v = arguments.get(name, default)
        if isinstance(v, bool):
            v = default
        if isinstance(v, str) and v.strip().isdigit():
            v = int(v)  # forgive "10" for 10
        if isinstance(v, float) and v.is_integer():
            v = int(v)
        if not isinstance(v, int) or v < 0:
            raise ToolError(
                INVALID_PARAMS,
                "INVALID_PAGING",
                "%s must be a non-negative integer (got %r)." % (name, arguments.get(name)),
                {"hint": "limit=0 means unlimited; omit both for the default page."},
            )
        return v

    return coerce("limit", DEFAULT_LIMIT), coerce("offset", 0)


# --------------------------------------------------------------------------
# JSONL -> paginated envelope
# --------------------------------------------------------------------------

def jsonl_envelope(tool, extractor, repo_path, stdout, limit, offset):
    records = []
    for line_no, line in enumerate(stdout.splitlines(), 1):
        if not line.strip():
            continue
        try:
            records.append(json.loads(line))
        except ValueError as exc:
            raise ToolError(
                E_OUTPUT_UNPARSEABLE,
                "OUTPUT_UNPARSEABLE",
                "trailtracker emitted a non-JSON line (%d): %s" % (line_no, exc),
                {"hint": "This is a trailtracker bug, not a usage error.", "line": line[:200]},
            )
    total = len(records)
    page = records[offset:] if limit == 0 else records[offset : offset + limit]
    truncated = offset + len(page) < total
    return {
        "tool": tool,
        "extractor": extractor,
        "repo_path": repo_path,
        "total_records": total,
        "offset": offset,
        "returned": len(page),
        "truncated": truncated,
        "next_offset": offset + len(page) if truncated else None,
        "records": page,
    }


# --------------------------------------------------------------------------
# Tool registry
# --------------------------------------------------------------------------

def _schema(paged):
    props = {
        "repo_path": {
            "type": "string",
            "description": (
                "Absolute path of the directory to analyze. Must exist on this "
                "machine. Use the repo root you are working in (e.g. from `pwd`)."
            ),
        }
    }
    if paged:
        props["limit"] = {
            "type": "integer",
            "minimum": 0,
            "default": DEFAULT_LIMIT,
            "description": (
                "Max JSONL records to return (default %d). 0 = unlimited — "
                "avoid on large repos (a 20k-node graph will flood your context). "
                "Output order is deterministic, so paging is stable." % DEFAULT_LIMIT
            ),
        }
        props["offset"] = {
            "type": "integer",
            "minimum": 0,
            "default": 0,
            "description": "Records to skip before the page starts (use with limit to page).",
        }
    return {
        "type": "object",
        "properties": props,
        "required": ["repo_path"],
        "additionalProperties": False,
    }


def _extractor_description(tool, extractor, what, when):
    return (
        "%s Runs TrailTracker's deterministic `%s` extractor (no LLM, no network) "
        "and returns a JSON envelope {total_records, returned, truncated, "
        "next_offset, records: [graph nodes/edges]}. %s "
        "Do: call `brief` first for orientation. "
        "Don't: pass a file path (directories only) or a placeholder path."
        % (what, extractor, when)
    )


TOOLS = [
    {
        "name": "brief",
        "description": (
            "Deterministic markdown brief of an unfamiliar codebase: overview + "
            "languages, architecture (domain clustering, largest units, module "
            "dependency map), entry "
            "points, hotspots (fan-in/fan-out), dependency cycles, and a "
            "plain-English synthesis. The best FIRST call on any repo — read this "
            "before pulling raw graph data. Returns markdown text. "
            "Don't: use it for machine-parseable data (use domains/graph/stats)."
        ),
        "inputSchema": _schema(paged=False),
    },
    {
        "name": "stats",
        "description": (
            "Honest coverage + graph statistics for a repo: files analyzed, "
            "lossless-parse rate, parse failures, node/edge counts by kind, and "
            "call-resolution provenance. Returns a small plain-text block. Use it "
            "to judge how much of the repo TrailTracker actually understood "
            "before trusting the derived views."
        ),
        "inputSchema": _schema(paged=False),
    },
    {
        "name": "graph",
        "description": (
            "The full canonical code graph (files, modules, functions, types, "
            "constants, external deps; CONTAINS/DECLARES/CALLS/IMPORTS/... edges) "
            "as a paginated JSON envelope. This is the raw substrate — it can be "
            "huge (20k+ nodes on large repos), so the default limit of %d records "
            "applies and `truncated`/`next_offset` tell you how to page. "
            "Do: prefer the derived views (domains, hierarchy, layers) and only "
            "drop to `graph` when you need raw nodes/edges. "
            "Don't: set limit=0 on a repo you haven't run `stats` on." % DEFAULT_LIMIT
        ),
        "inputSchema": _schema(paged=True),
    },
    {
        "name": "domains",
        "description": _extractor_description(
            "domains",
            "domains",
            "Business-domain clustering: which functional domains exist, which "
            "files/units belong to each, with symbol counts and confidence. "
            "EVERY file has a home: domain nodes carry kind='business' "
            "(clustered code) or kind='infrastructure' (the named groups "
            "Build & Tooling / Documentation / Generated / Repo root, each "
            "with a reason prop: scaffold/docs/generated/root), and test "
            "files fold into the domain of the code they exercise.",
            "Use to answer 'what are the functional areas of this codebase and "
            "where do they live?'.",
        ),
        "inputSchema": _schema(paged=True),
    },
    {
        "name": "archetypes",
        "description": _extractor_description(
            "archetypes",
            "archetypes",
            "Structural role classification of symbols (Controller, Model, "
            "Handler, Builder, Store, ...) with per-archetype counts.",
            "Use to see what KINDS of components a codebase is made of.",
        ),
        "inputSchema": _schema(paged=True),
    },
    {
        "name": "layers",
        "description": _extractor_description(
            "layers",
            "layers",
            "Architectural layering (Presentation / Application / Domain / "
            "Infrastructure / Shared) per unit, plus layering-violation edges.",
            "Use to check architecture shape and find layer violations.",
        ),
        "inputSchema": _schema(paged=True),
    },
    {
        "name": "lexicon",
        "description": _extractor_description(
            "lexicon",
            "lexicon",
            "The codebase's vocabulary: identifier tokens classified as "
            "concept/generic/etc. with frequencies.",
            "Use to learn the project's ubiquitous language before naming "
            "anything or searching for concepts.",
        ),
        "inputSchema": _schema(paged=True),
    },
    {
        "name": "hierarchy",
        "description": _extractor_description(
            "hierarchy",
            "hierarchy",
            "The Domain -> Project -> File -> Symbol containment hierarchy as "
            "nodes + edges — the navigable tree of the whole repo. Every file "
            "has a domain parent (business domain or a named infrastructure "
            "group with kind/reason props) — nothing is ungrouped.",
            "Use for drill-down navigation; page with limit/offset instead of "
            "loading all of a big repo at once.",
        ),
        "inputSchema": _schema(paged=True),
    },
    {
        "name": "data_ontology",
        "description": _extractor_description(
            "data_ontology",
            "data-ontology",
            "The data model view: entity-like types, their fields, and "
            "relationships between them.",
            "Use to understand what data the system manages before touching "
            "persistence or APIs.",
        ),
        "inputSchema": _schema(paged=True),
    },
    {
        "name": "workflow_spec",
        "description": _extractor_description(
            "workflow_spec",
            "workflow-spec",
            "Workflow/flow specifications recovered from the call graph: named "
            "flows with ordered steps.",
            "Use to find end-to-end behaviors (then `rebuild-brief` in the CLI "
            "for a deep dive on one flow).",
        ),
        "inputSchema": _schema(paged=True),
    },
    {
        "name": "search",
        "description": (
            "Hybrid code search over the repo's code graph: BM25 lexical "
            "ranking fused (reciprocal-rank) with deterministic hash "
            "embeddings, then re-ranked by graph proximity to the top lexical "
            "anchors. No LLM, no network, byte-deterministic. Returns "
            "{schema: 'trailtracker.search/v1', query, dir, total, results: "
            "[{rank, id, name, kind, path, score, why[]}]} where `why` "
            "explains each hit ('bm25 #1', 'embed #2', '1 hop from "
            "OrderService'). Handles typos and morphological near-misses via "
            "the embedding tier. Do: use it to find functions/types/files by "
            "concept or name fragment before pulling raw graph pages. "
            "Don't: expect full-text search of comments or string literals — "
            "it ranks graph nodes (functions, types, files, modules)."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "repo_path": {
                    "type": "string",
                    "description": (
                        "Absolute path of the directory to analyze. Must exist "
                        "on this machine. Use the repo root you are working in "
                        "(e.g. from `pwd`)."
                    ),
                },
                "query": {
                    "type": "string",
                    "description": (
                        "What to search for: a concept, symbol name, or phrase "
                        "(e.g. 'basket repository'). Typos are tolerated."
                    ),
                },
                "limit": {
                    "type": "integer",
                    "minimum": 0,
                    "maximum": SEARCH_MAX_LIMIT,
                    "default": SEARCH_DEFAULT_LIMIT,
                    "description": (
                        "Max results to return (default %d, capped at %d). "
                        "Results are small; no pagination."
                        % (SEARCH_DEFAULT_LIMIT, SEARCH_MAX_LIMIT)
                    ),
                },
            },
            "required": ["repo_path", "query"],
            "additionalProperties": False,
        },
    },
    {
        "name": "explain",
        "description": (
            "The atomic understanding primitive: ONE card that explains a "
            "file or symbol. Joins identity (name, kind, path:line, qualified "
            "name), classification (business domain, architectural layer, "
            "archetype), connectivity (fan-in/fan-out with top dependents and "
            "dependencies), blast radius (every node that could break if the "
            "target changes, same machinery as `query blast-radius`), and "
            "nearest neighbors (hybrid search with why-evidence). Returns "
            "{schema: 'trailtracker.explain/v1', identity, classification, "
            "connectivity, blast_radius, neighbors}. Deterministic, no LLM. "
            "Target resolution: exact node id, then exact file path, then "
            "exact symbol name. An ambiguous name errors with the candidate "
            "id list (AMBIGUOUS_TARGET — retry with one of them); an unknown "
            "target errors with search suggestions (TARGET_NOT_FOUND). "
            "Do: use it as the first call on any specific function/type/file "
            "you are about to work on. "
            "Don't: pass multi-word phrases (that is `search`'s job)."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "repo_path": {
                    "type": "string",
                    "description": (
                        "Absolute path of the directory to analyze. Must exist "
                        "on this machine. Use the repo root you are working in "
                        "(e.g. from `pwd`)."
                    ),
                },
                "target": {
                    "type": "string",
                    "description": (
                        "What to explain: an exact node id (e.g. "
                        "'fn::crate::parser::parse#7'), a file path relative to "
                        "the repo root (e.g. 'src/parser.rs'), or an exact "
                        "symbol name (e.g. 'IBasketRepository')."
                    ),
                },
            },
            "required": ["repo_path", "target"],
            "additionalProperties": False,
        },
    },
    {
        "name": "arch_verify",
        "description": (
            "Continuous architecture verification (ADR-0005): checks the "
            "ACTUAL code against the INTENDED architecture declared in a "
            "human-authored spec (default <repo>/.trailtracker-arch.json; "
            "override with spec_path). The spec declares domains as "
            "pathPrefixes plus rules: domain-existence, domain-containment, "
            "forbidden-dependency, forbidden-layer-dependency. Returns the "
            "trailtracker.arch-verify/v1 report: {format, dir, spec, domains, "
            "rules, findings: [{id, type, severity, message, count, "
            "examples[]}], status: clean|warnings|violated, exit}. "
            "Deterministic, no LLM. Findings are DATA, not a tool error — a "
            "'violated' status is the successful detection of drift. "
            "Do: commit a spec once (bootstrap it with `trailtracker "
            "arch-init <dir> -o <dir>/.trailtracker-arch.json`), then call "
            "this tool to check for drift before/after edits. "
            "Don't: call it on a repo with no spec (SPEC_NOT_FOUND tells you "
            "how to bootstrap one)."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "repo_path": {
                    "type": "string",
                    "description": (
                        "Absolute path of the directory to analyze. Must exist "
                        "on this machine. Use the repo root you are working in "
                        "(e.g. from `pwd`)."
                    ),
                },
                "spec_path": {
                    "type": "string",
                    "description": (
                        "Optional path of the architecture spec file. Defaults "
                        "to <repo_path>/.trailtracker-arch.json."
                    ),
                },
            },
            "required": ["repo_path"],
            "additionalProperties": False,
        },
    },
    {
        "name": "deadcode",
        "description": (
            "Rooted liveness analysis over the merged code graph. Marks forward "
            "from auditable entry, test, decorator, generated, and configured "
            "roots, then reports unreachable Function/Type/Constant nodes as "
            "dead-high, dead-medium, or transitively-dead with inbound-reference, "
            "ambiguous-candidacy, cross-file textual-mention, and export evidence. "
            "Returns trailtracker.deadcode/v1. Exit 1 means findings were "
            "successfully detected, not a tool failure. Deterministic, read-only, "
            "std-only. Do: start with min_confidence='high' for deletion candidates; "
            "use 'low' for the complete audit. Don't: treat medium/transitive "
            "findings as mechanically safe deletions without review."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "repo_path": {
                    "type": "string",
                    "description": (
                        "Absolute path of the source directory to analyze. Use "
                        "the repository root (for example, the result of `pwd`)."
                    ),
                },
                "min_confidence": {
                    "type": "string",
                    "enum": ["high", "medium", "low"],
                    "default": "low",
                    "description": (
                        "Minimum confidence to return: high only, high+medium, "
                        "or low for all tiers including transitively-dead."
                    ),
                },
                "limit": {
                    "type": "integer",
                    "minimum": 0,
                    "description": (
                        "Optional maximum findings per tier. Counts and the "
                        "complete auditable root list remain uncapped."
                    ),
                },
            },
            "required": ["repo_path"],
            "additionalProperties": False,
        },
    },
    {
        "name": "violations",
        "description": (
            "The spec-free FULL layer-violations report: every DEPENDS-family "
            "(CALLS, IMPORTS, USES_TYPE, ...) or SPECIALIZES-family (EXTENDS, "
            "IMPLEMENTS — cross-layer inheritance violates too) edge that "
            "points outward against the clean-architecture direction rule "
            "(Domain < Application < Infrastructure < Presentation; "
            "Test/Shared exempt), at UNIT grain — from-unit and to-unit with "
            "their layers, complete edge counts, and COMPLETE symbol-grain "
            "evidence ('path:symbol -[KIND]-> path:symbol', every edge named) "
            "— ranked worst-first with "
            "per-layer-pair totals. Unlike the `layers` extractor (which "
            "aggregates violations to layer->layer counts and loses unit "
            "identity), this NAMES the perpetrators. Needs no arch spec "
            "(use `arch_verify` for spec-driven gating). Returns the "
            "trailtracker.violations/v1 report: {schema, dir, rule, "
            "total_edges, unit_pairs, layer_pairs: [{from_layer, to_layer, "
            "edges, unit_pairs}], violations: [{from_unit, from_layer, "
            "to_unit, to_layer, count, examples[]}], status: "
            "clean|violations, exit}. Deterministic, no LLM. Violations are "
            "DATA, not a tool error — a 'violations' status is the "
            "successful detection of inverted dependencies. "
            "Do: call it to find WHO violates the layering before "
            "refactoring, then `explain` the offending units. "
            "Don't: expect spec rules here — it checks only the universal "
            "inward-dependency rule."
        ),
        "inputSchema": _schema(paged=False),
    },
    {
        "name": "nav_pack",
        "description": (
            "The context-efficient navigator (ADR-0004): ONE call that turns "
            "a task description into the highest-value EXACT subgraph that "
            "fits a character budget — the agent loop seed→orient→expand→"
            "read→verify in a single response. Returns {schema: "
            "'trailtracker.nav-pack/v1', budget{budget_chars, used_chars, "
            "estimated_chars, truncated, exceeded, omitted{}}, seeds (hybrid "
            "search hits with why-evidence), cards (per-seed: domain/layer/"
            "archetype, fan_in/fan_out, blast_count), orientation (domain/"
            "layer aggregation), read_plan (ranked file:line SPANS — read "
            "those spans, not whole files), neighborhood (the 2-hop "
            "DEPENDS-family edge list)}. Deterministic, no LLM, no tokenizer: "
            "the budget is an exact char count over the JSON (a proxy for "
            "your context window) and truncation is never silent — omitted "
            "counts are exact. A minimum share of every budget is reserved "
            "for read_plan spans, so any viable budget yields an actionable "
            "plan; budget.exceeded=true means the budget cannot hold even "
            "the minimal core plus one span (content is best-effort — raise "
            "the budget). "
            "Do: make this your FIRST call when starting a task on a large "
            "repo; then read exactly the read_plan spans and use nav_expand "
            "for more graph around any node. "
            "Don't: raise the budget past what you can afford to load — the "
            "pack degrades gracefully by dropping the lowest-value items. "
            "Don't: use it for aggregate/whole-repo questions ('how many "
            "files are in domain X', 'which domains depend on Y') — the pack "
            "is code-reading-shaped (where is X, what touches it); aggregate "
            "domain facts come from the domains/hierarchy/stats tools, and "
            "top-dependent facts from explain."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "repo_path": {
                    "type": "string",
                    "description": (
                        "Absolute path of the directory to analyze. Must exist "
                        "on this machine. Use the repo root you are working in "
                        "(e.g. from `pwd`)."
                    ),
                },
                "query": {
                    "type": "string",
                    "description": (
                        "The task, described in plain words (e.g. 'where is "
                        "playback session state managed'). Feeds hybrid "
                        "search; typos are tolerated."
                    ),
                },
                "budget": {
                    "type": "integer",
                    "minimum": 0,
                    "default": NAV_DEFAULT_BUDGET,
                    "description": (
                        "Character budget for the response (default %d). "
                        "A proxy for the consuming agent's context window — "
                        "chars, not tokens; there is no tokenizer here. "
                        "Applies to whichever format is returned."
                        % NAV_DEFAULT_BUDGET
                    ),
                },
                "format": {
                    "type": "string",
                    "enum": list(NAV_FORMATS),
                    "default": "json",
                    "description": (
                        "json = the exact nav-pack object (default, "
                        "unchanged). prose = the same value-ranked selection "
                        "as deterministic ADR-0008 sentences: a glossary "
                        "prelude (F1..Fn over the seeds), read-plan spans "
                        "stated as facts, seed cards, orientation, and "
                        "neighborhood edges — ready to paste into any "
                        "model's context. The char budget is honest over "
                        "the prose; a cut tail ends with 'The budget omits "
                        "N sentences of M sentences.'"
                    ),
                },
            },
            "required": ["repo_path", "query"],
            "additionalProperties": False,
        },
    },
    {
        "name": "nav_expand",
        "description": (
            "Exact neighborhood growth from any node (ADR-0004): the "
            "direction-aware (callers | callees | both), depth-bounded "
            "DEPENDS-family subgraph around a target, budget-truncated with "
            "an honest continuation cursor. Returns {schema: "
            "'trailtracker.nav-expand/v1', identity{}, direction, depth, "
            "budget{budget_chars, used_chars, estimated_chars, truncated, "
            "exceeded, omitted{}}, total_edges, cursor, returned, truncated, "
            "next_cursor, nodes[] (page endpoints with path:line), edges[] "
            "({from, kind, to, hops})}. Deterministic; paging is stable — "
            "pass next_cursor back as `cursor` to resume exactly where the "
            "page ended. Target resolution matches `explain`: exact node id, "
            "then file path, then symbol name (AMBIGUOUS_TARGET lists "
            "candidates; TARGET_NOT_FOUND carries suggestions). "
            "Do: use after nav_pack/search/explain to pull more exact "
            "structure around one node. "
            "Don't: use depth > 3 casually — the neighborhood grows "
            "exponentially; walk with the cursor instead."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "repo_path": {
                    "type": "string",
                    "description": (
                        "Absolute path of the directory to analyze. Must exist "
                        "on this machine. Use the repo root you are working in "
                        "(e.g. from `pwd`)."
                    ),
                },
                "target": {
                    "type": "string",
                    "description": (
                        "The node to expand from: an exact node id, a file "
                        "path relative to the repo root, or an exact symbol "
                        "name."
                    ),
                },
                "depth": {
                    "type": "integer",
                    "minimum": 0,
                    "maximum": NAV_MAX_DEPTH,
                    "default": NAV_DEFAULT_DEPTH,
                    "description": (
                        "How many hops to expand (default %d, capped at %d)."
                        % (NAV_DEFAULT_DEPTH, NAV_MAX_DEPTH)
                    ),
                },
                "direction": {
                    "type": "string",
                    "enum": list(NAV_DIRECTIONS),
                    "default": "both",
                    "description": (
                        "callers = incoming edges (who depends on it), "
                        "callees = outgoing (what it depends on), both = union."
                    ),
                },
                "budget": {
                    "type": "integer",
                    "minimum": 0,
                    "default": NAV_DEFAULT_BUDGET,
                    "description": (
                        "Character budget for the JSON response (default %d). "
                        "Chars, not tokens — there is no tokenizer here."
                        % NAV_DEFAULT_BUDGET
                    ),
                },
                "cursor": {
                    "type": "integer",
                    "minimum": 0,
                    "default": 0,
                    "description": (
                        "Continuation cursor from a previous truncated "
                        "response's next_cursor. Edge order is deterministic, "
                        "so paging is stable."
                    ),
                },
                "format": {
                    "type": "string",
                    "enum": list(NAV_FORMATS),
                    "default": "json",
                    "description": (
                        "json = the exact nav-expand object (default, "
                        "unchanged; carries next_cursor for paging). prose = "
                        "the target's identity and fan facts plus one "
                        "ADR-0008 sentence per edge from `cursor`, budget-"
                        "honest over the prose (a cut tail ends with the "
                        "omission sentence). Use json when you need "
                        "next_cursor; prose when feeding a model directly."
                    ),
                },
            },
            "required": ["repo_path", "target"],
            "additionalProperties": False,
        },
    },
]

TOOL_NAMES = [t["name"] for t in TOOLS]


# --------------------------------------------------------------------------
# Tool dispatch
# --------------------------------------------------------------------------

def call_tool(name, arguments):
    if name not in TOOL_NAMES:
        raise ToolError(
            INVALID_PARAMS,
            "UNKNOWN_TOOL",
            "Unknown tool '%s'." % name,
            {"hint": "Call tools/list for schemas.", "available_tools": TOOL_NAMES},
        )
    repo_path = validate_repo_path(arguments)

    if name == "brief":
        return text_result(run_binary(["brief", repo_path]))
    if name == "stats":
        return text_result(run_binary(["stats", repo_path]))
    if name == "search":
        query = validate_query(arguments)
        limit = validate_search_limit(arguments)
        stdout = run_binary(
            ["search", query, repo_path, "--json", "--limit", str(limit)]
        )
        try:
            payload = json.loads(stdout)
        except ValueError as exc:
            raise ToolError(
                E_OUTPUT_UNPARSEABLE,
                "OUTPUT_UNPARSEABLE",
                "trailtracker search emitted non-JSON output: %s" % exc,
                {"hint": "This is a trailtracker bug, not a usage error.",
                 "output": stdout[:200]},
            )
        return text_result(json.dumps(payload, separators=(",", ":")))

    if name == "explain":
        target = validate_target(arguments)
        payload = run_target_json(["explain", target, repo_path, "--json"], target)
        return text_result(json.dumps(payload, separators=(",", ":")))

    if name == "arch_verify":
        args = ["arch-verify", repo_path, "--json"]
        spec_path = arguments.get("spec_path")
        if spec_path is not None:
            if not isinstance(spec_path, str) or not spec_path.strip():
                raise ToolError(
                    INVALID_PARAMS,
                    "INVALID_SPEC_PATH",
                    "spec_path must be a non-empty string when provided (got %r)."
                    % (spec_path,),
                    {"hint": "Omit spec_path to use <repo_path>/.trailtracker-arch.json."},
                )
            args += ["--spec", spec_path]
        rc, stdout, stderr = run_binary_status(args)
        detail = (stderr or "").strip() or "(no stderr)"
        if rc == 2:
            # Malformed spec (or bad rule vocabulary): the CLI's stderr names
            # the exact problem and carries the fix line.
            raise ToolError(
                INVALID_PARAMS,
                "SPEC_INVALID",
                detail,
                {
                    "hint": (
                        "Fix the spec file: it must be a trailtracker.arch-spec/v1 "
                        "document {format, domains:[{name, pathPrefixes[]}], "
                        "rules:[{type, ...}]}. `trailtracker arch-init <dir>` "
                        "prints a valid example."
                    ),
                    "spec_path": spec_path,
                },
            )
        if rc == 3:
            raise ToolError(
                INVALID_PARAMS,
                "SPEC_NOT_FOUND",
                detail,
                {
                    "hint": (
                        "No architecture spec found. Bootstrap one from the "
                        "current recovered architecture with `trailtracker "
                        "arch-init %s -o %s/.trailtracker-arch.json`, commit "
                        "it, then call this tool again." % (repo_path, repo_path)
                    ),
                    "spec_path": spec_path,
                },
            )
        if rc not in (0, 1):
            raise ToolError(
                E_ANALYSIS_FAILED,
                "ANALYSIS_FAILED",
                "trailtracker failed (exit %d): %s" % (rc, detail),
                {
                    "hint": (
                        "Check that repo_path points at a source directory the "
                        "server process can read."
                    ),
                    "argv": args,
                    "stderr": detail,
                },
            )
        try:
            payload = json.loads(stdout)
        except ValueError as exc:
            raise ToolError(
                E_OUTPUT_UNPARSEABLE,
                "OUTPUT_UNPARSEABLE",
                "trailtracker arch-verify emitted non-JSON output: %s" % exc,
                {"hint": "This is a trailtracker bug, not a usage error.",
                 "output": stdout[:200]},
            )
        return text_result(json.dumps(payload, separators=(",", ":")))

    if name == "deadcode":
        min_confidence = arguments.get("min_confidence", "low")
        if min_confidence not in ("high", "medium", "low"):
            raise ToolError(
                INVALID_PARAMS,
                "INVALID_MIN_CONFIDENCE",
                "min_confidence must be high, medium, or low (got %r)."
                % (min_confidence,),
                {"hint": "Use 'high' for only top-confidence deletion candidates."},
            )
        limit = arguments.get("limit")
        if limit is not None and (
            isinstance(limit, bool) or not isinstance(limit, int) or limit < 0
        ):
            raise ToolError(
                INVALID_PARAMS,
                "INVALID_LIMIT",
                "limit must be a non-negative integer when provided (got %r)."
                % (limit,),
                {"hint": "Omit limit for the complete finding list."},
            )
        args = [
            "deadcode", repo_path, "--json",
            "--min-confidence", min_confidence,
        ]
        if limit is not None:
            args += ["--limit", str(limit)]
        rc, stdout, stderr = run_binary_status(args)
        detail = (stderr or "").strip() or "(no stderr)"
        if rc not in (0, 1):
            raise ToolError(
                E_ANALYSIS_FAILED,
                "ANALYSIS_FAILED",
                "trailtracker failed (exit %d): %s" % (rc, detail),
                {
                    "hint": (
                        "Check that repo_path points at a readable source "
                        "directory and that its deadcode config is valid."
                    ),
                    "argv": args,
                    "stderr": detail,
                },
            )
        try:
            payload = json.loads(stdout)
        except ValueError as exc:
            raise ToolError(
                E_OUTPUT_UNPARSEABLE,
                "OUTPUT_UNPARSEABLE",
                "trailtracker deadcode emitted non-JSON output: %s" % exc,
                {"hint": "This is a trailtracker bug, not a usage error.",
                 "output": stdout[:200]},
            )
        return text_result(json.dumps(payload, separators=(",", ":")))

    if name == "violations":
        # Exit 1 = violations present: that is DATA (the report), not an
        # error — same contract as arch_verify's findings.
        rc, stdout, stderr = run_binary_status(["violations", repo_path, "--json"])
        detail = (stderr or "").strip() or "(no stderr)"
        if rc not in (0, 1):
            raise ToolError(
                E_ANALYSIS_FAILED,
                "ANALYSIS_FAILED",
                "trailtracker failed (exit %d): %s" % (rc, detail),
                {
                    "hint": (
                        "Check that repo_path points at a source directory the "
                        "server process can read."
                    ),
                    "argv": ["violations", repo_path, "--json"],
                    "stderr": detail,
                },
            )
        try:
            payload = json.loads(stdout)
        except ValueError as exc:
            raise ToolError(
                E_OUTPUT_UNPARSEABLE,
                "OUTPUT_UNPARSEABLE",
                "trailtracker violations emitted non-JSON output: %s" % exc,
                {"hint": "This is a trailtracker bug, not a usage error.",
                 "output": stdout[:200]},
            )
        return text_result(json.dumps(payload, separators=(",", ":")))

    limit, offset = validate_paging(arguments)
    if name == "nav_pack":
        query = validate_query(arguments)
        budget = validate_nav_int(arguments, "budget", NAV_DEFAULT_BUDGET)
        fmt = validate_format(arguments)
        if fmt == "prose":
            stdout = run_binary(
                ["nav", "pack", query, repo_path,
                 "--format", "prose", "--budget", str(budget)]
            )
            return text_result(stdout)
        stdout = run_binary(
            ["nav", "pack", query, repo_path, "--json", "--budget", str(budget)]
        )
        try:
            payload = json.loads(stdout)
        except ValueError as exc:
            raise ToolError(
                E_OUTPUT_UNPARSEABLE,
                "OUTPUT_UNPARSEABLE",
                "trailtracker nav pack emitted non-JSON output: %s" % exc,
                {"hint": "This is a trailtracker bug, not a usage error.",
                 "output": stdout[:200]},
            )
        return text_result(json.dumps(payload, separators=(",", ":")))

    if name == "nav_expand":
        target = validate_target(arguments)
        budget = validate_nav_int(arguments, "budget", NAV_DEFAULT_BUDGET)
        depth = validate_nav_int(
            arguments, "depth", NAV_DEFAULT_DEPTH, maximum=NAV_MAX_DEPTH
        )
        cursor = validate_nav_int(arguments, "cursor", 0)
        direction = validate_direction(arguments)
        fmt = validate_format(arguments)
        if fmt == "prose":
            stdout = run_target_text(
                [
                    "nav", "expand", target, repo_path,
                    "--format", "prose",
                    "--depth", str(depth),
                    "--direction", direction,
                    "--budget", str(budget),
                    "--cursor", str(cursor),
                ],
                target,
            )
            return text_result(stdout)
        payload = run_target_json(
            [
                "nav", "expand", target, repo_path, "--json",
                "--depth", str(depth),
                "--direction", direction,
                "--budget", str(budget),
                "--cursor", str(cursor),
            ],
            target,
        )
        return text_result(json.dumps(payload, separators=(",", ":")))

    limit, offset = validate_paging(arguments)
    if name == "graph":
        stdout = run_binary(["graph", repo_path])
        envelope = jsonl_envelope("graph", None, repo_path, stdout, limit, offset)
    else:
        extractor = EXTRACTOR_TOOLS[name]
        stdout = run_binary(["extract", extractor, repo_path])
        envelope = jsonl_envelope(name, extractor, repo_path, stdout, limit, offset)
    return text_result(json.dumps(envelope, separators=(",", ":"), sort_keys=False))


def text_result(text):
    return {"content": [{"type": "text", "text": text}], "isError": False}


# --------------------------------------------------------------------------
# JSON-RPC plumbing (newline-delimited, per MCP stdio transport)
# --------------------------------------------------------------------------

def handle_request(msg):
    """Return a response dict, or None for notifications."""
    method = msg.get("method")
    msg_id = msg.get("id")
    params = msg.get("params") or {}
    is_notification = "id" not in msg

    if method == "initialize":
        client_version = params.get("protocolVersion", "")
        version = (
            client_version
            if client_version in SUPPORTED_PROTOCOL_VERSIONS
            else LATEST_PROTOCOL_VERSION
        )
        return ok(msg_id, {
            "protocolVersion": version,
            "capabilities": {"tools": {"listChanged": False}},
            "serverInfo": {
                "name": SERVER_NAME,
                "title": "TrailTracker code intelligence",
                "version": SERVER_VERSION,
            },
            "instructions": (
                "TrailTracker turns a repo into a deterministic code graph plus "
                "derived ontology views, all computed locally (no LLM, no "
                "network). Working a task on a large repo? Start with "
                "`nav_pack` (task description in, one character-budgeted exact "
                "context pack out: seeds, cards, orientation, a read-plan of "
                "file:line spans, and the dependency neighborhood), then read "
                "exactly those spans and grow with `nav_expand` "
                "(callers/callees, cursor-paged). Exploring instead? 1) `brief` "
                "for orientation, 2) `stats` to judge coverage, 3) `search` to "
                "find functions/types/files by concept or name (hybrid BM25 + "
                "embeddings + graph proximity, typo-tolerant, every hit "
                "explains its ranking), 4) `explain` for one card on any "
                "specific file or symbol (identity, domain/layer/archetype, "
                "fan-in/out, blast radius, neighbors), "
                "5) `domains`/`hierarchy`/`layers` "
                "to navigate, 6) `graph` (paged) only for raw nodes/edges. Every "
                "tool takes an absolute `repo_path`. Output is byte-deterministic: "
                "same repo in, same answer out."
            ),
        })
    if method in ("notifications/initialized", "notifications/cancelled"):
        return None
    if method == "ping":
        return ok(msg_id, {})
    if method == "tools/list":
        return ok(msg_id, {"tools": TOOLS})
    if method == "tools/call":
        name = params.get("name", "")
        arguments = params.get("arguments") or {}
        try:
            return ok(msg_id, call_tool(name, arguments))
        except ToolError as exc:
            return err(msg_id, exc.code, str(exc), exc.data)
    if is_notification:
        return None
    return err(msg_id, METHOD_NOT_FOUND, "Method not found: %s" % method,
               {"hint": "Supported: initialize, ping, tools/list, tools/call."})


def ok(msg_id, result):
    return {"jsonrpc": "2.0", "id": msg_id, "result": result}


def err(msg_id, code, message, data=None):
    e = {"code": code, "message": message}
    if data:
        e["data"] = data
    return {"jsonrpc": "2.0", "id": msg_id, "error": e}


def main():
    log("server starting (worktree=%s, pid=%d)" % (WORKTREE_ROOT, os.getpid()))
    out = sys.stdout
    for raw in sys.stdin:
        raw = raw.strip()
        if not raw:
            continue
        debug("<- %s" % raw[:500])
        try:
            msg = json.loads(raw)
        except ValueError as exc:
            response = err(None, PARSE_ERROR, "Parse error: %s" % exc)
        else:
            if not isinstance(msg, dict):
                # Valid JSON but not a Request object (`[1,2,3]`, `5`, `"x"`):
                # JSON-RPC 2.0 -32600, id null — and keep serving (UBS audit
                # C3: this used to raise AttributeError twice and kill the
                # transport).
                response = err(
                    None,
                    INVALID_REQUEST,
                    "Invalid Request: expected a JSON object, got %s"
                    % type(msg).__name__,
                )
            else:
                try:
                    response = handle_request(msg)
                except Exception as exc:  # never crash the transport
                    log("internal error: %r" % exc)
                    msg_id = msg.get("id") if isinstance(msg, dict) else None
                    response = err(msg_id, -32603, "Internal error: %s" % exc)
        if response is not None:
            line = json.dumps(response, separators=(",", ":"))
            debug("-> %s" % line[:500])
            out.write(line + "\n")
            out.flush()
    log("stdin closed; exiting")


if __name__ == "__main__":
    main()
