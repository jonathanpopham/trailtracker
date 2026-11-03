#!/usr/bin/env python3
"""End-to-end tests for the TrailTracker MCP server. Stdlib only, no mocks.

Spawns the real server as a subprocess, speaks real newline-delimited
JSON-RPC 2.0 over its stdio, and drives the real trailtracker binary on the
real eval corpus. Deterministic: asserts on structure and on facts that only
change if the corpus or the extractors change.

Run: python3 mcp/test_mcp.py            (exit 0 = all green)
     TRAILTRACKER_MCP_LOG=debug python3 mcp/test_mcp.py   (server chatter too)
"""

import json
import os
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
WORKTREE = HERE.parent
SERVER = HERE / "trailtracker_mcp.py"
CALC = WORKTREE / "eval" / "corpus" / "calc"

PASS, FAIL = 0, 0


def check(label, condition, detail=""):
    global PASS, FAIL
    if condition:
        PASS += 1
        print("  [PASS] %s" % label)
    else:
        FAIL += 1
        print("  [FAIL] %s%s" % (label, (" — " + detail) if detail else ""))


class Client:
    """Minimal MCP stdio client."""

    def __init__(self, env=None, capture_stderr=False):
        full_env = dict(os.environ)
        full_env.update(env or {})
        self.proc = subprocess.Popen(
            [sys.executable, str(SERVER)],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            # By default server logs pass through to our stderr; tests that
            # assert on warnings capture it instead.
            stderr=subprocess.PIPE if capture_stderr else None,
            text=True,
            env=full_env,
        )
        self._next_id = 0

    def request(self, method, params=None, timeout=300):
        self._next_id += 1
        msg = {"jsonrpc": "2.0", "id": self._next_id, "method": method}
        if params is not None:
            msg["params"] = params
        line = json.dumps(msg)
        print("    -> %s %s" % (method, json.dumps(params or {})[:120]))
        t0 = time.monotonic()
        self.proc.stdin.write(line + "\n")
        self.proc.stdin.flush()
        raw = self.proc.stdout.readline()
        elapsed = time.monotonic() - t0
        if not raw:
            raise RuntimeError("server closed stdout (crashed?)")
        resp = json.loads(raw)
        kind = "error" if "error" in resp else "result"
        print("    <- %s in %.2fs (%d bytes)" % (kind, elapsed, len(raw)))
        assert resp.get("id") == self._next_id, "response id mismatch"
        return resp

    def notify(self, method, params=None):
        msg = {"jsonrpc": "2.0", "method": method}
        if params is not None:
            msg["params"] = params
        self.proc.stdin.write(json.dumps(msg) + "\n")
        self.proc.stdin.flush()

    def send_raw(self, line):
        """Send a raw line (possibly malformed JSON-RPC), return the response."""
        print("    -> raw %s" % line[:120])
        self.proc.stdin.write(line + "\n")
        self.proc.stdin.flush()
        raw = self.proc.stdout.readline()
        if not raw:
            raise RuntimeError("server closed stdout (crashed?)")
        return json.loads(raw)

    def close(self):
        self.proc.stdin.close()
        self.proc.wait(timeout=10)


def tool_text(resp):
    return resp["result"]["content"][0]["text"]


def main():
    print("== TrailTracker MCP e2e ==")
    print("server: %s" % SERVER)
    print("corpus: %s" % CALC)
    assert CALC.is_dir(), "eval corpus missing: %s" % CALC

    c = Client()

    # -- initialize handshake ------------------------------------------------
    print("\n[1] initialize")
    resp = c.request("initialize", {
        "protocolVersion": "2025-06-18",
        "capabilities": {},
        "clientInfo": {"name": "e2e-test", "version": "0"},
    })
    r = resp.get("result", {})
    check("returns result", "result" in resp)
    check("serverInfo.name == trailtracker",
          r.get("serverInfo", {}).get("name") == "trailtracker")
    check("echoes supported protocolVersion",
          r.get("protocolVersion") == "2025-06-18")
    check("advertises tools capability", "tools" in r.get("capabilities", {}))
    check("has instructions", bool(r.get("instructions")))
    c.notify("notifications/initialized")

    # -- tools/list ----------------------------------------------------------
    print("\n[2] tools/list")
    resp = c.request("tools/list")
    tools = {t["name"]: t for t in resp["result"]["tools"]}
    expected = ["brief", "stats", "graph", "domains", "archetypes", "layers",
                "lexicon", "hierarchy", "data_ontology", "workflow_spec",
                "search", "explain", "nav_pack", "nav_expand", "arch_verify",
                "deadcode", "violations"]
    for name in expected:
        check("tool present: %s" % name, name in tools)
    check("exactly %d tools" % len(expected), len(tools) == len(expected),
          "got %s" % sorted(tools))
    for name, t in sorted(tools.items()):
        schema = t.get("inputSchema", {})
        if name in ("search", "nav_pack"):
            want_required = ["repo_path", "query"]
        elif name in ("explain", "nav_expand"):
            want_required = ["repo_path", "target"]
        else:
            want_required = ["repo_path"]
        check("%s: required == %s" % (name, want_required),
              schema.get("required") == want_required)
        check("%s: has description" % name, len(t.get("description", "")) > 40)
    check("search: documents limit with a cap",
          tools["search"]["inputSchema"]["properties"]
          .get("limit", {}).get("maximum") == 200)
    for name in ("graph", "domains", "hierarchy"):
        props = tools[name]["inputSchema"]["properties"]
        check("%s: documents limit+offset" % name,
              "limit" in props and "offset" in props)

    # -- tools/call brief (markdown) ------------------------------------------
    print("\n[3] tools/call brief on eval/corpus/calc")
    resp = c.request("tools/call",
                     {"name": "brief", "arguments": {"repo_path": str(CALC)}})
    text = tool_text(resp)
    check("brief is markdown with title",
          text.startswith("# Codebase brief:"), text[:80])
    check("brief has Overview section", "## Overview" in text)
    check("brief detects rust", "rust" in text)
    check("brief is non-trivial (>500 bytes)", len(text) > 500)

    # -- tools/call domains (JSONL envelope) ----------------------------------
    print("\n[4] tools/call domains on eval/corpus/calc")
    resp = c.request("tools/call",
                     {"name": "domains", "arguments": {"repo_path": str(CALC)}})
    env = json.loads(tool_text(resp))
    check("envelope.tool == domains", env.get("tool") == "domains")
    check("envelope.extractor == domains", env.get("extractor") == "domains")
    check("has records", env.get("total_records", 0) > 0)
    check("returned == len(records)", env.get("returned") == len(env["records"]))
    check("not truncated (small corpus)", env.get("truncated") is False)
    views = {n.get("properties", {}).get("view") for n in env["records"]
             if n.get("record") == "node"}
    check("records carry view=domains", "domains" in views, str(views))
    domain_nodes = [n for n in env["records"]
                    if "domain" in n.get("properties", {})
                    and "unit_count" in n.get("properties", {})]
    check("at least one domain cluster node", len(domain_nodes) >= 1)

    # -- determinism ----------------------------------------------------------
    print("\n[5] determinism: domains twice, byte-identical")
    resp2 = c.request("tools/call",
                      {"name": "domains", "arguments": {"repo_path": str(CALC)}})
    check("identical output across calls", tool_text(resp) == tool_text(resp2))

    # -- stats ----------------------------------------------------------------
    print("\n[6] tools/call stats")
    resp = c.request("tools/call",
                     {"name": "stats", "arguments": {"repo_path": str(CALC)}})
    text = tool_text(resp)
    check("stats mentions files analyzed", "files analyzed" in text)
    check("stats mentions graph nodes", "graph nodes" in text)

    # -- graph pagination ------------------------------------------------------
    print("\n[7] tools/call graph with limit=10 (pagination)")
    resp = c.request("tools/call", {"name": "graph", "arguments": {
        "repo_path": str(CALC), "limit": 10}})
    env = json.loads(tool_text(resp))
    check("returned == 10", env.get("returned") == 10, str(env.get("returned")))
    check("truncated flagged", env.get("truncated") is True)
    check("next_offset == 10", env.get("next_offset") == 10)
    total = env.get("total_records", 0)
    check("total_records > 10", total > 10, str(total))
    resp = c.request("tools/call", {"name": "graph", "arguments": {
        "repo_path": str(CALC), "limit": 10, "offset": 10}})
    env2 = json.loads(tool_text(resp))
    check("page 2 offset honored", env2.get("offset") == 10)
    check("pages don't overlap",
          env["records"][-1] != env2["records"][0] if env2["records"] else False)
    resp = c.request("tools/call", {"name": "graph", "arguments": {
        "repo_path": str(CALC), "limit": 0}})
    env3 = json.loads(tool_text(resp))
    check("limit=0 returns everything", env3.get("returned") == total)

    # -- every extractor tool answers -----------------------------------------
    print("\n[8] every extractor tool returns a valid envelope")
    for name in ("archetypes", "layers", "lexicon", "hierarchy",
                 "data_ontology", "workflow_spec"):
        resp = c.request("tools/call",
                         {"name": name, "arguments": {"repo_path": str(CALC)}})
        if "error" in resp:
            check("%s answers" % name, False, str(resp["error"])[:150])
            continue
        env = json.loads(tool_text(resp))
        check("%s envelope valid" % name,
              env.get("tool") == name and isinstance(env.get("records"), list))

    # -- search (tool #11) -------------------------------------------------------
    print("\n[8b] tools/call search on eval/corpus/calc")
    search_args = {"repo_path": str(CALC), "query": "parse"}
    resp = c.request("tools/call", {"name": "search", "arguments": search_args})
    env = json.loads(tool_text(resp))
    check("search schema", env.get("schema") == "trailtracker.search/v1",
          str(env)[:150])
    check("search echoes query + dir",
          env.get("query") == "parse" and env.get("dir") == str(CALC))
    results = env.get("results", [])
    check("search has results", env.get("total", 0) > 0 and len(results) > 0)
    check("total == len(results)", env.get("total") == len(results))
    top = results[0] if results else {}
    check("top hit is the parse fn",
          top.get("name") == "parse" and top.get("kind") == "Function",
          json.dumps(top)[:150])
    check("every result carries why[]",
          all(isinstance(r.get("why"), list) and r["why"] for r in results))
    check("ranks are 1-based ascending",
          [r.get("rank") for r in results] == list(range(1, len(results) + 1)))
    check("every result has id/name/kind/path/score",
          all(all(k in r for k in ("id", "name", "kind", "path", "score"))
              for r in results))
    resp2 = c.request("tools/call", {"name": "search", "arguments": search_args})
    check("search deterministic across calls",
          tool_text(resp) == tool_text(resp2))
    resp = c.request("tools/call", {"name": "search", "arguments": {
        "repo_path": str(CALC), "query": "parse", "limit": 1}})
    env = json.loads(tool_text(resp))
    check("limit=1 returns exactly one result", env.get("total") == 1)
    resp = c.request("tools/call", {"name": "search", "arguments": {
        "repo_path": str(CALC), "query": "parse", "limit": 5000}})
    check("limit above 200 is capped, not an error",
          "result" in resp and
          json.loads(tool_text(resp)).get("total", -1) <= 200,
          str(resp.get("error", ""))[:150])

    # -- explain (tool #12) -------------------------------------------------------
    print("\n[8c] tools/call explain on eval/corpus/calc")
    explain_args = {"repo_path": str(CALC), "target": "parse"}
    resp = c.request("tools/call", {"name": "explain", "arguments": explain_args})
    env = json.loads(tool_text(resp))
    check("explain schema", env.get("schema") == "trailtracker.explain/v1",
          str(env)[:150])
    check("explain echoes target + dir",
          env.get("target") == "parse" and env.get("dir") == str(CALC))
    identity = env.get("identity", {})
    check("identity resolves the parse fn",
          identity.get("id") == "fn::crate::parser::parse#7"
          and identity.get("kind") == "Function"
          and identity.get("path") == "src/parser.rs"
          and identity.get("line") == 7,
          json.dumps(identity)[:200])
    classification = env.get("classification", {})
    check("classification carries domain/layer/archetype",
          all(isinstance(classification.get(k), str) and classification[k]
              for k in ("domain", "layer", "archetype")),
          json.dumps(classification)[:150])
    connectivity = env.get("connectivity", {})
    check("connectivity has fan counts + listings",
          isinstance(connectivity.get("fan_in"), int)
          and isinstance(connectivity.get("fan_out"), int)
          and isinstance(connectivity.get("dependents"), list)
          and isinstance(connectivity.get("dependencies"), list))
    blast = env.get("blast_radius", {})
    check("blast radius has count + examples",
          blast.get("count", 0) > 0 and isinstance(blast.get("examples"), list),
          json.dumps(blast)[:150])
    neighbors = env.get("neighbors", [])
    check("neighbors exclude the target and carry why[]",
          all(n.get("id") != identity.get("id") and n.get("why")
              for n in neighbors))
    resp2 = c.request("tools/call", {"name": "explain", "arguments": explain_args})
    check("explain deterministic across calls",
          tool_text(resp) == tool_text(resp2))
    # A file path resolves to the File node.
    resp = c.request("tools/call", {"name": "explain", "arguments": {
        "repo_path": str(CALC), "target": "src/parser.rs"}})
    env = json.loads(tool_text(resp))
    check("explain resolves a file path",
          env.get("identity", {}).get("id") == "file::src/parser.rs",
          str(env.get("identity"))[:150])

    # Ambiguous name -> AMBIGUOUS_TARGET with the candidate list.
    resp = c.request("tools/call", {"name": "explain", "arguments": {
        "repo_path": str(CALC), "target": "reset"}})
    e = resp.get("error", {})
    check("ambiguous target -> -32602 AMBIGUOUS_TARGET",
          e.get("code") == -32602
          and e.get("data", {}).get("type") == "AMBIGUOUS_TARGET",
          str(e)[:200])
    check("ambiguous error names both candidates",
          "fn::crate::reset#18" in e.get("message", "")
          and "fn::crate::ops::reset#60" in e.get("message", ""),
          e.get("message", "")[:200])

    # Unknown target -> TARGET_NOT_FOUND with suggestions.
    resp = c.request("tools/call", {"name": "explain", "arguments": {
        "repo_path": str(CALC), "target": "NoSuchSymbolAnywhere"}})
    e = resp.get("error", {})
    check("unknown target -> -32602 TARGET_NOT_FOUND",
          e.get("code") == -32602
          and e.get("data", {}).get("type") == "TARGET_NOT_FOUND",
          str(e)[:200])
    check("not-found error carries a hint", "hint" in e.get("data", {}))

    # Missing/blank target -> MISSING_TARGET.
    resp = c.request("tools/call", {"name": "explain", "arguments": {
        "repo_path": str(CALC)}})
    e = resp.get("error", {})
    check("explain missing target -> -32602 MISSING_TARGET with hint",
          e.get("code") == -32602
          and e.get("data", {}).get("type") == "MISSING_TARGET"
          and "hint" in e.get("data", {}), str(e)[:150])
    resp = c.request("tools/call", {"name": "explain", "arguments": {
        "repo_path": str(CALC), "target": "   "}})
    e = resp.get("error", {})
    check("explain blank target rejected",
          e.get("data", {}).get("type") == "MISSING_TARGET", str(e)[:150])

    # -- nav_pack (tool #13) ------------------------------------------------------
    print("\n[8d] tools/call nav_pack on eval/corpus/calc")
    pack_args = {"repo_path": str(CALC), "query": "parse expression"}
    resp = c.request("tools/call", {"name": "nav_pack", "arguments": pack_args})
    env = json.loads(tool_text(resp))
    check("nav_pack schema", env.get("schema") == "trailtracker.nav-pack/v1",
          str(env)[:150])
    check("nav_pack echoes query + dir",
          env.get("query") == "parse expression" and env.get("dir") == str(CALC))
    budget = env.get("budget", {})
    check("budget block is char-named (no tokens anywhere)",
          all(k in budget for k in
              ("budget_chars", "used_chars", "estimated_chars",
               "truncated", "exceeded", "omitted"))
          and "token" not in json.dumps(budget),
          json.dumps(budget)[:200])
    check("budget default is %d" % 20000, budget.get("budget_chars") == 20000)
    seeds = env.get("seeds", [])
    check("seeds present with why[]",
          seeds and all(s.get("why") for s in seeds), str(seeds)[:150])
    check("top seed is the parse fn",
          seeds and seeds[0].get("id") == "fn::crate::parser::parse#7",
          str(seeds[:1])[:150])
    cards = env.get("cards", [])
    check("cards carry classification + impact",
          cards and all(
              all(k in cd for k in ("domain", "layer", "archetype",
                                    "fan_in", "fan_out", "blast_count"))
              for cd in cards),
          str(cards[:1])[:200])
    plan = env.get("read_plan", [])
    check("read_plan entries are spans (path + start_line)",
          plan and all("path" in p and "start_line" in p for p in plan),
          str(plan[:1])[:150])
    hood = env.get("neighborhood", {})
    check("neighborhood has depth/nodes/edges",
          hood.get("depth") == 2 and hood.get("node_count", 0) > 0
          and isinstance(hood.get("edges"), list), str(hood)[:150])
    resp2 = c.request("tools/call", {"name": "nav_pack", "arguments": pack_args})
    check("nav_pack deterministic across calls",
          tool_text(resp) == tool_text(resp2))
    # A tight budget truncates honestly and the payload fits.
    resp = c.request("tools/call", {"name": "nav_pack", "arguments": {
        "repo_path": str(CALC), "query": "parse expression", "budget": 2000}})
    text = tool_text(resp)
    env = json.loads(text)
    check("tight budget fits (%d <= 2000)" % len(text), len(text) <= 2000)
    check("tight budget marks truncated",
          env.get("budget", {}).get("truncated") is True)
    check("omitted counts are exact ints",
          all(isinstance(v, int)
              for v in env.get("budget", {}).get("omitted", {}).values()))
    resp = c.request("tools/call", {"name": "nav_pack", "arguments": {
        "repo_path": str(CALC)}})
    e = resp.get("error", {})
    check("nav_pack missing query -> MISSING_QUERY",
          e.get("data", {}).get("type") == "MISSING_QUERY", str(e)[:150])

    # -- nav_expand (tool #14) ----------------------------------------------------
    print("\n[8e] tools/call nav_expand on eval/corpus/calc")
    expand_args = {"repo_path": str(CALC),
                   "target": "fn::crate::parser::parse#7", "depth": 2}
    resp = c.request("tools/call", {"name": "nav_expand", "arguments": expand_args})
    env = json.loads(tool_text(resp))
    check("nav_expand schema", env.get("schema") == "trailtracker.nav-expand/v1",
          str(env)[:150])
    check("identity resolves the target",
          env.get("identity", {}).get("id") == "fn::crate::parser::parse#7")
    check("direction defaults to both", env.get("direction") == "both")
    check("edges carry from/kind/to/hops",
          env.get("edges") and all(
              all(k in ed for k in ("from", "kind", "to", "hops"))
              for ed in env["edges"]),
          str(env.get("edges", [])[:1])[:150])
    check("nodes table names the endpoints",
          env.get("nodes") and all("name" in n and "kind" in n
                                   for n in env["nodes"]))
    check("full budget -> not truncated, next_cursor null",
          env.get("truncated") is False and env.get("next_cursor") is None)
    # Cursor paging: a tight budget truncates, the cursor resumes.
    resp = c.request("tools/call", {"name": "nav_expand", "arguments": {
        "repo_path": str(CALC), "target": "fn::crate::parser::parse#7",
        "depth": 2, "budget": 1500}})
    page1 = json.loads(tool_text(resp))
    check("tight budget truncates with a next_cursor",
          page1.get("truncated") is True
          and isinstance(page1.get("next_cursor"), int), str(page1)[:200])
    resp = c.request("tools/call", {"name": "nav_expand", "arguments": {
        "repo_path": str(CALC), "target": "fn::crate::parser::parse#7",
        "depth": 2, "budget": 1500, "cursor": page1.get("next_cursor")}})
    page2 = json.loads(tool_text(resp))
    check("cursor resumes where page 1 ended",
          page2.get("cursor") == page1.get("next_cursor")
          and page2.get("returned", 0) > 0)
    first_page1 = page1.get("edges", [{}])[0]
    check("pages do not overlap",
          first_page1 not in page2.get("edges", []), str(first_page1)[:100])
    # Directions: callers-only edges all point at the target at depth 1.
    resp = c.request("tools/call", {"name": "nav_expand", "arguments": {
        "repo_path": str(CALC), "target": "fn::crate::parser::parse#7",
        "depth": 1, "direction": "callers"}})
    env = json.loads(tool_text(resp))
    check("callers direction honored",
          env.get("direction") == "callers"
          and all(ed.get("to") == "fn::crate::parser::parse#7"
                  for ed in env.get("edges", [])),
          str(env.get("edges"))[:200])
    resp = c.request("tools/call", {"name": "nav_expand", "arguments": {
        "repo_path": str(CALC), "target": "parse", "direction": "sideways"}})
    e = resp.get("error", {})
    check("bad direction -> INVALID_DIRECTION",
          e.get("data", {}).get("type") == "INVALID_DIRECTION", str(e)[:150])
    # The explain resolution contract is shared.
    resp = c.request("tools/call", {"name": "nav_expand", "arguments": {
        "repo_path": str(CALC), "target": "reset"}})
    e = resp.get("error", {})
    check("nav_expand ambiguous -> AMBIGUOUS_TARGET",
          e.get("code") == -32602
          and e.get("data", {}).get("type") == "AMBIGUOUS_TARGET", str(e)[:200])
    resp = c.request("tools/call", {"name": "nav_expand", "arguments": {
        "repo_path": str(CALC), "target": "NoSuchSymbolAnywhere"}})
    e = resp.get("error", {})
    check("nav_expand unknown -> TARGET_NOT_FOUND",
          e.get("data", {}).get("type") == "TARGET_NOT_FOUND", str(e)[:200])
    resp = c.request("tools/call", {"name": "nav_expand", "arguments": {
        "repo_path": str(CALC), "target": "parse", "budget": -1}})
    e = resp.get("error", {})
    check("nav_expand negative budget rejected",
          e.get("data", {}).get("type") == "INVALID_BUDGET", str(e)[:150])

    # -- error shapes -----------------------------------------------------------
    # -- arch_verify (tool #13) ---------------------------------------------
    print("\n[8d] tools/call arch_verify on eval/corpus/sflinked")
    import tempfile
    sflinked = WORKTREE / "eval" / "corpus" / "sflinked"
    violated_spec = {
        "format": "trailtracker.arch-spec/v1",
        "domains": [
            {"name": "Classes",
             "pathPrefixes": ["force-app/main/default/classes/"]},
            {"name": "Flows",
             "pathPrefixes": ["force-app/main/default/flows/"]},
        ],
        "rules": [
            {"type": "forbidden-dependency", "from": "Flows", "to": "Classes"},
        ],
    }
    with tempfile.TemporaryDirectory(prefix="tt-mcp-arch-") as tmp:
        spec_file = Path(tmp) / "arch.json"
        spec_file.write_text(json.dumps(violated_spec))
        arch_args = {"repo_path": str(sflinked), "spec_path": str(spec_file)}
        resp = c.request("tools/call",
                         {"name": "arch_verify", "arguments": arch_args})
        env = json.loads(tool_text(resp))
        check("arch_verify schema",
              env.get("format") == "trailtracker.arch-verify/v1",
              str(env)[:150])
        check("violated spec -> status violated, exit 1 (as DATA, not error)",
              env.get("status") == "violated" and env.get("exit") == 1,
              str(env)[:200])
        findings = env.get("findings", [])
        check("finding carries id/severity/count/examples",
              len(findings) == 1
              and findings[0].get("id") == "forbidden-dependency:Flows->Classes"
              and findings[0].get("severity") == "error"
              and findings[0].get("count", 0) >= 1
              and findings[0].get("examples"),
              json.dumps(findings)[:250])
        resp2 = c.request("tools/call",
                          {"name": "arch_verify", "arguments": arch_args})
        check("arch_verify deterministic across calls",
              tool_text(resp) == tool_text(resp2))

        # Malformed spec -> SPEC_INVALID with the CLI's fix text.
        bad_file = Path(tmp) / "bad.json"
        bad_file.write_text("not json {{{")
        resp = c.request("tools/call", {"name": "arch_verify", "arguments": {
            "repo_path": str(sflinked), "spec_path": str(bad_file)}})
        e = resp.get("error", {})
        check("garbage spec -> -32602 SPEC_INVALID",
              e.get("code") == -32602
              and e.get("data", {}).get("type") == "SPEC_INVALID",
              str(e)[:200])
        check("SPEC_INVALID carries a hint", "hint" in e.get("data", {}))

    # No spec anywhere -> SPEC_NOT_FOUND with the bootstrap hint.
    resp = c.request("tools/call", {"name": "arch_verify", "arguments": {
        "repo_path": str(sflinked)}})
    e = resp.get("error", {})
    check("missing spec -> -32602 SPEC_NOT_FOUND",
          e.get("code") == -32602
          and e.get("data", {}).get("type") == "SPEC_NOT_FOUND",
          str(e)[:200])
    check("SPEC_NOT_FOUND hint names arch-init",
          "arch-init" in e.get("data", {}).get("hint", ""), str(e)[:200])

    # Blank spec_path -> INVALID_SPEC_PATH.
    resp = c.request("tools/call", {"name": "arch_verify", "arguments": {
        "repo_path": str(sflinked), "spec_path": "   "}})
    e = resp.get("error", {})
    check("blank spec_path rejected",
          e.get("data", {}).get("type") == "INVALID_SPEC_PATH", str(e)[:150])

    # -- deadcode (tool #16) ------------------------------------------------
    print("\n[8e] tools/call deadcode on eval/corpus/calc")
    resp = c.request("tools/call", {"name": "deadcode", "arguments": {
        "repo_path": str(CALC), "min_confidence": "high", "limit": 1}})
    env = json.loads(tool_text(resp))
    check("deadcode schema",
          env.get("schema") == "trailtracker.deadcode/v1", str(env)[:150])
    check("deadcode report shape",
          isinstance(env.get("summary"), dict)
          and isinstance(env.get("findings"), list)
          and isinstance(env.get("roots"), list)
          and len(env.get("findings", [])) <= 1,
          str(env)[:250])
    resp2 = c.request("tools/call", {"name": "deadcode", "arguments": {
        "repo_path": str(CALC), "min_confidence": "high", "limit": 1}})
    check("deadcode deterministic across calls",
          tool_text(resp) == tool_text(resp2))

    # -- violations (tool #17) ----------------------------------------------
    print("\n[8f] tools/call violations on eval/corpus/calc")
    resp = c.request("tools/call",
                     {"name": "violations", "arguments": {"repo_path": str(CALC)}})
    env = json.loads(tool_text(resp))
    check("violations schema",
          env.get("schema") == "trailtracker.violations/v1", str(env)[:150])
    check("violations status is clean|violations with matching exit",
          (env.get("status"), env.get("exit")) in (("clean", 0), ("violations", 1)),
          str(env)[:150])
    check("violations report shape (layer_pairs + violations lists)",
          isinstance(env.get("layer_pairs"), list)
          and isinstance(env.get("violations"), list)
          and all(("from_unit" in v and "to_unit" in v and "from_layer" in v
                   and "to_layer" in v and "count" in v and "examples" in v)
                  for v in env.get("violations", [])),
          str(env)[:250])
    resp2 = c.request("tools/call",
                      {"name": "violations", "arguments": {"repo_path": str(CALC)}})
    check("violations deterministic across calls",
          tool_text(resp) == tool_text(resp2))

    print("\n[9] error shapes are structured and actionable")
    resp = c.request("tools/call",
                     {"name": "no_such_tool", "arguments": {"repo_path": str(CALC)}})
    e = resp.get("error", {})
    check("unknown tool -> -32602", e.get("code") == -32602)
    check("unknown tool lists available",
          "brief" in e.get("data", {}).get("available_tools", []))

    resp = c.request("tools/call", {"name": "brief", "arguments": {}})
    e = resp.get("error", {})
    check("missing repo_path -> -32602 with hint",
          e.get("code") == -32602 and "hint" in e.get("data", {}))

    resp = c.request("tools/call", {"name": "brief", "arguments": {
        "repo_path": "/no/such/dir/anywhere"}})
    e = resp.get("error", {})
    check("bad path -> REPO_PATH_NOT_FOUND",
          e.get("data", {}).get("type") == "REPO_PATH_NOT_FOUND", str(e)[:150])

    resp = c.request("tools/call", {"name": "brief", "arguments": {
        "repo_path": "/path/to/your_repo"}})
    e = resp.get("error", {})
    check("placeholder path detected",
          e.get("data", {}).get("type") == "PLACEHOLDER_PATH", str(e)[:150])

    resp = c.request("tools/call", {"name": "graph", "arguments": {
        "repo_path": str(CALC), "limit": -5}})
    e = resp.get("error", {})
    check("negative limit rejected",
          e.get("data", {}).get("type") == "INVALID_PAGING", str(e)[:150])

    resp = c.request("tools/call", {"name": "search", "arguments": {
        "repo_path": str(CALC)}})
    e = resp.get("error", {})
    check("search missing query -> -32602 MISSING_QUERY with hint",
          e.get("code") == -32602
          and e.get("data", {}).get("type") == "MISSING_QUERY"
          and "hint" in e.get("data", {}), str(e)[:150])

    resp = c.request("tools/call", {"name": "search", "arguments": {
        "repo_path": str(CALC), "query": "   "}})
    e = resp.get("error", {})
    check("search blank query rejected",
          e.get("data", {}).get("type") == "MISSING_QUERY", str(e)[:150])

    resp = c.request("tools/call", {"name": "search", "arguments": {
        "repo_path": str(CALC), "query": "parse", "limit": -3}})
    e = resp.get("error", {})
    check("search negative limit rejected",
          e.get("data", {}).get("type") == "INVALID_LIMIT", str(e)[:150])

    resp = c.request("no/such/method")
    check("unknown method -> -32601",
          resp.get("error", {}).get("code") == -32601)

    # -- C3: non-object JSON must not kill the transport ------------------------
    print("\n[10] valid-JSON-but-not-object lines -> -32600, server keeps serving")
    for bad in ("[1,2,3]", "5", '"x"'):
        resp = c.send_raw(bad)
        e = resp.get("error", {})
        check("%s -> -32600 Invalid Request" % bad,
              e.get("code") == -32600, str(resp)[:150])
        check("%s -> id is null" % bad,
              "id" in resp and resp.get("id") is None, str(resp)[:150])
    # Malformed JSON still gets the parse error, not a crash.
    resp = c.send_raw("{not json")
    check("malformed JSON -> -32700",
          resp.get("error", {}).get("code") == -32700, str(resp)[:150])
    resp = c.request("ping")
    check("server still serving after invalid requests", resp.get("result") == {})

    # -- C4: TRAILTRACKER_TIMEOUT_SECS is validated at startup -------------------
    print("\n[11] TRAILTRACKER_TIMEOUT_SECS validation")
    for bad in ("5m", "-1", "0", ""):
        c2 = Client(env={"TRAILTRACKER_TIMEOUT_SECS": bad}, capture_stderr=True)
        try:
            resp = c2.request("ping")
            check("server starts and serves with TIMEOUT_SECS=%r" % bad,
                  resp.get("result") == {})
        except Exception as exc:
            check("server starts and serves with TIMEOUT_SECS=%r" % bad,
                  False, repr(exc))
        c2.close()
        stderr = c2.proc.stderr.read()
        check("TIMEOUT_SECS=%r warns and falls back on stderr" % bad,
              "warning" in stderr and "TRAILTRACKER_TIMEOUT_SECS" in stderr,
              stderr[:200])
    c2 = Client(env={"TRAILTRACKER_TIMEOUT_SECS": "600"}, capture_stderr=True)
    resp = c2.request("ping")
    check("valid TIMEOUT_SECS=600 accepted", resp.get("result") == {})
    c2.close()
    stderr = c2.proc.stderr.read()
    check("no warning for a valid TIMEOUT_SECS", "warning" not in stderr,
          stderr[:200])

    # -- ping + clean shutdown --------------------------------------------------
    print("\n[12] ping + shutdown")
    resp = c.request("ping")
    check("ping -> {}", resp.get("result") == {})
    c.close()
    check("clean exit on stdin close", c.proc.returncode == 0,
          "rc=%s" % c.proc.returncode)

    print("\n== %d passed, %d failed ==" % (PASS, FAIL))
    return 1 if FAIL else 0


if __name__ == "__main__":
    sys.exit(main())
