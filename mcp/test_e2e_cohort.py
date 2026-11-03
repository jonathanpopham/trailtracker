#!/usr/bin/env python3
"""gs-B4 e2e: drive the MCP server against real cohort repos (a .NET one and a
non-.NET one) end to end — brief, domains, paged hierarchy, archetypes, and the
error shape. Needs COHORT_DIR (with eShop/ and django/) and a built binary.
Run: COHORT_DIR=... TRAILTRACKER_BIN=... python3 mcp/test_e2e_cohort.py
"""
import json, os, subprocess, sys

COHORT = os.environ.get("COHORT_DIR")
if not COHORT or not os.path.isdir(f"{COHORT}/eShop") or not os.path.isdir(f"{COHORT}/django"):
    print("SKIP: COHORT_DIR with eShop/ and django/ required"); sys.exit(0)

HERE = os.path.dirname(os.path.abspath(__file__))
proc = subprocess.Popen(["python3", f"{HERE}/trailtracker_mcp.py"],
                        stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)

def rpc(i, method, params=None):
    req = {"jsonrpc": "2.0", "id": i, "method": method}
    if params: req["params"] = params
    proc.stdin.write(json.dumps(req) + "\n"); proc.stdin.flush()
    while True:
        line = proc.stdout.readline()
        if not line: raise RuntimeError("server died")
        o = json.loads(line)
        if o.get("id") == i: return o

ok = fail = 0
def check(name, cond, detail=""):
    global ok, fail
    status = "PASS" if cond else "FAIL"
    print(f"  [{status}] {name} {detail}")
    if cond: ok += 1
    else: fail += 1

rpc(1, "initialize", {"protocolVersion": "2024-11-05", "capabilities": {},
                      "clientInfo": {"name": "b4", "version": "1"}})

r = rpc(2, "tools/call", {"name": "brief", "arguments": {"repo_path": f"{COHORT}/eShop"}})
txt = r["result"]["content"][0]["text"]
check("eShop brief", "# Codebase brief" in txt and "csharp" in txt, f"({len(txt)}ch)")

r = rpc(3, "tools/call", {"name": "domains", "arguments": {"repo_path": f"{COHORT}/eShop", "limit": 50}})
env = json.loads(r["result"]["content"][0]["text"])
doms = [x["properties"]["domain"] for x in env["records"]
        if x.get("properties", {}).get("domain") and "unit_count" in x.get("properties", {})]
check("eShop domains", any(d in doms for d in ("Ordering", "Order")) and any("Basket" in d for d in doms),
      f"domains={doms[:6]}")

r = rpc(4, "tools/call", {"name": "hierarchy", "arguments": {"repo_path": f"{COHORT}/eShop", "limit": 10}})
env = json.loads(r["result"]["content"][0]["text"])
check("eShop hierarchy paged", env["truncated"] and env["returned"] == 10 and env["total_records"] > 3000,
      f"total={env['total_records']}")

r = rpc(5, "tools/call", {"name": "brief", "arguments": {"repo_path": f"{COHORT}/django"}})
check("django brief", "python" in r["result"]["content"][0]["text"])

r = rpc(6, "tools/call", {"name": "domains", "arguments": {"repo_path": f"{COHORT}/django", "limit": 60}})
env = json.loads(r["result"]["content"][0]["text"])
doms = [x["properties"]["domain"] for x in env["records"]
        if x.get("properties", {}).get("domain") and "unit_count" in x.get("properties", {})]
check("django domains (non-.NET)", len(doms) >= 5, f"n={len(doms)}")

r = rpc(7, "tools/call", {"name": "archetypes", "arguments": {"repo_path": f"{COHORT}/django", "limit": 40}})
env = json.loads(r["result"]["content"][0]["text"])
archs = {x["properties"]["archetype"] for x in env["records"] if x.get("properties", {}).get("archetype")}
check("django archetypes", bool({"Controller", "Entity"} & archs), f"kinds={sorted(archs)[:6]}")

r = rpc(8, "tools/call", {"name": "brief", "arguments": {"repo_path": "/no/such/dir"}})
check("error shape", "error" in r and r["error"]["data"]["type"] == "REPO_PATH_NOT_FOUND")

proc.stdin.close(); proc.wait(timeout=10)
print(f"\n== {ok} passed, {fail} failed ==")
sys.exit(1 if fail else 0)
