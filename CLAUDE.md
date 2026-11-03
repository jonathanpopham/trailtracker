# trailtracker

## Context flywheel (nav-first)

FIRST action on any code task in this repo (use YOUR checkout/worktree dir):

    ./target/release/trailtracker nav pack "<task>" <your-checkout-dir> --budget 20000 --json

- Read ONLY the `read_plan` spans it returns (Read with offset/limit) — not whole files.
- Need more graph? `nav expand <node>` (callers/callees, depth-bounded, cursor-paged).
- Before editing any symbol: `explain <symbol>` — fan-in/out, blast radius, neighbors.
- Concept-finding: `search "<words>"` instead of grep.
- Where `.trailtracker-arch.json` exists: `arch-verify` before committing.
- Budget: >= 15,000 chars. Tighter budgets starve the read_plan (omissions are
  honest in the `budget` block) until the fill-order fix lands.
- MCP variant (server live in-session): call the `nav_pack` tool with the same
  task text + absolute `repo_path`, then follow the same read-plan discipline.
