# Running CI locally (act)

GitHub Actions can be run on this machine (Linux containers via Docker):

    act -j gate -P ubuntu-latest=catthehacker/ubuntu:act-latest --container-architecture linux/arm64

- `ci.yml` self-installs rustup when absent and skips artifact upload under act
  (both no-ops on real GitHub runners).
- First run pulls the runner image + cold-builds; subsequent runs are cached (~1 min).
- Known local skip: the kani job (needs the kani toolchain in-container — tracked
  with D3/K6). Release cross-builds genuinely require GitHub runners.
- verify.sh + `ontology_bench.py --check` + `mcp/test_mcp.py` remain the primary
  merge gate; act adds Linux coverage on demand.
