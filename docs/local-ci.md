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

## Bounded verification

`cargo test --workspace` includes exhaustive parser round trips over the exact
domain originally used by the symbolic harness: 17 ASCII characters, every
length from zero through five, 1,508,598 inputs. The alphabet and maximum length
are shared in `eval/src/losslessness.rs`. To see the count:

```sh
cargo test -p trailtracker-eval --test losslessness -- --nocapture
python3 scripts/check_verification_mutations.py parser
```

This checks the real parser, reconstruction, and normal panic/overflow checks on
every input. It does not claim Kani's additional symbolic memory-safety checks.
The symbolic parser proof did not finish in the original CI run; it remains
available for research without reducing its bounds:

```sh
cargo kani -p trailtracker-eval --features symbolic-parser-proof \
  --harness losslessness_is_total --output-format terse \
  -Z unstable-options --harness-timeout 300
```

The four rewrite schemas use Kani's default safety and unwinding checks. Their
formal CI job is blocking, pins Kani (including its bundled compiler/backend),
and fails on a five-minute per-harness timeout:

```sh
cargo install --locked kani-verifier --version 0.68.0
cargo kani setup
bash scripts/verify_kani.sh
```

The loop-fold proof compares vector lengths and elements explicitly: bytewise
`Vec<i32>` equality can require twelve `memcmp` iterations for three elements,
which exceeded the original unwind bound of six. Its input domain is unchanged.

Both mutation commands copy the packages into a temporary directory and first
require a passing unmodified control. The parser check drops source tokens; the
Kani check changes a mapped value and reverses a filter predicate. A surviving,
invalid, or timed-out mutant fails the command. Logs are retained under
`target/verification-mutations/`. These selected checks are not an exhaustive
mutation score. `scripts/verify.sh` runs the parser check and, when Kani is
installed, the formal checks. CI runs both on every PR update.
