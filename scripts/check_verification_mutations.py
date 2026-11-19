#!/usr/bin/env python3
"""Check selected verification defects in an isolated copy, after a green control."""

import argparse
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import tempfile


def run(command, root, log):
    with log.open("w", encoding="utf-8") as output:
        process = subprocess.Popen(
            command, cwd=root, stdout=output, stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        try:
            code = process.wait(timeout=600)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            raise SystemExit(f"TIMED OUT (not killed): see {log}")
    return code, log.read_text(encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("suite", choices=["parser", "kani"])
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    logs = root / "target" / "verification-mutations" / args.suite
    logs.mkdir(parents=True, exist_ok=True)

    if args.suite == "parser":
        command = ["cargo", "test", "-p", "trailtracker-eval", "--test", "losslessness"]
        path = Path("src/core/cst.rs")
        mutants = [(
            "drop-source-token",
            "Child::Token(t) => out.push_str(t.span.text(source)),",
            "Child::Token(_) => {},",
            "input bytes:",
        )]
    else:
        command = [
            "cargo", "kani", "-p", "trailtracker-eval", "--harness",
            "k3c_loop_fold_schema", "--output-format", "terse",
            "-Z", "unstable-options", "--harness-timeout", "300",
        ]
        path = Path("eval/src/kani_proofs.rs")
        mutants = [
            (
                "wrong-map-value",
                "map(|&x| x.wrapping_mul(2))",
                "map(|&x| x.wrapping_mul(3))",
                "push == map+collect element",
            ),
            (
                "reversed-filter",
                "filter_map(|&x| if x > t",
                "filter_map(|&x| if x < t",
                "guarded push == filter_map+collect",
            ),
        ]

    with tempfile.TemporaryDirectory(prefix="trailtracker-mutations-") as directory:
        isolated = Path(directory)
        for name in ["Cargo.toml", "Cargo.lock"]:
            shutil.copy2(root / name, isolated / name)
        for name in ["src", "eval"]:
            shutil.copytree(root / name, isolated / name)
        control_log = logs / "control.log"
        code, output = run(command, isolated, control_log)
        success = "VERIFICATION:- SUCCESSFUL" if args.suite == "kani" else "test result: ok. 1 passed"
        if code != 0 or success not in output:
            raise SystemExit(f"INVALID control: see {control_log}")
        print(f"PASS: {args.suite} unmodified control", flush=True)

        source = isolated / path
        original = source.read_text(encoding="utf-8")
        for name, before, after, expected in mutants:
            if original.count(before) != 1:
                raise SystemExit(f"INVALID mutation {name}: expected exactly one source match")
            source.write_text(original.replace(before, after), encoding="utf-8")
            log = logs / f"{name}.log"
            try:
                code, output = run(command, isolated, log)
            finally:
                source.write_text(original, encoding="utf-8")
            if code == 0:
                raise SystemExit(f"SURVIVED: {name}; see {log}")
            # Kani quotes assertion descriptions in its Failed Checks summary.
            # Match only that summary, not source excerpts in compiler output.
            failures = "\n".join(re.findall(r"^Failed Checks: (.+)$", output, re.MULTILINE))
            evidence = failures if args.suite == "kani" else output
            if expected not in evidence or (args.suite == "kani" and (
                "VERIFICATION:- FAILED" not in output
                or "undetermined" in output.lower()
                or "timed out" in output.lower()
            )):
                raise SystemExit(f"INVALID failure (not killed): {name}; see {log}")
            print(f"KILLED: {name} by its behavioral assertion; log: {log}", flush=True)


if __name__ == "__main__":
    main()
