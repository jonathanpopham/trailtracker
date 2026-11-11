#!/usr/bin/env python3
"""Package a native release binary and smoke-test the extracted download."""

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile
import tempfile
import zipfile


def main():
    tag = os.environ["RELEASE_TAG"]
    target = os.environ["TARGET"]
    if not re.fullmatch(r"v\d+\.\d+\.\d+(?:-[A-Za-z0-9.-]+)?", tag):
        raise SystemExit("RELEASE_TAG must be a version tag")
    if target not in {
        "x86_64-unknown-linux-gnu", "aarch64-apple-darwin",
        "x86_64-apple-darwin", "x86_64-pc-windows-msvc",
    }:
        raise SystemExit("unsupported release target")

    windows = target.endswith("windows-msvc")
    binary = "trailtracker.exe" if windows else "trailtracker"
    source = Path("target") / target / "release" / binary
    files = [(source, binary), (Path("README.md"), "README.md")]
    for name in ("LICENSE", "COPYRIGHT"):
        if Path(name).is_file():
            files.append((Path(name), name))

    output = Path("dist")
    output.mkdir(exist_ok=True)
    archive = output / f"trailtracker-{tag}-{target}.{'zip' if windows else 'tar.gz'}"
    if windows:
        with zipfile.ZipFile(archive, "w", zipfile.ZIP_DEFLATED) as package:
            for path, name in files:
                package.write(path, name)
    else:
        with tarfile.open(archive, "w:gz") as package:
            for path, name in files:
                package.add(path, arcname=name)

    with tempfile.TemporaryDirectory(prefix="trailtracker-release-") as directory:
        if windows:
            with zipfile.ZipFile(archive) as package:
                package.extractall(directory)
        else:
            with tarfile.open(archive) as package:
                package.extractall(directory, filter="data")
        executable = str(Path(directory) / binary)
        subprocess.run([executable, "help"], check=True, capture_output=True)
        result = subprocess.run(
            [executable, "stats", "eval/corpus/calc", "--json"],
            check=True, capture_output=True, text=True,
        )
        json.loads(result.stdout)

    digest = hashlib.sha256(archive.read_bytes()).hexdigest()
    archive.with_name(archive.name + ".sha256").write_text(
        f"{digest}  {archive.name}\n", encoding="utf-8",
    )
    print(f"Packaged and smoke-tested {archive}")


if __name__ == "__main__":
    main()
