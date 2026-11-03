#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Bind a coverage executable to its project sources and oracle bodies."""
import argparse
import hashlib
import json
from pathlib import Path


def hashes(paths):
    return {str(path.resolve()): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in paths}


def capture(inputs, binary):
    return {"sources": hashes(inputs), "binary": hashes([binary])}


def check(record, inputs, binary):
    if record != capture(inputs, binary):
        raise ValueError("coverage source/binary manifest differs; rebuild before reporting")


def finish(before, inputs, binary):
    record = capture(inputs, binary)
    if before != record["sources"]:
        raise ValueError("coverage inputs changed during the build")
    return record


def inputs(root, build):
    # All project-controlled inputs to this build. Nix supplies the compiler
    # and system headers from the pinned shell; this is not a compiler proof.
    project = ("permute.c", "permute.h", "shell.nix", "tests/test.h",
               "tests/check_case.c", "tests/guided.c", "tests/oracle.cpp",
               "tests/build-guided.sh", "tests/prepare_oracle.py",
               "tests/coverage-manifest.py")
    oracle = ("solc_types.inc", "solc_mapping.inc", "solc_permute.inc",
              "solc_emission_helpers.inc", "solc_stack_helpers.inc")
    return ([root / name for name in project] + [root.parents[1] / "flake.lock"] +
            [build / "oracle" / name for name in oracle])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("clear", "begin", "finish", "check"))
    parser.add_argument("build", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    build = args.build.resolve()
    pending = build / "coverage-inputs.json"
    manifest = build / "coverage-manifest.json"
    if args.action == "clear":
        manifest.unlink(missing_ok=True)
        pending.unlink(missing_ok=True)
        return
    sources = inputs(root, build)
    binary = build / "coverage/permute-fuzz"
    if args.action == "begin":
        manifest.unlink(missing_ok=True)
        pending.write_text(json.dumps(hashes(sources), indent=2) + "\n")
    elif args.action == "finish":
        record = finish(json.loads(pending.read_text()), sources, binary)
        manifest.write_text(json.dumps(record, indent=2) + "\n")
        pending.unlink()
    else:
        check(json.loads(manifest.read_text()), sources, binary)
        print("Coverage source and binary hashes match the completed build")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError) as error:
        raise SystemExit(str(error))
