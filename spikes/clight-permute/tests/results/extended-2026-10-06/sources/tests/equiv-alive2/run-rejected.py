#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check the C API's empty, oversized, and malformed-permutation calls."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

from completion import check_completions

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def selected_sizes(text):
    sizes = tuple(int(item) for item in text.split(","))
    if not sizes or len(set(sizes)) != len(sizes) or any(n < 0 or n > 1024 for n in sizes):
        raise argparse.ArgumentTypeError("sizes must be distinct integers from 0 through 1024")
    return sizes


def hashes(paths):
    return {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}


def run(command, log):
    print("+ " + repr(list(map(str, command))), flush=True)
    with log.open("w") as stream:
        return subprocess.run(list(map(str, command)), stdout=stream,
                              stderr=subprocess.STDOUT).returncode


def build(command, log):
    if run(command, log):
        raise RuntimeError(f"build or tool query failed: {log}")


def path_count(log, field):
    matches = re.findall(r"^KLEE: done: " + field + r" = (\d+)\s*$", log, re.MULTILINE)
    return int(matches[0]) if len(matches) == 1 else None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sizes", type=selected_sizes, default=selected_sizes("0,1,2,3,4,5"),
                        help="0 checks every empty/oversized call; other sizes check malformed permutations")
    parser.add_argument("--core", type=Path, default=ROOT / "permute.c")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--max-time", default="120s")
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    core = args.core.resolve(strict=True)
    sources = [core, ROOT / "permute.h", HERE / "rejected-driver.c",
               HERE / "completion.c", HERE / "completion.py", Path(__file__),
               HERE / "klee-shell.nix", ROOT.parents[1] / "flake.lock"]
    before = hashes(sources)
    manifest = {"source_sha256": before, "sizes": args.sizes, "cases": []}
    report = out / "manifest.json"
    report.write_text(json.dumps(manifest, indent=2) + "\n")
    for tool in ("clang", "klee", "z3"):
        build([tool, "--version"], out / (tool + "-version.txt"))
    flags = ["-std=c11", "-O0", "-g", "-Xclang", "-disable-O0-optnone",
             "-fno-vectorize", "-fno-slp-vectorize", "-U_FORTIFY_SOURCE",
             "-fsanitize=signed-integer-overflow,shift,integer-divide-by-zero,bounds",
             "-fno-sanitize-recover=all", "-emit-llvm", "-c", "-I", ROOT]
    build(["clang", *flags, core, "-o", out / "core.bc"], out / "core-build.log")
    build(["clang", *flags, HERE / "completion.c", "-o", out / "completion.bc"],
          out / "completion-build.log")
    for n in args.sizes:
        case = out / f"n{n}"
        case.mkdir()
        build(["clang", *flags, f"-DREJECT_N={n}", "-Dmain=checked_main",
               HERE / "rejected-driver.c", "-o", case / "driver.bc"], case / "build.log")
        build(["llvm-link", out / "core.bc", case / "driver.bc", out / "completion.bc",
               "-o", case / "linked.bc"], case / "link.log")
        code = run(["klee", "--solver-backend=z3", "--libc=none", "--ubsan-runtime",
                    "--external-calls=none", "--check-div-zero=true", "--check-overshift=true",
                    "--emit-all-errors", f"--max-time={args.max_time}",
                    f"--output-dir={case / 'proof'}", case / "linked.bc"], case / "proof.log")
        log = (case / "proof.log").read_text()
        complete = path_count(log, "completed paths")
        partial = path_count(log, "partially completed paths")
        errors = sorted(path.name for path in (case / "proof").glob("*.err"))
        completion = check_completions(case / "proof", complete or 0,
                                       "size_inputs" if n == 0 else "reject_inputs",
                                       16 if n == 0 else 4 * (2 * n + 3))
        after = hashes(sources)
        changed = [name for name in before if before[name] != after[name]]
        passed = (code == 0 and partial == 0 and not errors and not changed
                  and "KLEE: ERROR:" not in log and "calling external:" not in log
                  and completion["pass"])
        row = {"n": n, "pass": passed, "exit_code": code,
               "complete_paths": complete, "partial_paths": partial,
               "errors": errors, "completion": completion, "changed_sources": changed,
               "linked_sha256": hashes([case / "linked.bc"])[str(case / "linked.bc")]}
        manifest["cases"].append(row)
        report.write_text(json.dumps(manifest, indent=2) + "\n")
        print(json.dumps(row), flush=True)
    return 0 if all(case["pass"] for case in manifest["cases"]) else 1


if __name__ == "__main__":
    raise SystemExit(main())
