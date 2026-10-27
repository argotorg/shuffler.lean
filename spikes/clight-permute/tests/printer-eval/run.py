#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Compare generated Clight programs with their printed C."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import shlex
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "rocq-eval"))
from compare import Case, compare, execute


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inputs(seed, count):
    rng = random.Random(seed)
    limits = (0, 1, 7, 8, 16, 2**31 - 1, 2**31, 2**32 - 2, 2**32 - 1)
    cases = [Case(8, (x,) * 8, (y,) * 8, fuel=5000)
             for x in limits for y in (0, 2**32 - 1)]
    for _ in range(count):
        cases.append(Case(8, tuple(rng.getrandbits(32) for _ in range(8)),
                         tuple(rng.getrandbits(32) for _ in range(8)), fuel=5000))
    return cases


def compiler_environment():
    return {key: (" ".join(flag for flag in value.split()
                    if flag not in ("fortify", "fortify3"))
                    if key.startswith("NIX_HARDENING_ENABLE") else value)
            for key, value in os.environ.items()}


def reference(build, seed, directory, cases):
    # A shell adapter supplies the seed to the same extracted executable.
    wrapper = directory / "reference"
    wrapper.write_text("#!/bin/sh\nexec " + shlex.quote(str(build / "printer-eval")) +
                       " run " + str(seed) + "\n")
    wrapper.chmod(0o755)
    return execute(wrapper, cases, 60)


def compile_program(build, source, directory, compiler, level):
    binary = directory / f"native-{compiler}-O{level}"
    command = [compiler, "-std=c11", "-Wall", "-Wextra", "-Werror",
               "-Wno-unused-parameter", "-Wno-unused-but-set-variable",
               "-U_FORTIFY_SOURCE", f"-O{level}", "-I", str(build),
               str(build / "native.c"), str(source), "-o", str(binary)]
    with binary.with_suffix(".compile.log").open("w") as log:
        subprocess.run(command, env=compiler_environment(), stdout=log,
                       stderr=subprocess.STDOUT, check=True, timeout=60)
    return binary


def save_result(directory, name, result):
    (directory / (name + ".stdout")).write_text(result["stdout"])
    (directory / (name + ".stderr")).write_text(result["stderr"])


def campaign(build, output, first, programs, random_cases):
    output.mkdir(parents=True, exist_ok=False)
    manifest = json.loads((build / "build.json").read_text())
    for path, expected in manifest["sources"].items():
        if digest(Path(path)) != expected:
            raise ValueError(f"source changed since build: {path}")
    for name, expected in manifest["artifacts"].items():
        if digest(build / name) != expected:
            raise ValueError(f"build artifact changed: {name}")
    cases = inputs(20261007, random_cases)
    (output / "inputs.txt").write_text("\n".join(c.line() for c in cases) + "\n")
    (output / "hardening.json").write_text(json.dumps({k: v for k, v in
        compiler_environment().items() if "HARDENING" in k}, indent=2) + "\n")
    results = []
    for seed in range(first, first + programs):
        directory = output / f"seed-{seed}"
        directory.mkdir()
        source = directory / "program.c"
        source.write_bytes(subprocess.check_output(
            [str(build / "printer-eval"), "print", str(seed)], timeout=60))
        oracle = reference(build, seed, directory, cases)
        save_result(directory, "reference", oracle)
        comparisons = []
        for compiler in ("gcc", "clang"):
            for level in (0, 2, 3):
                binary = compile_program(build, source, directory, compiler, level)
                candidate = execute(binary, cases, 60)
                save_result(directory, binary.name, candidate)
                comparisons.append({"binary": binary.name, "sha256": digest(binary),
                                    **compare(oracle, candidate)})
        record = {"seed": seed, "source_sha256": digest(source),
                  "pass": oracle["pass"] and all(c["pass"] for c in comparisons),
                  "interpreter_errors": oracle["errors"], "comparisons": comparisons}
        results.append(record)
        (output / "progress.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps({"seed": seed, "pass": record["pass"]}), flush=True)
    summary = {"pass": all(r["pass"] for r in results), "programs": len(results),
        "cases_per_program": len(cases), "results": results,
        "inputs_sha256": digest(output / "inputs.txt"),
        "build_manifest_sha256": digest(build / "build.json")}
    (output / "results.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary["pass"]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--first", type=int, default=0)
    parser.add_argument("--programs", type=int, default=128)
    parser.add_argument("--random-cases", type=int, default=32)
    args = parser.parse_args()
    if args.first < 0 or args.programs < 1 or args.first + args.programs > 1000001:
        parser.error("program seeds must be in 0..1000000 and count must be positive")
    if args.random_cases < 0:
        parser.error("random case count must be nonnegative")
    raise SystemExit(0 if campaign(args.build.resolve(), args.output.resolve(),
        args.first, args.programs, args.random_cases) else 1)
