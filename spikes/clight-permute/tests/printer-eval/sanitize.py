#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Run generated printer programs with AddressSanitizer and UBSan."""
import argparse
import json
from pathlib import Path
import shlex
import subprocess

from run import (compare, compiler_environment, digest, execute, inputs,
                 reference, save_result)

HERE = Path(__file__).resolve().parent


def compile_checked(build, source, directory):
    binary = directory / "sanitized"
    command = ["clang", "-std=c11", "-O1", "-g", "-Wall", "-Wextra", "-Werror",
        "-Wno-unused-parameter", "-Wno-unused-but-set-variable", "-U_FORTIFY_SOURCE",
        "-fsanitize=address,undefined", "-fno-sanitize-recover=all",
        "-fno-omit-frame-pointer", "-I", str(build), str(build / "native.c"),
        str(source), "-o", str(binary)]
    (directory / "command.json").write_text(json.dumps(command, indent=2) + "\n")
    with (directory / "compile.log").open("w") as log:
        subprocess.run(command, env=compiler_environment(), stdout=log,
                       stderr=subprocess.STDOUT, check=True, timeout=60)
    return binary


def run_checked(binary, cases, timeout):
    # LeakSanitizer cannot inspect threads in this execution environment.
    # The tested functions use stack objects only. ASan and UBSan stay on.
    wrapper = binary.parent / "sanitized-run"
    wrapper.write_text("#!/bin/sh\nASAN_OPTIONS=detect_leaks=0\nexport ASAN_OPTIONS\nexec " +
                       shlex.quote(str(binary)) + "\n")
    wrapper.chmod(0o755)
    return execute(wrapper, cases, timeout)


def check(build, output, programs):
    output.mkdir(parents=True, exist_ok=False)
    manifest = json.loads((build / "build.json").read_text())
    for path, expected in manifest["sources"].items():
        if digest(Path(path)) != expected:
            raise ValueError(f"source changed since build: {path}")
    for name, expected in manifest["artifacts"].items():
        if digest(build / name) != expected:
            raise ValueError(f"build artifact changed: {name}")
    cases = inputs(20261007, 32)
    (output / "inputs.txt").write_text("\n".join(c.line() for c in cases) + "\n")
    (output / "clang-version.txt").write_bytes(subprocess.check_output(["clang", "--version"]))
    (output / "hardening.json").write_text(json.dumps({k: v for k, v in
        compiler_environment().items() if "HARDENING" in k}, indent=2) + "\n")
    results = []
    for seed in range(programs):
        directory = output / f"seed-{seed}"
        directory.mkdir()
        source = directory / "program.c"
        source.write_bytes(subprocess.check_output([str(build / "printer-eval"),
                                                   "print", str(seed)], timeout=60))
        oracle = reference(build, seed, directory, cases)
        save_result(directory, "reference", oracle)
        binary = compile_checked(build, source, directory)
        candidate = run_checked(binary, cases, 60)
        save_result(directory, "sanitized", candidate)
        verdict = compare(oracle, candidate)
        record = {"seed": seed, **verdict, "source_sha256": digest(source),
            "binary_sha256": digest(binary), "stderr_empty": not candidate["stderr"]}
        record["pass"] = record["pass"] and record["stderr_empty"]
        results.append(record)
        (output / "progress.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps({"seed": seed, "pass": record["pass"]}), flush=True)

    # The same compiler and execution gate must detect a memory error and UB.
    controls = []
    baseline = (output / "seed-0/program.c").read_text()
    marker = "  unsigned int v13;"
    if baseline.count(marker) != 1:
        raise ValueError("control insertion point changed")
    variants = (
        ("bounds", "v2[8] = v2[0];", "AddressSanitizer", "stack-buffer-overflow"),
        ("shift", "volatile unsigned int bad_shift = 32U; v2[0] <<= bad_shift;",
         "runtime error", "shift exponent 32"),
    )
    for name, statement, diagnostic, detail in variants:
        directory = output / ("control-" + name)
        directory.mkdir()
        source = directory / "program.c"
        source.write_text(baseline.replace(marker, marker + "\n  " + statement, 1))
        binary = compile_checked(build, source, directory)
        result = run_checked(binary, cases[:1], 30)
        save_result(directory, "sanitized", result)
        passed = (isinstance(result["exit"], int) and result["exit"] != 0 and
                  diagnostic in result["stderr"] and detail in result["stderr"])
        controls.append({"name": name, "expected_result_met": passed,
            "exit": result["exit"], "source_sha256": digest(source),
            "binary_sha256": digest(binary)})
    summary = {"pass": all(r["pass"] for r in results) and
                        all(c["expected_result_met"] for c in controls),
        "programs": len(results), "cases_per_program": len(cases),
        "asan_options": "detect_leaks=0",
        "results": results, "controls": controls,
        "build_manifest_sha256": digest(build / "build.json"),
        "inputs_sha256": digest(output / "inputs.txt"),
        "sources": {str(p): digest(p) for p in (HERE / "sanitize.py", HERE / "run.py",
                    HERE.parent / "rocq-eval/compare.py")}}
    (output / "results.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary["pass"]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--programs", type=int, default=128)
    args = parser.parse_args()
    if not 1 <= args.programs <= 1000001:
        parser.error("program count must be in 1..1000001")
    raise SystemExit(0 if check(args.build.resolve(), args.output.resolve(), args.programs) else 1)
