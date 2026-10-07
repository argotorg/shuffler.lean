#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check a fixed arithmetic example against an independently stated record."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess

from run import Case, compile_program, digest, execute, save_result

HERE = Path(__file__).resolve().parent


def check(build, output):
    output.mkdir(parents=True, exist_ok=False)
    manifest = json.loads((build / "build.json").read_text())
    for name, expected in manifest["artifacts"].items():
        if digest(build / name) != expected:
            raise ValueError(f"build artifact changed: {name}")
    shutil.copy2(HERE / "literal.ml", output / "literal.ml")
    subprocess.run(["ocamlopt", "-I", str(build), "-o", "literal",
        str(build / "extracted.cmx"), str(build / "printer.cmx"),
        str(build / "generator.cmx"), "literal.ml"], cwd=output, check=True)
    program = output / "program.c"
    program.write_bytes(subprocess.check_output([str(output / "literal"), "print"]))
    expected = (4294967295, 0, 4294967295, 4294967295,
                4294967295, 1, 2, 3, 4, 5, 6, 7, 1, 2, 1, 4, 5, 6, 7, 8)
    case = Case(8, (4294967295, 0, 2, 3, 4, 5, 6, 7), tuple(range(1, 9)), fuel=100)
    (output / "inputs.txt").write_text(case.line() + "\n")
    (output / "expected.json").write_text(json.dumps(expected) + "\n")
    result = subprocess.check_output([str(output / "literal"), "run"], text=True)
    (output / "reference.stdout").write_text(result)
    checks = [{"program": "extracted", "pass": tuple(map(int, result.split())) == expected}]
    for compiler in ("gcc", "clang"):
        for level in (0, 2, 3):
            binary = compile_program(build, program, output, compiler, level)
            result = execute(binary, [case], 10)
            save_result(output, binary.name, result)
            checks.append({"program": binary.name, "sha256": digest(binary),
                "pass": result["pass"] and result["records"] == [expected]})
    summary = {"pass": all(c["pass"] for c in checks), "checks": checks,
        "build_manifest_sha256": digest(build / "build.json"),
        "sources": {str(path): digest(path) for path in
                    (HERE / "literal.ml", HERE / "literal.py", HERE / "run.py")}}
    (output / "results.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary), flush=True)
    return summary["pass"]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    raise SystemExit(0 if check(args.build.resolve(), args.output.resolve()) else 1)
