#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check that an inhibited fork cannot turn a faulty C copy into a proof."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    original = (ROOT / "permute.c").read_text()
    anchor = "  v7[2U] = 0U;"
    if original.count(anchor) != 1:
        raise ValueError("mutation anchor differs")
    mutant = output / "permute.c"
    mutant.write_text(original.replace(anchor, anchor + "\n  if (v2[0] == 42U) return 2U;"))

    # Only the KLEE options change. The actual compiler, checker, and C
    # sources are used. Seed 1 retains the nonfailing branch of the mutant.
    real = str(Path(shutil.which("klee")).resolve())
    wrapper = output / "bin"
    wrapper.mkdir()
    script = wrapper / "klee"
    script.write_text("#!" + sys.executable + "\nimport os, sys\n"
        "extra = [] if sys.argv[1:] == ['--version'] else "
        "['--max-forks=0', '--rng-initial-seed=1']\n"
        "os.execv(" + repr(real) + ", [" + repr(real) + "] + extra + sys.argv[1:])\n")
    script.chmod(0o755)
    controls = (("baseline", False, False), ("faulty_unlimited", True, False),
                ("faulty_limited", True, True), ("baseline_limited", False, True))
    results = []
    for name, faulty, limited in controls:
        environment = dict(os.environ)
        if limited:
            environment["PATH"] = str(wrapper) + os.pathsep + environment["PATH"]
        size = 2 if name == "baseline_limited" else 1
        command = [sys.executable, str(HERE / "run-klee.py"), "--sizes", str(size),
                   "--permutation", "1,0" if size == 2 else "0", "--max-time", "30s",
                   "--output", str(output / name)]
        if faulty:
            command += ["--core", str(mutant)]
        with (output / (name + ".log")).open("w") as log:
            process = subprocess.run(command, env=environment, stdout=log, stderr=subprocess.STDOUT)
        manifest = json.loads((output / name / "manifest.json").read_text())
        if len(manifest["cases"]) != 1:
            raise ValueError(f"control did not produce exactly one result: {name}")
        case = manifest["cases"][0]
        if limited:
            exploration = case.get("exploration", {})
            matched = (process.returncode != 0 and not case["pass"]
                       and not case["errors"] and case["completion"]["pass"]
                       and exploration.get("counters", {}).get("InhibitedForks", 0) > 0
                       and exploration.get("pass") is False)
        elif faulty:
            matched = (process.returncode != 0 and not case["pass"]
                       and any(error.endswith(".assert.err") for error in case["errors"]))
        else:
            matched = process.returncode == 0 and case["pass"]
        row = {"name": name, "expected_result": matched, "case": case,
               "driver_exit": process.returncode}
        results.append(row)
        (output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps(row), flush=True)
    return 0 if all(row["expected_result"] for row in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
