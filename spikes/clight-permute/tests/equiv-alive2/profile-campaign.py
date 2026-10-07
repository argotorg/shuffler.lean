# SPDX-License-Identifier: GPL-3.0-or-later
"""Check named large-array families with unrestricted symbolic group values."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent


def exchanged(size, first, second):
    permutation = list(range(size))
    permutation[first], permutation[second] = permutation[second], permutation[first]
    return permutation


def cases():
    for size in [17, 18, 19]:
        yield f"n{size}-low-swap", exchanged(size, 0, 1), [0, 1] + [2] * (size - 2)
    for size in [18, 1024]:
        yield f"n{size}-end-swap", exchanged(size, 0, size - 1), [0] * (size - 1) + [1]
    for size in [255, 256, 257, 512, 1024]:
        yield f"n{size}-reverse-two-groups", list(reversed(range(size))), [i % 2 for i in range(size)]
    for size in [33, 257, 1024]:
        yield f"n{size}-rotate-three-groups", list(range(1, size)) + [0], [i % 3 for i in range(size)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    results = []
    for name, permutation, groups in cases():
        destination = output / name
        command = [sys.executable, str(HERE / "run-klee.py"),
                   "--sizes", str(len(permutation)), "--permutation", ",".join(map(str, permutation)),
                   "--value-groups", ",".join(map(str, groups)),
                   "--max-time", "600s", "--output", str(destination)]
        with (output / (name + ".log")).open("w") as log:
            process = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
        manifest = json.loads((destination / "manifest.json").read_text())
        result = {"name": name, "n": len(permutation), "permutation": permutation,
                  "value_groups": groups, "cases": manifest["cases"], "pass": process.returncode == 0}
        results.append(result)
        (output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps({"name": name, "pass": result["pass"],
                          "paths": [case["complete_paths"] for case in manifest["cases"]]}), flush=True)
        if not result["pass"]:
            raise SystemExit(f"symbolic profile did not pass: {name}")
    print(f"KLEE symbolic profiles passed: {len(results)}", flush=True)


if __name__ == "__main__":
    main()
