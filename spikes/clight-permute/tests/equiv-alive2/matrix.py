# SPDX-License-Identifier: GPL-3.0-or-later
"""Check the shared source-mutation matrix with explicit symbolic domains."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def domain(name):
    if name == "c-size-bound":
        return list(range(1024)), [0] * 1024
    if name in {"c-depth-bound", "c-blocked-position", "c-excess-depth",
                "cpp-excess-depth", "c-commute-control", "cpp-compare-control"}:
        return [1, 0] + list(range(2, 18)), [0, 1] + [2] * 16
    if name == "cpp-destination-pairing":
        return [2, 3, 0, 1], None
    return [1, 0, 2], None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=ROOT / "build/challenge/manifest.json")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    cases = json.loads(args.manifest.read_text())
    results = []
    for case in cases:
        source = Path(case["source"])
        if hashlib.sha256(source.read_bytes()).hexdigest() != case["sha256"]:
            raise ValueError(f"source hash differs: {case['id']}")
        permutation, groups = domain(case["id"])
        destination = output / case["id"]
        command = [sys.executable, str(HERE / "run-klee.py"),
                   "--sizes", str(len(permutation)), "--permutation",
                   ",".join(map(str, permutation)), "--output", str(destination),
                   "--max-time", "600s",
                   "--core" if case["language"] == "c" else "--solc-permute", str(source)]
        if groups is not None:
            command += ["--value-groups", ",".join(map(str, groups))]
        with (output / (case["id"] + ".log")).open("w") as log:
            process = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
        errors = sorted(destination.glob("n*/proof/*.err"))
        proof_manifest = json.loads((destination / "manifest.json").read_text())
        equivalent = case["kind"] == "control"
        if equivalent:
            validated = (process.returncode == 0 and not errors
                         and len(proof_manifest["cases"]) == 1
                         and proof_manifest["cases"][0]["pass"])
        else:
            # All shared mutants change a public result. A parser, external
            # call, timeout, or other tool failure is not a result witness.
            validated = (process.returncode != 0 and bool(errors)
                         and all(path.name.endswith(".assert.err") for path in errors))
        result = {"name": case["id"], "source_sha256": case["sha256"],
                  "n": len(permutation), "value_groups": groups,
                  "equivalent": equivalent, "validated": validated,
                  "errors": [str(path.relative_to(destination)) for path in errors]}
        results.append(result)
        (output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps(result), flush=True)
        if not validated:
            raise SystemExit(f"matrix control did not validate: {case['id']}")
    print(f"KLEE matrix controls passed: {len(results)}", flush=True)


if __name__ == "__main__":
    main()
