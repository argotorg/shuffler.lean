#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Compare extracted Clight execution with the actual generated C."""
import argparse
from dataclasses import dataclass
import hashlib
import itertools
import json
from pathlib import Path
import random
import subprocess
import time

MAX = 2**32 - 1


@dataclass(frozen=True)
class Case:
    size: int
    data: tuple[int, ...] = ()
    permutation: tuple[int, ...] = ()
    fuel: int = 20000

    def __post_init__(self):
        count = self.size if 0 < self.size <= 1024 else 0
        if not (0 <= self.size <= MAX and 0 <= self.fuel <= 100000):
            raise ValueError("size or fuel outside adapter domain")
        if len(self.data) != count or len(self.permutation) != count:
            raise ValueError("array length does not match the call domain")
        if any(not 0 <= x <= MAX for x in (*self.data, *self.permutation)):
            raise ValueError("input word outside uint32 domain")

    def line(self):
        return " ".join(map(str, (self.size, self.fuel, *self.data, *self.permutation)))


def execute(binary, cases, timeout):
    start = time.monotonic()
    try:
        run = subprocess.run([str(binary)], input="\n".join(c.line() for c in cases) + "\n",
                             text=True, capture_output=True, timeout=timeout)
        stdout, stderr, status = run.stdout, run.stderr, run.returncode
    except subprocess.TimeoutExpired as error:
        stdout = error.stdout or b""
        stderr = error.stderr or b""
        stdout = stdout.decode() if isinstance(stdout, bytes) else stdout
        stderr = stderr.decode() if isinstance(stderr, bytes) else stderr
        status = "timeout"
    lines = stdout.splitlines()
    records = []
    errors = []
    if status:
        errors.append(f"process exit {status}")
    if len(lines) != len(cases):
        errors.append(f"expected {len(cases)} records, received {len(lines)}")
    for index, (line, case) in enumerate(zip(lines, cases)):
        try:
            words = tuple(map(int, line.split()))
            if len(words) < 4 or any(not 0 <= x <= MAX for x in words):
                raise ValueError("invalid output word")
            count = len(case.data)
            if words[1] > 2 * count or len(words) != 4 + 2 * count + words[1]:
                raise ValueError("invalid trace count or record length")
            records.append(words)
        except ValueError as error:
            errors.append(f"case {index}: {error}: {line}")
            records.append(None)
    return {"pass": not errors, "errors": errors, "records": records,
            "stdout": stdout, "stderr": stderr,
            "seconds": time.monotonic() - start, "exit": status}


def compare(reference, candidate):
    mismatches = [i for i, (a, b) in enumerate(zip(reference["records"],
                   candidate["records"])) if a != b]
    errors = list(candidate["errors"])
    if len(reference["records"]) != len(candidate["records"]):
        errors.append("reference and candidate record counts differ")
    return {"pass": reference["pass"] and candidate["pass"] and not errors and not mismatches,
            "mismatches": mismatches, "errors": errors}


def controls():
    cases = [Case(0), Case(1025), Case(MAX), Case(1, (MAX,), (0,)),
             Case(2, (10, 20), (1, 0)), Case(2, (MAX, MAX), (1, 0)),
             Case(2, (10, 20), (0, 0)), Case(2, (10, 20), (0, MAX)),
             Case(3, (10, 20, 30), (1, 2, 0))]
    for n in (17, 18):
        perm = list(range(n))
        perm[0], perm[-1] = perm[-1], perm[0]
        cases.append(Case(n, tuple(range(n)), tuple(perm)))
    perm = (1, 0, *range(2, 18))
    cases.append(Case(18, tuple(range(18)), perm))
    cases.append(Case(1024, (0,) * 1024, tuple(range(1024))))
    # Equal values at positions 16 and 17 suppress a physical swap before
    # the later attempt to move position 0 is blocked.
    data = (*range(16), 17, 17)
    cases.append(Case(18, data, (16, *range(1, 16), 0, 17)))
    return cases


def corpus(profile, seed):
    if profile == "controls":
        return controls()
    rng = random.Random(seed)
    cases = [Case(0), Case(1025), Case(MAX)]
    if profile == "small":
        for n in range(1, 5):
            for perm in itertools.permutations(range(n)):
                for data in itertools.product((0, MAX), repeat=n):
                    cases.append(Case(n, data, perm))
        for n in range(1, 9):
            for _ in range(30):
                perm = list(range(n))
                rng.shuffle(perm)
                values = (0, 1, 2**31 - 1, 2**31, MAX, rng.getrandbits(32))
                data = tuple(rng.choice(values) for _ in range(n))
                cases.append(Case(n, data, tuple(perm)))
                bad = list(perm)
                bad[rng.randrange(n)] = rng.choice((n, MAX))
                cases.append(Case(n, data, tuple(bad)))
    else:
        for n in (16, 17, 18, 19, 32, 33, 64, 65, 255, 256, 257, 512, 1023, 1024):
            identity = tuple(range(n))
            end_swap = (n - 1, *range(1, n - 1), 0)
            near_swap = (1, 0, *range(2, n))
            for perm in (identity, end_swap, near_swap, tuple(reversed(identity))):
                for data in (identity, (MAX,) * n, tuple(i % 3 for i in identity)):
                    cases.append(Case(n, data, perm))
            cases.append(Case(n, identity, (*range(n - 1), MAX)))
    return cases


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def campaign(build, output, profile, seed, timeout):
    output.mkdir(parents=True, exist_ok=False)
    manifest = json.loads((build / "build.json").read_text())
    for path, expected in manifest["sources"].items():
        if digest(Path(path)) != expected:
            raise ValueError(f"source changed since build: {path}")
    binaries = [build / "rocq-eval", *sorted(build.glob("native-*-O?"))]
    if len(binaries) != 7:
        raise ValueError("expected interpreter and six compiler builds")
    for binary in binaries:
        if digest(binary) != manifest["artifacts"][binary.name]:
            raise ValueError(f"binary changed since build: {binary}")
    cases = corpus(profile, seed)
    (output / "inputs.txt").write_text("\n".join(c.line() for c in cases) + "\n")
    results = []
    reference = None
    for binary in binaries:
        result = execute(binary, cases, timeout)
        (output / (binary.name + ".stdout")).write_text(result.pop("stdout"))
        (output / (binary.name + ".stderr")).write_text(result.pop("stderr"))
        if reference is None:
            reference = result
            verdict = {"pass": result["pass"], "errors": result["errors"]}
        else:
            verdict = compare(reference, result)
        record = {"binary": str(binary), "sha256": digest(binary),
                  "seconds": result["seconds"], **verdict}
        results.append(record)
        print(json.dumps(record), flush=True)
    summary = {"pass": all(r["pass"] for r in results), "cases": len(cases),
               "profile": profile, "seed": seed, "results": results,
               "inputs_sha256": digest(output / "inputs.txt"),
               "build_manifest_sha256": digest(build / "build.json")}
    (output / "results.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary["pass"]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--profile", choices=("small", "boundary", "controls"), default="small")
    parser.add_argument("--seed", type=int, default=20261007)
    parser.add_argument("--timeout", type=int, default=3600)
    args = parser.parse_args()
    raise SystemExit(0 if campaign(args.build.resolve(), args.output.resolve(),
                     args.profile, args.seed, args.timeout) else 1)
