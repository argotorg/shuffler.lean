#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check the assignment analysis and mutations of its decisions."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


VARIANTS = (
    ("baseline", None, None, None),
    ("ignore-assignment-source", "if uses ids value then Some (continuing (id :: ids))",
     "if true then Some (continuing (id :: ids))", "rejects_undefined_self_copy"),
    ("union-branch-assignments", "filter (fun id => member id second) first",
     "first ++ second", "rejects_one_branch_assignment"),
    ("ignore-condition-read", "if uses ids condition then", "if true then",
     "rejects_undefined_condition"),
    ("ignore-address-read", "if uses ids address && uses ids value then",
     "if uses ids value then", "rejects_undefined_address"),
    ("ignore-store-read", "if uses ids address && uses ids value then",
     "if uses ids address then", "rejects_undefined_store"),
    ("ignore-return-read", "if uses ids value then Some returning", "if true then Some returning",
     "rejects_undefined_return"),
    ("ignore-loop-body", "match check ids body with\n      | Some paths => Some {| normal := broken paths; broken := None |}\n      | None => None\n      end",
     "Some returning", "rejects_undefined_read_in_loop"),
    ("duplicate-assignment-control", "continuing (id :: ids)", "continuing (id :: id :: ids)", None),
)


def check(base, output):
    output.mkdir(parents=True, exist_ok=False)
    prior = json.loads((base / "build.json").read_text())
    for path, expected in prior["sources"].items():
        if digest(Path(path)) != expected:
            raise ValueError(f"base source changed: {path}")
    for name, expected in prior["artifacts"].items():
        if name.endswith((".v", ".vo")) and digest(base / name) != expected:
            raise ValueError(f"base proof artifact changed: {name}")
    spec = importlib.util.spec_from_file_location("audit", ROOT / "audit-deps.py")
    audit = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(audit)
    audit.audit()
    source = (HERE / "AssignmentCheck.v").read_text()
    audit.imports(source, audit.PROJECT_MODULES | {Path(p).stem for p in audit.ALLOWED},
                  external=("Coq", "Stdlib", "Flocq", "mathcomp"))
    paths = ["-R", str(ROOT / "build/compcert"), "compcert", "-Q", str(base), ""]
    results = []
    for name, before, after, expected_failure in VARIANTS:
        directory = output / name
        directory.mkdir()
        text = source
        if before is not None:
            if text.count(before) != 1:
                raise ValueError(f"{name}: mutation must match once")
            text = text.replace(before, after, 1)
        path = directory / "AssignmentCheck.v"
        path.write_text(text)
        run = subprocess.run(["coqc", *paths, path.name], cwd=directory,
                             capture_output=True, text=True, timeout=120)
        log = run.stdout + run.stderr
        (directory / "compile.log").write_text(log)
        if expected_failure:
            statement = re.search(r"(?:Example|Theorem) " + re.escape(expected_failure) +
                                  r"\b[\s\S]*?Qed\.", text)
            if not statement:
                raise ValueError("missing expected fixture")
            first = text.count("\n", 0, statement.start()) + 1
            last = text.count("\n", 0, statement.end()) + 1
            error = re.search(r'File "[^"\n]*AssignmentCheck.v", line (\d+),', log)
            passed = (run.returncode != 0 and error is not None and
                      first <= int(error.group(1)) <= last and "Unable to unify" in log)
        else:
            passed = run.returncode == 0
        result = {"name": name, "expected_failure": expected_failure,
                  "expected_result_met": passed, "exit": run.returncode,
                  "source_sha256": digest(path)}
        results.append(result)
        print(json.dumps(result), flush=True)
    baseline = output / "baseline"
    with (baseline / "kernel.log").open("w") as log:
        subprocess.run(["coqchk", "-silent", "-o", *paths, "AssignmentCheck"],
                       cwd=baseline, stdout=log, stderr=subprocess.STDOUT, check=True)
    with (baseline / "kernel-policy.log").open("w") as log:
        subprocess.run(["python3", str(ROOT / "check-assumptions.py"), "--kernel",
                        str(baseline / "kernel.log")], stdout=log, stderr=subprocess.STDOUT,
                       check=True)
    summary = {"pass": all(r["expected_result_met"] for r in results),
        "results": results, "base_manifest_sha256": digest(base / "build.json"),
        "sources": {str(p): digest(p) for p in (HERE / "AssignmentCheck.v", HERE / "check.py")}}
    (output / "results.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary["pass"]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    raise SystemExit(0 if check(args.base.resolve(), args.output.resolve()) else 1)
