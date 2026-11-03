#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Challenge the soundness proof with checker mutations, without example tests."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess

import check

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def failure_at(text, log, theorem, module="AssignmentSound"):
    statement = re.search(r"(?:Lemma|Theorem|Corollary) " + re.escape(theorem) +
                          r"\b[\s\S]*?Qed\.", text)
    error = re.search(r'File "[^"\n]*' + re.escape(module) + r'\.v", line (\d+),', log)
    if not statement or not error:
        return False
    first = text.count("\n", 0, statement.start()) + 1
    last = text.count("\n", 0, statement.end()) + 1
    return (first <= int(error.group(1)) <= last and
            "Error:" in log and "Syntax error" not in log and
            "Cannot find a physical path" not in log)


def run(base, output):
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
    checker = (HERE / "AssignmentCheck.v").read_text()
    # These are isolated copies. Production examples and their evidence stay intact.
    checker, removed = re.subn(r"Example \w+\b[\s\S]*?Qed\.", "", checker)
    if removed != 21:
        raise ValueError(f"expected 21 examples, removed {removed}")
    proof = (HERE / "AssignmentSound.v").read_text()
    execution = (HERE / "AssignmentExec.v").read_text()
    local = audit.PROJECT_MODULES | {Path(p).stem for p in audit.ALLOWED} | {
        "AssignmentCheck", "AssignmentSound", "AssignmentExec"}
    for text in (checker, proof, execution):
        audit.imports(text, local, external=("Coq", "Stdlib", "Flocq", "mathcomp"))
    paths = ["-R", str(ROOT / "build/compcert"), "compcert", "-Q", str(base), ""]
    variants = [(name, before, after,
                 "join_left" if name == "union-branch-assignments" else
                 "complete_path_safe" if expected else None)
                for name, before, after, expected in check.VARIANTS
                if name != "duplicate-assignment-control"]
    variants.append(("parentheses-control", "if uses ids condition then",
                     "if (uses ids condition) then", None))
    results = []
    for name, before, after, expected in variants:
        directory = output / name
        directory.mkdir()
        text = checker
        if before is not None:
            if text.count(before) != 1:
                raise ValueError(f"{name}: mutation must match once")
            text = text.replace(before, after, 1)
        (directory / "AssignmentCheck.v").write_text(text)
        (directory / "AssignmentSound.v").write_text(proof)
        compiled = subprocess.run(["coqc", *paths, "AssignmentCheck.v"], cwd=directory,
                                  capture_output=True, text=True, timeout=120)
        (directory / "checker.log").write_text(compiled.stdout + compiled.stderr)
        if compiled.returncode:
            raise ValueError(f"{name}: checker did not compile before proof challenge")
        result = subprocess.run(["coqc", *paths, "AssignmentSound.v"], cwd=directory,
                                capture_output=True, text=True, timeout=120)
        log = result.stdout + result.stderr
        (directory / "proof.log").write_text(log)
        met = (result.returncode != 0 and failure_at(proof, log, expected)) if expected else (
            result.returncode == 0)
        record = {"name": name, "checker_compiles": True, "examples_removed": removed,
                  "expected_proof_failure": expected, "proof_exit": result.returncode,
                  "expected_result_met": met,
                  "checker_sha256": digest(directory / "AssignmentCheck.v"),
                  "proof_sha256": digest(directory / "AssignmentSound.v")}
        print(json.dumps(record), flush=True)
        results.append(record)
    execution_variants = (
        ("execution-baseline", None, None, None),
        ("execution-parentheses", "(uses ids value)", "((uses ids value))", None),
        ("execution-hide-unsafe-set",
         "eval_expr ge e le m value v ->\n    recorded_exec e le m (Sset id value)",
         "eval_expr ge e le m value v -> uses ids value = true ->\n    recorded_exec e le m (Sset id value)",
         "execution_recorded"),
        ("execution-reverse-branch", "(if choice then yes else no)",
         "(if choice then no else yes)", "recorded_erases"),
        ("execution-ignore-condition", "initial final (uses initial condition && safe)",
         "initial final safe", "recorded_path"),
        ("execution-loop-reset",
         "(Sloop body Sskip) t2 le2 m2 out middle final b",
         "(Sloop body Sskip) t2 le2 m2 out initial final b", "recorded_path"),
        ("execution-set-before-read", "ids (id :: ids) (uses ids value)",
         "ids (id :: ids) (uses (id :: ids) value)", "recorded_path"),
    )
    for name, before, after, expected in execution_variants:
        directory = output / name
        directory.mkdir()
        for module in ("AssignmentCheck", "AssignmentSound"):
            for suffix in (".v", ".vo"):
                shutil.copy2(output / "baseline" / (module + suffix), directory)
        text = execution
        if before is not None:
            # The parentheses control changes only the set-source check.
            if name == "execution-parentheses":
                before = "ids (id :: ids) " + before
                after = "ids (id :: ids) " + after
            if text.count(before) != 1:
                raise ValueError(f"{name}: mutation must match once")
            text = text.replace(before, after, 1)
        (directory / "AssignmentExec.v").write_text(text)
        result = subprocess.run(["coqc", *paths, "AssignmentExec.v"], cwd=directory,
                                capture_output=True, text=True, timeout=120)
        log = result.stdout + result.stderr
        (directory / "proof.log").write_text(log)
        met = (result.returncode != 0 and failure_at(text, log, expected, "AssignmentExec")) if expected else (
            result.returncode == 0)
        record = {"name": name, "kind": "execution-model-control",
                  "expected_proof_failure": expected, "proof_exit": result.returncode,
                  "expected_result_met": met, "proof_sha256": digest(directory / "AssignmentExec.v")}
        print(json.dumps(record), flush=True)
        results.append(record)
    # Actual compiler failures must not count as a soundness-proof result.
    fault_proofs = (
        ("missing-import", "Require Import MissingAssignmentControl.\n" + proof),
        ("syntax-in-theorem", proof.replace(
            "intro Run. induction Run; intros known paths Checked Bound;",
            "@@@. intro Run. induction Run; intros known paths Checked Bound;", 1)),
        ("unrelated-lemma", proof.replace(
            "intros Included. induction value;", "exact I. induction value;", 1)),
    )
    for name, text in fault_proofs:
        directory = output / name
        directory.mkdir()
        for suffix in (".v", ".vo"):
            shutil.copy2(output / "baseline" / ("AssignmentCheck" + suffix), directory)
        (directory / "AssignmentSound.v").write_text(text)
        result = subprocess.run(["coqc", *paths, "AssignmentSound.v"], cwd=directory,
                                capture_output=True, text=True, timeout=120)
        log = result.stdout + result.stderr
        (directory / "proof.log").write_text(log)
        classified = failure_at(text, log, "complete_path_safe")
        record = {"name": name, "kind": "error-classification-control",
                  "proof_exit": result.returncode, "classified_as_soundness_failure": classified,
                  "expected_result_met": result.returncode != 0 and not classified,
                  "proof_sha256": digest(directory / "AssignmentSound.v")}
        print(json.dumps(record), flush=True)
        results.append(record)
    summary = {"pass": all(r["expected_result_met"] for r in results), "results": results,
        "base_manifest_sha256": digest(base / "build.json"),
        "sources": {str(p): digest(p) for p in (
            HERE / "AssignmentCheck.v", HERE / "AssignmentSound.v", HERE / "AssignmentExec.v", HERE / "check.py",
            HERE / "proof_controls.py")}}
    (output / "results.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary["pass"]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    raise SystemExit(0 if run(args.base.resolve(), args.output.resolve()) else 1)
