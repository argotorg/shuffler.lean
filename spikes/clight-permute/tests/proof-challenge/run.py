#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Compile source variants, then check the unchanged dependent Rocq proofs."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def command(args, directory, log, timeout=180):
    with log.open("w") as output:
        try:
            result = subprocess.run(args, cwd=directory, stdout=output,
                                    stderr=subprocess.STDOUT, timeout=timeout)
            return result.returncode
        except subprocess.TimeoutExpired:
            return "timeout"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--only", action="append", help="Select a mutation by name")
    parser.add_argument("--output", type=Path, default=ROOT / "build/proof-challenge")
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    baseline = ROOT / "build/proofs"
    spec = importlib.util.spec_from_file_location("audit", ROOT / "audit-deps.py")
    audit = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(audit)
    modules = {p.stem for p in ROOT.glob("*.v")}
    compcert = {Path(name).stem for name in audit.ALLOWED if name.endswith(".v")}
    graph = {name: audit.imports((ROOT / f"{name}.v").read_text(), modules | compcert,
             external=("Coq", "Stdlib", "Flocq", "mathcomp"),
             qualified={"Legacy": audit.LEGACY_MODULES, "compcert": compcert}) & modules
             for name in modules}
    order = [Path(p).stem for p in (baseline / "source-order.txt").read_text().split()
             if "/" not in p]
    for name in modules:
        if (ROOT / f"{name}.v").read_bytes() != (baseline / f"{name}.v").read_bytes():
            raise ValueError(f"baseline source differs: {name}; run check-proofs.sh")
        if not (baseline / f"{name}.vo").is_file():
            raise ValueError(f"missing baseline proof object: {name}")
    flags = ["-w", "-notation-overridden,-deprecated-from-Coq", "-R",
             str(ROOT / "build/compcert"), "compcert", "-Q", str(ROOT / "build/legacy"), "Legacy"]
    mutations = json.loads((HERE / "mutations.json").read_text())
    if args.only:
        unknown = set(args.only) - {m["name"] for m in mutations}
        if unknown:
            raise ValueError(f"unknown mutations: {sorted(unknown)}")
        mutations = [m for m in mutations if m["name"] in args.only]
    results = []
    for mutation in mutations:
        name, module = mutation["name"], mutation["module"]
        case = output / name
        case.mkdir(exist_ok=True)
        work = case / "proofs"
        # Copy, never share mutable .vo or .v files with the checked baseline.
        if work.exists():
            shutil.rmtree(work)
        shutil.copytree(baseline, work)
        source = (ROOT / f"{module}.v").read_text()
        if source.count(mutation["old"]) != 1:
            raise ValueError(f"mutation is not unique: {name}")
        changed = source.replace(mutation["old"], mutation["new"], 1)
        (work / f"{module}.v").write_text(changed)
        shutil.copyfile(work / f"{module}.v", case / f"{module}.v")
        affected = {module}
        for dependent in order:
            if graph[dependent] & affected:
                affected.add(dependent)
        start = time.monotonic()
        result = {"name": name, "module": module,
                  "equivalent_control": mutation.get("equivalent", False),
                  "source_sha256": hashlib.sha256(changed.encode()).hexdigest(),
                  "compiled": []}
        for dependent in order:
            if dependent not in affected:
                continue
            status = command(["coqc", *flags, f"{dependent}.v"], work,
                             case / f"{dependent}.log")
            if status != 0:
                result.update(failed_module=dependent, exit=status,
                              stage="source" if dependent == module else "proof")
                break
            result["compiled"].append(dependent)
        else:
            # A surviving source must also satisfy each independent public type.
            for contract in ("ProofContract", "ReachabilityContract", "PublicContract"):
                shutil.copyfile(HERE / f"{contract}.v", work / f"{contract}.v")
                status = command(["coqc", *flags, f"{contract}.v"], work, case / f"{contract}.log")
                if status != 0:
                    break
            result.update(stage="contract" if status else "accepted", exit=status)
        result["seconds"] = round(time.monotonic() - start, 3)
        result["expected_result"] = (result["stage"] == "accepted" if result["equivalent_control"]
                                     else result["stage"] == "proof" and result["exit"] != "timeout")
        results.append(result)
        (output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps(result), flush=True)
    if not all(r["expected_result"] for r in results):
        raise SystemExit("some mutations survived, failed to compile, timed out, or rejected an equivalent control")


if __name__ == "__main__":
    main()
