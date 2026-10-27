#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Build and kernel-check the assignment path and execution proofs."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
MODULES = ("AssignmentCheck", "AssignmentSound", "SoundContract", "AssignmentExec", "ExecContract")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build(base, output):
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
    sources = {}
    local = audit.PROJECT_MODULES | {Path(p).stem for p in audit.ALLOWED} | set(MODULES)
    paths = ["-R", str(ROOT / "build/compcert"), "compcert", "-Q", str(base), ""]
    for module in MODULES:
        source = HERE / (module + ".v")
        audit.imports(source.read_text(), local, external=("Coq", "Stdlib", "Flocq", "mathcomp"))
        shutil.copy2(source, output / source.name)
        sources[str(source)] = digest(source)
        with (output / (module + ".log")).open("w") as log:
            subprocess.run(["coqc", *paths, source.name], cwd=output,
                           stdout=log, stderr=subprocess.STDOUT, check=True, timeout=120)
    with (output / "kernel.log").open("w") as log:
        subprocess.run(["coqchk", "-silent", "-o", *paths, *MODULES], cwd=output,
                       stdout=log, stderr=subprocess.STDOUT, check=True)
    with (output / "kernel-policy.log").open("w") as log:
        subprocess.run(["python3", str(ROOT / "check-assumptions.py"), "--kernel",
                        str(output / "kernel.log")], stdout=log, stderr=subprocess.STDOUT,
                       check=True)
    sources[str(HERE / "sound.py")] = digest(HERE / "sound.py")
    result = {"pass": True, "sources": sources,
        "base_manifest_sha256": digest(base / "build.json"),
        "artifacts": {p.name: digest(p) for p in output.iterdir() if p.is_file()}}
    (output / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    print("Assignment path and execution proofs, public types, and kernel policy pass", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    build(args.base.resolve(), args.output.resolve())
