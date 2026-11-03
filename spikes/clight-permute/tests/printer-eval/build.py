#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Extract generic Clight execution and link the unchanged C printer."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build(base, output):
    output.mkdir(parents=True, exist_ok=False)
    prior = json.loads((base / "build.json").read_text())
    for path, expected in prior["sources"].items():
        if digest(Path(path)) != expected:
            raise ValueError(f"base source changed: {path}")
    for name, expected in prior["artifacts"].items():
        if name.endswith((".vo", ".v")) and digest(base / name) != expected:
            raise ValueError(f"base proof artifact changed: {name}")
    spec = importlib.util.spec_from_file_location("audit", ROOT / "audit-deps.py")
    audit = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(audit)
    audit.audit()
    audit.imports((HERE / "Generic.v").read_text(),
        audit.PROJECT_MODULES | {Path(p).stem for p in audit.ALLOWED} | {"Driver"},
        external=("Coq", "Stdlib", "Flocq", "mathcomp"))
    sources = {}
    for path in (HERE / "Generic.v", HERE / "generator.ml", HERE / "main.ml",
                 HERE / "native.c", ROOT / "printer.ml", ROOT / "permute.h"):
        shutil.copy2(path, output / path.name)
        sources[str(path)] = digest(path)
    for path in (HERE / "build.py", HERE / "run.py", HERE / "test_controls.py",
                 HERE.parent / "rocq-eval/compare.py"):
        sources[str(path)] = digest(path)

    def command(args, log):
        print("+", " ".join(map(str, args)), flush=True)
        with (output / log).open("w") as stream:
            subprocess.run(args, cwd=output, stdout=stream, stderr=subprocess.STDOUT,
                           check=True)

    paths = ["-R", str(ROOT / "build/compcert"), "compcert", "-Q", str(base), "",
             "-Q", str(ROOT / "build/legacy"), "Legacy"]
    command(["coqc", *paths, "Generic.v"], "Generic.log")
    command(["coqchk", "-silent", "-o", *paths, "Generic"], "kernel.log")
    command(["python3", str(ROOT / "check-assumptions.py"), "--kernel",
             str(output / "kernel.log")], "kernel-policy.log")
    command(["ocamlopt", "-w", "-a", "-c", "extracted.mli"], "interface.log")
    command(["ocamlopt", "-w", "-a", "-c", "extracted.ml"], "extraction.log")
    command(["ocamlopt", "-w", "+a-4-70", "-o", "printer-eval", "extracted.cmx",
             "printer.ml", "generator.ml", "main.ml"], "program.log")
    artifacts = {p.name: digest(p) for p in output.iterdir() if p.is_file()}
    (output / "build.json").write_text(json.dumps({"sources": sources,
        "artifacts": artifacts, "base": str(base),
        "base_manifest_sha256": digest(base / "build.json")}, indent=2) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    build(args.base.resolve(), args.output.resolve())
