#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Build the actual Clight interpreter and C in a new output directory."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def build(output):
    output.mkdir(parents=True, exist_ok=False)
    spec = importlib.util.spec_from_file_location("audit", ROOT / "audit-deps.py")
    audit = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(audit)
    audit.audit()
    audit.audit_project()
    audit.imports((HERE / "Driver.v").read_text(),
                  audit.PROJECT_MODULES | {Path(p).stem for p in audit.ALLOWED},
                  external=("Coq", "Stdlib", "Flocq", "mathcomp"))
    records = {}
    staged = ROOT / "build/compcert"
    if {str(p.relative_to(staged)) for p in staged.rglob("*.v")} != {
            name for name in audit.ALLOWED if name.endswith(".v")}:
        raise ValueError("staged CompCert source set differs from LGPL allowlist")
    for name in sorted(audit.ALLOWED):
        path = staged / name
        if path.read_bytes() != (ROOT / "vendor/compcert" / name).read_bytes():
            raise ValueError(f"staged dependency source differs: {name}")
        records[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
        if path.suffix == ".v":
            obj = path.with_suffix(".vo")
            records[str(obj)] = hashlib.sha256(obj.read_bytes()).hexdigest()
    for path in (HERE / "build.py", HERE / "compare.py", HERE / "test_compare.py",
                 ROOT / "audit-deps.py",
                 ROOT / "check-assumptions.py"):
        records[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
    for path in [*ROOT.glob("*.v"), HERE / "Driver.v", HERE / "main.ml",
                 HERE / "native.c", ROOT / "permute.c", ROOT / "permute.h"]:
        shutil.copy2(path, output / path.name)
        records[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()

    # Nix adds fortify after command-line flags. It requires optimization.
    environment = {key: (" ".join(flag for flag in value.split()
                    if flag not in ("fortify", "fortify3"))
                    if key.startswith("NIX_HARDENING_ENABLE") else value)
                   for key, value in os.environ.items()}
    (output / "hardening.json").write_text(json.dumps({key: value
        for key, value in environment.items() if "HARDENING" in key}, indent=2) + "\n")

    def command(args, log):
        print("+", " ".join(map(str, args)), flush=True)
        with (output / log).open("w") as stream:
            subprocess.run(args, cwd=output, env=environment,
                           stdout=stream, stderr=subprocess.STDOUT,
                           check=True)

    paths = ["-R", str(ROOT / "build/compcert"), "compcert",
             "-Q", str(ROOT / "build/legacy"), "Legacy"]
    command(["coqdep", "-sort", *paths, "Driver.v"], "source-order.txt")
    sources = (output / "source-order.txt").read_text().split()
    for source in sources:
        if Path(source).parent == Path("."):
            command(["coqc", "-w", "-notation-overridden,-deprecated-from-Coq",
                     *paths, source], Path(source).stem + ".log")
    command(["coqchk", "-silent", "-o", *paths, "Driver"], "kernel.log")
    command(["python3", str(ROOT / "check-assumptions.py"), "--kernel",
             str(output / "kernel.log")], "kernel-policy.log")
    command(["ocamlopt", "-w", "-a", "-c", "evaluation.mli"], "ocaml-interface.log")
    command(["ocamlopt", "-w", "-a", "-c", "evaluation.ml"], "ocaml-extraction.log")
    command(["ocamlopt", "-w", "+a-4-70", "-o", "rocq-eval", "evaluation.cmx",
             "main.ml"], "ocaml-main.log")
    for compiler in ("gcc", "clang"):
        command([compiler, "--version"], compiler + "-version.txt")
        for level in ("0", "2", "3"):
            name = f"native-{compiler}-O{level}"
            command([compiler, "-std=c11", "-Wall", "-Wextra", "-Werror",
                     "-U_FORTIFY_SOURCE", "-O" + level, "-I.",
                     "native.c", "permute.c", "-o", name],
                    name + ".log")
    command(["coqc", "--version"], "rocq-version.txt")
    command(["ocamlopt", "-version"], "ocaml-version.txt")
    artifacts = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                 for p in output.iterdir() if p.is_file()}
    (output / "build.json").write_text(json.dumps({"sources": records,
        "artifacts": artifacts}, indent=2) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    build(parser.parse_args().output.resolve())
