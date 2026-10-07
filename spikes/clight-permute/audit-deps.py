#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check the exact LGPL CompCert source set and its import closure."""
import hashlib
from pathlib import Path
import re
import shutil
import sys

BASE = Path(__file__).resolve().parent
ALLOWED = frozenset("""
LICENSE
cfrontend/Clight.v cfrontend/ClightBigstep.v cfrontend/Cop.v cfrontend/Ctypes.v
common/AST.v common/Builtins.v common/Builtins0.v common/Errors.v
common/Events.v common/Globalenvs.v common/Linking.v common/Memdata.v
common/Memory.v common/Memtype.v common/Smallstep.v common/Values.v
export/Clightdefs.v export/Ctypesdefs.v
lib/Axioms.v lib/Coqlib.v lib/Floats.v lib/IEEE754_extra.v lib/Integers.v
lib/Intv.v lib/Maps.v lib/Zbits.v x86/Builtins1.v x86_64/Archi.v
""".split())
ROOTS = frozenset(("Clight", "ClightBigstep", "Clightdefs", "Ctypesdefs"))
PROJECT_MODULES = frozenset("""
Permute Extract SolcModel ModelProofs ModelTests ClightEval ClightEvalProofs
ClightEvalTests ClightMemory ClightEntry ClightSwap ClightScalar ClightExchange
ClightChoose ClightExchangeSuccess ChooseModel ModelArrays ClightMain ClightInitialize
ClightLoop ClightCall ClightNormalize ClightValidation ClightSearch ClightFill ClightFillLoop
FirstFree ClightCorrect ClightNormalization
Reachability ClightReachability
ModelSpec PermuteSpec PermuteCorrect
""".split())
LEGACY_MODULES = frozenset(("Permute", "Proofs", "Compute", "CycleProbe", "Tests"))


def uncomment(source):
    """Remove nested Rocq comments before reading commands."""
    depth, index, quoted = 0, 0, False
    result = []
    while index < len(source):
        pair = source[index:index + 2]
        if not depth and quoted:
            result.append(source[index])
            if source[index] == '"':
                if source[index:index + 2] == '""':
                    result.append('"')
                    index += 1
                else:
                    quoted = False
            index += 1
        elif not depth and source[index] == '"':
            quoted = True
            result.append(source[index])
            index += 1
        elif pair == "(*":
            depth += 1
            index += 2
        elif pair == "*)" and depth:
            depth -= 1
            index += 2
        else:
            result.append(" " if depth else source[index])
            index += 1
    if depth:
        raise ValueError("unfinished Rocq comment")
    if quoted:
        raise ValueError("unfinished Rocq string")
    return "".join(result)


def imports(source, local, external=("Coq", "Stdlib", "Flocq"), qualified=None):
    dependencies = set()
    source = uncomment(source)
    if re.search(r"\b(?:Load|LoadPath|Declare\s+ML)\b", source):
        raise ValueError("source loads code outside Require")
    for command in re.split(r"\.\s+", source):
        if not re.search(r"\bRequire\b", command):
            continue
        match = re.fullmatch(
            r"\s*(?:From\s+(\w+)\s+)?Require\s+"
            r"(?:(?:Import|Export)\s+)?([\w.\s]+)\s*", command)
        if match is None:
            raise ValueError(f"unrecognized import: {command.strip()}")
        origin, modules = match.groups()
        if origin in external:
            continue
        if qualified and origin in qualified:
            for module in modules.split():
                if module not in qualified[origin]:
                    raise ValueError(f"unapproved {origin} dependency: {module}")
            continue
        if origin not in (None, "compcert"):
            raise ValueError(f"unapproved import prefix: {origin}")
        for module in modules.split():
            if module not in local:
                raise ValueError(f"unapproved CompCert dependency: {module}")
            dependencies.add(module)
    return dependencies


def audit(root=BASE / "vendor/compcert", manifest=BASE / "vendor/compcert.sha256"):
    files = {str(path.relative_to(root)) for path in root.rglob("*") if path.is_file()}
    if files != ALLOWED:
        raise ValueError(f"source set differs: {sorted(files ^ ALLOWED)}")
    hashes = {}
    for line in manifest.read_text().splitlines():
        digest, name = line.split("  ", 1)
        if name in hashes or not re.fullmatch(r"[0-9a-f]{64}", digest):
            raise ValueError("invalid digest manifest")
        hashes[name] = digest
    if hashes.keys() != ALLOWED:
        raise ValueError("digest manifest differs from the license allowlist")
    for name, digest in hashes.items():
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
            raise ValueError(f"source digest mismatch: {name}")
    modules = {Path(name).stem: name for name in ALLOWED if name.endswith(".v")}
    graph = {module: imports((root / name).read_text(), modules)
             for module, name in modules.items()}
    reached = set()
    pending = list(ROOTS)
    while pending:
        module = pending.pop()
        if module not in reached:
            reached.add(module)
            pending.extend(graph[module])
    if reached != modules.keys():
        raise ValueError(f"unused files: {sorted(modules.keys() - reached)}")
    return len(modules)


def audit_project(root=BASE):
    modules = {path.stem for path in root.glob("*.v")}
    if not modules <= PROJECT_MODULES:
        raise ValueError(f"unapproved project modules: {sorted(modules - PROJECT_MODULES)}")
    compcert = {Path(name).stem for name in ALLOWED if name.endswith(".v")}
    for module in modules:
        source = root / (module + ".v")
        if source.is_symlink():
            raise ValueError(f"project source is a symlink: {module}")
        imports(source.read_text(), modules | compcert,
                external=("Coq", "Stdlib", "Flocq", "mathcomp"),
                qualified={"Legacy": LEGACY_MODULES, "compcert": compcert})
    return len(modules)


def stage_dependencies(destination=BASE / "build/compcert", source=BASE / "vendor/compcert"):
    """Copy only allowed source; invalidate compiled files after source changes."""
    artifacts = set()
    directories = set()
    if destination.is_symlink():
        raise ValueError("unexpected dependency build path: root is a symlink")
    for name in ALLOWED:
        path = Path(name)
        directories.update(str(parent) for parent in path.parents if str(parent) != ".")
        if path.suffix == ".v":
            artifacts.update(str(path.with_suffix(suffix))
                             for suffix in (".vo", ".vos", ".vok", ".glob"))
            artifacts.add(str(path.parent / ("." + path.stem + ".aux")))
    for path in destination.rglob("*"):
        relative = str(path.relative_to(destination))
        if path.is_symlink() or (path.is_dir() and relative not in directories):
            raise ValueError(f"unexpected dependency build path: {relative}")
        if path.is_file() and relative not in ALLOWED | artifacts:
            raise ValueError(f"unexpected dependency build file: {relative}")
    changed = any(not (destination / name).is_file() or
                  (destination / name).read_bytes() != (source / name).read_bytes()
                  for name in ALLOWED)
    if changed:
        for name in artifacts:
            (destination / name).unlink(missing_ok=True)
    for name in ALLOWED:
        target = destination / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source / name, target)
    return changed


if __name__ == "__main__":
    try:
        print(f"License allowlist and import closure: {audit()} CompCert modules")
        print(f"Project import boundary: {audit_project()} modules")
        if len(sys.argv) == 2 and sys.argv[1] == "--stage":
            if stage_dependencies():
                print("Dependency source changed; compiled cache discarded")
        elif len(sys.argv) != 1:
            sys.exit("usage: audit-deps.py [--stage]")
    except ValueError as error:
        sys.exit(str(error))
