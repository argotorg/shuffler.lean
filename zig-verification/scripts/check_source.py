#!/usr/bin/env python3
"""Check the pinned Zig source and the assembly embedded in the Lean program."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
ZIG_PATH = "Lift/LLVM/data/shuffler/src/shuffler.zig"
ASM_PATH = "Lift/LLVM/data/shuffler/shuffler.s"


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def embedded_assembly(source: str) -> bytes:
    pattern = r':=\s*shufflerProgram\(("(?:[^"\\]|\\.)*")\)'
    match = re.search(pattern, source)
    if match is None:
        raise ValueError("the Lean assembly literal is missing")
    return json.loads(match.group(1)).encode()


def check(root: Path, require_submodule: bool = False) -> None:
    manifest = json.loads((root / "SOURCE-MANIFEST.json").read_text())
    expected = {row["path"]: row["sha256"] for row in manifest["files"]}
    for name in [ZIG_PATH, ASM_PATH]:
        if digest((root / name).read_bytes()) != expected[name]:
            raise ValueError(f"source hash differs: {name}")
    assembly = (root / ASM_PATH).read_bytes()
    embedded = embedded_assembly((root / "Lift/Shuffler/Code.lean").read_text())
    if embedded != assembly:
        raise ValueError("the embedded Lean assembly differs from shuffler.s")
    source = root / "source/solidity-zig"
    if (source / ".git").exists():
        revision = subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip()
        if revision != manifest["soliditySource"]["commit"]:
            raise ValueError("the source submodule revision differs")
        relative = manifest["soliditySource"]["path"]
        if (source / relative).read_bytes() != (root / ZIG_PATH).read_bytes():
            raise ValueError("the source submodule Zig bytes differ")
    elif require_submodule:
        raise ValueError("initialize the exact Zig source submodule first")


def rebuild(root: Path, zig: str) -> None:
    version = subprocess.check_output([zig, "version"], text=True).strip()
    if version != "0.17.1":
        raise ValueError(f"Zig 0.17.1 is required; got {version}")
    with tempfile.TemporaryDirectory(prefix="shuffler-source-") as directory:
        work = Path(directory)
        environment = dict(os.environ, ZIG_GLOBAL_CACHE_DIR=str(work / "global-cache"),
                           ZIG_LOCAL_CACHE_DIR=str(work / "local-cache"))
        common = ["-target", "x86_64-linux-none", "-mcpu=baseline"]
        bc, assembly = work / "shuffler.bc", work / "shuffler.s"
        subprocess.run([zig, "build-obj", str(root / ZIG_PATH), *common,
                        "-O", "ReleaseSmall", "-fPIC", "-fstrip", "-fsingle-threaded",
                        "-fomit-frame-pointer", "-fno-unwind-tables", "-fno-stack-check",
                        "-fno-stack-protector", "-fno-builtin", "-fno-compiler-rt",
                        "-fno-ubsan-rt", "-fno-emit-bin", "-femit-llvm-bc=" + str(bc)],
                       env=environment, cwd=work, timeout=120, check=True)
        subprocess.run([zig, "cc", *common, "-S", "-O2", "-Xclang", "-disable-llvm-passes",
                        "-fPIC", "-fno-verbose-asm", "-fno-addrsig", "-Wno-override-module",
                        "-Wno-unused-command-line-argument", str(bc), "-o", str(assembly)],
                       env=environment, cwd=work, timeout=120, check=True)
        if assembly.read_bytes() != (root / ASM_PATH).read_bytes():
            raise ValueError("rebuilt assembly differs from the proved assembly")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-source", action="store_true")
    parser.add_argument("--rebuild", action="store_true")
    parser.add_argument("--zig", default=os.environ.get("ZIG", "zig"))
    args = parser.parse_args()
    check(ROOT, args.require_source)
    if args.rebuild:
        rebuild(ROOT, args.zig)
    print("Zig source and embedded assembly agree" + ("; rebuild agrees" if args.rebuild else ""))


if __name__ == "__main__":
    main()
