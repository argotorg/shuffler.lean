# SPDX-License-Identifier: GPL-3.0-or-later
"""Build both implementations with Fil-C; check the runtime and replay inputs."""
import hashlib
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys

TEST = Path(__file__).resolve().parent
BUILD = TEST.parent / "build" / "filc"
FILC = Path(os.environ["FILC_DIR"])
CHECKS = BUILD / "checks"
CHECKS.mkdir(exist_ok=True)


def run(args, **kwargs):
    display = args if len(args) < 20 else [*args[:2], f"... ({len(args) - 2} more arguments)"]
    print("+", shlex.join(map(str, display)), flush=True)
    return subprocess.run(list(map(str, args)), check=True, **kwargs)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


licenses = {
    "LLVM-LICENSE.txt": "8d85c1057d742e597985c7d4e6320b015a9139385cff4cbae06ffc0ebe89afee",
    "MUSL-LICENSE.txt": "f9bc4423732350eb0b3f7ed7e91d530298476f8fec0c6c427a1c04ade22655af",
    "PAS-LICENSE.txt": "e212b57835bca80de394f684995ce378de96f00b1c2036c3ae058a5381564df0",
}
for name, expected in licenses.items():
    if digest(FILC / name) != expected:
        raise SystemExit(f"license digest mismatch: {name}")

cc = FILC / "build/bin/clang"
cxx = FILC / "build/bin/clang++"
version = run([cc, "--version"], capture_output=True, text=True).stdout
print(version, flush=True)
if "Fil-C 0.686" not in version or "163fae598eaf249b74065b0156f3a7e7ba8c0e5a" not in version:
    raise SystemExit("unexpected Fil-C compiler version")

# Only range-v3 is a host header dependency. It is header-only and is compiled
# by Fil-C with Fil-C's C++ standard library. Do not import all Nix C flags.
candidates = shlex.split(os.environ.get("NIX_CFLAGS_COMPILE", ""))
range_include = os.environ.get("FILC_RANGE_INCLUDE")
if range_include is None:
    range_include = next((x for x in candidates if "range-v3-" in x and
                          (Path(x) / "range/v3/version.hpp").is_file()), None)
if range_include is None:
    raise SystemExit("set FILC_RANGE_INCLUDE to the pinned range-v3 include directory")
print(f"range-v3 headers: {range_include}", flush=True)
print(f"permute.c SHA-256: {digest(TEST.parent / 'permute.c')}", flush=True)
print(f"oracle.cpp SHA-256: {digest(TEST / 'oracle.cpp')}", flush=True)
run([sys.executable, TEST / "prepare_oracle.py", CHECKS / "oracle"])
run([sys.executable, TEST / "test_prepare_oracle.py", CHECKS / "oracle"])

# The Nix linker wrapper can add native library paths. Use its underlying ELF
# linker when available, and pass no native libraries to the Fil-C link.
linker = shutil.which("ld")
if os.environ.get("NIX_BINTOOLS"):
    raw = Path(os.environ["NIX_BINTOOLS"]) / "nix-support/orig-bintools"
    if raw.is_file():
        linker = str(Path(raw.read_text().strip()) / "bin/ld")
flags = ["-O2", "-g", "-fstrict-aliasing"]
link_flags = flags + [f"-fuse-ld={linker}"]
for unit in ["permute", "check_case", "tests", "fuzz", "guided", "filc-replay"]:
    source = TEST.parent / "permute.c" if unit == "permute" else TEST / f"{unit}.c"
    run([cc, "-std=c11", "-pedantic-errors", "-Wall", "-Wextra", "-Wconversion",
         "-Wsign-conversion", *flags, "-c", source, "-o", CHECKS / f"{unit}.o"])
run([cxx, "-std=c++20", "-pedantic-errors", "-Wall", "-Wextra", *flags,
     "-isystem", range_include, "-I", CHECKS / "oracle", "-c", TEST / "oracle.cpp",
     "-o", CHECKS / "oracle.o"])
for driver, extra in [("tests", []), ("fuzz", []), ("filc-replay", ["guided"])]:
    units = ["permute", "check_case", "oracle", driver] + extra
    run([cxx, *link_flags, *(CHECKS / f"{x}.o" for x in units),
         "-o", CHECKS / driver])

loader = FILC / "pizfix/lib/ld-fil1-x86_64.so"
for binary in ["tests", "fuzz", "filc-replay"]:
    linkage = run([loader, "--list", CHECKS / binary], capture_output=True, text=True).stdout
    (CHECKS / f"{binary}.libraries.txt").write_text(linkage)
    print(linkage, flush=True)
    for line in linkage.splitlines():
        path = line.split("=>", 1)[-1].strip().split(" ", 1)[0]
        if not Path(path).resolve().is_relative_to((FILC / "pizfix/lib").resolve()):
            raise SystemExit(f"library outside Fil-C runtime: {line}")
    run(["readelf", "-d", CHECKS / binary], stdout=(CHECKS / f"{binary}.elf.txt").open("w"))
headers = run([cxx, "-std=c++20", "-E", "-v", "-x", "c++", "/dev/null"],
              capture_output=True, text=True)
(CHECKS / "header-search.txt").write_text(headers.stderr)
for obj in ["permute", "oracle"]:
    symbols = run(["nm", CHECKS / f"{obj}.o"], capture_output=True, text=True).stdout
    if "pizlonated_" not in symbols or "filc_" not in symbols:
        raise SystemExit(f"Fil-C instrumentation missing from {obj}")

# Negative controls use C allocation and the C++ vector API.
# argc keeps the index unknown; volatile keeps the invalid store in the code.
probes = {
    "c": '#include <stdlib.h>\nint main(int argc,char **argv) { (void)argv; unsigned *p=malloc(sizeof(*p)); if (!p) return 2; ((volatile unsigned *)p)[argc]=42; free(p); return 0; }\n',
    "cpp": '#include <vector>\nint main(int argc,char **argv) { (void)argv; std::vector<unsigned> p(1); volatile unsigned *q=p.data(); q[argc]=42; return 0; }\n',
}
for language, source in probes.items():
    path = CHECKS / f"bounds-probe.{language}"
    path.write_text(source)
    binary = CHECKS / f"bounds-probe-{language}"
    run([cc if language == "c" else cxx, *link_flags, path, "-o", binary])
    near = subprocess.run([binary], capture_output=True, text=True)
    (CHECKS / f"bounds-probe-{language}-near.log").write_text(near.stdout + near.stderr)
    print(f"{language} index-one probe: status {near.returncode} (allocation rounding)", flush=True)
    result = subprocess.run([binary, *(["x"] * 16)], capture_output=True, text=True)
    (CHECKS / f"bounds-probe-{language}.log").write_text(result.stdout + result.stderr)
    if result.returncode == 0 or "filc safety error: cannot write" not in result.stderr:
        raise SystemExit(f"Fil-C bounds probe did not give the expected failure: {result.stderr}")
    print(f"{language} bounds probe: Fil-C panic, status {result.returncode}", flush=True)

run([CHECKS / "tests"])
run([CHECKS / "fuzz", os.environ.get("PERMUTE_FUZZ_CASES", "100000"),
     os.environ.get("PERMUTE_FUZZ_SEED", "2654435769")])
seeds = BUILD / "seeds"
run([sys.executable, TEST / "seed_corpus.py", seeds])
sources = [seeds] + list(map(Path, sys.argv[1:]))
snapshot = BUILD / "corpus"
snapshot.mkdir(exist_ok=True)
for directory in sources:
    if not directory.is_dir():
        raise SystemExit(f"missing corpus directory: {directory}")
    for path in sorted(directory.iterdir()):
        if not path.is_file() or path.name.startswith("."):
            continue
        try:
            content = path.read_bytes()
        except FileNotFoundError:  # Concurrent corpus reduction may remove it.
            continue
        if len(path.name) == 40 and all(x in "0123456789abcdef" for x in path.name):
            if hashlib.sha1(content).hexdigest() != path.name:
                continue  # Do not replay a file before the fuzzer finishes it.
        name = hashlib.sha256(content).hexdigest()
        (snapshot / name).write_bytes(content)
inputs = sorted(snapshot.iterdir())
manifest = "".join(f"{digest(path)}  {path.name}\n" for path in inputs)
(BUILD / "corpus.sha256").write_text(manifest)
for start in range(0, len(inputs), 128):
    run([CHECKS / "filc-replay", *inputs[start:start + 128]])
negative = subprocess.run([CHECKS / "filc-replay", CHECKS / "does-not-exist"],
                          capture_output=True, text=True)
if negative.returncode == 0:
    raise SystemExit("replay accepted a missing file")
empty = CHECKS / "empty-input"
empty.write_bytes(b"")
run([CHECKS / "filc-replay", empty])
oversized = CHECKS / "oversized-input"
with oversized.open("wb") as stream:
    stream.truncate(1048577)
negative = subprocess.run([CHECKS / "filc-replay", oversized], capture_output=True, text=True)
if negative.returncode == 0 or "invalid corpus file size" not in negative.stderr:
    raise SystemExit("replay accepted an oversized file")
print(f"Fil-C corpus replay: {len(inputs)} unique inputs; manifest SHA-256 "
      f"{hashlib.sha256(manifest.encode()).hexdigest()}", flush=True)
