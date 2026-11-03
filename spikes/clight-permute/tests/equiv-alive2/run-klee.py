# SPDX-License-Identifier: GPL-3.0-or-later
"""Check all symbolic values for each selected concrete permutation with KLEE."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import itertools
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from klee_coverage import function_coverage
from profiles import parse_value_groups, case_name
from fetch_nothrow import fetch
from completion import check_completions
from exploration import check_exploration
from program_symbols import check_modules

HERE = Path(__file__).resolve().parent
TEST = HERE.parent
DEFAULT = TEST.parent / "build/equiv-alive2"
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--sizes", default="2,3")
parser.add_argument("--jobs", type=int, default=1)
parser.add_argument("--permutation", help="One comma-separated permutation, instead of all permutations")
parser.add_argument("--value-groups", help="Restrict values to the given group pattern, e.g. 0,1,0")
parser.add_argument("--core", type=Path, default=TEST.parent / "permute.c")
parser.add_argument("--solc-permute", type=Path, help="Explicit mutant solc_permute.inc overlay")
parser.add_argument("--output", type=Path)
parser.add_argument("--max-time", default="120s", help="Limit for each case; any partial path fails the run")
args = parser.parse_args()
sizes = [int(x) for x in args.sizes.split(",")]
if args.jobs < 1 or args.jobs > 8:
    parser.error("jobs must be between 1 and 8")
if not sizes or any(x < 1 or x > 1024 for x in sizes):
    parser.error("sizes must be between 1 and 1024")
if args.permutation:
    permutation = tuple(map(int, args.permutation.split(",")))
    if sorted(permutation) != list(range(len(permutation))):
        parser.error("invalid permutation")
    if sizes != [len(permutation)]:
        parser.error("--sizes must match the selected permutation length")
groups = None
if args.value_groups is not None:
    try:
        groups = parse_value_groups(args.value_groups, sizes)
    except ValueError as error:
        parser.error(str(error))
build = args.output or DEFAULT / time.strftime("klee-%Y%m%d-%H%M%S", time.gmtime())
build = build.resolve()
build.mkdir(parents=True, exist_ok=False)
core = args.core.resolve(strict=True)


def run(command, log):
    command = list(map(str, command))
    print("+", " ".join(command), flush=True)
    with log.open("w") as stream:
        result = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        print(log.read_text(), file=sys.stderr)
        raise SystemExit(f"command failed ({result.returncode}): {log}")


run([sys.executable, TEST / "prepare_oracle.py", build / "oracle"], build / "oracle-fetch.log")
run([sys.executable, TEST / "test_prepare_oracle.py", build / "oracle"], build / "oracle-check.log")
if args.solc_permute:
    shutil.copyfile(args.solc_permute.resolve(strict=True), build / "oracle/solc_permute.inc")
run(["klee", "--version"], build / "klee-version.txt")
run(["clang", "--version"], build / "clang-version.txt")
run(["z3", "--version"], build / "z3-version.txt")
runtime = fetch(build / "runtime")
manifest = {
    "core": str(core), "core_sha256": hashlib.sha256(core.read_bytes()).hexdigest(),
    "solc_permute_sha256": hashlib.sha256((build / "oracle/solc_permute.inc").read_bytes()).hexdigest(),
    "sizes": sizes, "value_groups": groups, "cases": [],
}
driver = HERE / ("profile-driver.c" if groups is not None else "klee-driver.c")
sources = [core, HERE / "core.c", HERE / "oracle.cpp", driver,
           HERE / "observation.h", TEST / "oracle.cpp", TEST / "test.h",
           TEST.parent / "permute.h", Path(__file__), HERE / "profiles.py",
           HERE / "klee_coverage.py", HERE / "fetch_nothrow.py", runtime,
           HERE / "completion.py", HERE / "completion.c",
           HERE / "exploration.py",
           HERE / "program_symbols.py",
           HERE / "klee-shell.nix",
           *sorted((build / "oracle").glob("*.inc"))]
manifest["source_sha256"] = {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                              for path in sources}
(build / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
common = ["-O0", "-g", "-Xclang", "-disable-O0-optnone", "-fno-vectorize",
          "-fno-slp-vectorize", "-U_FORTIFY_SOURCE", "-emit-llvm", "-c",
          "-fsanitize=signed-integer-overflow,shift,integer-divide-by-zero,bounds",
          "-fno-sanitize-recover=all"]
run(["clang++", "-std=c++20", *common, "-fno-exceptions", runtime,
     "-o", build / "runtime.bc"], build / "runtime-build.log")
run(["clang", *common, HERE / "completion.c", "-o", build / "completion.bc"],
    build / "completion-build.log")
def check_case(item):
    size, choice = item
    name = case_name(choice)
    case = build / name
    case.mkdir()
    defines = [f"-DEQUIV_N={size}", "-DEQUIV_PERMUTATION={" +
               ",".join(f"{x}U" for x in choice) + "}"]
    if groups is not None:
        defines += [f"-DEQUIV_GROUP_COUNT={max(groups) + 1}",
                    "-DEQUIV_VALUE_GROUPS={" + ",".join(f"{x}U" for x in groups) + "}"]
    run(["clang", *common, *defines, "-Dobserve=observe_core",
         f'-DEQUIV_CORE_PATH="{core}"', "-I", TEST.parent,
         HERE / "core.c", "-o", case / "core.bc"], case / "core-build.log")
    run(["clang++", "-std=c++20", *common, "-fno-exceptions", *defines,
         "-Dobserve=observe_oracle", "-I", build / "oracle", HERE / "oracle.cpp",
         "-o", case / "oracle.bc"], case / "oracle-build.log")
    run(["clang", *common, *defines, "-Dmain=checked_main", driver, "-o", case / "driver.bc"],
        case / "driver-build.log")
    program_symbols = check_modules([case / "core.bc", case / "oracle.bc", build / "runtime.bc"],
                                    case / "program-symbols.json")
    if not program_symbols["pass"]:
        raise SystemExit(f"program modules use KLEE control symbols: {case / 'program-symbols.json'}")
    run(["llvm-link", case / "core.bc", case / "oracle.bc", case / "driver.bc", build / "runtime.bc",
         build / "completion.bc",
         "-o", case / "linked.bc"], case / "link.log")
    run(["klee", "--solver-backend=z3", "--libc=none", "--ubsan-runtime",
         "--external-calls=none", "--check-div-zero=true", "--check-overshift=true",
         "--emit-all-errors", f"--max-time={args.max_time}",
         f"--output-dir={case / 'proof'}", case / "linked.bc"], case / "proof.log")
    log = (case / "proof.log").read_text()
    complete = re.search(r"completed paths = (\d+)", log)
    partial = re.search(r"partially completed paths = (\d+)", log)
    errors = list((case / "proof").glob("*.err"))
    coverage = function_coverage(case / "proof/run.istats")
    completion = check_completions(case / "proof", int(complete[1]) if complete else 0,
                                   "symbols" if groups is not None else "values",
                                   4 * (max(groups) + 1 if groups is not None else size))
    exploration = check_exploration(case / "proof", log)
    changed_sources = [str(path) for path in sources
                       if hashlib.sha256(path.read_bytes()).hexdigest()
                       != manifest["source_sha256"][str(path)]]
    ok = (complete is not None and int(complete[1]) > 0 and partial is not None
          and int(partial[1]) == 0 and not errors and "KLEE: ERROR:" not in log
          and "calling external:" not in log
          and completion["pass"]
          and exploration["pass"]
          and not changed_sources
          and all(x["covered_instructions"] > 0 for x in coverage.values()))
    result = {"n": size, "directory": name, "permutation": choice, "complete_paths":
              int(complete[1]) if complete else None, "partial_paths":
              int(partial[1]) if partial else None,
              "errors": [x.name for x in errors], "function_coverage": coverage,
              "completion": completion, "exploration": exploration,
              "program_symbols": program_symbols,
              "changed_sources": changed_sources,
              "linked_sha256": hashlib.sha256((case / "linked.bc").read_bytes()).hexdigest(),
              "pass": ok}
    return result


def selected_cases():
    for size in sizes:
        choices = [permutation] if args.permutation else itertools.permutations(range(size))
        for choice in choices:
            yield size, choice


with ThreadPoolExecutor(max_workers=args.jobs) as workers:
    for result in workers.map(check_case, selected_cases(), buffersize=args.jobs):
        manifest["cases"].append(result)
        (build / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
        print(json.dumps(result), flush=True)
        if not result["pass"]:
            raise SystemExit(f"proof did not complete without errors: {result}")
print(f"KLEE passed {len(manifest['cases'])} permutation cases: {build}", flush=True)
