#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Build source mutations and controls; keep compilation and tests separate."""
import hashlib
import json
from pathlib import Path
import shlex
import os
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE.parent))
from prepare_oracle import prepare

# Each tuple performs exactly one source replacement. Controls also change bytes.
VARIANTS = (
    ("c-depth-bound", "c", "change", "v13 > 16U", "v13 > 15U"),
    ("c-size-bound", "c", "change", "v1 > 1024U", "v1 > 1023U"),
    ("c-target-destination", "c", "change", "v4[v9] = v2[v8];", "v4[v8] = v2[v8];"),
    ("c-equal-swap", "c", "change", "if (v2[v11] != v2[v10])", "if (1U)"),
    ("c-swap-data", "c", "change", "v2[v10] = v12;", "v2[v10] = v2[v11];"),
    ("c-trace-depth", "c", "change", "v6[v7[0U]] = v13;", "v6[v7[0U]] = (v13 + 1U);"),
    ("c-trace-count", "c", "change", "v7[0U] = (v7[0U] + 1U);", "v7[0U] = (v7[0U] + 2U);"),
    ("c-blocked-position", "c", "change", "v7[1U] = v11;", "v7[1U] = v10;"),
    ("c-excess-depth", "c", "change", "v7[2U] = (v13 - 16U);", "v7[2U] = (v13 - 15U);"),
    ("cpp-equal-swap", "cpp", "change", "if (m_data[_pos.value] == m_data[top.value])", "if (false)"),
    ("cpp-swap-data", "cpp", "change", "swapWith(_pos);", "m_mapping.swapDestinations(_pos, top);"),
    ("cpp-destination-pairing", "cpp", "change", "_permutation[movers[i]] = vacant[i];", "_permutation[movers[i]] = vacant[movers.size() - 1 - i];"),
    ("cpp-selection-order", "cpp", "change", "ranges::views::iota(std::size_t{0}, top) | ranges::views::reverse", "ranges::views::iota(std::size_t{0}, top)"),
    ("cpp-excess-depth", "cpp", "change", "return blockSwapUnreachable(_pos);", "return Blocked{_pos, 0};"),
    ("c-commute-control", "c", "control", "v7[0U] = (v7[0U] + 1U);", "v7[0U] = (1U + v7[0U]);"),
    ("cpp-compare-control", "cpp", "control", "m_data[_a] < m_data[_b]", "m_data[_b] > m_data[_a]"),
)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def command(arguments, log, timeout=60):
    with log.open("w") as output:
        try:
            run = subprocess.run(arguments, stdout=output, stderr=subprocess.STDOUT, timeout=timeout)
            return run.returncode
        except subprocess.TimeoutExpired:
            return "timeout"


def main(arguments):
    if len(arguments) > 1:
        raise ValueError("usage: matrix.py [BUILD_DIRECTORY]")
    build = Path(arguments[0]).resolve() if arguments else ROOT / "build/challenge"
    build.mkdir(parents=True, exist_ok=True)
    oracle = build / "oracle"
    prepare(oracle)
    originals = {"c": (ROOT / "permute.c").read_bytes(),
                 "cpp": (oracle / "solc_permute.inc").read_bytes()}
    printer = ROOT / "build/project/print-permute"
    generated = subprocess.check_output([printer])
    if generated != originals["c"]:
        raise ValueError("current generated C differs from the actual printer output")
    (build / "regenerated-permute.c").write_bytes(generated)
    manifest = []
    for name, language, kind, before, after in VARIANTS:
        source = originals[language].decode()
        if source.count(before) != 1:
            raise ValueError(f"{name}: replacement must match exactly once")
        directory = build / "mutants" / name
        directory.mkdir(parents=True, exist_ok=True)
        path = directory / ("permute.c" if language == "c" else "solc_permute.inc")
        data = source.replace(before, after, 1).encode()
        path.write_bytes(data)
        manifest.append({"id": name, "language": language, "kind": kind,
                         "source": str(path), "sha256": digest(data),
                         "original_sha256": digest(originals[language]),
                         "before": before, "after": after,
                         "source_regeneration": "rejected: bytes differ from canonical generation",
                         "formal_verifier": "not run; no proof claim"})
    (build / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    cc, cxx = shlex.split(os.environ.get("CC", "cc")), shlex.split(os.environ.get("CXX", "c++"))
    flags = ["-O2", "-g", "-fPIC", "-Wall", "-Wextra"]
    core_object, oracle_object = build / "core.o", build / "oracle.o"
    subprocess.run([*cc, "-std=c11", *flags, "-I", str(ROOT), "-c", str(ROOT / "permute.c"),
                    "-o", str(core_object)], check=True)
    subprocess.run([*cxx, "-std=c++20", *flags, "-I", str(oracle), "-c", str(HERE.parent / "oracle.cpp"),
                    "-o", str(oracle_object)], check=True)
    results = []
    all_variants = [{"id": "baseline", "kind": "control"}, *manifest]
    for variant in all_variants:
        name, kind = variant["id"], variant["kind"]
        directory = build / "runs" / name
        directory.mkdir(parents=True, exist_ok=True)
        core, reference = core_object, oracle_object
        compile_status = 0
        if name != "baseline":
            output = directory / "mutant.o"
            if variant["language"] == "c":
                args = [*cc, "-std=c11", *flags, "-I", str(ROOT), "-c", variant["source"], "-o", str(output)]
                core = output
            else:
                args = [*cxx, "-std=c++20", *flags, "-I", str(Path(variant["source"]).parent),
                        "-I", str(oracle), "-c", str(HERE.parent / "oracle.cpp"), "-o", str(output)]
                reference = output
            compile_status = command(args, directory / "compile.log")
        library = directory / "target.so"
        link_status = command([*cxx, "-shared", str(core), str(reference), "-o", str(library)],
                              directory / "link.log") if compile_status == 0 else "not run"
        status = command([sys.executable, str(HERE / "metamorphic.py"), str(library),
                          str(directory / "current-case.json")], directory / "test.log", timeout=30) if link_status == 0 else "not run"
        detected = status == 1 and "challenge failure:" in (directory / "test.log").read_text()
        passed = compile_status == 0 and link_status == 0 and (status == 0 if kind == "control" else detected)
        result = {"id": name, "kind": kind, "compile": compile_status, "link": link_status,
                  "test_exit": status, "test_witness": detected, "expected_result_met": passed,
                  "witness_input": str(directory / "current-case.json"),
                  "test_log": str(directory / "test.log"), "formal_verifier": "not run"}
        results.append(result)
        print(json.dumps(result), flush=True)
    (build / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    if not all(result["expected_result_met"] for result in results):
        raise ValueError("matrix has an undetected variant, failed control, or build failure")


if __name__ == "__main__":
    try:
        main(sys.argv[1:])
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        sys.exit(f"challenge matrix: {error}")
