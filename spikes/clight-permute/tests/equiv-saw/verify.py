#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Prove a finite set of permutation cases with symbolic full-width values."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
import time

from fetch_runtime import fetch

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def run(command, log):
    log.write("$ " + repr(list(map(str, command))) + "\n")
    log.flush()
    subprocess.run(list(map(str, command)), check=True, stdout=log,
                   stderr=subprocess.STDOUT)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def classify(code, output, marker):
    if code == "timeout":
        return "incomplete", "timeout"
    if code != 0 or marker not in output:
        return "rejected", "proof_failure"
    # SAW 1.5 accepts Crucible PartialRes after exit(0) on some paths.
    # Its proof then constrains only paths that reach the return value.
    if "Symbolic simulation completed with side conditions." in output:
        return "incomplete", "partial_execution"
    return "proved", "complete"


def order_classes(n):
    return [ranks for ranks in itertools.product(range(n), repeat=n)
            if set(ranks) == set(range(max(ranks) + 1))]


def order_condition(ranks):
    representatives = [ranks.index(rank) for rank in range(max(ranks) + 1)]
    terms = [f"((input @ {a}) < (input @ {b}))"
             for a, b in zip(representatives, representatives[1:])]
    rebuilt = "[" + ", ".join(f"input @ {representatives[r]}" for r in ranks) + "]"
    terms.append(f"({rebuilt} == input)")
    return " && ".join(terms)


def proof(module, n, ranks=None):
    if ranks is None:
        symbolic = f'  input <- llvm_fresh_var "input" (llvm_array {n} (llvm_int 32));\n'
        precondition = ""
    else:
        count = max(ranks) + 1
        symbolic = (f'  values <- llvm_fresh_var "values" (llvm_array {count} (llvm_int 32));\n'
                    + '  let input = {{ [' + ', '.join(f'values @ {r}' for r in ranks)
                    + '] }};\n')
        ordered = ' && '.join(f'((values @ {i}) < (values @ {i+1}))'
                              for i in range(count - 1)) or 'True'
        precondition = f"  llvm_precond {{{{ {ordered} }}}};\n"
    return f'''m <- llvm_load_module "{module}";
let spec = do {{
{symbolic}  input_ptr <- llvm_alloc (llvm_array {n} (llvm_int 32));
  llvm_points_to input_ptr (llvm_term input);
{precondition}  llvm_execute_func [input_ptr];
  llvm_return (llvm_term {{{{ 1 : [32] }}}});
}};
llvm_verify m "equivalence" [] true spec z3;
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--core", type=Path, default=ROOT / "permute.c")
    parser.add_argument("--oracle", type=Path, default=ROOT / "tests/oracle.cpp")
    parser.add_argument("--oracle-includes", type=Path,
                        help="explicit alternative include directory for mutation checks")
    parser.add_argument("--out", type=Path, default=ROOT / "build/equiv-saw/verification")
    parser.add_argument("--max-n", type=int, choices=range(1, 6), default=3)
    parser.add_argument("--permutation",
                        help="one comma-separated permutation instead of all small cases")
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument("--negative-control", action="store_true")
    parser.add_argument("--partition-values", action="store_true",
                        help="split full uint32 inputs by exhaustive orders with ties")
    parser.add_argument("--build-only", action="store_true")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("timeout must be positive")
    if args.permutation:
        p = tuple(map(int, args.permutation.split(",")))
        if not 1 <= len(p) <= 1024 or sorted(p) != list(range(len(p))):
            parser.error("permutation must contain each index exactly once")
        cases = [p]
    else:
        cases = [p for n in range(1, args.max_n + 1)
                 for p in itertools.permutations(range(n))]
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    # A failed build must not leave an earlier run's results available.
    (out / "results.json").write_text("[]\n")
    if args.partition_values and max(map(len, cases)) > 5:
        parser.error("order partitions are supported only through n=5")
    core, oracle = args.core.resolve(), args.oracle.resolve()
    inputs = ROOT / "build/equiv-saw/oracle"
    runtime = fetch(ROOT / "build/equiv-saw/runtime")
    with (out / "build.log").open("w") as log:
        run(["python3", ROOT / "tests/prepare_oracle.py", inputs], log)
        includes = args.oracle_includes.resolve() if args.oracle_includes else inputs
        for tool in ["clang", "saw", "z3", "yices"]:
            run([tool, "--version"], log)
        flags = ["-fno-vectorize", "-fno-slp-vectorize", "-emit-llvm", "-c"]
        run(["clang", "-std=c11", "-O1", *flags, "-I", ROOT,
             core, "-o", out / "core.bc"], log)
        # O0 avoids an aggregate load rejected by SAW at O1. The LLVM pass
        # below lowers llvm.is.constant, which SAW 1.5 does not implement.
        run(["clang++", "-std=c++20", "-O0", "-Xclang", "-disable-O0-optnone",
             *flags, "-I", includes, "-I", ROOT / "tests", oracle,
             "-o", out / "oracle.bc"], log)
        runtime_bc = []
        for source in runtime:
            target = out / (source.stem + ".bc")
            run(["clang++", "-std=c++20", "-O1", *flags,
                 "-Wno-unknown-warning-option", source, "-o", target], log)
            runtime_bc.append(target)
        manifest = {str(p): digest(p) for p in
                    [core, oracle, ROOT / "permute.h", ROOT / "tests/test.h",
                     HERE / "miter.c", HERE / "verify.py", HERE / "fetch_runtime.py",
                     HERE / "shell.nix", *runtime,
                     *sorted(includes.glob("*.inc"))]}
        (out / "source-hashes.json").write_text(json.dumps(manifest, indent=2) + "\n")
        checks = []
        for n in sorted(set(map(len, cases))):
            if args.partition_values:
                conditions = [order_condition(ranks) for ranks in order_classes(n)]
                coverage = (f"prove_print z3 {{{{ \\(input : [{n}][32]) -> or [\n"
                            + ",\n".join(f"({c})" for c in conditions)
                            + '] }};\nprint "Coverage proved!";\n')
                path = out / f"coverage-n{n}.saw"
                path.write_text(coverage)
                checks.append((f"coverage-n{n}", (), path))
        for permutation in cases:
            name = f"n{len(permutation)}-" + "_".join(map(str, permutation))
            target = out / name
            target.mkdir(exist_ok=True)
            control = ["-DNEGATIVE_CONTROL"] if args.negative_control else []
            run(["clang", "-std=c11", "-O1", *flags,
                 f"-DCASE_N={len(permutation)}",
                 "-DCASE_PERMUTATION=" + ",".join(map(str, permutation)),
                 *control, HERE / "miter.c", "-o", target / "miter.bc"], log)
            run(["llvm-link", out / "core.bc", out / "oracle.bc",
                 target / "miter.bc", *runtime_bc, "-o", target / "linked.bc"], log)
            run(["opt", "-passes=lower-constant-intrinsics", target / "linked.bc",
                 "-o", target / "lowered.bc"], log)
            if args.partition_values:
                for ranks in order_classes(len(permutation)):
                    label = "order-" + "_".join(map(str, ranks))
                    path = target / (label + ".saw")
                    path.write_text(proof(target / "lowered.bc", len(permutation), ranks))
                    checks.append((name + "/" + label, permutation, path))
            else:
                path = target / "proof.saw"
                path.write_text(proof(target / "lowered.bc", len(permutation)))
                checks.append((name, permutation, path))
    if args.build_only:
        return 0
    results = []
    for name, permutation, path in checks:
        start = time.monotonic()
        with path.with_suffix(".log").open("w") as log:
            try:
                result = subprocess.run(["saw", str(path)],
                    stdout=log, stderr=subprocess.STDOUT, timeout=args.timeout)
                code = result.returncode
            except subprocess.TimeoutExpired:
                code = "timeout"
        output = path.with_suffix(".log").read_text()
        marker = "Coverage proved!" if name.startswith("coverage-") else "Proof succeeded! equivalence"
        status, reason = classify(code, output, marker)
        row = {"case": name, "permutation": permutation, "status": status, "exit": code,
               "reason": reason, "seconds": round(time.monotonic() - start, 3)}
        results.append(row)
        (out / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps(row), flush=True)
    return 0 if all(row["status"] == "proved" for row in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
