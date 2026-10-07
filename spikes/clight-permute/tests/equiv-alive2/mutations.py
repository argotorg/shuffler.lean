# SPDX-License-Identifier: GPL-3.0-or-later
"""Run the same KLEE comparison on changed copies of the production sources."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
TEST = HERE.parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output", type=Path, default=TEST.parent / "build/equiv-alive2/klee-mutations")
BUILD = parser.parse_args().output.resolve()
BUILD.mkdir(parents=True, exist_ok=False)
subprocess.run([sys.executable, TEST / "prepare_oracle.py", BUILD / "oracle"], check=True)
core = (TEST.parent / "permute.c").read_text()
solc = (BUILD / "oracle/solc_permute.inc").read_text()

# Each edit acts on the actual generated C or extracted upstream C++ body.
# The two equivalent edits must pass; each faulty edit must yield a KLEE error.
changes = [
    ("c-status", "c", "return 0U;", "return 1U;", False),
    ("c-data-swap", "c", "v2[v11] = v2[v10];", "v2[v11] = v12;", False),
    ("c-trace-depth", "c", "v6[v7[0U]] = v13;", "v6[v7[0U]] = v13 + 1U;", False),
    ("c-trace-count", "c", "v7[0U] = (v7[0U] + 1U);", "v7[0U] = v7[0U];", False),
    ("c-write-outside-output", "c", "v7[2U] = 0U;", "v7[3U] = 0U;", False),
    ("c-signed-overflow", "c", "v7[2U] = 0U;",
     "v7[2U] = 0U; v7[1U] = (unsigned)((int)v2[0U] + 2147483647);", False),
    ("cpp-data", "cpp", "// Equal slots are interchangeable:",
     "m_data[0] ^= 1U;\n\t\t// Equal slots are interchangeable:", False),
    ("cpp-equal-swap", "cpp", "if (m_data[_pos.value] == m_data[top.value])",
     "if (false)", False),
    ("cpp-early-return", "cpp", "if (misplaced == empty)", "if (true)", False),
    ("cpp-early-exit", "cpp", "// Equal slots are interchangeable:",
     "if (m_data[0] == 0U) std::exit(0);\n\t\t// Equal slots are interchangeable:", False),
    ("c-equivalent-zero", "c", "v7[0U] = 0U;", "v7[0U] = 0U + 0U;", True),
    ("cpp-equivalent-loop", "cpp", "while (true)", "for (;;)", True),
]
results = []
for name, language, old, new, equivalent in changes:
    source = core if language == "c" else solc
    if old not in source:
        raise SystemExit(f"mutation source no longer matches: {name}")
    mutant = BUILD / (name + (".c" if language == "c" else ".inc"))
    mutant.write_text(source.replace(old, new))
    output = BUILD / name
    command = [sys.executable, str(HERE / "run-klee.py"), "--sizes", "3",
               "--permutation", "1,0,2", "--output", str(output),
               "--core" if language == "c" else "--solc-permute", str(mutant)]
    with (BUILD / f"{name}.log").open("w") as log:
        process = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
    errors = list(output.glob("n*/proof/*.err"))
    manifest = json.loads((output / "manifest.json").read_text())
    if equivalent:
        accepted = process.returncode == 0 and not errors and all(x["pass"] for x in manifest["cases"])
    elif name == "cpp-early-exit":
        accepted = (process.returncode != 0 and not errors and len(manifest["cases"]) == 1
                    and bool(manifest["cases"][0]["completion"]["invalid_witnesses"]))
    else:
        accepted = process.returncode != 0 and bool(errors)
    result = {"name": name, "equivalent": equivalent, "validated": accepted,
              "errors": [str(x.relative_to(output)) for x in errors]}
    if name == "cpp-early-exit":
        result["completion"] = manifest["cases"][0]["completion"]
    results.append(result)
    (BUILD / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(result), flush=True)
    if not accepted:
        raise SystemExit(f"unexpected mutation result: {name}; inspect {BUILD / (name + '.log')}")
print(f"mutation controls passed: {len(results)}", flush=True)
