#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Reject partial executions and stale proof results."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def replace_once(text, before, after):
    if text.count(before) != 1:
        raise ValueError("source anchor is not unique")
    return text.replace(before, after)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    cases = [("baseline", [], "proved", "complete")]

    core = (ROOT / "permute.c").read_text()
    core = replace_once(core, "  v7[0U] = 0U;",
                        "  if (v2[0] == 0U) exit(0);\n  v7[0U] = 0U;")
    mutant = out / "permute.c"
    mutant.write_text("#include <stdlib.h>\n" + core)
    cases.append(("c_exit", ["--core", str(mutant)],
                  "incomplete", "partial_execution"))

    includes = out / "oracle-includes"
    subprocess.run([sys.executable, str(ROOT / "tests/prepare_oracle.py"),
                    str(includes)], check=True)
    body = includes / "solc_permute.inc"
    anchor = "permute(std::vector<std::size_t> _permutation)\n\t{"
    body.write_text(replace_once(body.read_text(), anchor,
        anchor + "\n\t\tif (m_data[0] == 0U) std::exit(0);"))
    oracle = out / "oracle.cpp"
    oracle.write_text("#include <cstdlib>\n" + (ROOT / "tests/oracle.cpp").read_text())
    cases.append(("cpp_exit", ["--oracle", str(oracle),
                  "--oracle-includes", str(includes)],
                  "incomplete", "partial_execution"))

    rows = []
    for name, flags, status, reason in cases:
        target = out / name
        target.mkdir(exist_ok=True)
        with (target / "driver.log").open("w") as log:
            process = subprocess.run([sys.executable, str(HERE / "verify.py"),
                "--permutation", "1,0", "--timeout", "90", "--out", str(target),
                *flags], stdout=log, stderr=subprocess.STDOUT)
        records = json.loads((target / "results.json").read_text())
        matched = (len(records) == 1 and records[0]["status"] == status
                   and records[0]["reason"] == reason
                   and process.returncode == (0 if status == "proved" else 1))
        rows.append({"case": name, "matched": matched, "results": records})
        print(json.dumps(rows[-1]), flush=True)

    target = out / "stale"
    target.mkdir(exist_ok=True)
    (target / "results.json").write_text('[{"status":"proved"}]\n')
    with (target / "driver.log").open("w") as log:
        process = subprocess.run([sys.executable, str(HERE / "verify.py"),
            "--permutation", "1,0", "--core", str(target / "missing.c"),
            "--out", str(target)], stdout=log, stderr=subprocess.STDOUT)
    records = json.loads((target / "results.json").read_text())
    rows.append({"case": "stale_result", "matched": process.returncode != 0 and records == []})
    print(json.dumps(rows[-1]), flush=True)
    (out / "results.json").write_text(json.dumps(rows, indent=2) + "\n")
    return 0 if all(row["matched"] for row in rows) else 1


if __name__ == "__main__":
    raise SystemExit(main())
