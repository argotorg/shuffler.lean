#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check observed-output faults and equivalent changes in separate source copies."""
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent

# Each replacement must occur exactly once in the actual source.
CASES = [
    ("c_success_status", "core", "        return 0U;", "        return 1U;", False),
    ("c_data_swap", "core", "      v2[v11] = v2[v10];", "      v2[v11] = v12;", False),
    ("c_trace_value", "core", "      v6[v7[0U]] = v13;", "      v6[v7[0U]] = (v13 + 1U);", False),
    ("c_trace_count", "core", "      v7[0U] = (v7[0U] + 1U);", "      v7[0U] = (v7[0U] + 2U);", False),
    ("c_blocked_field", "core", "  v7[1U] = 0U;", "  v7[1U] = 1U;", False),
    ("c_excess_field", "core", "  v7[2U] = 0U;", "  v7[2U] = 1U;", False),
    ("c_depth_limit", "core", "      if (v13 > 16U)", "      if (v13 > 0U)", False),
    ("cpp_status", "oracle", "return blocked ? 1U : 0U;", "return blocked ? 1U : 1U;", False),
    ("cpp_data", "oracle", "    out[0] = static_cast<unsigned>(emission.m_trace.size());", "    data[0] = data[0] + 1U;\n    out[0] = static_cast<unsigned>(emission.m_trace.size());", False),
    ("cpp_trace", "oracle", "trace[i] = static_cast<unsigned>(emission.m_trace[i].depth);", "trace[i] = static_cast<unsigned>(emission.m_trace[i].depth) + 1U;", False),
    ("cpp_blocked_field", "oracle", "blocked ? static_cast<unsigned>(blocked->offset.value) : 0U;", "blocked ? static_cast<unsigned>(blocked->offset.value) : 1U;", False),
    ("cpp_excess_field", "oracle", "blocked ? static_cast<unsigned>(blocked->excess) : 0U;", "blocked ? static_cast<unsigned>(blocked->excess) : 1U;", False),
    ("c_equivalent", "core", "      v13 = (v10 - v11);", "      v13 = ((v10 - v11) + 0U);", True),
    ("cpp_equivalent", "oracle", "trace[i] = static_cast<unsigned>(emission.m_trace[i].depth);", "trace[i] = static_cast<unsigned>(emission.m_trace[i].depth) + 0U;", True),
]


def main():
    out = ROOT / "build/equiv-saw/mutations"
    out.mkdir(parents=True, exist_ok=True)
    sources = {"core": ROOT / "permute.c", "oracle": ROOT / "tests/oracle.cpp"}
    rows = []
    for name, side, before, after, equivalent in CASES:
        source = sources[side]
        text = source.read_text()
        if text.count(before) != 1:
            raise ValueError(f"mutation anchor is not unique: {name}")
        target = out / name
        target.mkdir(exist_ok=True)
        mutant = target / source.name
        mutant.write_text(text.replace(before, after))
        with (target / "driver.log").open("w") as log:
            result = subprocess.run([sys.executable, str(HERE / "verify.py"),
                "--" + side, str(mutant), "--permutation", "1,0", "--timeout", "90",
                "--out", str(target / "proof")], stdout=log, stderr=subprocess.STDOUT)
        results = target / "proof/results.json"
        records = json.loads(results.read_text()) if results.exists() else []
        status = records[0]["status"] if len(records) == 1 else "build_error"
        proof_log = target / "proof/n2-1_0/proof.log"
        counterexample = (proof_log.exists() and
                          "----------Counterexample----------" in proof_log.read_text())
        expected = "proved" if equivalent else "rejected"
        row = {"case": name, "expected": expected, "actual": status,
               "counterexample": counterexample, "exit": result.returncode,
               "matched": status == expected and (equivalent or counterexample)}
        rows.append(row)
        (out / "results.json").write_text(json.dumps(rows, indent=2) + "\n")
        print(json.dumps(row), flush=True)
    return 0 if all(row["matched"] for row in rows) else 1


if __name__ == "__main__":
    raise SystemExit(main())
