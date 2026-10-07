# SPDX-License-Identifier: GPL-3.0-or-later
"""Read instruction coverage for the three reached implementation functions."""
import json
from pathlib import Path
import sys


def function_coverage(path):
    selected = {"permute": "C permute", "solc_permute": "solc adapter",
                "_ZN12_GLOBAL__N_18Emission7permuteESt6vectorImSaImEE": "solc Emission::permute"}
    hits = {label: {} for label in selected.values()}
    lines = path.read_text().splitlines()
    expected = "events: Icov Forks Ireal Itime I UCdist Rtime States Iuncov Q Qiv Qv Qtime "
    if expected not in lines:
        raise ValueError("unsupported KLEE instruction-counter layout")
    current = None
    call_summary = False
    for line in lines:
        if line.startswith("fn="):
            current = selected.get(line[3:])
        elif line.startswith("calls="):
            call_summary = True
        elif line and line[0].isdigit():
            # The row after calls= attributes a whole callee to the call site.
            # Its Icov count is not coverage of the call instruction itself.
            if call_summary:
                call_summary = False
                continue
            if current:
                columns = line.split()
                if len(columns) != 15 or int(columns[2]) not in (0, 1):
                    raise ValueError("invalid KLEE instruction coverage row")
                instruction, covered = int(columns[0]), int(columns[2])
                hits[current][instruction] = max(hits[current].get(instruction, 0), covered)
    if any(not rows for rows in hits.values()):
        raise ValueError("implementation function missing from KLEE instruction records")
    return {name: {"covered_instructions": sum(rows.values()), "instructions": len(rows)}
            for name, rows in hits.items()}


if __name__ == "__main__":
    for argument in sys.argv[1:]:
        manifest_path = Path(argument)
        manifest = json.loads(manifest_path.read_text())
        for case in manifest["cases"]:
            name = case.get("directory", f"n{case['n']}-" + "-".join(map(str, case["permutation"])))
            case["function_coverage"] = function_coverage(manifest_path.parent / name / "proof/run.istats")
        manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
