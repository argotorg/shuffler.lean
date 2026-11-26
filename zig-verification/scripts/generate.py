#!/usr/bin/env python3
"""Audit all 31 functions in four batches, each bounded to 120 seconds."""

import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def combine(receipts):
    if len(receipts) != 4 or sorted(r["batchIndex"] for r in receipts) != list(range(4)):
        raise ValueError("expected four distinct batches")
    if any(r["batchCount"] != 4 or r["functions"] != 31 or r["statementShapes"] != 31
           or r["paidCalls"] != 0 for r in receipts):
        raise ValueError("batch coverage or paid-call count differs")
    generated = [row for receipt in receipts for row in receipt["generated"]]
    if len(generated) != 31 or len({r["function"] for r in generated}) != 31:
        raise ValueError("expected 31 distinct generated functions")
    return {"functions": 31, "statementShapes": 31, "batches": 4,
            "generated": sorted(generated, key=lambda r: r["function"]), "paidCalls": 0}


def main():
    environment = dict(os.environ)
    for key in ("LEAN_PATH", "LEAN_SRC_PATH"):
        environment.pop(key, None)
    environment["LEAN_NUM_THREADS"] = "2"
    directory = ROOT / "local/generation"
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "receipt.json").unlink(missing_ok=True)
    receipts, graphs = [], []
    for index in range(4):
        with (directory / f"batch-{index}.log").open("w") as output:
            result = subprocess.run(
                ["timeout", "-k", "5s", "120s", "lake", "env", "lean", "--run",
                 "scripts/Generate.lean", str(index), "4"], cwd=ROOT, env=environment,
                stdout=output, stderr=subprocess.STDOUT)
        if result.returncode:
            print(f"batch {index} failed: see local/generation/batch-{index}.log", flush=True)
            return result.returncode
        receipts.append(json.loads((directory / f"batch-{index}/receipt.json").read_text()))
        graphs.append((directory / f"batch-{index}/graph.json").read_bytes())
        print(f"batch {index}/4 passed", flush=True)
    combined = combine(receipts)
    if any(graph != graphs[0] for graph in graphs):
        raise ValueError("batch graphs differ")
    (directory / "receipt.json").write_text(json.dumps(combined, indent=2) + "\n")
    (directory / "graph.json").write_bytes(graphs[0])
    print("31 functions: statement shapes and obligation generation passed; no model calls")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
