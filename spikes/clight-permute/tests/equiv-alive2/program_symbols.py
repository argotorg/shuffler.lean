# SPDX-License-Identifier: GPL-3.0-or-later
"""Keep KLEE control functions out of the program modules under comparison."""
import hashlib
import json
import subprocess


def forbidden_symbols(symbols):
    # llvm-nm -j prints one symbol name per line, for both definitions and
    # references. Only the separate trusted drivers may use the KLEE API.
    return sorted({line.strip() for line in symbols.splitlines()
                   if line.strip().startswith("klee_")})


def check_modules(modules, report):
    records = []
    for module in modules:
        symbols = report.parent / (module.stem + "-symbols.txt")
        with symbols.open("w") as output:
            subprocess.run(["llvm-nm", "-j", str(module)], check=True,
                           text=True, stdout=output, stderr=subprocess.PIPE)
        records.append({"module": str(module),
                        "sha256": hashlib.sha256(module.read_bytes()).hexdigest(),
                        "forbidden_symbols": forbidden_symbols(symbols.read_text())})
    result = {"pass": all(not record["forbidden_symbols"] for record in records),
              "modules": records}
    report.write_text(json.dumps(result, indent=2) + "\n")
    return result
