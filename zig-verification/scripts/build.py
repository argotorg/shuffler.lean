#!/usr/bin/env python3
"""Build source modules in dependency order with one Lean build at a time."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import time
import tomllib

from source_imports import imports


ROOT = Path(__file__).resolve().parents[1]


def positive_seconds(value: str) -> int:
    seconds = int(value)
    if seconds <= 0 or seconds > 600:
        raise argparse.ArgumentTypeError("seconds must be from 1 to 600")
    return seconds


def source(module: str) -> Path | None:
    relative = module.replace(".", "/") + ".lean"
    return next((ROOT / prefix / relative for prefix in
                 [".", "vendor/Kraken", "pkgs/leantools", "vendor/loogle"]
                 if (ROOT / prefix / relative).is_file()), None)


def prerequisites(root: Path) -> dict[str, list[str]]:
    config = root / "lakefile.toml"
    if not config.exists():
        return {}
    data = tomllib.loads(config.read_text())
    libraries = data.get("lean_lib", [])
    executables = data.get("lean_exe", [])
    targets = {lib["name"]: lib.get("roots", [lib["name"]]) for lib in libraries}
    targets.update({exe["name"]: [exe.get("root", exe["name"])] for exe in executables})
    result = {}
    for exe in executables:
        needs = exe.get("needs", [])
        for name in needs:
            if name not in targets:
                raise ValueError(f"unknown prerequisite {name} of {exe['name']}")
        result[exe.get("root", exe["name"])] = [module for name in needs for module in targets[name]]
    return result


def ordered(roots: list[str]) -> list[str]:
    done, active, result = set(), set(), []
    needed = prerequisites(ROOT)

    def visit(module):
        if module in done:
            return
        if module in active:
            raise ValueError(f"import cycle at {module}")
        path = source(module)
        if path is None:
            if module in {"Lean", "Std", "Init", "Lake"} or module.startswith(("Lean.", "Std.", "Init.", "Lake.")):
                return
            raise ValueError(f"missing source module: {module}")
        active.add(module)
        for dependency in needed.get(module, []) + list(imports(path.read_text())):
            visit(dependency)
        active.remove(module)
        done.add(module)
        result.append(module)

    for module in roots:
        visit(module)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="*", default=["Review.Closed"])
    parser.add_argument("--seconds", type=positive_seconds, default=600)
    parser.add_argument("--facet", choices=["olean", "o"], default="olean",
                        help="use o to compile native objects one module at a time")
    args = parser.parse_args()
    environment = dict(os.environ)
    for key in ["LEAN_PATH", "LEAN_SRC_PATH"]:
        environment.pop(key, None)
    environment["LEAN_NUM_THREADS"] = "2"
    logdir = ROOT / "local" / "build"
    logdir.mkdir(parents=True, exist_ok=True)
    modules = ordered(args.modules)
    results = []
    for index, module in enumerate(modules, 1):
        log = logdir / (module + (".o" if args.facet == "o" else "") + ".log")
        started = time.monotonic()
        with log.open("w") as output:
            try:
                result = subprocess.run(["timeout", "-k", "5s", str(args.seconds) + "s",
                                         "lake", "--no-cache", "build", "+" + module + ":" + args.facet],
                                        cwd=ROOT, env=environment, stdout=output,
                                        stderr=subprocess.STDOUT)
                code = result.returncode
            except subprocess.TimeoutExpired:
                code = 124
        results.append({"module": module, "exitCode": code,
                        "seconds": round(time.monotonic() - started, 3)})
        (logdir / "receipt.json").write_text(json.dumps(results, indent=2) + "\n")
        print(f"{index}/{len(modules)} {module}: {code}", flush=True)
        if code:
            print("\n".join(log.read_text().splitlines()[-35:]), flush=True)
            return code
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
