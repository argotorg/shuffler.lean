#!/usr/bin/env python3
"""Check the source boundary between invariant producers and target adapters."""
import json
import re
import sys
from pathlib import Path


def sources(paths):
    for path in paths:
        if not path.exists():
            raise ValueError(f"no such source path: {path}")
        yield from (p for p in path.rglob("*") if p.is_file()) if path.is_dir() else [path]


def check(root, producer_root, paths):
    if not producer_root.is_dir():
        raise ValueError(f"no producer directory: {producer_root}")
    denied = json.loads((root / "leantools.json").read_text())["deny"]
    if not isinstance(denied, list) or not denied or not all(isinstance(p, str) and p for p in denied):
        raise ValueError("leantools.json has no denied source paths")
    denied_paths = {(root / p).resolve() for p in denied}
    names = denied + [p[:-5].replace("/", ".") for p in denied if p.endswith(".lean")]
    facade = (root / "Skel/Discover/Targets.lean").resolve()
    adapter = re.compile(r"\bSkel\.(?:Discover\.Targets\b|Targets\.)")
    bad = False
    for path in sorted(set(sources(paths)) | set(sources([producer_root]))):
        real = path.resolve()
        if any(real == denied or real.is_relative_to(denied) for denied in denied_paths):
            print(f"blind: denied source in scope: {path}", file=sys.stderr)
            bad = True
            continue
        for n, line in enumerate(path.read_text().splitlines(), 1):
            if any(name in line for name in names):
                print(f"{path}:{n}: blind: denied source reference: {line}", file=sys.stderr)
                bad = True
            if real != facade and real.is_relative_to(producer_root.resolve()) and adapter.search(line):
                print(f"{path}:{n}: blind: producer references target adapter: {line}", file=sys.stderr)
                bad = True
    return int(bad)


def main():
    try:
        root, producers, *paths = map(Path, sys.argv[1:])
        return check(root, producers, paths)
    except (OSError, ValueError, KeyError, TypeError, UnicodeError) as error:
        print(f"blind: source boundary error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
