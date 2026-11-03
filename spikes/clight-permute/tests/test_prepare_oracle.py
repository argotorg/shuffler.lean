#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check that local source corruption cannot silently change the oracle."""
from pathlib import Path
import sys
import tempfile

from prepare_oracle import FILES, checked_source, definition

cache = Path(sys.argv[1])
with tempfile.TemporaryDirectory(prefix="permute-oracle-negative-") as temporary:
    directory = Path(temporary)
    for name in FILES:
        original = (cache / name).read_bytes()
        (directory / name).write_bytes(original)
        assert checked_source(directory, name).encode("utf-8") == original
        (directory / name).write_bytes(original + b"\n")
        try:
            checked_source(directory, name)
        except ValueError as error:
            assert "cached hash mismatch" in str(error)
        else:
            raise AssertionError(f"source corruption accepted: {name}")
for text in ("", "int f() {} int f() {}"):
    try:
        definition(text, "int f()")
    except ValueError:
        pass
    else:
        raise AssertionError("absent or repeated signature accepted")
assert definition("int f() { if (1) { } }\n", "int f()") == "int f() { if (1) { } }\n"
print("oracle checks: three modified sources and invalid selectors rejected")
