#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Write boundary seeds for the documented guided.c byte format."""
from pathlib import Path
import struct
import sys


def encode(values, permutation):
    n = len(values)
    if not 1 <= n <= 1024 or sorted(permutation) != list(range(n)):
        raise ValueError("seed requires a nonempty permutation")
    # Invert the decoder's descending Fisher-Yates construction.
    current = list(range(n))
    choices = list(range(n))
    for i in range(n - 1, 0, -1):
        j = current.index(permutation[i], 0, i + 1)
        choices[i] = j
        current[i], current[j] = current[j], current[i]
    return bytes([128 if n > 32 else 0]) + struct.pack("<H", n - 1) + b"".join(
        struct.pack("<IH", value, choice) for value, choice in zip(values, choices)
    )


def seeds():
    yield "empty", bytes([2, 0, 0, 0, 0])
    yield "oversized", bytes([2]) + struct.pack("<I", 1025)
    yield "max-size", bytes([2]) + struct.pack("<I", 0xFFFFFFFF)
    for n in (1, 2, 5, 16, 17, 18, 32, 1024):
        p = list(range(n))
        yield f"identity-{n}", encode(list(range(n)), p)
        p[0], p[-1] = p[-1], p[0]
        yield f"end-swap-{n}", encode(list(range(n)), p)
        yield f"equal-{n}", encode([0xFFFFFFFF] * n, p)
        yield f"duplicates-{n}", encode([i % 3 for i in range(n)], p)
    p = list(range(18))
    p[17], p[16], p[0] = 16, 0, 17
    yield "block-after-swap", encode(list(range(18)), p)
    p = list(range(18))
    p[16], p[0] = 0, 16
    values = list(range(18))
    values[16] = values[17]
    yield "equal-top", encode(values, p)
    p = list(range(19))
    p[0], p[1] = 1, 0
    yield "block-with-fixed-top", encode(list(range(19)), p)
    for name, p in (("duplicate-index", [0, 0, 2]), ("bad-index", [0, 3, 2])):
        yield name, bytes([1, 2, 0]) + b"".join(
            struct.pack("<II", i + 5, destination) for i, destination in enumerate(p)
        )


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit("usage: seed_corpus.py DIRECTORY")
    root = Path(sys.argv[1])
    root.mkdir(parents=True, exist_ok=True)
    for name, data in seeds():
        (root / name).write_bytes(data)
