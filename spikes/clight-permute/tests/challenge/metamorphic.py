#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check observable behavior of actual C and solc code loaded from one library."""
import ctypes
import itertools
import json
from pathlib import Path
import random
import sys

if not __debug__:
    sys.exit("challenge failure: Python assertions must remain enabled")

MASK = (1 << 32) - 1
GUARD = 0xD13C7A59
WORD = ctypes.c_uint
POINTER = ctypes.POINTER(WORD)


def buffer(values, size, salt):
    result = (WORD * (size + 4))()
    result[:] = [salt] * size + [GUARD] * 4
    result[:len(values)] = values
    return result


def invoke(function, source, permutation, salt, oracle=False):
    n = len(source)
    data = buffer(source, n, salt)
    p = buffer(permutation, n, salt)
    trace = buffer([], 2 * n, salt)
    out = buffer([], 3, salt)
    target, used = buffer([], n, salt), buffer([], n, salt)
    status = (function(n, data, p, trace, out) if oracle else
              function(n, data, p, target, used, trace, out))
    for name, array, count in (("data", data, n), ("permutation", p, n),
                               ("target", target, n), ("used", used, n),
                               ("trace", trace, 2 * n), ("out", out, 3)):
        assert list(array[count:]) == [GUARD] * 4, f"{name} guard overwritten"
    assert out[0] <= 2 * n, "trace count exceeds capacity"
    assert list(trace[out[0]:2 * n]) == [salt] * (2 * n - out[0]), "unwritten trace tail changed"
    if oracle:
        assert list(p[:n]) == list(permutation), "oracle changed its input permutation"
    return status, tuple(data[:n]), tuple(trace[:out[0]]), tuple(out[:3])


def replay(source, permutation, result):
    status, data, trace, out = result
    n = len(source)
    assert status in (0, 1), "valid input returned a defensive error"
    values = list(source)
    for depth in trace:
        assert 1 <= depth <= 16 and depth < n, "illegal emitted swap depth"
        pos = n - 1 - depth
        values[pos], values[-1] = values[-1], values[pos]
    assert tuple(values) == data, "trace does not reproduce exact final/partial data"
    if status == 0:
        assert out[1:] == (0, 0), "success error fields are not zero"
        assert all(data[permutation[i]] == source[i] for i in range(n)), "wrong success data"
    else:
        pos, excess = out[1:]
        assert pos < n and n - 1 - pos > 16, "blocked position is reachable"
        assert excess == n - 1 - pos - 16, "wrong blocked excess depth"
        assert data[pos] != data[-1], "equal values must not block"


def check_case(core, oracle, source, p):
    original = invoke(core, source, p, 0x12345678)
    reference = invoke(oracle, source, p, 0x12345678, True)
    assert original == reference, "C and solc observable results differ"
    replay(source, p, original)
    for function, is_oracle in ((core, False), (oracle, True)):
        repeated = invoke(function, source, p, 0xA5A5A5A5, is_oracle)
        assert repeated == original, "repeat depends on work-buffer contents"
    # XOR, complement, and multiplication by an odd number followed by addition
    # are bijections of uint32. They preserve equality, but can change ordering.
    renamings = (lambda x: x ^ 0x9E3779B9, lambda x: MASK - x,
                 lambda x: (1664525 * x + 1013904223) & MASK)
    for rename in renamings:
        renamed = [rename(x) for x in source]
        expected = (original[0], tuple(map(rename, original[1])), original[2], original[3])
        for function, is_oracle in ((core, False), (oracle, True)):
            result = invoke(function, renamed, p, 0x31415926, is_oracle)
            assert result == expected, "value renaming changed trace, errors, or data"
            replay(renamed, p, result)


def cases():
    for n in (1, 16, 17, 18, 32, 1024):
        p = list(range(n))
        yield list(range(n)), p
        p = list(p)
        p[0], p[-1] = p[-1], p[0]
        yield list(range(n)), p
        yield [MASK] * n, p
    p, source = list(range(18)), list(range(18))
    p[17], p[16], p[0] = 16, 0, 17
    yield source, p
    p = list(range(18))
    p[16], p[0] = 0, 16
    source[16] = source[17]
    yield source, p
    for n in range(1, 5):
        for p in itertools.permutations(range(n)):
            for values in itertools.product((0, MASK), repeat=n):
                yield values, p
            yield list(range(n)), p
    generator = random.Random(81723)
    for _ in range(200):
        n = generator.randrange(1, 37)
        p = list(range(n))
        generator.shuffle(p)
        yield [generator.randrange(8) for _ in range(n)], p


def rejected(core):
    for n in (0, 1025, MASK):
        out = buffer([], 3, MASK)
        status = core(n, None, None, None, None, None, out)
        assert status == (0 if n == 0 else 2), "wrong empty/oversized return"
        assert list(out[:3]) == [0] * 3 and list(out[3:]) == [GUARD] * 4, "size output contract"
    for p in ([0, 0, 2], [0, 3, 2], [MASK, 1, 2]):
        source = [5, 6, 7]
        # Observe the input permutation too: rejection must leave it unchanged.
        data, destinations = buffer(source, 3, 17), buffer(p, 3, 17)
        target, used, trace, out = buffer([], 3, 17), buffer([], 3, 17), buffer([], 6, 17), buffer([], 3, 17)
        assert core(3, data, destinations, target, used, trace, out) == 2, "invalid permutation accepted"
        assert list(data[:3]) == source and list(destinations[:3]) == p, "rejection changed inputs"
        assert list(out[:3]) == [0, 0, 0], "rejection output fields"
        for array, count in ((data, 3), (destinations, 3), (target, 3), (used, 3), (trace, 6), (out, 3)):
            assert list(array[count:]) == [GUARD] * 4, "rejection changed guard"
        assert list(trace[:6]) == [17] * 6, "rejection wrote trace"


def main(arguments):
    if len(arguments) != 2:
        raise ValueError("usage: metamorphic.py LIBRARY CURRENT_CASE.json")
    library = ctypes.CDLL(arguments[0])
    core, oracle = library.permute, library.solc_permute
    core.argtypes, oracle.argtypes = [WORD] + [POINTER] * 6, [WORD] + [POINTER] * 4
    core.restype = oracle.restype = WORD
    witness = Path(arguments[1])
    witness.write_text(json.dumps({"phase": "empty/invalid API cases"}) + "\n")
    rejected(core)
    count = 0
    for source, p in cases():
        witness.write_text(json.dumps({"n": len(source), "values": list(source), "permutation": list(p)}) + "\n")
        check_case(core, oracle, source, p)
        count += 1
    print(f"metamorphic checks: {count} cases; 10 calls per valid case; rejected API cases")


if __name__ == "__main__":
    try:
        main(sys.argv[1:])
    except (OSError, ValueError, AssertionError) as error:
        sys.exit(f"challenge failure: {error}")
