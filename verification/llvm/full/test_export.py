#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Test the printed module against the generated Clight C, including buffer guards."""
import ctypes
import itertools
from pathlib import Path
import random
import subprocess
import sys
import tempfile

WORD = ctypes.c_uint32
POINTER = ctypes.POINTER(WORD)
GUARD = 0xDEADBEEF
SALT = 0xA57C913E


def command(*args):
    subprocess.run(args, check=True)


def load(path):
    library = ctypes.CDLL(str(path))
    function = library.permute
    function.argtypes = [WORD] + [POINTER] * 6
    function.restype = WORD
    return function


def cases():
    # Empty and oversized calls must not read the five input/scratch pointers.
    for size in (0, 1025, 0xFFFFFFFF):
        yield size, (), (), 0 if size == 0 else 2
    for size in range(1, 6):
        for permutation in itertools.permutations(range(size)):
            for values in (tuple(range(size)), (0xFFFFFFFF,) * size,
                           tuple((0, 0x80000000, 0xFFFFFFFF)[i % 3]
                                 for i in range(size))):
                yield size, values, permutation, 0
    for size in (16, 17, 18, 19, 32, 1024):
        identity = tuple(range(size))
        yield size, identity, identity, 0
        swap_ends = (size - 1, *range(1, size - 1), 0)
        yield size, identity, swap_ends, 0 if size <= 17 else 1
        yield size, (7,) * size, swap_ends, 0
    # A completed swap followed by a blocked swap.
    permutation = list(range(18))
    permutation[17], permutation[16], permutation[0] = 16, 0, 17
    yield 18, tuple(range(18)), tuple(permutation), 1
    generator = random.Random(73419)
    for _ in range(512):
        size = generator.choice((*range(1, 41), 1024))
        permutation = list(range(size))
        generator.shuffle(permutation)
        values = tuple(generator.choice((0, 1, 0x7FFFFFFF, 0x80000000,
                                         0xFFFFFFFF, generator.getrandbits(32)))
                       for _ in range(size))
        yield size, values, tuple(permutation), None
    # These native regression cases are outside the typed-permutation theorem.
    for permutation in ((0, 0, 2), (0, 1, 3), (0, 1, 0xFFFFFFFF)):
        yield 3, (5, 6, 7), permutation, 2


def execute(function, case):
    size, values, permutation, expected = case
    early = size == 0 or size > 1024
    lengths = (0, 0, 0, 0, 0, 3) if early else (size,) * 4 + (2 * size, 3)
    initial = (values, permutation, (), (), (), ())
    buffers = tuple((WORD * (length + 2))(
        GUARD, *(tuple(data) + (SALT,) * (length - len(data))), GUARD)
        for length, data in zip(lengths, initial))
    pointers = tuple(None if early and i < 5 else
                     ctypes.cast(ctypes.byref(buffer, ctypes.sizeof(WORD)), POINTER)
                     for i, buffer in enumerate(buffers))
    status = function(size, *pointers)
    for i, buffer in enumerate(buffers):
        if buffer[0] != GUARD or buffer[-1] != GUARD:
            raise AssertionError(f'buffer {i} guard changed for {case}')
    if expected is not None and status != expected:
        raise AssertionError(f'expected status {expected}, got {status} for {case}')
    result = tuple(tuple(buffer[1:-1]) for buffer in buffers)
    written = result[-1][0]
    if written > lengths[4] or result[4][written:] != (SALT,) * (lengths[4] - written):
        raise AssertionError(f'unwritten trace changed for {case}')
    return status, result


def compare(reference, actual, inputs):
    statuses = set()
    blocked_after_swap = False
    for case in inputs:
        expected = execute(reference, case)
        result = execute(actual, case)
        if result != expected:
            raise AssertionError(f'printed LLVM differs from generated C for {case}')
        statuses.add(result[0])
        blocked_after_swap |= result[0] == 1 and result[1][-1][0] > 0
    if statuses != {0, 1, 2}:
        raise AssertionError(f'missing return branch: {statuses}')
    if not blocked_after_swap:
        raise AssertionError('no test blocks after a completed swap')


def main(project, source):
    with tempfile.TemporaryDirectory(prefix='export-', dir=project) as temporary:
        build = Path(temporary)
        reference = build / 'reference.so'
        actual = build / 'actual.so'
        command('clang', '-std=c11', '-O0', '-U_FORTIFY_SOURCE', '-fPIC', '-shared', str(source),
                '-o', str(reference))
        command('clang', '-shared', str(project / 'permute.proved.o'), '-o', str(actual))
        inputs = tuple(cases())
        compare(load(reference), load(actual), inputs)
        print(f'Printed LLVM object: {len(inputs)} cases pass; all six buffers agree')

        # Check that this harness rejects a change to the actual printed module.
        llvm = (project / 'permute.proved.ll').read_text()
        before = 'ret i32 %retval.0'
        if llvm.count(before) != 1:
            raise AssertionError('expected one return in the printed module')
        changed = build / 'changed.ll'
        changed.write_text(llvm.replace(before, 'ret i32 0'))
        command('llvm-as', str(changed), '-o', str(build / 'changed.bc'))
        command('clang', '-Wno-unused-command-line-argument', '-O2', '-fPIC', '-shared', str(changed),
                '-o', str(build / 'changed.so'))
        try:
            compare(load(reference), load(build / 'changed.so'), inputs)
        except AssertionError as error:
            if 'expected status 2, got 0' not in str(error):
                raise
        else:
            raise AssertionError('native comparison accepted a changed return value')
        print('Printed LLVM with a changed return value fails the native comparison')


if __name__ == '__main__':
    if len(sys.argv) != 3:
        sys.exit('usage: test_export.py BUILD_DIRECTORY GENERATED_PERMUTE_C')
    main(Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve())
