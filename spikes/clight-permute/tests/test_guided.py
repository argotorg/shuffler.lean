#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check the actual byte decoder, C API, and upstream oracle together.

Run in the pinned shell. ASan/UBSan are enabled. On a host without a working
LeakSanitizer runtime, set ASAN_OPTIONS=detect_leaks=0 before running.
"""
import os
from pathlib import Path
import random
import shlex
import struct
import subprocess
import tempfile
import unittest

from prepare_oracle import prepare
from seed_corpus import encode, seeds

HERE = Path(__file__).resolve().parent


class GuidedTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory(prefix="permute-decoder-")
        cls.addClassCleanup(cls.directory.cleanup)
        build = Path(cls.directory.name)
        oracle = Path(os.environ.get("PERMUTE_ORACLE_DIR", HERE.parent / "build/tests/oracle"))
        prepare(oracle)
        cc = shlex.split(os.environ.get("CC", "clang"))
        cxx = shlex.split(os.environ.get("CXX", "clang++"))
        flags = ["-O1", "-g", "-fsanitize=address,undefined",
                 "-fno-sanitize-recover=all", "-fno-omit-frame-pointer"]
        objects = []
        for source in (HERE.parent / "permute.c", HERE / "guided.c",
                       HERE / "check_case.c", HERE / "test_guided.c"):
            output = build / (source.stem + ".o")
            subprocess.run([*cc, "-std=c11", "-pedantic-errors", "-Wall", "-Wextra",
                            "-Wconversion", "-Wsign-conversion", *flags,
                            "-c", str(source), "-o", str(output)], check=True)
            objects.append(str(output))
        output = build / "oracle.o"
        subprocess.run([*cxx, "-std=c++20", *flags, "-I", str(oracle),
                        "-c", str(HERE / "oracle.cpp"), "-o", str(output)], check=True)
        cls.executable = build / "test-guided"
        subprocess.run([*cxx, *flags, *objects, str(output),
                        "-Wl,--wrap=check_case", "-Wl,--wrap=check_rejected",
                        "-o", str(cls.executable)], check=True)

    def decode(self, data):
        run = subprocess.run([self.executable], input=data, capture_output=True)
        self.assertEqual(run.returncode, 0, run.stderr.decode())
        lines = run.stdout.decode().splitlines()
        if not data:
            self.assertEqual(lines, [])
            return None
        self.assertEqual(len(lines), 1, "each nonempty input must run one check")
        route, *numbers = lines[0].split()
        n, *values = map(int, numbers)
        if 0 < n <= 1024:
            self.assertEqual(len(values), 2 * n)
            return route, n, values[:n], values[n:]
        self.assertEqual(values, [])
        return route, n, [], []

    def test_empty_stream_and_every_mode_byte(self):
        self.assertIsNone(self.decode(b""))
        for mode in range(256):
            with self.subTest(mode=mode):
                expected = ("R", 0, [], []) if mode & 3 == 2 else ("V", 1, [0], [0])
                self.assertEqual(self.decode(bytes([mode])), expected)

    def test_size_limits_and_missing_records(self):
        for mode, limit in ((0, 32), (128, 1024)):
            for header in (0, 31, 32, 1023, 1024, 65535):
                with self.subTest(mode=mode, header=header):
                    n = 1 + header % limit
                    self.assertEqual(self.decode(bytes([mode]) + struct.pack("<H", header)),
                                     ("V", n, [0] * n, list(range(1, n)) + [0]))

    def test_empty_and_oversized_api_routes(self):
        for n in (0, 1, 1024, 1025, 0xFFFFFFFF):
            expected = n if n > 1024 else 0
            self.assertEqual(self.decode(bytes([2]) + struct.pack("<I", n)),
                             ("R", expected, [], []))

    def test_raw_destinations_validity_and_unsigned_values(self):
        values = [0, 0xFFFFFFFF, 0x80000000]
        for p in ([2, 0, 1], [0, 0, 2], [0, 3, 2], [0xFFFFFFFF, 1, 2]):
            route = "V" if p == [2, 0, 1] else "R"
            data = bytes([1, 2, 0]) + b"".join(struct.pack("<II", value, dest)
                                              for value, dest in zip(values, p))
            self.assertEqual(self.decode(data), (route, 3, values, p))
        self.assertEqual(self.decode(bytes([1, 2, 0])), ("R", 3, [0] * 3, [0] * 3))

    def test_seed_encoder_round_trip_and_duplicate_mode(self):
        generator = random.Random(73419)
        for n in (*range(1, 33), 1024):
            values = [generator.randrange(1 << 32) for _ in range(n)]
            p = list(range(n))
            generator.shuffle(p)
            data = encode(values, p)
            with self.subTest(n=n):
                self.assertEqual(self.decode(data), ("V", n, values, p))
                duplicate_data = bytes([data[0] | 3]) + data[1:]
                self.assertEqual(self.decode(duplicate_data),
                                 ("V", n, [value % 4 for value in values], p))
                self.assertEqual(self.decode(data + b"ignored trailing bytes"),
                                 ("V", n, values, p))

    def test_truncated_values_and_shuffle_records(self):
        data = encode([0xFFFFFFFF, 0x12345678, 0x80000000], [2, 0, 1])
        for size in range(3, len(data) + 1):
            with self.subTest(size=size):
                route, n, values, p = self.decode(data[:size])
                self.assertEqual((route, n), ("V", 3))
                self.assertEqual(values, [int.from_bytes(data[:size][3 + 6 * i:7 + 6 * i],
                                                         "little") for i in range(3)])
                self.assertEqual(sorted(p), [0, 1, 2])

    def test_every_named_seed_reaches_the_correct_checker(self):
        seen = set()
        for name, data in seeds():
            self.assertNotIn(name, seen)
            seen.add(name)
            expected = "R" if name in {"empty", "oversized", "max-size",
                                      "duplicate-index", "bad-index"} else "V"
            with self.subTest(seed=name):
                self.assertEqual(self.decode(data)[0], expected)

    def test_encoder_rejects_bad_permutations(self):
        for values, p in (([], []), ([0, 1], [0, 0]), ([0], [1]), ([0], [0, 1]),
                          ([0] * 1025, list(range(1025)))):
            with self.subTest(size=len(values)), self.assertRaises(ValueError):
                encode(values, p)


if __name__ == "__main__":
    unittest.main()
