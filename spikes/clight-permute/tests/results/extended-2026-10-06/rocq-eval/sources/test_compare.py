#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Exercise the real interpreter, C adapter, and changed production sources."""
import importlib.util
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from compare import Case, compare, controls, execute

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BUILD = Path(os.environ["ROCQ_EVAL_BUILD"]).resolve()


class ComparisonTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cases = controls()
        cls.reference = execute(BUILD / "rocq-eval", cls.cases, 300)
        if not cls.reference["pass"]:
            raise AssertionError(cls.reference["errors"])

    def test_independent_expected_records(self):
        expected = [
            (0, 0, 0, 0), (2, 0, 0, 0), (2, 0, 0, 0),
            (0, 0, 0, 0, 4294967295, 0),
            (0, 1, 0, 0, 20, 10, 0, 1, 1),
            (0, 0, 0, 0, 4294967295, 4294967295, 0, 1),
            (2, 0, 0, 0, 10, 20, 0, 0),
            (2, 0, 0, 0, 10, 20, 0, 4294967295),
            (0, 2, 0, 0, 30, 10, 20, 0, 1, 2, 2, 1),
        ]
        self.assertEqual(self.reference["records"][:9], expected)
        self.assertEqual(self.reference["records"][9][:4], (0, 1, 0, 0))
        self.assertEqual(self.reference["records"][10][:4], (1, 0, 0, 1))
        self.assertEqual(self.reference["records"][11][:4], (1, 1, 0, 1))
        self.assertEqual(self.reference["records"][11][-1], 16)
        self.assertEqual(self.reference["records"][12][:4], (0, 0, 0, 0))
        self.assertEqual(self.reference["records"][13][:4], (1, 0, 0, 1))

    def test_six_actual_c_builds(self):
        binaries = sorted(BUILD.glob("native-*-O?"))
        self.assertEqual(len(binaries), 6)
        for binary in binaries:
            with self.subTest(binary=binary.name):
                candidate = execute(binary, self.cases, 30)
                self.assertTrue(compare(self.reference, candidate)["pass"])

    def test_fuel_exhaustion_is_failure(self):
        result = execute(BUILD / "rocq-eval", [Case(0, fuel=0)], 10)
        self.assertFalse(result["pass"])
        self.assertIn("INCOMPLETE", result["stdout"])
        self.assertFalse(compare(result, result)["pass"])

    def test_different_record_counts_are_not_equal(self):
        candidate = execute(BUILD / "native-gcc-O2", self.cases[:1], 10)
        self.assertTrue(candidate["pass"])
        self.assertFalse(compare(self.reference, candidate)["pass"])

    def test_malformed_protocol_is_failure(self):
        for line in ("2 100 1 2 0\n", "1 100 4294967296 0\n", "0 100 7\n"):
            with self.subTest(line=line):
                result = subprocess.run([str(BUILD / "rocq-eval")], input=line,
                    text=True, capture_output=True, timeout=10)
                self.assertNotEqual(result.returncode, 0)

    def test_case_domain(self):
        for args in ((-1,), (1, (), ()), (0, (7,), (0,)),
                     (1, (-1,), (0,)), (1, (2**32,), (0,))):
            with self.subTest(args=args), self.assertRaises(ValueError):
                Case(*args)

    def test_actual_c_mutations(self):
        spec = importlib.util.spec_from_file_location("matrix", HERE.parent / "challenge/matrix.py")
        matrix = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(matrix)
        variants = [v for v in matrix.VARIANTS if v[1] == "c"]
        original = (ROOT / "permute.c").read_text()
        for name, _, kind, before, after in variants:
            with self.subTest(name=name), tempfile.TemporaryDirectory() as temp:
                directory = Path(temp)
                source = directory / "permute.c"
                self.assertEqual(original.count(before), 1)
                source.write_text(original.replace(before, after, 1))
                binary = directory / "native"
                subprocess.run(["gcc", "-std=c11", "-O2", "-I", str(ROOT),
                    str(HERE / "native.c"), str(source), "-o", str(binary)],
                    check=True, capture_output=True)
                candidate = execute(binary, self.cases, 30)
                verdict = compare(self.reference, candidate)
                self.assertEqual(verdict["pass"], kind == "control", verdict)

    def test_actual_c_early_exit_and_timeout(self):
        original = (ROOT / "permute.c").read_text()
        marker = "  unsigned int v13;"
        self.assertEqual(original.count(marker), 1)
        for change in ("exit(0);", "while (1) {}"):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as temp:
                directory = Path(temp)
                source = directory / "permute.c"
                source.write_text("#include <stdlib.h>\n" +
                    original.replace(marker, marker + "\n  " + change, 1))
                binary = directory / "native"
                subprocess.run(["gcc", "-std=c11", "-O2", "-I", str(ROOT),
                    str(HERE / "native.c"), str(source), "-o", str(binary)],
                    check=True, capture_output=True)
                candidate = execute(binary, [Case(0)], 0.2)
                self.assertFalse(candidate["pass"])
                self.assertFalse(compare(self.reference, candidate)["pass"])
                if change.startswith("while"):
                    self.assertEqual(candidate["exit"], "timeout")


if __name__ == "__main__":
    unittest.main()
