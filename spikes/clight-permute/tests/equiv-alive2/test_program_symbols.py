#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Test the symbol boundary and both actual KLEE command-line runners."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from program_symbols import forbidden_symbols

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


class SymbolTests(unittest.TestCase):
    def test_normal_program_symbols(self):
        self.assertEqual(forbidden_symbols("permute\nobserve_core\nmemcpy\n_Znwm\n"), [])

    def test_control_symbols(self):
        names = ["klee_assume", "klee_set_forking", "klee_get_value_i32",
                 "klee_silent_exit", "klee_make_symbolic"]
        self.assertEqual(forbidden_symbols("\n".join(names)), sorted(names))

    def test_names_are_not_substring_matches(self):
        self.assertEqual(forbidden_symbols("my_klee_assume\nnot_klee_assume\n"), [])

    def test_duplicate_names_are_reported_once(self):
        self.assertEqual(forbidden_symbols("klee_assume\nklee_assume\n"), ["klee_assume"])


class RunnerTests(unittest.TestCase):
    def run_variant(self, source, runner="run-klee.py"):
        with tempfile.TemporaryDirectory(prefix="permute-symbol-test-") as temporary:
            directory = Path(temporary)
            core = directory / "permute.c"
            core.write_text(source)
            result = directory / "result"
            command = [sys.executable, str(HERE / runner), "--sizes", "1",
                       "--core", str(core), "--output", str(result), "--max-time", "30s"]
            if runner == "run-klee.py":
                command += ["--permutation", "0"]
            process = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                                     stderr=subprocess.STDOUT)
            path = (result / "n1-0" if runner == "run-klee.py" else result) / "program-symbols.json"
            self.assertTrue(path.is_file(), process.stdout)
            return process.returncode, json.loads(path.read_text()), process.stdout

    def variant(self, defined=False):
        source = (ROOT / "permute.c").read_text()
        anchor = "  v7[2U] = 0U;"
        self.assertEqual(source.count(anchor), 1)
        prefix = ("void klee_assume(unsigned long condition) { (void)condition; }\n"
                  if defined else "#include <klee/klee.h>\n")
        return prefix + source.replace(anchor, anchor +
            "\n  klee_assume(v2[0] != 42U);\n  if (v2[0] == 42U) return 2U;")

    def assert_policy_rejection(self, result):
        code, report, output = result
        self.assertNotEqual(code, 0, output)
        self.assertFalse(report["pass"])
        self.assertIn("klee_assume", [symbol for module in report["modules"]
                                     for symbol in module["forbidden_symbols"]])

    def test_actual_baseline_passes(self):
        code, report, output = self.run_variant((ROOT / "permute.c").read_text())
        self.assertEqual(code, 0, output)
        self.assertTrue(report["pass"])

    def test_assumption_call_is_rejected(self):
        self.assert_policy_rejection(self.run_variant(self.variant()))

    def test_defined_control_function_is_rejected(self):
        self.assert_policy_rejection(self.run_variant(self.variant(defined=True)))

    def test_rejection_runner_uses_same_boundary(self):
        self.assert_policy_rejection(self.run_variant(self.variant(), "run-rejected.py"))


if __name__ == "__main__":
    unittest.main()
