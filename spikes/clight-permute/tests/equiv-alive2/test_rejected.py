#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Exercise the symbolic rejection checker with actual production C copies."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
CORE = HERE.parents[1] / "permute.c"


class RejectionTests(unittest.TestCase):
    def run_case(self, source=None, sizes="2"):
        with tempfile.TemporaryDirectory(prefix="permute-rejection-test-") as temporary:
            root = Path(temporary)
            command = [sys.executable, str(HERE / "run-rejected.py"),
                       "--sizes", sizes, "--max-time", "30s",
                       "--output", str(root / "result")]
            if source is not None:
                mutant = root / "permute.c"
                mutant.write_text(source)
                command += ["--core", str(mutant)]
            process = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                                     stderr=subprocess.STDOUT)
            manifest = root / "result/manifest.json"
            self.assertTrue(manifest.is_file(), process.stdout)
            result = json.loads(manifest.read_text())
            self.assertEqual(len(result["cases"]), len(sizes.split(",")))
            return process.returncode, result["cases"]

    def changed(self, before, after):
        source = CORE.read_text()
        self.assertEqual(source.count(before), 1)
        return source.replace(before, after)

    def test_actual_c_rejects_symbolic_inputs(self):
        code, cases = self.run_case(sizes="0,1,2,3")
        self.assertEqual(code, 0)
        self.assertTrue(all(case["pass"] for case in cases))
        self.assertTrue(all(case["completion"]["pass"] for case in cases))

    def test_wrong_rejection_status_has_assertion_witness(self):
        source = self.changed("if (v9 >= v1) {\n      return 2U;",
                              "if (v9 >= v1) {\n      return 0U;")
        code, cases = self.run_case(source)
        self.assertNotEqual(code, 0)
        self.assertTrue(any(name.endswith(".assert.err") for name in cases[0]["errors"]))

    def test_changed_data_has_assertion_witness(self):
        source = self.changed("if (v9 >= v1) {\n      return 2U;",
                              "if (v9 >= v1) {\n      v2[0] ^= 1U; return 2U;")
        code, cases = self.run_case(source)
        self.assertNotEqual(code, 0)
        self.assertTrue(any(name.endswith(".assert.err") for name in cases[0]["errors"]))

    def test_out_of_range_index_has_memory_witness(self):
        source = self.changed("if (v9 >= v1)", "if (v9 > v1)")
        code, cases = self.run_case(source)
        self.assertNotEqual(code, 0)
        self.assertTrue(any(name.endswith(".ptr.err") for name in cases[0]["errors"]))

    def test_oversized_call_cannot_access_null_arrays(self):
        source = self.changed("if (v1 > 1024U)", "if (v1 > 1025U)")
        code, cases = self.run_case(source, sizes="0")
        self.assertNotEqual(code, 0)
        self.assertTrue(any(name.endswith(".ptr.err") for name in cases[0]["errors"]))

    def test_changed_permutation_has_assertion_witness(self):
        source = self.changed("if (v5[v9] != 0U) {\n      return 2U;",
                              "if (v5[v9] != 0U) {\n      v3[0] ^= 1U; return 2U;")
        code, cases = self.run_case(source)
        self.assertNotEqual(code, 0)
        self.assertTrue(any(name.endswith(".assert.err") for name in cases[0]["errors"]))

    def test_missing_output_write_has_assertion_witness(self):
        source = self.changed("  v7[2U] = 0U;", "  /* omitted output write */")
        code, cases = self.run_case(source, sizes="0")
        self.assertNotEqual(code, 0)
        self.assertTrue(any(name.endswith(".assert.err") for name in cases[0]["errors"]))

    def test_early_exit_lacks_completion_marker(self):
        source = "#include <stdlib.h>\n" + self.changed(
            "  v7[0U] = 0U;", "  if (v2[0] == 0U) exit(0);\n  v7[0U] = 0U;")
        code, cases = self.run_case(source)
        self.assertNotEqual(code, 0)
        self.assertFalse(cases[0]["errors"])
        self.assertTrue(cases[0]["completion"]["invalid_witnesses"])

    def test_equivalent_change_passes(self):
        source = self.changed("  v7[0U] = 0U;", "  v7[0U] = 0U + 0U;")
        code, cases = self.run_case(source)
        self.assertEqual(code, 0)
        self.assertTrue(cases[0]["pass"])


if __name__ == "__main__":
    unittest.main()
