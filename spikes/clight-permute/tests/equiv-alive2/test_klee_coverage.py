# SPDX-License-Identifier: GPL-3.0-or-later
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from klee_coverage import function_coverage


class CoverageTests(unittest.TestCase):
    def check_text(self, text):
        with TemporaryDirectory() as directory:
            path = Path(directory) / "run.istats"
            path.write_text(text)
            return function_coverage(path)

    def fixture(self):
        text = "events: Icov Forks Ireal Itime I UCdist Rtime States Iuncov Q Qiv Qv Qtime \n"
        for name in ["permute", "solc_permute", "_ZN12_GLOBAL__N_18Emission7permuteESt6vectorImSaImEE"]:
            text += f"fn={name}\n"
            text += "2317 77 1 0 0 0 12 6566 0 0 0 0 0 0 0\n"
            text += "cfn=callee\ncalls=12 2438 59\n"
            text += "2317 77 834 0 0 0 47304 0 0 0 0 24048 0 0 0\n"
            text += "2318 77 0 0 0 0 0 1 0 0 1 0 0 0 0\n"
        return text

    def test_call_arc_is_not_an_instruction(self):
        for counts in self.check_text(self.fixture()).values():
            self.assertEqual(counts, {"covered_instructions": 1, "instructions": 2})

    def test_rejects_wrong_counter_layout(self):
        with self.assertRaises(ValueError):
            self.check_text(self.fixture().replace("events: Icov", "events: I"))

    def test_rejects_missing_function(self):
        with self.assertRaises(ValueError):
            self.check_text(self.fixture().replace("fn=permute\n", "fn=other\n"))

    def test_rejects_nonboolean_instruction_coverage(self):
        with self.assertRaises(ValueError):
            self.check_text(self.fixture().replace("2318 77 0", "2318 77 9"))


if __name__ == "__main__":
    unittest.main()
