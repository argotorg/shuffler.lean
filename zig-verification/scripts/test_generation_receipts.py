"""Reject incomplete or inconsistent generation audit receipts."""

from copy import deepcopy
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import generate
from generate import combine


def receipts():
    return [{"batchIndex": i, "batchCount": 4, "functions": 31,
             "statementShapes": 31, "paidCalls": 0,
             "generated": [{"function": f"fn{j}"} for j in range(31) if j % 4 == i]}
            for i in range(4)]


class GenerationReceipts(unittest.TestCase):
    def test_failed_run_removes_old_success_receipt(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            receipt = root / "local/generation/receipt.json"
            receipt.parent.mkdir(parents=True)
            receipt.write_text('{"functions":31}')
            with patch.object(generate, "ROOT", root), patch.object(
                    generate.subprocess, "run", return_value=SimpleNamespace(returncode=1)):
                self.assertEqual(generate.main(), 1)
            self.assertFalse(receipt.exists())

    def test_all_functions_are_combined(self):
        self.assertEqual(len(combine(receipts())["generated"]), 31)

    def test_missing_or_repeated_batch_is_rejected(self):
        for bad in [receipts()[:-1], receipts()[:-1] + [receipts()[0]]]:
            with self.assertRaisesRegex(ValueError, "four distinct batches"):
                combine(bad)

    def test_repeated_function_is_rejected(self):
        bad = receipts()
        bad[1]["generated"][0] = deepcopy(bad[0]["generated"][0])
        with self.assertRaisesRegex(ValueError, "31 distinct"):
            combine(bad)

    def test_inconsistent_batch_is_rejected(self):
        for key, value in [("paidCalls", 1), ("functions", 30),
                           ("statementShapes", 30), ("batchCount", 5)]:
            bad = receipts()
            bad[0][key] = value
            with self.assertRaisesRegex(ValueError, "coverage or paid-call"):
                combine(bad)


if __name__ == "__main__":
    unittest.main()
