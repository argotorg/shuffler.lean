#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check the policy for lost paths and incomplete KLEE statistics."""
from pathlib import Path
import sqlite3
import tempfile
import unittest

from exploration import check_exploration

COUNTERS = ("InhibitedForks", "TerminationEarly", "TerminationSolverError",
            "TerminationProgramError", "TerminationUserError", "TerminationExecutionError")


class ExplorationTests(unittest.TestCase):
    def check_rows(self, rows, log="", counters=COUNTERS):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            with sqlite3.connect(root / "run.stats") as database:
                database.execute("CREATE TABLE stats (" + ",".join(counters) + ")")
                for row in rows:
                    database.execute("INSERT INTO stats VALUES (" + ",".join("?" for _ in counters) + ")", row)
            return check_exploration(root, log)

    def test_no_lost_paths(self):
        self.assertTrue(self.check_rows([(0,) * 6])["pass"])

    def test_each_loss_or_error_counter_rejects(self):
        for index, name in enumerate(COUNTERS):
            with self.subTest(counter=name):
                row = tuple(1 if i == index else 0 for i in range(6))
                self.assertFalse(self.check_rows([row])["pass"])

    def test_earlier_lost_path_cannot_be_hidden_by_last_row(self):
        result = self.check_rows([(1, 0, 0, 0, 0, 0), (0,) * 6])
        self.assertFalse(result["pass"])
        self.assertEqual(result["counters"]["InhibitedForks"], 1)

    def test_warning_rejects_even_with_zero_counters(self):
        result = self.check_rows([(0,) * 6], "KLEE: WARNING ONCE: skipping fork (max-forks reached)\n")
        self.assertFalse(result["pass"])

    def test_missing_file_is_not_created(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.assertFalse(check_exploration(root, "")["pass"])
            self.assertFalse((root / "run.stats").exists())

    def test_empty_statistics_reject(self):
        self.assertFalse(self.check_rows([])["pass"])

    def test_missing_counter_rejects(self):
        self.assertFalse(self.check_rows([(0,) * 5], counters=COUNTERS[:-1])["pass"])

    def test_invalid_counter_rejects(self):
        for value in (-1, None, "zero", 0.5):
            with self.subTest(value=value):
                self.assertFalse(self.check_rows([(value, 0, 0, 0, 0, 0)])["pass"])

    def test_invalid_database_rejects(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "run.stats").write_text("not a statistics database")
            self.assertFalse(check_exploration(root, "")["pass"])


if __name__ == "__main__":
    unittest.main()
