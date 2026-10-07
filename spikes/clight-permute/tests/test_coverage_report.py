#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Test the raw LLVM branch report, including its failure paths."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("coverage-report.py")
spec = importlib.util.spec_from_file_location("coverage_report", SCRIPT)
report = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = report
spec.loader.exec_module(report)


def branch(line, true=1, false=1, file_id=0):
    return [line, 3, line, 8, true, false, file_id, 0, 4]


def source(path, branches):
    return {"filename": str(path), "branches": branches, "expansions": [],
            "summary": {"branches": {
                "count": 2 * len(branches),
                "covered": sum((row[4] > 0) + (row[5] > 0) for row in branches)}}}


def export(files):
    return {"type": "llvm.coverage.json.export", "version": "3.0.1",
            "data": [{"files": files}]}


class CoverageTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        root = Path(self.directory.name)
        self.core, self.oracle = root / "permute.c", root / "solc_permute.inc"
        self.core.touch()
        self.oracle.touch()
        self.paths = (self.core, self.oracle)
        self.data = export([source(self.core, [branch(10, 4, 0)]),
                            source(self.oracle, [branch(20, 0, 0), branch(30)])])

    def read(self, data=None):
        return report.read_coverage(self.data if data is None else data, self.paths)

    def test_raw_outcomes_include_unvisited_and_unreachable_sides(self):
        core, oracle = self.read()
        self.assertEqual((core.covered, core.total), (1, 2))
        self.assertEqual((oracle.covered, oracle.total), (2, 4))
        text = report.format_coverage((core, oracle))
        self.assertIn("1/2 outcomes (50.00%)", text)
        self.assertIn(f"{self.core}:10:3-10:8 false", text)
        self.assertIn(f"{self.oracle}:20:3-20:8 true", text)
        self.assertIn(f"{self.oracle}:20:3-20:8 false", text)
        self.assertIn("TOTAL LLVM: 3/6 outcomes (50.00%)", text)
        self.assertIn("TOTAL EXPORTED: 3/6 outcomes (50.00%)", text)

    def test_lambdas_count_and_library_and_helper_files_do_not(self):
        self.data["data"][0]["files"] += [
            source(self.core.parent / "helpers.inc", [branch(1, 0, 0)]),
            source(self.core.parent / "range-v3.hpp", [branch(2, 0, 0)]),
            source(self.core.parent / "other/permute.c", [branch(3, 0, 0)])]
        # LLVM file.branches already contains the included lambda's branch.
        self.data["data"][0]["functions"] = [
            {"name": "lambda", "branches": [branch(30)]}]
        self.assertEqual(sum(item.total for item in self.read()), 6)

    def test_macro_branches_count_at_the_selected_call_site(self):
        oracle = self.data["data"][0]["files"][1]
        macro = self.core.parent / "macro.h"
        oracle["expansions"] = [{
            "filenames": [str(self.oracle), str(macro)],
            "source_region": [61, 3, 61, 12, 9, 0, 1, 1],
            "branches": [branch(7, 9, 0, 1), branch(8, 0, 0, 1)]}]
        oracle["summary"]["branches"] = {"count": 8, "covered": 3}
        core, coverage = self.read()
        self.assertEqual((coverage.covered, coverage.total), (3, 8))
        text = report.format_coverage((core, coverage))
        self.assertIn(f"{self.oracle}:61:3-61:12 false", text)
        self.assertIn(f"expanded at {macro}:7:3-7:8", text)

    def test_folded_constant_summary_does_not_replace_raw_counts(self):
        self.data["data"][0]["files"][0]["summary"] = {
            "branches": {"count": 1, "covered": 1, "percent": 100}}
        self.assertEqual((self.read()[0].covered, self.read()[0].total), (1, 2))
        text = report.format_coverage(self.read())
        self.assertIn("LLVM: 1/1 outcomes (100.00%)", text)
        self.assertIn("exported: 1/2 outcomes (50.00%)", text)

    def test_full_coverage(self):
        data = export([source(path, [branch(1)]) for path in self.paths])
        self.assertIn("TOTAL LLVM: 4/4 outcomes (100.00%)",
                      report.format_coverage(self.read(data)))

    def test_missing_empty_or_duplicate_sources_fail(self):
        files = self.data["data"][0]["files"]
        for bad in (export(files[:1]), export([]), export(files + files[:1])):
            with self.subTest(data=bad), self.assertRaises(ValueError):
                self.read(bad)
        with self.assertRaises(ValueError):
            self.read(export([source(path, []) for path in self.paths]))

    def test_missing_branch_or_expansion_data_fails(self):
        for key in ("branches", "expansions"):
            data = copy.deepcopy(self.data)
            del data["data"][0]["files"][0][key]
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.read(data)

    def test_bad_branch_records_fail(self):
        for bad in ([1], branch(0), branch(1, -1), branch(1, True),
                    [1, 8, 1, 3, 1, 1, 0, 0, 4], branch(1)[:-1] + [0]):
            data = copy.deepcopy(self.data)
            data["data"][0]["files"][0]["branches"] = [bad]
            with self.subTest(branch=bad), self.assertRaises(ValueError):
                self.read(data)

    def test_bad_macro_file_index_fails(self):
        self.data["data"][0]["files"][0]["expansions"] = [{
            "filenames": [str(self.core)],
            "source_region": [1, 1, 1, 8, 1, 0, 0, 1],
            "branches": [branch(1, file_id=2)]}]
        with self.assertRaises(ValueError):
            self.read()

    def test_bad_export_format_fails(self):
        for key, value in (("type", "other"), ("version", "2.0.1"),
                           ("data", []), ("data", None)):
            data = copy.deepcopy(self.data)
            data[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.read(data)

    def test_missing_or_inconsistent_summary_fails(self):
        for summary in ({}, {"count": 3, "covered": 1},
                        {"count": 2, "covered": 2}, {"count": 0, "covered": 1},
                        {"count": 2, "covered": -1}, {"count": 2, "covered": True}):
            data = copy.deepcopy(self.data)
            data["data"][0]["files"][0]["summary"]["branches"] = summary
            with self.subTest(summary=summary), self.assertRaises(ValueError):
                self.read(data)
        data = copy.deepcopy(self.data)
        del data["data"][0]["files"][0]["summary"]
        with self.assertRaises(ValueError):
            self.read(data)

    def test_missing_source_file_fails(self):
        self.core.unlink()
        with self.assertRaises(ValueError):
            self.read()

    def test_cli_and_invalid_input_exit(self):
        path = self.core.parent / "export.json"
        path.write_text(json.dumps(self.data))
        command = [sys.executable, str(SCRIPT), str(path), *map(str, self.paths)]
        run = subprocess.run(command, text=True, capture_output=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn("TOTAL LLVM: 3/6", run.stdout)
        path.write_text("{}")
        run = subprocess.run(command, text=True, capture_output=True)
        self.assertNotEqual(run.returncode, 0)
        self.assertNotIn("100.00%", run.stdout)
        self.assertIn("coverage report:", run.stderr)


if __name__ == "__main__":
    unittest.main()
