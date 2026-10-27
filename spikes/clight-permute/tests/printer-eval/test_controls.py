#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Test actual printer changes against the extracted interpreter."""
import os
import json
from contextlib import nullcontext
from pathlib import Path
import subprocess
import tempfile
import unittest

from run import compile_program, compare, execute, inputs, reference, save_result

BUILD = Path(os.environ["PRINTER_EVAL_BUILD"]).resolve()


class PrinterControls(unittest.TestCase):
    def test_baseline_and_printer_mutations(self):
        # These copies use the actual production printer. The interpreter
        # executable and generated ASTs remain unchanged.
        variants = (
            ("baseline", None, None, True),
            ("subtract-as-add", '| Osub -> "-"', '| Osub -> "+"', False),
            ("less-as-greater", '| Olt -> "<"', '| Olt -> ">"', False),
            ("reverse-greater-equal", '| Oge -> ">="', '| Oge -> "<="', False),
            ("equivalent-parentheses", 'line (name id ^ " = " ^ unsigned fn value ^ ";")',
             'line (name id ^ " = (" ^ unsigned fn value ^ ");")', True),
        )
        cases = inputs(99, 8)
        original = (BUILD / "printer.ml").read_text()
        archive = os.environ.get("PRINTER_EVAL_CONTROLS")
        if archive:
            archive = Path(archive).resolve()
            archive.mkdir(parents=True, exist_ok=False)
            (archive / "inputs.txt").write_text("\n".join(c.line() for c in cases) + "\n")
        reports = []
        for name, before, after, expected in variants:
            location = nullcontext(str(archive / name)) if archive else tempfile.TemporaryDirectory()
            with self.subTest(name=name), location as temp:
                directory = Path(temp)
                directory.mkdir(exist_ok=True)
                text = original
                if before:
                    self.assertEqual(text.count(before), 1)
                    text = text.replace(before, after, 1)
                (directory / "printer.ml").write_text(text)
                for file in ("generator.ml", "main.ml"):
                    (directory / file).write_bytes((BUILD / file).read_bytes())
                subprocess.run(["ocamlopt", "-I", str(BUILD), "-o", "printer-eval",
                    str(BUILD / "extracted.cmx"), "printer.ml", "generator.ml", "main.ml"],
                    cwd=directory, check=True, capture_output=True)
                mismatches = []
                details = []
                for seed in range(6):
                    case_dir = directory / f"seed-{seed}"
                    case_dir.mkdir()
                    source = case_dir / "program.c"
                    source.write_bytes(subprocess.check_output(
                        [str(directory / "printer-eval"), "print", str(seed)]))
                    oracle = reference(BUILD, seed, case_dir, cases)
                    self.assertTrue(oracle["pass"], oracle["errors"])
                    binary = compile_program(BUILD, source, case_dir, "gcc", 2)
                    candidate = execute(binary, cases, 5)
                    verdict = compare(oracle, candidate)
                    save_result(case_dir, "reference", oracle)
                    save_result(case_dir, "candidate", candidate)
                    details.append({"seed": seed, **verdict})
                    mismatches.append(not verdict["pass"])
                reports.append({"name": name, "expected_pass": expected,
                    "expected_result_met": (not any(mismatches)) == expected,
                    "cases": details})
                if archive:
                    (archive / "results.json").write_text(json.dumps(reports, indent=2) + "\n")
                self.assertEqual(not any(mismatches), expected)

    def test_missing_fuel_and_bad_length(self):
        for line in ("8 0 " + "0 " * 15 + "0\n", "7 5000\n"):
            result = subprocess.run([str(BUILD / "printer-eval"), "run", "0"],
                input=line, text=True, capture_output=True, timeout=10)
            self.assertTrue(result.returncode != 0 or result.stdout == "INCOMPLETE\n")


if __name__ == "__main__":
    unittest.main()
