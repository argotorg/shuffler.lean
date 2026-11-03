#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check that proof evidence rejects new assumptions and missing claims."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("check_assumptions", ROOT / "check-assumptions.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class AssumptionTests(unittest.TestCase):
    def check(self, report):
        return checker.check(report, {"Example.claim"})

    def test_closed(self):
        self.assertEqual(self.check("Example.claim\nClosed under the global context\n"),
                         {"Example.claim": frozenset()})

    def test_allowed_axiom(self):
        result = self.check("Example.claim\nAxioms:\nClassical_Prop.classic : forall P, P \\/ ~ P\n")
        self.assertEqual(result["Example.claim"], {"Classical_Prop.classic"})

    def test_current_evidence(self):
        text = (ROOT / "proof-results/assumptions.txt").read_text()
        claims = checker.check(text)
        self.assertIn("ClightCorrect.permute_call_correct", claims)
        self.assertEqual(len(claims), 209)

    def test_admitted_claim(self):
        with self.assertRaises(ValueError):
            self.check("Example.claim\nAxioms:\nExample.claim : True\n")

    def test_new_assumption(self):
        with self.assertRaises(ValueError):
            self.check("Example.claim\nAxioms:\nNew.runtime_contract : True\n")

    def test_truncated_report(self):
        with self.assertRaises(ValueError):
            self.check("Example.claim\n")

    def test_missing_claim(self):
        with self.assertRaises(ValueError):
            self.check("Other.claim\nClosed under the global context\n")

    def test_duplicate_claim(self):
        with self.assertRaises(ValueError):
            self.check("Example.claim\nClosed under the global context\n" * 2)

    def test_empty_axioms(self):
        with self.assertRaises(ValueError):
            self.check("Example.claim\nAxioms:\n")

    def test_unrecognized_line(self):
        with self.assertRaises(ValueError):
            self.check("Example.claim\nSuccessful proof!\n")

    def test_unknown_extra_claim(self):
        with self.assertRaises(ValueError):
            self.check("Example.claim\nClosed under the global context\nOther.claim\nClosed under the global context\n")


KERNEL_REPORT = """
CONTEXT SUMMARY
===============

* Theory: Set is predicative
* Theory: Rewrite rules are not allowed
* Axioms:
    Stdlib.Logic.Classical_Prop.classic
* Constants/Inductives relying on type-in-type: <none>
* Constants/Inductives relying on unsafe (co)fixpoints: <none>
* Inductives whose positivity is assumed: <none>
"""


class KernelAssumptionTests(unittest.TestCase):
    def test_full_axiom_name(self):
        self.assertEqual(checker.check_kernel(KERNEL_REPORT),
                         {"Stdlib.Logic.Classical_Prop.classic"})

    def test_shadowed_axiom(self):
        report = KERNEL_REPORT.replace("Stdlib.Logic.Classical_Prop.classic",
                                       "ClightCorrect.Classical_Prop.classic")
        with self.assertRaises(ValueError):
            checker.check_kernel(report)

    def test_unapproved_axiom(self):
        with self.assertRaises(ValueError):
            checker.check_kernel(KERNEL_REPORT.replace(
                "    Stdlib.Logic.Classical_Prop.classic",
                "    Stdlib.Logic.Classical_Prop.classic\n    ClightCorrect.proof_shortcut"))

    def test_unsafe_flags(self):
        for category in ("type-in-type", "unsafe (co)fixpoints", "positivity is assumed"):
            lines = KERNEL_REPORT.splitlines()
            report = "\n".join(line.replace("<none>", "ClightCorrect.shortcut")
                               if category in line else line for line in lines)
            with self.subTest(category=category), self.assertRaises(ValueError):
                checker.check_kernel(report)

    def test_changed_theory(self):
        for theory in ("Set is predicative", "Rewrite rules are not allowed"):
            with self.subTest(theory=theory), self.assertRaises(ValueError):
                checker.check_kernel(KERNEL_REPORT.replace(theory, "unknown theory"))

    def test_no_axioms(self):
        report = KERNEL_REPORT.replace(
            "* Axioms:\n    Stdlib.Logic.Classical_Prop.classic", "* Axioms: <none>")
        self.assertEqual(checker.check_kernel(report), set())

    def test_empty_axioms(self):
        with self.assertRaises(ValueError):
            checker.check_kernel(KERNEL_REPORT.replace("    Stdlib.Logic.Classical_Prop.classic", ""))

    def test_missing_or_duplicate_section(self):
        for line in KERNEL_REPORT.splitlines():
            if line.strip():
                with self.subTest(line=line), self.assertRaises(ValueError):
                    checker.check_kernel(KERNEL_REPORT.replace(line, ""))
                with self.subTest(duplicate=line), self.assertRaises(ValueError):
                    checker.check_kernel(KERNEL_REPORT.replace(line, line + "\n" + line))

    def test_unrecognized_output(self):
        with self.assertRaises(ValueError):
            checker.check_kernel(KERNEL_REPORT + "Warnings were ignored.\n")


if __name__ == "__main__":
    unittest.main()
