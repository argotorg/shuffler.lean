#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check the proof-result acceptance rule."""
import unittest

import verify

MARKER = "Proof succeeded! equivalence"
PARTIAL = "Symbolic simulation completed with side conditions."


class ResultTests(unittest.TestCase):
    def test_complete_proof(self):
        self.assertEqual(verify.classify(0, MARKER, MARKER),
                         ("proved", "complete"))

    def test_partial_proof_is_incomplete(self):
        self.assertEqual(verify.classify(0, PARTIAL + "\n" + MARKER, MARKER),
                         ("incomplete", "partial_execution"))

    def test_missing_success_marker(self):
        self.assertEqual(verify.classify(0, "", MARKER),
                         ("rejected", "proof_failure"))

    def test_failure_exit(self):
        self.assertEqual(verify.classify(2, MARKER, MARKER),
                         ("rejected", "proof_failure"))

    def test_timeout_with_old_success_text(self):
        self.assertEqual(verify.classify("timeout", MARKER, MARKER),
                         ("incomplete", "timeout"))


if __name__ == "__main__":
    unittest.main()
