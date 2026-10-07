#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Exercise the version adapter with the actual CVC5 binary."""
from pathlib import Path
import shutil
import subprocess
import unittest
import annotate
import run


class WrapperTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.binary = shutil.which('cvc5')
        if not cls.binary:
            raise RuntimeError('run this test in the Frama-C Nix shell')
        cls.output = annotate.OUT / 'wrapper-tests'
        cls.output.mkdir(parents=True, exist_ok=True)
        cls.wrapper = cls.output / 'cvc5'
        cls.version = subprocess.check_output([cls.binary, '--version'], text=True)
        run.write_cvc5_wrapper(cls.wrapper, cls.binary, cls.version)

    def check_solver(self, name, formula, expected):
        (self.output / (name + '.smt2')).write_text(formula)
        for binary, label in ((self.binary, 'native'), (str(self.wrapper), 'wrapper')):
            result = subprocess.run([binary, '--lang=smt2'], input=formula, text=True,
                                    capture_output=True, check=False)
            (self.output / (name + '-' + label + '.log')).write_text(result.stdout + result.stderr)
            self.assertEqual(result.returncode, 0)
            self.assertEqual(result.stdout.strip(), expected)

    def test_unsat(self):
        self.check_solver('unsat', '(set-logic QF_LIA)\n(assert false)\n(check-sat)\n', 'unsat')

    def test_sat(self):
        self.check_solver('sat', '(set-logic QF_LIA)\n(assert true)\n(check-sat)\n', 'sat')

    def test_version_preserves_number_and_notice(self):
        actual = subprocess.check_output([self.wrapper, '--version'], text=True)
        self.assertEqual(actual, run.why3_cvc5_version(self.version))

    def test_invalid_solver_option_is_not_hidden(self):
        result = subprocess.run([self.wrapper, '--clean-deliberate-invalid-option'],
                                text=True, capture_output=True, check=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertNotIn('This is cvc5 version', result.stdout)


if __name__ == '__main__':
    unittest.main()
