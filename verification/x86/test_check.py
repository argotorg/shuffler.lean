#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Test the proof checker with omitted files and invalid kernel reports."""
from pathlib import Path
import sys
import tempfile
import unittest

import check
import test_proofs


CONTEXT = '''CONTEXT SUMMARY
===============
* Theory: Set is predicative
* Theory: Rewrite rules are not allowed
* Axioms:
    Stdlib.Logic.Classical_Prop.classic
* Constants/Inductives relying on type-in-type: <none>
* Constants/Inductives relying on unsafe (co)fixpoints: <none>
* Inductives whose positivity is assumed: <none>
'''


class ProofChecks(unittest.TestCase):
    def test_assumption_report_keeps_warnings_separate(self):
        with tempfile.TemporaryDirectory() as temporary:
            work = Path(temporary)
            report = check.command(
                [sys.executable, '-c', 'import sys; print("Claim"); print("Warning", file=sys.stderr)'],
                cwd=work, log=work / 'report.txt', stderr_log=work / 'warnings.txt')
            self.assertEqual(report, 'Claim\n')
            self.assertEqual((work / 'report.txt').read_text(), 'Claim\n')
            self.assertEqual((work / 'warnings.txt').read_text(), 'Warning\n')

    def test_manifest_accepts_exact_files(self):
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary)
            (source / 'X86First.v').write_text('Lemma first : True. Proof. exact I. Qed.\n')
            self.assertEqual(check.source_modules(source, ('X86First',)), ('X86First',))

    def test_manifest_rejects_missing_file(self):
        with tempfile.TemporaryDirectory() as temporary:
            with self.assertRaisesRegex(ValueError, 'module list differs'):
                check.source_modules(Path(temporary), ('X86Missing',))

    def test_manifest_rejects_unlisted_file(self):
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary)
            (source / 'X86Unlisted.v').write_text('')
            with self.assertRaisesRegex(ValueError, 'module list differs'):
                check.source_modules(source, ())

    def test_claims_include_each_named_proof(self):
        text = 'Lemma first : True.\nTheorem second : True.\nExample third : True.\n'
        self.assertEqual(check.declared_claims('X86Sample', text),
                         ('X86.X86Sample.first', 'X86.X86Sample.second', 'X86.X86Sample.third'))

    def test_claims_reject_duplicate_name(self):
        with self.assertRaisesRegex(ValueError, 'duplicate claim'):
            check.declared_claims('X86Sample', 'Lemma same : True.\nLemma same : True.\n')

    def test_claims_reject_empty_module(self):
        with self.assertRaisesRegex(ValueError, 'no named proofs'):
            check.declared_claims('X86Sample', 'Definition sample := 0.\n')

    def test_kernel_accepts_dependency_baseline(self):
        expected = frozenset({'Stdlib.Logic.Classical_Prop.classic'})
        self.assertEqual(check.check_kernel(CONTEXT, expected), expected)

    def test_kernel_rejects_new_axiom(self):
        changed = CONTEXT.replace('* Axioms:', '* Axioms:\n    Unproved.claim')
        with self.assertRaisesRegex(ValueError, 'kernel axioms differ'):
            check.check_kernel(changed, frozenset({'Stdlib.Logic.Classical_Prop.classic'}))

    def test_kernel_rejects_duplicate_axiom(self):
        changed = CONTEXT.replace('* Axioms:', '* Axioms:\n    Stdlib.Logic.Classical_Prop.classic')
        with self.assertRaisesRegex(ValueError, 'duplicate kernel axiom'):
            check.check_kernel(changed, frozenset({'Stdlib.Logic.Classical_Prop.classic'}))

    def test_kernel_rejects_unsafe_modes(self):
        for setting in ('type-in-type', 'unsafe (co)fixpoints'):
            with self.subTest(setting=setting), self.assertRaisesRegex(ValueError, 'unsafe typing'):
                check.check_kernel(CONTEXT.replace(f'{setting}: <none>', f'{setting}: Unproved.claim'),
                                   frozenset({'Stdlib.Logic.Classical_Prop.classic'}))

    def test_kernel_rejects_missing_summary(self):
        with self.assertRaisesRegex(ValueError, 'missing sections'):
            check.check_kernel('', frozenset())

    def test_mutation_rejection_requires_decoding_failure(self):
        report = ('File "./X86Decoded.v", line 65, characters 22-33:\n'
                  'Error:\nUnable to unify the decoded instructions.\n')
        self.assertTrue(test_proofs.rejected_lemma(report, 'X86Decoded', (55, 65)))
        for changed in (report.replace('X86Decoded', 'X86Program'),
                        report.replace('line 65', 'line 66'),
                        report.replace('Unable to unify', 'Missing dependency'),
                        report.replace('Error:', 'Warning:')):
            with self.subTest(report=changed):
                self.assertFalse(test_proofs.rejected_lemma(changed, 'X86Decoded', (55, 65)))


if __name__ == '__main__':
    unittest.main()
