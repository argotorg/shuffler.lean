# SPDX-License-Identifier: GPL-3.0-or-later
"""Composition checks must reject missing or changed contract clauses."""
import unittest
from unittest.mock import patch
import annotate
import composition


class CompositionTests(unittest.TestCase):
    def setUp(self):
        self.original = annotate.SOURCE.read_text()
        self.parts = {mode: annotate.annotate(self.original, mode)
                      for mode in composition.MODES}

    def test_complete_contract_is_covered(self):
        coverage = composition.check(self.original, self.parts)
        self.assertEqual(set(coverage), set(composition.postconditions(annotate.CONTRACT)))

    def test_missing_component_is_rejected(self):
        self.parts.pop('status')
        with self.assertRaisesRegex(ValueError, 'component'):
            composition.check(self.original, self.parts)

    def test_changed_quantified_clause_is_rejected(self):
        self.parts['trace'] = self.parts['trace'].replace(
            'ensures trace_bounds: \\forall integer k; 0 <= k < v7[0]',
            'ensures trace_bounds: \\forall integer k; 0 <= k < v7[0]-1')
        with self.assertRaisesRegex(ValueError, 'postcondition'):
            composition.check(self.original, self.parts)

    def test_changed_definition_is_rejected(self):
        self.parts['trace'] = self.parts['trace'].replace(
            'k <= 0 ? \\at(d[j],Input)', 'k <= 1 ? \\at(d[j],Input)')
        with self.assertRaisesRegex(ValueError, 'definition'):
            composition.check(self.original, self.parts)

    def test_changed_success_direction_is_rejected(self):
        self.parts['success'] = self.parts['success'].replace(
            'ensures blocked_unreachable: \\result == 1 ==>',
            'ensures blocked_unreachable: \\result == 0 ==>')
        with self.assertRaisesRegex(ValueError, 'postcondition'):
            composition.check(self.original, self.parts)

    def test_changed_full_equivalence_is_rejected(self):
        changed = annotate.CONTRACT.replace('ensures success_iff: (\\result == 0)',
                                            'ensures success_iff: (\\result == 1)')
        with patch.object(annotate, 'CONTRACT', changed):
            with self.assertRaisesRegex(ValueError, 'equivalence'):
                composition.check(self.original, self.parts)

    def test_missing_composition_lemma_is_rejected(self):
        self.parts['success'] = self.parts['success'].replace(
            'lemma guarded_success_iff{', 'lemma unrelated{')
        with self.assertRaisesRegex(ValueError, 'composition lemma'):
            composition.check(self.original, self.parts)

    def test_changed_full_input_definition_is_rejected(self):
        changed = annotate.CONTRACT.replace('0 <= p[i] < n)', '0 <= p[i] <= n)', 1)
        with patch.object(annotate, 'CONTRACT', changed):
            with self.assertRaisesRegex(ValueError, 'input'):
                composition.check(self.original, self.parts)

    def test_changed_domain_is_rejected(self):
        self.parts['target'] = self.parts['target'].replace('1 <= v1 <= 1024', '1 <= v1 <= 18')
        with self.assertRaisesRegex(ValueError, 'input'):
            composition.check(self.original, self.parts)

    def test_extra_assumption_is_rejected(self):
        self.parts['success'] = self.parts['success'].replace(
            '  requires size:', '  requires extra: v1 == 1;\n  requires size:')
        with self.assertRaisesRegex(ValueError, 'input'):
            composition.check(self.original, self.parts)

    def test_extra_ghost_write_is_rejected(self):
        self.parts['target'] += '\n/*@ ghost v1--; */\n'
        with self.assertRaisesRegex(ValueError, 'ghost'):
            composition.check(self.original, self.parts)

    def test_unproved_assumption_is_rejected(self):
        self.parts['status'] += '\n/*@ axiomatic False { axiom contradiction: \\false; } */\n'
        with self.assertRaisesRegex(ValueError, 'assumption'):
            composition.check(self.original, self.parts)

    def test_changed_c_is_rejected(self):
        self.parts['success'] = self.parts['success'].replace('return 0U;', 'return 1U;')
        with self.assertRaisesRegex(ValueError, 'C token'):
            composition.check(self.original, self.parts)


if __name__ == '__main__':
    unittest.main()
