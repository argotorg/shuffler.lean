#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""The runner must not accept an empty or partial proof report."""
import unittest
import run
import annotate


def goal(identifier, property_name):
    return {'goal': identifier, 'property': property_name, 'function': 'permute',
            'smoke': False, 'passed': True, 'verdict': 'valid', 'proved': 1}


def fixture(mode='full'):
    properties = ['permute_terminates', 'permute_assigns',
                  'permute_assert_rte_mem_access', 'permute_assert_rte_initialization',
                  'permute_loop_invariant_bounds', 'permute_loop_assigns',
                  'permute_loop_variant']
    properties += ['permute_ensures_' + name for name in run.required_postconditions(mode)]
    return [goal('test_' + str(i), p) for i, p in enumerate(properties)]


class ReportTests(unittest.TestCase):
    def test_status_and_success_require_their_postconditions(self):
        for mode in ('status', 'success'):
            with self.subTest(mode=mode):
                source = annotate.annotate(annotate.SOURCE.read_text(), mode)
                properties = run.source_properties(source)
                for name in run.required_postconditions(mode):
                    self.assertIn('permute_ensures_' + name, properties)
                goals = fixture(mode)
                self.assertFalse(run.report_errors(goals, len(goals), mode))
                name = run.required_postconditions(mode)[0]
                partial = [g for g in goals if g['property'] != 'permute_ensures_' + name]
                self.assertTrue(run.report_errors(partial, len(partial), mode))

    def test_composition_lemma_is_a_required_goal(self):
        source = annotate.annotate(annotate.SOURCE.read_text(), 'success')
        self.assertIn('lemma_guarded_success_iff', run.source_properties(source))

    def test_termination_requires_every_lemma_and_loop_variant(self):
        source = annotate.annotate(annotate.SOURCE.read_text(), 'termination')
        properties = run.source_properties(source)
        self.assertEqual(len([p for p in properties if 'lemma_' in p]), 10)
        self.assertIn('check_lemma_moved_frame_all', properties)
        self.assertIn('permute_loop_variant_7', properties)
        self.assertIn('permute_assert_ghost_initial_safe', properties)
        self.assertIn('permute_assert_ghost_step_safe', properties)
        goals = fixture()
        errors = run.report_errors(goals, len(goals), 'termination', source=source)
        self.assertTrue(any('missing properties' in e for e in errors))

    def test_safety_alone_has_no_total_correctness_claim(self):
        goals = [g for g in fixture('safety') if g['property'] != 'permute_terminates']
        self.assertFalse(run.report_errors(goals, len(goals), 'safety'))
        self.assertTrue(run.report_errors(goals, len(goals), 'memory'))

    def test_lemma_obligations_and_tactic_subgoals_are_checked(self):
        goals = fixture()
        lemma = goal('lemma_rank', 'lemma_rank')
        lemma.pop('function')
        lemma.update(subgoals=3, proved=3, tactics=1)
        goals.append(lemma)
        self.assertFalse(run.report_errors(goals, len(goals), 'full',
                                           lemma_names=('rank',)))
        lemma['proved'] = 2
        self.assertTrue(run.report_errors(goals, len(goals), 'full',
                                          lemma_names=('rank',)))

    def test_missing_or_unproved_prerequisite_lemma_is_rejected(self):
        goals = fixture()
        self.assertTrue(run.report_errors(goals, len(goals), 'full',
                                          lemma_names=('rank',)))
        lemma = goal('lemma_rank', 'lemma_rank')
        lemma.pop('function')
        lemma.update(subgoals=3, proved=2, passed=False, verdict='unknown')
        goals.append(lemma)
        self.assertTrue(run.report_errors(goals, len(goals), 'full',
                                          lemma_names=('rank',)))

    def test_unexpected_lemma_is_rejected(self):
        goals = fixture()
        lemma = goal('lemma_extra', 'lemma_extra')
        lemma.pop('function')
        goals.append(lemma)
        self.assertTrue(run.report_errors(goals, len(goals), 'full'))

    def test_complete_fixture(self):
        goals = fixture()
        self.assertFalse(run.report_errors(goals, len(goals), 'full'))

    def test_empty_report_is_rejected(self):
        self.assertTrue(run.report_errors([], 0, 'full'))

    def test_duplicate_goal_is_rejected(self):
        goals = fixture()
        goals[1]['goal'] = goals[0]['goal']
        self.assertTrue(run.report_errors(goals, len(goals), 'full'))

    def test_dropped_goal_is_rejected(self):
        goals = fixture()
        self.assertTrue(run.report_errors(goals[:-1], len(goals), 'full'))

    def test_dropped_semantic_property_is_rejected(self):
        goals = [g for g in fixture() if g['property'] != 'permute_ensures_trace_replay']
        self.assertTrue(run.report_errors(goals, len(goals), 'full'))

    def test_dropped_runtime_checks_are_rejected(self):
        goals = [g for g in fixture() if 'rte_mem_access' not in g['property']]
        self.assertTrue(run.report_errors(goals, len(goals), 'full'))

    def test_valid_without_passed_is_rejected(self):
        goals = fixture()
        goals[0]['passed'] = False
        self.assertTrue(run.report_errors(goals, len(goals), 'full'))

    def test_timeout_is_rejected(self):
        goals = fixture()
        goals[0]['verdict'] = 'timeout'
        self.assertTrue(run.report_errors(goals, len(goals), 'full'))

    def test_smoke_goal_is_not_a_proof(self):
        goals = fixture()
        goals[0]['smoke'] = True
        self.assertTrue(run.report_errors(goals, len(goals), 'full'))

    def test_unexpected_function_is_rejected(self):
        goals = fixture()
        goals[0]['function'] = 'replacement'
        self.assertTrue(run.report_errors(goals, len(goals), 'full'))

    def test_missing_termination_is_rejected(self):
        goals = [g for g in fixture() if g['property'] != 'permute_terminates']
        self.assertTrue(run.report_errors(goals, len(goals), 'full'))

    def test_automatic_termination_is_recorded(self):
        goals = [g for g in fixture() if g['property'] != 'permute_terminates']
        self.assertFalse(run.report_errors(goals, len(goals), 'full', True))


if __name__ == '__main__':
    unittest.main()
