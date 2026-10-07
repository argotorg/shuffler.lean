#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""The runner must not accept an empty or partial proof report."""
import unittest
import run


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
