#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
import unittest
import annotate


class AnnotationTests(unittest.TestCase):
    def test_trace_has_original_contract_and_only_snapshot_ghosts(self):
        source = annotate.SOURCE.read_text()
        trace = annotate.annotate(source, 'trace')
        self.assertEqual(annotate.strip_comments(trace).split(),
                         annotate.strip_comments(source).split())
        self.assertEqual(annotate.requirements(trace),
                         annotate.requirements(annotate.annotate(source, 'safety')))
        for name in ('trace_bounds', 'trace_replay', 'trace_changes_values'):
            self.assertIn('ensures ' + name + ':', trace)
        annotate.check_ghosts(trace, 'trace')
        with self.assertRaisesRegex(ValueError, 'ghost'):
            annotate.check_ghosts(trace.replace('trace_step: ;', 'trace_step: v1--;'), 'trace')

    def test_target_contract_uses_the_same_c_and_input_domain(self):
        source = annotate.SOURCE.read_text()
        target = annotate.annotate(source, 'target')
        safety = annotate.annotate(source, 'safety')
        self.assertEqual(annotate.strip_comments(target).split(),
                         annotate.strip_comments(source).split())
        self.assertEqual(annotate.requirements(target), annotate.requirements(safety))
        self.assertIn('ensures target_definition:', target)
        self.assertIn('ensures target_initialized:', target)
        self.assertNotIn('ensures success_iff:', target)

    def test_safety_and_termination_have_identical_inputs_and_c(self):
        source = annotate.SOURCE.read_text()
        safety = annotate.annotate(source, 'safety')
        termination = annotate.annotate(source, 'termination')
        for result in (safety, termination):
            self.assertEqual(annotate.strip_comments(result).split(),
                             annotate.strip_comments(source).split())
        self.assertEqual(annotate.requirements(safety), annotate.requirements(termination))
        self.assertIn(r'terminates \false;', safety)
        self.assertIn(r'terminates \true;', termination)
        self.assertEqual(termination.count('loop variant'), 7)
        self.assertIn('assert ghost_initial_safe:', termination)
        self.assertIn('assert ghost_step_safe:', termination)
        annotate.check_ghosts(termination)

    def test_ghost_writes_to_real_state_are_rejected(self):
        source = annotate.annotate(annotate.SOURCE.read_text(), 'termination')
        for changed in ('v1--;', 'v3[0] = 0;', 'proof_steps--; v1--;'):
            with self.subTest(changed=changed), self.assertRaisesRegex(ValueError, 'ghost'):
                annotate.check_ghosts(source.replace('proof_steps--;', changed))

    def test_added_input_assumption_is_rejected(self):
        source = annotate.SOURCE.read_text()
        safety = annotate.annotate(source, 'safety')
        termination = annotate.annotate(source, 'termination')
        changed = termination.replace('requires size:', 'requires extra: v1 == 1;\n  requires size:')
        with self.assertRaisesRegex(ValueError, 'input'):
            annotate.check_components(source, safety, changed)

    def test_changed_component_c_is_rejected(self):
        source = annotate.SOURCE.read_text()
        safety = annotate.annotate(source, 'safety')
        termination = annotate.annotate(source, 'termination')
        changed = termination.replace('v3[v10] = v12;', 'v3[v10] = 0U;')
        with self.assertRaisesRegex(ValueError, 'C token'):
            annotate.check_components(source, safety, changed)

    def test_changed_quantified_input_is_rejected(self):
        source = annotate.SOURCE.read_text()
        safety = annotate.annotate(source, 'safety')
        termination = annotate.annotate(source, 'termination')
        changed = termination.replace('==> 0 <= v3[i] < v1)', '==> 0 <= v3[i] < v1-1)', 1)
        with self.assertRaisesRegex(ValueError, 'input'):
            annotate.check_components(source, safety, changed)

    def test_memory_pass_preserves_tokens_and_input_initialization(self):
        source = annotate.SOURCE.read_text()
        result = annotate.annotate(source, 'memory')
        self.assertEqual(annotate.strip_comments(result).split(),
                         annotate.strip_comments(source).split())
        requirements = result.split('  terminates ')[0]
        self.assertEqual(requirements.count('requires data_initialized:'), 1)
        self.assertEqual(requirements.count('requires permutation_initialized:'), 1)
        self.assertNotIn('requires target_initialized:', requirements)
        self.assertEqual(result.count('loop assigns'), 7)
        self.assertNotIn('axiom ', result)
        self.assertNotIn('admit ', result)
        self.assertNotIn('assumes ', result)

    def test_unchanged_c_tokens(self):
        source = annotate.SOURCE.read_text()
        result = annotate.annotate(source)
        self.assertEqual(annotate.strip_comments(result).split(),
                         annotate.strip_comments(source).split())
        self.assertEqual(result.count('loop assigns'), 7)
        self.assertEqual(result.count('loop variant'), 7)
        self.assertIn('ensures success_iff:', result)
        self.assertIn('ensures trace_replay:', result)
        self.assertIn('ensures blocked_info:', result)
        self.assertIn('requires size: 1 <= v1 <= 1024;', result)
        self.assertNotIn('axiom ', result)
        self.assertNotIn('admit ', result)
        self.assertNotIn('assumes ', result)

    def test_changed_function_anchor_is_rejected(self):
        source = annotate.SOURCE.read_text().replace('unsigned int permute(',
                                                    'unsigned int changed(')
        with self.assertRaisesRegex(SystemExit, 'function anchor changed'):
            annotate.annotate(source)

    def test_extra_function_anchor_is_rejected(self):
        source = annotate.SOURCE.read_text() + '\nunsigned int permute('\

        with self.assertRaisesRegex(SystemExit, 'function anchor changed'):
            annotate.annotate(source)

    def test_missing_loop_is_rejected(self):
        source = annotate.SOURCE.read_text().replace('while (1)', 'for (;;)', 1)
        with self.assertRaisesRegex(SystemExit, 'loop count changed'):
            annotate.annotate(source)

    def test_extra_loop_is_rejected(self):
        source = annotate.SOURCE.read_text() + '\nwhile (1) {}'
        with self.assertRaisesRegex(SystemExit, 'loop count changed'):
            annotate.annotate(source)


if __name__ == '__main__':
    unittest.main()
