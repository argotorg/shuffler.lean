#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
import unittest
import annotate


class AnnotationTests(unittest.TestCase):
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
