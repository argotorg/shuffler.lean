#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
import unittest
import run


class VersionTests(unittest.TestCase):
    def test_current_header(self):
        self.assertEqual(run.why3_cvc5_version('cvc5 1.3.4\nnotice\n'),
                         'This is cvc5 version 1.3.4\nnotice\n')

    def test_unexpected_header_is_rejected(self):
        with self.assertRaises(ValueError):
            run.why3_cvc5_version('unrelated solver 1.3.4\n')

    def test_number_is_not_invented(self):
        self.assertEqual(run.why3_cvc5_version('cvc5 9.8.7\n'),
                         'This is cvc5 version 9.8.7\n')


if __name__ == '__main__':
    unittest.main()
