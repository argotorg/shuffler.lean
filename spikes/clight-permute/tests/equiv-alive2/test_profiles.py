# SPDX-License-Identifier: GPL-3.0-or-later
"""Check the input-domain parser and names used by the symbolic runner."""
import unittest
from profiles import parse_value_groups, case_name


class Profiles(unittest.TestCase):
    def test_repeated_groups(self):
        self.assertEqual(parse_value_groups("0,1,0,2,1", [5]), (0, 1, 0, 2, 1))

    def test_single_group(self):
        self.assertEqual(parse_value_groups("0,0", [2]), (0, 0))

    def test_reject_invalid_domains(self):
        for text, sizes in [("", [1]), ("0,2", [2]), ("-1,0", [2]),
                            ("0,a", [2]), ("0,1", [3]), ("0,1", [2, 3])]:
            with self.subTest(text=text, sizes=sizes), self.assertRaises(ValueError):
                parse_value_groups(text, sizes)

    def test_name_preserves_small_cases(self):
        self.assertEqual(case_name((1, 0, 2)), "n3-1-0-2")

    def test_large_name_is_bounded_and_distinguishes_permutations(self):
        permutation = tuple(range(1024))
        name = case_name(permutation)
        self.assertLess(len(name), 80)
        self.assertNotEqual(name, case_name(tuple(reversed(permutation))))
        self.assertEqual(name, case_name(permutation))


if __name__ == "__main__":
    unittest.main()
