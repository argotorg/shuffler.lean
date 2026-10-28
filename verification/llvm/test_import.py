# SPDX-License-Identifier: GPL-3.0-or-later
import unittest
from import_ast import import_ast

MARKER = "Internal Coq representation of the ast:\n"


class ImportTests(unittest.TestCase):
    def test_term(self):
        self.assertIn('Definition candidate', import_ast(MARKER + '[]'))

    def test_string_repair(self):
        result = import_ast(MARKER + r'[TLE_Comment "a \"quoted\" value"]')
        self.assertIn('"a ""quoted"" value"', result)

    def test_known_constructor_repairs(self):
        result = import_ast(MARKER + '[LOC_Armem; ANN_tail tail]')
        self.assertIn('[LOC_Argmem; ANN_tail Tail]', result)

    def test_bad_input(self):
        for text in ['', '[]', MARKER + 'x', MARKER + '[]' + MARKER,
                     MARKER + '[]. Axiom bad : False. Definition x := []',
                     MARKER + '[ltac:(exact nil)]',
                     MARKER + '[(* injected comment *)]',
                     MARKER + '["unfinished]']:
            with self.subTest(text=text), self.assertRaises(ValueError):
                import_ast(text)


if __name__ == '__main__':
    unittest.main()
