#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check that the code generation probe rejects incomplete evidence."""
import unittest

from probe_codegen import parse_instructions, parse_decodes


class ProbeTests(unittest.TestCase):
    def setUp(self):
        self.instructions = parse_instructions(
            bytes.fromhex('55 c3'), ' 0: 55 push rbp\n 1: c3 ret\n')

    def test_complete_byte_coverage(self):
        self.assertEqual(tuple(i.offset for i in self.instructions), (0, 1))
        self.assertEqual(tuple(i.encoding for i in self.instructions), (b'\x55', b'\xc3'))

    def test_incomplete_or_changed_bytes(self):
        for code, listing in (
            (b'', ''),
            (b'\x55\xc3', '0: 55 push rbp\n'),
            (b'\x55\xc3', '1: 55 push rbp\n2: c3 ret\n'),
            (b'\x55\xc3', '0: 56 push rsi\n1: c3 ret\n'),
            (b'\x55\xc3', '0: 55 push rbp\n0: c3 ret\n'),
        ):
            with self.subTest(code=code, listing=listing), self.assertRaises(ValueError):
                parse_instructions(code, listing)

    def test_decoded_kind_and_length(self):
        output = ('CHECK_0\nResult = Some((0x100001, PUSH((64, rmi_REG(REG_NORMAL(5))))))\n'
                  'CHECK_1\nResult = Some((0x100002, RET(())))\n')
        self.assertEqual([r['status'] for r in parse_decodes(self.instructions, output)],
                         ['accepted', 'accepted'])

    def test_none_and_interpreter_error(self):
        output = ('CHECK_0\nResult = None(())\n'
                  'CHECK_1\nError: Assertion failed: unsupported instruction\n')
        self.assertEqual([r['status'] for r in parse_decodes(self.instructions, output)],
                         ['rejected', 'error'])

    def test_wrong_length_and_kind_are_not_accepted(self):
        output = ('CHECK_0\nResult = Some((0x100002, PUSH(())))\n'
                  'CHECK_1\nResult = Some((0x100002, MOV(())))\n')
        self.assertEqual([r['status'] for r in parse_decodes(self.instructions, output)],
                         ['wrong_length', 'wrong_kind'])

    def test_missing_duplicate_or_reordered_results(self):
        for output in (
            '',
            'CHECK_0\nResult = None(())\n',
            'CHECK_0\nResult = None(())\nCHECK_0\nResult = None(())\n',
            'CHECK_1\nResult = None(())\nCHECK_0\nResult = None(())\n',
            'CHECK_0\nCHECK_1\nResult = None(())\n',
            'CHECK_0\nResult = None(())\nResult = None(())\n'
            'CHECK_1\nResult = None(())\n',
            'CHECK_0\nResult = unknown\nCHECK_1\nResult = None(())\n',
        ):
            with self.subTest(output=output), self.assertRaises(ValueError):
                parse_decodes(self.instructions, output)


if __name__ == '__main__':
    unittest.main()
