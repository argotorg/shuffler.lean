#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Execute instruction bytes with the production Sail decoder and semantics."""
import argparse
from dataclasses import dataclass
import os
from pathlib import Path
import re
import subprocess


@dataclass(frozen=True)
class Case:
    name: str
    expression: str
    expected: int


def expression(code, setup, observation, base=0x100000000):
    encoded = int.from_bytes(code.ljust(8, b'\0'), 'little')
    return (f'{{ rip = 0x{base:016X}; '
            'rflags = struct { bits = 0x0000000000000011 }; '
            f'{setup} '
            f'write_memory(8, rip, 0x{encoded:016X}, create_writeAccessDescriptor()); '
            f'{observation} }}')


def jumps():
    base = 0x100000000
    for displacement in (-128, -1, 0, 1, 127):
        code = bytes((0xEB, displacement & 255))
        yield Case(f'jmp8_{displacement}',
                   expression(code, '', 'fetch_execute(); rip'),
                   base + 2 + displacement)
    for displacement in (-2147483648, -129, -128, -1, 0, 1, 127, 128, 2147483647):
        code = b'\xE9' + displacement.to_bytes(4, 'little', signed=True)
        yield Case(f'jmp32_{displacement}',
                   expression(code, '', 'fetch_execute(); rip'),
                   base + 5 + displacement)
    for opcode, shift, name in ((0x75, 6, 'jne'), (0x79, 7, 'jns')):
        for displacement in (-128, -1, 0, 1, 127):
            for flag_value in (0, 1):
                code = bytes((opcode, displacement & 255))
                yield Case(f'{name}_{displacement}_{flag_value}',
                           expression(code, 'rflags = struct { bits = '
                                      f'0x{flag_value << shift:016X} }};',
                                      'fetch_execute(); rip'),
                           base + 2 + (displacement if flag_value == 0 else 0))
    # These remain outside the chosen instruction subset.
    for name, code in (('far_jmp', b'\xEA\0\0\0\0\0\0'),
                       ('short_je', b'\x74\0'),
                       ('near_jne', b'\x0F\x85\0\0\0\0')):
        yield Case(f'reject_{name}', expression(code, '',
                   'let accepted : bits(8) = match decode(rip) '
                   '{ None() => 0x00, Some(_) => 0x01 }; accepted'), 0)


def flags():
    for width, prefix in ((8, b''), (16, b'\x66'), (32, b''), (64, b'\x48')):
        maximum = (1 << width) - 1
        # Expected values are CF | (AF << 4). Test both setting and clearing.
        subcases = ((0x10, 1, 0x10), (0, 0x10, 1),
                    (0x10, 0x10, 0), (0x0F, 0x10, 1))
        addcases = ((0x0F, 1, 0x10), (maximum, 1, 0x11),
                    (maximum, 0x10, 1), (0, 0, 0))
        for name, opcode, inputs in (('cmp', 0x38, subcases),
                                     ('sub', 0x28, subcases),
                                     ('add', 0x00, addcases)):
            code = prefix + bytes((opcode + (width != 8), 0xD1))
            for left, right, expected in inputs:
                setup = f'rcx = 0x{left:016X}; rdx = 0x{right:016X};'
                yield Case(f'{name}{width}_{left:x}_{right:x}',
                           expression(code, setup,
                             'fetch_execute(); rflags.bits & 0x0000000000000011'),
                           expected)


def run(sail, model, cases):
    commands = '\n'.join(f'{case.expression}\n:run' for case in cases) + '\n:quit\n'
    environment = {**os.environ, 'PATH': str(sail.parent) + os.pathsep + os.environ['PATH']}
    result = subprocess.run(
        [str(sail), '--no-warn', '-i', 'prelude.sail', 'registers.sail',
         'interface.sail', 'operands.sail', 'decode.sail', 'tiny-x86.sail'],
        cwd=model, input=commands, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, env=environment, timeout=120, check=True)
    values = re.findall(r'Result = (0x[0-9A-Fa-f]+|[0-9]+)\s*(?:\r?\n|$)', result.stdout)
    if len(values) != len(cases):
        raise AssertionError(f'expected {len(cases)} results, got {len(values)}\n{result.stdout}')
    failures = tuple(f'{case.name}: expected {case.expected:#x}, got {int(value, 0):#x}'
                     for case, value in zip(cases, values)
                     if int(value, 0) != case.expected)
    if failures:
        raise AssertionError('\n'.join(failures))
    print(f'Sail instruction semantics: {len(cases)} cases pass')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('sail', type=Path)
    parser.add_argument('model', type=Path)
    parser.add_argument('--group', choices=('all', 'flags', 'jumps'), default='all')
    arguments = parser.parse_args()
    selected = (() if arguments.group == 'flags' else tuple(jumps())) + (
                () if arguments.group == 'jumps' else tuple(flags()))
    run(arguments.sail.resolve(), arguments.model.resolve(), selected)
