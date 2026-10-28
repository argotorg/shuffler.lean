#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Run the assembled permute bytes with the production Sail decoder and execution."""
import argparse
import os
from pathlib import Path
import re
import subprocess

import test_native as native

CODE = 0x100000
RETURN = 0x300000
STACK = 0x800008
BUFFERS = tuple(0x400000 + 0x10000 * index for index in range(6))
SAVED = dict(rbx=0x123456789ABCDEF0, rbp=0x23456789ABCDEF01,
             r12=0x3456789ABCDEF012, r13=0x456789ABCDEF0123,
             r14=0x56789ABCDEF01234, r15=0x6789ABCDEF012345)
REGISTERS = ('rax', 'rcx', 'rdx', 'rbx', 'rsp', 'rbp', 'rsi', 'rdi',
             'r8', 'r9', 'r10', 'r11', 'r12', 'r13', 'r14', 'r15')


def run(args, *, cwd=None, env=None, log=None, timeout=300):
    result = subprocess.run(args, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            timeout=timeout)
    if log is not None:
        log.write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(f'{args[0]} failed ({result.returncode}):\n{result.stdout[-12000:]}')
    return result.stdout


def write(address, value, width=4):
    return (f'write_memory({width}, 0x{address:016X}, 0x{value:0{width * 2}X}, '
            'create_writeAccessDescriptor());')


def check(address, value, label, width=4):
    return (f'assert(read_memory({width}, 0x{address:016X}, create_readAccessDescriptor()) '
            f'== 0x{value:0{width * 2}X}, "{label}");')


def words(address, values, label=None):
    """Compress fixture constants, not the implementation under test."""
    if len(values) > 2:
        difference = values[1] - values[0]
        if all(value == values[0] + difference * index for index, value in enumerate(values)):
            cell = f'get_slice_int(64, {address} + 4 * i, 0)'
            value = f'get_slice_int(32, {values[0]} + ({difference}) * i, 0)'
            statement = (f'write_memory(4, {cell}, {value}, create_writeAccessDescriptor())'
                         if label is None else
                         f'assert(read_memory(4, {cell}, create_readAccessDescriptor()) '
                         f'== {value}, "{label}")')
            return [f'foreach (i from 0 to {len(values) - 1}) {{ {statement} }};']
    return [write(address + 4 * index, value) if label is None else
            check(address + 4 * index, value, f'{label}:{index}')
            for index, value in enumerate(values)]


def selected_cases():
    for case in native.inputs():
        size, values, permutation, expected = case
        if expected is None:
            continue
        if size <= 3 or size > 1024 or size in (16, 17, 18, 19):
            yield case
        elif size == 1024 and values == tuple(range(size)) and permutation == values:
            yield case


def case_function(number, case, expected):
    size, values, permutation, _ = case
    status, result = expected
    label = f'case_{number}'
    early = size == 0 or size > 1024
    lengths = (0, 0, 0, 0, 0, 3) if early else (size,) * 4 + (2 * size, 3)
    initial = (values, permutation, (), (), (), ())
    registers = dict.fromkeys(REGISTERS, 0xFEDCBA9876543210)
    registers.update(SAVED)
    registers.update(rdi=0xDEADBEEF00000000 | size, rsp=STACK)
    registers.update(zip(('rsi', 'rdx', 'rcx', 'r8', 'r9'),
                         (0,) * 5 if early else BUFFERS[:5]))
    body = [f'{register} = 0x{value:016X};' for register, value in registers.items()]
    body += [f'rip = 0x{CODE:016X};',
             'rflags = struct { bits = 0x0000000000000CD5 };',
             write(STACK, RETURN, 8), write(STACK + 8, BUFFERS[5], 8),
             write(STACK - 48, 0x0123456789ABCDEF, 8),
             write(STACK + 16, 0xFEDCBA9876543210, 8)]
    for address, length, data in zip(BUFFERS, lengths, initial):
        body.append(write(address - 4, native.EXPORT.GUARD))
        body += words(address, tuple(data) + (native.EXPORT.SALT,) * (length - len(data)))
        body.append(write(address + 4 * length, native.EXPORT.GUARD))
    body += ['var steps : int = 0;',
             f'while (rip != 0x{RETURN:016X}) & (steps < 200000) do {{',
             '  fetch_execute(); steps = steps + 1;', '};',
             f'assert(rip == 0x{RETURN:016X}, "{label}:instruction limit");',
             f'assert(rax == 0x{status:016X}, "{label}:return");',
             f'assert(rsp == 0x{STACK + 8:016X}, "{label}:RSP");']
    body += [f'assert({register} == 0x{value:016X}, "{label}:{register}");'
             for register, value in SAVED.items()]
    body += [check(STACK, RETURN, f'{label}:return address', 8),
             check(STACK + 8, BUFFERS[5], f'{label}:output argument', 8),
             check(STACK - 48, 0x0123456789ABCDEF, f'{label}:lower stack guard', 8),
             check(STACK + 16, 0xFEDCBA9876543210, f'{label}:upper stack guard', 8)]
    for index, (address, length, final) in enumerate(zip(BUFFERS, lengths, result)):
        body.append(check(address - 4, native.EXPORT.GUARD, f'{label}:buffer{index}:lower guard'))
        body += words(address, final, f'{label}:buffer{index}')
        body.append(check(address + 4 * length, native.EXPORT.GUARD,
                          f'{label}:buffer{index}:upper guard'))
    body.append(f'print("{label} passed\\n");')
    return f'function {label}() -> unit = {{\n  ' + '\n  '.join(body) + '\n}\n'


def harness(code, listing, cases, reference):
    instructions = []
    for line in listing.splitlines():
        match = re.match(r'^\s*([0-9a-f]+):\s+((?:[0-9a-f]{2}\s+)+)', line)
        if match:
            instructions.append((int(match[1], 16), len(bytes.fromhex(match[2]))))
    initialize = [f'{register} = 0x0000000000000000;' for register in REGISTERS]
    for offset in range(0, len(code), 8):
        chunk = code[offset:offset + 8]
        initialize.append(write(CODE + offset, int.from_bytes(chunk, 'little'), len(chunk)))
    decode = []
    for offset, length in instructions:
        decode.append(f'match decode(0x{CODE + offset:016X}) {{ '
                      f'Some(next, _) => assert(next == 0x{CODE + offset + length:016X}, '
                      f'"decode length:{offset}"), '
                      f'None() => assert(false, "decode rejected:{offset}") }};')
    functions = [case_function(index, case, native.EXPORT.execute(reference, case))
                 for index, case in enumerate(cases)]
    calls = [f'case_{index}();' for index in range(len(cases))]
    calls.append(f'print("Sail full module: {len(instructions)} decoded instructions, '
                 f'{len(cases)} executions passed\\n");')
    return '\n'.join(functions) + '\nfunction main() -> unit = {\n  ' + '\n  '.join(
        initialize + decode + calls) + '\n}\n'


def main(sail, model, output, object_file, reference_object):
    output.mkdir(parents=True, exist_ok=True)
    native.check_instructions(object_file, output)
    code = (output / 'permute.bin').read_bytes()
    listing = (output / 'permute.disassembly.txt').read_text()
    library = output / 'reference.so'
    run(['clang', '-shared', str(reference_object), '-o', str(library)])
    cases = tuple(selected_cases())
    fixture = output / 'permute_cases.sail'
    fixture.write_text(harness(code, listing, cases, native.EXPORT.load(library)))
    environment = {**os.environ, 'PATH': str(sail.parent) + os.pathsep + os.environ['PATH']}
    files = (model / 'sail_files').read_text().split()
    run([str(sail), '--no-warn', '-c', '-O', *files, str(fixture),
         '-o', str(output / 'permute_model')], cwd=model, env=environment,
        log=output / 'sail-build.log')
    sail_directory = Path(run([str(sail), '--dir'], env=environment).strip())
    runtime = sail_directory / 'lib'
    executable = output / 'permute-model'
    run(['clang', '-O1', str(output / 'permute_model.c'),
         *(str(path) for path in sorted(runtime.glob('*.c'))), '-I', str(runtime),
         '-lgmp', '-lz', '-o', str(executable)], log=output / 'c-build.log')
    result = run([str(executable)], log=output / 'model-tests.log')
    expected = f'Sail full module: 136 decoded instructions, {len(cases)} executions passed'
    if expected not in result:
        raise AssertionError('Sail execution omitted its completion marker')
    print(expected)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('sail', type=Path)
    parser.add_argument('model', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('object', type=Path)
    parser.add_argument('reference_object', type=Path)
    arguments = parser.parse_args()
    main(*(path.resolve() for path in (arguments.sail, arguments.model,
          arguments.output, arguments.object, arguments.reference_object)))
