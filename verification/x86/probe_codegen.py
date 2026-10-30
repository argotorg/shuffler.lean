#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Generate x86 candidates and measure coverage in the actual Sail decoder.

This is a coverage experiment, not an equivalence validator. Unsupported
instructions are reported without making the probe fail.
"""
import argparse
from collections import Counter
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess


@dataclass(frozen=True)
class Instruction:
    offset: int
    encoding: bytes
    assembly: str


def parse_instructions(code, listing):
    instructions = tuple(
        Instruction(int(m[1], 16), bytes.fromhex(m[2]), m[3].strip())
        for line in listing.splitlines()
        if (m := re.match(r'^\s*([0-9a-f]+):\s+((?:[0-9a-f]{2}\s+)+)([a-z].*)$', line)))
    position = 0
    for instruction in instructions:
        length = len(instruction.encoding)
        if (instruction.offset != position or not 1 <= length <= 15 or
                code[position:position + length] != instruction.encoding):
            raise ValueError('disassembly does not cover consecutive object bytes')
        position += length
    if not instructions or position != len(code):
        raise ValueError('disassembly does not cover the text section')
    return instructions


def parse_decodes(instructions, output):
    chunks = re.split(r'^CHECK_(\d+)\n', output, flags=re.M)
    if len(chunks) != 2 * len(instructions) + 1:
        raise ValueError('missing or extra decoder records')
    results = []
    for index, instruction in enumerate(instructions):
        if int(chunks[2 * index + 1]) != index:
            raise ValueError('decoder records are out of order')
        outcomes = re.findall(r'^(?:Result = |Error: ).*$', chunks[2 * index + 2], re.M)
        if len(outcomes) != 1:
            raise ValueError('missing or duplicate decoder outcome')
        outcome = outcomes[0]
        decoded = {}
        if match := re.match(r'Result = Some\(\((0x[0-9A-Fa-f]+), (\w+)\(', outcome):
            length = int(match[1], 16) - 0x100000 - instruction.offset
            expected = instruction.assembly.split()[0].upper()
            kind_matches = match[2] == expected or (expected == 'JMP' and match[2] == 'JMP32')
            status = ('wrong_length' if length != len(instruction.encoding) else
                      'wrong_kind' if not kind_matches else 'accepted')
            decoded = dict(decoded_length=length, constructor=match[2])
        elif outcome == 'Result = None(())':
            status = 'rejected'
        elif outcome.startswith('Error: '):
            status, decoded = 'error', dict(error=outcome.removeprefix('Error: '))
        else:
            raise ValueError('unrecognized decoder outcome: ' + outcome)
        results.append(dict(offset=instruction.offset, encoding=instruction.encoding.hex(' '),
                            assembly=instruction.assembly, length=len(instruction.encoding),
                            status=status, **decoded))
    return results


def run(arguments, **options):
    result = subprocess.run([str(a) for a in arguments], text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, timeout=180, **options)
    if result.returncode:
        raise RuntimeError(f'{arguments[0]} failed:\n{result.stdout}\n{result.stderr}')
    return result.stdout


def memory_write(address, code):
    return (f'write_memory({len(code)}, 0x{address:016X}, '
            f'0x{int.from_bytes(code, "little"):0{2 * len(code)}X}, '
            'create_writeAccessDescriptor());')


def initialize(code):
    registers = ('rax', 'rcx', 'rdx', 'rbx', 'rsp', 'rbp', 'rsi', 'rdi',
                 'r8', 'r9', 'r10', 'r11', 'r12', 'r13', 'r14', 'r15')
    return ([f'{register} = 0x0000000000000000;' for register in registers] +
            ['rflags = struct { bits = 0x0000000000000000 };'] +
            [memory_write(0x100000 + offset, code[offset:offset + 8])
             for offset in range(0, len(code), 8)])


def interpret(sail, model, files, expressions, destination):
    commands = '\n'.join(expression + '\n:run' for expression in expressions) + '\n:quit\n'
    destination.with_suffix('.commands').write_text(commands)
    output = run([sail, '--no-warn', '-i', *files], cwd=model, input=commands,
                 env={**os.environ, 'PATH': str(sail.parent) + os.pathsep + os.environ['PATH']})
    output = re.sub(r'\x1b\[[0-?]*[ -/]*[@-~]', '', output)
    destination.with_suffix('.log').write_text(output)
    if len(re.findall(r'^INITIALIZED\nResult = \(\)', output, re.M)) != 1:
        raise ValueError('Sail fixture initialization did not complete')
    return output


def decode_object(object_file, sail, model, files, output):
    name = object_file.stem
    binary = output / (name + '.bin')
    run(['llvm-objcopy', '--dump-section', f'.text={binary}', object_file])
    code = binary.read_bytes()
    listing = run(['llvm-objdump', '-d', '--x86-asm-syntax=intel', object_file])
    (output / (name + '.disasm')).write_text(listing)
    relocations = run(['llvm-readobj', '--relocations', object_file])
    (output / (name + '.relocations')).write_text(relocations)
    # Debug/unwind relocations do not change code. Unresolved code relocations do.
    if re.search(r'Section[^\n]*\.rela?\.text[^\n]*\{[^}]*R_X86_64_', relocations):
        raise ValueError('unresolved text relocation')
    instructions = parse_instructions(code, listing)
    expressions = ['{ ' + ' '.join(initialize(code)) + ' print("INITIALIZED\\n"); () }']
    expressions += [f'{{ print("CHECK_{index}\\n"); decode(0x{0x100000 + ins.offset:016X}) }}'
                    for index, ins in enumerate(instructions)]
    log = interpret(sail, model, files, expressions, output / (name + '-decode'))
    results = parse_decodes(instructions, log)
    unsupported = Counter(row['assembly'].split()[0] for row in results
                          if row['status'] != 'accepted')
    return dict(name=name, code_sha256=hashlib.sha256(code).hexdigest(), bytes=len(code),
                instruction_count=len(instructions),
                status_counts=dict(Counter(row['status'] for row in results)),
                unsupported_mnemonics=dict(sorted(unsupported.items())), instructions=results)


def compile_candidates(source, output):
    target = '--target=x86_64-unknown-linux-gnu'
    assembly = output / 'clang-backend-O2.s'
    clang_commands = [
        ['clang', '-Wno-unused-command-line-argument', target, '-O2', '-Xclang',
         '-disable-llvm-passes', '-S', '-x', 'ir', '-masm=intel', source, '-o', assembly],
        ['clang', target, '-c', assembly, '-o', assembly.with_suffix('.o')],
    ]
    variants = [('clang-backend-O2', clang_commands)]
    for name, flags in (
        ('llc-O0', ['-O=0']),
        ('llc-O2', ['-O=2']),
        ('llc-align1', ['-O=2', '-align-loops=1']),
        ('llc-slowinc', ['-O=2', '-align-loops=1', '-mattr=+slow-incdec']),
        ('llc-slowlea', ['-O=2', '-align-loops=1',
                         '-mattr=+slow-incdec,+slow-lea,+slow-3ops-lea',
                         '-disable-x86-lea-opt']),
    ):
        common = ['llc', '-mtriple=x86_64-unknown-linux-gnu', *flags]
        variants.append((name, [
            common + ['-filetype=obj', source, '-o', output / (name + '.o')],
            common + ['-filetype=asm', '-x86-asm-syntax=intel', source,
                      '-o', output / (name + '.s')],
        ]))
    for _, commands in variants:
        for command in commands:
            run(command)
    return variants


def main(source, model_source, sail, output):
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        raise ValueError('output directory must be empty')
    model = output / 'model'
    model.mkdir()
    files = (model_source / 'sail_files').read_text().split()
    for filename in files:
        shutil.copyfile(model_source / filename, model / filename)
    variants = compile_candidates(source, output)
    run(['clang', '--target=x86_64-unknown-linux-gnu', '-c',
         Path(__file__).with_name('permute.S'), '-o', output / 'handwritten.o'])
    (output / 'unsupported.s').write_text('.text\n.intel_syntax noprefix\nud2\n')
    run(['clang', '--target=x86_64-unknown-linux-gnu', '-c',
         output / 'unsupported.s', '-o', output / 'unsupported.o'])
    controls = [decode_object(output / (name + '.o'), sail, model, files, output)
                for name in ('handwritten', 'unsupported')]
    if controls[0]['status_counts'] != {'accepted': controls[0]['instruction_count']}:
        raise ValueError('handwritten control failed decoding')
    if controls[1]['status_counts'] != {'rejected': 1}:
        raise ValueError('unsupported instruction control was not rejected')
    reports = []
    for name, commands in variants:
        report = decode_object(output / (name + '.o'), sail, model, files, output)
        reports.append(dict(report, commands=[[str(a) for a in command] for command in commands]))
        print(f'{name}: {report["status_counts"]}', flush=True)
    # Reproduce the first nine fetch/execute steps of the empty Clang call.
    code = (output / 'clang-backend-O2.bin').read_bytes()
    setup = initialize(code) + [
        'rsp = 0x0000000000800008;', 'rip = 0x0000000000100000;',
        memory_write(0x800008, (0x300000).to_bytes(8, 'little')),
        memory_write(0x800010, (0x450000).to_bytes(8, 'little')),
    ]
    expressions = ['{ ' + ' '.join(setup) + ' print("INITIALIZED\\n"); () }']
    expressions += [f'{{ print("STEP_{i}\\n"); fetch_execute(); rip }}' for i in range(9)]
    interpret(sail, model, files, expressions, output / 'clang-entry')
    metadata = dict(source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                    model_sha256={name: hashlib.sha256((model / name).read_bytes()).hexdigest()
                                  for name in files},
                    versions={name: run([name, '--version']).strip()
                              for name in ('clang', 'llc')},
                    sail_version=run([sail, '--version']).strip(),
                    controls=controls, variants=reports)
    (output / 'results.json').write_text(json.dumps(metadata, indent=2) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('llvm', type=Path, help='the proved LLVM export')
    parser.add_argument('model', type=Path, help='the patched sail-tiny-x86 source')
    parser.add_argument('sail', type=Path, help='the Sail executable')
    parser.add_argument('output', type=Path, help='an empty output directory')
    args = parser.parse_args()
    main(*(path.resolve() for path in (args.llvm, args.model, args.sail, args.output)))
