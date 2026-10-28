#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Compare the actual assembly object, proved LLVM object, and generated C."""
import ctypes
import importlib.util
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    'llvm_export_tests', ROOT / 'verification/llvm/full/test_export.py')
EXPORT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(EXPORT)

# This test wrapper calls the production assembly and checks every SysV
# callee-saved register. Its CALL instruction is outside the verified routine.
ABI_PROBE = '''
.text
.globl probe_permute
.type probe_permute, @function
probe_permute:
    push %rbx
    push %rbp
    push %r12
    push %r13
    push %r14
    push %r15
    sub $24, %rsp
    mov 80(%rsp), %rax
    mov %rax, (%rsp)
    mov $0x12345678, %ebx
    mov $0x23456789, %ebp
    mov $0x3456789a, %r12d
    mov $0x456789ab, %r13d
    mov $0x56789abc, %r14d
    mov $0x6789abcd, %r15d
    call permute
    cmp $0x12345678, %rbx
    jne .Labi_bad
    cmp $0x23456789, %rbp
    jne .Labi_bad
    cmp $0x3456789a, %r12
    jne .Labi_bad
    cmp $0x456789ab, %r13
    jne .Labi_bad
    cmp $0x56789abc, %r14
    jne .Labi_bad
    cmp $0x6789abcd, %r15
    jne .Labi_bad
    jmp .Labi_return
.Labi_bad:
    mov $0xffffffff, %eax
.Labi_return:
    add $24, %rsp
    pop %r15
    pop %r14
    pop %r13
    pop %r12
    pop %rbp
    pop %rbx
    ret
.size probe_permute, .-probe_permute
.section .note.GNU-stack,"",@progbits
'''


def run(*args):
    return subprocess.run(args, check=True, text=True, stdout=subprocess.PIPE).stdout


def check_instructions(object_file, output):
    binary = output / 'permute.bin'
    run('llvm-objcopy', '--dump-section', f'.text={binary}', str(object_file))
    machine_code = binary.read_bytes()
    listing = run('llvm-objdump', '-d', '--x86-asm-syntax=intel', str(object_file))
    (output / 'permute.disassembly.txt').write_text(listing)
    allowed = {'mov', 'xor', 'cmp', 'add', 'sub', 'push', 'pop', 'ret', 'jne', 'jns', 'jmp'}
    instructions = []
    offset = 0
    for line in listing.splitlines():
        match = re.match(r'^\s*([0-9a-f]+):\s+((?:[0-9a-f]{2}\s+)+)([a-z][a-z0-9]*)\b', line)
        if not match:
            continue
        address, encoding, opcode = int(match[1], 16), bytes.fromhex(match[2]), match[3]
        if address != offset or machine_code[offset:offset + len(encoding)] != encoding:
            raise AssertionError(f'disassembly does not cover consecutive object bytes: {line}')
        offset += len(encoding)
        if opcode not in allowed:
            raise AssertionError(f'unsupported instruction: {line}')
        if opcode in {'jne', 'jns'} and len(encoding) != 2:
            raise AssertionError(f'conditional jump is not short: {line}')
        if opcode == 'jmp' and encoding[0] not in {0xEB, 0xE9}:
            raise AssertionError(f'unexpected jump encoding: {line}')
        operation = encoding[1] if 0x40 <= encoding[0] <= 0x4F else encoding[0]
        if operation in {0x04, 0x05, 0x2C, 0x2D, 0x3C, 0x3D}:
            raise AssertionError(f'unsupported accumulator immediate encoding: {line}')
        instructions.append(opcode)
    if not instructions or set(instructions) != allowed:
        raise AssertionError(f'missing instructions or unexpected disassembly: {set(instructions)}')
    if offset != len(machine_code):
        raise AssertionError('disassembly omits bytes from the text section')
    print(f'{len(machine_code)} bytes, {len(instructions)} instructions; '
          f'allowed opcodes: {", ".join(sorted(set(instructions)))}')


def inputs():
    yield from EXPORT.cases()
    for size in (0x7FFFFFFF, 0x80000000, 0x80000001, 0xFFFFFFFE):
        yield size, (), (), 2
    for bad in (0x7FFFFFFF, 0x80000000, 0x80000001, 0xFFFFFFFE):
        yield 3, (0, 0x80000000, 0xFFFFFFFF), (0, 1, bad), 2


def main(output, llvm_object, source):
    output.mkdir(parents=True, exist_ok=True)
    assembly = ROOT / 'verification/x86/permute.S'
    object_file = output / 'permute.o'
    run('clang', '-Wa,-L', '-c', str(assembly), '-o', str(object_file))
    (output / 'permute.symbols.txt').write_text(run('llvm-nm', '--numeric-sort', str(object_file)))
    check_instructions(object_file, output)
    with tempfile.TemporaryDirectory(prefix='native-', dir=output) as temporary:
        build = Path(temporary)
        probe = build / 'abi_probe.S'
        probe.write_text(ABI_PROBE)
        asm_lib, llvm_lib, c_lib = (build / name for name in ('assembly.so', 'llvm.so', 'c.so'))
        run('clang', '-shared', '-Wl,-Bsymbolic', str(object_file), str(probe), '-o', str(asm_lib))
        run('clang', '-shared', str(llvm_object), '-o', str(llvm_lib))
        run('clang', '-std=c11', '-O0', '-fPIC', '-shared', str(source), '-o', str(c_lib))
        cases = tuple(inputs())
        assembly_function = EXPORT.load(asm_lib)
        EXPORT.compare(EXPORT.load(c_lib), assembly_function, cases)
        EXPORT.compare(EXPORT.load(llvm_lib), assembly_function, cases)
        print(f'{len(cases)} cases: assembly agrees with generated C and proved LLVM on all six buffers')
        library = ctypes.CDLL(str(asm_lib))
        abi_function = library.probe_permute
        abi_function.argtypes = [EXPORT.WORD] + [EXPORT.POINTER] * 6
        abi_function.restype = EXPORT.WORD
        EXPORT.compare(assembly_function, abi_function, cases)
        print(f'{len(cases)} ABI checks: RBX, RBP, R12, R13, R14, R15 preserved')

        # Change an instruction in the real assembly source and require the
        # same native comparison to reject the resulting object.
        text = assembly.read_text()
        old = '    mov eax, 2\n'
        if text.count(old) != 1:
            raise AssertionError('expected one invalid-return instruction')
        changed = build / 'changed.S'
        changed.write_text(text.replace(old, '    mov eax, 0\n'))
        changed_lib = build / 'changed.so'
        run('clang', '-shared', str(changed), '-o', str(changed_lib))
        try:
            EXPORT.compare(assembly_function, EXPORT.load(changed_lib), cases)
        except AssertionError as error:
            if 'expected status 2, got 0' not in str(error):
                raise
        else:
            raise AssertionError('native comparison accepted a changed return instruction')
        print('Changed assembly return instruction rejected')

        # Ensure the byte audit rejects an instruction outside the decoder subset.
        unsupported = build / 'unsupported.S'
        unsupported.write_text(text.replace('    ret\n', '    nop\n    ret\n'))
        unsupported_object = build / 'unsupported.o'
        run('clang', '-c', str(unsupported), '-o', str(unsupported_object))
        try:
            check_instructions(unsupported_object, build)
        except AssertionError as error:
            if 'unsupported instruction:' not in str(error) or 'nop' not in str(error):
                raise
        else:
            raise AssertionError('byte audit accepted an unsupported instruction')
        print('Assembly with an added NOP rejected by the byte audit')


if __name__ == '__main__':
    if len(sys.argv) != 4:
        sys.exit('usage: test_native.py OUTPUT_DIRECTORY VERIFIED_LLVM_OBJECT GENERATED_PERMUTE_C')
    main(*(Path(argument).resolve() for argument in sys.argv[1:]))
