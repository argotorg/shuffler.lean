#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check byte export using the production assembly object and generator."""
from pathlib import Path
import subprocess
import sys
import tempfile

from generate_program import inspect_object, rocq_source

HERE = Path(__file__).resolve().parent


def run(*arguments):
    subprocess.run(arguments, check=True, stdout=subprocess.PIPE)


def rejects(object_file, message):
    try:
        inspect_object(object_file)
    except ValueError as error:
        if message not in str(error):
            raise
    else:
        raise AssertionError(f'accepted {object_file}')


def main():
    with tempfile.TemporaryDirectory(prefix='x86-export-') as temporary:
        work = Path(temporary)
        object_file = work / 'permute.o'
        run('clang', '-Wa,-L', '-c', str(HERE / 'permute.S'), '-o', str(object_file))
        program = inspect_object(object_file)
        generated = rocq_source(program)
        if generated != (HERE / 'X86Program.v').read_text():
            raise AssertionError('X86Program.v does not match the assembly object')
        if generated != rocq_source(inspect_object(object_file)):
            raise AssertionError('export is not deterministic')
        print('Assembly object and checked-in byte definitions agree; export is deterministic')

        no_labels = work / 'no_labels.o'
        run('clang', '-c', str(HERE / 'permute.S'), '-o', str(no_labels))
        rejects(no_labels, 'missing assembly labels')
        print('Object without local labels rejected')

        source = (HERE / 'permute.S').read_text()
        if source.count('    mov eax, 2\n') != 1:
            raise AssertionError('expected one invalid-return instruction')
        changed_source = work / 'changed.S'
        changed_source.write_text(source.replace('    mov eax, 2\n', '    mov eax, 3\n'))
        changed_object = work / 'changed.o'
        run('clang', '-Wa,-L', '-c', str(changed_source), '-o', str(changed_object))
        if generated == rocq_source(inspect_object(changed_object)):
            raise AssertionError('byte export did not change after an instruction mutation')
        print('Changed return instruction changes the byte definitions')

        relocation_source = work / 'relocation.S'
        relocation_source.write_text(source + '\n.text\n.quad external_address\n')
        relocation_object = work / 'relocation.o'
        run('clang', '-Wa,-L', '-c', str(relocation_source), '-o', str(relocation_object))
        rejects(relocation_object, 'object contains relocations')
        print('Object with unresolved relocations rejected')


if __name__ == '__main__':
    if len(sys.argv) != 1:
        sys.exit('usage: test_program.py')
    main()
