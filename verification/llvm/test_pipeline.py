#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Test the production import, proof, printer, and compiled output."""
import ctypes
import itertools
import random
import runpy
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from import_ast import import_ast


def command(args, directory):
    return subprocess.run(args, cwd=directory, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)


def require_success(args, directory):
    result = command(args, directory)
    if result.returncode:
        raise AssertionError(f"{args} failed:\n{result.stdout}")
    return result.stdout


def changed(text, old, new):
    if text.count(old) != 1:
        raise AssertionError(f"expected one occurrence of {old!r}")
    return text.replace(old, new)


def negative_case(project, name, source, proof_failure):
    compcert = project.parent / 'clight/build/compcert'
    with tempfile.TemporaryDirectory(prefix=f'{name}-', dir=project) as temporary:
        directory = Path(temporary)
        for module in ['Normalize', 'PureResult', 'ClightDepth', 'Permute']:
            shutil.copyfile(project / f'{module}.vo', directory / f'{module}.vo')
        for module in ['Program', 'Equivalence']:
            shutil.copyfile(project / f'{module}.v', directory / f'{module}.v')
        (directory / 'depth.ll').write_text(source)
        require_success(['llvm-as', 'depth.ll', '-o', 'depth.bc'], directory)
        require_success(['frontend', '-op', '.', 'depth.ll'], directory)
        (directory / 'Candidate.v').write_text(
            import_ast((directory / 'depth.v.ast').read_text()))
        coqc = ['coqc', '-R', str(compcert), 'compcert']
        require_success(coqc + ['Candidate.v'], directory)
        if proof_failure:
            require_success(coqc + ['Program.v'], directory)
            result = command(coqc + ['Equivalence.v'], directory)
            # This is the arithmetic proof step, after the full interpreter
            # reduces. A missing dependency is not an expected rejection.
            expected = 'Found no subterm matching'
        else:
            result = command(coqc + ['Program.v'], directory)
            expected = 'Unable to unify'
        if result.returncode == 0 or expected not in result.stdout:
            raise AssertionError(f'{name}: unexpected result:\n{result.stdout}')
        if (directory / 'Equivalence.vo').exists():
            raise AssertionError(f'{name}: produced a proof object')
        print(f'Rejected {name}')


def native_test(project):
    require_success(['clang', '-shared', 'depth.proved.o', '-o', 'libdepth.so'], project)
    library = ctypes.CDLL(str(project / 'libdepth.so'))
    function = library.shuffler_depth
    function.argtypes = [ctypes.c_uint32, ctypes.c_uint32]
    function.restype = ctypes.c_uint32
    boundaries = [0, 1, 2, 0x7fffffff, 0x80000000, 0xfffffffe, 0xffffffff]
    generator = random.Random(0)
    cases = list(itertools.product(boundaries, repeat=2))
    cases += [(generator.getrandbits(32), generator.getrandbits(32)) for _ in range(2048)]
    for x, y in cases:
        actual = function(x, y)
        if actual != (x - y) % (1 << 32):
            raise AssertionError((x, y, actual))
    print(f'Compiled printed LLVM: {len(cases)} cases pass')


def empty_module_test(project):
    # The pinned frontend does not flush its formatter for an empty module.
    # The importer must reject the incomplete export. Check normalization's
    # empty-AST case separately in Rocq, with the production definition.
    with tempfile.TemporaryDirectory(prefix='empty-', dir=project) as temporary:
        directory = Path(temporary)
        (directory / 'empty.ll').write_text('; no definitions\n')
        require_success(['llvm-as', 'empty.ll', '-o', 'empty.bc'], directory)
        require_success(['frontend', '-op', '.', 'empty.ll'], directory)
        try:
            import_ast((directory / 'empty.v.ast').read_text())
        except ValueError as error:
            if str(error) != 'expected one Vellvm AST marker':
                raise
        else:
            raise AssertionError('expected the pinned frontend\'s incomplete empty export')
        shutil.copyfile(project / 'Normalize.vo', directory / 'Normalize.vo')
        (directory / 'Empty.v').write_text(
            'Require Import Normalize.\n'
            'Example empty_rejected : normalize nil = None.\n'
            'Proof. reflexivity. Qed.\n')
        require_success(['coqc', 'Empty.v'], directory)
        print('Rejected empty export and empty AST')


def main(project):
    policy = runpy.run_path(str(project.parent / 'clight/check-assumptions.py'))
    report = 'Equivalence.depth_equivalence\n' + (project / 'assumptions.txt').read_text()
    policy['check'](report, expected=['Equivalence.depth_equivalence'])
    try:
        policy['check'](report + '\nUnproved.claim : False\n',
                        expected=['Equivalence.depth_equivalence'])
    except ValueError:
        pass
    else:
        raise AssertionError('assumption check accepts an added axiom')
    print('Theorem assumptions pass PR #6\'s existing policy')
    original = (project / 'depth.ll').read_text()
    native_test(project)
    negative_case(project, 'add', changed(original, 'sub i32', 'add i32'), True)
    negative_case(project, 'return-argument',
                  changed(original, 'ret i32 %sub', 'ret i32 %v10'), True)
    negative_case(project, 'multiply', changed(original, 'sub i32', 'mul i32'), False)
    negative_case(project, 'calling-convention',
                  changed(original, 'define noundef', 'define fastcc noundef'), False)
    negative_case(project, 'external-declaration',
                  original + '\ndeclare i32 @external(i32)\n', False)
    empty_module_test(project)
    negative_case(project, 'two-functions', original + '''
define i32 @extra(i32 %x, i32 %y) {
entry:
  %z = sub i32 %x, %y
  ret i32 %z
}
''', False)


if __name__ == '__main__':
    main(Path(sys.argv[1]).resolve())
