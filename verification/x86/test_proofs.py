#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Require decoding proofs to reject changed bytes from the production assembly."""
from dataclasses import dataclass
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

from generate_program import inspect_object, rocq_source


@dataclass(frozen=True)
class Mutation:
    name: str
    before: str
    after: str
    module: str
    lemma: str


MUTATIONS = (
    Mutation('return-code', '    mov eax, 2\n', '    mov eax, 3\n',
             'X86OversizedBody', 'size_return_invalid_step'),
    Mutation('size-bound', '    cmp edi, 1025\n', '    cmp edi, 1024\n',
             'X86Decoded', 'decode_entry_control'),
)


def lemma_range(source, name):
    lines = source.splitlines()
    starts = [index for index, line in enumerate(lines, 1)
              if re.match(rf'^(?:Lemma|Theorem)\s+{re.escape(name)}\b', line)]
    if len(starts) != 1:
        raise ValueError(f'expected one proof of {name}')
    start = starts[0]
    for index in range(start, len(lines) + 1):
        if re.search(r'\bQed\.', lines[index - 1]):
            return start, index
    raise ValueError(f'no Qed for {name}')


def rejected_lemma(report, module, bounds):
    errors = re.findall(r'File "([^"]+)", line (\d+), characters \d+-\d+:\s*Error:',
                        report)
    if not errors:
        return False
    filename, line = errors[-1]
    return (Path(filename).name == module + '.v' and
            bounds[0] <= int(line) <= bounds[1] and
            ('Unable to unify' in report or 'Not convertible' in report))


def check_mutation(mutation, compcert, llvm_proofs, checked, modules):
    proof = checked / 'proof'
    source = (proof / 'permute.S').read_text()
    if source.count(mutation.before) != 1:
        raise ValueError(f'{mutation.name}: expected one assembly instruction')
    report = checked / 'mutations' / mutation.name
    report.mkdir(parents=True)
    with tempfile.TemporaryDirectory(prefix=f'x86-{mutation.name}-') as temporary:
        work = Path(temporary)
        for module in modules:
            shutil.copyfile(proof / (module + '.v'), work / (module + '.v'))
        assembly = work / 'permute.S'
        assembly.write_text(source.replace(mutation.before, mutation.after))
        object_file = work / 'permute.o'
        subprocess.run(['clang', '-Wa,-L', '-c', str(assembly), '-o', str(object_file)],
                       check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        program = inspect_object(object_file)
        generated = rocq_source(program)
        if generated == (proof / 'X86Program.v').read_text():
            raise AssertionError(f'{mutation.name}: assembly mutation did not change the bytes')
        (work / 'X86Program.v').write_text(generated)
        for name in ('permute.S', 'permute.o', 'X86Program.v'):
            shutil.copyfile(work / name, report / name)
        (report / 'permute.bin').write_bytes(program.code)
        bounds = lemma_range((work / (mutation.module + '.v')).read_text(), mutation.lemma)
        paths = ['-R', str(compcert), 'compcert', '-Q', str(llvm_proofs), '',
                 '-Q', str(work), 'X86']
        # Compile the manifest prefix from source. No compiled file from the
        # original program is present in this directory.
        for module in modules[:modules.index(mutation.module) + 1]:
            result = subprocess.run(['coqc', *paths, module + '.v'], cwd=work,
                                    text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT)
            (report / (module + '.log')).write_text(result.stdout)
            if result.returncode:
                if module != mutation.module or not rejected_lemma(result.stdout, module, bounds):
                    raise RuntimeError(f'{mutation.name}: unexpected failure in {module}\n'
                                       f'{result.stdout[-12000:]}')
                (report / 'rejection.txt').write_text(
                    f'Changed object bytes rejected by {module}.{mutation.lemma}\n')
                print(f'{mutation.name}: changed object bytes rejected by '
                      f'{module}.{mutation.lemma}', flush=True)
                return
        raise AssertionError(f'{mutation.name}: changed object bytes passed the decoding proof')


def main(compcert, llvm_proofs, checked):
    modules = tuple((checked / 'modules.txt').read_text().splitlines())
    if any(not (checked / 'proof' / (module + '.vo')).is_file() for module in modules):
        raise ValueError('the original proof modules must compile before the mutation tests')
    for mutation in MUTATIONS:
        check_mutation(mutation, compcert, llvm_proofs, checked, modules)


if __name__ == '__main__':
    if len(sys.argv) != 4:
        sys.exit('usage: test_proofs.py COMPCERT_PROOFS LLVM_PROOFS CHECKED_OUTPUT')
    main(*(Path(argument).resolve() for argument in sys.argv[1:]))
