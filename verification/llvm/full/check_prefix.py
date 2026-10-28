#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check the imported entry block and initialization loop, including mutations."""
from pathlib import Path
import shutil
import subprocess
import sys

import check

CANDIDATE = ('Normalize', 'FullNormalize', 'NormalizeTests', 'FullCandidate',
             'FullProgram', 'FullCFG')
PROOFS = ('Entry', 'Index', 'Initialize', 'Prefix')
CLAIMS = check.CLAIMS + (
    'Entry.entry_runs', 'Entry.entry_related',
    'Index.index_add', 'Index.index_eq', 'Index.index_gep', 'Index.extend_word',
    'Initialize.initialize_step', 'Initialize.initialize_loop',
    'Initialize.initialize_array',
    'Prefix.initialized_prefix', 'Prefix.initialized_prefix_semantics',
)

# Each mutation changes the actual LLVM source. Parse and import it again.
# The normalizer must accept it, then the affected proof must fail.
MUTATIONS = (
    ('entry_store', 'store i32 0, ptr %v7,', 'store i32 1, ptr %v7,', 'Entry'),
    ('size_limit', 'icmp ugt i32 %v1, 1024', 'icmp ugt i32 %v1, 1023', 'Entry'),
    ('loop_store', 'store i32 0, ptr %arrayidx11,',
     'store i32 1, ptr %arrayidx11,', 'Initialize'),
    ('loop_phi', 'phi i64 [ 0, %if.end10.preheader ]',
     'phi i64 [ 1, %if.end10.preheader ]', 'Initialize'),
    ('loop_increment', '%indvars.iv.next = add nuw nsw i64 %indvars.iv, 1',
     '%indvars.iv.next = add nuw nsw i64 %indvars.iv, 2', 'Initialize'),
)


def run(args, directory, log, expected_failure=False):
    path = directory / log
    with path.open('w') as stream:
        try:
            result = subprocess.run(args, cwd=directory, text=True,
                                    stdout=stream, stderr=subprocess.STDOUT,
                                    timeout=120)
        except subprocess.TimeoutExpired:
            stream.write('\nProof check timed out.\n')
            stream.flush()
            print(f'{directory.name}: {log}\n{path.read_text()[-8000:]}',
                  file=sys.stderr, flush=True)
            raise
    output = path.read_text()
    if expected_failure:
        if result.returncode == 0 or 'Error:' not in output:
            raise AssertionError(f'{directory.name}: expected proof rejection in {log}')
        if any(message in output for message in
               ('Cannot find', 'Unable to locate', 'inconsistent assumptions',
                'Unknown logical path', 'User interrupt', 'Anomaly')):
            raise AssertionError(f'{directory.name}: dependency or tool failure in {log}')
    elif result.returncode != 0:
        raise RuntimeError(f'{directory.name}: {log}\n{output}')


def mutations(compcert, importer, proofs=PROOFS, cases=MUTATIONS,
              dependencies=check.MODULES):
    base = Path.cwd()
    source = (base / 'permute.ll').read_text()
    root = base / 'mutations'
    root.mkdir(exist_ok=True)
    variants = [('comment_control', source + '\n; proof control\n', None)]
    for name, before, after, failure in cases:
        if source.count(before) != 1:
            raise AssertionError(f'{name}: expected one mutation site')
        variants.append((name, source.replace(before, after), failure))
    for name, variant, failure in variants:
        directory = root / name
        if directory.exists():
            shutil.rmtree(directory)
        directory.mkdir()
        for module in dependencies + CANDIDATE + proofs:
            relative = Path(module.replace('.', '/') + '.v')
            (directory / relative).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(base / relative, directory / relative)
        for module in dependencies:
            relative = Path(module.replace('.', '/') + '.vo')
            shutil.copy2(base / relative, directory / relative)
        (directory / 'permute.ll').write_text(variant)
        run(['opt', '-passes=verify', '-disable-output', 'permute.ll'],
            directory, 'verify.log')
        run(['frontend', '-op', '.', 'permute.ll'], directory, 'parse.log')
        run([sys.executable, str(importer), 'permute.v.ast', 'FullCandidate.v'],
            directory, 'import.log')
        coqc = ['coqc', '-time', '-R', str(compcert), 'compcert', '-Q', '.', '']
        for module in CANDIDATE + proofs:
            run(coqc + [module + '.v'], directory, module + '.log', module == failure)
            if module == failure:
                break
        print(f'{name}: ' + ('proof rejected' if failure else 'proof passed'), flush=True)
    (base / 'mutations.txt').write_text('\n'.join(
        f'{name}: {"rejected in " + failure if failure else "passed"}'
        for name, _, failure in variants) + '\n')


if __name__ == '__main__':
    if len(sys.argv) != 4:
        sys.exit('usage: check_prefix.py COMPCERT ASSUMPTION_POLICY IMPORTER')
    compcert, policy, importer = (Path(arg).resolve() for arg in sys.argv[1:])
    check.check(compcert, policy, check.MODULES + CANDIDATE + PROOFS, CLAIMS)
    mutations(compcert, importer)
