#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check the memory proofs, regression cases, and PR #6 assumption policy."""
from pathlib import Path
import runpy
import subprocess
import sys

MODULES = ('MemoryRelation', 'WordMemory', 'CellRelation', 'MemoryTests',
           'Control', 'Instructions')
CLAIMS = (
    'MemoryRelation.read_four_correct',
    'MemoryRelation.write_four_correct',
    'WordMemory.load_word_correct',
    'WordMemory.store_word_correct',
    'CellRelation.related_load',
    'CellRelation.related_store',
    'Control.block_path_sound',
    'Control.block_steps_sound',
    'Instructions.runs_expression_gep',
    'Instructions.runs_instruction_load',
    'Instructions.runs_instruction_read',
    'Instructions.runs_instruction_store',
    'Instructions.runs_block_no_phis',
    'Instructions.runs_block_single_phi',
)


def check_kernel(report, expected):
    """Check the full imported context, including unused library axioms."""
    lines = [line.strip() for line in report.splitlines() if line.strip()]
    header = ['CONTEXT SUMMARY', '===============',
              '* Theory: Set is predicative',
              '* Theory: Rewrite rules are not allowed', '* Axioms:']
    tail = ['* Constants/Inductives relying on type-in-type: <none>',
            '* Constants/Inductives relying on unsafe (co)fixpoints: <none>',
            '* Inductives whose positivity is assumed: <none>']
    if lines[:5] != header or lines[-3:] != tail:
        raise ValueError('kernel context has missing sections or unsafe typing settings')
    names = lines[5:-3]
    actual = frozenset(names)
    if len(names) != len(actual) or actual != expected:
        raise ValueError(f'kernel axioms differ from the dependency baseline: '
                         f'{sorted(actual ^ expected)}')
    return actual


def check(compcert, policy_path, modules=MODULES, claims=CLAIMS,
          context_file='kernel-axioms.txt'):
    coqc = ['coqc', '-R', str(compcert), 'compcert', '-Q', '.', '']
    for module in modules:
        subprocess.run(coqc + [module.replace('.', '/') + '.v'], check=True)
    statements = [f'Require {module}.' for module in modules]
    for claim in claims:
        # The closed True goal only prints a report delimiter.
        statements += ['Goal True.', f'idtac "{claim}".', 'exact I.', 'Qed.',
                       f'Print Assumptions {claim}.']
    Path('Assumptions.v').write_text('\n'.join(statements) + '\n')
    report = subprocess.run(coqc + ['Assumptions.v'], check=True,
                            text=True, stdout=subprocess.PIPE).stdout
    Path('assumptions.txt').write_text(report)
    policy = runpy.run_path(str(policy_path))
    checked = policy['check'](report, expected=claims)
    try:
        policy['check'](report + '\nUnproved.claim : False\n', expected=claims)
    except ValueError:
        pass
    else:
        raise AssertionError('assumption policy accepted an added axiom')
    result = subprocess.run(
        ['coqchk', '-silent', '-o', '-R', str(compcert), 'compcert',
         '-Q', '.', '', *modules], check=True, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    Path('kernel-context.txt').write_text(result.stderr)
    expected = frozenset(Path(context_file).read_text().splitlines())
    axioms = check_kernel(result.stderr, expected)
    for bad in [result.stderr.replace('* Axioms:', '* Axioms:\n    Unproved.claim'),
                result.stderr.replace('type-in-type: <none>', 'type-in-type: Bad.claim')]:
        try:
            check_kernel(bad, expected)
        except ValueError:
            pass
        else:
            raise AssertionError('kernel check accepted an axiom or unsafe typing')
    print(f'{len(checked)} claims pass the assumption policy; '
          f'{len(axioms)} allowed axioms in the kernel context')


if __name__ == '__main__':
    if len(sys.argv) != 3:
        sys.exit('usage: check.py COMPCERT_PROOF_DIRECTORY ASSUMPTION_POLICY')
    check(Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve())
