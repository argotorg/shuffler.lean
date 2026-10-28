#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Compile an isolated x86 proof copy and check its assumptions and kernel context."""
from pathlib import Path
import re
import runpy
import shutil
import subprocess
import sys

# Keep this list in dependency order. A source file omitted here is an error.
MODULES = (
    'X86Program', 'X86Layout', 'X86Arithmetic', 'X86Flags', 'X86Control',
    'X86Instructions', 'X86Data', 'X86Sail', 'X86Compare', 'X86Alu',
    'X86Memory', 'X86MemoryStore', 'X86MemoryInstructions', 'X86ABI', 'X86CodeMemory',
    'X86MemoryFrame', 'X86FetchAddress', 'X86Decode', 'X86DecodeReplay', 'X86Decoder',
    'X86Entry', 'X86Execution', 'X86Stack', 'X86StackMemory', 'X86Address',
    'X86CellAddress', 'X86StackLayout', 'X86StackFrame', 'X86Decoded', 'X86ArrayDecode',
    'X86Prologue', 'X86SavedFrame', 'X86Initialize', 'X86UsedZero', 'X86EmptyBody',
    'X86OversizedBody', 'X86Cleanup', 'X86Call', 'X86EmptyCall', 'X86OversizedCall',
    'X86CallFrame', 'X86Arguments', 'X86Size', 'X86Prefix', 'X86ValidationSteps',
    'X86Validation', 'X86ValidationEntry', 'X86LLVMValidation', 'X86ValidationAgreement', 'X86ValidationPass',
    'X86CheckedPrefix', 'X86NormalizeStores', 'X86FixedMemory', 'X86Normalize', 'X86FixedAgreement',
    'X86ModelTypes', 'X86FixedPrefix', 'X86MainSetup', 'X86NormalizationModel', 'X86Done',
    'X86FillSteps', 'X86Fill', 'X86LLVMFill', 'X86LLVMExchangePermutation', 'X86LLVMExchangeBlocked',
    'X86LLVMExchangeSuccess', 'X86SearchSteps', 'X86Search', 'X86SearchLoop', 'X86SearchModel',
    'X86FillAgreement', 'X86NormalizedPrefix', 'X86MainPrefix', 'X86ChoiceSteps', 'X86Choice',
    'X86ChoiceLoop', 'X86ChoiceModel', 'X86ChoiceAgreement', 'X86PermuteSwap', 'X86ExchangeSteps',
    'X86LoopModel', 'X86Exchange', 'X86ExchangeAgreement', 'X86MainLoopCore', 'X86MainLoop',
    'X86NonemptyCall',
)
REQUIRED_CLAIMS = frozenset({
    'X86.X86Instructions.fetch_execute_decoded',
    'X86.X86DecodeReplay.decode_instruction_trace',
    'X86.X86Compare.execute_cmp32_registers',
    'X86.X86Execution.framed_instruction',
    'X86.X86StackMemory.execute_push64',
    'X86.X86StackMemory.execute_ret',
    'X86.X86EmptyCall.empty_call_agrees',
    'X86.X86EmptyCall.empty_call_run_agrees',
    'X86.X86OversizedCall.oversized_call_agrees',
    'X86.X86OversizedCall.oversized_call_run_agrees',
    'X86.X86CellAddress.scaled_word_cell_address',
    'X86.X86CallFrame.cell_store_frame',
    'X86.X86UsedZero.used_zero_preheader',
    'X86.X86Arguments.call_body_arguments',
    'X86.X86Size.nonempty_size_path',
    'X86.X86Prefix.initialized_prefix_agrees',
    'X86.X86Validation.validation_iteration',
    'X86.X86ValidationEntry.validation_preheader',
    'X86.X86LLVMValidation.llvm_validation_step',
    'X86.X86ValidationAgreement.validation_iteration_agrees',
    'X86.X86ValidationAgreement.validation_loop_agrees',
    'X86.X86ValidationPass.validation_pass_agrees',
    'X86.X86CheckedPrefix.checked_prefix_agrees',
    'X86.X86NormalizeStores.normalize_stores_frame',
    'X86.X86FixedMemory.fixed_store_step',
    'X86.X86Normalize.normalize_llvm_iteration',
    'X86.X86Normalize.normalize_machine_iteration',
    'X86.X86Normalize.normalize_preheader',
    'X86.X86FixedAgreement.fixed_pass_agrees',
    'X86.X86ModelTypes.model_target_uint',
    'X86.X86FixedPrefix.fixed_prefix_agrees',
    'X86.X86MainSetup.main_setup_path',
    'X86.X86NormalizationModel.model_normalization_fill',
    'X86.X86NormalizedPrefix.normalized_prefix_agrees',
    'X86.X86MainPrefix.main_prefix_agrees',
    'X86.X86Done.done_path',
    'X86.X86FillSteps.fill_mark_used',
    'X86.X86Fill.fill_machine_assign',
    'X86.X86LLVMFill.llvm_fill_assignment_stores',
    'X86.X86FillAgreement.fill_pass_agrees',
    'X86.X86LLVMExchangePermutation.llvm_exchange_equal_choice_stores',
    'X86.X86LLVMExchangeBlocked.llvm_exchange_blocked_choice_stores',
    'X86.X86LLVMExchangeSuccess.llvm_successful_exchange_stores',
    'X86.X86SearchSteps.search_compare_step',
    'X86.X86Search.search_probe',
    'X86.X86SearchLoop.search_found_loop',
    'X86.X86SearchModel.first_free_machine_search',
    'X86.X86ChoiceSteps.choice_decrement',
    'X86.X86Choice.choice_scan_iteration',
    'X86.X86ChoiceLoop.choice_descending',
    'X86.X86ChoiceModel.choose_machine_permutation',
    'X86.X86ChoiceAgreement.main_choose_agrees',
    'X86.X86PermuteSwap.permute_swap_block',
    'X86.X86ExchangeSteps.exchange_output_store',
    'X86.X86LoopModel.model_initial_budget',
    'X86.X86LoopModel.model_permute_normalized',
    'X86.X86Exchange.exchange_equal',
    'X86.X86Exchange.exchange_exhausted',
    'X86.X86Exchange.exchange_success',
    'X86.X86ExchangeAgreement.equal_exchange_agrees',
    'X86.X86ExchangeAgreement.blocked_exchange_agrees',
    'X86.X86ExchangeAgreement.successful_exchange_agrees',
    'X86.X86MainLoopCore.main_loop_from_exchange_agreements',
    'X86.X86MainLoop.main_loop_agrees',
    'X86.X86MainLoop.main_loop_nonempty_agrees',
    'X86.X86NonemptyCall.nonempty_call_agrees',
    'X86.X86NonemptyCall.nonempty_call_run_agrees',
})
DEPENDENCIES = ('ArchSemX86.X86Inst', 'FullContract')
SUPPORT = ('permute.S', 'generate_program.py', 'test_program.py')
NAME = r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)+"


def source_modules(source, modules=MODULES):
    actual = {path.stem for path in source.glob('X86*.v')}
    if len(modules) != len(set(modules)) or actual != set(modules):
        raise ValueError(f'module list differs from source files: {sorted(actual ^ set(modules))}')
    return tuple(modules)


def declared_claims(module, text):
    names = re.findall(r'^(?:Lemma|Theorem|Corollary|Proposition|Fact|Remark|Example)\s+([\w\']+)',
                       text, re.MULTILINE)
    if not names:
        raise ValueError(f'no named proofs in {module}')
    if len(names) != len(set(names)):
        raise ValueError(f'duplicate claim in {module}')
    return tuple(f'X86.{module}.{name}' for name in names)


def check_kernel(report, expected):
    lines = [line.strip() for line in report.splitlines() if line.strip()]
    header = ['CONTEXT SUMMARY', '===============',
              '* Theory: Set is predicative', '* Theory: Rewrite rules are not allowed']
    tail = ['* Constants/Inductives relying on type-in-type: <none>',
            '* Constants/Inductives relying on unsafe (co)fixpoints: <none>',
            '* Inductives whose positivity is assumed: <none>']
    if lines[:4] != header or lines[-3:] != tail:
        raise ValueError('kernel context has missing sections or unsafe typing settings')
    section = lines[4:-3]
    if section == ['* Axioms: <none>']:
        names = []
    elif len(section) >= 2 and section[0] == '* Axioms:':
        names = section[1:]
    else:
        raise ValueError('kernel context has missing sections')
    if any(re.fullmatch(NAME, name) is None for name in names):
        raise ValueError('invalid kernel axiom name')
    if len(names) != len(set(names)):
        raise ValueError('duplicate kernel axiom')
    actual = frozenset(names)
    if actual != expected:
        raise ValueError(f'kernel axioms differ from the dependency baseline: '
                         f'{sorted(actual ^ expected)}')
    return actual


def command(arguments, *, cwd, log, stderr_log=None):
    result = subprocess.run(arguments, cwd=cwd, text=True,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE if stderr_log is not None else subprocess.STDOUT)
    log.write_text(result.stdout)
    if stderr_log is not None:
        stderr_log.write_text(result.stderr)
    if result.returncode:
        diagnostic = result.stdout + (result.stderr or '')
        raise RuntimeError(f'{arguments[0]} failed; see {log}\n{diagnostic[-12000:]}')
    return result.stdout


def check(compcert, llvm_proofs, policy_path, output):
    source = Path(__file__).resolve().parent
    modules = source_modules(source)
    if output.exists() and any(output.iterdir()):
        raise ValueError(f'output directory is not empty: {output}')
    proof = output / 'proof'
    proof.mkdir(parents=True)
    for filename in tuple(f'{module}.v' for module in modules) + SUPPORT:
        shutil.copyfile(source / filename, proof / filename)
    claims = tuple(claim for module in modules
                   for claim in declared_claims(module, (proof / f'{module}.v').read_text()))
    if not REQUIRED_CLAIMS <= set(claims):
        raise ValueError(f'missing required claims: {sorted(REQUIRED_CLAIMS - set(claims))}')
    (output / 'theorems.txt').write_text('\n'.join(claims) + '\n')
    (output / 'modules.txt').write_text('\n'.join(modules) + '\n')
    command([sys.executable, 'test_program.py'], cwd=proof, log=output / 'byte-tests.txt')
    command(['clang', '-Wa,-L', '-c', 'permute.S', '-o', str(output / 'permute.o')],
            cwd=proof, log=output / 'assembly.txt')
    generator = runpy.run_path(str(proof / 'generate_program.py'))
    program = generator['inspect_object'](output / 'permute.o')
    if generator['rocq_source'](program) != (proof / 'X86Program.v').read_text():
        raise ValueError('exported object differs from the checked byte definitions')
    (output / 'permute.bin').write_bytes(program.code)
    (output / 'byte-export.txt').write_text(
        f'Exported object and binary match X86Program.v: {len(program.code)} bytes\n')
    paths = ['-R', str(compcert), 'compcert', '-Q', str(llvm_proofs), '',
             '-Q', str(proof), 'X86']
    for module in modules:
        command(['coqc', *paths, f'{module}.v'], cwd=proof, log=output / f'{module}.log')
        print(f'Checked {module}', flush=True)
    command([sys.executable, str(source / 'test_proofs.py'), str(compcert),
             str(llvm_proofs), str(output)], cwd=proof, log=output / 'mutation-tests.txt')
    # Import the pinned dependency roots so the kernel comparison includes the
    # same context as kernel-axioms.txt, including unused upstream axioms.
    statements = [f'Require {module}.' for module in DEPENDENCIES]
    statements.extend(f'Require X86.{module}.' for module in modules)
    for claim in claims:
        statements.extend(('Goal True.', f'idtac "{claim}".', 'exact I.', 'Qed.',
                           f'Print Assumptions {claim}.'))
    (proof / 'Assumptions.v').write_text('\n'.join(statements) + '\n')
    report = command(['coqc', *paths, 'Assumptions.v'], cwd=proof,
                     log=output / 'assumptions.txt', stderr_log=output / 'assumption-warnings.txt')
    policy = runpy.run_path(str(policy_path))
    checked = policy['check'](report, expected=claims)
    try:
        policy['check']('Check.unapproved\nAxioms:\nUnproved.claim : False\n',
                        expected=('Check.unapproved',))
    except ValueError:
        pass
    else:
        raise AssertionError('the assumption policy accepted an added axiom')
    result = subprocess.run(['coqchk', '-silent', '-o', *paths, 'X86.Assumptions'],
                            cwd=proof, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE)
    (output / 'kernel-context.txt').write_text(result.stderr)
    (output / 'kernel-check.txt').write_text(result.stdout)
    result.check_returncode()
    baseline = (source / 'kernel-axioms.txt').read_text()
    expected = frozenset(baseline.splitlines())
    axioms = check_kernel(result.stderr, expected)
    (output / 'kernel-axioms.txt').write_text(baseline)
    command(['coqc', '--version'], cwd=proof, log=output / 'rocq-version.txt')
    command(['clang', '--version'], cwd=proof, log=output / 'clang-version.txt')
    print(f'{len(checked)} claims pass the unchanged per-theorem policy; '
          f'{len(axioms)} dependency axioms in the checked kernel context', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 5:
        sys.exit('usage: check.py COMPCERT_PROOFS LLVM_PROOFS ASSUMPTION_POLICY OUTPUT')
    try:
        check(*(Path(argument).resolve() for argument in sys.argv[1:]))
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        sys.exit(str(error))
