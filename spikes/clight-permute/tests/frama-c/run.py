#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Run all WP obligations with free SMT solvers; reject any unproved goal."""
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

import annotate
import composition

ROOT = annotate.ROOT


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def why3_cvc5_version(output):
    if not re.match(r'^cvc5 [0-9]+\.[0-9]+\.[0-9]+\n', output):
        raise ValueError('unexpected CVC5 version header')
    return output.replace('cvc5 ', 'This is cvc5 version ', 1)


def write_cvc5_wrapper(path, executable, version_output):
    # Change only the version header which Why3 1.8.2 parses. Solver calls
    # replace this process with the exact binary and original arguments.
    path.write_text('#!' + sys.executable + '\n'
                    '# SPDX-License-Identifier: GPL-3.0-or-later\n'
                    'import os, sys\n'
                    "if sys.argv[1:] == ['--version']:\n"
                    '    sys.stdout.write(' + repr(why3_cvc5_version(version_output)) + ')\n'
                    'else:\n'
                    '    os.execv(' + repr(executable) + ', [' + repr(executable) + '] + sys.argv[1:])\n')
    path.chmod(0o755)


def execute(command, log, *, env=None):
    with log.open('w') as output:
        return subprocess.run(command, cwd=ROOT, env=env, stdout=output,
                              stderr=subprocess.STDOUT, check=False).returncode


def required_postconditions(mode):
    if mode == 'termination':
        return []
    if mode == 'target':
        return ['target_initialized', 'target_definition']
    if mode == 'trace':
        return ['trace_bounds', 'trace_replay', 'trace_changes_values']
    if mode == 'status':
        return ['status']
    if mode == 'success':
        return ['success_reachable', 'blocked_unreachable', 'success_data',
                'success_info', 'blocked_info']
    contract = annotate.CONTRACT if mode == 'full' else annotate.MEMORY_CONTRACT
    return re.findall(r'ensures ([a-z_]+):', contract)


def source_properties(source):
    """Require each named obligation and every loop in the actual source."""
    properties = set()
    for checked, name in re.findall(r'\b(check\s+)?lemma\s+(\w+)\{', source):
        properties.add(('check_lemma_' if checked else 'lemma_') + name)
    for kind in ('ensures', 'assert', 'loop invariant'):
        counts = Counter()
        for name in re.findall(r'\b' + kind + r'\s+(\w+):', source):
            counts[name] += 1
            suffix = '' if counts[name] == 1 else '_' + str(counts[name])
            properties.add('permute_' + kind.replace(' ', '_') + '_' + name + suffix)
    for kind in ('loop assigns', 'loop variant'):
        for index in range(source.count(kind)):
            suffix = '' if index == 0 else '_' + str(index + 1)
            properties.add('permute_' + kind.replace(' ', '_') + suffix)
    return properties


def report_errors(results, scheduled, mode, automatic_termination=False, *, lemma_names=(), source=None):
    errors = []
    if not results:
        errors.append('empty goal report')
    if scheduled != len(results):
        errors.append('goal count differs from the scheduled count')
    identifiers = [goal.get('goal') for goal in results]
    if None in identifiers or len(set(identifiers)) != len(identifiers):
        errors.append('missing or duplicate goal identifier')
    properties = {goal.get('property', '') for goal in results}
    required = {'permute_ensures_' + name for name in required_postconditions(mode)}
    lemma_properties = {'lemma_' + name for name in lemma_names}
    if source is not None:
        expected = source_properties(source)
        required |= expected
        lemma_properties |= {p for p in expected if p.startswith(('lemma_', 'check_lemma_'))}
    required |= lemma_properties
    missing = sorted(required - properties)
    if missing:
        errors.append('missing properties: ' + ', '.join(missing))
    # WP can discharge termination during generation and omit it from JSON.
    if mode not in ('safety', 'target', 'trace', 'success') and 'permute_terminates' not in properties and not automatic_termination:
        errors.append('missing termination obligation or automatic result')
    categories = ['permute_loop_assigns', 'permute_loop_invariant_', 'permute_loop_variant']
    if mode not in ('termination', 'target', 'trace', 'status', 'success'):
        categories += ['permute_assigns', 'permute_assert_rte_mem_access',
                       'permute_assert_rte_initialization']
    for category in categories:
        if not any(prop.startswith(category) for prop in properties):
            errors.append('missing property category: ' + category)
    for goal in results:
        is_lemma = goal.get('property') in lemma_properties
        expected_function = None if is_lemma else 'permute'
        if goal.get('function') != expected_function or goal.get('smoke') is not False:
            errors.append('unexpected function or smoke goal: ' + str(goal.get('goal')))
        subgoals = goal.get('subgoals', 1)
        if (goal.get('verdict') != 'valid' or goal.get('passed') is not True
                or type(subgoals) is not int or subgoals < 1
                or type(goal.get('proved')) is not int
                or goal.get('proved') != subgoals):
            errors.append('unproved goal: ' + str(goal.get('goal')))
    return errors


def proof_command(executable, config, source, result_dir, timeout, mode='full'):
    # Parse the function before applying the RTE function selector. Select
    # provers in the stage that runs WP, after the local Why3 configuration.
    configuration = ['-wp-why3-config', str(config), '-wp-no-why3-detect']
    logical = mode in ('termination', 'target', 'trace', 'status', 'success')
    checks = [] if logical else ['-wp-rte', '-rte-initialized=permute']
    # A native solver can prove the whole goal when a tactic leaves a child
    # open. The same strict report check applies to either proof route.
    provers = 'tip,cvc5,z3'
    strategy = ['-wp-strategy', 'ProofSMT'] if logical else []
    return [str(executable), *configuration, '-machdep', 'x86_64',
            '-cpp-extra-args=-I' + str(ROOT), str(source), '-then',
            *configuration, '-wp-prover', provers,
            '-wp', *checks, *strategy,
            '-wp-model', 'Typed+ref', '-wp-split', '-wp-auto-depth', '12', '-wp-par', '4',
            '-wp-timeout', str(timeout), '-wp-cache', 'none', '-wp-proof-trace',
            '-wp-out', str(result_dir / 'obligations'),
            '-wp-session', str(result_dir / 'session'),
            '-wp-report-json', str(result_dir / 'goals.json')]


def run_component(executable, config, result_dir, source, mode, timeout):
    result_dir.mkdir(parents=True, exist_ok=False)
    path = result_dir / 'annotated.c'
    path.write_text(source)
    command = proof_command(executable, config, path, result_dir, timeout, mode)
    files = ('annotate.py', 'termination.py', 'target.py', 'trace_annotations.py',
             'lemmas.acsl', 'trace.acsl', 'status.c', 'success.c', 'composition.py', 'run.py')
    manifest = {'source_sha256': digest(annotate.SOURCE),
                'annotated_sha256': digest(path), 'config_sha256': digest(config),
                'annotation_mode': mode, 'command': command,
                'annotation_files': {name: digest(Path(__file__).with_name(name)) for name in files},
                'requirements': annotate.requirements(source)}
    (result_dir / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    returncode = execute(command, result_dir / 'wp.log')
    report = result_dir / 'goals.json'
    results = json.loads(report.read_text()) if report.exists() else []
    log = (result_dir / 'wp.log').read_text()
    counts = re.findall(r'\[wp\] (\d+) goals scheduled', log)
    scheduled = int(counts[0]) if len(counts) == 1 else None
    automatic = bool(re.search(r'^  Terminating:\s+1\s*$', log, re.M))
    errors = report_errors(results, scheduled, mode, automatic, source=source)
    summary = {'process_returncode': returncode, 'goals': len(results),
               'verdicts': dict(Counter(g['verdict'] for g in results)),
               'unproved_goals': [g['goal'] for g in results if g.get('verdict') != 'valid'],
               'report_errors': errors, 'complete': returncode == 0 and not errors}
    (result_dir / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({'component': mode, **summary}, indent=2), flush=True)
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=int, default=5)
    parser.add_argument('--name', default='run')
    parser.add_argument('--mode', choices=('full', 'memory', 'termination', 'target', 'trace',
                                           'status', 'success'), default='full')
    args = parser.parse_args()
    if not args.name.replace('-', '').replace('_', '').isalnum() or args.timeout <= 0:
        parser.error('use a plain run name and a positive solver timeout')
    result_dir = ROOT / 'build' / 'frama-c' / args.name
    result_dir.mkdir(parents=True, exist_ok=False)
    original = annotate.SOURCE.read_text()
    modes = (composition.MODES if args.mode == 'full' else
             ('safety', 'termination') if args.mode == 'memory' else (args.mode,))
    sources = {mode: annotate.annotate(original, mode) for mode in modes}
    composition.check_sources(original, sources)
    coverage = composition.check(original, sources) if args.mode == 'full' else None
    executables = {name: str(Path(shutil.which(name)).resolve())
                   for name in ('frama-c', 'why3', 'z3', 'cvc5')}
    # Do not inspect user-wide prover configuration or discover other provers.
    prover_bin = result_dir / 'prover-bin'
    prover_bin.mkdir()
    (prover_bin / 'z3').symlink_to(executables['z3'])
    version_output = subprocess.check_output([executables['cvc5'], '--version'], text=True)
    (result_dir / 'cvc5-version.txt').write_text(version_output)
    write_cvc5_wrapper(prover_bin / 'cvc5', executables['cvc5'], version_output)
    environment = dict(os.environ, PATH=str(prover_bin))
    detected_config = result_dir / 'why3-detected.conf'
    config = result_dir / 'why3.conf'
    detect = [executables['why3'], 'config', '-C', str(detected_config), 'detect']
    if execute(detect, result_dir / 'detect.log', env=environment):
        raise SystemExit('SMT solver configuration failed; see detect.log')
    config_text = subprocess.check_output(
        [executables['why3'], 'config', '-C', str(detected_config), 'show'], text=True)
    config.write_text(config_text)
    manifest = {'source': str(annotate.SOURCE), 'source_sha256': digest(annotate.SOURCE),
                'annotation_generator_sha256': digest(Path(annotate.__file__)),
                'runner_sha256': digest(Path(__file__)),
                'executables': executables, 'configure': detect,
                'size_domain': 'all integers 1 <= n <= 1024',
                'annotation_mode': args.mode,
                'input_domain': 'all permutations and all initialized uint32 values'}
    (result_dir / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    components = {mode: run_component(executables['frama-c'], config,
                                     result_dir / mode, sources[mode], mode, args.timeout)
                  for mode in modes}
    scope = {'memory': 'memory safety and termination; functional contract is separate',
             'target': 'target definition and initialization; other contract clauses are separate',
             'trace': 'trace bounds, replay, and changes of values; other contract clauses are separate',
             'status': 'status is zero or one; other contract clauses are separate',
             'success': 'guarded success and blocked clauses; requires separate status and safety proofs',
             'termination': 'termination only; requires separate C safety proof',
             'full': 'full functional contract, memory safety, and termination'}[args.mode]
    summary = {'scope': scope, 'components': components,
               'source_and_domain_checked': True, 'contract_coverage': coverage,
               'complete': all(c['complete'] for c in components.values())}
    (result_dir / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))
    raise SystemExit(0 if summary['complete'] else 1)


if __name__ == '__main__':
    main()
