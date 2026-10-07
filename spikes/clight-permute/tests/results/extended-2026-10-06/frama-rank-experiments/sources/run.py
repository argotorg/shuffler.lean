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
    contract = annotate.CONTRACT if mode == 'full' else annotate.MEMORY_CONTRACT
    return re.findall(r'ensures ([a-z_]+):', contract)


def report_errors(results, scheduled, mode, automatic_termination=False):
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
    missing = sorted(required - properties)
    if missing:
        errors.append('missing postconditions: ' + ', '.join(missing))
    # WP can discharge termination during generation and omit it from JSON.
    if 'permute_terminates' not in properties and not automatic_termination:
        errors.append('missing termination obligation or automatic result')
    for category in ('permute_assigns', 'permute_loop_assigns',
                     'permute_loop_invariant_', 'permute_loop_variant',
                     'permute_assert_rte_mem_access', 'permute_assert_rte_initialization'):
        if not any(prop.startswith(category) for prop in properties):
            errors.append('missing property category: ' + category)
    for goal in results:
        if goal.get('function') != 'permute' or goal.get('smoke') is not False:
            errors.append('unexpected function or smoke goal: ' + str(goal.get('goal')))
        if (goal.get('verdict') != 'valid' or goal.get('passed') is not True
                or goal.get('proved') != 1):
            errors.append('unproved goal: ' + str(goal.get('goal')))
    return errors


def proof_command(executable, config, source, result_dir, timeout):
    # Parse the function before applying the RTE function selector. Select
    # provers in the stage that runs WP, after the local Why3 configuration.
    configuration = ['-wp-why3-config', str(config), '-wp-no-why3-detect']
    return [str(executable), *configuration, '-machdep', 'x86_64',
            '-cpp-extra-args=-I' + str(ROOT), str(source), '-then',
            *configuration, '-wp-prover', 'tip,cvc5,z3',
            '-wp', '-wp-rte', '-rte-initialized=permute',
            '-wp-model', 'Typed+ref', '-wp-split', '-wp-par', '4',
            '-wp-timeout', str(timeout), '-wp-cache', 'none', '-wp-proof-trace',
            '-wp-out', str(result_dir / 'obligations'),
            '-wp-session', str(result_dir / 'session'),
            '-wp-report-json', str(result_dir / 'goals.json')]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=int, default=5)
    parser.add_argument('--name', default='run')
    parser.add_argument('--mode', choices=('full', 'memory'), default='full')
    args = parser.parse_args()
    if not args.name.replace('-', '').replace('_', '').isalnum() or args.timeout <= 0:
        parser.error('use a plain run name and a positive solver timeout')
    annotate.main(args.mode)
    result_dir = ROOT / 'build' / 'frama-c' / args.name
    result_dir.mkdir(parents=True, exist_ok=False)
    shutil.copyfile(annotate.OUT / 'annotated.c', result_dir / 'annotated.c')
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
    goals = result_dir / 'goals.json'
    command = proof_command(executables['frama-c'], config,
                            result_dir / 'annotated.c', result_dir, args.timeout)
    manifest = {'source': str(annotate.SOURCE), 'source_sha256': digest(annotate.SOURCE),
                'annotated_sha256': digest(result_dir / 'annotated.c'),
                'annotation_generator_sha256': digest(Path(annotate.__file__)),
                'runner_sha256': digest(Path(__file__)),
                'executables': executables, 'configure': detect, 'command': command,
                'size_domain': 'all integers 1 <= n <= 1024',
                'annotation_mode': args.mode,
                'input_domain': 'all permutations and all initialized uint32 values'}
    (result_dir / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    returncode = execute(command, result_dir / 'wp.log')
    if not goals.exists():
        raise SystemExit('WP produced no goal report; see wp.log')
    results = json.loads(goals.read_text())
    pending = [goal for goal in results if goal.get('verdict') != 'valid']
    log_text = (result_dir / 'wp.log').read_text()
    scheduled_counts = re.findall(r'\[wp\] (\d+) goals scheduled', log_text)
    scheduled = int(scheduled_counts[0]) if len(scheduled_counts) == 1 else None
    automatic_termination = bool(re.search(r'^  Terminating:\s+1\s*$', log_text, re.M))
    errors = report_errors(results, scheduled, args.mode, automatic_termination)
    summary = {'process_returncode': returncode,
               'goals': len(results), 'verdicts': dict(Counter(g['verdict'] for g in results)),
               'unproved_goals': [g['goal'] for g in pending],
               'report_errors': errors,
               'complete': returncode == 0 and not errors}
    (result_dir / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))
    raise SystemExit(0 if summary['complete'] else 1)


if __name__ == '__main__':
    main()
