#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check target initialization and source controls with the actual WP command."""
import argparse
import json
from pathlib import Path
import re
import shutil

import annotate
import run


def check(config, output):
    output.mkdir(parents=True, exist_ok=False)
    source = annotate.SOURCE.read_text()
    store = 'v4[v9] = v2[v8];'
    if source.count(store) != 1:
        raise ValueError('target-store anchor changed')
    variants = (
        ('baseline', source, True),
        ('parentheses', source.replace(store, 'v4[v9] = (v2[v8]);'), True),
        ('missing-target-store', source.replace(store, ';'), False),
    )
    executable = shutil.which('frama-c')
    if not executable:
        raise ValueError('run in the Frama-C proof shell')
    results = []
    for name, text, expected in variants:
        directory = output / name
        directory.mkdir()
        core = directory / 'core.c'
        core.write_text(text)
        annotated = directory / 'annotated.c'
        annotated.write_text(annotate.annotate(text, 'memory'))
        command = run.proof_command(executable, config, annotated, directory, 10)
        command += ['-wp-prop', 'filled_initialized,target_initialized', '-wp-print']
        manifest = {'command': command, 'core_sha256': run.digest(core),
                    'annotated_sha256': run.digest(annotated),
                    'config_sha256': run.digest(config)}
        (directory / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
        exit_code = run.execute(command, directory / 'wp.log')
        report = directory / 'goals.json'
        if exit_code or not report.exists():
            raise ValueError(f'{name}: Frama-C did not produce a goal report')
        goals = json.loads(report.read_text())
        scheduled = re.findall(r'\[wp\] (\d+) goals scheduled', (directory / 'wp.log').read_text())
        if len(scheduled) != 1 or int(scheduled[0]) != len(goals) or not goals:
            raise ValueError(f'{name}: invalid goal count')
        identifiers = [goal['goal'] for goal in goals]
        if len(identifiers) != len(set(identifiers)):
            raise ValueError(f'{name}: duplicate goal identifier')
        required = {'permute_loop_invariant_filled_initialized',
                    'permute_loop_invariant_target_initialized'}
        if not required <= {goal['property'] for goal in goals}:
            raise ValueError(f'{name}: missing initialization obligations')
        if any(g.get('function') != 'permute' or g.get('smoke') is not False for g in goals):
            raise ValueError(f'{name}: unexpected goal domain')
        pending = [g['goal'] for g in goals if g.get('verdict') != 'valid' or
                   g.get('passed') is not True or g.get('proved') != 1]
        passed = not pending
        # A changed store must fail its fill obligation, not an unrelated goal.
        met = passed if expected else (not passed and any(
            'filled_initialized_preserved' in goal for goal in pending))
        row = {'name': name, 'goals': len(goals), 'pending': pending,
               'expected_proof_pass': expected, 'expected_result_met': met}
        results.append(row)
        print(json.dumps(row), flush=True)
    result = {'pass': all(row['expected_result_met'] for row in results), 'results': results,
              'production_sha256': run.digest(annotate.SOURCE),
              'sources': {str(path): run.digest(path) for path in (
                  Path(annotate.__file__), Path(run.__file__), Path(__file__))}}
    (output / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
    return result['pass']


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    raise SystemExit(0 if check(args.config.resolve(), args.output.resolve()) else 1)
