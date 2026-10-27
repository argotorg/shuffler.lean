#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check every obligation for source-C contract mutations."""
import argparse
import json
from pathlib import Path
import shutil

import annotate
import run


def cases(mode, source):
    if mode == 'target':
        store = 'v4[v9] = v2[v8];'
        changes = (
            ('parentheses', store, 'v4[v9] = (v2[v8]);', None),
            ('wrong-source', store, 'v4[v9] = v2[v9];', 'permute_loop_invariant_filled'),
        )
    elif mode == 'trace':
        store = 'v6[v7[0U]] = v13;'
        changes = (
            ('parentheses', store, 'v6[v7[0U]] = (v13);', None),
            ('wrong-depth', store, 'v6[v7[0U]] = (v13 + 1U);', 'permute_assert_trace_written'),
            ('missing-swap', 'v2[v10] = v12;', 'v2[v10] = v2[v10];',
             'permute_assert_trace_data_swap'),
        )
    elif mode == 'status':
        store = '        return 0U;'
        changes = (
            ('parentheses', store, '        return (0U);', None),
            ('wrong-status', store, '        return 2U;', 'permute_ensures_status'),
            ('wrong-target', 'v4[v9] = v2[v8];', 'v4[v9] = v2[v9];',
             'permute_assert_collected_changed'),
        )
    elif mode == 'success':
        store = '        return 1U;'
        changes = (
            ('parentheses', store, '        return (1U);', None),
            ('false-success', store, '        return 0U;', 'permute_ensures_success_reachable'),
            ('missing-swap', 'v2[v10] = v12;', 'v2[v10] = v2[v10];',
             'permute_assert_data_exchange'),
        )
    else:
        raise ValueError('unknown contract control')
    for _, old, _, _ in changes:
        if source.count(old) != 1:
            raise ValueError('mutation anchor changed')
    return (('baseline', source, None),) + tuple(
        (name, source.replace(old, new), expected) for name, old, new, expected in changes)


def check(mode, config, output):
    output.mkdir(parents=True, exist_ok=False)
    source = annotate.annotate(annotate.SOURCE.read_text(), mode)
    rows = []
    for name, text, failed_property in cases(mode, source):
        directory = output / name
        summary = run.run_component(shutil.which('frama-c'), config, directory,
                                    text, mode, 30)
        if summary['process_returncode'] or any(
                not error.startswith('unproved goal:') for error in summary['report_errors']):
            raise ValueError(f'{name}: invalid proof report or Frama-C process failure')
        goals = json.loads((directory / 'goals.json').read_text())
        pending = {g['property'] for g in goals if g.get('verdict') != 'valid'
                   or g.get('passed') is not True or g.get('proved') != g.get('subgoals', 1)}
        matched = summary['complete'] if failed_property is None else failed_property in pending
        row = {'name': name, 'goals': len(goals), 'pending': sorted(pending),
               'expected_failed_property': failed_property, 'matched': matched}
        rows.append(row)
        print(json.dumps(row), flush=True)
    result = {'mode': mode, 'pass': all(row['matched'] for row in rows), 'results': rows,
              'production_sha256': run.digest(annotate.SOURCE),
              'control_sha256': run.digest(Path(__file__))}
    (output / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
    return result['pass']


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode', choices=('target', 'trace', 'status', 'success'), required=True)
    parser.add_argument('--config', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    raise SystemExit(0 if check(args.mode, args.config.resolve(), args.output.resolve()) else 1)
