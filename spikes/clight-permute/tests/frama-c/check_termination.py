#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Require proof rejection of faulty counter and permutation updates."""
import argparse
import json
from pathlib import Path
import re
import shutil

import annotate
import run


def check(config, output):
    output.mkdir(parents=True, exist_ok=False)
    source = annotate.annotate(annotate.SOURCE.read_text(), 'termination')
    cases = (
        ('baseline', source, None),
        ('parentheses', source.replace('v3[v10] = v12;', 'v3[v10] = (v12);'), None),
        ('missing-decrement', source.replace('proof_steps--;', ';'),
         'permute_loop_variant_6'),
        ('wrong-swap', source.replace('v3[v11] = v3[v10];', 'v3[v11] = v11;'),
         'permute_assert_swap_endpoints'),
    )
    rows = []
    for name, text, failed_property in cases:
        if name != 'baseline' and text == source:
            raise ValueError(f'{name}: missing mutation anchor')
        directory = output / name
        directory.mkdir()
        path = directory / 'annotated.c'
        path.write_text(text)
        command = run.proof_command(shutil.which('frama-c'), config, path,
                                    directory, 10, 'termination')
        manifest = {'command': command, 'source_sha256': run.digest(path),
                    'config_sha256': run.digest(config)}
        (directory / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
        code = run.execute(command, directory / 'wp.log')
        report = directory / 'goals.json'
        if code or not report.exists():
            raise ValueError(f'{name}: Frama-C failed before producing a report')
        goals = json.loads(report.read_text())
        scheduled = re.findall(r'\[wp\] (\d+) goals scheduled', (directory / 'wp.log').read_text())
        properties = {g.get('property') for g in goals}
        # A downstream assertion can use earlier assertions as premises.
        # Check the whole component, including those earlier obligations.
        expected = run.source_properties(source)
        if (len(scheduled) != 1 or int(scheduled[0]) != len(goals)
                or properties != expected
                or len({g.get('goal') for g in goals}) != len(goals)
                or any(g.get('smoke') is not False or g.get('function') !=
                       (None if 'lemma_' in g['property'] else 'permute') for g in goals)):
            raise ValueError(f'{name}: unexpected goal report')
        pending = [g['property'] for g in goals if g.get('verdict') != 'valid'
                   or g.get('passed') is not True or g.get('proved') != g.get('subgoals', 1)]
        matched = not pending if failed_property is None else failed_property in pending
        row = {'name': name, 'goals': len(goals), 'pending': sorted(set(pending)),
               'expected_failed_property': failed_property, 'matched': matched}
        rows.append(row)
        print(json.dumps(row), flush=True)
    result = {'pass': all(row['matched'] for row in rows), 'results': rows,
              'production_sha256': run.digest(annotate.SOURCE)}
    (output / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
    return result['pass']


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    raise SystemExit(0 if check(args.config.resolve(), args.output.resolve()) else 1)
