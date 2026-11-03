#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check the actual rank library and require rejection of faulty copies."""
import argparse
import json
from pathlib import Path
import re
import shutil

import annotate
import run


def check(config, output, kind='rank'):
    output.mkdir(parents=True, exist_ok=False)
    library = Path(__file__).with_name('lemmas.acsl')
    # Include the real C so WP uses its integer-memory side conditions.
    # Select only lemma obligations; this is not a function-contract proof.
    source = library.read_text() + annotate.SOURCE.read_text()
    properties = {p for p in run.source_properties(source) if 'lemma_' in p}
    frame = (r'(\forall integer i; 0 <= i < k ==> \at(p[i],A) == \at(p[i],B)) ==>'
             '\n      moved{A}(p,k) == moved{B}(p,k);')
    cases = (
        ('baseline', source, None),
        ('parentheses', source.replace('k <= 0 ? 0 : k', '(k <= 0 ? 0 : k)'), None),
        ('bounds', source.replace('0 <= moved(p,k)', '1 <= moved(p,k)', 1),
         'lemma_moved_bounds_all'),
        ('frame', source.replace(frame, 'moved{A}(p,k) == moved{B}(p,k);', 1),
         'check_lemma_moved_frame_all'),
        ('update', source.replace('moved{A}(p,k) +', 'moved{A}(p,k) -', 1),
         'check_lemma_moved_update_all'),
        ('injective_swap', source.replace('&& injective{A}(p,n)', '', 1),
         'lemma_injective_swap'),
        ('selected_mark', source.replace(r'&& \at(u[dest],B) != 0', '', 1),
         'lemma_selected_marked_step'),
    )
    if kind in ('status', 'success'):
        library = Path(__file__).with_name(kind + '.c')
        source = annotate.annotate(annotate.SOURCE.read_text(), kind)
        properties = {p for p in run.source_properties(source) if 'lemma_' in p}
        if kind == 'status':
            changes = (
                ('parentheses', 'k <= 0 ? 0 : k', '(k <= 0 ? 0 : k)', None),
                ('insert-used', r'\at(u[pos],A) == 0 && \at(u[pos],B) != 0',
                 r'\at(u[pos],B) != 0', 'lemma_collected_insert'),
                ('pending-sign', 'pending(d,t,k,s,v) == pending(d,t,k,s+1,v) +',
                 'pending(d,t,k,s,v) == pending(d,t,k,s+1,v) -', 'lemma_pending_shift'),
            )
        else:
            changes = (
                ('parentheses', 'n-1-j > 16', '(n-1-j > 16)', None),
                ('missing-data-exchange', 'exchanged{A,B}(d,n,a,b) && ', '',
                 'lemma_values_exchange'),
                ('missing-status-bound', '0 <= result <= 1 &&', '0 <= result &&',
                 'lemma_guarded_success_iff'),
            )
        cases = (('baseline', source, None),) + tuple(
            (name, source.replace(old, new, 1), failed) for name, old, new, failed in changes)
    rows = []
    for name, text, failed_property in cases:
        if name != 'baseline' and text == source:
            raise ValueError(f'{name}: mutation anchor missing')
        directory = output / name
        directory.mkdir()
        path = directory / 'lemmas.c'
        path.write_text(text)
        command = run.proof_command(shutil.which('frama-c'), config, path, directory, 3, 'termination')
        # The function supplies the memory types. This run checks lemmas only.
        command = [arg for arg in command if arg not in ('-wp-rte', '-rte-initialized=permute')]
        command += ['-wp-prop', '@lemma']
        manifest = {'command': command, 'source_sha256': run.digest(path),
                    'config_sha256': run.digest(config)}
        (directory / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
        code = run.execute(command, directory / 'wp.log')
        report = directory / 'goals.json'
        if code or not report.exists():
            raise ValueError(f'{name}: Frama-C failed before producing a report')
        goals = json.loads(report.read_text())
        scheduled = re.findall(r'\[wp\] (\d+) goals scheduled', (directory / 'wp.log').read_text())
        if (len(scheduled) != 1 or int(scheduled[0]) != len(goals)
                or len(goals) != len(properties)
                or {g.get('property') for g in goals} != properties
                or len({g.get('goal') for g in goals}) != len(goals)
                or any(g.get('function') is not None or g.get('smoke') is not False for g in goals)):
            raise ValueError(f'{name}: unexpected goal report')
        pending = [g['property'] for g in goals if g.get('verdict') != 'valid'
                   or g.get('passed') is not True or g.get('proved') != g.get('subgoals', 1)]
        matched = not pending if failed_property is None else failed_property in pending
        row = {'name': name, 'goals': len(goals), 'pending': pending,
               'expected_failed_property': failed_property, 'matched': matched}
        rows.append(row)
        print(json.dumps(row), flush=True)
    result = {'library': kind, 'pass': all(row['matched'] for row in rows), 'results': rows,
              'sources': {str(p): run.digest(p) for p in
                          (library, Path(annotate.__file__), Path(run.__file__), Path(__file__))}}
    (output / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
    return result['pass']


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--library', choices=('rank', 'status', 'success'), default='rank')
    args = parser.parse_args()
    raise SystemExit(0 if check(args.config.resolve(), args.output.resolve(), args.library) else 1)
