#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Audit the retained n1..4 results and the resumed full n5 campaign."""
import hashlib
import itertools
import json
from pathlib import Path
import re
import sys

old_path, new_path, out = map(Path, sys.argv[1:])
root = Path('spikes/clight-permute').resolve()
sys.path.insert(0, str(root / 'tests/equiv-alive2'))
from completion import check_completions

records = []
paths_per_case = {1: 1, 2: 3, 3: 13, 4: 75, 5: 541}
for path, sizes in ((old_path, {1, 2, 3, 4}), (new_path, {5})):
    manifest = json.loads(path.read_text())
    assert manifest['value_groups'] is None
    for name, digest in manifest['source_sha256'].items():
        assert hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest, name
    cases = [case for case in manifest['cases'] if case['n'] in sizes]
    expected = {(n, permutation) for n in sizes for permutation in itertools.permutations(range(n))}
    actual = {(case['n'], tuple(case['permutation'])) for case in cases}
    assert actual == expected and len(cases) == len(expected)
    for case in cases:
        directory = path.parent / case['directory']
        assert case['pass'] and not case['errors'] and not case['changed_sources']
        assert case['partial_paths'] == 0
        assert case['complete_paths'] == paths_per_case[case['n']]
        assert hashlib.sha256((directory / 'linked.bc').read_bytes()).hexdigest() == case['linked_sha256']
        log = (directory / 'proof.log').read_text()
        assert 'KLEE: ERROR:' not in log and 'calling external:' not in log
        assert not list((directory / 'proof').glob('*.err'))
        assert int(re.search(r'completed paths = (\d+)', log)[1]) == case['complete_paths']
        assert int(re.search(r'partially completed paths = (\d+)', log)[1]) == 0
        completion = check_completions(directory / 'proof', case['complete_paths'], 'values', 4 * case['n'])
        assert completion['pass'], (case['directory'], completion)
        assert all(item['covered_instructions'] > 0 for item in case['function_coverage'].values())
    records.append({'manifest': str(path), 'manifest_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                    'sizes': sorted(sizes), 'cases': len(cases),
                    'marked_paths': sum(case['complete_paths'] for case in cases)})
    print(json.dumps(records[-1]), flush=True)
summary = {'campaigns': records, 'cases': sum(item['cases'] for item in records),
           'marked_paths': sum(item['marked_paths'] for item in records),
           'complete_n1_through_n5': True,
           'scope': 'Arbitrary uint32 values and all valid permutations at lengths 1 through 5, under the recorded KLEE runtime assumptions.'}
assert summary['cases'] == 153 and summary['marked_paths'] == 66805
out.write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary), flush=True)
