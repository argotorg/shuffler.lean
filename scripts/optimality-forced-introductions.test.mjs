import assert from 'node:assert/strict';
import test from 'node:test';
import { normalizeCase, replay } from './optimality-oracle.mjs';
import { reachableWithDirectLimit } from './optimality-forced-introductions.mjs';

test('boundary placement needs two direct introductions at the DUP limit', () => {
  const problem = normalizeCase({ source: ['l:0', 'l:0'], target: ['v:42', 'l:0', 'l:0', 'v:42'],
    spills: [42], caps: { swap: 2, dup: 2 } });
  assert.equal(reachableWithDirectLimit(problem, 'v:42', 1).status, 'unreachable');
  const two = reachableWithDirectLimit(problem, 'v:42', 2);
  assert.equal(two.status, 'reachable');
  assert.equal(two.direct, 2);
  replay(problem, two.ops);
});

test('a shorter stack can retain the introduced value for DUP', () => {
  const problem = normalizeCase({ source: ['l:0'], target: ['v:42', 'l:0', 'v:42'],
    spills: [42], caps: { swap: 2, dup: 2 } });
  const result = reachableWithDirectLimit(problem, 'v:42', 1);
  assert.equal(result.status, 'reachable');
  assert.equal(result.direct, 1);
  replay(problem, result.ops);
});

test('a prefix run can force three direct introductions', () => {
  const problem = normalizeCase({ source: ['l:0', 'l:0'], target: ['v:42', 'v:42', 'v:42', 'l:0', 'l:0'],
    spills: [42], caps: { swap: 2, dup: 2 } });
  assert.equal(reachableWithDirectLimit(problem, 'v:42', 2).status, 'unreachable');
  const result = reachableWithDirectLimit(problem, 'v:42', 3);
  assert.equal(result.status, 'reachable');
  assert.equal(result.direct, 3);
  replay(problem, result.ops);
});

test('two new kinds share one retained seed slot', () => {
  const problem = normalizeCase({ source: ['l:0'],
    target: ['v:42', 'v:43', 'v:42', 'v:43', 'l:0'],
    spills: [42, 43], caps: { swap: 2, dup: 2 } });
  assert.equal(reachableWithDirectLimit(problem, ['v:42', 'v:43'], 2).status, 'unreachable');
  const result = reachableWithDirectLimit(problem, ['v:42', 'v:43'], 3);
  assert.equal(result.status, 'reachable');
  assert.equal(result.direct, 3);
  replay(problem, result.ops);
});
