import test from 'node:test';
import assert from 'node:assert/strict';
import { sourcePotential } from './optimality-source-potential.mjs';
import { exactSourceWordMinSwaps } from './optimality-source-entry.mjs';
import { normalizeCase } from './optimality-oracle.mjs';

test('an open three-cycle can attain the same-assignment factor two', () => {
  const value = sourcePotential([3, 0, 2, 1], 3);
  assert.deepEqual([value.K, value.c, value.q, value.F], [2, 1, 0, 4]);
  const problem = normalizeCase({ source: ['l:0', 'l:1', 'l:2'], target: ['l:1', 'l:3', 'l:2', 'l:0'],
    spills: [], caps: { swap: 16, dup: 16 } });
  const exact = exactSourceWordMinSwaps(problem, ['l:3']).get(problem.target.join('|'));
  assert.equal(exact.swaps, 2);
});

test('a closed two-cycle away from the source top needs an entry', () => {
  const value = sourcePotential([1, 0, 2], 3);
  assert.deepEqual([value.K, value.c, value.q, value.F], [1, 1, 1, 3]);
  const problem = normalizeCase({ source: ['l:0', 'l:1', 'l:2'], target: ['l:1', 'l:0', 'l:2'],
    spills: [], caps: { swap: 16, dup: 16 } });
  const exact = exactSourceWordMinSwaps(problem, []).get(problem.target.join('|'));
  assert.equal(exact.swaps, 3);
});

test('cycles through the initial top need no added entry term', () => {
  const value = sourcePotential([2, 1, 0], 3);
  assert.deepEqual([value.K, value.c, value.q, value.F], [1, 0, 0, 1]);
  assert.equal(sourcePotential([], 0).F, 0);
});
