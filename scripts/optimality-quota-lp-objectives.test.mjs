import assert from 'node:assert/strict';
import test from 'node:test';
import { exactObjective, retentionEntries } from './optimality-quota-lp-objectives.mjs';
import { solveQuotaLP } from './optimality-quota-lp.mjs';

test('joint retention objective selects movement before an expensive repeated load', () => {
  const target = ['a', 'b', 'a'];
  const retention = retentionEntries(target, { a: 10, b: 10 });
  const result = exactObjective(target, 1, [], { retention, swapPrice: 1 });
  assert.equal(result.objective, 2);
  assert.equal(result.E, 2);
  assert.deepEqual(result.retained, [true]);
});

test('generic endpoint costs use separate generation quotas', () => {
  const target = ['a', 'b'], jobs = [{ value: 'b', deadline: 0 }, { value: 'a', deadline: 1 }];
  assert.equal(exactObjective(target, 1, jobs, { edgeCosts: [[0, 5], [3, 0]] }).objective, 8);
});

test('joint and generic LP objectives agree on two exact small cases', { skip: !process.env.Z3_BIN }, () => {
  const target = ['a', 'b', 'a'], jobs = target.map((value, output) => ({ value, deadline: output + 1 }));
  const retention = retentionEntries(target, { a: 10, b: 10 });
  assert.equal(solveQuotaLP(target, 1, jobs, { retention }).objective, 2);
  assert.equal(solveQuotaLP(target, 1, jobs, { retention, integral: true }).objective, 2);
  const forced = [{ value: 'b', deadline: 0 }, { value: 'a', deadline: 1 }];
  assert.equal(solveQuotaLP(['a', 'b'], 1, forced, { edgeCosts: [[0, 5], [3, 0]] }).objective, 8);
  assert.equal(solveQuotaLP(['a', 'b'], 1, forced, { edgeCosts: [[0, 5], [3, 0]], integral: true }).objective, 8);
});

test('generic endpoint costs have a fractional gap at length six', { skip: !process.env.Z3_BIN }, () => {
  const target = ['a', 'a', 'a', 'a', 'b', 'c'];
  const jobs = [{ value: 'a', deadline: 2 }, { value: 'a', deadline: 3 }, { value: 'a', deadline: 3 },
    { value: 'a', deadline: 5 }, { value: 'b', deadline: 6 }, { value: 'c', deadline: 7 }];
  const edgeCosts = [[0, 2, 2, 2, 2, 2], [2, 2, 2, 0, 2, 0], [2, 2, 1, 2, 0, 2],
    [2, 0, 2, 2, 2, 2], [2, 2, 0, 2, 2, 0], [2, 2, 2, 0, 0, 2]];
  assert.equal(exactObjective(target, 2, jobs, { edgeCosts }).objective, 1);
  assert.equal(solveQuotaLP(target, 2, jobs, { edgeCosts }).exactObjective, '1/2');
  assert.equal(solveQuotaLP(target, 2, jobs, { edgeCosts, integral: true }).objective, 1);
});

test('a forced-prefetch embedding has integral moved-endpoint optimum four', { skip: !process.env.Z3_BIN }, () => {
  const target = ['d', 'a', 'a', 'a', 'a', 'b', 'c', 'd'];
  const jobs = [{ value: 'd', deadline: 2 }, { value: 'a', deadline: 3 }, { value: 'a', deadline: 4 },
    { value: 'a', deadline: 4 }, { value: 'a', deadline: 6 }, { value: 'b', deadline: 7 },
    { value: 'c', deadline: 8 }, { value: 'd', deadline: 2 }];
  assert.equal(exactObjective(target, 2, jobs).objective, 4);
  const result = solveQuotaLP(target, 2, jobs);
  assert.equal(result.objective, 4);
  assert.equal(result.fractionalEntries, 0);
});
