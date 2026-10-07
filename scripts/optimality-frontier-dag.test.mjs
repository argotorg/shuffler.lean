import assert from 'node:assert/strict';
import test from 'node:test';
import { frontierPlan } from './optimality-frontier-dag.mjs';
import { baseline, normalizeCase } from './optimality-oracle.mjs';
import { realizeAssignment } from './optimality-assignment-realizer.mjs';
import { exactObjective, retentionEntries } from './optimality-quota-lp-objectives.mjs';

test('empty frontier DAG has zero cost', () => {
  const result = frontierPlan(normalizeCase({ source: [], target: [] }));
  assert.equal(result.status, 'optimal');
  assert.equal(result.objective, 0);
  assert.deepEqual(result.assignment, []);
});

test('one retained remote copy is present exactly when the frontier contains it', () => {
  const problem = normalizeCase({ source: [], target: ['v:42', 'v:43', 'v:42'], spills: [42, 43],
    loadWidths: [[42, 32], [43, 32]], weights: { gas: 0, bytes: 1 }, caps: { swap: 1, dup: 1 } });
  const result = frontierPlan(problem);
  assert.equal(result.objective - 2 * baseline(problem), 2);
  assert.equal(result.E, 2);
  assert.equal(result.births.filter(birth => birth.kind === 'load').length, 2);
  assert.equal(result.births.filter(birth => birth.kind === 'dup').length, 1);
  assert.equal(realizeAssignment(problem, result.births, result.assignment).swaps, 1);
});

test('cheap direct births remain direct when a copy is present', () => {
  const problem = normalizeCase({ source: [], target: ['l:0', 'l:0'], weights: { gas: 1, bytes: 0 } });
  const result = frontierPlan(problem);
  assert.equal(result.objective, 8);
  assert.deepEqual(result.births.map(birth => birth.kind), ['push', 'push']);
});

test('unavailable values are infeasible and a state limit is not infeasibility', () => {
  assert.equal(frontierPlan(normalizeCase({ source: [], target: ['v:42'] })).status, 'infeasible');
  const problem = normalizeCase({ source: [], target: ['l:0', 'l:1'] });
  assert.equal(frontierPlan(problem, { stateLimit: 1 }).status, 'limit');
});

test('frontier objective agrees with independent permutation enumeration', () => {
  const target = ['v:43', 'v:44', 'v:42', 'v:42', 'v:42', 'v:42', 'v:43', 'v:44'];
  const problem = normalizeCase({ source: [], target, spills: [42, 43, 44],
    loadWidths: [[42, 32], [43, 32], [44, 32]], weights: { gas: 0, bytes: 1 }, caps: { swap: 3, dup: 3 } });
  const result = frontierPlan(problem);
  const retention = retentionEntries(target, { 'v:42': 33, 'v:43': 33, 'v:44': 33 });
  const exact = exactObjective(target, 3, [], { retention, swapPrice: 1 });
  assert.equal(result.objective - 2 * baseline(problem), exact.objective);
  assert.equal(result.objective - 2 * baseline(problem), 4);
  assert.equal(realizeAssignment(problem, result.births, result.assignment).swaps, 2);
});
