import assert from 'node:assert/strict';
import test from 'node:test';
import { realizeAssignment, extractAssignment } from './optimality-assignment-realizer.mjs';
import { normalizeCase } from './optimality-oracle.mjs';

test('empty assignment has no operations', () => {
  const problem = normalizeCase({ source: [], target: [] });
  assert.deepEqual(realizeAssignment(problem, [], []).ops, []);
});

test('a maximum-depth displacement uses the legal boundary SWAP', () => {
  const problem = normalizeCase({ source: [], target: ['v:42', 'v:43'], spills: [42, 43], caps: { swap: 1, dup: 1 } });
  const result = realizeAssignment(problem, [{ kind: 'load', value: 'v:43' }, { kind: 'load', value: 'v:42' }], [1, 0]);
  assert.deepEqual(result.ops, [['load', 43], ['load', 42], ['swap', 1]]);
  assert.equal(result.D, 2);
  assert.equal(result.swaps, 1);
});

test('equal copies use the supplied one-SWAP assignment', () => {
  const problem = normalizeCase({ source: [], target: ['v:43', 'v:42', 'v:43', 'v:42'], spills: [42, 43], caps: { swap: 3, dup: 3 } });
  const births = [{ kind: 'load', value: 'v:42' }, { kind: 'dup', value: 'v:42' },
    { kind: 'load', value: 'v:43' }, { kind: 'dup', value: 'v:43' }];
  const result = realizeAssignment(problem, births, [3, 1, 2, 0]);
  assert.equal(result.swaps, 1);
  assert.deepEqual(result.ops.at(-1), ['swap', 3]);
  assert.equal(result.D, 2);
});

test('assignment validates bijection, values, lag, and DUP prefix counts', () => {
  const problem = normalizeCase({ source: [], target: ['v:42', 'v:43', 'v:42'], spills: [42, 43], caps: { swap: 1, dup: 1 } });
  const births = [{ kind: 'load', value: 'v:42' }, { kind: 'load', value: 'v:43' }, { kind: 'dup', value: 'v:42' }];
  assert.throws(() => realizeAssignment(problem, births, [0, 1, 1]), /bijection/);
  assert.throws(() => realizeAssignment(problem, births, [1, 0, 2]), /value/);
  assert.throws(() => realizeAssignment(problem, births, [2, 1, 0]), /lag/);
  assert.throws(() => realizeAssignment(problem, births, [0, 1, 2]), /DUP prefix/);
});

test('extracting a valid trace gives its actual token assignment', () => {
  const problem = normalizeCase({ source: [], target: ['v:43', 'v:42'], spills: [42, 43] });
  const plan = extractAssignment(problem, [['load', 42], ['load', 43], ['swap', 1]]);
  assert.deepEqual(plan.assignment, [1, 0]);
  assert.deepEqual(plan.births.map(birth => birth.value), ['v:42', 'v:43']);
  assert.equal(realizeAssignment(problem, plan.births, plan.assignment).swaps, 1);
});

test('moved token support can exceed the number of value mismatches', () => {
  const problem = normalizeCase({ source: [], target: ['v:42', 'v:42', 'v:43'], spills: [42, 43], caps: { swap: 1, dup: 1 } });
  const births = [{ kind: 'load', value: 'v:43' }, { kind: 'load', value: 'v:42' }, { kind: 'load', value: 'v:42' }];
  const result = realizeAssignment(problem, births, [2, 0, 1]);
  assert.equal(result.E, 3);
  assert.equal(births.filter((birth, index) => birth.value !== problem.target[index]).length, 2);
  assert.equal(result.swaps, 2);
});
