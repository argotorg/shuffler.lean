import assert from 'node:assert/strict';
import test from 'node:test';
import { coloredPinPlan } from './optimality-colored-pins.mjs';

test('empty plan and early and late window boundaries', () => {
  assert.equal(coloredPinPlan([], 2, [], []).status, 'feasible');
  const result = coloredPinPlan(['a', 'a'], 16, [0], [0, 1]);
  assert.equal(result.status, 'feasible');
  assert.deepEqual(result.obligations, []);
  assert.equal(result.cuts[0].capacity, 1);
  assert.equal(result.cuts.at(-1).capacity, 0);
});

test('later pin cannot meet an earlier seed deadline', () => {
  const result = coloredPinPlan(['a', 'b', 'b', 'a', 'b', 'a'], 2, [1], [0, 2, 3]);
  assert.equal(result.status, 'infeasible');
  assert.equal(result.cut, 3);
  assert.deepEqual(result.obligations, [{ value: 'a', start: 2, end: 7, gap: 1 }]);
  assert.equal(result.cuts[3].pinned, 2);
  assert.deepEqual(result.cuts[3].uncovered, ['a']);
});

test('a seed can remain valid through a later pinned endpoint', () => {
  const result = coloredPinPlan(['a', 'b', 'b', 'a', 'b', 'a'], 2, [1], [0, 1, 3]);
  assert.equal(result.status, 'feasible');
  assert.deepEqual(result.cuts[4].uncovered, ['a']);
  assert.deepEqual(result.cuts[7].uncovered, []);
});

test('a pin at the seed deadline covers the seed', () => {
  const result = coloredPinPlan(['a', 'b', 'a'], 2, [0], [0, 2]);
  assert.equal(result.status, 'feasible');
  assert.deepEqual(result.obligations, []);
});

test('an uncovered seed with no free endpoint is rejected', () => {
  const result = coloredPinPlan(['a', 'b', 'b', 'a'], 2, [1], [0, 3]);
  assert.equal(result.status, 'infeasible');
  assert.equal(result.obligations[0].end, null);
});

test('no retained gaps permits every endpoint to be pinned', () => {
  const result = coloredPinPlan(['a', 'b', 'a', 'c', 'b'], 1, [], [0, 1, 2, 3, 4]);
  assert.equal(result.status, 'feasible');
  assert.ok(result.cuts.every(cut => cut.pinned === cut.capacity));
});

test('reject invalid reach and duplicate selections', () => {
  assert.throws(() => coloredPinPlan(['a', 'a'], 0, [], []));
  assert.throws(() => coloredPinPlan(['a', 'a'], 1, [0, 0], []));
  assert.throws(() => coloredPinPlan(['a', 'a'], 1, [], [0, 0]));
});
