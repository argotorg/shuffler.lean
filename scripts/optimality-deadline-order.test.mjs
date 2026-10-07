import assert from 'node:assert/strict';
import test from 'node:test';
import { lexicographicDeadlineOrder, exhaustiveDeadlineOrders, checkDeadlineRule } from './optimality-deadline-order.mjs';

test('the rule preserves target order whenever target order meets deadlines', () => {
  assert.deepEqual(lexicographicDeadlineOrder([3, 4, 3]), [0, 1, 2]);
  assert.deepEqual(lexicographicDeadlineOrder([]), []);
});

test('a tight cut forces the required earlier birth', () => {
  assert.deepEqual(lexicographicDeadlineOrder([2, 3, 2]), [0, 2, 1]);
  assert.deepEqual(lexicographicDeadlineOrder([2, 1]), [1, 0]);
  assert.equal(lexicographicDeadlineOrder([1, 1]), null);
  assert.equal(lexicographicDeadlineOrder([0]), null);
});

test('the exhaustive comparator includes all feasible permutations', () => {
  assert.deepEqual(exhaustiveDeadlineOrders([3, 3, 3]),
    [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]);
  assert.deepEqual(exhaustiveDeadlineOrders([2, 3, 2]), [[0, 2, 1], [2, 0, 1]]);
});

test('the rule matches exhaustive lexicographic optima on all tiny deadlines', () => {
  const result = checkDeadlineRule(5);
  assert.equal(result.first, null);
  assert.equal(result.instances, 8477);
});
