import assert from 'node:assert/strict';
import test from 'node:test';
import { globalInventoryPlan } from './optimality-global-inventory.mjs';
import { minimumPlanSwaps } from './optimality-plan-presence.mjs';

test('a new first boundary value has a nonpositive deadline and fails capacity', () => {
  const plan = globalInventoryPlan(['a', 'a', 'a'], ['b', 'a', 'a', 'a'], [], 2);
  assert.deepEqual(plan.deadlines, [0]);
  assert.equal(plan.capacityFeasible, false);
  assert.equal(plan.deadlineOrder, null);
  assert.equal(plan.reserveFeasible, false);
});

test('a sole boundary seed needs another introduction', () => {
  const selected = globalInventoryPlan(['a', 'b', 'b'], ['a', 'a', 'b', 'b'], [0], 2);
  assert.equal(selected.capacityFeasible, false);
  assert.equal(selected.deadlineOrder, null);
  assert.equal(minimumPlanSwaps(selected).status, 'unreachable');
  const direct = globalInventoryPlan(['a', 'b', 'b'], ['a', 'a', 'b', 'b'], [], 2);
  assert.equal(direct.capacityFeasible, true);
  assert.equal(minimumPlanSwaps(direct).status, 'reachable');
});

test('a second old copy can supply the selected fresh occurrence', () => {
  const plan = globalInventoryPlan(['a', 'b', 'a'], ['a', 'a', 'a', 'b'], [0], 2);
  assert.equal(plan.capacityFeasible, true);
  assert.deepEqual(plan.deadlines, [1]);
  assert.deepEqual(plan.budgets, [0, 0]);
  const result = minimumPlanSwaps(plan);
  assert.equal(result.status, 'reachable');
  assert.deepEqual(result.direct, [0, 0]);
});

test('normalization and multiset balance are input conditions', () => {
  assert.throws(() => globalInventoryPlan(['a', 'a', 'a', 'a'], ['a', 'a', 'a', 'a'], [], 2));
  assert.throws(() => globalInventoryPlan(['a'], ['b'], [], 2));
});
