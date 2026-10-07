import assert from 'node:assert/strict';
import test from 'node:test';
import { minimumPlanSwaps, ordinaryFreshPlan } from './optimality-plan-presence.mjs';
import { replay } from './optimality-oracle.mjs';

test('equal-value roots can exchange roles in a selected retention plan', () => {
  const plan = ordinaryFreshPlan(['a', 'b', 'b', 'b', 'a'], [0, 2], 2, 0);
  const result = minimumPlanSwaps(plan);
  assert.equal(result.status, 'reachable');
  assert.equal(result.swaps, 1);
  assert.ok(result.direct.every((count, index) => count <= plan.budgets[index]));
  assert.deepEqual(replay(plan.problem, result.ops).target, plan.problem.target);
});

test('retained presence is checked before each freezing birth', () => {
  const selected = ordinaryFreshPlan(['a', 'a'], [0], 1, 1);
  selected.budgets = [2];
  assert.equal(minimumPlanSwaps(selected).status, 'unreachable');
  const unselected = ordinaryFreshPlan(['a', 'a'], [], 1, 1);
  assert.equal(minimumPlanSwaps(unselected).status, 'reachable');
});

test('introduction budgets, empty inputs, and search limits retain their meaning', () => {
  const plan = ordinaryFreshPlan(['a'], [], 1, 0);
  plan.budgets = [0];
  assert.equal(minimumPlanSwaps(plan).status, 'unreachable');
  assert.equal(minimumPlanSwaps(ordinaryFreshPlan([], [], 1, 0)).swaps, 0);
  assert.equal(minimumPlanSwaps(ordinaryFreshPlan(['a', 'b'], [], 1, 0), { stateLimit: 1 }).status, 'limit');
});

test('a fixed value birth order can require more swaps than another feasible order', () => {
  const plan = ordinaryFreshPlan(['a', 'b', 'b', 'c', 'c', 'd', 'd', 'e', 'a'], [0, 1, 2, 3], 4, 0);
  const fixed = [0, 1, 1, 2, 0, 2, 3, 3, 4].map(index => plan.values[index]);
  const result = minimumPlanSwaps(plan, { birthOrder: fixed });
  assert.equal(result.status, 'reachable');
  assert.equal(result.swaps, 3);
  assert.equal(minimumPlanSwaps(plan).swaps, 2);
  assert.deepEqual(replay(plan.problem, result.ops).target, plan.problem.target);
});

test('fixed birth order rejects a wrong birth count or multiset', () => {
  const plan = ordinaryFreshPlan(['a'], [], 1, 0);
  assert.throws(() => minimumPlanSwaps(plan, { birthOrder: [] }), /birth order/);
  assert.throws(() => minimumPlanSwaps(plan, { birthOrder: ['v:999'] }), /birth order/);
  assert.equal(minimumPlanSwaps(ordinaryFreshPlan([], [], 1, 0), { birthOrder: [] }).swaps, 0);
});
