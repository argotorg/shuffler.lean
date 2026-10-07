import assert from 'node:assert/strict';
import test from 'node:test';
import { encodeIntervalPlan, testIntervalPlan } from './optimality-interval-realizability.mjs';
import { replay } from './optimality-oracle.mjs';

test('selected intervals force one direct root for each retained group', () => {
  const plan = encodeIntervalPlan(['a', 'b', 'a', 'b', 'a'], [0, 2], 2, 1);
  assert.equal(plan.capacityFeasible, true);
  assert.equal(plan.roots.length, 3);
  assert.deepEqual(plan.problem.target.slice(0, 5), ['v:100', 'v:101', 'v:100', 'v:102', 'v:100']);
  const result = testIntervalPlan(plan);
  assert.equal(result.status, 'reachable');
  assert.equal(result.direct, 3);
  assert.deepEqual(replay(plan.problem, result.ops).target, plan.problem.target);
});

test('the old copies leave no retained slot at q=R', () => {
  const retained = encodeIntervalPlan(['a', 'a'], [0], 2, 2);
  assert.equal(retained.capacityFeasible, false);
  assert.equal(testIntervalPlan(retained).status, 'unreachable');
  const separate = encodeIntervalPlan(['a', 'a'], [], 2, 2);
  assert.equal(separate.capacityFeasible, true);
  const result = testIntervalPlan(separate);
  assert.equal(result.status, 'reachable');
  assert.equal(result.direct, 2);
});

test('empty plans and the full available seed capacity are realizable', () => {
  for (const [word, selected, reach, old] of [[[], [], 1, 0], [[], [], 3, 3],
    [['a', 'b', 'a', 'b'], [0, 1], 2, 0]]) {
    const plan = encodeIntervalPlan(word, selected, reach, old);
    assert.equal(plan.capacityFeasible, true);
    const result = testIntervalPlan(plan);
    assert.equal(result.status, 'reachable');
    assert.equal(result.direct, plan.roots.length);
  }
});

test('invalid interval selections and dimensions reject', () => {
  assert.throws(() => encodeIntervalPlan(['a'], [0], 2, 0));
  assert.throws(() => encodeIntervalPlan(['a', 'a'], [0, 0], 2, 0));
  assert.throws(() => encodeIntervalPlan(['a'], [], 0, 0));
  assert.throws(() => encodeIntervalPlan(['a'], [], 2, 3));
});
