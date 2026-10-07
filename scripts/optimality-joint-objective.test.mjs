import assert from 'node:assert/strict';
import test from 'node:test';
import { weightedFreshCase, jointPlanChoice } from './optimality-joint-objective.mjs';
import { ordinaryFreshPlan, minimumPlanSwaps } from './optimality-plan-presence.mjs';
import { baseline, solve } from './optimality-oracle.mjs';

test('joint premium and movement objective avoids the introduction-only obstruction', () => {
  const word = ['a', 'b', 'b', 'b', 'a'];
  const problem = weightedFreshCase(word, 1, 0, ['load0', 'literal32'], { gas: 22, bytes: 1 });
  const plans = [[], [0], [1], [0, 1], [2]].map(selected => {
    const plan = ordinaryFreshPlan(word, selected, 1, 0);
    return { selected, result: minimumPlanSwaps(plan) };
  });
  const chosen = jointPlanChoice(problem, word, plans);
  assert.equal(baseline(problem), 434);
  assert.equal(chosen.floor, 67);
  assert.equal(chosen.candidates.length, 1);
  assert.deepEqual(chosen.candidates[0].selected, [0, 1]);
  assert.equal(chosen.candidates[0].score, 501);
  assert.equal(solve(problem).score, 501);
});

test('empty input has zero joint cost and one empty plan', () => {
  const problem = weightedFreshCase([], 1, 0, [], { gas: 1, bytes: 0 });
  const chosen = jointPlanChoice(problem, [], [{ selected: [], result: { status: 'reachable', ops: [], swaps: 0 } }]);
  assert.equal(chosen.floor, 0);
  assert.equal(chosen.candidates[0].score, 0);
});

test('PUSH0 uses direct births when DUP costs more than direct generation', () => {
  const word = ['a', 'a'];
  const problem = weightedFreshCase(word, 1, 0, ['zero'], { gas: 1, bytes: 0 });
  const plans = [[], [0]].map(selected => ({ selected,
    result: minimumPlanSwaps(ordinaryFreshPlan(word, selected, 1, 0)) }));
  const chosen = jointPlanChoice(problem, word, plans);
  assert.equal(baseline(problem), 4);
  assert.equal(chosen.floor, 0);
  assert.equal(chosen.candidates.length, 1);
  assert.deepEqual(chosen.candidates[0].selected, []);
  assert.deepEqual(chosen.candidates[0].ops, [['push', 'l:0'], ['push', 'l:0']]);
  assert.equal(chosen.candidates[0].score, 4);
  const bytesOnly = jointPlanChoice({ ...problem, weights: { gas: 0, bytes: 1 } }, word, plans);
  assert.equal(bytesOnly.floor, 0);
  assert.equal(bytesOnly.candidates[0].score, 2);
});

test('fresh PUSH0 differs from old copies and profile kinds remain distinct', () => {
  const problem = weightedFreshCase(['a'], 1, 1, ['zero'], { gas: 1, bytes: 1 });
  assert.deepEqual(problem.source, ['return']);
  assert.deepEqual(problem.target, ['l:0', 'return']);
  assert.throws(() => weightedFreshCase(['a', 'b'], 1, 0, ['zero', 'zero'], { gas: 1, bytes: 0 }), /profile/);
});
