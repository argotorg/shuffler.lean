import assert from 'node:assert/strict';
import test from 'node:test';
import { swapPositionGraph, carrierRealization } from './optimality-one-gap.mjs';
import { ordinaryFreshPlan } from './optimality-plan-presence.mjs';
import { replay } from './optimality-oracle.mjs';

test('SWAP positions account for intervening births', () => {
  const graph = swapPositionGraph([['load', 42], ['dup', 1], ['load', 43], ['dup', 1],
    ['swap', 2], ['load', 44], ['swap', 1]]);
  assert.deepEqual(graph.edges, [[1, 3], [3, 4]]);
  assert.deepEqual(graph.shared, [3]);
  assert.equal(graph.connected, true);
});

test('position graph distinguishes disjoint SWAPs and accepts an empty trace', () => {
  const graph = swapPositionGraph([['load', 42], ['load', 43], ['swap', 1],
    ['load', 44], ['load', 45], ['swap', 1]]);
  assert.deepEqual(graph.edges, [[0, 1], [2, 3]]);
  assert.equal(graph.connected, false);
  assert.deepEqual(swapPositionGraph([]).edges, []);
});

test('carrier construction handles a one-hop and a two-hop interval', () => {
  for (const [word, reach, swaps] of [
    [['a', 'b', 'a'], 1, 1],
    [['a', 'b', 'b', 'c', 'a'], 2, 2],
    [['a', 'b', 'b', 'c', 'c', 'd', 'd', 'e', 'a'], 4, 2],
  ]) {
    const result = carrierRealization(word, reach);
    assert.ok(result);
    assert.equal(result.positions.length - 1, swaps);
    const plan = ordinaryFreshPlan(word, [], reach, 0);
    assert.deepEqual(replay(plan.problem, result.ops).target, plan.problem.target);
  }
});

test('carrier construction rejects a missing endpoint and excessive distance', () => {
  assert.throws(() => carrierRealization(['a', 'b'], 1), /interval/);
  assert.throws(() => carrierRealization(['a', 'b', 'c', 'a'], 1), /interval/);
});
