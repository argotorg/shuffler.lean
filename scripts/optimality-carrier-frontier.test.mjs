import assert from 'node:assert/strict';
import test from 'node:test';
import { carrierFrontier } from './optimality-carrier-frontier.mjs';

test('frontier reaches the endpoint of the two-SWAP example', () => {
  const result = carrierFrontier(['a', 'b', 'b', 'c', 'a'], 2);
  assert.equal(result.capacityFeasible, true);
  assert.deepEqual(result.frontiers.slice(0, 3), [2, 3, 4]);
  assert.equal(result.firstFailure, null);
});

test('a full short-gap cycle blocks the carrier and exceeds capacity', () => {
  const result = carrierFrontier(['a', 'b', 'c', 'b', 'c', 'a'], 2);
  assert.equal(result.capacityFeasible, false);
  assert.equal(result.maximumOccupancy, 3);
  assert.deepEqual(result.frontiers.slice(0, 4), [2, 4, 4, 4]);
  assert.notEqual(result.firstFailure, null);
});

test('frontier handles longer intervals and rejects a second long value gap', () => {
  const result = carrierFrontier(['a', 'b', 'b', 'b', 'b', 'b', 'a'], 2);
  assert.equal(result.capacityFeasible, true);
  assert.equal(result.firstFailure, null);
  assert.equal(result.frontiers.at(-1), 6);
  assert.throws(() => carrierFrontier(['a', 'b', 'c', 'c', 'b', 'a'], 2), /short gap/);
});
