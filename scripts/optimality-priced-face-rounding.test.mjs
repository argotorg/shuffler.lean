import test from 'node:test';
import assert from 'node:assert/strict';
import { checkFaceFixture, checkDenominatorThree, checkCanonicalCounterexample } from './optimality-priced-face-rounding.mjs';

test('the four-row unpriced obstruction is not a positive-price common face', () => {
  const result = checkFaceFixture({ name: 'four-row', target: [0, 0, 1, 2], reach: 2 });
  assert.equal(result.faces, 1);
  assert.equal(result.pairs, 0);
  assert.deepEqual(result.failures, []);
});

test('the mixed-pin value-job case permits exact face-preserving rounding', () => {
  const result = checkFaceFixture({ name: 'mixed-pin', target: [0, 0, 1, 1, 1, 1, 0, 0], reach: 2 });
  assert.ok(result.nontrivialPairs > 0);
  assert.ok(result.splitStats.largeDiscrepancyCycles > 0);
  assert.ok(result.splitStats.totalSplits > 0);
  assert.deepEqual(result.failures, []);
  assert.deepEqual(result.splitFailures, []);
  assert.deepEqual(result.terminalFailures, []);
  assert.equal(result.roundingWitness.inputMoved, result.roundingWitness.bestOutputMoved);
});

test('denominator-three prefetch has a checked common optimum and balanced endpoints', () => {
  const result = checkDenominatorThree();
  assert.equal(result.dual.reward, '22');
  assert.equal(result.inputMoved, 6);
  assert.equal(result.bestOutputMoved, 6);
  assert.equal(result.balancedColorings, 6);
});

test('a common canonical-price face can require extra E under canonical-cut row-token rounding', () => {
  const result = checkCanonicalCounterexample();
  assert.equal(result.dual.reward, '12');
  assert.equal(result.inputMoved, 4);
  assert.equal(result.bestOutputMoved, 5);
  assert.equal(result.balancedColorings, 2);
  assert.equal(result.outputSwapRank, 3);
  assert.equal(result.alternative.reward, 12);
  assert.equal(result.alternative.moved, 4);
  assert.deepEqual(result.alternative.gapCounts, [2, 2, 2, 3]);
});
