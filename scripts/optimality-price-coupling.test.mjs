import assert from 'node:assert/strict';
import test from 'node:test';
import { checkPriceCoupling } from './optimality-price-coupling.mjs';

test('a missed-gap coordinate update can force a score increase', () => {
  const result = checkPriceCoupling();
  assert.equal(result.permutations, 24);
  assert.equal(result.legalAssignments, 8);
  assert.equal(result.tied.supplied.score, '25');
  assert.equal(result.tied.surplusComparison.passes, false);
  assert.ok(result.coordinate.optimal.every(candidate => BigInt(candidate.score) > 25n));
});

test('a joint price change certifies the original assignment', () => {
  const result = checkPriceCoupling();
  assert.deepEqual(result.joint.supplied.assignment, result.tied.supplied.assignment);
  assert.equal(result.joint.suppliedOracleOptimal, true);
  assert.equal(result.joint.surplusComparison.candidatePlusBaseline, '44');
  assert.equal(result.joint.surplusComparison.lower, '44');
  assert.equal(result.joint.surplusComparison.passes, true);
});
