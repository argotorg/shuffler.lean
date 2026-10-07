import assert from 'node:assert/strict';
import test from 'node:test';
import { checkPricedFixtures, canonicalRouteLoads, pricedAssignment } from './optimality-priced-assignment.mjs';

test('sparse flow agrees with each small assignment optimum', () => {
  const records = checkPricedFixtures();
  assert.equal(records.length, 7);
  assert.ok(records.every(record => record.equal));
});

test('last occurrences are entry events even without a gap multiplier', () => {
  const result = pricedAssignment({ target: ['a', 'b'], source: ['b'], reach: 1, swap: 3, gaps: [] });
  assert.equal(result.status, 'optimal');
  assert.deepEqual(result.assignment, [1, 0]);
});

test('a same-time entry can carry R plus one units', () => {
  const instance = { target: ['a', 'a', 'a'], reach: 1, swap: 0, gaps: [] };
  const result = canonicalRouteLoads(instance, [1, 0, 2]);
  assert.equal(result.maximumEntryLoad, 2);
  assert.equal(result.maximumPositiveTimeLoad, 1);
});

test('a frozen source value conflict makes the priced problem infeasible', () => {
  const result = pricedAssignment({ source: ['b', 'a', 'a'], target: ['a', 'b', 'a'], reach: 1, swap: 2, gaps: [] });
  assert.equal(result.status, 'infeasible');
});

test('prices must be nonnegative and attached to target deadlines', () => {
  assert.throws(() => pricedAssignment({ target: ['a'], reach: 1, swap: 2, gaps: [{ left: 0, weight: -1 }] }));
  assert.throws(() => pricedAssignment({ target: ['a'], reach: 1, swap: 2, gaps: [{ left: 1, weight: 1 }] }));
});
