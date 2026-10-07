import test from 'node:test';
import assert from 'node:assert/strict';
import { minimumAssignment, checkAssignment, birthMismatchMatching, periodicCase } from './optimality-birth-matching.mjs';

const brute = costs => {
  const visit = (row, used) => row === costs.length ? 0 : Math.min(...costs[row].map((cost, column) =>
    used.has(column) ? Infinity : cost + visit(row + 1, new Set([...used, column]))));
  return costs.length === 0 ? 0 : visit(0, new Set());
};

test('assignment returns checked dual certificates for tied and forbidden edges', () => {
  for (let size = 0; size <= 6; size++) for (let seed = 0; seed < 20; seed++) {
    const costs = Array.from({ length: size }, (_, row) => Array.from({ length: size }, (_, column) =>
      (row * 7 + column * 3 + seed) % 5 === 0 ? Infinity : (row * 11 + column * 7 + seed) % 4));
    const expected = brute(costs), result = minimumAssignment(costs);
    if (Number.isFinite(expected)) { assert.equal(result.cost, expected); checkAssignment(costs, result); }
    else assert.equal(result.status, 'infeasible');
  }
});

test('assignment rejects malformed inputs and invalid certificates', () => {
  assert.throws(() => minimumAssignment([[0, 1]]));
  assert.throws(() => minimumAssignment([[-1]]));
  const good = minimumAssignment([[0, 2], [2, 0]]);
  assert.throws(() => checkAssignment([[0, 2], [2, 0]], { ...good, columns: [0, 0] }));
  assert.throws(() => checkAssignment([[0, 2], [2, 0]], { ...good, rowDual: [1, 0] }));
});

test('fixed source mismatches and height-capacity failure keep their meaning', () => {
  assert.equal(birthMismatchMatching(['a'], ['b', 'a'], 1, []).mismatches, 2);
  assert.equal(birthMismatchMatching(['a', 'b'], ['c', 'a', 'b'], 1, []).status, 'infeasible');
  assert.equal(birthMismatchMatching([], [], 1, []).mismatches, 0);
  assert.throws(() => birthMismatchMatching(['a'], ['b'], 1, []));
  assert.throws(() => birthMismatchMatching([], ['a'], 0, []));
  assert.throws(() => birthMismatchMatching([], ['a'], 1, [0]));
});

test('periodic full-retention plans force mismatches beyond the gap count', () => {
  const r5 = periodicCase(5), r16 = periodicCase(16);
  assert.equal(r5.gapDemand, 2); assert.equal(r5.match.mismatches, 6); assert.equal(r5.match.swapFloor, 3);
  assert.equal(r16.gapDemand, 2); assert.equal(r16.match.mismatches, 17); assert.equal(r16.match.swapFloor, 9);
  assert.deepEqual(r5.actualSuffix, r5.forcedSuffix);
  assert.deepEqual(r16.actualSuffix, r16.forcedSuffix);
});
