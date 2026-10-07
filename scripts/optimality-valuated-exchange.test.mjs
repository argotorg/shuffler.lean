import assert from 'node:assert/strict';
import test from 'node:test';
import { endpointMovement, valuatedExchange } from './optimality-valuated-exchange.mjs';

test('one-value endpoint movement includes forced loss of a shared position', () => {
  assert.equal(endpointMovement([1, 2], [0, 1], 1), 2);
  assert.equal(endpointMovement([0, 2], [0, 1], 1), 1);
  assert.equal(endpointMovement([2, 3], [0, 1], 1), null);
});

test('unrestricted endpoint identity cost passes valuated exchange', () => {
  const result = valuatedExchange(5, [0, 2, 4], 16, [16, 18, 20]);
  assert.equal(result.failure, null);
  assert.equal(result.bases.length, 10);
});

test('no feasible birth bases gives no exchange obligation', () => {
  const result = valuatedExchange(3, [0, 1, 2], 1, [0, 0, 0]);
  assert.deepEqual(result.bases, []);
  assert.equal(result.failure, null);
});

test('fixed generation deadlines can break endpoint-valuated exchange', () => {
  const result = valuatedExchange(5, [0, 1, 2], 2, [2, 2, 4]);
  assert.deepEqual(result.failure.a.births, [0, 1, 4]);
  assert.deepEqual(result.failure.b.births, [0, 2, 3]);
  assert.equal(result.failure.x, 1);
  assert.equal(result.failure.a.cost + result.failure.b.cost, 2);
  assert.equal(result.failure.attempts[0].first.cost + result.failure.attempts[0].second.cost, 3);
  assert.equal(result.failure.attempts[1].first, null);
});

test('full cost exchange fails for every tested positive premium and SWAP price', () => {
  for (const premium of [1, 3, 33]) for (const swapPrice of [1, 3]) {
    const result = valuatedExchange(5, [0, 1, 2], 2, [2, 3, 4], { premium, swapPrice });
    const failure = result.failure;
    assert.deepEqual(failure.a.births, [0, 1, 4]);
    assert.deepEqual(failure.b.births, [0, 2, 3]);
    assert.equal(failure.a.cost + failure.b.cost, 2 * premium + 2 * swapPrice);
    assert.equal(failure.attempts[0].first.cost + failure.attempts[0].second.cost, 2 * premium + 3 * swapPrice);
    assert.equal(failure.attempts[1].first.cost + failure.attempts[1].second.cost, 4 * premium + 2 * swapPrice);
  }
});
