import assert from 'node:assert/strict';
import test from 'node:test';
import { checkNormalization } from './optimality-normalization-check.mjs';
import { normalizeCase, replay } from './optimality-oracle.mjs';

const observed = (problem, ops) => ({ status: 'ok', ops, ...replay(problem, ops) });

test('production normalization checker accepts a shorter fixed point', () => {
  const problem = normalizeCase({ source: ['l:0', 'l:1'], target: ['l:0', 'l:1'],
    referenceOps: [['swap', 1], ['swap', 1]] });
  const result = checkNormalization(problem, observed(problem, []), observed(problem, []));
  assert.deepEqual(result.savedCost, { gas: 6, bytes: 2 });
  assert.equal(result.idempotent, true);
});

test('production normalization checker rejects changed non-SWAP instructions', () => {
  const problem = normalizeCase({ source: ['v:42'], target: ['v:42', 'v:42'], spills: [42],
    referenceOps: [['dup', 1]] });
  const changed = observed(problem, [['load', 42]]);
  assert.throws(() => checkNormalization(problem, changed, changed), /non-SWAP/);
});

test('production normalization checker rejects changed addition order', () => {
  const problem = normalizeCase({ source: ['v:42', 'v:43'], target: ['v:42', 'v:43', 'v:42', 'v:43'],
    referenceOps: [['dup', 2], ['dup', 2]] });
  const changed = observed(problem, [['swap', 1], ['dup', 2], ['dup', 2], ['swap', 3], ['swap', 2], ['swap', 1]]);
  assert.throws(() => checkNormalization(problem, changed, changed), /addition order/);
});

test('production normalization checker rejects larger cost and records idempotence separately', () => {
  const problem = normalizeCase({ source: ['l:0', 'l:0'], target: ['l:0', 'l:0'], referenceOps: [] });
  const empty = observed(problem, []), swap = observed(problem, [['swap', 1]]);
  assert.throws(() => checkNormalization(problem, swap, swap), /cost increases/);
  const withSwap = { ...problem, referenceOps: [['swap', 1]] };
  assert.equal(checkNormalization(withSwap, empty, swap).idempotent, false);
});
