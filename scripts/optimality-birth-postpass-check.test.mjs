import test from 'node:test';
import assert from 'node:assert/strict';
import { checkPostpass } from './optimality-birth-postpass-check.mjs';

const problem = { id: 'same-word', source: [], target: ['l:0', 'l:1'],
  missing: ['l:0', 'l:1'], spills: [], weights: { gas: 1, bytes: 0 },
  caps: { swap: 16, dup: 16 }, loadWidths: [], gasModel: 'evm',
  referenceOps: [['push', 'l:0'], ['push', 'l:1']],
  expectedOriginalCost: { gas: 5, bytes: 3 }, savedPortfolioNanos: 1000000 };
const output = { elapsedNanos: 100000, result: { id: 'same-word', algorithms: {
  'birth-reference': { status: 'ok', ops: problem.referenceOps, cost: { gas: 5, bytes: 3 }, score: 5 } } } };

test('checks production output against independent replay', () => {
  const checked = checkPostpass(problem, output, 'birth-reference');
  assert.equal(checked.selectedScore, 5);
  assert.equal(checked.keepCandidate, false);
});

test('rejects a reported cost that differs from instruction replay', () => {
  const altered = structuredClone(output);
  altered.result.algorithms['birth-reference'].cost.gas = 4;
  assert.throws(() => checkPostpass(problem, altered, 'birth-reference'), /costs differ/);
});

test('rejects a different ordered birth word with the same endpoint', () => {
  const altered = structuredClone(output);
  altered.result.algorithms['birth-reference'] = { status: 'ok',
    ops: [['push', 'l:1'], ['push', 'l:0'], ['swap', 1]], cost: { gas: 8, bytes: 4 }, score: 8 };
  assert.throws(() => checkPostpass(problem, altered, 'birth-reference'), /birth values differ/);
});

test('rejects a source output that does not reach the target', () => {
  const altered = structuredClone(output);
  altered.result.algorithms['source-reference'] = { status: 'ok',
    ops: [['push', 'l:1'], ['push', 'l:0']], cost: { gas: 5, bytes: 3 }, score: 5 };
  assert.throws(() => checkPostpass(problem, altered, 'source-reference'), /endpoint differs/);
});
