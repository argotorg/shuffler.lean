import test from 'node:test';
import assert from 'node:assert/strict';
import { normalizeCase } from './optimality-oracle.mjs';
import { sourceWordFeasible, exactSourceWordEndpoints, realizeSourceWordForAudit } from './optimality-source-word-feasibility.mjs';

const a = 'l:0', x = 'v:42';
const problem = (source, target, spills = [], reach = 16) => normalizeCase({ source, target, spills,
  caps: { swap: reach, dup: reach } });

test('repair the SWAP16 boundary before duplicating its old value', () => {
  const input = problem([x, ...Array(16).fill(a)], [...Array(16).fill(a), x, x]);
  assert.equal(sourceWordFeasible(input, [x]), true);
  const built = realizeSourceWordForAudit(input, [x]);
  assert.ok(built.boundarySwaps <= 2);
  assert.ok(built.ops.some(op => op[0] === 'dup'));
});

test('a sole copy at the fixed boundary cannot supply DUP', () => {
  const source = [x, ...Array(16).fill(a)], target = [...source, x];
  assert.equal(sourceWordFeasible(problem(source, target), [x]), false);
  assert.equal(sourceWordFeasible(problem(source, target, [42]), [x]), true);
  realizeSourceWordForAudit(problem(source, target, [42]), [x]);
});

test('wrong counts and unavailable first births fail', () => {
  assert.equal(sourceWordFeasible(problem([], [x]), [x]), false);
  assert.equal(sourceWordFeasible(problem([a], [a, x]), [a]), false);
  assert.equal(sourceWordFeasible(problem([], []), []), true);
});

test('the initial frozen prefix requires a separate normalization', () => {
  assert.throws(() => sourceWordFeasible(problem(Array(18).fill(a), Array(18).fill(a)), []), /normalize/);
});

test('exact search includes initial permutations before any birth', () => {
  const input = problem(['l:0', 'l:1', 'l:2'], ['l:1', 'l:0', 'l:2'], [], 2);
  assert.ok(exactSourceWordEndpoints(input, []).endpoints.has(input.target.join('|')));
  realizeSourceWordForAudit(input, []);
});
