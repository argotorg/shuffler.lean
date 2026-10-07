import test from 'node:test';
import assert from 'node:assert/strict';
import { normalizeCase, replay, baseline } from './optimality-oracle.mjs';
import { constructSourceEntry, exactSourceWordMinSwaps } from './optimality-source-entry.mjs';

const source = ['v:42', 'v:43', 'v:44'], word = ['v:43', 'v:44'];
const target = ['v:43', 'v:44', 'v:44', 'v:42', 'v:43'];

test('min-E plus exact source entry can exceed twice the SWAP optimum', () => {
  const problem = normalizeCase({ source, target, spills: [], caps: { swap: 16, dup: 16 } });
  const actual = constructSourceEntry(problem, word);
  const exact = exactSourceWordMinSwaps(problem, word).get(target.join('|'));
  assert.equal(actual.swaps, 5);
  assert.equal(exact.swaps, 2);
  assert.deepEqual(actual.entry, ['v:43', 'v:42', 'v:44']);
  assert.equal(actual.entrySwaps, 3);
  assert.deepEqual(actual.assignment, [3, 0, 2, 4, 1]);
  replay(problem, actual.ops); replay(problem, exact.ops);
});

test('the production-reach counterexample exceeds twice the cost above baseline', () => {
  for (const weights of [{ gas: 1, bytes: 0 }, { gas: 0, bytes: 1 }]) {
    const problem = normalizeCase({ source, target, spills: [], caps: { swap: 16, dup: 16 }, weights });
    const actual = constructSourceEntry(problem, word);
    const exact = exactSourceWordMinSwaps(problem, word).get(target.join('|'));
    const candidate = replay(problem, actual.ops).score, optimum = replay(problem, exact.ops).score;
    assert.ok(candidate - baseline(problem) > 2 * (optimum - baseline(problem)));
    assert.ok(candidate <= 2 * optimum, 'this example does not refute the total EVM score bound');
  }
});
