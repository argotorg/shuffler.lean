import assert from 'node:assert/strict';
import test from 'node:test';
import { constructFixedWord, exactFixedWordMinima } from './optimality-fixed-word-bound.mjs';
import { normalizeCase, replay } from './optimality-oracle.mjs';

test('empty fixed word has zero exact and constructed cost', () => {
  const problem = normalizeCase({ source: [], target: [] });
  assert.equal(exactFixedWordMinima(problem, []).endpoints.get('').score, 0);
  assert.equal(constructFixedWord(problem, []).score, 0);
});

test('fixed word can force movement of an equal value position', () => {
  const word = ['v:43', 'v:42', 'v:42'];
  const problem = normalizeCase({ source: [], target: ['v:42', 'v:42', 'v:43'], spills: [42, 43],
    weights: { gas: 0, bytes: 1 }, caps: { swap: 1, dup: 1 } });
  const candidate = constructFixedWord(problem, word);
  const exact = exactFixedWordMinima(problem, word).endpoints.get(problem.target.join('|'));
  assert.equal(candidate.E, 3);
  assert.equal(candidate.swaps, 2);
  assert.equal(candidate.generationScore, 9);
  assert.equal(candidate.score, 11);
  assert.equal(exact.score, 11);
  assert.deepEqual(replay(problem, exact.ops).added, word);
});

test('PUSH0 replaces a reachable DUP when its gas cost is lower', () => {
  const word = ['l:0', 'l:0'];
  const problem = normalizeCase({ source: [], target: word, weights: { gas: 1, bytes: 0 } });
  const candidate = constructFixedWord(problem, word);
  assert.deepEqual(candidate.ops, [['push', 'l:0'], ['push', 'l:0']]);
  assert.equal(candidate.score, 4);
  assert.equal(exactFixedWordMinima(problem, word).endpoints.get(word.join('|')).score, 4);
});

test('unavailable direct birth and a missed endpoint deadline are infeasible', () => {
  const inaccessible = normalizeCase({ source: [], target: ['v:42'] });
  assert.equal(constructFixedWord(inaccessible, ['v:42']).status, 'infeasible');
  assert.equal(exactFixedWordMinima(inaccessible, ['v:42']).endpoints.size, 0);
  const word = ['v:43', 'v:43', 'v:42'];
  const deadline = normalizeCase({ source: [], target: ['v:42', 'v:43', 'v:43'], spills: [42, 43], caps: { swap: 1, dup: 1 } });
  assert.equal(constructFixedWord(deadline, word).status, 'infeasible');
  assert.equal(exactFixedWordMinima(deadline, word).endpoints.has(deadline.target.join('|')), false);
});

test('fixed word must have the target multiset and an empty source', () => {
  const problem = normalizeCase({ source: [], target: ['l:0'] });
  assert.throws(() => exactFixedWordMinima(problem, ['l:1']), /multiset/);
  assert.throws(() => constructFixedWord(problem, []), /length/);
  const nonempty = normalizeCase({ source: ['l:0'], target: ['l:0'] });
  assert.throws(() => constructFixedWord(nonempty, ['l:0']), /empty/);
});

test('minimum moved support need not give the minimum SWAP count', () => {
  const word = ['v:42', 'v:42', 'v:43', 'v:43', 'v:43', 'v:44'];
  const target = ['v:43', 'v:43', 'v:44', 'v:42', 'v:42', 'v:43'];
  const problem = normalizeCase({ source: [], target, spills: [42, 43, 44],
    weights: { gas: 1, bytes: 0 }, caps: { swap: 3, dup: 3 } });
  const candidate = constructFixedWord(problem, word);
  const exact = exactFixedWordMinima(problem, word).endpoints.get(target.join('|'));
  assert.equal(candidate.E, 6);
  assert.equal(candidate.swaps, 5);
  assert.equal(exact.ops.filter(op => op[0] === 'swap').length, 3);
  assert.equal(candidate.generationScore, 27);
  assert.equal(candidate.score - candidate.generationScore, 15);
  assert.equal(exact.score - candidate.generationScore, 9);
});
