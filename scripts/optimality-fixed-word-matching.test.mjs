import test from 'node:test';
import assert from 'node:assert/strict';
import { minimumAssignment } from './optimality-birth-matching.mjs';
import { fixedWordAssignment, introductionCuts } from './optimality-fixed-word-matching.mjs';

const words = size => size === 0 ? [[]] : words(size - 1).flatMap(prefix => ['a', 'b'].map(value => [...prefix, value]));

test('reservation sweep agrees with exact endpoint assignment on binary words', () => {
  for (let size = 0; size <= 6; size++) {
    const all = words(size);
    for (const word of all) for (const target of all) {
      if (word.filter(value => value === 'a').length !== target.filter(value => value === 'a').length) continue;
      for (const reach of [1, 2, 3]) {
        const costs = word.map((value, birth) => target.map((wanted, output) =>
          value === wanted && birth <= output + reach ? Number(birth !== output) : Infinity));
        const exact = minimumAssignment(costs), actual = fixedWordAssignment(word, target, reach);
        assert.equal(actual.status, exact.status);
        if (actual.status === 'optimal') assert.equal(actual.moved, exact.cost);
      }
    }
  }
});

test('a correct value position can need movement to satisfy endpoint deadlines', () => {
  const word = ['b', 'a', 'b', 'a'], target = ['a', 'a', 'b', 'b'];
  const result = fixedWordAssignment(word, target, 2);
  assert.equal(result.moved, 3);
  assert.equal(word.filter((value, index) => value !== target[index]).length, 2);
  assert.notEqual(result.assignment[1], 1);
});

test('birth-prefix availability keeps copy identities separate', () => {
  const word = ['a', 'b', 'a', 'b', 'b'], target = ['a', 'b', 'b', 'b', 'a'];
  const result = fixedWordAssignment(word, target, 2);
  assert.equal(result.moved, 2);
  assert.deepEqual(result.assignment, [0, 1, 4, 3, 2]);
  assert.deepEqual(introductionCuts(word, target, 2).direct, [{ birth: 0, value: 'a' }, { birth: 1, value: 'b' }]);
});

test('empty, count-balance, reach, and frozen-prefix boundary cases are checked', () => {
  assert.equal(fixedWordAssignment([], [], 1).moved, 0);
  assert.equal(fixedWordAssignment(['a'], ['b'], 1).status, 'infeasible');
  assert.equal(fixedWordAssignment(['b', 'b', 'a'], ['a', 'b', 'b'], 1).status, 'infeasible');
  assert.throws(() => fixedWordAssignment([], [], 0));
  assert.throws(() => fixedWordAssignment(['a'], [], 1));
  assert.deepEqual(introductionCuts(['a', 'b', 'a'], ['a', 'b', 'a'], 2).direct,
    [{ birth: 0, value: 'a' }, { birth: 1, value: 'b' }]);
  assert.deepEqual(introductionCuts(['a', 'b', 'b', 'a'], ['a', 'b', 'b', 'a'], 2).direct,
    [{ birth: 0, value: 'a' }, { birth: 1, value: 'b' }, { birth: 3, value: 'a' }]);
});
