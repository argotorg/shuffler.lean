import assert from 'node:assert/strict';
import test from 'node:test';
import { fixedPointsFeasible, sortedResidualAssignment, exactAssignments } from './optimality-fixed-points.mjs';

test('keeping an equal position can consume required Hall slack', () => {
  const word = ['b', 'a', 'a'], target = ['a', 'a', 'b'];
  assert.equal(fixedPointsFeasible(word, target, 1, []), true);
  assert.equal(fixedPointsFeasible(word, target, 1, [1]), false);
  assert.deepEqual(exactAssignments(word, target, 1), [[2, 0, 1]]);
  assert.deepEqual(sortedResidualAssignment(word, target, 1, []), [2, 0, 1]);
  assert.equal(exactAssignments(word, target, 1)[0].filter((final, birth) => final !== birth).length, 3);
  assert.equal(word.filter((value, position) => value !== target[position]).length, 2);
});

test('duplicate matching retains both correct positions when reach permits', () => {
  const word = ['a', 'a', 'b', 'b'], target = ['b', 'a', 'b', 'a'];
  assert.equal(fixedPointsFeasible(word, target, 3, [1, 2]), true);
  assert.deepEqual(sortedResidualAssignment(word, target, 3, [1, 2]), [3, 1, 2, 0]);
  assert.equal(fixedPointsFeasible(word, target, 1, []), false);
});

test('fixed-point criterion handles empty input and rejects invalid subsets', () => {
  assert.equal(fixedPointsFeasible([], [], 1, []), true);
  assert.deepEqual(sortedResidualAssignment([], [], 1, []), []);
  assert.equal(fixedPointsFeasible(['a'], ['b'], 1, []), false);
  assert.equal(fixedPointsFeasible(['a'], ['a'], 1, [0, 0]), false);
  assert.equal(fixedPointsFeasible(['a'], ['a'], 1, [1]), false);
});
