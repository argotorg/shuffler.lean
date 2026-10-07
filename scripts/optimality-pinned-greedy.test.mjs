import assert from 'node:assert/strict';
import test from 'node:test';
import { increasingPinnedSet } from './optimality-pinned-greedy.mjs';
import { deadlineJobs } from './optimality-birth-matching.mjs';
import { exactPinnedSets } from './optimality-pinned-quotas.mjs';

test('empty input has an empty maximum pinned set', () => {
  assert.deepEqual(increasingPinnedSet([], 1, []).pinned, []);
});

test('increasing selection finds three pins in the nonmatroid example', () => {
  const target = ['a', 'b', 'b', 'b', 'a'];
  const jobs = deadlineJobs([], target, 2, [0, 1, 2]).map(job => ({ value: job.value, deadline: job.deadline - 1 }));
  assert.deepEqual(increasingPinnedSet(target, 2, jobs).pinned, [0, 1, 3]);
});

test('infeasible generation quotas have no pinned completion', () => {
  const jobs = [{ value: 'a', deadline: 0 }, { value: 'b', deadline: 0 }];
  assert.equal(increasingPinnedSet(['a', 'b'], 1, jobs).status, 'infeasible');
});

test('increasing pinning can lose one identity on a length-six target', () => {
  const target = ['a', 'b', 'b', 'a', 'b', 'a'];
  const jobs = deadlineJobs([], target, 2, [1]).map(job => ({ value: job.value, deadline: job.deadline - 1 }));
  assert.deepEqual(increasingPinnedSet(target, 2, jobs).pinned, [0, 1, 3]);
  const family = exactPinnedSets(target, 2, jobs).feasible;
  assert.equal(Math.max(...family.flatMap((valid, mask) => valid ? [mask.toString(2).replaceAll('0', '').length] : [])), 4);
  assert.equal(family[1 + 2 + 16 + 32], true);
});
