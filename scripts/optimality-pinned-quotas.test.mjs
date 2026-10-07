import assert from 'node:assert/strict';
import test from 'node:test';
import { pinnedQuotaPlan, exactPinnedSets } from './optimality-pinned-quotas.mjs';
import { deadlineJobs } from './optimality-birth-matching.mjs';

test('empty pinned problem has an empty completion', () => {
  const result = pinnedQuotaPlan([], 1, [], []);
  assert.equal(result.status, 'feasible');
  assert.deepEqual(result.word, []);
  assert.deepEqual(result.assignment, []);
  assert.deepEqual(exactPinnedSets([], 1, []).feasible, [true]);
});

test('a pinned birth cannot supply an earlier generation job', () => {
  const target = ['b', 'b', 'a'];
  const jobs = [{ value: 'a', deadline: 0 }, { value: 'b', deadline: 20 }, { value: 'b', deadline: 20 }];
  assert.equal(pinnedQuotaPlan(target, 16, jobs, []).status, 'feasible');
  assert.equal(pinnedQuotaPlan(target, 16, jobs, [2]).status, 'infeasible');
  assert.equal(exactPinnedSets(target, 16, jobs).feasible[4], false);
});

test('pinned slots must leave enough positions before a retained-value deadline', () => {
  const target = ['a', 'b', 'a'];
  const jobs = deadlineJobs([], target, 1, [0]).map(job => ({ value: job.value, deadline: job.deadline - 1 }));
  assert.equal(pinnedQuotaPlan(target, 1, jobs, [0]).status, 'feasible');
  assert.equal(pinnedQuotaPlan(target, 1, jobs, [1]).status, 'infeasible');
  assert.deepEqual(exactPinnedSets(target, 1, jobs).feasible, [true, true, false, false, false, false, false, false]);
});

test('invalid pins and job counts are rejected', () => {
  assert.throws(() => pinnedQuotaPlan(['a'], 1, [{ value: 'b', deadline: 0 }], []), /counts/);
  assert.throws(() => pinnedQuotaPlan(['a'], 1, [{ value: 'a', deadline: 0 }], [0, 0]), /pinned/);
  assert.throws(() => pinnedQuotaPlan(['a'], 0, [{ value: 'a', deadline: 0 }], []), /reach/);
});

test('all-reuse pinned sets do not satisfy matroid exchange', () => {
  const target = ['a', 'b', 'b', 'b', 'a'];
  const jobs = deadlineJobs([], target, 2, [0, 1, 2]).map(job => ({ value: job.value, deadline: job.deadline - 1 }));
  for (const pinned of [[2], [1, 3]]) assert.equal(pinnedQuotaPlan(target, 2, jobs, pinned).status, 'feasible');
  for (const pinned of [[1, 2], [2, 3]]) assert.equal(pinnedQuotaPlan(target, 2, jobs, pinned).status, 'infeasible');
  const exact = exactPinnedSets(target, 2, jobs).feasible;
  assert.equal(exact[4], true);
  assert.equal(exact[10], true);
  assert.equal(exact[6], false);
  assert.equal(exact[12], false);
});
