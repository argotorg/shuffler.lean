import assert from 'node:assert/strict';
import test from 'node:test';
import { compareCandidate, compareWitness, normalizeCase } from './optimality-oracle.mjs';
import { summarize } from './optimality-bench.mjs';

function record(id, target, candidateOps, witnessOps, oracle = { status: 'not-run', states: 0 }) {
  const problem = normalizeCase({ id, source: ['l:0', 'l:1'], target, weights: { gas: 0, bytes: 1 } });
  const comparison = compareCandidate(problem, { status: 'ok', ops: candidateOps }, oracle);
  comparison.witness = compareWitness(problem, candidateOps, witnessOps);
  return { problem, oracle, comparisons: { schedule: comparison } };
}

test('report measures a witness ratio below one and names its actual case', () => {
  const rows = [record('one-third', ['l:1', 'l:0'], [['swap', 1]], Array(3).fill(['swap', 1])),
    record('one-fifth', ['l:1', 'l:0'], [['swap', 1]], Array(5).fill(['swap', 1]))];
  const stats = summarize(rows, {}).algorithms.schedule;
  assert.equal(stats.maxWitnessExcessRatio, 1 / 3);
  assert.equal(stats.worstWitnessCase, 'one-third');
  assert.equal(stats.witnessPositiveExcessComparisons, 2);
  assert.deepEqual(stats.worstWitnessComparison, { caseId: 'one-third', baseline: 0,
    candidateScore: 1, witnessScore: 3, candidateExcess: 1, witnessExcess: 3 });
  assert.equal(rows[0].comparisons.schedule.witness.candidateScore, 1);
  assert.equal(rows[0].comparisons.schedule.witness.witnessScore, 3);
});

test('zero reference excess is counted separately from a measured finite ratio', () => {
  const rows = [record('positive-candidate', ['l:0', 'l:1'], Array(2).fill(['swap', 1]), []),
    record('both-baseline', ['l:0', 'l:1'], [], [])];
  const stats = summarize(rows, {}).algorithms.schedule;
  assert.equal(stats.maxWitnessExcessRatio, null);
  assert.equal(stats.worstWitnessCase, null);
  assert.equal(stats.witnessZeroExcessComparisons, 2);
  assert.equal(stats.witnessZeroExcessViolations, 1);
  assert.equal(stats.worstZeroExcessWitnessCase, 'positive-candidate');
});

test('exact-oracle approximation ratios remain distinct from witness ratios', () => {
  const rows = [record('oracle-exact', ['l:1', 'l:0'], [['swap', 1]], Array(3).fill(['swap', 1]),
    { status: 'optimal', states: 2, score: 1 })];
  const stats = summarize(rows, {}).algorithms.schedule;
  assert.equal(stats.oracleComparisons, 1);
  assert.equal(stats.maxCostRatio, 1);
  assert.equal(stats.maxExcessRatio, 1);
  assert.equal(stats.maxWitnessExcessRatio, 1 / 3);
});

test('a measured zero ratio still names the observed case', () => {
  const rows = [record('zero-candidate', ['l:0', 'l:1'], [], Array(2).fill(['swap', 1]))];
  const stats = summarize(rows, {}).algorithms.schedule;
  assert.equal(stats.maxWitnessExcessRatio, 0);
  assert.equal(stats.worstWitnessCase, 'zero-candidate');
});
