import assert from 'node:assert/strict';
import test from 'node:test';
import { solveQuotaLP } from './optimality-quota-lp.mjs';

const solverAvailable = Boolean(process.env.Z3_BIN);

test('LP handles empty input and forced exchange', { skip: !solverAvailable }, () => {
  assert.equal(solveQuotaLP([], 1, []).objective, 0);
  const jobs = [{ value: 'b', deadline: 0 }, { value: 'a', deadline: 1 }];
  const result = solveQuotaLP(['a', 'b'], 1, jobs);
  assert.equal(result.status, 'optimal');
  assert.equal(result.objective, 2);
  assert.deepEqual(result.matrix, [['0/1', '1/1'], ['1/1', '0/1']]);
});

test('LP rejects two jobs due in the first slot', { skip: !solverAvailable }, () => {
  const jobs = [{ value: 'a', deadline: 0 }, { value: 'b', deadline: 0 }];
  assert.equal(solveQuotaLP(['a', 'b'], 1, jobs).status, 'infeasible');
});
