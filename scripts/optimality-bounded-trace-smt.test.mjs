import assert from 'node:assert/strict';
import test from 'node:test';
import { encodeBoundedTrace, solveBoundedTrace } from './optimality-bounded-trace-smt.mjs';

const run = (problem, budget, fixedOps = null) => solveBoundedTrace(encodeBoundedTrace(problem, budget,
  { timeoutMs: 5000, fixedOps }));
const enabled = { skip: !process.env.Z3_BIN };

test('bounded SMT independently replays a valid model', enabled, () => {
  const problem = { source: [], target: ['v:42', 'v:42'], spills: [42], caps: { swap: 1, dup: 1 } };
  const result = run(problem, 0);
  assert.equal(result.status, 'sat');
  assert.deepEqual(result.ops, [['load', 42], ['dup', 1]]);
});

test('bounded SMT distinguishes zero and one SWAP with one introduction per kind', enabled, () => {
  const problem = { source: [], target: ['v:42', 'v:43', 'v:42'], spills: [42, 43], caps: { swap: 1, dup: 1 } };
  assert.equal(run(problem, 0).status, 'unsat');
  const result = run(problem, 1);
  assert.equal(result.status, 'sat');
  assert.equal(result.swaps, 1);
});

test('bounded SMT accepts a fixed witness and rejects a changed endpoint', enabled, () => {
  const problem = { source: [], target: ['v:42', 'v:43', 'v:42'], spills: [42, 43], caps: { swap: 1, dup: 1 } };
  const witness = [['load', 42], ['dup', 1], ['load', 43], ['swap', 1]];
  assert.equal(run(problem, 1, witness).status, 'sat');
  assert.equal(run({ ...problem, target: ['v:43', 'v:42', 'v:42'] }, 1, witness).status, 'unsat');
});
