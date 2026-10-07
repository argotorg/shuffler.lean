import assert from 'node:assert/strict';
import test from 'node:test';
import { normalizeCase, replay, score, solve, solvePareto } from './optimality-oracle.mjs';
import { frontierWeights, mixedParetoCases } from './optimality-mixed-pareto.mjs';

const normalize = input => normalizeCase({ id: 'pareto-test', ...input });

test('mixed cases include the exact 31:3 crossover and both sides', () => {
  const p = mixedParetoCases()[0];
  const result = solvePareto(p);
  assert.equal(result.status, 'optimal');
  assert.deepEqual(result.frontier.map(point => point.cost), [{ gas: 27, bytes: 73 }, { gas: 30, bytes: 42 }]);
  const weights = frontierWeights(result.frontier);
  for (const expected of [{ gas: 10, bytes: 1 }, { gas: 31, bytes: 3 }, { gas: 11, bytes: 1 }]) {
    assert.ok(weights.some(weight => weight.gas === expected.gas && weight.bytes === expected.bytes));
    const weighted = normalize({ ...p, weights: expected });
    assert.equal(Math.min(...result.frontier.map(point => score(weighted, point.cost))), solve(weighted).score);
  }
});

test('Pareto costs include both wide PUSH and carry choices', () => {
  const wide = `l:${1n << 248n}`;
  const p = normalize({ source: [wide, ...Array(15).fill('l:0')],
    target: [wide, ...Array(16).fill('l:0'), wide] });
  const result = solvePareto(p);
  assert.equal(result.status, 'optimal');
  assert.deepEqual(result.frontier.map(point => point.cost), [{ gas: 5, bytes: 34 }, { gas: 8, bytes: 3 }]);
  for (const point of result.frontier) assert.deepEqual(replay(p, point.ops).cost, point.cost);
  for (const weights of [{ gas: 0, bytes: 1 }, { gas: 1, bytes: 0 },
    { gas: 1, bytes: 1 }, { gas: 1, bytes: 3 }, { gas: 3, bytes: 1 }]) {
    const weighted = normalize({ ...p, weights });
    const exact = solve(weighted);
    assert.equal(Math.min(...result.frontier.map(point => score(weighted, point.cost))), exact.score);
  }
});

test('equal LOAD and carry cost pairs produce one frontier point', () => {
  const p = normalize({ source: ['v:1', ...Array(15).fill('l:0')],
    target: ['v:1', ...Array(16).fill('l:0'), 'v:1'], spills: [1], loadWidths: [[1, 0]] });
  const result = solvePareto(p);
  assert.equal(result.status, 'optimal');
  assert.deepEqual(result.frontier.map(point => point.cost), [{ gas: 8, bytes: 3 }]);
  assert.deepEqual(replay(p, result.frontier[0].ops).cost, result.frontier[0].cost);
});

test('Pareto search returns an exact zero frontier and detects infeasibility', () => {
  const p = normalize({ source: ['v:1'], target: ['v:1'] });
  const result = solvePareto(p);
  assert.equal(result.status, 'optimal');
  assert.deepEqual(result.frontier.map(point => point.cost), [{ gas: 0, bytes: 0 }]);
  assert.deepEqual(result.frontier[0].ops, []);
  for (const input of [{ source: [], target: ['v:1'] },
    { source: ['v:1'], target: [] }, { source: [], target: ['l:0'], missing: [] }]) {
    assert.equal(solvePareto(normalize(input)).status, 'infeasible');
  }
});

test('Pareto state and label limits never claim an optimum', () => {
  const p = normalize({ source: ['v:1', 'v:2'], target: ['v:2', 'v:1'] });
  assert.equal(solvePareto(p, { stateLimit: 1 }).status, 'limit');
  assert.equal(solvePareto(p, { labelLimit: 1 }).status, 'limit');
  assert.throws(() => solvePareto(p, { stateLimit: 0 }));
  assert.throws(() => solvePareto(p, { labelLimit: 0 }));
});

test('Pareto and scalar searches agree on finite reduced and actual caps', () => {
  const values = ['l:0', 'l:256', 'v:1'];
  const words = length => length ? words(length - 1).flatMap(prefix =>
    values.map(value => [...prefix, value])) : [[]];
  for (const cap of [1, 16]) for (let size = 0; size <= 2; size++) {
    for (const source of words(size)) for (const target of words(3)) {
      const p = normalize({ source, target, spills: [1], loadWidths: [[1, 0]],
        caps: { swap: cap, dup: cap } });
      const frontier = solvePareto(p);
      assert.notEqual(frontier.status, 'limit');
      for (const weights of [{ gas: 1, bytes: 0 }, { gas: 0, bytes: 1 },
        { gas: 1, bytes: 4 }, { gas: 3, bytes: 2 }]) {
        const weighted = normalize({ ...p, weights });
        const exact = solve(weighted);
        assert.equal(frontier.status, exact.status);
        if (exact.status !== 'optimal') continue;
        assert.equal(Math.min(...frontier.frontier.map(point => score(weighted, point.cost))), exact.score);
        for (const point of frontier.frontier) assert.deepEqual(replay(p, point.ops).cost, point.cost);
      }
    }
  }
});
