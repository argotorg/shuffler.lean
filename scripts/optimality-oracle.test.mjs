import assert from 'node:assert/strict';
import test from 'node:test';
import { baseline, compareWitness, normalizeCase, replay, reserve, solve } from './optimality-oracle.mjs';
import { casesFor } from './optimality-bench.mjs';
import { gapCount, gapPotential } from './optimality-bounds.mjs';

const problem = (source, target, extra = {}) => normalizeCase({
  id: 'test', source, target, spills: [], weights: { gas: 1, bytes: 1 }, ...extra,
});

test('empty and unchanged stacks have zero optimum', () => {
  for (const source of [[], ['v:1'], ['l:1', 'l:2']]) {
    const p = problem(source, source);
    const result = solve(p);
    assert.equal(result.status, 'optimal');
    assert.deepEqual(result.cost, { gas: 0, bytes: 0 });
    assert.deepEqual(result.ops, []);
  }
});

test('actual top-swap distance and birth order agree with small witnesses', () => {
  const swapped = solve(problem(['v:1', 'v:2', 'v:3'], ['v:2', 'v:1', 'v:3']));
  assert.equal(swapped.cost.gas, 9);
  assert.equal(swapped.cost.bytes, 3);
  const born = solve(problem(['v:1'], ['l:2', 'l:1', 'v:1']));
  assert.deepEqual(born.cost, { gas: 9, bytes: 5 });
});

test('missing unspilled values, removed values, and inconsistent H reject', () => {
  for (const p of [
    problem([], ['v:1']),
    problem(['v:1'], []),
    problem(['v:1'], ['v:1', 'v:1'], { missing: [] }),
  ]) {
    assert.equal(reserve(p), false);
    assert.equal(solve(p).status, 'infeasible');
  }
});

test('replay rejects illegal opcodes and exact-H mismatches', () => {
  const p = problem(['v:1'], ['v:1', 'v:1']);
  for (const ops of [[['dup', 0]], [['dup', 2]], [['swap', 0]], [['load', 1]],
    [['push', 'v:1']], [['pop']], []]) {
    assert.throws(() => replay(p, ops));
  }
  assert.deepEqual(replay(p, [['dup', 1]]).cost, { gas: 3, bytes: 1 });
});

test('DUP16 and SWAP16 have different boundary slots', () => {
  const source = ['v:1', ...Array(16).fill('l:0')];
  const target = [...Array(16).fill('l:0'), 'v:1', 'v:1'];
  const p = problem(source, target);
  assert.equal(reserve(p), true);
  assert.throws(() => replay(p, [['dup', 17]]));
  assert.deepEqual(replay(p, [['swap', 16], ['dup', 1]]).cost, { gas: 6, bytes: 2 });
});

test('the combined boundary and seed condition counts two copies', () => {
  const p = problem(['v:1', ...Array(16).fill('l:0')],
    ['v:1', ...Array(16).fill('l:0'), 'v:1']);
  assert.equal(reserve(p), false);
  assert.equal(solve(p).status, 'infeasible');
});

test('encoding widths are derived from actual literal values', () => {
  assert.deepEqual(solve(problem([], ['l:0'])).cost, { gas: 2, bytes: 1 });
  assert.deepEqual(solve(problem([], ['l:255'])).cost, { gas: 3, bytes: 2 });
  assert.deepEqual(solve(problem([], ['l:256'])).cost, { gas: 3, bytes: 3 });
  const wide = `l:${1n << 248n}`;
  assert.deepEqual(solve(problem([], [wide])).cost, { gas: 3, bytes: 33 });
  assert.throws(() => problem([], [`l:${1n << 256n}`]));
});

test('the cost model distinguishes actual PUSH0 addresses and the C++ estimate', () => {
  const args = { spills: [1], loadWidths: [[1, 0]] };
  assert.deepEqual(solve(problem([], ['v:1'], { ...args, gasModel: 'evm' })).cost,
    { gas: 5, bytes: 2 });
  assert.deepEqual(solve(problem([], ['v:1'], { ...args, gasModel: 'cpp' })).cost,
    { gas: 6, bytes: 2 });
});

test('baseline includes one required introduction and cheap later copies', () => {
  const wide = `l:${1n << 248n}`;
  const p = problem([], [wide, wide], { weights: { gas: 0, bytes: 1 } });
  assert.equal(baseline(p), 34);
  assert.equal(solve(p).score, 34);
});

test('a state budget reports a limit, not an infeasibility result', () => {
  const result = solve(problem(['v:1', 'v:2'], ['v:2', 'v:1']), { stateLimit: 1 });
  assert.equal(result.status, 'limit');
  assert.equal(result.reason, 'state-limit');
});

test('reduced caps are explicit and retain the actual ordinal convention', () => {
  const p = problem(['v:1'], ['l:1', 'l:1', 'l:1', 'v:1'], {
    caps: { swap: 2, dup: 2 }, weights: { gas: 0, bytes: 1 },
  });
  assert.equal(p.model, 'reduced-cap');
  const result = solve(p);
  assert.equal(result.cost.bytes, 6);
  assert.deepEqual(replay(p, result.ops).target, p.target);
});

test('zero weights and unsafe integer costs cannot enter the model', () => {
  assert.throws(() => problem([], [], { weights: { gas: 0, bytes: 0 } }));
  assert.throws(() => problem([], [], { weights: { gas: -1, bytes: 1 } }));
  assert.throws(() => problem([], [], { weights: { gas: Number.MAX_SAFE_INTEGER + 1, bytes: 1 } }));
});

test('Reserve agrees with an independent exact search on finite small inputs', () => {
  const words = length => length === 0 ? [[]] : words(length - 1)
    .flatMap(prefix => ['l:0', 'v:1'].map(value => [...prefix, value]));
  for (const cap of [2, 16]) for (let size = 0; size <= 3; size++) {
    for (let final = size; final <= 4; final++) for (const source of words(size)) {
      for (const target of words(final)) for (const spills of [[], [1]]) {
        const p = problem(source, target, { spills, caps: { swap: cap, dup: cap } });
        const result = solve(p, { stateLimit: 10000 });
        assert.notEqual(result.status, 'limit');
        assert.equal(result.status === 'optimal', reserve(p), JSON.stringify(p));
        if (result.status === 'optimal') assert.deepEqual(replay(p, result.ops).target, target);
      }
    }
  }
});

test('seeded holdout cases are reproducible and generated witnesses replay', () => {
  for (const suite of ['small', 'boundary', 'random', 'medium', 'sparse', 'no-growth', 'loads', 'mixed', 'planted', 'planted-chains']) {
    const first = casesFor(suite, 2026100711, 30);
    assert.deepEqual(first, casesFor(suite, 2026100711, 30));
    assert.notDeepEqual(first, casesFor(suite, 2026100712, 30));
    for (const p of first) {
      assert.equal(reserve(p), true);
      if (p.referenceOps) assert.deepEqual(replay(p, p.referenceOps).target, p.target);
    }
  }
});


test('a replayed witness can disprove factor two without an oracle', () => {
  const p = problem(['v:1', 'v:2'], ['v:2', 'v:1']);
  const witness = [['swap', 1]];
  const candidate = [['swap', 1], ['swap', 1], ['swap', 1]];
  const result = compareWitness(p, candidate, witness);
  assert.equal(result.baseline, 0);
  assert.equal(result.candidateScore, 12);
  assert.equal(result.witnessScore, 4);
  assert.equal(result.twiceExcessViolation, true);
  assert.equal(compareWitness(p, witness, witness).twiceExcessViolation, false);
  assert.throws(() => compareWitness(p, candidate, []), /endpoint/);
  assert.throws(() => compareWitness(p, [], witness), /endpoint/);
});

test('witness comparison includes the generation baseline', () => {
  const p = problem(['v:1'], ['v:1', 'l:0']);
  const witness = [['push', 'l:0']];
  const candidate = [...witness, ['swap', 1], ['swap', 1]];
  const result = compareWitness(p, candidate, witness);
  assert.equal(result.baseline, 3);
  assert.equal(result.witnessScore, 3);
  assert.equal(result.twiceExcessViolation, true);
  assert.equal(result.excessRatioAgainstWitness, 'inf');
});


test('gap counts retain separate wide intervals and their boundary cases', () => {
  const stack = ['v:1', ...Array(16).fill('l:0'), 'v:1', ...Array(16).fill('l:0'), 'v:1'];
  assert.equal(gapPotential(stack, 'v:1', 16), 2);
  assert.equal(gapCount(stack, 'v:1', 16), 2);
  assert.equal(Math.ceil(gapPotential(stack, 'v:1', 16) / 16), 1);
  assert.equal(gapCount([], 'v:1', 16), 0);
  assert.equal(gapCount(Array(16).fill('l:0').concat('v:1'), 'v:1', 16), 1);
  assert.equal(gapCount(Array(17).fill('l:0').concat('v:1'), 'v:1', 16), 2);
});

test('finite local operations respect the experimental gap count', () => {
  let words = [[]];
  for (let size = 0; size <= 7; size++) {
    for (const stack of words) for (const cap of [1, 2, 3, 16]) for (const value of ['l:0', 'v:1']) {
      const before = gapCount(stack, value, cap);
      for (let depth = 1; depth <= Math.min(cap, size); depth++) if (stack[size - depth] === value) {
        assert.equal(gapCount([...stack, value], value, cap), before);
      }
      for (let depth = 1; depth <= Math.min(cap, size - 1); depth++) {
        const next = [...stack], lower = size - depth - 1;
        [next[lower], next[size - 1]] = [next[size - 1], next[lower]];
        assert.ok(gapCount(next, value, cap) <= before + (stack[lower] === value ? 1 : 0));
      }
      if (size) assert.ok(gapCount(stack.slice(0, -1), value, cap) <= before);
    }
    words = words.flatMap(word => ['l:0', 'v:1'].map(value => [...word, value]));
  }
});
