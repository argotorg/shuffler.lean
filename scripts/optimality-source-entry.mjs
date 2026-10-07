#!/usr/bin/env node
/** Research only: exact entry into the virtual empty-source schedule. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { normalizeCase, replay } from './optimality-oracle.mjs';
import { fixedWordAssignment } from './optimality-fixed-word-matching.mjs';
import { sourceWordFeasible } from './optimality-source-word-feasibility.mjs';

const key = stack => stack.join('|');
const direct = (problem, value) => value === 'wildcard' || value.startsWith('l:') ? ['push', value] :
  value.startsWith('v:') && problem.spills.includes(Number(value.slice(2))) ? ['load', Number(value.slice(2))] : null;

/** Minimize SWAP count. Birth edges have zero cost. No target-prefix pruning. */
export function exactSourceWordMinSwaps(problem, word) {
  const initial = { stack: [...problem.source], swaps: 0, ops: [] };
  const distances = new Map([[key(initial.stack), initial]]), queue = [initial];
  while (queue.length) {
    queue.sort((a, b) => b.swaps - a.swaps);
    const current = queue.pop();
    if (distances.get(key(current.stack)) !== current) continue;
    const size = current.stack.length, next = size - problem.source.length, moves = [];
    for (let depth = 1; depth <= problem.caps.swap && depth < size; depth++) {
      const lower = size - depth - 1;
      if (current.stack[lower] === current.stack.at(-1)) continue;
      const stack = [...current.stack]; [stack[lower], stack[size - 1]] = [stack[size - 1], stack[lower]];
      moves.push({ stack, swaps: 1, op: ['swap', depth] });
    }
    if (next < word.length) {
      const value = word[next], birth = direct(problem, value), stack = [...current.stack, value];
      if (birth) moves.push({ stack, swaps: 0, op: birth });
      else for (let depth = 1; depth <= problem.caps.dup && depth <= size; depth++) {
        if (current.stack[size - depth] === value) { moves.push({ stack, swaps: 0, op: ['dup', depth] }); break; }
      }
    }
    for (const move of moves) {
      const nextState = { stack: move.stack, swaps: current.swaps + move.swaps, ops: [...current.ops, move.op] };
      if (nextState.swaps < (distances.get(key(nextState.stack))?.swaps ?? Infinity)) {
        distances.set(key(nextState.stack), nextState); queue.push(nextState);
      }
    }
  }
  return new Map([...distances].filter(([, record]) => record.stack.length === problem.source.length + word.length));
}

export function constructSourceEntry(problem, word) {
  if (!sourceWordFeasible(problem, word)) return null;
  const values = [...problem.source, ...word], sourceLength = problem.source.length;
  const matched = fixedWordAssignment(values, problem.target, problem.caps.swap);
  assert.equal(matched.status, 'optimal');
  const assignment = matched.assignment, tokens = [], future = [];
  let entry = [];
  for (let birth = 0; birth < values.length; birth++) {
    tokens.push(birth);
    if (birth >= sourceLength) future.push({ birth: values[birth] });
    while (assignment[tokens.at(-1)] < birth) {
      const lower = assignment[tokens.at(-1)], depth = birth - lower;
      assert.ok(depth > 0 && depth <= problem.caps.swap);
      [tokens[lower], tokens[birth]] = [tokens[birth], tokens[lower]];
      if (birth >= sourceLength) future.push({ swap: depth });
    }
    if (birth + 1 === sourceLength) entry = tokens.map(token => values[token]);
  }
  const entryProblem = normalizeCase({ ...problem, target: entry });
  const first = exactSourceWordMinSwaps(entryProblem, []).get(key(entry));
  assert.ok(first, 'source entry permutation must be reachable');
  const stack = [...entry], ops = [...first.ops];
  for (const step of future) {
    if (step.swap) {
      const lower = stack.length - step.swap - 1;
      [stack[lower], stack[stack.length - 1]] = [stack.at(-1), stack[lower]];
      ops.push(['swap', step.swap]);
    } else {
      const value = step.birth, birth = direct(problem, value);
      if (birth) ops.push(birth);
      else {
        const depth = stack.length - stack.lastIndexOf(value);
        assert.ok(depth > 0 && depth <= problem.caps.dup, 'virtual schedule must have a readable copy');
        ops.push(['dup', depth]);
      }
      stack.push(value);
    }
  }
  const actual = replay(problem, ops);
  assert.deepEqual(actual.added, word);
  const swaps = ops.filter(op => op[0] === 'swap').length;
  return { assignment, moved: matched.moved, entry, entrySwaps: first.swaps, futureSwaps: swaps - first.swaps, swaps, ops };
}

function* canonicalWords(size, prefix = []) {
  if (prefix.length === size) { yield prefix; return; }
  for (let value = 0; value < Math.min(3, new Set(prefix).size + 1); value++) yield* canonicalWords(size, [...prefix, value]);
}
function* permutations(values, prefix = []) {
  if (!values.length) { yield prefix; return; }
  for (const value of new Set(values)) {
    const index = values.indexOf(value);
    yield* permutations([...values.slice(0, index), ...values.slice(index + 1)], [...prefix, value]);
  }
}

export function auditSourceEntry() {
  let searches = 0, cases = 0, feasible = 0, maximumRatio = 0, worst = null;
  const failures = [];
  for (const reach of [1, 2, 3, 4, 16]) for (let size = 0; size <= 7; size++) {
    for (let sourceSize = 0; sourceSize <= Math.min(reach + 1, size); sourceSize++) {
      for (const abstract of canonicalWords(size)) {
        const values = abstract.map(value => `l:${value}`), source = values.slice(0, sourceSize), word = values.slice(sourceSize);
        const input = { source, target: values, spills: [], caps: { swap: reach, dup: reach } };
        const endpoints = exactSourceWordMinSwaps(normalizeCase(input), word); searches++;
        for (const target of permutations(values)) {
          cases++;
          const problem = normalizeCase({ ...input, target }), exact = endpoints.get(key(target));
          const actual = constructSourceEntry(problem, word);
          assert.equal(Boolean(actual), Boolean(exact), 'feasibility differs');
          if (!exact) continue;
          feasible++;
          if (exact.swaps === 0) assert.equal(actual.swaps, 0, 'zero optimum increased');
          else if (actual.swaps / exact.swaps > maximumRatio) {
            maximumRatio = actual.swaps / exact.swaps;
            worst = { reach, source, word, target, exactSwaps: exact.swaps, exactOps: exact.ops, ...actual };
          }
          if (actual.swaps > 2 * exact.swaps) {
            failures.push({ reach, source, word, target, exactSwaps: exact.swaps, exactOps: exact.ops, ...actual });
            return { status: 'counterexample found; not a production mode', searches, cases, feasible, maximumRatio, worst, failures };
          }
        }
      }
    }
    console.error(`source-entry R=${reach} total=${size}: ${cases} cases; max ratio ${maximumRatio}`);
  }
  return { status: 'finite exact evidence only; no general-source factor-two theorem', searches, cases, feasible, maximumRatio, worst, failures,
    domain: { reaches: [1, 2, 3, 4, 16], totalLength: '0 through 7', sourceLength: '0 through min(reach+1,totalLength)',
      values: 'all canonical three-value words', targets: 'all distinct permutations', costs: 'birth edges zero, each SWAP one' } };
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const report = auditSourceEntry();
  fs.writeFileSync(process.argv[2] ?? 'Bench/evidence-source-entry.json', JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify(report));
}
