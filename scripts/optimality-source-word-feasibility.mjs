#!/usr/bin/env node
/** Offline audit of fixed-word existence with an initial source. No production policy. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { normalizeCase, replay } from './optimality-oracle.mjs';

const key = values => values.join('|');
const count = (values, value) => values.filter(item => item === value).length;
const sameMultiset = (left, right) => key([...left].sort()) === key([...right].sort());
const direct = (problem, value) => value === 'wildcard' || value.startsWith('l:') ? ['push', value] :
  value.startsWith('v:') && problem.spills.includes(Number(value.slice(2))) ? ['load', Number(value.slice(2))] : null;

export function sourceWordFeasible(problem, word) {
  const { source, target, caps } = problem;
  assert.equal(caps.dup, caps.swap, 'the theorem uses equal SWAP and DUP reach');
  assert.ok(source.length <= caps.swap + 1, 'normalize the initially frozen prefix first');
  if (!sameMultiset([...source, ...word], target)) return false;
  for (let index = 0; index <= word.length; index++) {
    const prior = [...source, ...word.slice(0, index)];
    const frozen = target.slice(0, Math.max(0, prior.length - caps.swap));
    for (const value of new Set(frozen)) if (count(frozen, value) > count(prior, value)) return false;
    if (index < word.length && !direct(problem, word[index]) &&
        count(prior, word[index]) <= count(frozen, word[index])) return false;
  }
  return true;
}

/** Complete reachability on value stacks, with no quota or target-prefix pruning. */
export function exactSourceWordEndpoints(problem, word) {
  const initial = [...problem.source], states = new Map([[key(initial), initial]]), queue = [initial];
  let edges = 0;
  for (let cursor = 0; cursor < queue.length; cursor++) {
    const stack = queue[cursor], size = stack.length, next = size - problem.source.length;
    const moves = [];
    for (let depth = 1; depth <= problem.caps.swap && depth < size; depth++) {
      const lower = size - depth - 1;
      const moved = [...stack]; [moved[lower], moved[size - 1]] = [moved[size - 1], moved[lower]];
      moves.push(moved);
    }
    if (next < word.length) {
      const value = word[next];
      if (direct(problem, value)) moves.push([...stack, value]);
      for (let depth = 1; depth <= problem.caps.dup && depth <= size; depth++) {
        if (stack[size - depth] === value) moves.push([...stack, value]);
      }
    }
    edges += moves.length;
    for (const moved of moves) if (!states.has(key(moved))) { states.set(key(moved), moved); queue.push(moved); }
  }
  return { states: states.size, edges, endpoints: new Set([...states].filter(([, stack]) =>
    stack.length === problem.source.length + word.length).map(([state]) => state)) };
}

/** Execute the paper proof and check it with the independent instruction replay. */
export function realizeSourceWordForAudit(problem, word) {
  assert.ok(sourceWordFeasible(problem, word));
  const stack = [...problem.source], ops = [];
  let fixed = 0, boundarySwaps = 0;
  const swap = position => {
    const depth = stack.length - 1 - position;
    if (!depth) return;
    assert.ok(depth > 0 && depth <= problem.caps.swap);
    [stack[position], stack[stack.length - 1]] = [stack.at(-1), stack[position]];
    ops.push(['swap', depth]);
  };
  const fixNext = () => {
    if (stack[fixed] !== problem.target[fixed]) {
      const position = stack.indexOf(problem.target[fixed], fixed);
      assert.ok(position >= fixed, 'quota must supply the imminent output');
      swap(position); swap(fixed);
    }
    fixed++;
  };
  for (const value of word) {
    if (stack.length - fixed === problem.caps.swap + 1) {
      const before = ops.length; fixNext(); boundarySwaps += ops.length - before;
      assert.ok(ops.length - before <= 2);
    }
    const birth = direct(problem, value);
    if (birth) ops.push(birth);
    else {
      const position = stack.lastIndexOf(value), depth = stack.length - position;
      assert.ok(position >= fixed && depth >= 1 && depth <= problem.caps.dup);
      ops.push(['dup', depth]);
    }
    stack.push(value);
  }
  while (fixed < stack.length) fixNext();
  assert.deepEqual(stack, problem.target);
  const actual = replay(problem, ops);
  assert.deepEqual(actual.target, problem.target);
  assert.deepEqual(actual.added, word);
  return { ops, boundarySwaps };
}

function* words(size, values) {
  if (!size) { yield []; return; }
  for (const rest of words(size - 1, values)) for (const value of values) yield [...rest, value];
}
function* permutations(values, prefix = []) {
  if (!values.length) { yield prefix; return; }
  for (const value of new Set(values)) {
    const index = values.indexOf(value);
    yield* permutations([...values.slice(0, index), ...values.slice(index + 1)], [...prefix, value]);
  }
}

export function audit() {
  const profiles = [
    { values: ['l:0', 'l:1'], spills: [] },
    { values: ['v:42', 'l:0'], spills: [] },
    { values: ['v:42', 'v:43'], spills: [] },
    { values: ['v:42', 'v:43'], spills: [42] }
  ];
  let searches = 0, states = 0, edges = 0, cases = 0, feasible = 0, rejected = 0;
  for (const reach of [1, 2, 3]) for (let sourceSize = 0; sourceSize <= reach + 1; sourceSize++) {
    for (let wordSize = 0; wordSize <= Math.min(3, 6 - sourceSize); wordSize++) {
      for (const profile of profiles) for (const source of words(sourceSize, profile.values)) {
        for (const word of words(wordSize, profile.values)) {
          const base = { source, target: [...source, ...word], spills: profile.spills,
            caps: { swap: reach, dup: reach }, weights: { gas: 1, bytes: 0 } };
          const search = exactSourceWordEndpoints(normalizeCase(base), word);
          searches++; states += search.states; edges += search.edges;
          for (const target of permutations([...source, ...word])) {
            const problem = normalizeCase({ ...base, target }), expected = search.endpoints.has(key(target));
            assert.equal(sourceWordFeasible(problem, word), expected, JSON.stringify({ reach, source, word, target }));
            cases++;
            if (expected) { feasible++; realizeSourceWordForAudit(problem, word); }
            else rejected++;
          }
        }
      }
    }
  }
  return { status: 'finite exact evidence; general-source Lean theorem not yet proved',
    scope: 'Normalized sources of at most reach+1 values; no POP; fixed ordered birth values; exact target.',
    oracle: 'Complete value-stack reachability with every legal SWAP, matching DUP, and available direct birth. No target-prefix pruning.',
    domain: { reaches: [1, 2, 3], sourceLength: '0 through reach+1', birthLength: '0 through 3',
      totalLength: 'at most 6', profiles, targets: 'all distinct permutations of source plus birth word' },
    searches, states, edges, cases, feasible, rejected,
    reproduce: 'node scripts/optimality-source-word-feasibility.mjs Bench/evidence-source-word-feasibility.json' };
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const report = audit();
  fs.writeFileSync(process.argv[2] ?? 'Bench/evidence-source-word-feasibility.json', JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify(report));
}
