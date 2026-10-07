#!/usr/bin/env node
/** Offline construction and audit for a fixed birth-to-target assignment. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { normalizeCase, replay } from './optimality-oracle.mjs';
import { random } from './optimality-bench.mjs';

const count = (values, value) => values.filter(item => item === value).length;

export function extractAssignment(problem, ops) {
  assert.equal(problem.source.length, 0, 'source must be empty');
  replay(problem, ops);
  const births = [], stack = [];
  for (const op of ops) {
    if (op[0] === 'swap') {
      const lower = stack.length - op[1] - 1;
      [stack[lower], stack[stack.length - 1]] = [stack.at(-1), stack[lower]];
    } else {
      const value = op[0] === 'dup' ? births[stack[stack.length - op[1]]].value :
        op[0] === 'load' ? `v:${op[1]}` : op[1];
      stack.push(births.length); births.push({ kind: op[0], value });
    }
  }
  const assignment = Array(births.length);
  stack.forEach((birth, position) => { assignment[birth] = position; });
  return { births, assignment };
}

export function realizeAssignment(problem, births, assignment) {
  const size = births.length, reach = problem.caps.swap;
  assert.equal(problem.source.length, 0, 'source must be empty');
  assert.ok(assignment.length === size && size === problem.target.length && new Set(assignment).size === size &&
    assignment.every(position => Number.isInteger(position) && position >= 0 && position < size), 'assignment is not a bijection');
  assert.ok(assignment.every((position, index) => births[index].value === problem.target[position]), 'assignment changes a value');
  assert.ok(assignment.every((position, index) => index <= position + reach), 'assignment exceeds the birth lag');
  const stack = [], ops = [], earlierValues = [];
  for (let index = 0; index < size; index++) {
    const birth = births[index];
    if (birth.kind === 'dup') {
      assert.ok(count(earlierValues, birth.value) > count(problem.target.slice(0, Math.max(0, index - reach)), birth.value), 'DUP prefix count fails');
      const position = stack.findLastIndex(token => births[token].value === birth.value), depth = stack.length - position;
      assert.ok(position >= 0 && depth <= reach, 'DUP is not reachable');
      ops.push(['dup', depth]);
    } else if (birth.kind === 'load') ops.push(['load', Number(birth.value.slice(2))]);
    else if (birth.kind === 'push') ops.push(['push', birth.value]);
    else throw new Error('unsupported birth kind');
    earlierValues.push(birth.value); stack.push(index);
    while (assignment[stack.at(-1)] < index) {
      const lower = assignment[stack.at(-1)], depth = index - lower;
      assert.ok(depth >= 1 && depth <= reach, 'SWAP is not reachable');
      [stack[lower], stack[index]] = [stack[index], stack[lower]];
      ops.push(['swap', depth]);
    }
  }
  const observed = replay(problem, ops), swaps = ops.filter(op => op[0] === 'swap').length;
  const E = assignment.filter((position, index) => position !== index).length;
  const D = assignment.reduce((sum, position, index) => sum + Math.ceil(Math.abs(index - position) / reach), 0);
  const seen = new Set(); let cycles = 0;
  for (let index = 0; index < size; index++) if (!seen.has(index)) {
    cycles++; let current = index;
    while (!seen.has(current)) { seen.add(current); current = assignment[current]; }
  }
  assert.equal(swaps, size - cycles, 'cycle SWAP count differs');
  assert.ok(swaps <= E, 'constructed SWAP count exceeds moved token support');
  assert.ok(swaps <= D, 'constructed SWAP count exceeds D');
  assert.deepEqual(observed.added, births.map(birth => birth.value), 'birth value order differs');
  return { ops, swaps, E, D, cycles, ...observed };
}

function* permutations(values, prefix = []) {
  if (!values.length) { yield prefix; return; }
  for (const value of values) yield* permutations(values.filter(other => other !== value), [...prefix, value]);
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-assignment-realizer.json';
  let fixedPlans = 0, extractedPlans = 0, originalSwaps = 0, constructedSwaps = 0, maximumEOverSwaps = null, maximumDOverSwaps = null;
  const failures = []; const seed = 2026100743, next = random(seed), choose = values => values[Math.floor(next() * values.length)];
  for (const reach of [1, 2, 3, 4, 16]) for (let size = 0; size <= 7; size++) {
    const target = Array.from({ length: size }, (_, index) => `v:${42 + index % 3}`);
    const problem = normalizeCase({ source: [], target, spills: [42, 43, 44], caps: { swap: reach, dup: reach } });
    for (const assignment of permutations(Array.from({ length: size }, (_, index) => index))) {
      if (assignment.some((position, index) => index > position + reach)) continue;
      const values = assignment.map(position => target[position]);
      const births = values.map((value, index) => ({ value,
        kind: count(values.slice(0, index), value) > count(target.slice(0, Math.max(0, index - reach)), value) ? 'dup' : 'load' }));
      try { realizeAssignment(problem, births, assignment); fixedPlans++; }
      catch (error) { failures.push({ problem, births, assignment, error: error.message }); }
    }
  }
  for (const reach of [1, 2, 3, 4, 5, 16]) for (let sample = 0; sample < 1000; sample++) {
    const births = choose([0, 1, reach, reach + 1, 2 * reach + 1, 4 * reach]);
    const stack = [], ops = [], spills = [42, 43, 44, 45, 46];
    const swap = () => {
      if (stack.length < 2) return;
      const depth = 1 + Math.floor(next() * Math.min(reach, stack.length - 1)), lower = stack.length - depth - 1;
      [stack[lower], stack[stack.length - 1]] = [stack.at(-1), stack[lower]]; ops.push(['swap', depth]);
    };
    for (let index = 0; index < births; index++) {
      if (next() < .8) swap(); if (next() < .3) swap();
      if (stack.length && next() < .65) {
        const depth = 1 + Math.floor(next() * Math.min(reach, stack.length)), value = stack[stack.length - depth];
        stack.push(value); ops.push(['dup', depth]);
      } else if (next() < .6) { const id = choose(spills); stack.push(`v:${id}`); ops.push(['load', id]); }
      else { const value = choose(['l:0', `l:${1n << 248n}`]); stack.push(value); ops.push(['push', value]); }
    }
    swap(); swap();
    const problem = normalizeCase({ source: [], target: stack, spills, caps: { swap: reach, dup: reach },
      loadWidths: spills.map(id => [id, choose([0, 32])]), weights: choose([{ gas: 1, bytes: 0 }, { gas: 0, bytes: 1 }, { gas: 1, bytes: 1 }]) });
    try {
      const plan = extractAssignment(problem, ops), result = realizeAssignment(problem, plan.births, plan.assignment);
      const swaps = ops.filter(op => op[0] === 'swap').length;
      assert.ok(result.E <= 2 * swaps, 'actual trace moved token support exceeds twice its SWAP count');
      assert.ok(result.D <= 2 * swaps, 'actual trace displacement exceeds twice its SWAP count');
      const original = replay(problem, ops);
      assert.deepEqual(result.added, original.added, 'birth order differs after extraction');
      extractedPlans++; originalSwaps += swaps; constructedSwaps += result.swaps;
      if (swaps > 0) {
        maximumEOverSwaps = Math.max(maximumEOverSwaps ?? 0, result.E / swaps);
        maximumDOverSwaps = Math.max(maximumDOverSwaps ?? 0, result.D / swaps);
      }
    } catch (error) { failures.push({ problem, ops, error: error.message }); }
  }
  const report = { status: 'finite verification of a fixed-plan construction; not a joint-plan optimizer or production policy',
    construction: 'After birth j, repeatedly SWAP the top token into its assigned final position if that position is below j. Stop when its assignment is at least j.',
    precondition: 'Value-preserving bijection f from birth positions to target positions; b<=f(b)+R; a DUP birth of v at b has priorBornCount(v)>target.take(max(b-R,0)).count(v).',
    bounds: 'Constructed SWAPs equal sum over permutation cycles(length-1), and are at most E=#{b:f(b)!=b}, the moved token support. E is not the number of value mismatches. For assignments extracted from actual traces, E<=2*actualSWAPs. The separate displacement bound D=sum_b ceil(abs(b-f(b))/R) satisfies constructed SWAPs<=D<=2*actualSWAPs.',
    fixedDomain: { reaches: [1, 2, 3, 4, 16], births: '0 through 7', targetKinds: 'periodic three-kind word', assignments: 'every lag-valid permutation' },
    traceDomain: { reaches: [1, 2, 3, 4, 5, 16], samplesPerReach: 1000, births: 'chosen from 0,1,R,R+1,2R+1,4R', includes: 'equal values, PUSH0, width 32 literals, LOAD widths 0/32, endpoint scalar weights', seed },
    fixedPlans, extractedPlans, originalSwaps, constructedSwaps, maximumEOverSwaps, maximumDOverSwaps, failures,
    reproduce: `node scripts/optimality-assignment-realizer.mjs ${output}` };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n'); console.log(JSON.stringify(report));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
