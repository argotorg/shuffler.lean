#!/usr/bin/env node
/** Bounded offline research. This is not a production planner or a proof. */
import fs from 'node:fs';
import { baseline, normalizeCase, opCost, reserve, score } from './optimality-oracle.mjs';
import { experimentalLineageBound, gapCount, relaxedGraphBound } from './optimality-bounds.mjs';

const key = stack => JSON.stringify(stack);
const words = n => n === 0 ? [[]] : words(n - 1).flatMap(rest => ['l:0', 'v:42'].map(v => [...rest, v]));
const currentBounds = process.argv.includes('--current-bounds');
const gapOnly = currentBounds || process.argv.includes('--gap-only');
const prefixReserveCount = process.argv.includes('--prefix-reserve-count');
const combinedValueAccounting = currentBounds || gapOnly || prefixReserveCount || process.argv.includes('--combined-value-accounting');
const forcedIntroduction = combinedValueAccounting || process.argv.includes('--forced-introduction');
const option = (name, fallback) => {
  const index = process.argv.indexOf(name);
  return index < 0 ? fallback : process.argv[index + 1];
};
const birthCount = Number(option('--births', '1'));
const caseLimit = Number(option('--case-limit', '10000'));
if (![1, 2].includes(birthCount) || !Number.isSafeInteger(caseLimit) || caseLimit < 1) {
  throw new Error('births must be 1 or 2 and case-limit must be a positive integer');
}

function swapClosure(stack, cap) {
  const states = new Map([[key(stack), { stack, swaps: [], distance: 0 }]]), queue = [stack];
  for (let index = 0; index < queue.length; index++) {
    const old = states.get(key(queue[index]));
    for (let depth = 1; depth <= Math.min(cap, stack.length - 1); depth++) {
      const next = [...old.stack], lower = next.length - depth - 1;
      if (next[lower] === next.at(-1)) continue;
      [next[lower], next[next.length - 1]] = [next.at(-1), next[lower]];
      const id = key(next); if (states.has(id)) continue;
      states.set(id, { stack: next, swaps: [...old.swaps, ['swap', depth]], distance: old.distance + 1 }); queue.push(next);
    }
  }
  return states;
}

function direct(problem, value) {
  if (value === 'wildcard' || value.startsWith('l:')) return ['push', value];
  if (value.startsWith('v:') && problem.spills.includes(Number(value.slice(2)))) return ['load', Number(value.slice(2))];
  return null;
}

// Reduced-capacity research analogue of the graph, transport, Q, and capped-F
// bounds. An optional forced-introduction condition rules out retention when
// the initial working window cannot supply both the boundary slot and a seed.
// Actual-cap counterexamples are checked separately against the Lean runner.
function excess(problem) {
  const swapPrice = score(problem, { gas: 3, bytes: 1 }), cap = problem.caps.swap;
  const components = experimentalLineageBound(problem, true, true);
  const frozenPosition = Math.max(0, problem.source.length - cap - 1);
  const boundaryValue = problem.target[frozenPosition];
  const correctBoundary = currentBounds && problem.missing.length > 0 && problem.source.length >= cap + 1 &&
    problem.source[frozenPosition] !== boundaryValue && problem.source.at(-1) !== boundaryValue &&
    problem.source.every((value, index) => value !== boundaryValue || problem.target[index] === value);
  const boundaryFloor = correctBoundary ? problem.source.slice(0, -1)
    .filter((value, index) => problem.target[index] !== value).length + 2 : 0;
  const floor = Math.max(0, relaxedGraphBound(problem, true, true), boundaryFloor);
  let states = new Map([[0, 0]]), capped = 0;
  const potential = (stack, value, premium, leading) => {
    let previous = -1, result = 0;
    for (let index = 0; index < stack.length; index++) if (stack[index] === value) {
      result += previous < 0 ? (leading ? Math.min(premium, swapPrice * Math.ceil(index / cap)) : 0) :
        Math.min(premium, swapPrice * Math.floor((index - previous - 1) / cap));
      previous = index;
    }
    return result;
  };
  for (const value of new Set([...problem.source, ...problem.target])) {
    const generator = direct(problem, value), price = generator ? score(problem, opCost(problem, generator)) : Infinity;
    const premium = price === Infinity ? Infinity : price - Math.min(swapPrice, price);
    const leading = problem.source.includes(value);
    let gapCost = Math.max(0, potential(problem.target, value, premium, leading) - potential(problem.source, value, premium, leading));
    if (gapOnly) gapCost = Math.max(gapCost,
      potential(problem.target, value, premium, false) - potential(problem.source, value, premium, false));
    const frozen = Math.max(0, problem.source.length - cap - 1);
    const boundary = problem.missing.length > 0 && problem.source.length >= cap + 1 &&
      problem.target[frozen] === value ? 1 : 0;
    const available = problem.source.slice(frozen).filter(v => v === value).length;
    const required = forcedIntroduction && problem.missing.includes(value) && available < boundary + 1;
    const row = components.optionsByValue.find(row => row.value === value);
    let mandatory = leading && required ? premium : 0;
    if (prefixReserveCount && problem.source.length >= cap && available === boundary) {
      const position = problem.source.length - cap;
      let run = 0;
      while (problem.target[position + run] === value) run++;
      const introductions = Math.min(problem.missing.filter(v => v === value).length, run + 1);
      mandatory = premium * Math.max(0, introductions - (leading ? 0 : 1));
    }
    if (currentBounds) {
      const protectedKinds = new Set(problem.source.filter(v => v !== value));
      const oldCount = problem.source.filter(v => protectedKinds.has(v)).length;
      let prefixIntroductions = 0;
      if (oldCount >= cap) {
        const protectedPositions = problem.target.flatMap((v, index) => protectedKinds.has(v) ? [index] : []);
        const cutoff = protectedPositions[oldCount - cap] ?? problem.target.length;
        const demand = problem.target.slice(0, cutoff).filter(v => v === value).length +
          (problem.target.slice(cutoff).includes(value) ? 1 : 0);
        prefixIntroductions = Math.max(0, demand - problem.source.filter(v => v === value).length);
      }
      mandatory = premium * Math.max(0, Math.max(required ? 1 : 0, prefixIntroductions) - (leading ? 0 : 1));
    }
    capped += combinedValueAccounting ? Math.max(gapCost, swapPrice * (row?.original ?? 0) + mandatory) : gapCost;
    if (!leading) continue;
    const retained = Math.max(row.original, row.maxPosition,
      gapCount(problem.target, value, cap) - gapCount(problem.source, value, cap));
    const options = required ? [] : [{ swaps: retained, premium: 0 }];
    if (generator && problem.missing.includes(value)) options.push({ swaps: row.original, premium });
    const next = new Map();
    for (const [accumulated, cost] of states) for (const option of options) {
      const total = accumulated + option.swaps, state = Math.min(floor, total);
      const price = cost + option.premium + Math.max(0, total - floor) * swapPrice;
      next.set(state, Math.min(next.get(state) ?? Infinity, price));
    }
    states = next;
  }
  return Math.max(capped, floor * swapPrice + Math.min(...states.values()));
}

function check(problem) {
  const base = baseline(problem), bound = excess(problem), swapPrice = score(problem, { gas: 3, bytes: 1 });
  const before = swapClosure(problem.source, problem.caps.swap);
  let minimum = Infinity, best = null, generated = 0, feasibleEnds = 0;
  const targetClosure = problem.missing.length === 1 ? swapClosure(problem.target, problem.caps.swap) : null;
  for (const prior of before.values()) for (const value of new Set(problem.missing)) {
    const remaining = [...problem.missing]; remaining.splice(remaining.indexOf(value), 1);
    const births = [], generator = direct(problem, value);
    if (generator) births.push(generator);
    const position = prior.stack.lastIndexOf(value), depth = prior.stack.length - position;
    if (position >= 0 && depth <= problem.caps.dup) births.push(['dup', depth]);
    for (const birth of births) {
      generated++;
      const after = swapClosure([...prior.stack, value], problem.caps.swap);
      for (const next of after.values()) {
        let residual, residualBaseline;
        if (targetClosure) {
          const final = targetClosure.get(key(next.stack)); if (!final) continue;
          residual = final.distance * swapPrice; residualBaseline = 0;
        } else {
          const nextProblem = normalizeCase({ ...problem, source: next.stack, missing: remaining });
          if (!reserve(nextProblem)) continue;
          residual = excess(nextProblem); residualBaseline = baseline(nextProblem);
        }
        feasibleEnds++;
        const prefixCost = (prior.distance + next.distance) * swapPrice + score(problem, opCost(problem, birth));
        const lhs = prefixCost + residualBaseline - base + 2 * residual;
        if (lhs < minimum) { minimum = lhs; best = { prefix: [...prior.swaps, birth, ...next.swaps],
          prefixCost, nextSource: next.stack, remaining, residualBaseline,
          residualExcess: residual, residualIsExactPermutationCost: targetClosure !== null, lhs }; }
      }
    }
  }
  return { baseline: base, staticExcess: bound, rhs: 2 * bound, minimum, best,
    beforeStates: before.size, birthBranches: generated, feasibleEnds, succeeds: minimum <= 2 * bound };
}

let checked = 0, first = null, limited = false;
outer: for (let size = 0; size <= 4; size++) for (const source of words(size)) for (const target of words(size + birthCount)) {
  for (const width of [0, 2, 32]) {
    const problem = normalizeCase({ id: `descent-${checked}`, source, target, spills: [42],
      loadWidths: [[42, width]], weights: { gas: 0, bytes: 1 }, caps: { swap: 2, dup: 2 } });
    if (problem.missing.length !== birthCount || !reserve(problem)) continue;
    if (checked >= caseLimit) { limited = true; break outer; }
    const result = check(problem); checked++;
    if (!result.succeeds) { first = { problem, result }; break outer; }
  }
}
const report = { status: 'bounded experimental result; not a production algorithm',
  boundVersion: currentBounds ? 'graph-transport-Q-F-tail-prefix-count-correct-boundary' :
    gapOnly ? 'graph-transport-Q-F-forced-combined-gap-only' :
    prefixReserveCount ? 'graph-transport-Q-F-forced-combined-prefix-reserve-count' :
    combinedValueAccounting ? 'graph-transport-Q-F-forced-combined-per-value' :
    forcedIntroduction ? 'graph-transport-Q-F-forced-introduction' : 'graph-transport-Q-F',
  checked, first, completed: first === null && !limited, limited, caseLimit,
  domain: { alphabet: ['l:0', 'v:42'], sourceLengths: { minimum: 0, maximum: 4 }, births: birthCount,
    capacity: 2, loadWidths: [0, 2, 32], weights: { gas: 0, bytes: 1 },
    macro: 'arbitrary legal SWAPs, one birth, arbitrary legal SWAPs',
    residual: 'exact no-growth SWAP distance at H=0; the same static bound otherwise' } };
const output = process.argv.slice(2).find(arg => !arg.startsWith('--')) ?? '/tmp/optimality-descent-result.json';
fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
console.log(JSON.stringify(report, null, 2));
