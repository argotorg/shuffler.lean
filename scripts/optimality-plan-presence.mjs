#!/usr/bin/env node
/** Exact offline plans use value presence, with no fixed copy ancestry. */
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { normalizeCase, replay } from './optimality-oracle.mjs';
import { consecutiveIntervals, encodeIntervalPlan } from './optimality-interval-realizability.mjs';

const counts = stack => stack.reduce((map, value) => map.set(value, (map.get(value) ?? 0) + 1), new Map());
const equal = (first, second) => first.length === second.length && first.every((value, index) => value === second[index]);

export function ordinaryFreshPlan(word, selected, reach, old) {
  const checked = encodeIntervalPlan(word, selected, reach, old);
  const names = [...new Set(word)], values = names.map((_, index) => `v:${42 + index}`);
  const valueOf = value => values[names.indexOf(value)];
  const intervals = selected.map(index => ({ ...checked.intervals[index], value: valueOf(checked.intervals[index].value) }));
  const source = Array(old).fill('l:0');
  const problem = normalizeCase({ source, target: [...word.map(valueOf), ...source],
    spills: values.map(value => Number(value.slice(2))), caps: { swap: reach, dup: reach } });
  const budgets = values.map(value => problem.target.filter(item => item === value).length -
    intervals.filter(interval => interval.value === value).length);
  return { problem, values, budgets, intervals, capacityFeasible: checked.capacityFeasible };
}

export function minimumPlanSwaps(plan, { stateLimit = 300000 } = {}) {
  const { problem, values, budgets, intervals } = plan;
  if (values.length !== budgets.length || budgets.some(budget => !Number.isInteger(budget) || budget < 0)) {
    throw new Error('invalid per-value introduction budgets');
  }
  const desired = counts(problem.target), initialCounts = counts(problem.source);
  if ([...initialCounts].some(([value, count]) => count > (desired.get(value) ?? 0))) {
    return { status: 'unreachable', states: 0, reason: 'count-balance' };
  }
  const presence = (stack, cut) => intervals.every(interval =>
    !(interval.start < cut && cut <= interval.end) || stack.slice(cut).includes(interval.value));
  const terminalCut = Math.max(1, problem.target.length - problem.caps.swap);
  for (let cut = terminalCut; cut <= problem.target.length; cut++) {
    if (!presence(problem.target, cut)) return { status: 'unreachable', states: 0, reason: 'virtual-presence' };
  }
  const first = { stack: problem.source, direct: values.map(() => 0), previous: null, op: null };
  const key = state => JSON.stringify([state.stack, state.direct]);
  const queue = [first], seen = new Set([key(first)]);
  for (let index = 0; index < queue.length; index++) {
    const current = queue[index], stack = current.stack;
    if (equal(stack, problem.target)) {
      const ops = []; for (let node = current; node.op !== null; node = node.previous) ops.push(node.op);
      ops.reverse(); replay(problem, ops);
      return { status: 'reachable', states: seen.size, ops, direct: current.direct,
        swaps: ops.filter(op => op[0] === 'swap').length };
    }
    const next = [], push = (stack, op, direct = current.direct) => next.push({ stack, op, direct, previous: current });
    for (let depth = 1; depth <= Math.min(problem.caps.swap, stack.length - 1); depth++) {
      const lower = stack.length - depth - 1;
      if (stack[lower] === stack.at(-1)) continue;
      const copy = [...stack]; [copy[lower], copy[copy.length - 1]] = [copy.at(-1), copy[lower]];
      push(copy, ['swap', depth]);
    }
    const cut = stack.length - problem.caps.swap;
    const canFreeze = cut <= 0 || (equal(stack.slice(0, cut), problem.target.slice(0, cut)) && presence(stack, cut));
    if (stack.length < problem.target.length && canFreeze) {
      const present = counts(stack);
      for (const [value, count] of desired) {
        if ((present.get(value) ?? 0) >= count) continue;
        const position = stack.lastIndexOf(value), depth = stack.length - position;
        if (position >= 0 && depth <= problem.caps.dup) push([...stack, value], ['dup', depth]);
        const tracked = values.indexOf(value);
        if (tracked < 0 || current.direct[tracked] >= budgets[tracked]) continue;
        const direct = [...current.direct]; direct[tracked]++;
        if (value.startsWith('l:')) push([...stack, value], ['push', value], direct);
        else if (value.startsWith('v:') && problem.spills.includes(Number(value.slice(2)))) {
          push([...stack, value], ['load', Number(value.slice(2))], direct);
        }
      }
    }
    for (const state of next) {
      const id = key(state); if (seen.has(id)) continue;
      if (seen.size >= stateLimit) return { status: 'limit', states: seen.size };
      seen.add(id); queue.push(state);
    }
  }
  return { status: 'unreachable', states: seen.size };
}

const words = length => length === 0 ? [[]] : words(length - 1).flatMap(prefix => ['a', 'b'].map(value => [...prefix, value]));

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-plan-presence.json';
  const cache = new Map(); let plans = 0, states = 0, firstUnrealizable = null, violations = 0, firstViolation = null;
  let requiredSelectionViolations = 0, firstRequiredSelectionViolation = null;
  outer: for (const reach of [1, 2, 3]) for (let old = 0; old <= reach; old++) {
    for (let size = 0; size <= 6; size++) for (const word of words(size)) {
      const all = consecutiveIntervals(word);
      for (let mask = 0; mask < 2 ** all.length; mask++) {
        const selected = all.flatMap((_, index) => mask & 2 ** index ? [index] : []);
        const plan = ordinaryFreshPlan(word, selected, reach, old);
        if (!plan.capacityFeasible) continue;
        plans++;
        const key = JSON.stringify([reach, old, plan.problem.target, plan.intervals, plan.budgets]);
        if (!cache.has(key)) { const result = minimumPlanSwaps(plan); cache.set(key, result); states += result.states; }
        const result = cache.get(key);
        if (result.status !== 'reachable') { firstUnrealizable = { word, selected, plan, result }; break outer; }
        const M = Math.max(Math.min(old - 1, size), old > 0 && size > 0 ? 1 : 0);
        const Q = Math.ceil(old * size / reach) + selected.reduce((sum, index) =>
          sum + Math.floor((all[index].end - all[index].start - 1) / reach), 0);
        if (result.swaps > M + Q) { violations++; firstViolation ??= { word, selected, plan, result, M, Q }; }
        const requiredSelections = Math.min(old, size);
        if (result.swaps > requiredSelections + Q) {
          requiredSelectionViolations++;
          firstRequiredSelectionViolation ??= { word, selected, plan, result, requiredSelections, Q };
        }
      }
    }
  }
  const report = { status: 'finite exact value-presence evidence, not a Lean theorem',
    semantics: 'Per-value direct counts are upper bounds. Selected intervals require their value in the readable suffix at each real output cut. Terminal cuts use target.drop(c). Equal copies can exchange roots; extra retention is allowed.',
    domain: { reaches: [1, 2, 3], oldCopies: '0 through reach', freshAlphabet: ['a', 'b'], prefixLengths: '0 through6', stateLimit: 300000 },
    plans, distinctProblems: cache.size, states, firstUnrealizable,
    swapBound: { formula: 'M=max(min(q-1,m), q>0 and m>0 ? 1 : 0); Q=ceil(q*m/R)+sum_selected floor((end-start-1)/R)', violations, firstViolation },
    requiredSelectionBound: { formula: 'M=min(q,m), with the same Q. Every initial position replaced by a fresh value must be SWAP-selected, including the initial top.',
      violations: requiredSelectionViolations, firstViolation: firstRequiredSelectionViolation },
    reproduce: `node scripts/optimality-plan-presence.mjs ${output}` };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n'); console.log(JSON.stringify(report));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
