#!/usr/bin/env node
/** Tiny exact check of global mandatory inventory and new-copy deadlines. */
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { normalizeCase, reserve } from './optimality-oracle.mjs';
import { minimumPlanSwaps } from './optimality-plan-presence.mjs';
import { lexicographicDeadlineOrder, exhaustiveDeadlineOrders } from './optimality-deadline-order.mjs';

const counts = values => values.reduce((map, value) => map.set(value, (map.get(value) ?? 0) + 1), new Map());

export function globalInventoryPlan(source, target, selected, reach) {
  if (!Number.isInteger(reach) || reach < 1 || reach > 16 || source.length > reach + 1) {
    throw new Error('source must be normalized to the reachable window');
  }
  const old = counts(source), final = counts(target);
  if ([...old].some(([value, count]) => count > (final.get(value) ?? 0))) throw new Error('source count exceeds target count');
  const names = [...new Set([...source, ...target])], values = names.map((_, index) => `v:${42 + index}`);
  const valueOf = value => values[names.indexOf(value)];
  const occurrences = new Map(), previous = new Map(), intervals = [], jobs = [];
  target.forEach((value, index) => {
    const count = (occurrences.get(value) ?? 0) + 1; occurrences.set(value, count);
    if (count > (old.get(value) ?? 0)) {
      jobs.push(index);
      if (previous.has(value)) intervals.push({ start: previous.get(value), end: index, value: valueOf(value) });
    }
    previous.set(value, index);
  });
  if (new Set(selected).size !== selected.length || selected.some(index =>
    !Number.isInteger(index) || index < 0 || index >= intervals.length)) throw new Error('invalid interval selection');
  const chosen = selected.map(index => intervals[index]), parents = new Map(chosen.map(interval => [interval.end, interval.start]));
  const deadlines = jobs.map(index => (parents.get(index) ?? index) + reach - source.length + 1);
  const inventory = [];
  for (let cut = Math.max(0, source.length - reach); cut <= target.length; cut++) {
    const consumed = counts(target.slice(0, cut));
    const mandatory = [...old].reduce((sum, [value, count]) => sum + Math.max(0, count - (consumed.get(value) ?? 0)), 0);
    const crossing = chosen.filter(interval => interval.start < cut && cut <= interval.end).length;
    inventory.push({ cut, mandatory, crossing, capacity: reach - mandatory });
  }
  const problem = normalizeCase({ source: source.map(valueOf), target: target.map(valueOf),
    spills: values.map(value => Number(value.slice(2))), caps: { swap: reach, dup: reach } });
  const budgets = names.map(value => (final.get(value) ?? 0) - (old.get(value) ?? 0) -
    chosen.filter(interval => interval.value === valueOf(value)).length);
  return { problem, values, budgets, intervals: chosen, allIntervals: intervals, selected,
    jobs, deadlines, inventory, deadlineOrder: lexicographicDeadlineOrder(deadlines),
    capacityFeasible: inventory.every(cut => cut.crossing <= cut.capacity), reserveFeasible: reserve(problem) };
}

const words = length => length === 0 ? [[]] : words(length - 1).flatMap(prefix => ['a', 'b'].map(value => [...prefix, value]));

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-global-inventory.json';
  const cache = new Map(); let plans = 0, feasible = 0, states = 0;
  let firstDeadlineMismatch = null, firstParentMismatch = null, firstUnrealizable = null;
  outer: for (const reach of [1, 2, 3]) for (let size = 0; size <= reach + 1; size++) {
    for (const source of words(size)) for (let births = 0; births <= 3; births++) {
      for (const target of words(size + births)) {
        const old = counts(source), final = counts(target);
        if ([...old].some(([value, count]) => count > (final.get(value) ?? 0))) continue;
        const first = globalInventoryPlan(source, target, [], reach);
        for (let mask = 0; mask < 2 ** first.allIntervals.length; mask++) {
          const selected = first.allIntervals.flatMap((_, index) => mask & 2 ** index ? [index] : []);
          const plan = globalInventoryPlan(source, target, selected, reach); plans++;
          if (plan.capacityFeasible !== (plan.deadlineOrder !== null)) {
            firstDeadlineMismatch = { source, target, reach, selected, plan }; break outer;
          }
          if (!plan.capacityFeasible) continue;
          feasible++;
          const parentBeforeChild = order => plan.intervals.every(interval => {
            const parent = plan.jobs.indexOf(interval.start), child = plan.jobs.indexOf(interval.end);
            return parent < 0 || order.indexOf(parent) < order.indexOf(child);
          });
          const exactOrder = exhaustiveDeadlineOrders(plan.deadlines).find(parentBeforeChild) ?? null;
          if (!parentBeforeChild(plan.deadlineOrder) || JSON.stringify(exactOrder) !== JSON.stringify(plan.deadlineOrder)) {
            firstParentMismatch = { source, target, reach, selected, plan, exactOrder }; break outer;
          }
          const key = JSON.stringify([reach, plan.problem.source, plan.problem.target, plan.intervals, plan.budgets]);
          if (!cache.has(key)) { const result = minimumPlanSwaps(plan); cache.set(key, result); states += result.states; }
          const result = cache.get(key);
          if (!plan.reserveFeasible || result.status !== 'reachable') {
            firstUnrealizable = { source, target, reach, selected, plan, result }; break outer;
          }
        }
      }
    }
  }
  const report = { status: 'finite exact global-inventory evidence, not a Lean theorem',
    semantics: 'First sourceCount(v) target occurrences are mandatory old outputs. Selected later intervals require retained value presence, with per-value direct budgets. The source is already reduced to at most R+1 slots.',
    deadlines: 'A new root at target index j has deadline j+R-n+1. A selected child of previous equal output i has deadline i+R-n+1. Slots are1-based; target indices are0-based. Nonpositive new-job deadlines reject.',
    domain: { reaches: [1, 2, 3], sourceLengths: '0 through R+1', alphabet: ['a', 'b'], births: '0 through3', stateLimit: 300000 },
    plans, feasible, distinctSearches: cache.size, states, firstDeadlineMismatch, firstParentMismatch, firstUnrealizable,
    reproduce: `node scripts/optimality-global-inventory.mjs ${output}` };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n'); console.log(JSON.stringify(report));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
