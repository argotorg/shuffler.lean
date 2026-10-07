#!/usr/bin/env node
/** Offline realization test. Copy labels encode the selected reuse pattern. */
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { normalizeCase, replay } from './optimality-oracle.mjs';
import { reachableWithDirectLimit } from './optimality-forced-introductions.mjs';

export function consecutiveIntervals(word) {
  const previous = new Map(), intervals = [];
  word.forEach((value, end) => {
    if (previous.has(value)) intervals.push({ start: previous.get(value), end, value });
    previous.set(value, end);
  });
  return intervals;
}

export function encodeIntervalPlan(word, selected, reach, old) {
  if (!Number.isInteger(reach) || reach < 1 || reach > 16 ||
      !Number.isInteger(old) || old < 0 || old > reach) throw new Error('invalid dimensions');
  const intervals = consecutiveIntervals(word), chosen = new Set(selected);
  if (chosen.size !== selected.length || selected.some(index =>
    !Number.isInteger(index) || index < 0 || index >= intervals.length)) throw new Error('invalid interval selection');
  const occupancy = Array(word.length).fill(0), linked = new Map();
  for (const index of selected) {
    const interval = intervals[index]; linked.set(interval.end, interval.start);
    for (let cut = interval.start; cut < interval.end; cut++) occupancy[cut]++;
  }
  const roots = [], labeled = [];
  word.forEach((value, index) => {
    if (linked.has(index)) labeled.push(labeled[linked.get(index)]);
    else { const label = `v:${100 + roots.length}`; roots.push({ label, value, first: index }); labeled.push(label); }
  });
  const source = Array(old).fill('l:0');
  const problem = normalizeCase({ id: 'selected-interval-plan', source, target: [...labeled, ...source],
    spills: roots.map(root => Number(root.label.slice(2))), caps: { swap: reach, dup: reach } });
  return { word, reach, old, intervals, selected, occupancy, roots,
    capacity: reach - old, capacityFeasible: occupancy.every(count => count <= reach - old), problem };
}

export function testIntervalPlan(plan, stateLimit = 300000) {
  const result = reachableWithDirectLimit(plan.problem, plan.roots.map(root => root.label), plan.roots.length, stateLimit);
  if (result.status === 'reachable') {
    replay(plan.problem, result.ops);
    if (result.direct !== plan.roots.length) throw new Error('a root lacks its required introduction');
  }
  return result;
}

const words = length => length === 0 ? [[]] : words(length - 1).flatMap(prefix =>
  ['a', 'b'].map(value => [...prefix, value]));

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-interval-realizability.json';
  const cache = new Map(), totals = {}; let feasiblePlans = 0, rejectedPlans = 0, states = 0, first = null;
  let maximumSwaps = { count: 0, plan: null, ops: [] };
  const swapBound = { scope: 'Rigid copy-component assignments only. Failures do not refute a value-presence plan, which can exchange equal roots and retain extra copies at unselected cuts.',
    formula: 'M=max(min(q-1,m), q>0 and m>0 ? 1 : 0); Q=ceil(q*m/R)+sum_selected floor((end-start-1)/R)',
    violations: 0, first: null, firstWithNoOldCopies: null };
  outer: for (const reach of [1, 2, 3]) for (let old = 0; old <= reach; old++) {
    for (let size = 0; size <= 6; size++) for (const word of words(size)) {
      const intervals = consecutiveIntervals(word);
      for (let mask = 0; mask < 2 ** intervals.length; mask++) {
        const selected = intervals.flatMap((_, index) => mask & 2 ** index ? [index] : []);
        const plan = encodeIntervalPlan(word, selected, reach, old);
        if (!plan.capacityFeasible) { rejectedPlans++; continue; }
        feasiblePlans++;
        totals[`${reach}/${old}`] = (totals[`${reach}/${old}`] ?? 0) + 1;
        const key = JSON.stringify([reach, old, plan.problem.target]);
        if (!cache.has(key)) { const result = testIntervalPlan(plan); cache.set(key, result); states += result.states; }
        const result = cache.get(key);
        if (result.status !== 'reachable') { first = { plan, result }; break outer; }
        const swaps = result.ops.filter(op => op[0] === 'swap').length;
        if (swaps > maximumSwaps.count) maximumSwaps = { count: swaps, plan, ops: result.ops };
        const M = Math.max(Math.min(old - 1, size), old > 0 && size > 0 ? 1 : 0);
        const Q = Math.ceil(old * size / reach) + selected.reduce((sum, index) =>
          sum + Math.floor((intervals[index].end - intervals[index].start - 1) / reach), 0);
        if (swaps > M + Q) {
          swapBound.violations++;
          const failure = { plan, minimumSwaps: swaps, M, Q, ops: result.ops };
          swapBound.first ??= failure;
          if (old === 0) swapBound.firstWithNoOldCopies ??= failure;
        }
      }
    }
  }
  const report = { status: 'finite exact reachability evidence, not a Lean theorem',
    encoding: 'Each selected-interval component has one fresh variable label. Labels are absent from source; a total direct budget equal to label count forces exactly one introduction per component. DUP preserves labels.',
    cutSemantics: 'An interval [start,end) occupies cuts after outputs start through end-1.',
    domain: { reaches: [1, 2, 3], oldCopies: '0 through reach', freshAlphabet: ['a', 'b'], prefixLengths: '0 through 6', stateLimit: 300000 },
    feasiblePlans, rejectedPlans, distinctLabeledProblems: cache.size, states, totals, first, maximumSwaps, swapBound,
    completed: first === null, reproduce: `node scripts/optimality-interval-realizability.mjs ${output}` };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({ ...report, maximumSwaps: { count: maximumSwaps.count } }));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
