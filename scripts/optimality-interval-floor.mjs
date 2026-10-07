#!/usr/bin/env node
/** Exhaustive bounded interval experiment. Never used by production planning. */
import fs from 'node:fs';
import { normalizeCase } from './optimality-oracle.mjs';
import { reachableWithDirectLimit } from './optimality-forced-introductions.mjs';

const words = (alphabet, n) => n === 0 ? [[]] : words(alphabet, n - 1).flatMap(rest => alphabet.map(v => [...rest, v]));
function intervalBound(prefix, capacity) {
  const previous = new Map(), intervals = [];
  prefix.forEach((value, end) => {
    if (previous.has(value)) intervals.push({start: previous.get(value), end, value});
    previous.set(value, end);
  });
  let retained = 0;
  for (let mask = 0; mask < 2 ** intervals.length; mask++) {
    let selected = 0, valid = true;
    const occupancy = Array(prefix.length).fill(0);
    intervals.forEach(({start, end}, i) => {
      if (!(mask & 2 ** i)) return;
      selected++;
      for (let cut = start; cut < end; cut++) if (++occupancy[cut] > capacity) valid = false;
    });
    if (valid) retained = Math.max(retained, selected);
  }
  return {minimumDirect: prefix.length - retained, retained, intervals};
}
let checked = 0, states = 0, first = null;
const totals = {};
outer: for (const reach of [1, 2, 3]) for (let old = 0; old <= reach; old++) {
  for (let n = 1; n <= 6; n++) for (const prefix of words(['v:42', 'v:43'], n)) {
    const source = Array(old).fill('l:0');
    const problem = normalizeCase({source, target: [...prefix, ...source], spills: [42, 43], caps: {swap: reach, dup: reach}});
    const bound = intervalBound(prefix, reach - old);
    const result = reachableWithDirectLimit(problem, ['v:42', 'v:43'], bound.minimumDirect - 1, 300000);
    checked++; states += result.states;
    totals[`${reach}/${old}`] = (totals[`${reach}/${old}`] ?? 0) + 1;
    if (result.status !== 'unreachable') { first = {problem, bound, result}; break outer; }
  }
}
const alternating = [];
for (const k of [2, 3, 8, 17]) {
  const prefix = Array.from({length: 2*k}, (_,i) => i % 2 ? 'v:43' : 'v:42');
  // Equal two-cut intervals admit a maximum of k-1 pairwise-disjoint gaps.
  alternating.push({k, minimumDirect: k+1, intervalCount: 2*k-2, retained: k-1});
}
const report = {status: 'finite reachability evidence, not a Lean proof', checked, states, first, totals,
  domain: {reaches:[1,2,3], oldCopies:'0 through reach', freshAlphabet:['v:42','v:43'], prefixLengths:'1 through 6', stateLimit:300000},
  formulaExamples: {status:'closed-form interval counts; not additional trace searches', alternating}};
fs.writeFileSync(process.argv[2] ?? '/tmp/collective-interval-check.json', JSON.stringify(report, null, 2)+'\n');
console.log(JSON.stringify(report));
