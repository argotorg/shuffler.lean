#!/usr/bin/env node
/** Offline attempt to falsify increasing-order identity pinning. */
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { deadlineJobs } from './optimality-birth-matching.mjs';
import { consecutiveIntervals } from './optimality-interval-realizability.mjs';
import { exactPinnedSets, pinnedQuotaPlan } from './optimality-pinned-quotas.mjs';

const bits = (mask, size) => Array.from({ length: size }, (_, index) => index).filter(index => mask & 2 ** index);

export function increasingPinnedSet(target, reach, jobs) {
  if (pinnedQuotaPlan(target, reach, jobs, []).status !== 'feasible') return { status: 'infeasible' };
  const pinned = [];
  for (let index = 0; index < target.length; index++) {
    if (pinnedQuotaPlan(target, reach, jobs, [...pinned, index]).status === 'feasible') pinned.push(index);
  }
  return { status: 'selected', pinned, completion: pinnedQuotaPlan(target, reach, jobs, pinned) };
}

function* canonicalWords(size, prefix = []) {
  if (prefix.length === size) { yield prefix; return; }
  for (const value of ['a', 'b', 'c'].slice(0, Math.min(3, new Set(prefix).size + 1))) yield* canonicalWords(size, [...prefix, value]);
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-pinned-greedy.json';
  let plans = 0, feasiblePlans = 0;
  const losses = [];
  outer: for (let size = 0; size <= 7; size++) for (const reach of [1, 2, 3, 16]) {
    for (const target of canonicalWords(size)) {
      const intervals = consecutiveIntervals(target), all = 2 ** intervals.length - 1;
      for (const mask of [all, ...Array.from({ length: all }, (_, index) => index)]) {
        const selected = bits(mask, intervals.length);
        const jobs = deadlineJobs([], target, reach, selected).map(job => ({ value: job.value, deadline: job.deadline - 1 }));
        const exact = exactPinnedSets(target, reach, jobs), actual = increasingPinnedSet(target, reach, jobs); plans++;
        if (!exact.feasible[0]) {
          if (actual.status !== 'infeasible') throw new Error('initial feasibility differs');
          continue;
        }
        feasiblePlans++;
        const family = exact.feasible.flatMap((valid, mask) => valid ? [bits(mask, size)] : []);
        const maximum = Math.max(...family.map(set => set.length));
        if (actual.pinned.length < maximum) {
          const optimal = family.filter(set => set.length === maximum);
          losses.push({ target, reach, selected, jobs, actual, maximum, optimal,
            exactWitnesses: optimal.map(pinned => pinnedQuotaPlan(target, reach, jobs, pinned)),
            exactAssignments: exact.assignments, validAssignments: exact.validAssignments });
          break outer;
        }
      }
    }
    console.error(`pinned greedy n=${size} R=${reach}: ${plans} plans, ${losses.length} losses`);
  }
  const report = {
    status: losses.length ? 'finite strict counterexample to increasing-order pinning' : 'finite increasing-order pinning evidence; no optimality theorem claimed',
    candidate: 'Process positions in increasing order. Pin a position if the exact quota predicate says that the current pinned set with that position has a completion.',
    comparison: 'Maximum cardinality is computed from all lag-valid endpoint permutations with separate generation-deadline matching. The quota predicate is used by the candidate and to reconstruct optimal pinned sets, but not to determine the comparison optimum.',
    domain: { maximumLength: 7, reaches: [1, 2, 3, 16], targets: 'canonical words with at most 3 values', retention: 'all subsets, with all-reuse first', stopping: 'first strict loss; size is the outer loop, so smaller tested lengths are exhausted' },
    plans, feasiblePlans, losses,
    reproduce: `node scripts/optimality-pinned-greedy.mjs ${output}`
  };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n'); console.log(JSON.stringify(report));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
