#!/usr/bin/env node
/** Offline check of pinned endpoint identities with independent generation jobs. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { deadlineJobs } from './optimality-birth-matching.mjs';
import { consecutiveIntervals } from './optimality-interval-realizability.mjs';
import { sortedResidualAssignment } from './optimality-fixed-points.mjs';

const positions = (word, value) => word.flatMap((item, index) => item === value ? [index] : []);
const bits = (mask, size) => Array.from({ length: size }, (_, index) => index).filter(index => mask & 2 ** index);

function checkInput(target, reach, jobs, pinned = []) {
  assert.ok(Number.isInteger(reach) && reach >= 1, 'invalid reach');
  assert.deepEqual(jobs.map(job => job.value).sort(), [...target].sort(), 'job counts differ');
  assert.ok(jobs.every(job => Number.isInteger(job.deadline) && job.deadline >= 0), 'invalid deadline');
  assert.ok(new Set(pinned).size === pinned.length && pinned.every(index => Number.isInteger(index) && index >= 0 && index < target.length), 'invalid pinned set');
}

/** All deadlines and positions use zero-based birth indices. */
export function pinnedQuotaPlan(target, reach, jobs, pinned) {
  checkInput(target, reach, jobs, pinned);
  const selected = new Set(pinned), values = [...new Set(target)], freeSlots = target.flatMap((_, index) => selected.has(index) ? [] : [index]);
  const end = Math.max(target.length - 1 + reach, ...jobs.map(job => job.deadline));
  const h = new Map(values.map(value => [value, 0])), quotas = [], freeJobs = [];
  for (let cut = 0; cut <= end; cut++) {
    for (const value of values) {
      const fixedBefore = pinned.filter(index => target[index] === value && index <= cut).length;
      const generationDue = jobs.filter(job => job.value === value && job.deadline <= cut).length;
      const endpointDue = target.filter((item, index) => item === value && !selected.has(index) && index + reach <= cut).length;
      const next = Math.max(h.get(value), 0, generationDue - fixedBefore, endpointDue);
      for (let ordinal = h.get(value); ordinal < next; ordinal++) freeJobs.push({ value, deadline: cut });
      h.set(value, next);
    }
    const required = [...h.values()].reduce((sum, value) => sum + value, 0);
    const available = freeSlots.filter(index => index <= cut).length;
    quotas.push({ cut, byValue: Object.fromEntries(h), required, available });
    if (required > available) return { status: 'infeasible', cut, quotas };
  }
  assert.equal(freeJobs.length, freeSlots.length, 'terminal free count differs');
  freeJobs.sort((a, b) => a.deadline - b.deadline);
  const word = Array(target.length);
  pinned.forEach(index => { word[index] = target[index]; });
  freeJobs.forEach((job, index) => {
    assert.ok(freeSlots[index] <= job.deadline, 'free job misses its deadline');
    word[freeSlots[index]] = job.value;
  });
  for (const value of values) {
    const births = positions(word, value), deadlines = jobs.filter(job => job.value === value).map(job => job.deadline).sort((a, b) => a - b);
    assert.ok(births.every((birth, index) => birth <= deadlines[index]), 'generation matching fails');
  }
  const assignment = sortedResidualAssignment(word, target, reach, pinned);
  assert.ok(pinned.every(index => assignment[index] === index));
  return { status: 'feasible', word, assignment, quotas, freeJobs };
}

function* permutations(size, prefix = []) {
  if (prefix.length === size) { yield prefix; return; }
  for (let value = 0; value < size; value++) if (!prefix.includes(value)) yield* permutations(size, [...prefix, value]);
}

export function exactPinnedSets(target, reach, jobs) {
  checkInput(target, reach, jobs);
  const feasible = Array(2 ** target.length).fill(false), witnesses = new Map(), values = [...new Set(target)];
  const deadlines = new Map(values.map(value => [value, jobs.filter(job => job.value === value).map(job => job.deadline).sort((a, b) => a - b)]));
  let assignments = 0, validAssignments = 0;
  for (const assignment of permutations(target.length)) {
    if (assignment.some((output, birth) => birth > output + reach)) continue;
    assignments++;
    const word = assignment.map(output => target[output]);
    if (values.some(value => positions(word, value).some((birth, index) => birth > deadlines.get(value)[index]))) continue;
    validAssignments++;
    const fixedMask = assignment.reduce((mask, output, birth) => mask + (output === birth ? 2 ** birth : 0), 0);
    if (!witnesses.has(fixedMask)) witnesses.set(fixedMask, { word, assignment });
    let subset = fixedMask;
    while (true) {
      feasible[subset] = true;
      if (subset === 0) break;
      subset = (subset - 1) & fixedMask;
    }
  }
  return { feasible, assignments, validAssignments, witnesses };
}

function exchangeFailure(feasible, size) {
  const sets = feasible.flatMap((valid, mask) => valid ? [{ mask, elements: bits(mask, size) }] : []);
  for (const a of sets) for (const b of sets) {
    if (a.elements.length >= b.elements.length) continue;
    const additions = b.elements.filter(index => !(a.mask & 2 ** index));
    if (additions.every(index => !feasible[a.mask | 2 ** index])) return { a: a.elements, b: b.elements, failedAdditions: additions };
  }
  return null;
}

function* canonicalWords(size, prefix = []) {
  if (prefix.length === size) { yield prefix; return; }
  for (const value of ['a', 'b', 'c'].slice(0, Math.min(3, new Set(prefix).size + 1))) yield* canonicalWords(size, [...prefix, value]);
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-pinned-quotas.json';
  let plans = 0, pinnedSets = 0, feasibleSets = 0, assignments = 0, validAssignments = 0, infeasiblePlans = 0;
  let firstExchangeFailure = null, allReuseExchangeFailure = null;
  const failures = [];
  for (const reach of [1, 2, 3, 16]) for (let size = 0; size <= 6; size++) {
    for (const target of canonicalWords(size)) {
      const intervals = consecutiveIntervals(target);
      for (let retainedMask = 0; retainedMask < 2 ** intervals.length; retainedMask++) {
        const selected = bits(retainedMask, intervals.length);
        const jobs = deadlineJobs([], target, reach, selected).map(job => ({ value: job.value, deadline: job.deadline - 1 }));
        const exact = exactPinnedSets(target, reach, jobs);
        plans++; assignments += exact.assignments; validAssignments += exact.validAssignments;
        if (!exact.feasible[0]) infeasiblePlans++;
        for (let mask = 0; mask < 2 ** size; mask++) {
          const pinned = bits(mask, size); pinnedSets++;
          try {
            const actual = pinnedQuotaPlan(target, reach, jobs, pinned);
            assert.equal(actual.status === 'feasible', exact.feasible[mask], 'pinned feasibility differs');
            if (actual.status === 'feasible') feasibleSets++;
          } catch (error) {
            failures.push({ target, reach, selected, pinned, jobs, error: error.message });
          }
        }
        if (!firstExchangeFailure || !allReuseExchangeFailure && selected.length === intervals.length) {
          const failure = exchangeFailure(exact.feasible, size);
          if (failure) {
            const result = { target, reach, selected, jobs, ...failure, feasibleSets: exact.feasible.flatMap((valid, mask) => valid ? [bits(mask, size)] : []) };
            if (!firstExchangeFailure) firstExchangeFailure = result;
            if (!allReuseExchangeFailure && selected.length === intervals.length) allReuseExchangeFailure = result;
          }
        }
      }
    }
    console.error(`pinned quotas R=${reach} n=${size}: ${plans} plans, ${pinnedSets} sets, ${failures.length} failures`);
  }
  const report = {
    status: 'finite exact pinned-set feasibility check; no polynomial joint optimizer or Lean theorem claimed',
    predicate: 'For each value v, F_v(k) counts pinned births through k, r_v(k) counts generation jobs due through k, and u_v(k) counts unpinned target positions t with t+R<=k. Define h_v(k)=max_{s<=k}(0,r_v(s)-F_v(s),u_v(s)). At every cut, sum_v h_v(k) must be at most the number of unpinned birth slots through k. Cuts run through every generation and endpoint deadline, so per-value terminal totals are included.',
    construction: 'Each unit increase in h creates a free value job due at that cut. Put the jobs in deadline order into the unpinned birth slots. Match generation jobs by sorted equal-value occurrence order. Independently match endpoint copies with the selected pinned identities and sorted residual occurrences.',
    exactCheck: 'Enumerate every birth-to-target permutation satisfying birth<=target+R. Its target values determine the birth word. Check a separate value-preserving generation matching by sorted deadlines. Every subset of its identity positions is feasible. Compare this exhaustive family with the quota predicate and check each constructed completion.',
    domain: { reaches: [1, 2, 3, 16], length: '0 through 6', targets: 'canonical words with at most 3 values', generation: 'every subset of consecutive equal-value retention intervals', pinned: 'every subset of target positions' },
    plans, pinnedSets, feasibleSets, assignments, validAssignments, infeasiblePlans, failures,
    firstExchangeFailure, allReuseExchangeFailure,
    reproduce: `node scripts/optimality-pinned-quotas.mjs ${output}`
  };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({ plans, pinnedSets, feasibleSets, assignments, validAssignments, infeasiblePlans,
    failures: failures.length, firstExchangeFailure, allReuseExchangeFailure }));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
