#!/usr/bin/env node
/** Offline interval form of the exact pinned quota condition. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { deadlineJobs } from './optimality-birth-matching.mjs';
import { consecutiveIntervals } from './optimality-interval-realizability.mjs';
import { pinnedQuotaPlan } from './optimality-pinned-quotas.mjs';

const subsets = size => Array.from({ length: 2 ** size }, (_, mask) =>
  Array.from({ length: size }, (_, index) => index).filter(index => mask & 2 ** index));

/** Positions and cuts are zero-based. Interval ends are exclusive. */
export function coloredPinPlan(target, reach, selected, pinned) {
  assert.ok(Number.isInteger(reach) && reach >= 1, 'invalid reach');
  const gaps = consecutiveIntervals(target), values = [...new Set(target)];
  assert.ok(new Set(selected).size === selected.length && selected.every(index =>
    Number.isInteger(index) && index >= 0 && index < gaps.length), 'invalid selected gaps');
  assert.ok(new Set(pinned).size === pinned.length && pinned.every(index =>
    Number.isInteger(index) && index >= 0 && index < target.length), 'invalid pinned endpoints');
  const obligations = selected.flatMap(gap => {
    const { value, start } = gaps[gap];
    if (pinned.some(index => target[index] === value && start < index && index <= start + reach)) return [];
    const next = target.findIndex((item, index) => item === value && index > start && !pinned.includes(index));
    return [{ value, start: start + reach, end: next === -1 ? null : next + reach, gap }];
  });
  const cuts = Array.from({ length: target.length + reach }, (_, cut) => {
    const uncovered = values.filter(value => obligations.some(interval => interval.value === value &&
      interval.start <= cut && (interval.end === null || cut < interval.end)));
    const pinCount = pinned.filter(index => index <= cut && cut < index + reach).length;
    const capacity = target.filter((_, index) => index <= cut && cut < index + reach).length;
    const byValue = Object.fromEntries(values.map(value => [value,
      target.filter((item, index) => item === value && index + reach <= cut && !pinned.includes(index)).length +
      Number(uncovered.includes(value))]));
    return { cut, pinned: pinCount, uncovered, capacity, required: pinCount + uncovered.length, byValue };
  });
  const failure = cuts.find(cut => cut.required > cut.capacity);
  return { status: failure ? 'infeasible' : 'feasible', ...(failure ? { cut: failure.cut } : {}), obligations, cuts };
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-colored-pins.json';
  const fixtures = [[], ['a'], ['a', 'a'], ['a', 'b', 'a'], ['a', 'b', 'b', 'a'],
    ['a', 'b', 'b', 'a', 'b', 'a'], ['a', 'a', 'b', 'a', 'b', 'a'],
    ['b', 'c', 'a', 'a', 'a', 'a', 'b', 'c']];
  const reaches = [1, 2, 3, 16];
  let plans = 0, comparisons = 0, feasible = 0;
  const failures = [];
  for (const target of fixtures) for (const reach of reaches) {
    for (const selected of subsets(consecutiveIntervals(target).length)) {
      const jobs = deadlineJobs([], target, reach, selected).map(job => ({ value: job.value, deadline: job.deadline - 1 }));
      plans++;
      for (const pinned of subsets(target.length)) {
        comparisons++;
        try {
          const actual = coloredPinPlan(target, reach, selected, pinned);
          const quota = pinnedQuotaPlan(target, reach, jobs, pinned);
          assert.equal(actual.status, quota.status, 'feasibility differs');
          if (actual.status === 'feasible') feasible++;
          else assert.equal(actual.cut, quota.cut, 'first failed cut differs');
          for (const cut of quota.quotas) assert.deepEqual(actual.cuts[cut.cut].byValue, cut.byValue, 'per-value quota differs');
        } catch (error) { failures.push({ target, reach, selected, pinned, error: error.message }); }
      }
    }
  }
  const counterexample = coloredPinPlan(['a', 'b', 'b', 'a', 'b', 'a'], 2, [1], [0, 2, 3]);
  const report = {
    status: 'finite check of an algebraic quota reformulation; no new trace oracle or production policy',
    predicate: 'For each retained same-value gap p to t without a pinned same-value endpoint in (p,p+R], add [p+R,u+R), where u is the next unpinned same-value endpoint after p, or infinity if absent. At each cut count every pin in (k-R,k] plus each value covered by the union of its obligation intervals. This count must not exceed the number of target indices in (k-R,k].',
    comparison: 'Compare all per-value quotas returned by the separate exact pinned-quota implementation, each first failed cut, and overall feasibility. This checks eight named targets, all their retained-gap and pin subsets, and four reaches.',
    domain: { fixtures, reaches }, plans, comparisons, feasible, failures, counterexample,
    reproduce: `node scripts/optimality-colored-pins.mjs ${output}`
  };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({ plans, comparisons, feasible, failures }));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
