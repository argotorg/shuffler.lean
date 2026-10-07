#!/usr/bin/env node
/** Small structured family with two retained values before an a block. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { exactObjective, retentionEntries } from './optimality-quota-lp-objectives.mjs';
import { solveQuotaLP } from './optimality-quota-lp.mjs';
import { deadlineJobs } from './optimality-birth-matching.mjs';
import { consecutiveIntervals } from './optimality-interval-realizability.mjs';

function compare(target, reach, selected, options) {
  const jobs = deadlineJobs([], target, reach, selected).map(job => ({ value: job.value, deadline: job.deadline - 1 }));
  const exact = exactObjective(target, reach, jobs, options), lp = solveQuotaLP(target, reach, jobs, options);
  assert.equal(lp.status, exact.status, 'feasibility differs');
  return { target, reach, selected, jobs, options, exact, lp,
    gap: lp.status === 'optimal' && lp.objective < exact.objective };
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-coupled-prefetch.json';
  const records = [], failures = [];
  const profiles = [
    { premiums: { a: 1, b: 1, c: 1 }, swapPrice: 1 },
    { premiums: { a: 1, b: 33, c: 33 }, swapPrice: 1 },
    { premiums: { a: 33, b: 1, c: 3 }, swapPrice: 3 },
    { premiums: { a: 3, b: 3, c: 3 }, swapPrice: 3 }
  ];
  for (const length of [3, 4, 5, 6]) for (const reach of [3, 4]) {
    const target = ['b', 'c', ...Array(length).fill('a'), 'b', 'c'], intervals = consecutiveIntervals(target);
    for (let internal = 0; internal < length - 1; internal++) {
      const selected = intervals.flatMap((gap, index) => gap.value !== 'a' || gap.start === 2 + internal ? [index] : []);
      try { records.push({ mode: 'fixed-E', internal, ...compare(target, reach, selected, {}) }); }
      catch (error) { failures.push({ target, reach, selected, error: error.message }); }
    }
    for (const profile of profiles) {
      const options = { retention: retentionEntries(target, profile.premiums), swapPrice: profile.swapPrice };
      try { records.push({ mode: 'optional-retention', profile, ...compare(target, reach, [], options) }); }
      catch (error) { failures.push({ target, reach, profile, error: error.message }); }
    }
    console.error(`coupled prefetch a=${length} R=${reach}: ${records.length} cases, ${failures.length} failures`);
  }
  const report = {
    status: records.some(record => record.gap) ? 'fractional gap in a coupled-prefetch family' : 'finite coupled-prefetch family with no fractional objective gap',
    scope: 'Targets are b,c,a^m,b,c. Fixed-E cases retain both long b/c gaps and one chosen internal a gap. Optional-retention cases optimize all gaps with one premium per value. Integer minima are exhaustive over all lag-valid endpoint permutations and independent generation matching. LP primal models use exact rational checks. This structured family is not an integrality proof.',
    domain: { aBlockLengths: [3, 4, 5, 6], reaches: [3, 4], internalGaps: 'each consecutive a pair', profiles },
    cases: records.length, gaps: records.filter(record => record.gap).length,
    fractionalModels: records.filter(record => record.lp.fractionalEntries > 0).length,
    exactFeasibleAssignments: records.reduce((sum, record) => sum + record.exact.assignments, 0),
    failures, records,
    reproduce: `Z3_BIN=<z3-path> node scripts/optimality-coupled-prefetch.mjs ${output}`
  };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({ cases: report.cases, gaps: report.gaps, fractionalModels: report.fractionalModels,
    exactFeasibleAssignments: report.exactFeasibleAssignments, failures }));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
