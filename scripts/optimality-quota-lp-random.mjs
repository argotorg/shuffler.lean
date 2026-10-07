#!/usr/bin/env node
/** Seeded larger LP probes, separate from exhaustive permutation evidence. */
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { solveQuotaLP } from './optimality-quota-lp.mjs';
import { retentionEntries } from './optimality-quota-lp-objectives.mjs';
import { deadlineJobs } from './optimality-birth-matching.mjs';
import { consecutiveIntervals } from './optimality-interval-realizability.mjs';
import { random } from './optimality-bench.mjs';

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-quota-lp-random.json';
  const seed = 2026100749, next = random(seed), choose = size => Math.floor(next() * size);
  const stats = Object.fromEntries(['E', 'generic', 'retention'].map(mode => [mode, { cases: 0, integralModels: 0, fractionalModels: 0, integerSolves: 0, gaps: [], unresolved: [] }]));
  const started = Date.now(); let targets = 0;
  for (let sample = 0; sample < 400 && Date.now() - started < 10 * 60 * 1000; sample++) {
    const size = 8 + choose(7), kinds = 3 + choose(4), reach = sample % 10 === 0 ? 16 : 1 + choose(Math.min(8, size - 1));
    const values = Array.from({ length: kinds }, (_, index) => `v${index}`);
    const target = [...values, ...Array.from({ length: size - kinds }, () => values[choose(kinds)])];
    for (let i = target.length - 1; i > 0; i--) { const j = choose(i + 1); [target[i], target[j]] = [target[j], target[i]]; }
    const intervals = consecutiveIntervals(target); let selected = intervals.flatMap((_, index) => next() < .75 ? [index] : []);
    let jobs;
    while (true) {
      jobs = deadlineJobs([], target, reach, selected).map(job => ({ value: job.value, deadline: job.deadline - 1 }));
      const deadlines = jobs.map(job => job.deadline).sort((a, b) => a - b);
      if (deadlines.every((deadline, index) => index <= deadline)) break;
      selected = selected.filter((_, index) => index !== choose(selected.length));
    }
    targets++;
    for (const mode of ['E', 'generic', 'retention']) {
      if (stats[mode].gaps.length) continue;
      const premiums = Object.fromEntries(values.map(value => [value, [0, 1, 2, 3, 8, 33][choose(6)]]));
      const options = mode === 'E' ? {} : mode === 'generic' ? { edgeCosts: target.map(() => target.map(() => choose(16))) } :
        { retention: retentionEntries(target, premiums), swapPrice: 1 + choose(7) };
      const activeJobs = mode === 'retention' ? target.map((value, output) => ({ value, deadline: output + reach })) : jobs;
      const result = solveQuotaLP(target, reach, activeJobs, options);
      const info = { sample, target, reach, selected: mode === 'retention' ? [] : selected, jobs: activeJobs, options, result };
      stats[mode].cases++;
      if (result.status !== 'optimal') { stats[mode].unresolved.push(info); continue; }
      if (!result.fractionalEntries) { stats[mode].integralModels++; continue; }
      stats[mode].fractionalModels++;
      const integer = solveQuotaLP(target, reach, activeJobs, { ...options, integral: true, timeoutMs: 20000 });
      stats[mode].integerSolves++;
      if (integer.status !== 'optimal') { stats[mode].unresolved.push({ ...info, integer }); continue; }
      if (result.objective < integer.objective) stats[mode].gaps.push({ ...info, integer });
      else if (result.objective !== integer.objective) stats[mode].unresolved.push({ ...info, integer });
    }
    if (sample % 20 === 0) console.error(`random LP ${sample}: ${JSON.stringify(Object.fromEntries(Object.entries(stats).map(([mode, info]) => [mode, { cases: info.cases, fractional: info.fractionalModels, gaps: info.gaps.length }])))} `);
    if (Object.values(stats).every(info => info.gaps.length)) break;
  }
  const report = {
    status: 'seeded larger LP probes; solver integer optima are separate from exhaustive permutation checks',
    scope: 'For a returned integral LP optimum, the same matrix is a legal integer solution. For a fractional LP optimum, compare with a separate integer-variable solve in Z3. Every primal matrix, quota, endpoint lag, optional retention inequality, and objective is checked with exact rational arithmetic. Unknown and error results are inconclusive.',
    domain: { seed, targetsRequested: 400, length: '8 through 14', kinds: '3 through 6', reaches: '1 through min(8,n-1), plus 16 every tenth sample', fixedRetention: 'seeded subsets reduced until unit-job deadline capacity holds', genericCosts: 'independent integers 0 through 15', premiums: [0, 1, 2, 3, 8, 33], swapPrices: '1 through 7', wallLimitMinutes: 10 },
    solver: process.env.Z3_BIN ?? 'z3', targets, milliseconds: Date.now() - started, stats,
    reproduce: `Z3_BIN=<z3-path> node scripts/optimality-quota-lp-random.mjs ${output}`
  };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n'); console.log(JSON.stringify(report));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
