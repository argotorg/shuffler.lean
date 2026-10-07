#!/usr/bin/env node
/** Offline objective tests for the endpoint assignment and birth quota LP. */
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { solveQuotaLP } from './optimality-quota-lp.mjs';
import { deadlineJobs } from './optimality-birth-matching.mjs';
import { consecutiveIntervals } from './optimality-interval-realizability.mjs';
import { random } from './optimality-bench.mjs';

const positions = (word, value) => word.flatMap((item, index) => item === value ? [index] : []);

export function retentionEntries(target, premiums) {
  return consecutiveIntervals(target).filter(gap => premiums[gap.value] > 0).map(gap => ({
    value: gap.value, previous: gap.start, output: gap.end,
    ordinal: target.slice(0, gap.end + 1).filter(value => value === gap.value).length,
    premium: premiums[gap.value]
  }));
}

function* permutations(size, reach, prefix = []) {
  if (prefix.length === size) { yield prefix; return; }
  for (let output = 0; output < size; output++) {
    if (!prefix.includes(output) && prefix.length <= output + reach) yield* permutations(size, reach, [...prefix, output]);
  }
}

export function exactObjective(target, reach, jobs, { retention = null, swapPrice = 1, edgeCosts = null } = {}) {
  const deadlines = new Map([...new Set(target)].map(value => [value,
    jobs.filter(job => job.value === value).map(job => job.deadline).sort((a, b) => a - b)]));
  let best = null, assignments = 0;
  for (const assignment of permutations(target.length, reach)) {
    const word = assignment.map(output => target[output]);
    const births = new Map([...new Set(target)].map(value => [value, positions(word, value)]));
    if (jobs.length && [...births].some(([value, indices]) => indices.some((birth, index) => birth > deadlines.get(value)[index]))) continue;
    assignments++;
    const E = assignment.filter((output, birth) => output !== birth).length;
    const retained = retention?.map(entry => births.get(entry.value)[entry.ordinal - 1] <= entry.previous + reach) ?? [];
    const objective = retention !== null ? swapPrice * E + retention.reduce((sum, entry, index) => sum + (retained[index] ? 0 : 2 * entry.premium), 0) :
      edgeCosts !== null ? assignment.reduce((sum, output, birth) => sum + edgeCosts[birth][output], 0) : E;
    if (best === null || objective < best.objective) best = { objective, word, assignment, E, retained };
  }
  return best ? { status: 'optimal', ...best, assignments } : { status: 'infeasible', assignments };
}

function* canonicalWords(size, prefix = []) {
  if (prefix.length === size) { yield prefix; return; }
  for (const value of ['a', 'b', 'c'].slice(0, Math.min(3, new Set(prefix).size + 1))) yield* canonicalWords(size, [...prefix, value]);
}

function main() {
  const mode = process.argv[2] ?? 'retention';
  if (!['retention', 'generic'].includes(mode)) throw new Error('mode must be retention or generic');
  const output = process.argv[3] ?? `Bench/evidence-quota-lp-${mode}.json`;
  const seed = 2026100747, next = random(seed), choose = size => Math.floor(next() * size);
  const profiles = [
    { premiums: { a: 1, b: 1, c: 1 }, swapPrice: 1 },
    { premiums: { a: 1, b: 2, c: 33 }, swapPrice: 1 },
    { premiums: { a: 3, b: 3, c: 3 }, swapPrice: 3 },
    { premiums: { a: 0, b: 1, c: 33 }, swapPrice: 1 },
    { premiums: { a: 1, b: 33, c: 2 }, swapPrice: 7 }
  ];
  let cases = 0, trivialZero = 0, solverCases = 0, fractionalModels = 0;
  const failures = [], gaps = [];
  outer: for (let size = 0; size <= 7; size++) for (const reach of [1, 2, 3, 16]) {
    for (const target of canonicalWords(size)) {
      const intervals = consecutiveIntervals(target), all = 2 ** intervals.length - 1;
      const masks = mode === 'retention' ? [0] : [...new Set([all, 0,
        intervals.reduce((mask, _, index) => mask + (index % 2 ? 2 ** index : 0), 0),
        intervals.reduce((mask, _, index) => mask + (index % 2 ? 0 : 2 ** index), 0), choose(all + 1), choose(all + 1)])];
      for (const mask of masks) {
        const selected = intervals.flatMap((_, index) => mask & 2 ** index ? [index] : []);
        const jobs = deadlineJobs([], target, reach, selected).map(job => ({ value: job.value, deadline: job.deadline - 1 }));
        for (const profile of mode === 'retention' ? profiles : [0, 1, 2, 3]) {
          const options = mode === 'retention' ? { retention: retentionEntries(target, profile.premiums), swapPrice: profile.swapPrice } :
            { edgeCosts: target.map(() => target.map(() => choose(10))) };
          const exact = exactObjective(target, reach, jobs, options); cases++;
          if (exact.objective === 0) { trivialZero++; continue; }
          const result = solveQuotaLP(target, reach, jobs, options); solverCases++;
          if (result.status !== 'optimal') {
            if (result.status !== exact.status) failures.push({ target, reach, selected, options, exact, result });
            continue;
          }
          if (result.fractionalEntries) fractionalModels++;
          if (exact.status !== 'optimal' || result.objective < exact.objective) {
            gaps.push({ target, reach, selected, jobs, options, exact, result }); break outer;
          }
          if (result.objective !== exact.objective) failures.push({ target, reach, selected, options, exact, result });
        }
      }
    }
    console.error(`quota LP ${mode} n=${size} R=${reach}: ${cases} cases, ${solverCases} solver calls, ${fractionalModels} fractional models`);
  }
  const report = {
    status: gaps.length ? `finite fractional objective gap for ${mode} LP` : `finite ${mode} LP comparison; no integrality theorem claimed`,
    objective: mode === 'retention' ? 'Minimize twice the generation premium above baseline plus swapPrice*E. Each retention y is in [0,1] and requires the kth equal-value birth by previousTargetPosition+R. Values with zero direct premium have no retention variable.' :
      'Minimize independently sampled integer endpoint-edge costs in 0..9 under fixed generation deadlines. This checks general integrality, not just the moved-token objective E.',
    check: 'Enumerate all lag-valid endpoint permutations and check generation deadlines by value independently. LP primal models and their costs are checked with exact rational arithmetic. Zero integer cost proves zero LP cost without a solver call. Stop at the first fractional objective gap.',
    domain: { maximumLength: 7, reaches: [1, 2, 3, 16], targets: 'all canonical words with at most 3 values until first gap', profiles: mode === 'retention' ? profiles : 'four independent random edge matrices per selected interval plan; all, none, alternating, and two seeded random selections' },
    seed, solver: process.env.Z3_BIN ?? 'z3', cases, trivialZero, solverCases, fractionalModels, gaps, failures,
    reproduce: `Z3_BIN=<z3-path> node scripts/optimality-quota-lp-objectives.mjs ${mode} ${output}`
  };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n'); console.log(JSON.stringify(report));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
