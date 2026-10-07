#!/usr/bin/env node
/** Falsify a proposed realization bound on canonical words. Offline only. */
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { ordinaryFreshPlan, minimumPlanSwaps } from './optimality-plan-presence.mjs';
import { consecutiveIntervals } from './optimality-interval-realizability.mjs';

export function canonicalWords(length, kinds = 3) {
  const alphabet = ['a', 'b', 'c'];
  const extend = prefix => {
    if (prefix.length === length) return [prefix];
    const present = new Set(prefix).size;
    return alphabet.slice(0, Math.min(kinds, present + 1)).flatMap(value => extend([...prefix, value]));
  };
  return extend([]);
}

export function movementTerms(word, selected, reach, old) {
  const intervals = consecutiveIntervals(word);
  const M = Math.min(old, word.length);
  const Q = Math.ceil(old * word.length / reach) + selected.reduce((sum, index) =>
    sum + Math.floor((intervals[index].end - intervals[index].start - 1) / reach), 0);
  return { M, Q, floor: Math.max(M, Q) };
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-plan-factor-two.json';
  const cachePath = process.argv[3] ?? 'Bench/plan-realization-cache.jsonl';
  const cache = new Map(fs.existsSync(cachePath) ? fs.readFileSync(cachePath, 'utf8').trim().split('\n')
    .filter(Boolean).map(line => { const row = JSON.parse(line); return [row.key, row.result]; }) : []);
  let plans = 0, searches = 0, states = 0, violations = 0, first = null, maximumRatio = null, worst = null;
  let zeroFloorCases = 0, zeroFloorViolations = 0;
  outer: for (const reach of [1, 2, 3]) for (let old = 0; old <= reach; old++) {
    for (let size = 0; size <= 6; size++) for (const word of canonicalWords(size)) {
      const intervals = consecutiveIntervals(word);
      for (let mask = 0; mask < 2 ** intervals.length; mask++) {
        const selected = intervals.flatMap((_, index) => mask & 2 ** index ? [index] : []);
        const plan = ordinaryFreshPlan(word, selected, reach, old);
        if (!plan.capacityFeasible) continue;
        plans++;
        const key = JSON.stringify([reach, old, word, selected]);
        if (!cache.has(key)) {
          const result = minimumPlanSwaps(plan); cache.set(key, result); searches++;
          fs.appendFileSync(cachePath, JSON.stringify({ key, result }) + '\n');
        }
        const result = cache.get(key); states += result.states;
        if (result.status !== 'reachable') { first = { key, plan, result, reason: 'unrealizable-or-limit' }; break outer; }
        const terms = movementTerms(word, selected, reach, old);
        if (terms.floor === 0) { zeroFloorCases++; if (result.swaps > 0) zeroFloorViolations++; }
        else if (maximumRatio === null || result.swaps / terms.floor > maximumRatio) {
          maximumRatio = result.swaps / terms.floor; worst = { key, plan, result, ...terms };
        }
        if (result.swaps > 2 * terms.floor) { violations++; first ??= { key, plan, result, ...terms }; }
      }
    }
  }
  const report = { status: 'finite falsification evidence for a proposed realization theorem, not a proof',
    semantics: 'Ordinary value presence at selected cuts; per-value introduction upper budgets; equal-copy exchange and extra retention are allowed.',
    M: 'min(q,m): every initial position replaced by a fresh value requires selection by a SWAP, including the initial top.',
    Q: 'ceil(q*m/R) + sum over selected(i,j) of floor((j-i-1)/R). The two terms propose old-copy transport and retained-seed lifts.',
    proposedBound: 'minimum SWAPs under the plan budgets and presence conditions <= 2*max(M,Q)',
    domain: { reaches: [1, 2, 3], oldCopies: '0 through R', canonicalFreshKinds: 'at most3', freshLength: '0 through6', stateLimit: 300000 },
    plans, newSearches: searches, states, violations, zeroFloorCases, zeroFloorViolations, maximumRatio, worst, first,
    cachePath, reproduce: `node scripts/optimality-plan-factor-two.mjs ${output} ${cachePath}` };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({ ...report, worst: worst && { key: worst.key, swaps: worst.result.swaps, M: worst.M, Q: worst.Q } }));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
