#!/usr/bin/env node
/** Exact offline assignment checks for indistinguishable old copies. */
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { consecutiveIntervals } from './optimality-interval-realizability.mjs';

function dimensions(reach, old, fresh) {
  if (!Number.isSafeInteger(reach) || reach < 1 || !Number.isSafeInteger(old) || old < 0 || old > reach ||
      !Number.isSafeInteger(fresh) || fresh < 0) throw new Error('invalid dimensions');
}

export function oldTransportFloor(reach, old, fresh) {
  dimensions(reach, old, fresh);
  return old * Math.floor(fresh / reach) + Math.min(old, fresh % reach);
}

export function minimumOldAssignment(reach, old, fresh) {
  dimensions(reach, old, fresh);
  if (old > 16) throw new Error('exact assignment check supports at most16 old copies');
  const memo = new Map();
  const visit = (used, destination) => {
    if (destination === old) return { cost: 0, sources: [] };
    if (memo.has(used)) return memo.get(used);
    let best = null;
    for (let source = 0; source < old; source++) {
      if (used & 2 ** source) continue;
      const rest = visit(used | 2 ** source, destination + 1);
      const cost = Math.ceil(Math.max(fresh + destination - source, 0) / reach) + rest.cost;
      if (best === null || cost < best.cost) best = { cost, sources: [source, ...rest.sources] };
    }
    memo.set(used, best); return best;
  };
  return visit(0, 0);
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-old-transport-floor.json';
  const cachePath = process.argv[3] ?? 'Bench/plan-realization-cache.jsonl';
  let assignments = 0, firstAssignmentMismatch = null;
  for (let reach = 1; reach <= 6; reach++) for (let old = 0; old <= reach; old++) {
    for (let fresh = 0; fresh <= 3 * reach; fresh++) {
      const formula = oldTransportFloor(reach, old, fresh), exact = minimumOldAssignment(reach, old, fresh);
      assignments++;
      if (formula !== exact.cost) firstAssignmentMismatch ??= { reach, old, fresh, formula, exact };
    }
  }
  const records = fs.readFileSync(cachePath, 'utf8').trim().split('\n').filter(Boolean).map(JSON.parse);
  let violations = 0, maximumRatio = null, worst = null, strongerThanPooled = 0, firstViolation = null;
  for (const { key, result } of records) {
    const [reach, old, word, selected] = JSON.parse(key), intervals = consecutiveIntervals(word);
    const oldFloor = oldTransportFloor(reach, old, word.length);
    if (oldFloor > Math.ceil(old * word.length / reach)) strongerThanPooled++;
    const gapFloor = selected.reduce((sum, index) => sum + Math.floor((intervals[index].end - intervals[index].start - 1) / reach), 0);
    const total = oldFloor + gapFloor;
    if (result.status !== 'reachable') throw new Error('the saved cache has an incomplete result');
    if (result.swaps > 2 * total) { violations++; firstViolation ??= { key, result, oldFloor, gapFloor }; }
    if (total > 0 && (maximumRatio === null || result.swaps / total > maximumRatio)) {
      maximumRatio = result.swaps / total; worst = { key, swaps: result.swaps, oldFloor, gapFloor };
    }
  }
  const report = { status: 'finite exact assignment and cached-realization evidence, not a Lean theorem',
    scope: 'q equal old source values at positions0..q-1, final old positionsm..m+q-1, with q<=R. Each selected fresh interval uses value presence, not fixed ancestry.',
    assignmentObjective: 'min over old-copy matchings sum ceil(max(finalPosition-sourcePosition,0)/R)',
    formula: 'Qold=q*floor(m/R)+min(q,m mod R)',
    assignmentDomain: { reach: '1 through6', old: '0 through reach', fresh: '0 through3*reach' },
    assignments, firstAssignmentMismatch,
    actualCapExample: { reach: 16, old: 2, fresh: 20, pooled: 3, exact: minimumOldAssignment(16, 2, 20), formula: oldTransportFloor(16, 2, 20) },
    realizationCheck: { formula: 'minimum SWAPs <= 2*(Qold + sum_selected floor((j-i-1)/R))',
      cachedPlans: records.length, strongerThanPooled, violations, firstViolation, maximumRatio, worst, cachePath },
    reproduce: `node scripts/optimality-old-transport.mjs ${output} ${cachePath}` };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n'); console.log(JSON.stringify(report));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
