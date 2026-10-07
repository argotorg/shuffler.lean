#!/usr/bin/env node
/** Offline one-value exchange tests for diagonal endpoint costs. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { minimumAssignment } from './optimality-birth-matching.mjs';

export function endpointMovement(births, targets, reach) {
  assert.equal(births.length, targets.length);
  const costs = births.map(birth => targets.map(target => birth <= target + reach ? Number(birth !== target) : Infinity));
  const result = minimumAssignment(costs);
  return result.status === 'optimal' ? result.cost : null;
}

function* subsets(size, count, prefix = [], start = 0) {
  if (prefix.length === count) { yield prefix; return; }
  for (let index = start; index < size; index++) yield* subsets(size, count, [...prefix, index], index + 1);
}

export function valuatedExchange(size, targets, reach, deadlines, { premium = null, swapPrice = 1 } = {}) {
  const orderedDeadlines = [...deadlines].sort((a, b) => a - b), bases = [], lookup = new Map();
  assert.equal(orderedDeadlines.length, targets.length);
  for (const births of subsets(size, targets.length)) {
    if (births.some((birth, index) => birth > orderedDeadlines[index])) continue;
    const moved = endpointMovement(births, targets, reach);
    if (moved === null) continue;
    const extraDirect = births.filter((birth, index) => index > 0 && birth > targets[index - 1] + reach).length;
    const cost = premium === null ? moved : 2 * premium * extraDirect + swapPrice * moved;
    const entry = { births, moved, extraDirect, cost };
    bases.push(entry); lookup.set(births.join(','), entry);
  }
  let obligations = 0;
  for (const a of bases) for (const b of bases) {
    const onlyA = a.births.filter(index => !b.births.includes(index));
    const onlyB = b.births.filter(index => !a.births.includes(index));
    for (const x of onlyA) {
      obligations++; const attempts = []; let satisfied = false;
      for (const y of onlyB) {
        const aNext = [...a.births.filter(index => index !== x), y].sort((first, second) => first - second);
        const bNext = [...b.births.filter(index => index !== y), x].sort((first, second) => first - second);
        const first = lookup.get(aNext.join(',')), second = lookup.get(bNext.join(','));
        attempts.push({ y, aNext, bNext, first: first ?? null, second: second ?? null });
        if (first && second && a.cost + b.cost >= first.cost + second.cost) { satisfied = true; break; }
      }
      if (!satisfied) return { bases, obligations, failure: { a, b, x, attempts } };
    }
  }
  return { bases, obligations, failure: null };
}

function main() {
  const mode = process.argv[2] ?? 'fixed';
  if (!['fixed', 'full'].includes(mode)) throw new Error('mode must be fixed or full');
  const output = process.argv[3] ?? `Bench/evidence-valuated-exchange-${mode}.json`;
  let instances = 0, bases = 0, obligations = 0;
  const failures = [];
  outer: for (let size = 0; size <= 8; size++) for (const reach of [1, 2, 3, 16]) {
    for (let count = 0; count <= size; count++) for (const targets of subsets(size, count)) {
      const selections = mode === 'fixed' ? Array.from({ length: 2 ** Math.max(0, count - 1) }, (_, mask) => mask) : [0];
      const prices = mode === 'full' ? [0, 1, 3, 33].flatMap(premium => [1, 3].map(swapPrice => ({ premium, swapPrice }))) : [{}];
      for (const selectedMask of selections) for (const price of prices) {
        const deadlines = targets.map((target, index) => (index > 0 && selectedMask & 2 ** (index - 1) ? targets[index - 1] : target) + reach);
        const result = valuatedExchange(size, targets, reach, deadlines, price);
        instances++; bases += result.bases.length; obligations += result.obligations;
        if (result.failure) {
          failures.push({ size, targets, reach, deadlines, selectedMask, price, ...result.failure });
          break outer;
        }
      }
    }
    console.error(`valuated ${mode} n=${size} R=${reach}: ${instances} instances, ${obligations} obligations`);
  }
  const report = {
    status: failures.length ? `finite counterexample to ${mode} one-value valuated exchange` : `finite ${mode} one-value exchange evidence; no valuated-matroid theorem claimed`,
    valuation: mode === 'fixed' ? 'f(B) is minimum moved endpoints in a matching from birth positions B to fixed target positions T, under birth<=target+R. B must also meet fixed generation deadlines from every selected interval subset.' :
      'g(B)=2*premium*extraDirect(B)+swapPrice*minimumMovedEndpoints(B). The domain is all endpoint-feasible birth sets. extraDirect counts kth births beyond previousTargetPosition+R for k>=2. First direct cost is a constant and is omitted.',
    exchange: 'For every feasible A,B and x in A minus B, require some y in B minus A with both exchanged sets feasible and cost(A)+cost(B)>=cost(A-x+y)+cost(B-y+x). Endpoint costs use exact assignment matching with a checked primal-dual certificate.',
    domain: { maximumSize: 8, reaches: [1, 2, 3, 16], targets: 'all position subsets of the ground set', generation: mode === 'fixed' ? 'all selected consecutive occurrence intervals' : 'all endpoint-feasible sets', prices: mode === 'full' ? { premiums: [0, 1, 3, 33], swapPrices: [1, 3] } : null, stopping: 'first failed exchange, by increasing ground-set size' },
    instances, bases, obligations, failures,
    ...(mode === 'full' && failures[0]?.size === 5 && failures[0]?.targets.join(',') === '0,1,2' ? {
      symbolicCounterexample: { assumptions: 'premium p>0 and swap price s>0', targets: [0, 1, 2], reach: 2,
        A: [0, 1, 4], B: [0, 2, 3], x: 1, originalCost: '2p+2s',
        exchanges: [{ y: 2, cost: '2p+3s', strictIncrease: 's' }, { y: 3, cost: '4p+2s', strictIncrease: '2p' }],
        scope: 'Direct symbolic calculation from the displayed exact endpoint movement and extra-direct counts. This is not a Lean theorem.' }
    } : {}),
    reproduce: `node scripts/optimality-valuated-exchange.mjs ${mode} ${output}`
  };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n'); console.log(JSON.stringify(report));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
