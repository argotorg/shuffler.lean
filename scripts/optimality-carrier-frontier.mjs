#!/usr/bin/env node
/** Falsify a static two-hop frontier-growth hypothesis. Offline only. */
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { random } from './optimality-bench.mjs';
import { consecutiveIntervals } from './optimality-interval-realizability.mjs';

export function carrierFrontier(word, reach) {
  const end = word.length - 1, intervals = consecutiveIntervals(word);
  if (word[0] !== 'a' || word[end] !== 'a' || word.slice(1, end).includes('a') ||
      !Number.isInteger(reach) || reach < 1 || end <= reach) throw new Error('invalid carrier interval');
  if (intervals.some(interval => interval.value !== 'a' && interval.end - interval.start > reach)) {
    throw new Error('invalid short gap');
  }
  const occupancy = Array(end).fill(0);
  for (const interval of intervals) for (let cut = interval.start; cut < interval.end; cut++) occupancy[cut]++;
  const maximumOccupancy = Math.max(...occupancy), capacityFeasible = maximumOccupancy <= reach;
  const ceilings = word.map((value, position) => {
    const previous = word.slice(0, position).lastIndexOf(value);
    const offset = word.slice(position + 1).indexOf(value);
    const next = offset < 0 ? Infinity : position + 1 + offset;
    const height = previous < 0 || next - previous <= reach ? position + reach : previous + reach;
    return Math.min(end, height);
  });
  const Q = Math.floor((end - 1) / reach), frontiers = [reach];
  for (let step = 0; step < 2 * Q + 2; step++) {
    const previous = frontiers.at(-1);
    frontiers.push(Math.max(previous, ...ceilings.slice(1, Math.min(previous + 1, end))));
  }
  const first = frontiers.findIndex((frontier, index) => index + 2 < frontiers.length &&
    frontiers[index + 2] < Math.min(end, frontier + reach));
  return { Q, occupancy, maximumOccupancy, capacityFeasible, ceilings, frontiers,
    firstFailure: first < 0 ? null : { step: first, before: frontiers[first], afterTwo: frontiers[first + 2],
      required: Math.min(end, frontiers[first] + reach) } };
}

function* canonicalMiddle(size, kinds, prefix = []) {
  if (prefix.length === size) { yield prefix; return; }
  for (const value of ['b', 'c', 'd'].slice(0, Math.min(kinds, new Set(prefix).size + 1))) {
    yield* canonicalMiddle(size, kinds, [...prefix, value]);
  }
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-carrier-frontier.json';
  const seed = 2026100742, next = random(seed), choose = values => values[Math.floor(next() * values.length)];
  let tested = 0, capacityRejected = 0, gapRejected = 0, frontierSteps = 0, randomAttempts = 0;
  let violatingInputs = 0, globalBoundFailures = 0, firstGlobalFailure = null;
  const failures = [], counts = {};
  const check = (word, reach, source) => {
    if (consecutiveIntervals(word).some(interval => interval.value !== 'a' && interval.end - interval.start > reach)) {
      gapRejected++; return;
    }
    const result = carrierFrontier(word, reach);
    if (!result.capacityFeasible) { capacityRejected++; return; }
    tested++; frontierSteps += result.frontiers.length - 2;
    counts[source] = (counts[source] ?? 0) + 1;
    if (result.firstFailure) {
      violatingInputs++; if (failures.length < 10) failures.push({ word, reach, source, result });
    }
    if (result.frontiers[2 * result.Q] < word.length - 1) {
      globalBoundFailures++; firstGlobalFailure ??= { word, reach, source, result };
    }
  };
  for (let reach = 1; reach <= 3; reach++) for (let end = reach + 1; end <= 4 * reach; end++) {
    for (const middle of canonicalMiddle(end - 1, 3)) check(['a', ...middle, 'a'], reach, 'exhaustive canonical middle');
  }
  for (let reach = 1; reach <= 16; reach++) for (let attempt = 0; attempt < 1000; attempt++) {
    const end = reach + 1 + Math.floor(next() * 7 * reach), kinds = 1 + Math.floor(next() * (reach + 2));
    const middle = [], latest = new Map();
    for (let index = 1; index < end; index++) {
      const active = [...latest].filter(([, last]) => index - last <= reach).map(([value]) => value);
      const value = active.length === 0 || latest.size < kinds && next() < .35 ? `b${latest.size}` : choose(active);
      latest.set(value, index); middle.push(value);
    }
    randomAttempts++; check(['a', ...middle, 'a'], reach, 'seeded short-gap word');
  }
  const report = { status: 'finite counterexamples to the proposed static carrier frontier bounds; no production approximation claim',
    scope: 'a occurs only at0 andj. Every other consecutive equal-value gap is at mostR and selected. Retained-value occupancy must be at mostR. All values have one direct introduction budget.',
    edge: 'For p<q<=p+R, with u the previous occurrence of target[p] and v the next, p→q iff u is absent or min(v,q)-u<=R.',
    frontier: 'F0=R; F(k+1)=max(Fk,max_{1<=p<=Fk} H(p)), capped atj. H=p+R if p is a first occurrence or next(p)-prev(p)<=R; otherwise H=prev(p)+R.',
    hypothesis: 'F(k+2)>=min(j,Fk+R) for every tested k. If true generally, this yields at most2*floor((j-1)/R) carrier SWAPs.',
    domain: { exhaustive: 'R1..3, j in[R+1,4R], at most3 canonical middle kinds', random: 'R1..16, j in[R+1,8R], at mostR+2 middle kinds', seed },
    tested, counts, frontierSteps, gapRejected, capacityRejected, randomAttempts,
    violatingInputs, globalBoundFailures, failures, firstGlobalFailure,
    excludedTrap: { word: ['a', 'b', 'c', 'b', 'c', 'a'], reach: 2,
      result: carrierFrontier(['a', 'b', 'c', 'b', 'c', 'a'], 2) },
    reproduce: `node scripts/optimality-carrier-frontier.mjs ${output}` };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify(report));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
