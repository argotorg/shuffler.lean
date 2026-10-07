#!/usr/bin/env node
/** Offline check of a closed-form Q=1 carrier selection rule. */
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { random } from './optimality-bench.mjs';
import { consecutiveIntervals } from './optimality-interval-realizability.mjs';
import { ordinaryFreshPlan } from './optimality-plan-presence.mjs';
import { carrierRealization } from './optimality-one-gap.mjs';

export function structuralCarrierPaths(word, reach) {
  const end = word.length - 1, intervals = consecutiveIntervals(word);
  if (word[0] !== 'a' || word[end] !== 'a' || word.slice(1, end).includes('a') ||
      !Number.isInteger(reach) || reach < 1 || end <= reach || end > 2 * reach ||
      intervals.some(interval => interval.value !== 'a' && interval.end - interval.start > reach)) {
    throw new Error('invalid one-gap interval');
  }
  const p = Array.from({ length: reach }, (_, index) => index + 1)
    .filter(index => word.indexOf(word[index]) === index).at(-1);
  const threshold = end - reach;
  if (p >= threshold) return [[p, end]];
  return Array.from({ length: p + reach - threshold + 1 }, (_, index) => index + threshold)
    .filter(k => word.indexOf(word[k]) === k || word.slice(0, k).lastIndexOf(word[k]) >= threshold)
    .map(k => [p, k, end]);
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-carrier-selection.json';
  const seed = 2026100741, next = random(seed), choose = values => values[Math.floor(next() * values.length)];
  const fixtures = new Map();
  const add = (word, reach, source) => {
    const intervals = consecutiveIntervals(word);
    if (intervals.some(interval => interval.value !== 'a' && interval.end - interval.start > reach)) return;
    const plan = ordinaryFreshPlan(word, intervals.map((_, index) => index), reach, 0);
    if (!plan.capacityFeasible) return;
    const key = JSON.stringify([word, reach]);
    if (!fixtures.has(key)) fixtures.set(key, { word, reach, source });
  };
  const canonical = (size, kinds) => {
    const extend = prefix => prefix.length === size ? [prefix] :
      ['b', 'c', 'd', 'e'].slice(0, Math.min(kinds, new Set(prefix).size + 1))
        .flatMap(value => extend([...prefix, value]));
    return extend([]);
  };
  for (let reach = 1; reach <= 4; reach++) for (let end = reach + 1; end <= 2 * reach; end++) {
    for (const middle of canonical(end - 1, reach)) add(['a', ...middle, 'a'], reach, 'same870 exact domain');
  }
  for (let reach = 1; reach <= 16; reach++) {
    for (let attempt = 0; attempt < 1000; attempt++) {
      const end = reach + 1 + Math.floor(next() * reach), kinds = 1 + Math.floor(next() * reach);
      const middle = [], latest = new Map();
      for (let index = 1; index < end; index++) {
        const active = [...latest].filter(([, last]) => index - last <= reach).map(([value]) => value);
        const value = active.length === 0 || latest.size < kinds && next() < .35 ? `b${latest.size}` : choose(active);
        latest.set(value, index); middle.push(value);
      }
      add(['a', ...middle, 'a'], reach, 'seeded short-gap word');
    }
    if (reach >= 2) add(['a', ...Array.from({ length: reach - 1 }, (_, index) => [`c${index}`, `c${index}`]).flat(), 'd', 'a'], reach, 'collision family');
  }
  let pathsChecked = 0, oneHop = 0, twoHop = 0, equalDisplacedValues = 0;
  const failures = [], counts = {}, collisionWitnesses = [];
  for (const fixture of fixtures.values()) {
    const { word, reach } = fixture, paths = structuralCarrierPaths(word, reach);
    counts[fixture.source] = (counts[fixture.source] ?? 0) + 1;
    if (paths.length === 0) failures.push({ ...fixture, reason: 'no qualifying path' });
    for (const path of paths) {
      const witness = carrierRealization(word, reach, path);
      pathsChecked++; if (path.length === 2) oneHop++; else twoHop++;
      if (path.length === 3 && word[path[0]] === word[path[1]]) equalDisplacedValues++;
      if (witness === null) failures.push({ ...fixture, path, reason: 'path failed emission or presence' });
      if (fixture.source === 'collision family' && path === paths[0]) collisionWitnesses.push({ ...fixture, path, witness });
    }
  }
  const report = { status: 'finite constructive check, not a Lean proof or production integration',
    rule: 'Let p be the last first-occurrence position in1..R. If p>=j-R, choose p→j. Otherwise any k in[j-R,p+R] that is a first occurrence or whose previous equal occurrence is>=j-R gives p→k→j.',
    scope: 'Empty source; a occurs only at0 andj, R<j<=2R; all other consecutive equal-value gaps are at mostR and selected. One direct introduction per kind. Every qualifying intermediate k is tested, not just the first.',
    proofIdea: 'If no qualifying k existed, the interval[j-R,p+R] would contain at leastp+1 distinct values whose first occurrences are all among positions1..p. This contradicts the number of those positions. This text is an argument, not a machine-checked theorem.',
    witnessCheck: 'The fixed path determines the birth word. The existing offline emitter checks DUP reach, exact frozen prefix, selected-cut value presence, one direct per kind, and final replay. It performs no search for another path after a supplied structural path fails.',
    seed, randomAttempts: 16000, fixtures: fixtures.size, counts, pathsChecked, oneHop, twoHop,
    equalDisplacedValues, failures, collisionWitnesses,
    reproduce: `node scripts/optimality-carrier-selection.mjs ${output}` };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({ ...report, collisionWitnesses: collisionWitnesses.map(({ reach, path }) => ({ reach, path })) }));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
