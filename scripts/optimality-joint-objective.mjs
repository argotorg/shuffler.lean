#!/usr/bin/env node
/** Offline weighted check of an interval-plan objective. No production imports. */
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { normalizeCase, baseline, opCost, score, replay, solvePareto } from './optimality-oracle.mjs';
import { consecutiveIntervals } from './optimality-interval-realizability.mjs';
import { oldTransportFloor } from './optimality-old-transport.mjs';

export function weightedFreshCase(word, reach, old, profile, weights) {
  const names = [...new Set(word)];
  const used = profile.slice(0, names.length);
  if (used.length !== names.length || used.some(kind => !['zero', 'literal32', 'load0', 'load32'].includes(kind)) ||
      used.filter(kind => kind === 'zero').length > 1) throw new Error('invalid fresh-kind profile');
  const values = names.map((_, index) => profile[index] === 'zero' ? 'l:0' : profile[index] === 'literal32' ?
    `l:${(1n << 248n) + BigInt(index)}` : `v:${42 + index}`);
  const source = Array(old).fill(values.includes('l:0') ? 'return' : 'l:0');
  return normalizeCase({ source, target: [...word.map(name => values[names.indexOf(name)]), ...source],
    spills: values.filter(value => value.startsWith('v:')).map(value => Number(value.slice(2))),
    loadWidths: names.flatMap((_, index) => values[index].startsWith('l:') ? [] : [[42 + index, profile[index] === 'load0' ? 0 : 32]]),
    weights, caps: { swap: reach, dup: reach } });
}

export function jointPlanChoice(problem, word, plans) {
  const names = [...new Set(word)], intervals = consecutiveIntervals(word);
  const values = names.map(name => problem.target[word.indexOf(name)]);
  const duplicate = score(problem, opCost(problem, ['dup', 1]));
  const direct = value => value.startsWith('l:') ? ['push', value] : ['load', Number(value.slice(2))];
  const prices = values.map(value => score(problem, opCost(problem, direct(value))) - duplicate);
  const cheap = new Set(values.filter((_, index) => prices[index] <= 0));
  const qOld = oldTransportFloor(problem.caps.swap, problem.source.length, word.length);
  const entries = plans.filter(({ selected }) => selected.every(index =>
    !cheap.has(values[names.indexOf(intervals[index].value)]))).map(({ selected, result }) => {
    if (result.status !== 'reachable') throw new Error('incomplete cached realization');
    const premium = names.reduce((sum, name, index) => sum + Math.max(0, prices[index]) *
      (word.filter(value => value === name).length - selected.filter(i => intervals[i].value === name).length - 1), 0);
    const qGap = selected.reduce((sum, index) => sum +
      Math.floor((intervals[index].end - intervals[index].start - 1) / problem.caps.swap), 0);
    return { selected, result, premium, qOld, qGap, floor: premium + duplicate * (qOld + qGap) };
  });
  const floor = Math.min(...entries.map(entry => entry.floor));
  const candidates = entries.filter(entry => entry.floor === floor).map(entry => {
    const mapped = entry.result.ops.reduce(({ stack, ops }, op) => {
      if (op[0] === 'swap') {
        const copy = [...stack], lower = copy.length - op[1] - 1;
        [copy[lower], copy[copy.length - 1]] = [copy.at(-1), copy[lower]];
        return { stack: copy, ops: [...ops, op] };
      }
      const value = op[0] === 'dup' ? stack[stack.length - op[1]] : values[op[1] - 42];
      const next = op[0] === 'dup' && !cheap.has(value) ? op : direct(value);
      return { stack: [...stack, value], ops: [...ops, next] };
    }, { stack: problem.source, ops: [] });
    const ops = mapped.ops;
    const observed = replay(problem, ops);
    return { selected: entry.selected, premium: entry.premium, qOld, qGap: entry.qGap,
      swaps: entry.result.swaps, score: observed.score, cost: observed.cost, ops };
  });
  return { floor, candidates };
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-joint-objective.json';
  const cachePath = process.argv[3] ?? 'Bench/plan-realization-cache.jsonl';
  const groups = new Map();
  for (const line of fs.readFileSync(cachePath, 'utf8').trim().split('\n')) {
    const { key, result } = JSON.parse(line), [reach, old, word, selected] = JSON.parse(key);
    const id = JSON.stringify([reach, old, word]);
    if (!groups.has(id)) groups.set(id, { reach, old, word, plans: [] });
    groups.get(id).plans.push({ selected, result });
  }
  const profiles = [
    ['load0', 'load0', 'load0'], ['load32', 'load32', 'load32'], ['literal32', 'literal32', 'literal32'],
    ['load0', 'literal32', 'load32'], ['load0', 'load32', 'literal32'],
    ['literal32', 'load0', 'load32'], ['literal32', 'load32', 'load0'],
    ['load32', 'load0', 'literal32'], ['load32', 'literal32', 'load0'],
    ['zero', 'load0', 'literal32'], ['zero', 'literal32', 'load0'],
    ['load0', 'zero', 'literal32'], ['literal32', 'zero', 'load0'],
    ['load0', 'literal32', 'zero'], ['literal32', 'load0', 'zero'],
  ];
  const weights = [{ gas: 1, bytes: 0 }, { gas: 0, bytes: 1 }, { gas: 1, bytes: 1 },
    { gas: 4, bytes: 1 }, { gas: 22, bytes: 1 }];
  let baseCases = 0, weightedCases = 0, states = 0, labels = 0, candidates = 0, zeroExcess = 0;
  let lowerBoundViolations = 0, realizationViolations = 0, maximumRatio = null, worst = null, first = null;
  outer: for (const { reach, old, word, plans } of groups.values()) {
    const distinct = new Map(profiles.map(profile => [JSON.stringify(profile.slice(0, new Set(word).size)), profile]));
    for (const profile of distinct.values()) {
      const original = weightedFreshCase(word, reach, old, profile, weights[0]);
      const oracle = solvePareto(original);
      baseCases++; states += oracle.states; labels += oracle.labels ?? 0;
      if (oracle.status !== 'optimal') { first = { reason: 'oracle-incomplete', original, oracle }; break outer; }
      for (const weight of weights) {
        const problem = { ...original, weights: weight }, B = baseline(problem);
        const best = oracle.frontier.reduce((best, point) => score(problem, point.cost) < score(problem, best.cost) ? point : best);
        const optimum = score(problem, best.cost), chosen = jointPlanChoice(problem, word, plans);
        weightedCases++; candidates += chosen.candidates.length;
        if (chosen.floor > optimum - B) {
          lowerBoundViolations++; first ??= { reason: 'floor-above-optimum-excess', problem, B, optimum, chosen, best };
        }
        for (const candidate of chosen.candidates) {
          const excess = candidate.score - B, optExcess = optimum - B;
          if (excess > 2 * optExcess) {
            realizationViolations++; first ??= { reason: 'realization-above-two', problem, B, optimum, chosen, candidate, best };
          }
          if (optExcess === 0) zeroExcess++;
          else if (maximumRatio === null || excess / optExcess > maximumRatio) {
            maximumRatio = excess / optExcess;
            worst = { problem, B, optimum, jointFloor: chosen.floor, candidate, best };
          }
        }
      }
      if (baseCases % 500 === 0) console.log(JSON.stringify({ baseCases, weightedCases, states, lowerBoundViolations, realizationViolations }));
    }
  }
  const report = { status: 'finite exact weighted evidence, not a theorem or production policy',
    scope: 'Source consists of equal old copies. Target is a fresh prefix using at most three kinds, followed by the old copies. Each candidate comes from one exact minimum-SWAP oracle witness under the selected plan\'s per-value introduction upper budgets and selected-cut presence. DUPs of kinds whose direct cost is at most DUP cost are then replaced by their direct operation, preserving all stack values and not increasing the scalar cost. This is not a production or polynomial-time constructor, and the witness need not minimize weighted cost within that plan.',
    quantifiers: 'For every tested weighted input and every plan that minimizes the joint objective, the saved exact minimum-SWAP search supplies one suitable realization. The claim is existence of a realization for each tied minimizer, not a bound on every possible realization. The optimum comparison uses an independent unrestricted Pareto oracle.',
    objective: 'Omit all retention intervals for kinds whose direct price is at most DUP price. Minimize over the remaining capacity-feasible selections: sum_v (roots_v - 1)*max(directPrice_v-DUPPrice,0) + SWAPPrice*(Qold+sum_selected floor((j-i-1)/R)).',
    domain: { reach: '1 through3', oldCopies: '0 through reach', freshLength: '0 through6', profiles, weights },
    cachedPlanGroups: groups.size, baseCases, weightedCases, states, labels, candidates, zeroExcess,
    lowerBoundViolations, realizationViolations, maximumRatio, worst, first, cachePath,
    reproduce: `node scripts/optimality-joint-objective.mjs ${output} ${cachePath}` };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({ ...report, worst: worst && { B: worst.B, optimum: worst.optimum, score: worst.candidate.score, jointFloor: worst.jointFloor } }));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
