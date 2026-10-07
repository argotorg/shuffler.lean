#!/usr/bin/env node
/** Offline exact search for a Q=1 value-presence obstruction. */
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { consecutiveIntervals } from './optimality-interval-realizability.mjs';
import { ordinaryFreshPlan, minimumPlanSwaps } from './optimality-plan-presence.mjs';
import { replay } from './optimality-oracle.mjs';

const canonicalMiddle = (length, kinds) => {
  const extend = prefix => prefix.length === length ? [prefix] :
    ['b', 'c', 'd', 'e'].slice(0, Math.min(kinds, new Set(prefix).size + 1))
      .flatMap(value => extend([...prefix, value]));
  return extend([]);
};

export function swapPositionGraph(ops) {
  const state = ops.reduce(({ height, edges }, op) => op[0] === 'swap' ?
    { height, edges: [...edges, [height - op[1] - 1, height - 1]] } :
    { height: height + 1, edges }, { height: 0, edges: [] });
  const shared = state.edges.length === 2 ? state.edges[0].filter(position => state.edges[1].includes(position)) : [];
  return { edges: state.edges, shared, connected: state.edges.length < 2 || shared.length > 0 };
}

export function carrierRealization(word, reach, requiredPath = null) {
  const end = word.length - 1;
  if (word[0] !== 'a' || word[end] !== 'a' || word.slice(1, end).includes('a') ||
      !Number.isInteger(reach) || reach < 1 || end <= reach || end > 2 * reach) {
    throw new Error('invalid one-gap interval');
  }
  const intervals = consecutiveIntervals(word), plan = ordinaryFreshPlan(word, intervals.map((_, i) => i), reach, 0);
  const target = plan.problem.target, paths = [];
  for (let p = 1; p <= reach; p++) if (end - p <= reach) paths.push([p, end]);
  for (let p = 1; p <= reach; p++) for (let k = p + 1; k < end && k <= p + reach; k++) {
    if (end - k <= reach) paths.push([p, k, end]);
  }
  if (requiredPath !== null) {
    if (!paths.some(path => JSON.stringify(path) === JSON.stringify(requiredPath))) throw new Error('invalid carrier path');
    paths.splice(0, paths.length, requiredPath);
  }
  let trials = 0;
  for (const positions of paths) {
    trials++;
    const births = [...target]; births[positions[0]] = target[0];
    for (let i = 1; i < positions.length; i++) births[positions[i]] = target[positions[i - 1]];
    let stack = [], ops = [], introduced = new Set(), failed = false;
    for (let index = 0; index < births.length; index++) {
      const cut = stack.length - reach;
      if (cut > 0 && (stack.slice(0, cut).some((value, i) => value !== target[i]) ||
          plan.intervals.some(interval => interval.start < cut && cut <= interval.end && !stack.slice(cut).includes(interval.value)))) {
        failed = true; break;
      }
      const value = births[index];
      if (introduced.has(value)) {
        const depth = stack.length - stack.lastIndexOf(value);
        if (depth > reach || depth > stack.length) { failed = true; break; }
        ops.push(['dup', depth]);
      } else { ops.push(['load', Number(value.slice(2))]); introduced.add(value); }
      stack = [...stack, value];
      const pathIndex = positions.indexOf(index);
      if (pathIndex > 0) {
        const lower = positions[pathIndex - 1], copy = [...stack];
        [copy[lower], copy[index]] = [copy[index], copy[lower]];
        stack = copy; ops.push(['swap', index - lower]);
      }
    }
    if (!failed && stack.every((value, index) => value === target[index])) {
      replay(plan.problem, ops);
      return { positions, ops, trials };
    }
  }
  return null;
}

function retainedPath(ops) {
  let stack = [], births = [], lifts = [];
  for (const op of ops) {
    if (op[0] === 'swap') {
      const lower = stack.length - op[1] - 1, upper = stack.length - 1;
      lifts.push({ lower, upper, carriesA: stack[lower] === 'v:42' });
      const copy = [...stack]; [copy[lower], copy[upper]] = [copy[upper], copy[lower]]; stack = copy;
    } else {
      const value = op[0] === 'dup' ? stack[stack.length - op[1]] : `v:${op[1]}`;
      if (value === 'v:42') births.push(stack.length);
      stack = [...stack, value];
    }
  }
  return { births, lifts };
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-one-gap.json';
  const maximumReach = Number(process.argv[3] ?? 4);
  let plans = 0, states = 0, maximumSwaps = 0, twoSwaps = 0, connectedTwoSwaps = 0, carrierTwoSwaps = 0;
  const limits = [], violations = [], disjointExamples = [], nonCarrierExamples = [], maximumExamples = [], carrierFailures = [];
  const counts = {};
  for (let reach = 1; reach <= maximumReach; reach++) for (let end = reach + 1; end <= 2 * reach; end++) {
    for (const middle of canonicalMiddle(end - 1, Math.min(reach, 4))) {
      const word = ['a', ...middle, 'a'], intervals = consecutiveIntervals(word);
      if (intervals.some(interval => interval.value !== 'a' && interval.end - interval.start > reach)) continue;
      const selected = intervals.map((_, index) => index), plan = ordinaryFreshPlan(word, selected, reach, 0);
      if (!plan.capacityFeasible) continue;
      const result = minimumPlanSwaps(plan), graph = result.status === 'reachable' ? swapPositionGraph(result.ops) : null;
      const constructed = carrierRealization(word, reach);
      if (constructed === null) carrierFailures.push({ word, reach });
      plans++; states += result.states;
      counts[reach] = (counts[reach] ?? 0) + 1;
      if (result.status !== 'reachable') { limits.push({ word, reach, result }); continue; }
      if (result.swaps > maximumSwaps) { maximumSwaps = result.swaps; maximumExamples.length = 0; }
      if (result.swaps === maximumSwaps && maximumExamples.length < 5) maximumExamples.push({ word, reach, result, graph });
      if (result.swaps > 2) violations.push({ word, reach, plan, result, graph });
      if (result.swaps === 2) {
        twoSwaps++; if (graph.connected) connectedTwoSwaps++;
        else if (disjointExamples.length < 5) disjointExamples.push({ word, reach, result, graph });
        const path = retainedPath(result.ops);
        const carrier = path.births[0] === 0 && path.births[1] >= 1 && path.births[1] <= reach &&
          path.lifts.every(lift => lift.carriesA) && path.lifts[0].lower === path.births[1] &&
          path.lifts[1].lower === path.lifts[0].upper && path.lifts[1].upper === end;
        if (carrier) carrierTwoSwaps++;
        else if (nonCarrierExamples.length < 5) nonCarrierExamples.push({ word, reach, result, path });
      }
    }
    console.log(JSON.stringify({ reach, end, plans, states, violations: violations.length, limits: limits.length }));
  }
  const report = { status: 'finite exact search, not a movement theorem',
    scope: 'Empty source; first and last target values are a, with no other a. The selected a interval has R<j<=2R. Every consecutive interval of another value is selected and has gap at most R. All per-value direct budgets equal one. Capacity is checked. Equal-copy role exchange and every birth order are allowed.',
    monotonicity: 'Removing selected short intervals only raises the introduction budgets and removes presence requirements. Therefore each witness also works for every subset of its selected short intervals, while retaining the a interval.',
    geometryScope: 'Position graphs describe the returned minimum-SWAP witness only. A disconnected graph does not exclude another connected witness.',
    domain: { reach: `1 through${maximumReach}`, lastA: 'R+1 through2R', middleKinds: 'at most min(R,4)', stateLimit: 300000 },
    carrierDefinition: 'a is born first at0 and copied at some p with1<=p<=R. Both SWAPs lift that copied a: first p→k, then k→j, with no other SWAP.',
    carrierConstruction: 'Try at most R one-hop paths p→j and R squared two-hop paths p→k→j. Rotate the prescribed birth values along the path, then emit one direct introduction per kind and DUP thereafter; perform each path SWAP immediately after its upper position is born. Check the exact presence and reach guards. This is an offline construction experiment, not an integrated runtime policy or a theorem that some path always succeeds.',
    plans, states, counts, maximumSwaps, twoSwaps, connectedTwoSwaps, carrierTwoSwaps,
    limits, violations, disjointExamples, nonCarrierExamples, carrierFailures, maximumExamples,
    reproduce: `node scripts/optimality-one-gap.mjs ${output} ${maximumReach}` };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({ ...report, maximumExamples: maximumExamples.map(({ word, reach, result }) => ({ word, reach, swaps: result.swaps })) }));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
