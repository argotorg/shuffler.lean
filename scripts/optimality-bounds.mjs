#!/usr/bin/env node
/** Experimental lower bounds. These functions are not production certificates. */
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { baseline, normalizeCase, opCost, replay, score, solve } from './optimality-oracle.mjs';

function closure(start, edges) {
  const seen = new Set([start]), queue = [start];
  for (let index = 0; index < queue.length; index++) for (const next of edges.get(queue[index]) ?? []) {
    if (!seen.has(next)) { seen.add(next); queue.push(next); }
  }
  return seen;
}

export function relaxedGraphBound(problem, boundaryAware = false, deadlineAware = false) {
  const directed = new Map(), weak = new Map(); let mismatches = 0;
  const connect = (graph, from, to) => {
    if (!graph.has(from)) graph.set(from, new Set()); graph.get(from).add(to);
  };
  for (let index = 0; index < problem.source.length; index++) {
    const from = problem.source[index], to = problem.target[index];
    if (from === to) continue;
    mismatches++; connect(directed, from, to); connect(weak, from, to); connect(weak, to, from);
  }
  const terminals = new Set(problem.target.slice(problem.source.length));
  const oldTop = problem.source.at(-1), frozen = problem.source.length - problem.caps.swap - 1;
  const boundaryValue = boundaryAware && problem.missing.length > 0 && frozen >= 0 &&
    problem.source[frozen] !== problem.target[frozen] ? problem.source[frozen] : undefined;
  const visited = new Set(); let detached = 0;
  for (const vertex of weak.keys()) if (!visited.has(vertex)) {
    const component = closure(vertex, weak);
    const firstMismatch = problem.source.findIndex((value, index) =>
      value !== problem.target[index] && component.has(value));
    const timelyBirth = problem.target.some((value, index) => index >= problem.source.length &&
      index <= firstMismatch + problem.caps.swap && component.has(value));
    const needsEntry = deadlineAware ? !timelyBirth :
      ![...component].some(value => terminals.has(value)) || component.has(boundaryValue);
    if (!component.has(oldTop) && needsEntry) detached++;
    for (const value of component) visited.add(value);
  }
  const requestedTop = problem.target[problem.source.length - 1];
  const cycleBonus = problem.source.length > 0 && oldTop !== requestedTop &&
    closure(requestedTop, directed).has(oldTop) ? 1 : 0;
  return mismatches + detached - cycleBonus;
}

export function aggregateTransportBound(problem) {
  let upwardDistance = 0;
  for (const value of new Set(problem.source)) {
    const old = problem.source.flatMap((v, index) => v === value ? [index] : []);
    const target = problem.target.flatMap((v, index) => v === value ? [index] : []);
    for (let i = 0; i < old.length; i++) upwardDistance += Math.max(0, target[i] - old[i]);
  }
  // Round the aggregate, not each matched occurrence separately.
  return Math.ceil(upwardDistance / problem.caps.swap);
}

function introduction(problem, value) {
  if (value === 'wildcard' || value.startsWith('l:')) return score(problem, opCost(problem, ['push', value]));
  if (value.startsWith('v:') && problem.spills.includes(Number(value.slice(2)))) {
    return score(problem, opCost(problem, ['load', Number(value.slice(2))]));
  }
  return Infinity;
}

// These occurrence potentials are experimental; the Lean proof is separate.
export function gapPotential(stack, value, cap) {
  let previous = -1, result = 0;
  for (let index = 0; index < stack.length; index++) if (stack[index] === value) {
    result += previous < 0 ? index : Math.max(0, index - previous - cap);
    previous = index;
  }
  return result;
}

export function gapCount(stack, value, cap) {
  let previous = -1, result = 0;
  for (let index = 0; index < stack.length; index++) if (stack[index] === value) {
    result += previous < 0 ? Math.ceil(index / cap) : Math.floor((index - previous - 1) / cap);
    previous = index;
  }
  return result;
}

export function gapBlocks(problem, value) {
  const first = problem.source.lastIndexOf(value), last = problem.target.lastIndexOf(value);
  let run = 0, blocks = 0;
  for (let i = first + 1; i < last; i++) {
    if (problem.target[i] === value) { blocks += Math.floor(run / problem.caps.swap); run = 0; }
    else run++;
  }
  return blocks + Math.floor(run / problem.caps.swap);
}

export function experimentalLowerBound(problem, boundaryAware = false, deadlineAware = false) {
  const base = baseline(problem), frozen = Math.max(0, problem.source.length - problem.caps.swap - 1);
  const retained = problem.source.slice(frozen);
  let preparation = 0;
  if (problem.missing.length && problem.source.length >= problem.caps.swap + 1) {
    const boundary = problem.target[frozen], occurrence = retained.indexOf(boundary);
    if (occurrence < 0) return { total: Infinity, reason: 'missing boundary' };
    preparation = retained[0] === boundary ? 0 : retained.at(-1) === boundary ? 1 : 2;
    retained.splice(occurrence, 1);
  }
  let generationExtra = 0;
  const duplicate = score(problem, { gas: 3, bytes: 1 });
  for (const value of new Set(problem.missing)) if (problem.source.includes(value) && !retained.includes(value)) {
    const direct = introduction(problem, value);
    generationExtra += direct - Math.min(duplicate, direct);
  }
  const graph = relaxedGraphBound(problem, boundaryAware, deadlineAware), transport = aggregateTransportBound(problem);
  const swaps = Math.max(graph, transport, preparation);
  return { baseline: base, generationExtra, graph, transport, preparation, swaps,
    total: base + generationExtra + duplicate * swaps };
}

export function experimentalLineageBound(problem, boundaryAware = false, deadlineAware = false, gapAware = false, gapCountAware = false) {
  const cap = problem.caps.swap, swapCost = score(problem, { gas: 3, bytes: 1 });
  const frozen = Math.max(0, problem.source.length - cap - 1);
  const retained = problem.source.slice(frozen);
  let preparation = 0;
  if (problem.missing.length && problem.source.length >= cap + 1) {
    const boundary = problem.target[frozen], occurrence = retained.indexOf(boundary);
    if (occurrence < 0) return { total: Infinity, reason: 'missing boundary' };
    preparation = retained[0] === boundary ? 0 : retained.at(-1) === boundary ? 1 : 2;
    retained.splice(occurrence, 1);
  }
  const graph = Math.max(relaxedGraphBound(problem, boundaryAware, deadlineAware), preparation);
  let states = new Map([[0, 0]]);
  const optionsByValue = [];
  for (const value of new Set(problem.source)) {
    const oldPositions = problem.source.flatMap((v, i) => v === value ? [i] : []);
    const targetPositions = problem.target.flatMap((v, i) => v === value ? [i] : []);
    const additions = problem.missing.filter(v => v === value).length;
    let distance = 0;
    for (let i = 0; i < oldPositions.length; i++) distance += Math.max(0, targetPositions[i] - oldPositions[i]);
    const original = Math.ceil(distance / cap);
    const maxPosition = Math.ceil(Math.max(0, targetPositions.at(-1) - oldPositions.at(-1) - cap * additions) / cap);
    const gap = gapAware ? gapBlocks(problem, value) : 0;
    const countedGap = gapCountAware ? Math.max(0, gapCount(problem.target, value, cap) -
      gapCount(problem.source, value, cap)) : 0;
    const lineage = Math.max(maxPosition, gap, countedGap);
    const direct = introduction(problem, value), surcharge = direct - Math.min(swapCost, direct);
    const mandatory = additions > 0 && !retained.includes(value);
    const options = [];
    if (!mandatory) options.push({ swaps: Math.max(original, lineage), regeneration: 0, kind: 'retain' });
    if (additions > 0 && Number.isFinite(direct)) options.push({ swaps: original, regeneration: surcharge, kind: 'regenerate' });
    optionsByValue.push({ value, original, maxPosition, gap, countedGap, lineage, mandatory, options });
    const next = new Map();
    for (const [accumulated, cost] of states) for (const option of options) {
      const total = accumulated + option.swaps, state = Math.min(graph, total);
      const nextCost = cost + option.regeneration + Math.max(0, total - graph) * swapCost;
      next.set(state, Math.min(next.get(state) ?? Infinity, nextCost));
    }
    states = next;
  }
  const extra = Math.min(...states.values()) + graph * swapCost;
  return { baseline: baseline(problem), graph, optionsByValue, extra, total: baseline(problem) + extra };
}

function words(alphabet, length) {
  if (length === 0) return [[]];
  return words(alphabet, length - 1).flatMap(prefix => alphabet.map(value => [...prefix, value]));
}

async function main(args) {
  if (args[0] === '--reports' || args[0] === '--witnesses') {
    const witnessMode = args[0] === '--witnesses';
    let checked = 0, violations = [];
    for (const file of args.slice(1)) for (const line of fs.readFileSync(file, 'utf8').split('\n').filter(Boolean)) {
      const record = JSON.parse(line);
      if (witnessMode ? !record.problem.referenceOps : record.oracle.status !== 'optimal') continue;
      const upper = witnessMode ? replay(record.problem, record.problem.referenceOps).score : record.oracle.score;
      const bound = experimentalLowerBound(record.problem), lineage = experimentalLineageBound(record.problem);
      const boundary = experimentalLowerBound(record.problem, true), lineageBoundary = experimentalLineageBound(record.problem, true); checked++;
      const deadline = experimentalLowerBound(record.problem, false, true), lineageDeadline = experimentalLineageBound(record.problem, false, true);
      const gap = experimentalLineageBound(record.problem, false, true, true);
      const countedGap = experimentalLineageBound(record.problem, false, true, false, true);
      if (Math.max(bound.total, lineage.total, boundary.total, lineageBoundary.total, deadline.total, lineageDeadline.total, gap.total, countedGap.total) > upper) {
        violations.push({ id: record.problem.id, bound, lineage, boundary, lineageBoundary, deadline, lineageDeadline, gap, countedGap, upper, source: witnessMode ? 'supplied witness' : 'exact oracle' });
      }
    }
    console.log(JSON.stringify({ mode: witnessMode ? 'witnesses' : 'oracle', checked, violations }, null, 2));
    return;
  }
  const outputIndex = args.indexOf('--output');
  const outputPath = outputIndex < 0 ? null : args[outputIndex + 1];
  const output = outputPath ? fs.openSync(outputPath, 'w') : null;
  const save = record => { if (output !== null) fs.writeSync(output, JSON.stringify(record) + '\n'); };
  const alphabet = ['l:0', 'v:42', 'v:43'];
  let checked = 0, states = 0, infeasible = 0;
  for (let size = 0; size <= 3; size++) for (let final = size; final <= 4; final++) {
    for (const source of words(alphabet, size)) for (const target of words(alphabet, final)) {
      for (const spills of [[], [42, 43]]) for (const [gas, bytes] of [[1, 0], [0, 1], [1, 1], [6, 1]]) {
        const problem = normalizeCase({ source, target, spills, weights: { gas, bytes },
          caps: { swap: 2, dup: 2 }, loadWidths: spills.map(id => [id, 2]) });
        const oracle = solve(problem, { stateLimit: 10000 }); states += oracle.states;
        if (oracle.status === 'infeasible') { save({ problem, oracle }); infeasible++; continue; }
        if (oracle.status !== 'optimal') throw new Error('unexpected oracle limit');
        const bound = experimentalLowerBound(problem), lineage = experimentalLineageBound(problem);
        const boundary = experimentalLowerBound(problem, true), lineageBoundary = experimentalLineageBound(problem, true); checked++;
        const deadline = experimentalLowerBound(problem, false, true), lineageDeadline = experimentalLineageBound(problem, false, true);
        const gap = experimentalLineageBound(problem, false, true, true);
        const countedGap = experimentalLineageBound(problem, false, true, false, true);
        save({ problem, oracle, bound, lineage, boundary, lineageBoundary, deadline, lineageDeadline, gap, countedGap });
        if (Math.max(bound.total, lineage.total, boundary.total, lineageBoundary.total, deadline.total, lineageDeadline.total, gap.total, countedGap.total) > oracle.score) {
          console.log(JSON.stringify({ checked, problem, bound, lineage, boundary, lineageBoundary, deadline, lineageDeadline, gap, countedGap, oracle }, null, 2));
          process.exitCode = 1; return;
        }
      }
    }
  }
  if (output !== null) fs.closeSync(output);
  console.log(JSON.stringify({ model: 'reduced-cap-2', checked, infeasible, states, violations: 0,
    output: outputPath, configuration: { alphabet, sourceLengths: [0, 1, 2, 3],
      targetLengths: 'source.length through 4', spills: [[], [42, 43]],
      weights: [[1, 0], [0, 1], [1, 1], [6, 1]], loadWidth: 2, stateLimit: 10000 } }, null, 2));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  main(process.argv.slice(2)).catch(error => { console.error(error.stack); process.exitCode = 1; });
}
