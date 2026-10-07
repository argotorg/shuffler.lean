#!/usr/bin/env node
/** Offline mixed-weight fixtures with exact gas/byte frontiers. */
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { normalizeCase, score, solvePareto } from './optimality-oracle.mjs';

const gcd = (a, b) => b === 0 ? a : gcd(b, a % b);

export function frontierWeights(frontier) {
  const weights = new Map();
  const add = (gas, bytes) => {
    const divisor = gcd(gas, bytes);
    if (divisor === 0) return;
    gas /= divisor; bytes /= divisor;
    weights.set(`${gas}:${bytes}`, { gas, bytes });
  };
  add(0, 1); add(1, 0); add(1, 1);
  for (const first of frontier) for (const second of frontier) {
    const gas = first.cost.bytes - second.cost.bytes;
    const bytes = second.cost.gas - first.cost.gas;
    if (gas <= 0 || bytes <= 0) continue;
    const tied = first.cost.gas * gas + first.cost.bytes * bytes;
    if (frontier.some(point => point.cost.gas * gas + point.cost.bytes * bytes < tied)) continue;
    add(gas, bytes);
    add(Math.floor(gas / bytes), 1);
    add(Math.ceil(gas / bytes), 1);
  }
  return [...weights.values()].sort((a, b) => a.bytes === 0 ? 1 : b.bytes === 0 ? -1 :
    a.gas * b.bytes - b.gas * a.bytes);
}

export function mixedParetoCases() {
  const wide = `l:${1n << 248n}`, load = 'v:42', zero = 'l:0';
  const patterns = [
    ...[2, 3, 8].flatMap(count => [[wide, load], [load, wide]].map(pair =>
      Array.from({ length: count }, () => pair).flat())),
    [wide, load, load, wide], [load, wide, wide, load],
  ];
  return patterns.flatMap((pattern, index) => [0, 2].map(width => normalizeCase({
    id: `mixed-pareto-pattern${index}-width${width}`,
    source: Array(15).fill(zero), target: [...pattern, ...Array(15).fill(zero)],
    spills: [42], loadWidths: [[42, width]], gasModel: 'cpp',
  })));
}

function main() {
  const output = process.argv[2] ?? 'Bench/mixed-pareto.jsonl';
  const evidenceOutput = process.argv[3] ?? 'Bench/evidence-mixed-pareto-frontiers.json';
  const frontiers = mixedParetoCases().map(problem => {
    const oracle = solvePareto(problem, { stateLimit: 100000, labelLimit: 500000 });
    if (oracle.status !== 'optimal') throw new Error(`${problem.id}: ${oracle.status}`);
    return { problem, oracle };
  });
  const cases = frontiers.flatMap(({ problem, oracle }) => frontierWeights(oracle.frontier).map(weights => {
    const weighted = normalizeCase({ ...problem, weights, id: `${problem.id}/g${weights.gas}b${weights.bytes}` });
    const best = oracle.frontier.reduce((best, point) => score(weighted, point.cost) < score(weighted, best.cost) ? point : best);
    return { ...weighted, referenceOps: best.ops, expectedOracleScore: score(weighted, best.cost) };
  }));
  fs.writeFileSync(output, cases.map(problem => JSON.stringify(problem)).join('\n') + '\n');
  fs.writeFileSync(evidenceOutput, JSON.stringify({
    scope: 'Exact offline Pareto frontiers for these fixed actual-cap inputs. No general approximation theorem is claimed.',
    reproduce: `node scripts/optimality-mixed-pareto.mjs ${output} ${evidenceOutput}`,
    baseCases: frontiers.length, weightedCases: cases.length,
    states: frontiers.reduce((sum, record) => sum + record.oracle.states, 0),
    frontiers,
  }, null, 2) + '\n');
  console.log(JSON.stringify({ output, evidenceOutput, baseCases: frontiers.length, weightedCases: cases.length }));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
