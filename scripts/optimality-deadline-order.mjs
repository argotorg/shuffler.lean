#!/usr/bin/env node
/** Offline check of a deadline normal form; no stack planner imports it. */
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';

export function lexicographicDeadlineOrder(deadlines) {
  if (deadlines.some(due => !Number.isInteger(due) || due < 1)) return null;
  let remaining = deadlines.map((_, index) => index);
  const order = [];
  while (remaining.length) {
    const slot = order.length + 1;
    const cuts = [...new Set(remaining.map(index => deadlines[index]))].sort((a, b) => a - b);
    let tight = Infinity;
    for (const cut of cuts) {
      const count = remaining.filter(index => deadlines[index] <= cut).length;
      if (count > cut - slot + 1) return null;
      if (count === cut - slot + 1 && tight === Infinity) tight = cut;
    }
    const next = remaining.find(index => deadlines[index] <= tight);
    if (next === undefined) throw new Error('a feasible deadline set has no next job');
    order.push(next); remaining = remaining.filter(index => index !== next);
  }
  return order;
}

export function exhaustiveDeadlineOrders(deadlines) {
  const visit = (prefix, remaining) => {
    if (!remaining.length) return [prefix];
    return remaining.flatMap(index => deadlines[index] >= prefix.length + 1 ?
      visit([...prefix, index], remaining.filter(other => other !== index)) : []);
  };
  return visit([], deadlines.map((_, index) => index));
}

export function checkDeadlineRule(maximumSize) {
  const words = (length, limit) => length === 0 ? [[]] : words(length - 1, limit)
    .flatMap(prefix => Array.from({ length: limit }, (_, index) => [...prefix, index + 1]));
  let instances = 0, feasible = 0, feasibleOrders = 0, first = null;
  outer: for (let size = 0; size <= maximumSize; size++) for (const deadlines of words(size, size + 1)) {
    const all = exhaustiveDeadlineOrders(deadlines), actual = lexicographicDeadlineOrder(deadlines);
    instances++; feasibleOrders += all.length; if (all.length) feasible++;
    if (JSON.stringify(actual) !== JSON.stringify(all[0] ?? null)) { first = { deadlines, actual, expected: all[0] ?? null }; break outer; }
  }
  return { instances, feasible, feasibleOrders, first };
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-deadline-order.json';
  const report = { status: 'finite exhaustive combinatorial evidence, not a Lean theorem',
    domain: { jobs: '0 through5', deadlines: '1 through job count plus1', slots: '1-based', indices: '0-based' },
    rule: 'At each slot, choose the least remaining target index whose deadline is at most the earliest tight deadline cut. If no cut is tight, choose the least remaining target index.',
    ...checkDeadlineRule(5), reproduce: `node scripts/optimality-deadline-order.mjs ${output}` };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n'); console.log(JSON.stringify(report));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
