#!/usr/bin/env node
/** Exact offline plan DAG. The number of states prevents production use. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { baseline, normalizeCase, opCost, score } from './optimality-oracle.mjs';
import { realizeAssignment } from './optimality-assignment-realizer.mjs';
import { exactObjective, retentionEntries } from './optimality-quota-lp-objectives.mjs';

const directOp = (problem, value) => value === 'wildcard' || value.startsWith('l:') ? ['push', value] :
  value.startsWith('v:') && problem.spills.includes(Number(value.slice(2))) ? ['load', Number(value.slice(2))] : null;

export function frontierPlan(problem, { stateLimit = 100000 } = {}) {
  assert.equal(problem.source.length, 0, 'frontier plan requires empty source');
  const size = problem.target.length, reach = problem.caps.swap;
  const swapPrice = score(problem, opCost(problem, ['swap', 1]));
  const direct = new Map([...new Set(problem.target)].map(value => {
    const op = directOp(problem, value);
    return [value, op ? { kind: op[0], price: score(problem, opCost(problem, op)) } : null];
  }));
  const initial = { frontier: [], objective: 0, generationCost: 0, E: 0, parent: null };
  let layer = new Map([['', initial]]), states = 1, edges = 0;
  for (let birth = 0; birth < size; birth++) {
    const nextLayer = new Map(), due = birth - reach;
    for (const current of layer.values()) {
      assert.equal(current.frontier.length, Math.min(birth, reach));
      const occupied = new Set(current.frontier);
      const outputs = due >= 0 && !occupied.has(due) ? [due] :
        Array.from({ length: size - Math.max(0, due) }, (_, index) => index + Math.max(0, due)).filter(output => !occupied.has(output));
      for (const output of outputs) {
        const value = problem.target[output], introduction = direct.get(value);
        const canDuplicate = current.frontier.some(index => problem.target[index] === value);
        const choice = canDuplicate && swapPrice < (introduction?.price ?? Infinity) ? { kind: 'dup', price: swapPrice } : introduction;
        if (choice === null) continue;
        const frontier = [...current.frontier, output].filter(index => index !== due).sort((a, b) => a - b);
        assert.equal(frontier.length, Math.min(birth + 1, reach));
        const E = current.E + Number(output !== birth), generationCost = current.generationCost + choice.price;
        const record = { frontier, objective: 2 * generationCost + swapPrice * E, generationCost, E,
          parent: current, output, birth: { value, kind: choice.kind } };
        const key = frontier.join(','); edges++;
        if (record.objective < (nextLayer.get(key)?.objective ?? Infinity)) {
          if (!nextLayer.has(key)) {
            states++;
            if (states > stateLimit) return { status: 'limit', states, edges, stateLimit };
          }
          nextLayer.set(key, record);
        }
      }
    }
    layer = nextLayer;
    if (!layer.size) return { status: 'infeasible', states, edges };
  }
  assert.equal(layer.size, 1, 'terminal frontier is not unique');
  const final = [...layer.values()][0], assignment = [], births = [], frontiers = [];
  let current = final;
  while (current.parent !== null) {
    assignment.push(current.output); births.push(current.birth); frontiers.push(current.parent.frontier);
    current = current.parent;
  }
  assignment.reverse(); births.reverse(); frontiers.reverse();
  assert.equal(new Set(assignment).size, size);
  assert.ok(assignment.every((output, birth) => birth <= output + reach));
  return { status: 'optimal', objective: final.objective, generationCost: final.generationCost, E: final.E,
    assignment, births, frontiers, states, edges };
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-frontier-dag.json';
  const fixtures = [
    { name: 'empty', target: [], reach: 1 },
    { name: 'one-copy', target: ['v:42'], reach: 1 },
    { name: 'adjacent-repeat', target: ['v:42', 'v:42', 'v:42'], reach: 1 },
    { name: 'one-prefetch', target: ['v:42', 'v:43', 'v:42'], reach: 1 },
    { name: 'two-prefetches', target: ['v:43', 'v:44', 'v:42', 'v:42', 'v:42', 'v:42', 'v:43', 'v:44'], reach: 3 },
    { name: 'push0-between-copies', target: ['v:42', 'l:0', 'l:0', 'v:42'], reach: 1 },
    { name: 'mixed-widths', target: ['v:42', 'v:43', 'v:42', 'v:44', 'v:43', 'v:44'], reach: 2 }
  ];
  const records = [], failures = [];
  for (const fixture of fixtures) for (const weights of [{ gas: 0, bytes: 1 }, { gas: 1, bytes: 0 }]) {
    const problem = normalizeCase({ source: [], target: fixture.target, spills: [42, 43, 44],
      loadWidths: [[42, 32], [43, 0], [44, 2]], gasModel: 'evm', weights,
      caps: { swap: fixture.reach, dup: fixture.reach } });
    try {
      const actual = frontierPlan(problem), swapPrice = score(problem, opCost(problem, ['swap', 1]));
      assert.equal(actual.status, 'optimal');
      const premiums = Object.fromEntries([...new Set(problem.target)].map(value => {
        const op = directOp(problem, value);
        return [value, Math.max(0, score(problem, opCost(problem, op)) - swapPrice)];
      }));
      const retention = retentionEntries(problem.target, premiums);
      const exact = exactObjective(problem.target, fixture.reach, [], { retention, swapPrice });
      assert.equal(actual.objective - 2 * baseline(problem), exact.objective, 'DAG and exact plan objectives differ');
      const realization = realizeAssignment(problem, actual.births, actual.assignment);
      assert.equal(realization.E, actual.E);
      assert.equal(realization.score - swapPrice * realization.swaps, actual.generationCost);
      records.push({ name: fixture.name, problem, actual, exact, realization });
    } catch (error) { failures.push({ name: fixture.name, problem, error: error.message }); }
  }
  const report = {
    status: 'exact offline frontier-DAG specification with small independent checks; no production integration',
    objective: 'Minimize 2*generationCost + swapPrice*E over empty-source lag-valid plans. E counts moved token positions. This is a plan objective, not an exact SWAP objective.',
    state: 'Before birth b, all target slots below max(b-R,0) are already assigned. The frontier S contains the other assigned target slots and has size min(b,R). A DUP of v is available exactly when some index in S has target value v.',
    transition: 'Choose an unassigned target index j>=b-R. If b>=R, the index b-R must belong to S union {j}; then remove it from that union to get the next frontier. Charge the cheapest legal birth of target[j] and the movement indicator j!=b.',
    scope: 'Only 14 named small fixtures are checked against exhaustive endpoint-permutation optimization, with independent realizer replay. The state count grows as a degree-R+1 polynomial when R is fixed and as 2^n when R>=n. This is not suitable for production at R=16.',
    cases: records.length, failures, records,
    reproduce: `node scripts/optimality-frontier-dag.mjs ${output}`
  };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({ cases: records.length, states: records.reduce((sum, record) => sum + record.actual.states, 0), failures }));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
