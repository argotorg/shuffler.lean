#!/usr/bin/env node
/** Exact small checks for one priced assignment subproblem, not a joint optimizer. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { checkJointCertificate } from './optimality-joint-dual.mjs';

const natural = value => {
  assert.ok(Number.isSafeInteger(value) || typeof value === 'string' && /^\d+$/.test(value));
  const result = BigInt(value); assert.ok(result >= 0n); return result;
};

function prepare({ target, source = [], reach, swap, gaps }) {
  assert.ok(Number.isSafeInteger(reach) && reach >= 1);
  assert.ok(source.length <= target.length);
  const prices = gaps.map(gap => {
    assert.ok(Number.isSafeInteger(gap.left) && gap.left >= 0 && gap.left < target.length);
    return { value: target[gap.left], cut: gap.left + reach, weight: natural(gap.weight) };
  });
  assert.equal(new Set(gaps.map(gap => gap.left)).size, gaps.length, 'duplicate priced deadline');
  return { target, source, reach, swap: natural(swap), prices };
}

const allowed = (problem, birth, output) => birth <= output + problem.reach &&
  (birth >= problem.source.length || problem.source[birth] === problem.target[output]) &&
  (birth + problem.reach + 1 >= problem.source.length || birth === output);
const price = (problem, value, time) => problem.prices.reduce((sum, gap) =>
  sum + (gap.value === value && time <= gap.cut ? gap.weight : 0n), 0n);
const reward = (problem, assignment) => assignment.reduce((sum, output, birth) =>
  sum + price(problem, problem.target[output], birth) + (birth === output ? problem.swap : 0n), 0n);

function network(problem) {
  const { target, source, reach } = problem, size = target.length;
  const internalCapacity = reach + 2;
  const names = [], byName = new Map(), arcs = [], byArc = new Map();
  const node = name => { if (!byName.has(name)) { byName.set(name, names.length); names.push(name); } return byName.get(name); };
  const add = (name, from, to, capacity, cost, kind, timeFrom, timeTo) => {
    assert.ok(!byArc.has(name)); byArc.set(name, arcs.length);
    arcs.push({ from: node(from), to: node(to), capacity, cost, kind, timeFrom, timeTo });
  };
  const events = new Map([...new Set(target)].map(value => [value,
    target.flatMap((item, index) => item === value ? [index] : [])]));
  const times = [...new Set(target.flatMap((_, index) => [index, index + reach]))].sort((a, b) => a - b);
  node('s'); node('t');
  for (let birth = 0; birth < size; birth++) {
    add(`s:${birth}`, 's', `b:${birth}`, 1, 0n, 'supply');
    if (allowed(problem, birth, birth)) add(`identity:${birth}`, `b:${birth}`, `o:${birth}`, internalCapacity,
      -problem.swap - price(problem, target[birth], birth), 'identity', birth, birth + reach);
    if (birth + reach + 1 < source.length) continue;
    if (birth < source.length) {
      const first = (events.get(source[birth]) ?? []).find(index => birth <= index + reach);
      if (first !== undefined) add(`birth:${birth}`, `b:${birth}`, `e:${first}`, internalCapacity,
        -price(problem, source[birth], birth), 'source-entry', birth, first + reach);
    } else add(`birth:${birth}`, `b:${birth}`, `g:${birth}`, internalCapacity, 0n, 'birth-entry', birth, birth);
  }
  times.slice(0, -1).forEach((time, index) => add(`global:${time}`, `g:${time}`, `g:${times[index + 1]}`,
    internalCapacity, 0n, 'global', time, times[index + 1]));
  for (let output = 0; output < size; output++) {
    const deadline = output + reach;
    add(`entry:${output}`, `g:${deadline}`, `e:${output}`, internalCapacity,
      -price(problem, target[output], deadline), 'entry', deadline, deadline);
    add(`exit:${output}`, `e:${output}`, `o:${output}`, internalCapacity, 0n, 'exit', deadline, deadline);
    add(`t:${output}`, `o:${output}`, 't', 1, 0n, 'demand');
  }
  for (const indices of events.values()) indices.slice(0, -1).forEach((output, index) =>
    add(`chain:${output}`, `e:${output}`, `e:${indices[index + 1]}`, internalCapacity, 0n,
      'chain', output + reach, indices[index + 1] + reach));
  return { names, byName, arcs, byArc, events, times };
}

// Bellman-Ford is used only for these small exact checks. This is not the
// potential-based Dijkstra implementation used in the paper-level runtime.
function minCostFlow(graph, amount) {
  const edges = graph.arcs.flatMap((arc, index) => [
    { ...arc, residual: arc.capacity, reverse: 2 * index + 1 },
    { from: arc.to, to: arc.from, residual: 0, cost: -arc.cost, reverse: 2 * index }
  ]);
  let flow = 0, cost = 0n;
  while (flow < amount) {
    const distance = Array(graph.names.length).fill(null), previous = Array(graph.names.length).fill(-1);
    distance[graph.byName.get('s')] = 0n;
    for (let pass = 0; pass < graph.names.length - 1; pass++) {
      let changed = false;
      edges.forEach((edge, index) => {
        if (!edge.residual || distance[edge.from] === null) return;
        const next = distance[edge.from] + edge.cost;
        if (distance[edge.to] === null || next < distance[edge.to]) {
          distance[edge.to] = next; previous[edge.to] = index; changed = true;
        }
      });
      if (!changed) break;
    }
    const sink = graph.byName.get('t');
    if (distance[sink] === null) break;
    let at = sink, steps = 0;
    while (at !== graph.byName.get('s')) {
      assert.ok(++steps <= graph.names.length, 'residual predecessor cycle');
      const edge = edges[previous[at]];
      assert.ok(edge && edge.residual > 0);
      edge.residual--; edges[edge.reverse].residual++; at = edge.from;
    }
    flow++; cost += distance[sink];
  }
  // A zero-cost super-source to all nodes gives residual dual potentials.
  const potential = graph.names.map(() => 0n);
  for (let pass = 0; pass < graph.names.length; pass++) {
    let changed = false;
    for (const edge of edges) if (edge.residual && potential[edge.to] > potential[edge.from] + edge.cost) {
      potential[edge.to] = potential[edge.from] + edge.cost; changed = true;
    }
    if (!changed) break;
    assert.ok(pass + 1 < graph.names.length, 'negative residual cycle');
  }
  return { flow, cost, potential, used: graph.arcs.map((arc, index) => arc.capacity - edges[2 * index].residual) };
}

export function pricedAssignment(input) {
  const problem = prepare(input), graph = network(problem), result = minCostFlow(graph, problem.target.length);
  if (result.flow !== problem.target.length) return { status: 'infeasible', vertices: graph.names.length, arcs: graph.arcs.length };
  const remaining = [...result.used], assignment = [];
  for (let birth = 0; birth < problem.target.length; birth++) {
    let at = graph.byName.get(`b:${birth}`), steps = 0;
    while (!graph.names[at].startsWith('o:')) {
      assert.ok(++steps <= graph.names.length, 'flow decomposition cycle');
      const index = graph.arcs.findIndex((arc, index) => arc.from === at && remaining[index] > 0);
      assert.ok(index >= 0, 'incomplete flow path');
      remaining[index]--; at = graph.arcs[index].to;
    }
    assignment.push(Number(graph.names[at].slice(2)));
  }
  assert.equal(new Set(assignment).size, problem.target.length);
  assert.ok(assignment.every((output, birth) => allowed(problem, birth, output)));
  assert.equal(reward(problem, assignment), -result.cost, 'decoded edge reward differs from optimum flow reward');
  const row = problem.target.map((_, birth) => result.potential[graph.byName.get(`b:${birth}`)]);
  const column = problem.target.map((_, output) => -result.potential[graph.byName.get(`o:${output}`)]);
  for (let birth = 0; birth < problem.target.length; birth++) for (let output = 0; output < problem.target.length; output++) {
    if (!allowed(problem, birth, output)) continue;
    assert.ok(row[birth] + column[output] >= price(problem, problem.target[output], birth) +
      (birth === output ? problem.swap : 0n), 'assignment dual edge inequality fails');
  }
  assert.equal([...row, ...column].reduce((sum, value) => sum + value, 0n), -result.cost, 'assignment dual is not tight');
  return { status: 'optimal', reward: String(-result.cost), assignment,
    row: row.map(String), column: column.map(String),
    vertices: graph.names.length, arcs: graph.arcs.length };
}

export function canonicalRouteLoads(input, assignment) {
  const problem = prepare(input), graph = network(problem), loads = graph.arcs.map(() => 0);
  assert.equal(assignment.length, problem.target.length);
  assert.equal(new Set(assignment).size, problem.target.length);
  const use = name => { const index = graph.byArc.get(name); assert.notEqual(index, undefined, name); loads[index]++; };
  assignment.forEach((output, birth) => {
    assert.ok(output >= 0 && output < assignment.length && allowed(problem, birth, output));
    use(`s:${birth}`); use(`t:${output}`);
    if (birth === output) { use(`identity:${birth}`); return; }
    use(`birth:${birth}`);
    const indices = graph.events.get(problem.target[output]);
    const first = indices.find(index => birth <= index + problem.reach);
    assert.notEqual(first, undefined);
    if (birth >= problem.source.length) {
      for (const time of graph.times) if (birth <= time && time < first + problem.reach) use(`global:${time}`);
      use(`entry:${first}`);
    }
    for (const index of indices) if (first <= index && index < output) use(`chain:${index}`);
    use(`exit:${output}`);
  });
  graph.arcs.forEach((arc, index) => assert.ok(loads[index] <= arc.capacity, 'canonical path exceeds capacity'));
  graph.arcs.forEach((arc, index) => {
    if (arc.timeFrom < arc.timeTo) assert.ok(loads[index] <= problem.reach, 'positive-time load exceeds R');
    else if (arc.timeFrom !== undefined) assert.ok(loads[index] <= problem.reach + 1, 'same-time load exceeds R+1');
  });
  const flowCost = graph.arcs.reduce((sum, arc, index) => sum + arc.cost * BigInt(loads[index]), 0n);
  assert.equal(-flowCost, reward(problem, assignment));
  return { maximumEntryLoad: Math.max(0, ...graph.arcs.flatMap((arc, index) => arc.kind === 'entry' ? [loads[index]] : [])),
    maximumPositiveTimeLoad: Math.max(0, ...graph.arcs.flatMap((arc, index) => arc.timeFrom < arc.timeTo ? [loads[index]] : [])) };
}

function* permutations(values, prefix = []) {
  if (!values.length) { yield prefix; return; }
  for (const value of values) yield* permutations(values.filter(other => other !== value), [...prefix, value]);
}

export function checkPricedFixtures() {
  const fixtures = [
    { name: 'empty', target: [], reach: 16, swap: 3, gaps: [] },
    { name: 'last-occurrence-entry', source: ['b'], target: ['a', 'b'], reach: 1, swap: 3, gaps: [] },
    { name: 'several-value-prices', target: ['a', 'b', 'c', 'a', 'b', 'a'], reach: 2, swap: 3,
      gaps: [{ left: 0, weight: 9 }, { left: 1, weight: 2 }, { left: 3, weight: 5 }] },
    { name: 'zero-swap-price', target: ['a', 'b', 'a', 'b'], reach: 1, swap: 0,
      gaps: [{ left: 0, weight: 7 }, { left: 1, weight: 1 }] },
    { name: 'source-fixed-value', source: ['b', 'a'], target: ['a', 'b', 'a', 'b'], reach: 1, swap: 2,
      gaps: [{ left: 0, weight: 4 }, { left: 1, weight: 6 }] },
    { name: 'frozen-source', source: ['a', 'b', 'a', 'b'], target: ['a', 'b', 'b', 'a', 'a'], reach: 1, swap: 3,
      gaps: [{ left: 0, weight: 1 }, { left: 1, weight: 8 }] },
    { name: 'frozen-conflict', source: ['b', 'a', 'a'], target: ['a', 'b', 'a'], reach: 1, swap: 3, gaps: [] }
  ];
  return fixtures.map(fixture => {
    const problem = prepare(fixture), flow = pricedAssignment(fixture);
    let best = null, feasible = 0, checked = 0;
    for (const assignment of permutations(fixture.target.map((_, index) => index))) {
      checked++;
      if (!assignment.every((output, birth) => allowed(problem, birth, output))) continue;
      feasible++; canonicalRouteLoads(fixture, assignment);
      const value = reward(problem, assignment);
      if (best === null || best < value) best = value;
    }
    assert.equal(flow.status, best === null ? 'infeasible' : 'optimal');
    if (best !== null) assert.equal(flow.reward, String(best));
    return { fixture, permutations: checked, feasibleAssignments: feasible, exactReward: best === null ? null : String(best), flow, equal: true };
  });
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-priced-assignment.json', records = checkPricedFixtures();
  const entryBoundary = canonicalRouteLoads({ target: ['a', 'a', 'a'], reach: 1, swap: 0, gaps: [] }, [1, 0, 2]);
  const savedPrices = ['Bench/evidence-periodic-joint-dual.json', 'Bench/evidence-source-joint-dual.json'].map(path => {
    const saved = JSON.parse(fs.readFileSync(path, 'utf8')), instance = saved.instance, certificate = saved.solved.certificate;
    const priced = pricedAssignment({ target: instance.target, source: instance.source ?? [], reach: instance.reach,
      swap: String(BigInt(instance.prices.swap) * BigInt(certificate.scale)),
      gaps: saved.checked.gaps.map((gap, index) => ({ left: gap.start, weight: certificate.prefix[index] })) });
    assert.equal(priced.status, 'optimal');
    const checked = checkJointCertificate({ ...instance, certificate: { ...certificate, row: priced.row, column: priced.column } });
    assert.ok(BigInt(saved.checked.lowerBoundNumerator) <= BigInt(checked.lowerBoundNumerator));
    return { source: path, vertices: priced.vertices, arcs: priced.arcs, rowColumnSum: priced.reward,
      previousLowerNumerator: saved.checked.lowerBoundNumerator, lowerNumerator: checked.lowerBoundNumerator,
      scale: checked.scale };
  });
  const report = { status: 'finite exact comparison of a sparse priced-assignment flow and independent permutation enumeration',
    scope: 'Seven small named cases and two saved price vectors. No production solver, scheduler change, broad random search, outer multiplier algorithm, LP rounding theorem, or Lean proof is claimed.',
    method: 'BigInt successive shortest paths with Bellman-Ford; this small-check implementation does not claim the research note runtime.',
    cases: records.length, assignments: records.reduce((sum, record) => sum + record.permutations, 0),
    feasibleAssignments: records.reduce((sum, record) => sum + record.feasibleAssignments, 0),
    records, entryBoundary, savedPrices, reproduce: `node scripts/optimality-priced-assignment.mjs ${output}` };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({ cases: report.cases, assignments: report.assignments, feasibleAssignments: report.feasibleAssignments, entryBoundary }));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
