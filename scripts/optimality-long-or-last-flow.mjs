#!/usr/bin/env node
/** Exact offline checks of the long-or-last joint flow construction. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { consecutiveIntervals } from './optimality-interval-realizability.mjs';
import { checkJointCertificate } from './optimality-joint-dual.mjs';

const natural = value => {
  assert.ok(Number.isSafeInteger(value) || typeof value === 'string' && /^\d+$/.test(value));
  const result = BigInt(value); assert.ok(result >= 0n); return result;
};
const sum = items => items.reduce((total, item) => total + item, 0n);

function prepare(input) {
  const { target, reach, prices } = input;
  assert.ok(Number.isSafeInteger(reach) && reach >= 1);
  assert.ok(!input.source?.length, 'the joint flow construction assumes an empty source');
  const direct = new Map(prices.direct.map(([value, price]) => [value, natural(price)]));
  assert.equal(direct.size, prices.direct.length);
  assert.ok(target.every(value => direct.has(value)));
  const dup = natural(prices.dup), swap = natural(prices.swap);
  const gaps = consecutiveIntervals(target).map(gap => {
    const premium = direct.get(gap.value) - dup;
    const reward = 2n * (premium > 0n ? premium : 0n);
    const linear = !target.slice(gap.end + 1).includes(gap.value);
    assert.ok(reward === 0n || linear || gap.end - gap.start > reach,
      'a positive gap is neither long nor last');
    return { ...gap, reward, linear, cut: gap.start + reach,
      base: target.slice(0, gap.start + 1).filter(value => value === gap.value).length };
  });
  return { target, reach, direct, dup, swap, gaps };
}
const linearPrice = (problem, value, time) => sum(problem.gaps.flatMap(gap =>
  gap.linear && gap.value === value && time <= gap.cut ? [gap.reward] : []));
const reward = (problem, assignment) => problem.swap * BigInt(assignment.filter((j, b) => b === j).length) +
  sum(problem.gaps.flatMap(gap => assignment.filter((j, b) => b <= gap.cut && problem.target[j] === gap.value).length > gap.base
    ? [gap.reward] : []));

function network(problem) {
  const { target, reach } = problem, capacity = reach + 2;
  const names = [], byName = new Map(), arcs = [], byArc = new Map();
  const node = name => { if (!byName.has(name)) { byName.set(name, names.length); names.push(name); } return byName.get(name); };
  const add = (name, from, to, bound, cost) => {
    assert.ok(!byArc.has(name)); byArc.set(name, arcs.length);
    arcs.push({ from: node(from), to: node(to), capacity: bound, cost });
  };
  const events = new Map([...new Set(target)].map(value => [value,
    target.flatMap((item, index) => item === value ? [index] : [])]));
  const times = [...new Set(target.flatMap((_, index) => [index, index + reach]))].sort((a, b) => a - b);
  node('s'); node('t');
  target.forEach((value, birth) => {
    add(`s:${birth}`, 's', `b:${birth}`, 1, 0n);
    add(`identity:${birth}`, `b:${birth}`, `o:${birth}`, capacity, -problem.swap - linearPrice(problem, value, birth));
    add(`birth:${birth}`, `b:${birth}`, `g:${birth}`, capacity, 0n);
  });
  times.slice(0, -1).forEach((time, index) => add(`global:${time}`, `g:${time}`, `g:${times[index + 1]}`, capacity, 0n));
  target.forEach((value, output) => {
    add(`entry:${output}`, `g:${output + reach}`, `e:${output}`, capacity, -linearPrice(problem, value, output + reach));
    add(`exit:${output}`, `e:${output}`, `o:${output}`, capacity, 0n);
    add(`t:${output}`, `o:${output}`, 't', 1, 0n);
  });
  for (const gap of problem.gaps) {
    add(`chain:${gap.start}`, `e:${gap.start}`, `e:${gap.end}`, capacity, 0n);
    if (!gap.linear && gap.reward > 0n)
      add(`reward:${gap.start}`, `e:${gap.start}`, `e:${gap.end}`, 1, -gap.reward);
  }
  return { names, byName, arcs, byArc, events, times };
}

// This small-check implementation uses Bellman-Ford. It is not a production
// solver and does not claim the sparse Dijkstra arithmetic-operation bound.
function minCostFlow(graph, amount) {
  const edges = graph.arcs.flatMap((arc, index) => [
    { ...arc, residual: arc.capacity, reverse: 2 * index + 1 },
    { from: arc.to, to: arc.from, residual: 0, cost: -arc.cost, reverse: 2 * index }
  ]);
  let flow = 0, cost = 0n;
  while (flow < amount) {
    const distance = graph.names.map(() => null), previous = graph.names.map(() => -1);
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
    let at = graph.byName.get('t'), steps = 0;
    assert.notEqual(distance[at], null, 'identity is a feasible complete flow');
    cost += distance[at];
    while (at !== graph.byName.get('s')) {
      assert.ok(++steps <= graph.names.length);
      const edge = edges[previous[at]];
      assert.ok(edge && edge.residual > 0);
      edge.residual--; edges[edge.reverse].residual++; at = edge.from;
    }
    flow++;
  }
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

function canonicalRoute(problem, graph, assignment) {
  const loads = graph.arcs.map(() => 0);
  const use = name => { const index = graph.byArc.get(name); assert.notEqual(index, undefined); loads[index]++; };
  assignment.forEach((output, birth) => {
    use(`s:${birth}`); use(`t:${output}`);
    if (birth === output) { use(`identity:${birth}`); return; }
    use(`birth:${birth}`);
    const events = graph.events.get(problem.target[output]), first = events.find(index => birth <= index + problem.reach);
    assert.notEqual(first, undefined);
    for (const time of graph.times) if (birth <= time && time < first + problem.reach) use(`global:${time}`);
    use(`entry:${first}`);
    for (const index of events) if (first <= index && index < output) use(`chain:${index}`);
    use(`exit:${output}`);
  });
  for (const gap of problem.gaps) if (!gap.linear && gap.reward > 0n) {
    const bulk = graph.byArc.get(`chain:${gap.start}`);
    if (loads[bulk]) { loads[bulk]--; loads[graph.byArc.get(`reward:${gap.start}`)]++; }
  }
  graph.arcs.forEach((arc, index) => assert.ok(loads[index] <= arc.capacity));
  const flowReward = -sum(graph.arcs.map((arc, index) => arc.cost * BigInt(loads[index])));
  const constant = sum(problem.gaps.flatMap(gap => gap.linear ? [BigInt(gap.base) * gap.reward] : []));
  assert.equal(flowReward - constant, reward(problem, assignment), 'canonical routing changes reward');
}

export function longOrLastFlow(input) {
  const problem = prepare(input), graph = network(problem), result = minCostFlow(graph, problem.target.length);
  const remaining = [...result.used], assignment = [];
  for (let birth = 0; birth < problem.target.length; birth++) {
    let at = graph.byName.get(`b:${birth}`), steps = 0;
    while (!graph.names[at].startsWith('o:')) {
      assert.ok(++steps <= graph.names.length);
      const index = graph.arcs.findIndex((arc, index) => arc.from === at && remaining[index] > 0);
      assert.ok(index >= 0);
      remaining[index]--; at = graph.arcs[index].to;
    }
    assignment.push(Number(graph.names[at].slice(2)));
  }
  assert.equal(new Set(assignment).size, assignment.length);
  assert.ok(assignment.every((output, birth) => birth <= output + problem.reach));
  const constant = sum(problem.gaps.flatMap(gap => gap.linear ? [BigInt(gap.base) * gap.reward] : []));
  assert.equal(reward(problem, assignment), -result.cost - constant, 'decoded reward differs from flow optimum');

  const lambda = problem.gaps.map(gap => {
    if (gap.linear) return gap.reward;
    const difference = result.potential[graph.byName.get(`e:${gap.start}`)] - result.potential[graph.byName.get(`e:${gap.end}`)];
    assert.ok(difference >= 0n);
    return difference < gap.reward ? difference : gap.reward;
  });
  const row = problem.target.map((_, birth) => result.potential[graph.byName.get(`b:${birth}`)]);
  const column = problem.target.map((value, output) => -result.potential[graph.byName.get(`o:${output}`)] +
    sum(problem.gaps.flatMap((gap, index) => !gap.linear && gap.value === value && output <= gap.start ? [lambda[index]] : [])));
  const prior = new Map();
  const modes = assignment.map((output, birth) => {
    const value = problem.target[output], ordinal = prior.get(value) ?? 0;
    prior.set(value, ordinal + 1);
    return ordinal > 0 && birth <= graph.events.get(value)[ordinal - 1] + problem.reach && problem.dup < problem.direct.get(value)
      ? 'dup' : 'direct';
  });
  const certificate = { scale: '1', row: row.map(String), column: column.map(String), prefix: lambda.map(String),
    upper: problem.gaps.map((gap, index) => String(gap.reward - lambda[index])) };
  const candidate = { assignment, modes }, checked = checkJointCertificate({ ...input, candidate, certificate });
  assert.equal(checked.status, 'certified');
  return { assignment, candidate, certificate, checked, reward: String(reward(problem, assignment)),
    vertices: graph.names.length, arcs: graph.arcs.length };
}

function* assignments(size, reach, entries = [], used = 0) {
  if (entries.length === size) { yield entries; return; }
  for (let output = Math.max(0, entries.length - reach); output < size; output++)
    if (!(used & 2 ** output)) yield* assignments(size, reach, [...entries, output], used | 2 ** output);
}

export function checkLongOrLastFixtures() {
  const fixtures = [
    { name: 'empty', target: [], reach: 16, prices: { direct: [], dup: 1, swap: 3 } },
    { name: 'three-separated-copies', target: ['a', 'b', 'c', 'a', 'b', 'c', 'a'], reach: 2,
      prices: { direct: [['a', 8], ['b', 1], ['c', 1]], dup: 1, swap: 3 } },
    { name: 'long-then-short-last', target: ['a', 'b', 'c', 'a', 'a', 'd'], reach: 2,
      prices: { direct: [['a', 9], ['b', 1], ['c', 1], ['d', 1]], dup: 1, swap: 2 } },
    { name: 'two-values-mixed', target: ['a', 'b', 'x', 'a', 'b', 'a', 'b'], reach: 2,
      prices: { direct: [['a', 9], ['b', 5], ['x', 1]], dup: 1, swap: 3 } },
    { name: 'zero-swap-price', target: ['a', 'b', 'x', 'a', 'b', 'a', 'b'], reach: 2,
      prices: { direct: [['a', 9], ['b', 5], ['x', 1]], dup: 1, swap: 0 } },
    { name: 'reuse-costs-too-much-movement', target: ['a', 'b', 'a', 'b', 'a'], reach: 1,
      prices: { direct: [['a', 2], ['b', 2]], dup: 1, swap: 30 } },
    { name: 'zero-reward-short-nonlast', target: ['a', 'a', 'x', 'a'], reach: 1,
      prices: { direct: [['a', 1], ['x', 5]], dup: 2, swap: 3 } }
  ];
  const records = fixtures.map(fixture => {
    const problem = prepare(fixture), graph = network(problem), result = longOrLastFlow(fixture);
    let best = null, count = 0;
    for (const assignment of assignments(fixture.target.length, fixture.reach)) {
      count++; canonicalRoute(problem, graph, assignment);
      const value = reward(problem, assignment);
      if (best === null || best < value) best = value;
    }
    assert.equal(result.reward, String(best));
    return { fixture, assignments: count, exactReward: String(best), result };
  });
  assert.throws(() => longOrLastFlow({ target: ['a', 'a', 'b', 'a'], reach: 1,
    prices: { direct: [['a', 5], ['b', 1]], dup: 1, swap: 2 } }), /neither long nor last/);
  return records;
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-long-or-last-flow.json', records = checkLongOrLastFixtures();
  const report = {
    status: 'exact offline checks of the paper long-or-last flow construction; no production solver or Lean flow theorem',
    scope: 'Seven named empty-source cases, each compared with every lag-valid endpoint permutation. Every canonical route and every extracted integer joint certificate is checked. One positive short nonlast gap is rejected.',
    cases: records.length, assignments: records.reduce((total, record) => total + record.assignments, 0), records,
    reproduce: `node scripts/optimality-long-or-last-flow.mjs ${output}`
  };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({ cases: report.cases, assignments: report.assignments }));
}
if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
