#!/usr/bin/env node
/** One exact offline obstruction to a coordinate price-update claim. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { pricedAssignment } from './optimality-priced-assignment.mjs';
import { checkJointCertificate } from './optimality-joint-dual.mjs';

const target = ['a', 'b', 'a', 'b'];
const direct = new Map([['a', 11n], ['b', 6n]]);
const identity = [0, 1, 2, 3];
const retainA = [0, 2, 1, 3];
const retainB = [0, 1, 3, 2];
const baseline = 19n;

function* permutations(values, prefix = []) {
  if (!values.length) { yield prefix; return; }
  for (const value of values) yield* permutations(values.filter(other => other !== value), [...prefix, value]);
}

function plan(assignment) {
  const word = assignment.map(output => target[output]);
  const counts = [word.slice(0, 2).filter(value => value === 'a').length,
    word.slice(0, 3).filter(value => value === 'b').length];
  const modes = word.map((value, birth) => {
    const earlierBirths = word.slice(0, birth).filter(item => item === value).length;
    const earlierTargets = target.flatMap((item, index) => item === value ? [index] : []);
    return earlierBirths > 0 && birth <= earlierTargets[earlierBirths - 1] + 1 ? 'dup' : 'direct';
  });
  const generation = modes.reduce((total, mode, birth) => total + (mode === 'dup' ? 1n : direct.get(word[birth])), 0n);
  const moved = assignment.filter((output, birth) => output !== birth).length;
  const visited = new Set(); let cycles = 0;
  for (const start of assignment.keys()) {
    if (visited.has(start)) continue;
    let length = 0;
    for (let at = start; !visited.has(at); at = assignment[at]) { visited.add(at); length++; }
    if (length > 1) cycles++;
  }
  return { assignment, word, modes, counts, moved, cycles, generation: String(generation),
    score: String(generation + BigInt(moved - cycles)) };
}

const reward = (candidate, prices) => BigInt(4 - candidate.moved) +
  prices.reduce((total, price, index) => total + BigInt(price * candidate.counts[index]), 0n);

export function checkPriceCoupling() {
  const all = [...permutations(identity)];
  const legal = all.filter(assignment => assignment.every((output, birth) => birth <= output + 1)).map(plan);
  const classes = [[1, 1], [2, 1], [1, 2]].map(counts => {
    const members = legal.filter(candidate => candidate.counts.every((count, index) => count === counts[index]));
    assert.ok(members.length > 0);
    return { counts, plans: members.length, minimumMoved: Math.min(...members.map(candidate => candidate.moved)),
      minimumScore: String(members.reduce((best, candidate) => best < BigInt(candidate.score) ? best : BigInt(candidate.score), 1000n)) };
  });
  assert.equal(classes.reduce((total, group) => total + group.plans, 0), legal.length);
  assert.deepEqual(classes.map(group => group.minimumMoved), [0, 2, 2]);
  assert.deepEqual(classes.map(group => group.minimumScore), ['34', '25', '30']);

  const checked = ([a, b], assignment) => {
    const supplied = plan(assignment);
    const oracle = pricedAssignment({ target, reach: 1, swap: 1,
      gaps: [{ left: 0, weight: a }, { left: 1, weight: b }] });
    assert.equal(oracle.status, 'optimal');
    const best = legal.reduce((value, candidate) => {
      const next = reward(candidate, [a, b]); return next > value ? next : value;
    }, -1n);
    assert.equal(oracle.reward, String(best));
    const optimal = legal.filter(candidate => reward(candidate, [a, b]) === best);
    const certificate = { scale: 1, row: oracle.row, column: oracle.column, prefix: [a, b], upper: [20 - a, 10 - b] };
    const verified = checkJointCertificate({ target, reach: 1,
      prices: { direct: [...direct].map(([value, price]) => [value, String(price)]), dup: 1, swap: 1 },
      candidate: { assignment, modes: supplied.modes }, certificate });
    return { prices: [a, b], supplied, suppliedOracleOptimal: reward(supplied, [a, b]) === best,
      oracle, optimal, certificate, verified,
      surplusComparison: { candidatePlusBaseline: String(BigInt(supplied.score) + baseline),
        lower: verified.lowerBoundNumerator,
        passes: BigInt(supplied.score) + baseline <= BigInt(verified.lowerBoundNumerator) } };
  };

  const tied = checked([2, 2], retainA);
  const coordinate = checked([2, 3], retainB);
  const coordinateCap = checked([2, 10], retainB);
  const joint = checked([4, 4], retainA);
  assert.ok(tied.suppliedOracleOptimal && !tied.surplusComparison.passes);
  assert.equal(tied.verified.lowerBoundNumerator, '42');
  for (const result of [coordinate, coordinateCap]) {
    assert.ok(result.optimal.every(candidate => candidate.counts[0] === 1 && candidate.counts[1] === 2));
    assert.ok(result.optimal.every(candidate => BigInt(candidate.score) >= 30n));
    assert.equal(result.verified.lowerBoundNumerator, '42');
  }
  assert.ok(joint.suppliedOracleOptimal && joint.surplusComparison.passes);
  assert.equal(joint.verified.lowerBoundNumerator, '44');
  return { status: 'exact named obstruction to score-nonincreasing coordinate oracle exchanges',
    scope: 'Empty source, reach one. Four positions; no production change, LP solve, broad search, or reach-16 embedding.',
    instance: { target, reach: 1, prices: { direct: [['a', 11], ['b', 6]], dup: 1, swap: 1 }, baseline: String(baseline) },
    permutations: all.length, legalAssignments: legal.length, classes,
    comparisonPlans: [plan(identity), plan(retainA), plan(retainB)], tied, coordinate, coordinateCap, joint };
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-price-coupling.json';
  const report = checkPriceCoupling();
  fs.writeFileSync(output, JSON.stringify({ ...report, reproduce: `node scripts/optimality-price-coupling.mjs ${output}` }, null, 2) + '\n');
  console.log(JSON.stringify({ permutations: report.permutations, legalAssignments: report.legalAssignments,
    coordinateRaisesScore: true, jointCertificatePasses: report.joint.surplusComparison.passes }));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
