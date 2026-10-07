#!/usr/bin/env node
/** Exact offline weak-duality certificates. This file does not solve an LP. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { consecutiveIntervals } from './optimality-interval-realizability.mjs';
import { exactObjective, retentionEntries } from './optimality-quota-lp-objectives.mjs';

const integer = value => {
  assert.ok(typeof value === 'string' && /^-?\d+$/.test(value) || Number.isSafeInteger(value), 'invalid exact integer');
  return BigInt(value);
};
const natural = value => { const result = integer(value); assert.ok(result >= 0n, 'negative nonnegative coefficient'); return result; };
const sum = values => values.reduce((total, value) => total + value, 0n);
const positivePart = value => value > 0n ? value : 0n;

export function checkJointCertificate({ source = [], target, hard = [], reach, prices, candidate, certificate }) {
  assert.ok(Number.isSafeInteger(reach) && reach >= 1, 'invalid reach');
  const size = target.length, values = [...new Set(target)];
  const direct = new Map(prices.direct.map(([value, price]) => [value, natural(price)]));
  assert.equal(direct.size, prices.direct.length, 'duplicate direct price');
  assert.ok(values.every(value => direct.has(value)), 'missing direct introduction');
  const dup = natural(prices.dup), swap = natural(prices.swap);
  const count = (items, value) => items.filter(item => item === value).length;
  assert.ok(source.every(value => count(source, value) <= count(target, value)), 'source multiplicity exceeds target');
  assert.ok(hard.every(value => direct.get(value) === dup), 'hard fallback price must equal DUP');
  const gaps = consecutiveIntervals(target).map(gap => {
    const ordinal = count(target.slice(0, gap.start + 1), gap.value);
    const eligible = ordinal >= count(source, gap.value), forced = eligible && hard.includes(gap.value);
    return { ...gap, cut: gap.start + reach, required: ordinal + Number(forced), forced,
      reward: eligible && !forced ? 2n * positivePart(direct.get(gap.value) - dup) : 0n };
  });
  const scale = natural(certificate.scale); assert.ok(scale > 0n, 'zero scale');
  const row = certificate.row.map(integer), column = certificate.column.map(integer);
  const prefix = certificate.prefix.map(natural), upper = certificate.upper.map(natural);
  assert.equal(row.length, size); assert.equal(column.length, size);
  assert.equal(prefix.length, gaps.length); assert.equal(upper.length, gaps.length);
  gaps.forEach((gap, index) => assert.ok(prefix[index] + upper[index] >= scale * gap.reward, 'retention dual inequality fails'));

  // A suffix sum by value gives every edge's prefix term. The arrays and
  // maps are local to this call. The checker uses O(n^2) integer operations.
  const active = new Map(values.map(value => [value, sum(gaps.flatMap((gap, index) => gap.value === value ? [prefix[index]] : []))]));
  const expire = Array.from({ length: size }, (_, cut) => gaps.flatMap((gap, index) => gap.cut === cut ? [index] : []));
  for (let birth = 0; birth < size; birth++) {
    for (let output = Math.max(0, birth - reach); output < size; output++) {
      if (birth < source.length && target[output] !== source[birth]) continue;
      if (birth + reach + 1 < source.length && birth !== output) continue;
      assert.ok(row[birth] + column[output] - active.get(target[output]) >=
        (birth === output ? scale * swap : 0n), 'endpoint dual inequality fails');
    }
    for (const index of expire[birth]) active.set(gaps[index].value, active.get(gaps[index].value) - prefix[index]);
  }

  const { assignment, modes } = candidate;
  assert.equal(assignment.length, size); assert.equal(modes.length, size - source.length);
  assert.ok(new Set(assignment).size === size && assignment.every((output, birth) =>
    Number.isInteger(output) && output >= 0 && output < size && birth <= output + reach &&
    (birth >= source.length || target[output] === source[birth]) &&
    (birth + reach + 1 >= source.length || output === birth)), 'invalid endpoint assignment');
  const prior = new Map(), endpoints = new Map(values.map(value => [value,
    target.flatMap((item, index) => item === value ? [index] : [])]));
  const birthPrices = assignment.map((output, birth) => {
    const value = target[output], ordinal = prior.get(value) ?? 0;
    prior.set(value, ordinal + 1);
    if (birth < source.length) return 0n;
    const mode = modes[birth - source.length];
    const canDuplicate = ordinal > 0 && birth <= endpoints.get(value)[ordinal - 1] + reach;
    assert.ok(mode === 'direct' || mode === 'dup', 'invalid birth method');
    assert.ok(mode !== 'direct' || !hard.includes(value), 'hard value cannot be introduced directly');
    assert.ok(mode !== 'dup' || canDuplicate, 'DUP has no available copy');
    return mode === 'dup' ? dup : direct.get(value);
  });
  const generation = sum(birthPrices), moved = assignment.filter((output, birth) => output !== birth).length;
  const objective = 2n * generation + swap * BigInt(moved);
  const allDirect = sum(target.map(value => direct.get(value))) - sum(source.map(value => direct.get(value)));
  const constant = 2n * allDirect + swap * BigInt(size);
  const upperBound = sum(row) + sum(column) - sum(gaps.map((gap, index) => BigInt(gap.required) * prefix[index])) + sum(upper);
  const lowerBound = scale * constant - upperBound, scaledGap = scale * objective - lowerBound;
  assert.ok(scaledGap >= 0n, 'candidate is below a verified lower bound');
  return { status: scaledGap === 0n ? 'certified' : 'lower-bound',
    scale: String(scale), lowerBoundNumerator: String(lowerBound), candidateObjective: String(objective),
    generationCost: String(generation), moved, scaledGap: String(scaledGap),
    constant: String(constant), rewardUpperBoundNumerator: String(upperBound),
    gaps: gaps.map(gap => ({ ...gap, reward: String(gap.reward) })) };
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-joint-dual.json';
  const fixtures = [
    { name: 'empty', target: [], reach: 16,
      prices: { direct: [], dup: 3, swap: 1 }, candidate: { assignment: [], modes: [] },
      certificate: { scale: 1, row: [], column: [], prefix: [], upper: [] } },
    { name: 'first-copies', target: ['a', 'b'], reach: 1,
      prices: { direct: [['a', 4], ['b', 6]], dup: 3, swap: 2 },
      candidate: { assignment: [0, 1], modes: ['direct', 'direct'] },
      certificate: { scale: 1, row: [2, 2], column: [0, 0], prefix: [], upper: [] } },
    { name: 'retained-copy', target: ['a', 'b', 'a'], reach: 1,
      prices: { direct: [['a', 34], ['b', 34]], dup: 1, swap: 1 },
      candidate: { assignment: [0, 2, 1], modes: ['direct', 'dup', 'direct'] },
      certificate: { scale: 1, row: [2, 1, 0], column: [1, 0, 1], prefix: [2], upper: [64] } },
    { name: 'separate-dup-and-swap-prices', target: ['a', 'b', 'a'], reach: 1,
      prices: { direct: [['a', 7], ['b', 4]], dup: 2, swap: 3 },
      candidate: { assignment: [0, 2, 1], modes: ['direct', 'dup', 'direct'] },
      certificate: { scale: 1, row: [6, 3, 0], column: [3, 0, 3], prefix: [6], upper: [4] } },
    { name: 'movement-cost-prevents-reuse', target: ['a', 'b', 'a'], reach: 1,
      prices: { direct: [['a', 3], ['b', 4]], dup: 2, swap: 3 },
      candidate: { assignment: [0, 1, 2], modes: ['direct', 'direct', 'direct'] },
      certificate: { scale: 1, row: [5, 3, 3], column: [0, 0, 0], prefix: [2], upper: [0] } },
    { name: 'cheap-direct', target: ['zero', 'zero'], reach: 1,
      prices: { direct: [['zero', 2]], dup: 3, swap: 5 },
      candidate: { assignment: [0, 1], modes: ['direct', 'direct'] },
      certificate: { scale: 1, row: [5, 5], column: [0, 0], prefix: [0], upper: [0] } }
  ];
  const records = [], failures = [];
  for (const fixture of fixtures) {
    try {
      const result = checkJointCertificate(fixture);
      assert.equal(result.status, 'certified');
      const direct = Object.fromEntries(fixture.prices.direct);
      const premiums = Object.fromEntries(fixture.prices.direct.map(([value, price]) => [value, Math.max(price - fixture.prices.dup, 0)]));
      const retention = retentionEntries(fixture.target, premiums);
      const exact = exactObjective(fixture.target, fixture.reach, [], { retention, swapPrice: fixture.prices.swap });
      const baseline = fixture.target.reduce((total, value) => total + direct[value], 0) -
        retention.reduce((total, gap) => total + gap.premium, 0);
      assert.equal(BigInt(result.candidateObjective), BigInt(2 * baseline + exact.objective));
      records.push({ ...fixture, result, baseline, exact });
    } catch (error) { failures.push({ fixture, error: error.message }); }
  }
  const report = {
    status: 'exact integer check of supplied joint dual certificates; no solver or Lean theorem claimed',
    certificate: 'Signed row and column potentials, nonnegative prefix and retention-upper-bound multipliers, and one positive common denominator. O(n) scalars and O(n^2) exact integer operations.',
    scope: 'Six hand-supplied small certificates are checked against independent endpoint-permutation optima. DUP and SWAP prices can differ. First-copy direct prices and direct-over-DUP dominance are included.',
    cases: records.length, failures, records,
    reproduce: `node scripts/optimality-joint-dual.mjs ${output}`
  };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({ cases: records.length, failures }));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
