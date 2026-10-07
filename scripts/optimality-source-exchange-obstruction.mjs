#!/usr/bin/env node
/** Research regression: a minimum-moved-count source assignment can need a pin transfer. */
import assert from 'node:assert/strict';
import { sourcePotential } from './optimality-source-potential.mjs';
import { normalizeCase, replay } from './optimality-oracle.mjs';

const source = ['l:1', 'l:2', 'l:3', 'l:4', 'l:2'];
const word = ['l:2', 'l:2'];
const target = ['l:2', 'l:2', 'l:4', 'l:2', 'l:2', 'l:3', 'l:1'];
const assignment = [6, 0, 5, 2, 4, 1, 3];
const comparison = [6, 1, 5, 2, 0, 3, 4];
const moved = f => f.filter((value, index) => value !== index).length;

function* permutations(values) {
  if (values.length === 0) { yield []; return; }
  for (let index = 0; index < values.length; index++) {
    const rest = values.filter((_, position) => position !== index);
    for (const tail of permutations(rest)) yield [values[index], ...tail];
  }
}

function inspect(scale) {
  const reach = 4 * scale, height = 4 * scale + 1, size = 6 * scale + 1;
  const values = Array.from({ length: size }, (_, index) => `l:${100 + index}`);
  const output = [...values];
  const f = Array.from({ length: size }, (_, index) => index);
  const g = [...f];
  [...source, ...word].forEach((value, index) => { values[scale * index] = value; });
  target.forEach((value, index) => { output[scale * index] = value; });
  assignment.forEach((value, index) => { f[scale * index] = scale * value; });
  comparison.forEach((value, index) => { g[scale * index] = scale * value; });
  const valid = p => p.every((position, index) =>
    values[index] === output[position] && index <= position + reach);
  assert.ok(valid(f) && valid(g));
  assert.equal(moved(f), 6);
  assert.equal(moved(g), 6);
  assert.equal(sourcePotential(f, height).F, 9);
  assert.equal(sourcePotential(g, height).F, 6);

  // All singleton values have one possible endpoint. Only the four b rows vary.
  const equalRows = [1, 4, 5, 6].map(index => scale * index);
  const equalColumns = [0, 1, 3, 4].map(index => scale * index);
  const feasible = [...permutations(equalColumns)].map(destinations => {
    const p = [...f];
    equalRows.forEach((row, index) => { p[row] = destinations[index]; });
    return p;
  }).filter(valid);
  const minimumMoved = Math.min(...feasible.map(moved));
  assert.equal(minimumMoved, 6);
  const minimumFacePotential = Math.min(...feasible.filter(p => moved(p) === 6)
    .map(p => sourcePotential(p, height).F));
  assert.ok(minimumFacePotential <= 8);

  const exchanges = [];
  for (let left = 0; left < equalRows.length; left++) {
    for (let right = left + 1; right < equalRows.length; right++) {
      const first = equalRows[left], second = equalRows[right], p = [...f];
      [p[first], p[second]] = [p[second], p[first]];
      exchanges.push({ rows: [first, second], feasible: valid(p), moved: moved(p) });
      assert.ok(!valid(p) || moved(p) > minimumMoved);
    }
  }

  const operations = [['swap', reach]];
  for (let index = height; index < size; index++) {
    if (index % scale !== 0) operations.push(['push', values[index]]);
    else {
      operations.push(['dup', (index === 5 * scale ? 4 : 3) * scale]);
      if (index === 5 * scale) operations.push(['swap', 2 * scale], ['swap', 3 * scale]);
      else operations.push(['swap', 2 * scale]);
    }
  }
  const problem = normalizeCase({ source: values.slice(0, height), target: output,
    spills: [], caps: { swap: reach, dup: reach } });
  const actual = replay(problem, operations);
  assert.deepEqual(actual.added, values.slice(height));
  assert.equal(operations.filter(op => op[0] === 'swap').length, 4);
  assert.ok(sourcePotential(f, height).F > 2 * 4);
  return { reach, height, size, minimumMoved, minimumFacePotential,
    badAssignment: f, comparisonAssignment: g, exchanges, operations };
}

console.log(JSON.stringify({ status: 'checked finite obstruction; not a Lean theorem',
  reduced: inspect(1), production: inspect(4) }, null, 2));
