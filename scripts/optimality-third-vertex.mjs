#!/usr/bin/env node
/** One exact vertex check; no optimizer or search. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { deadlineJobs } from './optimality-birth-matching.mjs';

function rank(rows) {
  const matrix = rows.map(row => row.map(BigInt));
  let next = 0;
  for (let column = 0; column < (matrix[0]?.length ?? 0) && next < matrix.length; column++) {
    const pivot = matrix.findIndex((row, index) => index >= next && row[column] !== 0n);
    if (pivot < 0) continue;
    [matrix[next], matrix[pivot]] = [matrix[pivot], matrix[next]];
    const divisor = matrix[next][column];
    for (let row = next + 1; row < matrix.length; row++) {
      const multiple = matrix[row][column];
      if (multiple === 0n) continue;
      matrix[row] = matrix[row].map((value, index) => divisor * value - multiple * matrix[next][index]);
    }
    next++;
  }
  return next;
}

export function checkThirdVertex() {
  const target = Array.from({ length: 20 }, (_, index) => index === 0 || index >= 17 ? 'a' :
    index <= 13 ? `f${index}` : ['b', 'c', 'd'][index - 14]);
  const first = target.map((_, index) => index), second = [...first];
  const cycle = [14, 17, 15, 18, 16, 19];
  cycle.forEach((row, index) => { second[row] = cycle[(index + 1) % cycle.length]; });
  for (const assignment of [first, second]) {
    assert.equal(new Set(assignment).size, target.length);
    assert.ok(assignment.every((output, birth) => birth <= output + 16));
  }
  const numerator = target.map((_, birth) => target.map((_, output) =>
    2 * Number(first[birth] === output) + Number(second[birth] === output)));
  assert.ok(numerator.every(row => row.reduce((sum, value) => sum + value, 0) === 3));
  assert.ok(target.every((_, output) => numerator.reduce((sum, row) => sum + row[output], 0) === 3));
  const jobs = deadlineJobs([], target, 16, [0]).map(job => ({ value: job.value, deadline: job.deadline - 1 }));
  for (const value of new Set(target)) for (const cut of new Set(jobs.filter(job => job.value === value).map(job => job.deadline))) {
    const required = jobs.filter(job => job.value === value && job.deadline <= cut).length;
    const supplied = numerator.reduce((sum, row, birth) => sum + (birth <= cut ?
      row.reduce((total, amount, output) => total + (target[output] === value ? amount : 0), 0) : 0), 0);
    assert.ok(supplied >= 3 * required, `quota fails for ${value} at ${cut}`);
  }
  const count = assignment => assignment.filter((output, birth) => birth <= 16 && target[output] === 'a').length;
  assert.deepEqual([count(first), count(second)], [1, 4]);
  assert.equal(2 * count(first) + count(second), 3 * 2);
  const support = numerator.flatMap((row, birth) => row.flatMap((amount, output) => amount ? [{ birth, output, amount }] : []));
  const equations = [
    ...target.map((_, birth) => support.map(edge => Number(edge.birth === birth))),
    ...target.map((_, output) => support.map(edge => Number(edge.output === output)))
  ];
  const quota = support.map(edge => Number(edge.birth <= 16 && target[edge.output] === 'a'));
  assert.equal(rank(equations), support.length - 1);
  assert.equal(rank([...equations, quota]), support.length);
  assert.ok(support.some(edge => (2 * edge.amount) % 3 !== 0));
  return { status: 'exact non-half-integral vertex of the endpoint and fixed-generation-quota polytope',
    scope: 'One named reach-16 instance. No optimizer, broad search, or gap for moved-position cost is claimed.',
    target, reach: 16, selected: [0], jobs, first, second, relativeCycle: cycle,
    denominator: 3, support, counts: { first: 1, second: 4, required: 2, mixedNumerator: 6 },
    supportVariables: support.length, rowColumnRank: rank(equations), activeRank: rank([...equations, quota]) };
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-third-vertex.json';
  const report = checkThirdVertex();
  fs.writeFileSync(output, JSON.stringify({ ...report, reproduce: `node scripts/optimality-third-vertex.mjs ${output}` }, null, 2) + '\n');
  console.log(JSON.stringify({ denominator: report.denominator, supportVariables: report.supportVariables,
    rowColumnRank: report.rowColumnRank, activeRank: report.activeRank }));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
