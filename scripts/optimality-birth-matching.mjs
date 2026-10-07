#!/usr/bin/env node
/** Offline assignment relaxation. This module does not emit stack traces. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { consecutiveIntervals } from './optimality-interval-realizability.mjs';

// The returned dual variables certify the assignment cost. Forbidden edges
// have infinite cost and cannot occur in the assignment.
export function minimumAssignment(costs) {
  const size = costs.length;
  if (costs.some(row => row.length !== size || row.some(cost => cost !== Infinity &&
      (!Number.isSafeInteger(cost) || cost < 0)))) throw new Error('invalid square cost matrix');
  const u = Array(size + 1).fill(0), v = Array(size + 1).fill(0);
  const assigned = Array(size + 1).fill(0), previous = Array(size + 1).fill(0);
  for (let row = 1; row <= size; row++) {
    assigned[0] = row;
    let column = 0;
    const slack = Array(size + 1).fill(Infinity), used = Array(size + 1).fill(false);
    do {
      used[column] = true;
      const current = assigned[column];
      let delta = Infinity, next = 0;
      for (let candidate = 1; candidate <= size; candidate++) {
        if (used[candidate]) continue;
        const reduced = costs[current - 1][candidate - 1] - u[current] - v[candidate];
        if (reduced < slack[candidate]) {
          slack[candidate] = reduced; previous[candidate] = column;
        }
        if (slack[candidate] < delta) { delta = slack[candidate]; next = candidate; }
      }
      if (!Number.isFinite(delta)) return { status: 'infeasible' };
      for (let candidate = 0; candidate <= size; candidate++) {
        if (used[candidate]) { u[assigned[candidate]] += delta; v[candidate] -= delta; }
        else slack[candidate] -= delta;
      }
      column = next;
    } while (assigned[column] !== 0);
    do {
      const prior = previous[column]; assigned[column] = assigned[prior]; column = prior;
    } while (column !== 0);
  }
  const columns = Array(size);
  for (let column = 1; column <= size; column++) columns[assigned[column] - 1] = column - 1;
  const result = { status: 'optimal', columns,
    cost: columns.reduce((sum, column, row) => sum + costs[row][column], 0),
    rowDual: u.slice(1), columnDual: v.slice(1) };
  checkAssignment(costs, result);
  return result;
}

export function checkAssignment(costs, result) {
  const size = costs.length;
  assert.equal(result.status, 'optimal');
  assert.equal(result.columns.length, size);
  assert.equal(new Set(result.columns).size, size);
  assert.equal(result.rowDual.length, size); assert.equal(result.columnDual.length, size);
  let primal = 0;
  for (let row = 0; row < size; row++) {
    const column = result.columns[row];
    assert.ok(Number.isInteger(column) && column >= 0 && column < size);
    assert.ok(Number.isFinite(costs[row][column]), 'assignment uses a forbidden edge');
    primal += costs[row][column];
    for (let candidate = 0; candidate < size; candidate++) {
      assert.ok(result.rowDual[row] + result.columnDual[candidate] <= costs[row][candidate],
        'dual bound exceeds an edge cost');
    }
  }
  const dual = [...result.rowDual, ...result.columnDual].reduce((sum, value) => sum + value, 0);
  assert.equal(primal, result.cost); assert.equal(primal, dual, 'primal and dual costs differ');
  return true;
}

const counts = values => values.reduce((map, value) => map.set(value, (map.get(value) ?? 0) + 1), new Map());

export function deadlineJobs(source, target, reach, selected) {
  if (!Number.isInteger(reach) || reach < 1) throw new Error('invalid reach');
  const old = counts(source), wanted = counts(target);
  if ([...old].some(([value, count]) => count > (wanted.get(value) ?? 0))) throw new Error('source exceeds target counts');
  const intervals = consecutiveIntervals(target), stops = new Map();
  for (const index of selected) {
    if (!Number.isInteger(index) || !intervals[index] || stops.has(intervals[index].end)) throw new Error('invalid interval selection');
    const gap = intervals[index];
    if (target.slice(0, gap.start + 1).filter(value => value === gap.value).length < (old.get(gap.value) ?? 0)) {
      throw new Error('selected interval is not paid');
    }
    stops.set(gap.end, gap.start);
  }
  const seen = new Map(), jobs = [];
  for (let index = 0; index < target.length; index++) {
    const value = target[index], before = seen.get(value) ?? 0;
    seen.set(value, before + 1);
    if (before < (old.get(value) ?? 0)) continue;
    const origin = stops.get(index) ?? index;
    jobs.push({ output: index, value, origin, deadline: origin + reach - source.length + 1 });
  }
  return jobs;
}

export function birthMismatchMatching(source, target, reach, selected) {
  const jobs = deadlineJobs(source, target, reach, selected);
  const costs = jobs.map(job => jobs.map((_, slot) => slot + 1 <= job.deadline ?
    Number(job.value !== target[source.length + slot]) : Infinity));
  const match = minimumAssignment(costs);
  if (match.status !== 'optimal') return { ...match, jobs };
  const birthWord = Array(jobs.length);
  jobs.forEach((job, row) => { birthWord[match.columns[row]] = job.value; });
  const fixedMismatches = source.filter((value, index) => value !== target[index]).length;
  return { ...match, jobs, birthWord, fixedMismatches, mismatches: fixedMismatches + match.cost,
    swapFloor: Math.ceil((fixedMismatches + match.cost) / 2) };
}

export function periodicCase(reach, repetitions = 3) {
  if (!Number.isInteger(reach) || reach < 2 || !Number.isInteger(repetitions) || repetitions < 1) throw new Error('invalid periodic family');
  const block = Array.from({ length: reach - 1 }, (_, index) => `x${index + 1}`);
  const target = ['a', ...Array.from({ length: repetitions }, () => block).flat(), 'a'];
  const intervals = consecutiveIntervals(target), selected = intervals.map((_, index) => index);
  const match = birthMismatchMatching([], target, reach, selected);
  return { reach, repetitions, target, selected,
    gapDemand: intervals.reduce((sum, gap) => sum + Math.floor((gap.end - gap.start - 1) / reach), 0),
    forcedSuffix: repetitions === 3 ? block : null,
    actualSuffix: repetitions === 3 && match.status === 'optimal' ? match.birthWord.slice(2 * reach) : null,
    match };
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-birth-matching.json';
  const cases = [3, 4, 5, 8, 16].map(reach => periodicCase(reach));
  const report = {
    status: 'exact offline assignment optima with checked primal-dual certificates',
    scope: 'Birth jobs use the proved inventory deadline formula. This checker finds minimum value mismatches between source++birthWord and target over fixed-plan deadline assignments. It does not enforce DUP availability or time-ordered SWAP placement, and emits no production trace. The assignment certificates are checked in JavaScript; no Lean matching theorem is claimed.',
    complexity: 'The dense assignment algorithm uses O(n^3) time and O(n^2) space. This does not meet the intended O(n^2) time target.',
    cases
  };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify(cases.map(({ reach, gapDemand, match }) => ({ reach, gapDemand,
    status: match.status, mismatches: match.mismatches, swapFloor: match.swapFloor }))));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
