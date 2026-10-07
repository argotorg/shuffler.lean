#!/usr/bin/env node
/** Exact offline check of fixed-point interval capacity versus lag matching. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';

const count = (word, value) => word.filter(item => item === value).length;

export function fixedPointsFeasible(word, target, reach, selected) {
  const values = [...new Set([...word, ...target])];
  if (!Number.isInteger(reach) || reach < 1 || word.length !== target.length ||
      values.some(value => count(word, value) !== count(target, value)) ||
      new Set(selected).size !== selected.length || selected.some(index => !Number.isInteger(index) ||
        index < 0 || index >= word.length || word[index] !== target[index])) return false;
  return values.every(value => Array.from({ length: word.length + reach }, (_, k) => k).every(k => {
    const slack = count(word.slice(0, k + 1), value) - count(target.slice(0, Math.max(0, k - reach + 1)), value);
    const occupied = selected.filter(c => word[c] === value && c <= k && k < c + reach).length;
    return occupied <= slack;
  }));
}

export function sortedResidualAssignment(word, target, reach, selected) {
  assert.ok(fixedPointsFeasible(word, target, reach, selected), 'fixed-point capacity fails');
  const fixed = new Set(selected), assignment = Array(word.length);
  selected.forEach(index => { assignment[index] = index; });
  for (const value of new Set(word)) {
    const births = word.flatMap((item, index) => item === value && !fixed.has(index) ? [index] : []);
    const finals = target.flatMap((item, index) => item === value && !fixed.has(index) ? [index] : []);
    births.forEach((birth, index) => { assignment[birth] = finals[index]; });
  }
  assert.ok(assignment.every((final, birth) => birth <= final + reach), 'sorted residual lag fails');
  return assignment;
}

export function exactAssignments(word, target, reach) {
  if (word.length !== target.length) return [];
  const visit = (birth, remaining, prefix) => birth === word.length ? [prefix] :
    remaining.filter(final => word[birth] === target[final] && birth <= final + reach)
      .flatMap(final => visit(birth + 1, remaining.filter(other => other !== final), [...prefix, final]));
  return visit(0, Array.from({ length: target.length }, (_, index) => index), []);
}

function* canonicalWords(size, prefix = []) {
  if (prefix.length === size) { yield prefix; return; }
  for (const value of ['a', 'b', 'c'].slice(0, Math.min(3, new Set(prefix).size + 1))) yield* canonicalWords(size, [...prefix, value]);
}

function* distinctPermutations(word, prefix = []) {
  if (!word.length) { yield prefix; return; }
  for (const value of new Set(word)) {
    const index = word.indexOf(value);
    yield* distinctPermutations([...word.slice(0, index), ...word.slice(index + 1)], [...prefix, value]);
  }
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-fixed-points.json';
  let instances = 0, feasibleInstances = 0, subsets = 0, feasibleSubsets = 0, matchings = 0, minEExceedsValueMismatches = 0;
  const failures = [];
  for (const reach of [1, 2, 3, 16]) for (let size = 0; size <= 6; size++) {
    for (const word of canonicalWords(size)) for (const target of distinctPermutations(word)) {
      const exact = exactAssignments(word, target, reach), candidates = word.flatMap((value, index) => value === target[index] ? [index] : []);
      instances++; matchings += exact.length; if (exact.length) feasibleInstances++;
      const masks = exact.map(assignment => candidates.reduce((mask, position, bit) => mask + (assignment[position] === position ? 2 ** bit : 0), 0));
      let capacityMaximum = -1;
      for (let mask = 0; mask < 2 ** candidates.length; mask++) {
        const selected = candidates.filter((_, bit) => mask & 2 ** bit), actual = fixedPointsFeasible(word, target, reach, selected);
        const expected = masks.some(fixed => (fixed & mask) === mask); subsets++;
        if (actual !== expected) failures.push({ word, target, reach, selected, actual, expected });
        if (actual) {
          feasibleSubsets++; capacityMaximum = Math.max(capacityMaximum, selected.length);
          const assignment = sortedResidualAssignment(word, target, reach, selected);
          assert.ok(new Set(assignment).size === size && assignment.every((final, birth) => word[birth] === target[final] && birth <= final + reach));
          assert.ok(selected.every(position => assignment[position] === position));
        }
      }
      const exactMaximum = exact.length ? Math.max(...exact.map(assignment => assignment.filter((final, birth) => final === birth).length)) : -1;
      if (capacityMaximum !== exactMaximum) failures.push({ word, target, reach, capacityMaximum, exactMaximum });
      if (exact.length && size - exactMaximum > word.filter((value, index) => value !== target[index]).length) minEExceedsValueMismatches++;
    }
  }
  const report = { status: 'finite exact matching evidence; no polynomial selection algorithm or Lean theorem claimed',
    predicate: 'For each value v and cut k, selected correct positions c with c<=k<c+R must number at most #births(v)<=k minus #targets(v)<=k-R.',
    checkedEquivalence: 'A selected subset satisfies interval capacity iff some value-preserving bijection with birth<=target+R fixes every selected position. Sorted matching of the residual occurrences is then legal.',
    objective: 'Maximum feasible selected-subset cardinality equals the maximum number of fixed points over all exact lag matchings. Thus minimum E, the moved token support, is n minus that cardinality. E is not the number of value mismatches. Extra fixed points in a nonmaximal residual assignment are permitted.',
    domain: { reaches: [1, 2, 3, 16], length: '0 through 6', words: 'canonical words with at most 3 kinds', targets: 'all distinct permutations', subsets: 'all subsets of equal birth/target positions' },
    instances, feasibleInstances, subsets, feasibleSubsets, matchings, minEExceedsValueMismatches, failures,
    reproduce: `node scripts/optimality-fixed-points.mjs ${output}` };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n'); console.log(JSON.stringify(report));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
