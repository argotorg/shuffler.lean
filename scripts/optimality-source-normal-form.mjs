#!/usr/bin/env node
/** Named counterexample to earliest pins followed by latest eligible rows. */
import assert from 'node:assert/strict';
import { fixedWordAssignment } from './optimality-fixed-word-matching.mjs';
import { sourcePotential } from './optimality-source-potential.mjs';
import { normalizeCase, replay } from './optimality-oracle.mjs';

function latestResidual(word, target, reach) {
  const matched = fixedWordAssignment(word, target, reach);
  assert.equal(matched.status, 'optimal');
  const assignment = [...matched.assignment];
  for (const group of matched.groups) {
    const fixed = new Set(group.fixed);
    const rows = group.births.filter(row => !fixed.has(row));
    for (const output of group.outputs.filter(column => !fixed.has(column))) {
      const index = rows.findLastIndex(row => row <= output + reach);
      assert.ok(index >= 0);
      assignment[rows[index]] = output;
      rows.splice(index, 1);
    }
  }
  return { assignment, original: matched.assignment, moved: matched.moved };
}

function check(scale, reach = 4 * scale) {
  const sourceSize = 4 * scale + 1, size = 6 * scale + 1;
  const activeWord = ['l:1', 'l:2', 'l:2', 'l:1', 'l:2', 'l:3', 'l:4'];
  const activeTarget = ['l:2', 'l:1', 'l:4', 'l:3', 'l:2', 'l:1', 'l:2'];
  const activeAssignment = [5, 6, 0, 1, 4, 3, 2];
  const word = Array.from({ length: size }, (_, index) => `l:${100 + index}`);
  const target = [...word], expected = word.map((_, index) => index);
  activeWord.forEach((value, index) => { word[scale * index] = value; });
  activeTarget.forEach((value, index) => { target[scale * index] = value; });
  activeAssignment.forEach((value, index) => { expected[scale * index] = scale * value; });
  const candidate = latestResidual(word, target, reach);
  assert.deepEqual(candidate.assignment, expected);
  assert.equal(candidate.moved, 6);
  assert.equal(candidate.assignment.filter((output, row) => output !== row).length, 6);
  assert.ok(candidate.assignment.every((output, row) => row <= output + reach && word[row] === target[output]));
  assert.equal(sourcePotential(candidate.assignment, sourceSize).F, 9);
  assert.equal(sourcePotential(candidate.original, sourceSize).F, 5);

  const operations = [['swap', 4 * scale], ['swap', 3 * scale]];
  for (let row = sourceSize; row < size; row++) {
    operations.push(['push', word[row]]);
    if (row === 5 * scale) operations.push(['swap', 2 * scale]);
    if (row === 6 * scale) operations.push(['swap', 4 * scale]);
  }
  const actual = replay(normalizeCase({ source: word.slice(0, sourceSize), target, spills: [],
    caps: { swap: reach, dup: reach } }), operations);
  assert.deepEqual(actual.added, word.slice(sourceSize));
  assert.equal(operations.filter(op => op[0] === 'swap').length, 4);
  return { reach, sourceSize, size, assignment: candidate.assignment,
    moved: 6, canonicalSwaps: 9, comparisonSwaps: 4,
    earliestResidualSwaps: 5, operations };
}

console.log(JSON.stringify({ status: 'checked selection obstruction; not a production change or a Lean theorem',
  reduced: check(1), production: check(1, 16), embedded: check(4) }, null, 2));
