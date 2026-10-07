#!/usr/bin/env node
/** Bounded offline checks of local and two-word rounding statements. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';

const indices = size => Array.from({ length: size }, (_, index) => index);
const moved = assignment => assignment.filter((output, birth) => output !== birth).length;
function cycles(assignment) {
  const seen = new Set(), result = [];
  for (const start of indices(assignment.length)) {
    if (seen.has(start)) continue;
    const component = [];
    for (let index = start; !seen.has(index); index = assignment[index]) {
      seen.add(index); component.push(index);
    }
    result.push(component);
  }
  return result;
}
const rank = assignment => assignment.length - cycles(assignment).length;
const relative = (first, second) => {
  const inverse = []; second.forEach((output, birth) => { inverse[output] = birth; });
  return first.map(output => inverse[output]);
};
function* assignments(size, reach, prefix = [], used = 0) {
  if (prefix.length === size) { yield prefix; return; }
  for (let output = Math.max(0, prefix.length - reach); output < size; output++) {
    if (!(used & 2 ** output)) yield* assignments(size, reach, [...prefix, output], used | 2 ** output);
  }
}

export function localPermutationCheck() {
  let pairs = 0, splits = 0, recombinations = 0, tight = 0;
  for (const size of [2, 3, 4]) {
    const all = [...assignments(size, size)];
    for (const first of all) for (const second of all) {
      pairs++;
      const before = cycles(relative(first, second));
      for (let left = 0; left < size; left++) for (let right = left + 1; right < size; right++) {
        if (!before.some(component => component.includes(left) && component.includes(right))) continue;
        splits++;
        const exchanged = [...second];
        [exchanged[left], exchanged[right]] = [exchanged[right], exchanged[left]];
        const after = cycles(relative(first, exchanged));
        assert.equal(after.length, before.length + 1);
        for (let mask = 0; mask < 2 ** after.length; mask++) {
          const a = [...first], b = [...exchanged];
          after.forEach((component, index) => {
            if (mask & 2 ** index) for (const row of component) { a[row] = exchanged[row]; b[row] = first[row]; }
          });
          assert.equal(new Set(a).size, size); assert.equal(new Set(b).size, size);
          const actual = rank(a) + rank(b), bound = moved(first) + moved(second);
          assert.ok(actual <= bound, JSON.stringify({ first, second, left, right, a, b, actual, bound }));
          recombinations++; if (actual === bound) tight++;
        }
      }
    }
  }
  return { sizes: [2, 3, 4], pairs, splits, recombinations, tight };
}

function* canonicalTargets(size, prefix = []) {
  if (prefix.length === size) { yield prefix; return; }
  const next = prefix.length ? Math.max(...prefix) + 1 : 0;
  for (let value = 0; value <= next; value++) yield* canonicalTargets(size, [...prefix, value]);
}
const wordKey = word => word.join(',');
function endpointTable(target, reach) {
  const table = new Map(); let count = 0;
  for (const assignment of assignments(target.length, reach)) {
    count++;
    const word = assignment.map(output => target[output]), key = wordKey(word);
    const e = moved(assignment), k = rank(assignment), old = table.get(key);
    if (!old) table.set(key, { word, e, k, eAssignment: assignment, kAssignment: assignment });
    else {
      if (e < old.e) { old.e = e; old.eAssignment = assignment; }
      if (k < old.k) { old.k = k; old.kAssignment = assignment; }
    }
  }
  return { table, count };
}
function balanced(first, second, kinds) {
  const difference = Array(kinds).fill(0);
  for (const row of indices(first.length)) {
    difference[first[row]]++; difference[second[row]]--;
    if (difference.some(value => Math.abs(value) > 1)) return false;
  }
  return difference.every(value => value === 0);
}
function* balancedWords(first, second, kinds, row = 0, difference = Array(kinds).fill(0), a = [], b = []) {
  if (row === first.length) {
    if (difference.every(value => value === 0)) yield [a, b];
    return;
  }
  const choices = first[row] === second[row] ? [[first[row], second[row]]] :
    [[first[row], second[row]], [second[row], first[row]]];
  for (const [left, right] of choices) {
    const next = [...difference]; next[left]++; next[right]--;
    if (next.some(value => Math.abs(value) > 1)) continue;
    yield* balancedWords(first, second, kinds, row + 1, next, [...a, left], [...b, right]);
  }
}

export function boundedTwoWordCheck({ maximumSize = 6, wallLimitMs = 120000 } = {}) {
  assert.ok(Number.isInteger(maximumSize) && maximumSize >= 0 && maximumSize <= 6);
  const started = Date.now(), reaches = [1, 2, 16];
  let instances = 0, endpointPermutations = 0, coveredOrderedAssignmentPairs = 0;
  let wordPairs = 0, alreadyBalanced = 0, roundedPairs = 0, colorings = 0, complete = true, eFailureCount = 0;
  const eFailures = [], kFailures = [];
  outer: for (let size = 0; size <= maximumSize; size++) for (const target of canonicalTargets(size)) for (const reach of reaches) {
    if (Date.now() - started > wallLimitMs) { complete = false; break outer; }
    const { table, count } = endpointTable(target, reach), words = [...table.values()];
    const kinds = target.length ? Math.max(...target) + 1 : 0;
    instances++; endpointPermutations += count; coveredOrderedAssignmentPairs += count * count;
    for (let first = 0; first < words.length; first++) for (let second = first; second < words.length; second++) {
      wordPairs++;
      const a = words[first], b = words[second], bound = a.e + b.e;
      if (balanced(a.word, b.word, kinds)) {
        alreadyBalanced++;
        assert.ok(a.k + b.k <= bound);
        continue;
      }
      roundedPairs++;
      let bestE = null, bestK = null, eWitness = null, kWitness = null;
      for (const [left, right] of balancedWords(a.word, b.word, kinds)) {
        colorings++;
        const x = table.get(wordKey(left)), y = table.get(wordKey(right));
        assert.ok(x && y, 'balanced words have no lag-valid endpoint assignment');
        if (bestE === null || x.e + y.e < bestE) {
          bestE = x.e + y.e; eWitness = [x.eAssignment, y.eAssignment];
        }
        if (bestK === null || x.k + y.k < bestK) {
          bestK = x.k + y.k; kWitness = [x.kAssignment, y.kAssignment];
        }
      }
      assert.notEqual(bestK, null, 'no balanced two-color word pair');
      const fixture = { target, reach, inputWords: [a.word, b.word], inputAssignments: [a.eAssignment, b.eAssignment],
        bound, bestE, bestK, eWitness, kWitness };
      if (bestE > bound) { eFailureCount++; if (eFailures.length < 5) eFailures.push(fixture); }
      if (bestK > bound) { kFailures.push(fixture); complete = false; break outer; }
    }
  }
  return { maximumSize, reaches, complete, instances, endpointPermutations, coveredOrderedAssignmentPairs,
    wordPairs, alreadyBalanced, roundedPairs, colorings, eFailureCount, eFailures, kFailures, milliseconds: Date.now() - started };
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-local-cycle-rounding.json';
  const report = {
    status: 'bounded exact permutation checks; no global rounding theorem or production change',
    local: localPermutationCheck(),
    global: boundedTwoWordCheck(),
    scope: 'All canonical target partitions through length 6, reaches 1/2/16, and all lag-valid input assignment pairs. Birth-word quotienting keeps the minimum input E for each word, which gives the strongest bound for every assignment with that word. Each rounded word has independently enumerated minimum E and minimum K endpoint assignments. Both proposed inequalities are checked separately. The report retains the first five E failures and counts all of them.',
    reproduce: `node scripts/optimality-local-cycle-rounding.mjs ${output}`
  };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({ local: report.local, global: report.global }));
}
if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
