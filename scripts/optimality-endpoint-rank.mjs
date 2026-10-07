#!/usr/bin/env node
/** Fixed birth-word endpoint objectives; no production scheduling policy. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';

const moved = assignment => assignment.filter((output, birth) => output !== birth).length;
export function permutationRank(assignment) {
  const seen = new Set(); let components = 0;
  for (let start = 0; start < assignment.length; start++) {
    if (seen.has(start)) continue;
    components++;
    for (let index = start; !seen.has(index); index = assignment[index]) seen.add(index);
  }
  return assignment.length - components;
}
function* assignments(size, reach, prefix = [], used = 0) {
  if (prefix.length === size) { yield prefix; return; }
  for (let output = Math.max(0, prefix.length - reach); output < size; output++) {
    if (!(used & 2 ** output)) yield* assignments(size, reach, [...prefix, output], used | 2 ** output);
  }
}
function* canonicalTargets(size, prefix = []) {
  if (prefix.length === size) { yield prefix; return; }
  const next = prefix.length ? Math.max(...prefix) + 1 : 0;
  for (let value = 0; value <= next; value++) yield* canonicalTargets(size, [...prefix, value]);
}
const positions = (word, value) => word.flatMap((item, index) => item === value ? [index] : []);

// This follows Reservations.select, Hall.fixed, and Endpoint.optimal.
// A named Lean test must check any claimed production witness separately.
export function orderedEndpointModel(word, target, reach) {
  const result = Array(word.length);
  for (const value of new Set(word)) {
    const births = positions(word, value), outputs = positions(target, value), selected = [];
    assert.equal(births.length, outputs.length);
    for (const start of births.filter(index => target[index] === value)) {
      const available = Array.from({ length: reach }, (_, offset) => start + offset).every(cut =>
        births.filter(index => index <= cut).length - outputs.filter(index => index + reach <= cut).length -
          selected.filter(index => index <= cut && cut < index + reach).length > 0);
      if (available) selected.push(start);
    }
    const fixed = new Set(selected), remainingBirths = births.filter(index => !fixed.has(index));
    const remainingOutputs = outputs.filter(index => !fixed.has(index));
    selected.forEach(index => { result[index] = index; });
    remainingBirths.forEach((index, ordinal) => { result[index] = remainingOutputs[ordinal]; });
  }
  assert.equal(new Set(result).size, word.length);
  assert.ok(result.every((output, birth) => word[birth] === target[output] && birth <= output + reach));
  return result;
}

export function checkEndpointRanks({ maximumSize = 7, wallLimitMs = 120000 } = {}) {
  assert.ok(Number.isInteger(maximumSize) && maximumSize >= 0 && maximumSize <= 8);
  const started = Date.now(), reaches = [1, 2, 3, 16];
  let instances = 0, permutations = 0, words = 0, modelRankGaps = 0, complete = true;
  const firstModelGaps = [], normalizationFailures = [];
  outer: for (let size = 0; size <= maximumSize; size++) for (const target of canonicalTargets(size)) for (const reach of reaches) {
    if (Date.now() - started > wallLimitMs) { complete = false; break outer; }
    instances++;
    const table = new Map();
    for (const assignment of assignments(size, reach)) {
      permutations++;
      const word = assignment.map(output => target[output]), key = word.join(',');
      const e = moved(assignment), k = permutationRank(assignment), old = table.get(key);
      if (!old) table.set(key, { word, minE: e, minK: k, minKAtMinE: k,
        minEWitness: assignment, minKWitness: assignment, minKAtMinEWitness: assignment });
      else {
        if (e < old.minE) {
          old.minE = e; old.minEWitness = assignment;
          old.minKAtMinE = k; old.minKAtMinEWitness = assignment;
        } else if (e === old.minE && k < old.minKAtMinE) {
          old.minKAtMinE = k; old.minKAtMinEWitness = assignment;
        }
        if (k < old.minK) { old.minK = k; old.minKWitness = assignment; }
      }
    }
    for (const entry of table.values()) {
      words++;
      const model = orderedEndpointModel(entry.word, target, reach), modelK = permutationRank(model);
      assert.equal(moved(model), entry.minE, 'ordered model does not minimize E');
      if (modelK > entry.minK) {
        modelRankGaps++;
        if (firstModelGaps.length < 5) firstModelGaps.push({ target, reach, ...entry, model, modelK });
      }
      if (entry.minKAtMinE > entry.minK) {
        normalizationFailures.push({ target, reach, ...entry, model, modelK });
        complete = false; break outer;
      }
    }
  }
  return { maximumSize, reaches, complete, instances, permutations, words, modelRankGaps,
    firstModelGaps, normalizationFailures, milliseconds: Date.now() - started };
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-endpoint-rank.json', result = checkEndpointRanks();
  const report = {
    status: 'bounded fixed-word endpoint comparison; no production change or general normalization theorem',
    scope: 'Compare minimum E, minimum K, minimum K among minimum-E assignments, and the ordered endpoint model. Enumerate all lag-valid endpoint permutations independently. Stop at the first E-versus-K normalization obstruction or after two minutes. A model witness is not a Lean production evaluation.',
    result, reproduce: `node scripts/optimality-endpoint-rank.mjs ${output}`
  };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify(report));
}
if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
