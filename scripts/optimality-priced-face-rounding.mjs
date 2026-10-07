#!/usr/bin/env node
/** Named exact checks of prefix rounding on one positive-price assignment face. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { pricedAssignment } from './optimality-priced-assignment.mjs';

const moved = assignment => assignment.filter((output, row) => output !== row).length;
const key = word => word.join(',');
function* assignments(size, reach, prefix = [], used = 0) {
  if (prefix.length === size) { yield prefix; return; }
  for (let output = Math.max(0, prefix.length - reach); output < size; output++) {
    if (!(used & 2 ** output)) yield* assignments(size, reach, [...prefix, output], used | 2 ** output);
  }
}
const gapLefts = target => target.flatMap((value, row) => target.slice(row + 1).includes(value) ? [row] : []);
const counts = (word, target, reach, gaps) => gaps.map(left =>
  word.slice(0, left + reach + 1).filter(value => value === target[left]).length);
function tableFor(target, reach) {
  const table = new Map(); let permutations = 0;
  for (const assignment of assignments(target.length, reach)) {
    permutations++;
    const word = assignment.map(output => target[output]), k = key(word), e = moved(assignment);
    if (!table.has(k) || e < table.get(k).e) table.set(k, { word, e, assignment, assignments: [assignment] });
    else if (e === table.get(k).e) table.get(k).assignments.push(assignment);
  }
  const gaps = gapLefts(target);
  for (const entry of table.values()) entry.counts = counts(entry.word, target, reach, gaps);
  return { table, gaps, permutations };
}

function relativeCycles(first, second) {
  const inverse = []; second.forEach((output, row) => { inverse[output] = row; });
  const relative = first.map(output => inverse[output]), seen = new Set(), result = [];
  for (let start = 0; start < first.length; start++) {
    if (seen.has(start)) continue;
    const cycle = [];
    for (let row = start; !seen.has(row); row = relative[row]) { seen.add(row); cycle.push(row); }
    result.push(cycle);
  }
  return result;
}
function splitObstruction(first, second, target, reach, gaps, stats) {
  for (const cycle of relativeCycles(first, second)) {
    const bad = gaps.flatMap(left => {
      const difference = cycle.filter(row => row <= left + reach).reduce((sum, row) =>
        sum + Number(target[first[row]] === target[left]) - Number(target[second[row]] === target[left]), 0);
      return Math.abs(difference) >= 2 ? [{ left, value: target[left], difference }] : [];
    });
    if (!bad.length) continue;
    stats.largeDiscrepancyCycles++;
    let split = null;
    for (const assignment of [first, second]) for (const left of cycle) for (const right of cycle) {
      if (left >= right || assignment[left] === left || assignment[right] === right) continue;
      if (target[assignment[left]] !== target[assignment[right]]) continue;
      if (left > assignment[right] + reach || right > assignment[left] + reach) continue;
      const after = [...assignment]; [after[left], after[right]] = [after[right], after[left]];
      assert.equal(moved(after), moved(assignment), 'a legal generic exchange gained an identity in a minimum-E assignment');
      split = { side: assignment === first ? 0 : 1, left, right };
    }
    if (!split) return { cycle, gaps: bad };
  }
  return null;
}
function terminalSplitCheck(first, second, target, reach) {
  const inputs = [[...first], [...second]], splits = [];
  for (;;) {
    const cycles = relativeCycles(...inputs);
    let found = null;
    outer: for (const cycle of cycles) for (let side = 0; side < 2; side++) {
      const assignment = inputs[side];
      for (const left of cycle) for (const right of cycle) {
        if (left >= right || assignment[left] === left || assignment[right] === right) continue;
        if (target[assignment[left]] !== target[assignment[right]]) continue;
        if (left > assignment[right] + reach || right > assignment[left] + reach) continue;
        found = { side, left, right }; break outer;
      }
    }
    if (!found) break;
    const { side, left, right } = found, before = moved(inputs[side]);
    [inputs[side][left], inputs[side][right]] = [inputs[side][right], inputs[side][left]];
    assert.equal(moved(inputs[side]), before);
    assert.equal(relativeCycles(...inputs).length, cycles.length + 1);
    splits.push(found);
  }
  const active = relativeCycles(...inputs).filter(cycle => cycle.length > 1), kinds = Math.max(...target) + 1;
  for (let mask = 0; mask < 2 ** active.length; mask++) {
    const output = inputs.map(assignment => [...assignment]);
    active.forEach((cycle, index) => {
      if (mask & 2 ** index) for (const row of cycle) [output[0][row], output[1][row]] = [output[1][row], output[0][row]];
    });
    const difference = Array(kinds).fill(0);
    let balanced = true;
    for (let row = 0; row < target.length; row++) {
      difference[target[output[0][row]]]++; difference[target[output[1][row]]]--;
      if (difference.some(value => Math.abs(value) > 1)) { balanced = false; break; }
    }
    if (balanced) return { splits, output };
  }
  return { splits, terminal: inputs, cycles: active };
}
function* priceVectors(size, values, prefix = []) {
  if (prefix.length === size) { yield prefix; return; }
  for (const value of values) yield* priceVectors(size, values, [...prefix, value]);
}
function* balancedPairs(first, second, kinds, row = 0, difference = Array(kinds).fill(0), a = [], b = []) {
  if (row === first.length) {
    if (difference.every(value => value === 0)) yield [a, b];
    return;
  }
  const choices = first[row] === second[row] ? [[first[row], second[row]]] :
    [[first[row], second[row]], [second[row], first[row]]];
  for (const [left, right] of choices) {
    const next = [...difference]; next[left]++; next[right]--;
    if (next.some(value => Math.abs(value) > 1)) continue;
    yield* balancedPairs(first, second, kinds, row + 1, next, [...a, left], [...b, right]);
  }
}

export function checkFaceFixture(fixture) {
  const { target, reach } = fixture, { table, gaps, permutations } = tableFor(target, reach);
  const entries = [...table.values()], kinds = Math.max(...target) + 1, seenFaces = new Set(), seenPairs = new Set();
  const seenAssignmentPairs = new Set(), splitFailures = [], terminalFailures = [];
  const splitStats = { largeDiscrepancyCycles: 0, pairsWithSplits: 0, totalSplits: 0 };
  let pricesChecked = 0, faces = 0, pairs = 0, colorings = 0, nontrivialPairs = 0;
  let roundingWitness = null;
  const failures = [];
  for (const swap of [1, 2]) for (const prices of priceVectors(gaps.length, [0, 1, 2, 3, 4])) {
    pricesChecked++;
    const rewards = entries.map(entry => swap * (target.length - entry.e) +
      entry.counts.reduce((sum, count, index) => sum + count * prices[index], 0));
    const optimum = Math.max(...rewards), face = entries.flatMap((_, index) => rewards[index] === optimum ? [index] : []);
    const faceKey = face.join(','); if (seenFaces.has(faceKey)) continue;
    seenFaces.add(faceKey); faces++;
    for (let a = 0; a < face.length; a++) for (let b = a + 1; b < face.length; b++) {
      const pairKey = `${face[a]}:${face[b]}`; if (seenPairs.has(pairKey)) continue;
      seenPairs.add(pairKey); pairs++;
      const first = entries[face[a]], second = entries[face[b]], bound = first.e + second.e;
      if (!splitFailures.length) for (const p of first.assignments) for (const q of second.assignments) {
        const assignmentPair = `${key(p)}:${key(q)}`;
        if (seenAssignmentPairs.has(assignmentPair)) continue;
        seenAssignmentPairs.add(assignmentPair);
        const obstruction = splitObstruction(p, q, target, reach, gaps, splitStats);
        if (!terminalFailures.length) {
          const terminal = terminalSplitCheck(p, q, target, reach);
          splitStats.totalSplits += terminal.splits.length;
          if (terminal.splits.length) splitStats.pairsWithSplits++;
          if (!terminal.output) {
            const input = { target, reach, swap, gaps: gaps.map((left, index) => ({ left, weight: prices[index] })) };
            const dual = pricedAssignment(input);
            assert.equal(dual.reward, String(optimum));
            terminalFailures.push({ input, dual, first: p, second: q, ...terminal });
          }
        }
        if (obstruction) {
          const input = { target, reach, swap, gaps: gaps.map((left, index) => ({ left, weight: prices[index] })) };
          const dual = pricedAssignment(input);
          assert.equal(dual.reward, String(optimum));
          splitFailures.push({ input, dual, first: p, second: q, obstruction });
          break;
        }
      }
      let best = Infinity, witness = null, balancedInput = false;
      for (const [left, right] of balancedPairs(first.word, second.word, kinds)) {
        colorings++;
        const x = table.get(key(left)), y = table.get(key(right));
        assert.ok(x && y, 'balanced row-token word has no legal endpoint assignment');
        if (key(left) === key(first.word) && key(right) === key(second.word)) balancedInput = true;
        if (x.e + y.e < best) { best = x.e + y.e; witness = [x.assignment, y.assignment]; }
      }
      assert.ok(Number.isFinite(best));
      if (!balancedInput) {
        nontrivialPairs++;
        if (roundingWitness === null) {
          const input = { target, reach, swap, gaps: gaps.map((left, index) => ({ left, weight: prices[index] })) };
          const dual = pricedAssignment(input);
          assert.equal(dual.reward, String(optimum));
          roundingWitness = { input, dual, first: first.assignment, second: second.assignment,
            inputMoved: bound, bestOutputMoved: best, outputWitness: witness };
        }
      }
      // The summed priced prefix counts are preserved, so any success must stay on the same face.
      if (best <= bound) assert.equal(best, bound);
      else {
        const input = { target, reach, swap, gaps: gaps.map((left, index) => ({ left, weight: prices[index] })) };
        const dual = pricedAssignment(input);
        assert.equal(dual.status, 'optimal'); assert.equal(dual.reward, String(optimum));
        failures.push({ input, dual, inputAssignments: [first.assignment, second.assignment],
          inputWords: [first.word, second.word], inputMoved: bound, bestOutputMoved: best, outputWitness: witness });
        return { name: fixture.name, target, reach, permutations, words: entries.length, pricesChecked,
          faces, pairs, nontrivialPairs, colorings, failures, roundingWitness,
          splitAssignmentPairs: seenAssignmentPairs.size, splitStats, splitFailures, terminalFailures };
      }
    }
  }
  return { name: fixture.name, target, reach, permutations, words: entries.length, pricesChecked,
    faces, pairs, nontrivialPairs, colorings, failures, roundingWitness,
    splitAssignmentPairs: seenAssignmentPairs.size, splitStats, splitFailures, terminalFailures };
}

function minimumMovedForWord(word, target, reach) {
  let best = Infinity, witness = null;
  const visit = (row, assignment, used, score) => {
    if (score >= best) return;
    if (row === word.length) { best = score; witness = assignment; return; }
    for (let output = Math.max(0, row - reach); output < target.length; output++) {
      if (word[row] !== target[output] || (used & 2 ** output)) continue;
      visit(row + 1, [...assignment, output], used | 2 ** output, score + Number(row !== output));
    }
  };
  visit(0, [], 0, 0);
  assert.ok(Number.isFinite(best));
  return { e: best, assignment: witness };
}

export function checkDenominatorThree() {
  const target = [0, ...Array.from({ length: 16 }, (_, index) => index + 1), 0, 0, 0], reach = 16;
  const identity = target.map((_, index) => index), prefetch = [...identity], cycle = [14, 17, 15, 18, 16, 19];
  cycle.forEach((row, index) => { prefetch[row] = cycle[(index + 1) % cycle.length]; });
  const input = { target, reach, swap: 1, gaps: [{ left: 0, weight: 2 }] }, dual = pricedAssignment(input);
  const inputs = [identity, identity, prefetch], words = inputs.map(assignment => assignment.map(output => target[output]));
  const reward = assignment => target.length - moved(assignment) +
    2 * assignment.slice(0, 17).filter(output => target[output] === 0).length;
  inputs.forEach(assignment => {
    assert.ok(assignment.every((output, row) => row <= output + reach));
    assert.equal(String(reward(assignment)), dual.reward);
  });
  let colorings = 0, best = Infinity, witness = null;
  const visit = (row, counts, outputs) => {
    if (row === target.length) {
      if (target.some(value => counts.some(color => color[value] !== counts[0][value]))) return;
      colorings++;
      const endpoints = outputs.map(word => minimumMovedForWord(word, target, reach));
      const e = endpoints.reduce((sum, entry) => sum + entry.e, 0);
      if (e < best) { best = e; witness = endpoints.map(entry => entry.assignment); }
      return;
    }
    const tokens = words.map(word => word[row]), choices = new Map();
    for (let a = 0; a < 3; a++) for (let b = 0; b < 3; b++) if (a !== b) {
      const choice = [tokens[a], tokens[b], tokens[3 - a - b]]; choices.set(key(choice), choice);
    }
    for (const choice of choices.values()) {
      const next = counts.map((color, index) => color.map((count, value) => count + Number(choice[index] === value)));
      if (next[0].some((_, value) => Math.max(...next.map(color => color[value])) - Math.min(...next.map(color => color[value])) > 1)) continue;
      visit(row + 1, next, outputs.map((word, index) => [...word, choice[index]]));
    }
  };
  visit(0, Array.from({ length: 3 }, () => Array(17).fill(0)), [[], [], []]);
  const bound = inputs.reduce((sum, assignment) => sum + moved(assignment), 0);
  assert.equal(best, bound);
  return { name: 'three-copy-prefetch-denominator-three', input, dual, inputAssignments: inputs,
    inputMoved: bound, balancedColorings: colorings, bestOutputMoved: best, outputWitness: witness };
}

/** Refutes E-preserving row-token rounding even at canonical cuts. */
export function checkCanonicalCounterexample() {
  const input = { target: [0, 1, 2, 1, 1, 3, 2, 0], reach: 3, swap: 1,
    gaps: [{ left: 0, weight: 2 }, { left: 2, weight: 2 }] };
  const { target, reach } = input, { table, gaps, permutations } = tableFor(target, reach);
  const inputs = [target.map((_, row) => row), [0, 1, 2, 7, 6, 5, 3, 4]];
  const words = inputs.map(assignment => assignment.map(output => target[output]));
  const reward = assignment => target.length - moved(assignment) + input.gaps.reduce((sum, gap) =>
    sum + gap.weight * assignment.slice(0, gap.left + reach + 1).filter(output =>
      target[output] === target[gap.left]).length, 0);
  const optimum = Math.max(...[...table.values()].map(entry => reward(entry.assignment)));
  const dual = pricedAssignment(input);
  assert.equal(String(optimum), dual.reward);
  inputs.forEach(assignment => {
    assert.ok(assignment.every((output, row) => row <= output + reach));
    assert.equal(reward(assignment), optimum);
  });
  let colorings = 0, best = Infinity, witness = null;
  const visit = (row, difference, left, right) => {
    if (row === target.length) {
      if (difference.some(value => value !== 0)) return;
      const a = table.get(key(left)), b = table.get(key(right));
      if (!a || !b) return;
      colorings++;
      if (a.e + b.e < best) { best = a.e + b.e; witness = [a.assignment, b.assignment]; }
      return;
    }
    const [a, b] = words.map(word => word[row]);
    for (const [x, y] of a === b ? [[a, b]] : [[a, b], [b, a]]) {
      const next = [...difference]; next[x]++; next[y]--;
      if (gaps.some(gap => gap + reach === row && Math.abs(next[target[gap]]) > 1)) continue;
      visit(row + 1, next, [...left, x], [...right, y]);
    }
  };
  visit(0, Array(4).fill(0), [], []);
  const rank = assignment => relativeCycles(assignment, target.map((_, row) => row))
    .reduce((sum, cycle) => sum + cycle.length - 1, 0);
  const alternative = [0, 1, 2, 7, 4, 6, 3, 5];
  assert.ok(alternative.every((output, row) => row <= output + reach));
  assert.equal(reward(alternative), optimum);
  return { name: 'canonical-price-mixed-pin-obstruction', input, dual, permutations, words: table.size,
    inputAssignments: inputs, inputMoved: inputs.reduce((sum, assignment) => sum + moved(assignment), 0),
    canonicalGaps: gaps.map(left => ({ left, value: target[left], cut: left + reach })),
    balancedColorings: colorings, bestOutputMoved: best, outputWitness: witness,
    outputSwapRank: witness.reduce((sum, assignment) => sum + rank(assignment), 0),
    alternative: { assignment: alternative, moved: moved(alternative), reward: reward(alternative),
      gapCounts: counts(alternative.map(output => target[output]), target, reach, gaps) },
    scope: 'This refutes canonical-cut E-preserving row-token rounding on a common canonical-price face. The witnesses have total swap rank 3 <= input E 4. A different common-face assignment changes row values and retains every gap. This is not a factor-two or LP-integrality counterexample.' };
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-priced-face-rounding.json';
  const fixtures = [
    { name: 'unpriced-four-row-obstruction', target: [0, 0, 1, 2], reach: 2 },
    { name: 'pin-interval-overlap', target: [0, 1, 1, 0, 1, 0], reach: 2 },
    { name: 'safe-split-away-from-excess', target: [0, 1, 1, 0, 1, 1, 0, 0], reach: 2 },
    { name: 'mixed-pin-value-job-obstruction', target: [0, 0, 1, 1, 1, 1, 0, 0], reach: 2 },
    { name: 'three-paired-values', target: [0, 0, 1, 1, 2, 2, 0, 0], reach: 2 },
    { name: 'interleaved-short-nonlast', target: [0, 1, 0, 1, 2, 2, 0, 0], reach: 2 }
  ];
  const records = [];
  for (const fixture of fixtures) {
    const record = checkFaceFixture(fixture); records.push(record);
    console.log(JSON.stringify({ ...record, roundingWitness: record.roundingWitness !== null }));
    if (record.failures.length) break;
  }
  const report = { status: 'refuted by a named exact canonical-price counterexample',
    claim: 'E-preserving row-token rounding can fail on a positive-SWAP-price canonical-gap-price optimum face, even when balance is required only at canonical cuts.',
    priceDomain: { swap: [1, 2], eachCanonicalGap: [0, 1, 2, 3, 4] }, records,
    denominatorThree: checkDenominatorThree(),
    counterexample: checkCanonicalCounterexample(),
    scope: 'Six named reach-2 cases and one denominator-three case pass the stronger all-prefix check. The separate named reach-3 case refutes even canonical-cut row-token E rounding. Endpoint minima are independently enumerated and the counterexample has a checked sparse-flow assignment dual. The terminal tests use one deterministic split sequence per pair. No factor-two failure, LP integrality result, production change, or runtime bound is claimed.',
    reproduce: `node scripts/optimality-priced-face-rounding.mjs ${output}` };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
}
if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
