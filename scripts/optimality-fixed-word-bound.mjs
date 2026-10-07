#!/usr/bin/env node
/** Offline exact trace search for a supplied birth word. No production policy. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { baseline, normalizeCase, opCost, replay, score } from './optimality-oracle.mjs';
import { fixedWordAssignment } from './optimality-fixed-word-matching.mjs';
import { extractAssignment, realizeAssignment } from './optimality-assignment-realizer.mjs';

const count = (values, value) => values.filter(item => item === value).length;
const key = values => values.join('|');
const directOp = (problem, value) => value === 'wildcard' || value.startsWith('l:') ? ['push', value] :
  value.startsWith('v:') && problem.spills.includes(Number(value.slice(2))) ? ['load', Number(value.slice(2))] : null;

function checkWord(problem, word) {
  assert.equal(problem.source.length, 0, 'source must be empty');
  assert.equal(word.length, problem.target.length, 'word length differs');
  assert.deepEqual([...word].sort(), [...problem.target].sort(), 'word multiset differs');
}

export function constructFixedWord(problem, word) {
  checkWord(problem, word);
  const matched = fixedWordAssignment(word, problem.target, problem.caps.swap);
  if (matched.status !== 'optimal') return matched;
  const births = []; let generationScore = 0;
  for (let birth = 0; birth < word.length; birth++) {
    const value = word[birth], direct = directOp(problem, value);
    const canDuplicate = count(word.slice(0, birth), value) >
      count(problem.target.slice(0, Math.max(0, birth - problem.caps.swap)), value);
    const directCost = direct ? score(problem, opCost(problem, direct)) : Infinity;
    const duplicateCost = canDuplicate ? score(problem, opCost(problem, ['dup', 1])) : Infinity;
    if (!Number.isFinite(Math.min(directCost, duplicateCost))) return { status: 'infeasible', reason: 'birth-mode', birth, value };
    births.push({ value, kind: duplicateCost < directCost ? 'dup' : direct[0] });
    generationScore += Math.min(directCost, duplicateCost);
  }
  const realized = realizeAssignment(problem, births, matched.assignment);
  assert.equal(realized.E, matched.moved);
  assert.equal(realized.score, generationScore + score(problem, opCost(problem, ['swap', 1])) * realized.swaps);
  return { status: 'constructed', generationScore, births, assignment: matched.assignment, ...realized };
}

/** Dijkstra over all value stacks. Only the next introduced value is fixed.
 * It includes each legal SWAP, each matching DUP, and each legal direct birth.
 * No assignment, Hall criterion, or target-prefix pruning is used in this search.
 */
export function exactFixedWordMinima(problem, word) {
  checkWord(problem, word);
  const initial = { stack: [], score: 0, ops: [] }, distances = new Map([['', initial]]), queue = [initial];
  let expanded = 0, edges = 0;
  while (queue.length) {
    queue.sort((a, b) => b.score - a.score);
    const current = queue.pop();
    if (distances.get(key(current.stack)) !== current) continue;
    expanded++;
    const moves = [], size = current.stack.length;
    for (let depth = 1; depth <= problem.caps.swap && depth < size; depth++) {
      const lower = size - depth - 1;
      if (current.stack[lower] === current.stack.at(-1)) continue;
      const stack = [...current.stack]; [stack[lower], stack[size - 1]] = [stack[size - 1], stack[lower]];
      moves.push({ stack, op: ['swap', depth] });
    }
    if (size < word.length) {
      const value = word[size], direct = directOp(problem, value), stack = [...current.stack, value];
      if (direct) moves.push({ stack, op: direct });
      for (let depth = 1; depth <= problem.caps.dup && depth <= size; depth++) {
        if (current.stack[size - depth] === value) moves.push({ stack, op: ['dup', depth] });
      }
    }
    edges += moves.length;
    for (const move of moves) {
      const next = { stack: move.stack, score: current.score + score(problem, opCost(problem, move.op)), ops: [...current.ops, move.op] };
      const nextKey = key(next.stack);
      if (next.score < (distances.get(nextKey)?.score ?? Infinity)) { distances.set(nextKey, next); queue.push(next); }
    }
  }
  return { states: distances.size, expanded, edges,
    endpoints: new Map([...distances].filter(([, record]) => record.stack.length === word.length)) };
}

function* canonicalWords(size, prefix = []) {
  if (prefix.length === size) { yield prefix; return; }
  for (let value = 0; value < Math.min(3, new Set(prefix).size + 1); value++) yield* canonicalWords(size, [...prefix, value]);
}

function* distinctPermutations(word, prefix = []) {
  if (!word.length) { yield prefix; return; }
  for (const value of new Set(word)) {
    const index = word.indexOf(value);
    yield* distinctPermutations([...word.slice(0, index), ...word.slice(index + 1)], [...prefix, value]);
  }
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-fixed-word-bound.json';
  const profiles = [
    { name: 'variable-widths-0-2-32', values: ['v:42', 'v:43', 'v:44'], spills: [42, 43, 44], loadWidths: [[42, 0], [43, 2], [44, 32]], gasModel: 'cpp' },
    { name: 'variable-widths-32', values: ['v:42', 'v:43', 'v:44'], spills: [42, 43, 44], loadWidths: [[42, 32], [43, 32], [44, 32]], gasModel: 'evm' },
    { name: 'push0-small-literal-load32', values: ['l:0', 'l:1', 'v:42'], spills: [42], loadWidths: [[42, 32]], gasModel: 'cpp' },
    { name: 'push0-wide-literal-load0', values: ['l:0', `l:${1n << 248n}`, 'v:42'], spills: [42], loadWidths: [[42, 0]], gasModel: 'evm' }
  ];
  const weights = [{ gas: 1, bytes: 0 }, { gas: 0, bytes: 1 }, { gas: 1, bytes: 1 }, { gas: 6, bytes: 1 }];
  let searches = 0, states = 0, edges = 0, endpointCases = 0, feasibleCases = 0, infeasibleCases = 0, exactConstructions = 0, positiveWordExcess = 0, zeroWordExcess = 0;
  let maximumWordExcessRatio = 0, maximumBaselineExcessRatio = 0, worst = null;
  const failures = [];
  for (const reach of [1, 2, 3, 16]) for (let size = 0; size <= 6; size++) {
    for (const abstractWord of canonicalWords(size)) for (const profile of profiles) for (const weight of weights) {
      const word = abstractWord.map(value => profile.values[value]);
      const input = { source: [], target: word, spills: profile.spills, loadWidths: profile.loadWidths,
        gasModel: profile.gasModel, caps: { swap: reach, dup: reach }, weights: weight };
      const search = exactFixedWordMinima(normalizeCase(input), word);
      searches++; states += search.states; edges += search.edges;
      for (const target of distinctPermutations(word)) {
        endpointCases++;
        const problem = normalizeCase({ ...input, target }), exact = search.endpoints.get(key(target));
        try {
          const actual = constructFixedWord(problem, word);
          assert.equal(actual.status === 'constructed', Boolean(exact), 'feasibility differs');
          if (!exact) { infeasibleCases++; continue; }
          feasibleCases++;
          const observed = replay(problem, exact.ops), plan = extractAssignment(problem, exact.ops);
          assert.deepEqual(observed.added, word);
          assert.equal(observed.score, exact.score);
          const exactSwaps = exact.ops.filter(op => op[0] === 'swap').length;
          const swapCost = score(problem, opCost(problem, ['swap', 1]));
          const support = plan.assignment.filter((position, birth) => position !== birth).length;
          assert.ok(actual.E <= support && support <= 2 * exactSwaps, 'moved token support bound fails');
          assert.equal(exact.score - exactSwaps * swapCost, actual.generationScore, 'minimum generation cost differs');
          const B = baseline(problem), candidateExcess = actual.score - actual.generationScore;
          const exactExcess = exact.score - actual.generationScore;
          assert.ok(actual.generationScore >= B, 'fixed-word generation cost is below baseline');
          assert.ok(candidateExcess <= 2 * exactExcess, 'fixed-word generation excess exceeds factor two');
          assert.ok(actual.score - B <= 2 * (exact.score - B), 'global baseline excess exceeds factor two');
          if (actual.score === exact.score) exactConstructions++;
          if (exactExcess === 0) { zeroWordExcess++; assert.equal(candidateExcess, 0); }
          else {
            positiveWordExcess++;
            const ratio = candidateExcess / exactExcess;
            if (ratio > maximumWordExcessRatio) {
              maximumWordExcessRatio = ratio;
              worst = { word, target, reach, profile: profile.name, weights: weight, E: actual.E,
                constructedSwaps: actual.swaps, exactSwaps, generationScore: actual.generationScore,
                candidateScore: actual.score, exactScore: exact.score, candidateOps: actual.ops, exactOps: exact.ops };
            }
          }
          if (exact.score > B) maximumBaselineExcessRatio = Math.max(maximumBaselineExcessRatio, (actual.score - B) / (exact.score - B));
        } catch (error) {
          failures.push({ word, target, reach, profile: profile.name, weights: weight, error: error.message });
        }
      }
    }
    console.error(`fixed-word R=${reach} n=${size}: ${endpointCases} cases, ${failures.length} failures`);
  }
  const report = {
    status: 'finite exact fixed-word trace evidence; no global birth-order optimizer or Lean theorem claimed',
    scope: 'The constructor chooses the cheapest legal birth mode by target-prefix counts, minimizes E over lag-valid equal-copy assignments with interval packing, then uses the assignment realizer. E counts moved token positions, not value mismatches.',
    oracle: 'Complete Dijkstra on actual value stacks, with fixed next birth value, every legal SWAP and matching DUP, and each legal direct birth. No assignment criterion or target-prefix pruning is used. Equal-value SWAPs are omitted because they preserve the value stack and have positive cost.',
    checkedBounds: 'For every feasible fixed word w, constructedCost-G(w) <= 2*(exactFixedWordOPT-G(w)); also constructedCost-B <= 2*(exactFixedWordOPT-B). G(w) is its minimum generation cost and B is the usual target generation baseline. Zero excess is checked separately. These are fixed-word comparisons, not comparisons with unrestricted OPT.',
    domain: { reaches: [1, 2, 3, 16], length: '0 through 6', words: 'canonical words with at most 3 kinds', targets: 'all distinct permutations', profiles, weights },
    searches, states, edges, endpointCases, feasibleCases, infeasibleCases, exactConstructions,
    positiveWordExcess, zeroWordExcess, maximumWordExcessRatio, maximumBaselineExcessRatio, worst, failures,
    reproduce: `node scripts/optimality-fixed-word-bound.mjs ${output}`
  };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({ searches, states, endpointCases, feasibleCases, infeasibleCases, exactConstructions,
    maximumWordExcessRatio, maximumBaselineExcessRatio, failures: failures.length }));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
