#!/usr/bin/env node
/** Endpoint assignment for one supplied birth word; no birth-order search. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { periodicCase } from './optimality-birth-matching.mjs';

const positions = (word, value) => word.flatMap((item, index) => item === value ? [index] : []);

// Each fixed endpoint at c consumes one unit of Hall slack on [c,c+reach).
// At a capacity violation, reject the active reservation with the last end.
export function fixedWordAssignment(word, target, reach) {
  if (!Number.isInteger(reach) || reach < 1 || word.length !== target.length) throw new Error('invalid endpoint input');
  const values = [...new Set([...word, ...target])], assignment = Array(word.length), groups = [];
  for (const value of values) {
    const births = positions(word, value), outputs = positions(target, value);
    if (births.length !== outputs.length) return { status: 'infeasible', reason: 'count-balance' };
    const outputSet = new Set(outputs), candidates = births.filter(index => outputSet.has(index));
    const candidateSet = new Set(candidates), selected = new Set(), capacities = [];
    const events = [...new Set([...births, ...outputs.map(index => index + reach)])].sort((a, b) => a - b);
    let born = 0, due = 0, active = [];
    for (const cut of events) {
      while (born < births.length && births[born] <= cut) born++;
      while (due < outputs.length && outputs[due] + reach <= cut) due++;
      const capacity = born - due;
      if (capacity < 0) return { status: 'infeasible', reason: 'endpoint-deadline', value, cut };
      active = active.filter(start => cut < start + reach);
      if (candidateSet.has(cut)) { active.push(cut); selected.add(cut); }
      while (active.length > capacity) selected.delete(active.pop());
      capacities.push({ cut, capacity, reserved: active.length });
    }
    const remainingBirths = births.filter(index => !selected.has(index));
    const remainingOutputs = outputs.filter(index => !selected.has(index));
    for (const index of selected) assignment[index] = index;
    remainingBirths.forEach((birth, index) => {
      const output = remainingOutputs[index];
      assert.ok(birth <= output + reach, 'remaining sorted matching violates its deadline');
      assignment[birth] = output;
    });
    groups.push({ value, births, outputs, candidates, fixed: [...selected].sort((a, b) => a - b), capacities });
  }
  assert.equal(new Set(assignment).size, word.length);
  assignment.forEach((output, birth) => {
    assert.equal(word[birth], target[output]); assert.ok(birth <= output + reach);
  });
  return { status: 'optimal', assignment, moved: assignment.filter((output, birth) => output !== birth).length, groups };
}

// Given the frozen-prefix invariant, this count decides whether the next
// value has a readable copy. It does not label that copy by a final output.
// The caller must first check value balance and endpoint feasibility. This
// helper does not establish that invariant for values other than the next one.
export function introductionCuts(word, target, reach) {
  if (!Number.isInteger(reach) || reach < 1) throw new Error('invalid reach');
  const born = new Map(), frozen = new Map(), direct = [];
  for (let birth = 0; birth < word.length; birth++) {
    if (birth > reach) {
      const output = target[birth - reach - 1];
      frozen.set(output, (frozen.get(output) ?? 0) + 1);
    }
    const value = word[birth], inventory = (born.get(value) ?? 0) - (frozen.get(value) ?? 0);
    if (inventory < 0) return { status: 'infeasible', birth, value };
    if (inventory === 0) direct.push({ birth, value });
    born.set(value, (born.get(value) ?? 0) + 1);
  }
  return { status: 'checked', direct };
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-fixed-word-matching.json';
  const cases = [3, 4, 5, 8, 16].map(reach => {
    const problem = periodicCase(reach);
    return { reach, word: problem.match.birthWord, target: problem.target,
      endpoint: fixedWordAssignment(problem.match.birthWord, problem.target, reach),
      generation: introductionCuts(problem.match.birthWord, problem.target, reach) };
  });
  const report = {
    status: 'fixed-word endpoint optimization by interval packing',
    scope: 'A fixed endpoint c reserves one Hall-slack unit on [c,c+R). The sweep removes a latest-ending active reservation at each violation, then matches the remaining equal-value positions in sorted order. This JavaScript implementation is checked against exact assignment optima in tests; no Lean optimizer theorem is claimed. Generation counts are checked separately from endpoint-copy labels. No joint birth-order optimizer is supplied.',
    complexity: 'At most O(n^2) operations and O(n) retained entries for a fixed word in this array implementation; no dependence on a search over stack states.',
    cases
  };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify(cases.map(({ reach, endpoint, generation }) => ({ reach, moved: endpoint.moved,
    direct: generation.direct?.length }))));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
