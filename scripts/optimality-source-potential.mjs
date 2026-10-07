#!/usr/bin/env node
/** Research only: audit a source-entry potential for a fixed labelled assignment. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { normalizeCase } from './optimality-oracle.mjs';
import { exactSourceWordMinSwaps } from './optimality-source-entry.mjs';

function cycles(permutation) {
  const seen = new Set(), result = [];
  for (let index = 0; index < permutation.length; index++) if (!seen.has(index)) {
    const cycle = []; let next = index;
    while (!seen.has(next)) { seen.add(next); cycle.push(next); next = permutation[next]; }
    if (cycle.length > 1) result.push(cycle);
  }
  return result;
}

export function sourcePotential(assignment, sourceLength) {
  assert.equal(new Set(assignment).size, assignment.length);
  assert.ok(assignment.every(index => Number.isInteger(index) && index >= 0 && index < assignment.length));
  const tokens = [], swaps = [];
  for (let birth = 0; birth < sourceLength; birth++) {
    tokens.push(birth);
    while (assignment[tokens.at(-1)] < birth) {
      const lower = assignment[tokens.at(-1)];
      [tokens[lower], tokens[birth]] = [tokens[birth], tokens[lower]];
      swaps.push([birth, lower]);
    }
  }
  const fullCycles = cycles(assignment), prefixCycles = cycles(tokens);
  const top = sourceLength - 1;
  const K = fullCycles.reduce((sum, cycle) => sum + cycle.length - 1, 0);
  const Kprefix = prefixCycles.reduce((sum, cycle) => sum + cycle.length - 1, 0);
  const c = prefixCycles.filter(cycle => !cycle.includes(top)).length;
  const q = fullCycles.filter(cycle => cycle.length === 2 && cycle.every(index => index < top)).length;
  assert.equal(Kprefix, swaps.length, 'virtual prefix uses exactly its arbitrary-transposition distance');
  for (const cycle of fullCycles) {
    const local = prefixCycles.filter(part => part.every(index => cycle.includes(index)) && !part.includes(top)).length;
    const exceptional = cycle.length === 2 && cycle.every(index => index < top) ? 1 : 0;
    assert.ok(2 * local <= cycle.length - 1 + exceptional, 'per-cycle prefix bound fails');
  }
  for (const part of prefixCycles) assert.ok(fullCycles.some(cycle => part.every(index => cycle.includes(index))), 'prefix mixes full cycles');
  assert.ok(2 * c <= K + q);
  return { K, Kprefix, c, q, F: K + 2 * c, tokens, prefixCycles, fullCycles, swaps };
}

export function auditSourcePotential() {
  let searches = 0, cases = 0, maximumRatio = 0, worst = null, exceptionalCases = 0;
  for (const reach of [1, 2, 3, 4, 16]) for (let size = 0; size <= 7; size++) {
    for (let sourceLength = 0; sourceLength <= Math.min(size, reach + 1); sourceLength++) {
      const values = Array.from({ length: size }, (_, index) => `l:${index}`);
      const source = values.slice(0, sourceLength), word = values.slice(sourceLength);
      const problem = normalizeCase({ source, target: values, spills: [], caps: { swap: reach, dup: reach } });
      const endpoints = exactSourceWordMinSwaps(problem, word); searches++;
      for (const exact of endpoints.values()) {
        const assignment = values.map(value => exact.stack.indexOf(value));
        const potential = sourcePotential(assignment, sourceLength); cases++;
        assert.ok(potential.K + 2 * potential.q <= exact.swaps, 'source-only two-cycle entry lower bound fails');
        assert.ok(potential.F <= 2 * exact.swaps, 'same-assignment factor-two bound fails');
        if (potential.q > 0) exceptionalCases++;
        if (exact.swaps === 0) assert.equal(potential.F, 0);
        else if (potential.F / exact.swaps > maximumRatio) {
          maximumRatio = potential.F / exact.swaps;
          worst = { reach, sourceLength, size, assignment, exactSwaps: exact.swaps, exactOps: exact.ops, ...potential };
        }
      }
    }
    console.error(`source-potential R=${reach} total=${size}: ${cases} cases; max ratio ${maximumRatio}`);
  }
  return { status: 'finite exact evidence for the same-assignment potential; not a proved Lean theorem or endpoint optimizer',
    potential: 'F(f)=K(f)+2*c(P_f), where P_f is the virtual source-prefix permutation and c excludes its cycle through the initial top.',
    checks: ['Every prefix cycle stays inside one full assignment cycle.', '2c <= K+q, with q the full source-only two-cycles that omit the initial top.',
      'K+2q <= exact SWAP count.', 'F <= 2*exact SWAP count.'],
    domain: { reaches: [1, 2, 3, 4, 16], totalTokens: '0 through 7', sourceLength: '0 through min(totalTokens,reach+1)',
      endpoints: 'all reachable labelled assignments; distinct token values make the final assignment explicit' },
    searches, cases, exceptionalCases, maximumRatio, worst,
    reproduce: 'node scripts/optimality-source-potential.mjs Bench/evidence-source-potential.json' };
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const report = auditSourcePotential();
  fs.writeFileSync(process.argv[2] ?? 'Bench/evidence-source-potential.json', JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify(report));
}
