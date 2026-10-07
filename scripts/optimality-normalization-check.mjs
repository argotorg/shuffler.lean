#!/usr/bin/env node
/** Check actual Lean normalizer outputs. This script does not normalize traces. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { replay } from './optimality-oracle.mjs';

export function checkNormalization(problem, once, twice) {
  const original = replay(problem, problem.referenceOps);
  const nonSwaps = ops => ops.filter(op => op[0] !== 'swap');
  if (problem.expectedOriginalCost) assert.deepEqual(original.cost, problem.expectedOriginalCost, 'saved original cost differs');
  for (const candidate of [once, twice]) {
    assert.equal(candidate?.status, 'ok', 'normalizer did not return a trace');
    const actual = replay(problem, candidate.ops);
    assert.deepEqual(nonSwaps(candidate.ops), nonSwaps(problem.referenceOps), 'ordered non-SWAP instructions differ');
    assert.deepEqual(actual.added, original.added, 'addition order differs');
    assert.deepEqual(actual.cost, candidate.cost, 'Lean and JS cost differ');
    assert.equal(actual.score, candidate.score, 'Lean and JS score differ');
    assert.ok(actual.cost.gas <= original.cost.gas && actual.cost.bytes <= original.cost.bytes, 'componentwise cost increases');
  }
  return { originalCost: original.cost, normalizedCost: once.cost,
    savedCost: { gas: original.cost.gas - once.cost.gas, bytes: original.cost.bytes - once.cost.bytes },
    removedInstructions: problem.referenceOps.length - once.ops.length,
    idempotent: JSON.stringify(once.ops) === JSON.stringify(twice.ops) };
}

function main() {
  const recordsPath = process.argv[2], summaryPath = process.argv[3];
  const output = process.argv[4] ?? 'Bench/evidence-normalization-production.json';
  if (!recordsPath || !summaryPath) throw new Error('provide production records and summary paths');
  const records = fs.readFileSync(recordsPath, 'utf8').trim().split('\n').filter(Boolean).map(JSON.parse);
  const summary = JSON.parse(fs.readFileSync(summaryPath, 'utf8'));
  const errors = [], nonIdempotent = [], changes = [];
  let savedGas = 0, savedBytes = 0, removedInstructions = 0;
  for (const record of records) {
    try {
      assert.equal(record.modelError, undefined, 'benchmark model disagreement');
      const algorithms = record.production.result.algorithms;
      const result = checkNormalization(record.problem, algorithms['normalize-reference'], algorithms['normalize-reference-twice']);
      if (!result.idempotent) nonIdempotent.push(record.problem.id);
      if (result.removedInstructions > 0) changes.push({ id: record.problem.id, ...result });
      savedGas += result.savedCost.gas; savedBytes += result.savedCost.bytes; removedInstructions += result.removedInstructions;
    } catch (error) { errors.push({ id: record.problem.id, error: error.message }); }
  }
  changes.sort((a, b) => b.removedInstructions - a.removedInstructions);
  const report = { status: 'finite checks of actual production Lean normalization',
    scope: 'The reference traces are saved successful production BBU results and six explicit edge cases. Only the compiled Lean normalizer creates the candidates. JS independently replays both passes and checks endpoints, ordered non-SWAP instructions, ordered additions, componentwise gas/byte cost, and equality of one-pass/two-pass instruction lists.',
    idempotenceStatus: 'Measured only; no general Lean idempotence theorem is claimed.',
    recordsPath, summaryPath, runnerSha256: summary.configuration.runnerSnapshot?.sha256,
    configuration: summary.configuration, cases: records.length, passed: records.length - errors.length,
    changedTraces: changes.length, savedGas, savedBytes, removedInstructions,
    errors, nonIdempotent, changes,
    reproduce: `node scripts/optimality-normalization-check.mjs ${recordsPath} ${summaryPath} ${output}` };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({ ...report, changes: changes.slice(0, 5) }));
  if (errors.length) process.exitCode = 1;
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
