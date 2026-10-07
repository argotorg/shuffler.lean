#!/usr/bin/env node
/** Independently replay saved portfolio traces and actual Lean post-pass outputs. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { createHash } from 'node:crypto';
import { pathToFileURL } from 'node:url';
import { replay } from './optimality-oracle.mjs';

const digest = path => createHash('sha256').update(fs.readFileSync(path)).digest('hex');
const rows = path => fs.readFileSync(path, 'utf8').trim().split('\n').filter(Boolean).map(JSON.parse);
const order = (left, right) => left.score - right.score || left.cost.gas - right.cost.gas || left.cost.bytes - right.cost.bytes;

export function checkPostpass(problem, output, mode) {
  assert.equal(output.result.id, problem.id, 'input and output IDs differ');
  const before = replay(problem, problem.referenceOps);
  assert.deepEqual(before.cost, problem.expectedOriginalCost, 'saved portfolio cost differs');
  const candidate = output.result.algorithms[mode];
  assert.equal(candidate?.status, 'ok', 'post-pass did not return a trace');
  const after = replay(problem, candidate.ops);
  assert.deepEqual(after.cost, candidate.cost, 'Lean and JS costs differ');
  assert.equal(after.score, candidate.score, 'Lean and JS scores differ');
  assert.deepEqual(after.added, before.added, 'ordered birth values differ');
  if (mode === 'birth-reference') assert.ok(after.score <= before.score, 'empty-source score increases');
  if (mode === 'source-reference') {
    const methods = ops => ops.filter(op => op[0] !== 'swap').map(op => op[0]);
    assert.deepEqual(methods(candidate.ops), methods(problem.referenceOps), 'source birth methods differ');
  }
  const keepCandidate = order(after, before) < 0;
  return { id: problem.id, sourceSize: problem.source.length, targetSize: problem.target.length,
    beforeCost: before.cost, candidateCost: after.cost, beforeScore: before.score, candidateScore: after.score,
    selectedCost: keepCandidate ? after.cost : before.cost,
    selectedScore: keepCandidate ? after.score : before.score,
    measuredMs: output.elapsedNanos / 1e6,
    savedPortfolioMs: problem.savedPortfolioNanos / 1e6,
    keepCandidate };
}

function assess(inputPath, outputPath, timePath, mode) {
  const input = rows(inputPath), output = rows(outputPath);
  assert.equal(input.length, output.length, 'output row count differs');
  const results = input.map((problem, index) => checkPostpass(problem, output[index], mode));
  const times = results.map(r => r.measuredMs).sort((a, b) => a - b);
  const time = JSON.parse(fs.readFileSync(timePath, 'utf8'));
  assert.equal(time.status, 0, 'runner failed');
  const changes = results.filter(r => r.keepCandidate);
  return { mode, cases: input.length, inputPath, inputSha256: digest(inputPath),
    outputPath, outputSha256: digest(outputPath), wallMs: time.wallMs,
    timingScope: 'Each measured case includes production replay, the post-pass, output replay, cost and certificate reporting, and JSON serialization. It excludes the saved portfolio run.',
    medianMs: times[Math.floor(times.length / 2)], p95Ms: times[Math.floor(times.length * 0.95)], maxMs: times.at(-1),
    maxSourceSize: Math.max(...input.map(p => p.source.length)), maxTargetSize: Math.max(...input.map(p => p.target.length)),
    rawScoreImprovements: results.filter(r => r.candidateScore < r.beforeScore).length,
    rawScoreIncreases: results.filter(r => r.candidateScore > r.beforeScore).length,
    selectedScoreIncreases: results.filter(r => r.selectedScore > r.beforeScore).length,
    selectedGasSaved: changes.reduce((sum, r) => sum + r.beforeCost.gas - r.selectedCost.gas, 0),
    selectedBytesSaved: changes.reduce((sum, r) => sum + r.beforeCost.bytes - r.selectedCost.bytes, 0),
    sourceRecords: [...new Set(input.map(p => p.savedPortfolioPath))].map(path => ({ path, sha256: digest(path) })),
    changes };
}

function main() {
  const runner = process.argv[2] ?? '/tmp/optimality-bench-postpass-v1';
  const output = process.argv[3] ?? 'Bench/evidence-birth-postpass.json';
  const groups = [assess('/tmp/postpass-empty-input.jsonl', '/tmp/postpass-empty-output.jsonl',
    '/tmp/postpass-empty-time.json', 'birth-reference'),
    assess('/tmp/postpass-source-input.jsonl', '/tmp/postpass-source-output.jsonl',
      '/tmp/postpass-source-time.json', 'source-reference')];
  const report = { status: 'checked actual production outputs from saved portfolio traces',
    scope: 'No portfolio builder or optimality oracle was rerun. The empty-source pass optimizes a fixed birth word. The source pass preserves the supplied labelled assignment and birth methods; its raw increases are rejected by the incumbent comparison.',
    runner, runnerSha256: digest(runner), groups,
    preservedV15Runner: { path: '/tmp/optimality-bench-normalized-portfolio-v15',
      sha256: digest('/tmp/optimality-bench-normalized-portfolio-v15') },
    proofScope: 'No new global factor-two claim follows from these finite checks. Empty fixed-word and general supplied-assignment guarantees remain separate.',
    reproduce: `node scripts/optimality-birth-postpass-check.mjs ${runner} ${output}` };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  process.stdout.write(JSON.stringify(report, null, 2) + '\n');
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
