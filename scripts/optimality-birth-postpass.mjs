#!/usr/bin/env node
/** Run only post-passes on saved successful portfolio outputs. */
import fs from 'node:fs';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { assess } from './optimality-birth-postpass-check.mjs';

const runner = process.argv[2] ?? '.lake/build/bin/optimality_bench';
const output = process.argv[3] ?? 'Bench/evidence-birth-postpass-integrated.json';
const stem = process.argv[4] ?? '/tmp/optimality-postpass-integrated';
const digest = path => createHash('sha256').update(fs.readFileSync(path)).digest('hex');
const paths = ['/tmp/optimality-v15-planted.jsonl', '/tmp/optimality-v15-regressions.jsonl',
  '/tmp/optimality-v6-small-20261007.jsonl', '/tmp/optimality-v6-medium-2026100721.jsonl',
  '/tmp/optimality-v6-medium-2026100722.jsonl', '/tmp/optimality-v6-medium-2026100723.jsonl'];
const seen = new Set(), inputs = [];
for (const path of paths) {
  const records = fs.readFileSync(path, 'utf8').trim().split('\n').filter(Boolean).map(JSON.parse);
  for (const record of records) {
    const candidate = record.production?.result?.algorithms?.schedule;
    if (candidate?.status !== 'ok' || record.problem.caps?.swap !== 16) continue;
    if (!path.includes('v15') && record.problem.source.length) continue;
    const p = record.problem;
    const key = JSON.stringify([p.source, p.target, p.missing, p.spills, p.loadWidths, p.weights, p.gasModel, candidate.ops]);
    if (seen.has(key)) continue;
    seen.add(key);
    inputs.push({ ...p, id: `${path.split('/').pop()}:${p.id}`, referenceOps: candidate.ops,
      expectedOriginalCost: candidate.cost, savedPortfolioPath: path,
      savedPortfolioNanos: record.production.elapsedNanos });
  }
}

function run(name, mode, cases) {
  const inputPath = `${stem}-${name}-input.jsonl`, outputPath = `${stem}-${name}-output.jsonl`;
  const timePath = `${stem}-${name}-time.json`;
  const input = cases.map(p => JSON.stringify({ ...p, algorithms: [mode] })).join('\n') + '\n';
  fs.writeFileSync(inputPath, input);
  const start = process.hrtime.bigint();
  const result = spawnSync(runner, [], { input, maxBuffer: 64 * 1024 * 1024, timeout: 120000 });
  const wallMs = Number(process.hrtime.bigint() - start) / 1e6;
  fs.writeFileSync(outputPath, result.stdout);
  fs.writeFileSync(timePath, JSON.stringify({ wallMs, status: result.status, stderr: result.stderr.toString(),
    error: result.error?.message }, null, 2) + '\n');
  const report = assess(inputPath, outputPath, timePath, mode);
  process.stdout.write(JSON.stringify({ mode, cases: report.cases, wallMs, improvements: report.rawScoreImprovements,
    increases: report.rawScoreIncreases }) + '\n');
  return report;
}

const runnerSha256 = digest(runner);
const groups = [run('empty', 'birth-reference', inputs.filter(p => !p.source.length)),
  run('source-cheapest', 'source-cheapest-reference', inputs.filter(p => p.source.length)),
  run('selected', 'postpass-reference', inputs)];
if (digest(runner) !== runnerSha256) throw new Error('runner changed during measurement');
const report = { status: 'independently replayed production post-pass outputs', runner, runnerSha256,
  scope: 'The input instructions are saved actual portfolio results. No portfolio builder, state search, or optimum oracle was rerun. The final helper selects a birth candidate once and retains the incumbent when the candidate is more costly.',
  proofScope: 'For empty sources, competitors can use any assignment with the same ordered birth values. For nonempty sources, competitors share the seed assignment. No output-assignment extraction theorem or global birth-order guarantee is claimed.',
  groups, preservedV15Runner: { path: '/tmp/optimality-bench-normalized-portfolio-v15',
    sha256: digest('/tmp/optimality-bench-normalized-portfolio-v15') },
  reproduce: `node scripts/optimality-birth-postpass.mjs ${runner} ${output} ${stem}` };
fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
