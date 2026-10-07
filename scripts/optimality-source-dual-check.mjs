#!/usr/bin/env node
/** One saved nonempty-source witness; no production scheduler or oracle search. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { checkJointCertificate } from './optimality-joint-dual.mjs';
import { solveJointDual } from './optimality-joint-dual-solver.mjs';
import { baseline, normalizeCase, opCost, replay, score } from './optimality-oracle.mjs';

export function sourceWitnessInstance(problem, witness) {
  assert.equal(problem.caps.dup, problem.caps.swap, 'joint model requires a common DUP and SWAP reach');
  replay(problem, witness);
  const rows = problem.source.map(value => ({ value, kind: 'source' }));
  const stack = problem.source.map((_, index) => index);
  for (const op of witness) {
    if (op[0] === 'swap') {
      const lower = stack.length - op[1] - 1;
      [stack[lower], stack[stack.length - 1]] = [stack.at(-1), stack[lower]];
    } else {
      assert.ok(['dup', 'push', 'load'].includes(op[0]), 'unsupported birth instruction');
      const value = op[0] === 'dup' ? rows[stack[stack.length - op[1]]].value :
        op[0] === 'load' ? `v:${op[1]}` : op[1];
      stack.push(rows.length); rows.push({ value, kind: op[0] });
    }
  }
  const assignment = Array(problem.target.length);
  stack.forEach((birth, output) => { assignment[birth] = output; });
  const values = [...new Set(problem.target)];
  const hard = values.filter(value => value.startsWith('v:') && !problem.spills.includes(Number(value.slice(2))));
  const dup = score(problem, opCost(problem, ['dup', 1]));
  const prices = { dup, swap: score(problem, opCost(problem, ['swap', 1])),
    direct: values.map(value => [value, hard.includes(value) ? dup : score(problem,
      opCost(problem, value.startsWith('v:') ? ['load', Number(value.slice(2))] : ['push', value]))]) };
  return { source: problem.source, target: problem.target, hard, reach: problem.caps.swap, prices,
    candidate: { assignment, modes: rows.slice(problem.source.length).map(row => row.kind === 'dup' ? 'dup' : 'direct') } };
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-source-joint-dual.json';
  const source = 'Bench/evidence-static-gap-exact-optimum.json';
  const saved = JSON.parse(fs.readFileSync(source, 'utf8')), problem = normalizeCase(saved.problem);
  const witness = saved.schedule.ops, observed = replay(problem, witness), base = baseline(problem);
  const instance = sourceWitnessInstance(problem, witness), threshold = observed.score + base;
  const solved = solveJointDual(instance, { minimumLowerBound: threshold });
  assert.equal(solved.status, 'certificate', JSON.stringify(solved));
  const checked = checkJointCertificate({ ...instance, certificate: solved.certificate });
  const scale = BigInt(checked.scale), lower = BigInt(checked.lowerBoundNumerator);
  assert.ok(scale * BigInt(threshold) <= lower);
  const report = { status: 'one saved source witness with an exactly checked finite dual and a Lean trace-bound regression',
    source, identity: saved.identity.plantedId,
    scope: 'Replays the saved 81-cost schedule. Hard-value gaps impose mandatory quotas; source rows emit no code and preserve their values. No scheduler rerun, broad oracle expansion, or new exact optimum claim.',
    problem: saved.problem, witness, observed, baseline: base, surplusThreshold: threshold,
    savedOracleScore: saved.oracle.score,
    leanRegression: 'Tests.OptimalitySourceDual; checks the saved operations and coefficients, derives the mandatory quota from SourcePlan availability, and proves the all-trace surplus bound',
    instance, solved, checked,
    certifiesTwiceSurplusNumerically: scale * BigInt(threshold) <= lower,
    certifiesExactScoreNumerically: 2n * scale * BigInt(observed.score) <= lower,
    reproduce: `Z3_BIN=<z3-path> node scripts/optimality-source-dual-check.mjs ${output}` };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({ baseline: base, score: observed.score, threshold,
    lowerBound: solved.lowerBound, candidateObjective: checked.candidateObjective,
    certifiesTwiceSurplusNumerically: report.certifiesTwiceSurplusNumerically,
    certifiesExactScoreNumerically: report.certifiesExactScoreNumerically, milliseconds: solved.milliseconds }));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
