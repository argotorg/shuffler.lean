import assert from 'node:assert/strict';
import test from 'node:test';
import fs from 'node:fs';
import { solveJointDual } from './optimality-joint-dual-solver.mjs';
import { checkJointCertificate } from './optimality-joint-dual.mjs';

const fixture = { target: ['a', 'b', 'a'], reach: 1,
  prices: { direct: [['a', 34], ['b', 34]], dup: 1, swap: 1 },
  candidate: { assignment: [0, 2, 1], modes: ['direct', 'dup', 'direct'] } };

test('external solver supplies data checked by exact arithmetic', () => {
  const result = solveJointDual(fixture, { minimumLowerBound: 140 });
  assert.equal(result.status, 'certificate');
  const checked = checkJointCertificate({ ...fixture, certificate: result.certificate });
  assert.equal(checked.status, 'certified');
  assert.equal(BigInt(checked.lowerBoundNumerator), 140n * BigInt(checked.scale));
});

test('a bound above the feasible plan is unsatisfiable', () => {
  assert.equal(solveJointDual(fixture, { minimumLowerBound: 141 }).status, 'infeasible');
});

test('solver errors are not reported as infeasibility', () => {
  const result = solveJointDual(fixture, { solver: '/missing/joint-dual-solver', minimumLowerBound: 140 });
  assert.equal(result.status, 'error');
});

test('the saved source case needs its mandatory hard-value quota', () => {
  const saved = JSON.parse(fs.readFileSync('Bench/evidence-source-joint-dual.json', 'utf8'));
  const result = solveJointDual(saved.instance, { minimumLowerBound: 147 });
  assert.equal(result.status, 'certificate');
  const checked = checkJointCertificate({ ...saved.instance, certificate: result.certificate });
  assert.equal(BigInt(checked.lowerBoundNumerator), 147n * BigInt(checked.scale));
  assert.equal(checked.candidateObjective, '150');
  assert.equal(solveJointDual({ ...saved.instance, hard: [] }, { minimumLowerBound: 147 }).status, 'infeasible');
});
