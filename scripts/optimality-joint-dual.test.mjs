import assert from 'node:assert/strict';
import test from 'node:test';
import { checkJointCertificate } from './optimality-joint-dual.mjs';

const fixture = () => ({ target: ['a', 'b', 'a'], reach: 1,
  prices: { direct: [['a', 34], ['b', 34]], dup: 1, swap: 1 },
  candidate: { assignment: [0, 2, 1], modes: ['direct', 'dup', 'direct'] },
  certificate: { scale: 1, row: [2, 1, 0], column: [1, 0, 1], prefix: [2], upper: [64] } });

test('a supplied dual certifies a nontrivial global plan minimum', () => {
  const result = checkJointCertificate(fixture());
  assert.equal(result.status, 'certified');
  assert.equal(result.candidateObjective, '140');
  assert.equal(result.lowerBoundNumerator, '140');
});

test('integer scaling preserves the same exact rational bound', () => {
  const input = fixture();
  input.certificate = { scale: 3, row: [7, 4, 1], column: [2, -1, 2], prefix: [6], upper: [192] };
  const result = checkJointCertificate(input);
  assert.equal(result.status, 'certified');
  assert.equal(result.lowerBoundNumerator, '420');
  assert.equal(result.scale, '3');
});

test('DUP and SWAP can have different prices', () => {
  const input = fixture();
  input.prices = { direct: [['a', 7], ['b', 4]], dup: 2, swap: 3 };
  input.certificate = { scale: 1, row: [6, 3, 0], column: [3, 0, 3], prefix: [6], upper: [4] };
  const result = checkJointCertificate(input);
  assert.equal(result.status, 'certified');
  assert.equal(result.candidateObjective, '32');
});

test('cheap direct births and first copies retain their full direct cost', () => {
  const input = { target: ['zero', 'zero'], reach: 1,
    prices: { direct: [['zero', 2]], dup: 3, swap: 5 },
    candidate: { assignment: [0, 1], modes: ['direct', 'direct'] },
    certificate: { scale: 1, row: [5, 5], column: [0, 0], prefix: [0], upper: [0] } };
  assert.equal(checkJointCertificate(input).candidateObjective, '8');
  input.candidate.modes[1] = 'dup';
  const result = checkJointCertificate(input);
  assert.equal(result.status, 'lower-bound');
  assert.equal(result.scaledGap, '2');
});

test('invalid dual signs and edge inequalities are rejected', () => {
  for (const [field, values] of [['prefix', [-1]], ['upper', [63]], ['row', [1, 1, 0]]]) {
    const input = fixture(); input.certificate[field] = values;
    assert.throws(() => checkJointCertificate(input));
  }
  const input = fixture(); input.certificate.scale = 0;
  assert.throws(() => checkJointCertificate(input));
});

test('invalid candidate assignments and unavailable DUP births are rejected', () => {
  for (const candidate of [
    { assignment: [0, 0, 1], modes: ['direct', 'dup', 'direct'] },
    { assignment: [1, 2, 0], modes: ['direct', 'direct', 'dup'] },
    { assignment: [0, 2, 1], modes: ['dup', 'dup', 'direct'] },
    { assignment: [0, 1, 2], modes: ['direct', 'direct', 'dup'] }
  ]) { const input = fixture(); input.candidate = candidate; assert.throws(() => checkJointCertificate(input)); }
});

test('empty target has a zero certificate', () => {
  const result = checkJointCertificate({ target: [], reach: 16,
    prices: { direct: [], dup: 3, swap: 1 }, candidate: { assignment: [], modes: [] },
    certificate: { scale: 1, row: [], column: [], prefix: [], upper: [] } });
  assert.equal(result.status, 'certified');
  assert.equal(result.candidateObjective, '0');
});
