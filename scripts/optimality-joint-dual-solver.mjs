#!/usr/bin/env node
/** Offline external certificate search. Every returned coefficient is untrusted. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { spawnSync } from 'node:child_process';
import { pathToFileURL } from 'node:url';
import { consecutiveIntervals } from './optimality-interval-realizability.mjs';
import { checkJointCertificate } from './optimality-joint-dual.mjs';
import { extractAssignment } from './optimality-assignment-realizer.mjs';
import { baseline, normalizeCase, opCost, replay, score } from './optimality-oracle.mjs';

const sum = terms => terms.length ? `(+ ${terms.join(' ')})` : '0';
const gcd = (left, right) => right === 0n ? left : gcd(right, left % right);
const rational = (n, d = 1n) => {
  assert.notEqual(d, 0n);
  if (d < 0n) { n = -n; d = -d; }
  const factor = gcd(n < 0n ? -n : n, d);
  return { n: n / factor, d: d / factor };
};
function forms(source) {
  const tokens = source.match(/\(|\)|[^\s()]+/g) ?? []; let cursor = 0;
  const read = () => {
    const token = tokens[cursor++];
    if (token !== '(') return token;
    const result = [];
    while (tokens[cursor] !== ')') { assert.ok(cursor < tokens.length, 'unclosed solver form'); result.push(read()); }
    cursor++; return result;
  };
  const result = []; while (cursor < tokens.length) result.push(read()); return result;
}
function coefficient(form) {
  if (Array.isArray(form)) {
    if (form[0] === '-') { const value = coefficient(form[1]); return rational(-value.n, value.d); }
    assert.equal(form[0], '/');
    const left = coefficient(form[1]), right = coefficient(form[2]);
    return rational(left.n * right.d, left.d * right.n);
  }
  const match = /^(-?\d+)(?:\.(\d+))?$/.exec(form); assert.ok(match, 'unsupported solver number');
  const denominator = 10n ** BigInt(match[2]?.length ?? 0);
  return rational(BigInt(match[1]) * denominator + BigInt(match[2] ?? 0) * (match[1].startsWith('-') ? -1n : 1n), denominator);
}

export function solveJointDual({ target, reach, prices }, {
  solver = process.env.Z3_BIN ?? 'z3', timeoutMs = 30000, minimumLowerBound = null
} = {}) {
  assert.ok(Number.isSafeInteger(reach) && reach >= 1);
  assert.ok(minimumLowerBound === null || Number.isSafeInteger(minimumLowerBound));
  const direct = new Map(prices.direct), size = target.length;
  assert.ok([prices.dup, prices.swap, ...direct.values()].every(price => Number.isSafeInteger(price) && price >= 0));
  assert.ok(target.every(value => direct.has(value)), 'missing direct price');
  const gaps = consecutiveIntervals(target).map(gap => ({ ...gap,
    required: target.slice(0, gap.start + 1).filter(value => value === gap.value).length,
    reward: 2 * Math.max(direct.get(gap.value) - prices.dup, 0) }));
  const names = { row: target.map((_, index) => `a_${index}`), column: target.map((_, index) => `b_${index}`),
    prefix: gaps.map((_, index) => `l_${index}`), upper: gaps.map((_, index) => `m_${index}`) };
  const lines = [`(set-option :timeout ${timeoutMs})`, '(set-logic QF_LRA)'];
  for (const name of Object.values(names).flat()) lines.push(`(declare-const ${name} Real)`);
  for (const name of [...names.prefix, ...names.upper]) lines.push(`(assert (>= ${name} 0))`);
  for (let birth = 0; birth < size; birth++) for (let output = Math.max(0, birth - reach); output < size; output++) {
    const weights = gaps.flatMap((gap, index) => gap.value === target[output] && birth <= gap.start + reach ? [names.prefix[index]] : []);
    lines.push(`(assert (>= (- (+ ${names.row[birth]} ${names.column[output]}) ${sum(weights)}) ${birth === output ? prices.swap : 0}))`);
  }
  gaps.forEach((gap, index) => lines.push(`(assert (>= (+ ${names.prefix[index]} ${names.upper[index]}) ${gap.reward}))`));
  const constant = 2 * target.reduce((total, value) => total + direct.get(value), 0) + prices.swap * size;
  const upper = `(+ ${sum(names.row)} ${sum(names.column)} (- ${sum(gaps.map((gap, index) => `(* ${gap.required} ${names.prefix[index]})`))}) ${sum(names.upper)})`;
  lines.push(`(define-fun lower () Real (- ${constant} ${upper}))`);
  if (minimumLowerBound === null) lines.push('(maximize lower)');
  else lines.push(`(assert (>= lower ${minimumLowerBound}))`);
  lines.push('(check-sat)', `(get-value (lower ${Object.values(names).flat().join(' ')}))`);
  const started = performance.now();
  const result = spawnSync(solver, ['-in', '-smt2'], { input: lines.join('\n') + '\n', encoding: 'utf8', timeout: timeoutMs + 1000 });
  const parsed = forms(result.stdout ?? ''), status = parsed[0], milliseconds = performance.now() - started;
  if (status === 'unsat') return { status: 'infeasible', milliseconds };
  if (status !== 'sat') return { status: status === 'unknown' ? 'unknown' : 'error', milliseconds,
    error: result.error?.message, stdout: result.stdout, stderr: result.stderr };
  const values = new Map(parsed[1].map(([name, value]) => [name, coefficient(value)]));
  const scale = [...values.values()].reduce((total, value) => total / gcd(total, value.d) * value.d, 1n);
  const certificate = { scale: String(scale), ...Object.fromEntries(Object.entries(names).map(([field, list]) =>
    [field, list.map(name => { const value = values.get(name); return String(value.n * (scale / value.d)); })])) };
  const lower = values.get('lower');
  return { status: 'certificate', certificate, lowerBound: `${lower.n}/${lower.d}`, milliseconds,
    mode: minimumLowerBound === null ? 'optimized external dual; optimality not trusted' : 'external feasibility at the requested bound' };
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-periodic-joint-dual.json';
  const source = 'Bench/evidence-carrier-r16-relaxation-gap.json';
  const saved = JSON.parse(fs.readFileSync(source, 'utf8')), problem = normalizeCase(saved.records[0].problem);
  const witness = problem.referenceOps, observed = replay(problem, witness), extracted = extractAssignment(problem, witness);
  const prices = { direct: [...new Set(problem.target)].map(value => [value,
    score(problem, opCost(problem, ['load', Number(value.slice(2))]))]),
    dup: score(problem, opCost(problem, ['dup', 1])), swap: score(problem, opCost(problem, ['swap', 1])) };
  const candidate = { assignment: extracted.assignment, modes: extracted.births.map(birth => birth.kind === 'dup' ? 'dup' : 'direct') };
  const instance = { target: problem.target, reach: problem.caps.swap, prices, candidate };
  const base = baseline(problem), threshold = observed.score + base;
  const solved = solveJointDual(instance, { minimumLowerBound: threshold });
  assert.equal(solved.status, 'certificate', JSON.stringify(solved));
  const checked = checkJointCertificate({ ...instance, certificate: solved.certificate });
  const scale = BigInt(checked.scale), lower = BigInt(checked.lowerBoundNumerator);
  assert.ok(scale * BigInt(threshold) <= lower, 'dual does not certify the requested surplus bound');
  const report = {
    status: 'one saved production witness with an externally supplied and exactly checked joint dual',
    source, scope: 'No production scheduler rerun, broad oracle expansion, or exact optimum claim. The saved trace is replayed, its assignment is extracted, and all dual coefficients are checked with exact integers.',
    solver: process.env.Z3_BIN ?? 'z3',
    leanRegression: 'Tests.OptimalityPeriodicDual; the saved operations and integer coefficients are checked independently by Lean',
    problem, witness, observed, baseline: base, surplusThreshold: threshold,
    instance, solved, checked,
    certifiesTwiceSurplus: scale * BigInt(threshold) <= lower,
    certifiesExactScore: 2n * scale * BigInt(observed.score) <= lower,
    replayScore: observed.score,
    reproduce: `Z3_BIN=<z3-path> node scripts/optimality-joint-dual-solver.mjs ${output}`
  };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({ baseline: base, score: observed.score, threshold,
    lowerBound: solved.lowerBound, candidateObjective: checked.candidateObjective,
    certifiesTwiceSurplus: report.certifiesTwiceSurplus, certifiesExactScore: report.certifiesExactScore,
    milliseconds: solved.milliseconds }));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
