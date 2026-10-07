#!/usr/bin/env node
/** Offline LP relaxation of joint birth words and endpoint assignments. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { spawnSync } from 'node:child_process';
import { pathToFileURL } from 'node:url';
import { deadlineJobs } from './optimality-birth-matching.mjs';
import { consecutiveIntervals } from './optimality-interval-realizability.mjs';
import { exactPinnedSets } from './optimality-pinned-quotas.mjs';

const sum = terms => terms.length ? `(+ ${terms.join(' ')})` : '0.0';
const gcd = (a, b) => b === 0n ? a : gcd(b, a % b);
const rational = (numerator, denominator = 1n) => {
  assert.notEqual(denominator, 0n);
  const sign = denominator < 0n ? -1n : 1n, factor = gcd(numerator < 0n ? -numerator : numerator, denominator * sign);
  return { n: numerator * sign / factor, d: denominator * sign / factor };
};
const add = (a, b) => rational(a.n * b.d + b.n * a.d, a.d * b.d);
const rationalSum = values => values.reduce(add, rational(0n));
const equal = (a, b) => a.n * b.d === b.n * a.d;
const atLeast = (a, b) => a.n * b.d >= b.n * a.d;
const display = a => `${a.n}/${a.d}`;

function parseForms(text) {
  const tokens = text.match(/\(|\)|[^\s()]+/g) ?? []; let index = 0;
  const parse = () => {
    const token = tokens[index++];
    if (token !== '(') return token;
    const children = [];
    while (tokens[index] !== ')') { assert.ok(index < tokens.length); children.push(parse()); }
    index++; return children;
  };
  const forms = []; while (index < tokens.length) forms.push(parse()); return forms;
}

function readRational(form) {
  if (Array.isArray(form)) {
    if (form[0] === '-') { const value = readRational(form[1]); return rational(-value.n, value.d); }
    assert.equal(form[0], '/');
    const a = readRational(form[1]), b = readRational(form[2]); return rational(a.n * b.d, a.d * b.n);
  }
  const match = /^(-?\d+)(?:\.(\d+))?$/.exec(form); assert.ok(match, `unsupported rational ${form}`);
  const denominator = 10n ** BigInt(match[2]?.length ?? 0);
  return rational(BigInt(match[1]) * denominator + BigInt(match[2] ?? 0) * (match[1].startsWith('-') ? -1n : 1n), denominator);
}

export function solveQuotaLP(target, reach, jobs, { solver = process.env.Z3_BIN ?? 'z3', timeoutMs = 10000, retention = null, swapPrice = 1, edgeCosts = null, integral = false } = {}) {
  assert.ok(Number.isInteger(reach) && reach > 0);
  assert.deepEqual(jobs.map(job => job.value).sort(), [...target].sort());
  const size = target.length, names = target.map((_, birth) => target.map((_, output) => `x_${birth}_${output}`));
  const lines = [`(set-option :timeout ${timeoutMs})`, `(set-logic ${integral ? 'QF_LIRA' : 'QF_LRA'})`];
  const constrain = expression => lines.push(`(assert ${expression})`);
  names.forEach((row, birth) => row.forEach((name, output) => {
    lines.push(`(declare-const ${name} ${integral ? 'Int' : 'Real'})`); constrain(`(>= ${name} 0.0)`);
    if (birth > output + reach) constrain(`(= ${name} 0.0)`);
  }));
  for (let index = 0; index < size; index++) {
    constrain(`(= ${sum(names[index])} 1.0)`);
    constrain(`(= ${sum(names.map(row => row[index]))} 1.0)`);
  }
  for (const value of new Set(target)) for (let cut = 0; cut < size; cut++) {
    const required = jobs.filter(job => job.value === value && job.deadline <= cut).length;
    constrain(`(>= ${sum(names.flatMap((row, birth) => birth > cut ? [] : row.filter((_, output) => target[output] === value)))} ${required})`);
  }
  const retentionNames = (retention ?? []).map((_, index) => `y_${index}`);
  (retention ?? []).forEach((entry, index) => {
    assert.ok(Number.isSafeInteger(entry.premium) && entry.premium >= 0);
    const name = retentionNames[index], cut = entry.previous + reach;
    lines.push(`(declare-const ${name} ${integral ? 'Int' : 'Real'})`); constrain(`(and (<= 0.0 ${name}) (<= ${name} 1.0))`);
    constrain(`(>= ${sum(names.flatMap((row, birth) => birth > cut ? [] : row.filter((_, output) => target[output] === entry.value)))} (+ ${entry.ordinal - 1} ${name}))`);
  });
  const moved = sum(names.flatMap((row, birth) => row.filter((_, output) => birth !== output)));
  lines.push(`(define-fun E () Real ${integral && size > 1 ? `(to_real ${moved})` : moved})`);
  const objectiveName = retention === null ? edgeCosts === null ? 'E' : 'W' : 'J2';
  if (edgeCosts !== null) {
    assert.equal(retention, null, 'generic edge costs and retention are separate experiments');
    assert.ok(edgeCosts.length === size && edgeCosts.every(row => row.length === size && row.every(cost => Number.isSafeInteger(cost) && cost >= 0)));
    const weighted = sum(names.flatMap((row, birth) => row.map((name, output) => `(* ${edgeCosts[birth][output]} ${name})`)));
    lines.push(`(define-fun W () Real ${integral && size > 0 ? `(to_real ${weighted})` : weighted})`);
  }
  if (retention !== null) {
    assert.ok(Number.isSafeInteger(swapPrice) && swapPrice > 0);
    const premiums = retention.map((entry, index) => `(* ${2 * entry.premium} (- 1.0 ${retentionNames[index]}))`);
    lines.push(`(define-fun J2 () Real (+ ${sum(premiums)} (* ${swapPrice} E)))`);
  }
  lines.push(`(minimize ${objectiveName})`, '(check-sat)', `(get-value (E ${objectiveName === 'E' ? '' : objectiveName} ${names.flat().join(' ')} ${retentionNames.join(' ')}))`);
  const encoded = lines.join('\n') + '\n';
  const started = performance.now(), solved = spawnSync(solver, ['-in', '-smt2'], { input: encoded, encoding: 'utf8', timeout: timeoutMs + 1000 });
  const forms = parseForms(solved.stdout ?? ''), status = forms[0], milliseconds = performance.now() - started;
  if (status === 'unsat') return { status: 'infeasible', milliseconds };
  if (status !== 'sat') return { status: status === 'unknown' ? 'unknown' : 'error', stdout: solved.stdout, stderr: solved.stderr, error: solved.error?.message, milliseconds };
  const bindings = new Map(forms[1].map(([name, form]) => [name, readRational(form)]));
  const matrix = names.map(row => row.map(name => bindings.get(name))), objective = bindings.get(objectiveName), movedValue = bindings.get('E');
  const zero = rational(0n), one = rational(1n);
  for (let birth = 0; birth < size; birth++) {
    assert.ok(equal(rationalSum(matrix[birth]), one), 'LP row sum differs');
    assert.ok(equal(rationalSum(matrix.map(row => row[birth])), one), 'LP column sum differs');
    for (let output = 0; output < size; output++) {
      assert.ok(atLeast(matrix[birth][output], zero), 'LP edge is negative');
      if (birth > output + reach) assert.ok(equal(matrix[birth][output], zero), 'LP edge misses its endpoint deadline');
    }
  }
  for (const value of new Set(target)) for (let cut = 0; cut < size; cut++) {
    const required = jobs.filter(job => job.value === value && job.deadline <= cut).length;
    const total = rationalSum(matrix.flatMap((row, birth) => birth > cut ? [] : row.filter((_, output) => target[output] === value)));
    assert.ok(atLeast(total, rational(BigInt(required))), 'LP generation quota fails');
  }
  assert.ok(equal(rationalSum(matrix.flatMap((row, birth) => row.filter((_, output) => birth !== output))), movedValue), 'LP moved support differs');
  const retentionValues = retentionNames.map(name => bindings.get(name));
  (retention ?? []).forEach((entry, index) => {
    const value = retentionValues[index], cut = entry.previous + reach;
    assert.ok(atLeast(value, zero) && atLeast(one, value), 'LP retention is outside its bounds');
    const total = rationalSum(matrix.flatMap((row, birth) => birth > cut ? [] : row.filter((_, output) => target[output] === entry.value)));
    assert.ok(atLeast(total, add(rational(BigInt(entry.ordinal - 1)), value)), 'LP retention quota fails');
  });
  if (retention !== null) {
    const premiumTotal = rationalSum(retention.map((entry, index) => rational(2n * BigInt(entry.premium) * (retentionValues[index].d - retentionValues[index].n), retentionValues[index].d)));
    assert.ok(equal(add(premiumTotal, rational(BigInt(swapPrice) * movedValue.n, movedValue.d)), objective), 'LP retention objective differs');
  }
  if (edgeCosts !== null) {
    const edgeTotal = rationalSum(matrix.flatMap((row, birth) => row.map((value, output) => rational(BigInt(edgeCosts[birth][output]) * value.n, value.d))));
    assert.ok(equal(edgeTotal, objective), 'LP edge objective differs');
  }
  if (integral) assert.ok([...matrix.flat(), ...retentionValues].every(value => value.d === 1n), 'integer model has a fractional entry');
  return { status: 'optimal', objective: Number(objective.n) / Number(objective.d), exactObjective: display(objective),
    moved: Number(movedValue.n) / Number(movedValue.d), exactMoved: display(movedValue), retention: retentionValues.map(display),
    matrix: matrix.map(row => row.map(display)), fractionalEntries: [...matrix.flat(), ...retentionValues].filter(value => value.d !== 1n).length, milliseconds };
}

function* canonicalWords(size, prefix = []) {
  if (prefix.length === size) { yield prefix; return; }
  for (const value of ['a', 'b', 'c'].slice(0, Math.min(3, new Set(prefix).size + 1))) yield* canonicalWords(size, [...prefix, value]);
}

function main() {
  const output = process.argv[2] ?? 'Bench/evidence-quota-lp.json';
  let cases = 0, trivialZero = 0, solverCases = 0, infeasible = 0, fractionalModels = 0;
  const gaps = [], failures = [];
  outer: for (let size = 0; size <= 7; size++) for (const reach of [1, 2, 3, 16]) {
    for (const target of canonicalWords(size)) {
      const intervals = consecutiveIntervals(target), all = 2 ** intervals.length - 1;
      const masks = [all, ...Array.from({ length: all }, (_, mask) => mask)];
      for (const mask of masks) {
        const selected = intervals.flatMap((_, index) => mask & 2 ** index ? [index] : []);
        const jobs = deadlineJobs([], target, reach, selected).map(job => ({ value: job.value, deadline: job.deadline - 1 }));
        const exact = exactPinnedSets(target, reach, jobs), cardinalities = exact.feasible.flatMap((feasible, mask) => feasible ? [mask.toString(2).replaceAll('0', '').length] : []);
        const minimumE = cardinalities.length ? size - Math.max(...cardinalities) : null;
        cases++;
        if (minimumE === 0) { trivialZero++; continue; }
        const result = solveQuotaLP(target, reach, jobs); solverCases++;
        if (result.status === 'infeasible') {
          infeasible++;
          if (minimumE !== null) failures.push({ target, reach, selected, minimumE, result });
          continue;
        }
        if (result.status !== 'optimal') { failures.push({ target, reach, selected, minimumE, result }); continue; }
        if (result.fractionalEntries) fractionalModels++;
        if (minimumE === null || result.objective < minimumE) {
          gaps.push({ target, reach, selected, jobs, minimumE, result }); break outer;
        }
        if (result.objective !== minimumE) failures.push({ target, reach, selected, minimumE, result });
      }
    }
    console.error(`quota LP n=${size} R=${reach}: ${cases} cases, ${solverCases} solver runs, ${gaps.length} gaps`);
  }
  const report = {
    status: gaps.length ? 'finite fractional-gap witness for the natural endpoint-assignment LP' : 'finite LP comparison; no integrality theorem claimed',
    relaxation: 'Variables x[b,j]>=0 have each row and column sum 1, and x[b,j]=0 when b>j+R. For each value v and cut k, sum x[b,j] over b<=k and target[j]=v is at least the count of generation jobs for v due through k. The objective is E=sum x[b,j] over b!=j. Generation matching remains separate from endpoint labels.',
    check: 'Integer optimum is exhaustive over all endpoint permutations and separate sorted generation-deadline matches. LP models are checked with exact BigInt rational arithmetic. A zero integer optimum proves zero LP optimum from nonnegative objective without a solver call. The experiment stops at the first fractional objective or feasibility gap.',
    domain: { maximumLength: 7, reaches: [1, 2, 3, 16], targets: 'canonical words with at most 3 values', retention: 'all subsets, with all-reuse tested first for each target' },
    solver: process.env.Z3_BIN ?? 'z3', cases, trivialZero, solverCases, infeasible, fractionalModels, gaps, failures,
    reproduce: `Z3_BIN=<z3-path> node scripts/optimality-quota-lp.mjs ${output}`
  };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n'); console.log(JSON.stringify(report));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
