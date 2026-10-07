#!/usr/bin/env node
/** Bounded offline trace search. Each fresh variable has one LOAD budget. */
import fs from 'node:fs';
import { spawnSync } from 'node:child_process';
import { pathToFileURL } from 'node:url';
import { normalizeCase, replay } from './optimality-oracle.mjs';

const sum = terms => terms.length ? `(+ ${terms.join(' ')})` : '0';

export function encodeBoundedTrace(input, swapBudget, { timeoutMs = 60000, fixedOps = null } = {}) {
  const problem = normalizeCase(input), values = [...new Set(problem.target)], size = problem.target.length;
  if (problem.source.length || values.some(value => !value.startsWith('v:') || !problem.spills.includes(Number(value.slice(2)))) ||
      !Number.isInteger(swapBudget) || swapBudget < 0) throw new Error('unsupported bounded-trace input');
  const slots = size + swapBudget, reach = problem.caps.swap;
  const lines = [`(set-option :timeout ${timeoutMs})`, '(set-option :produce-models true)', '(set-logic QF_AUFLIA)'];
  const assert = expression => lines.push(`(assert ${expression})`);
  for (let t = 0; t <= slots; t++) {
    lines.push(`(declare-const h_${t} Int)`, `(declare-const s_${t} (Array Int Int))`);
    assert(`(and (<= 0 h_${t}) (<= h_${t} ${size}))`);
    for (let i = 0; i < size; i++) assert(`(=> (< ${i} (- h_${t} ${reach + 1})) (= (select s_${t} ${i}) ${values.indexOf(problem.target[i])}))`);
  }
  assert('(= h_0 0)'); assert('(= s_0 ((as const (Array Int Int)) (- 1)))');
  for (let t = 0; t < slots; t++) lines.push(`(declare-const op_${t} Int)`, `(declare-const depth_${t} Int)`, `(declare-const value_${t} Int)`);
  for (let t = 0; t < slots; t++) {
    const op = `op_${t}`, depth = `depth_${t}`, value = `value_${t}`, height = `h_${t}`, stack = `s_${t}`;
    assert(`(and (<= 0 ${op}) (<= ${op} 3))`);
    assert(`(=> (= ${op} 0) (and (< ${height} ${size}) (= ${depth} 0) (<= 0 ${value}) (< ${value} ${values.length})))`);
    assert(`(=> (= ${op} 1) (and (< ${height} ${size}) (<= 1 ${depth}) (<= ${depth} ${reach}) (<= ${depth} ${height}) (= ${value} 0)))`);
    assert(`(=> (= ${op} 2) (and (<= 1 ${depth}) (<= ${depth} ${reach}) (< ${depth} ${height}) (= ${value} 0)))`);
    assert(`(=> (= ${op} 3) (and (= ${depth} 0) (= ${value} 0)))`);
    if (t + 1 < slots) assert(`(=> (= ${op} 3) (= op_${t + 1} 3))`);
    const born = `(ite (= ${op} 0) ${value} (select ${stack} (- ${height} ${depth})))`;
    lines.push(`(define-fun born_${t} () Int ${born})`);
    assert(`(= h_${t + 1} (+ ${height} (ite (<= ${op} 1) 1 0)))`);
    const lower = `(- ${height} ${depth} 1)`, upper = `(- ${height} 1)`;
    const swapped = `(store (store ${stack} ${lower} (select ${stack} ${upper})) ${upper} (select ${stack} ${lower}))`;
    assert(`(= s_${t + 1} (ite (<= ${op} 1) (store ${stack} ${height} born_${t}) (ite (= ${op} 2) ${swapped} ${stack})))`);
  }
  for (let value = 0; value < values.length; value++) {
    assert(`(= ${sum(Array.from({ length: slots }, (_, t) => `(ite (and (= op_${t} 0) (= value_${t} ${value})) 1 0)`))} 1)`);
    const count = problem.target.filter(item => item === values[value]).length;
    assert(`(= ${sum(Array.from({ length: slots }, (_, t) => `(ite (and (<= op_${t} 1) (= born_${t} ${value})) 1 0)`))} ${count})`);
  }
  assert(`(<= ${sum(Array.from({ length: slots }, (_, t) => `(ite (= op_${t} 2) 1 0)`))} ${swapBudget})`);
  assert(`(= h_${slots} ${size})`);
  problem.target.forEach((value, index) => assert(`(= (select s_${slots} ${index}) ${values.indexOf(value)})`));
  if (fixedOps !== null) {
    if (fixedOps.length > slots) throw new Error('fixed trace exceeds bounded slots');
    for (let t = 0; t < slots; t++) {
      const op = fixedOps[t], kind = op === undefined ? 3 : op[0] === 'load' ? 0 : op[0] === 'dup' ? 1 : 2;
      assert(`(= op_${t} ${kind})`);
      if (kind === 0) assert(`(= value_${t} ${values.indexOf(`v:${op[1]}`)})`);
      if (kind === 1 || kind === 2) assert(`(= depth_${t} ${op[1]})`);
    }
  }
  lines.push('(check-sat)', `(get-value (${Array.from({ length: slots }, (_, t) => `op_${t} depth_${t} value_${t}`).join(' ')}))`);
  return { problem, values, slots, swapBudget, timeoutMs, text: lines.join('\n') + '\n' };
}

export function solveBoundedTrace(encoded, { solver = process.env.Z3_BIN ?? 'z3' } = {}) {
  const started = performance.now();
  const result = spawnSync(solver, ['-in', '-smt2'], { input: encoded.text, encoding: 'utf8', timeout: encoded.timeoutMs + 5000, maxBuffer: 16 * 1024 * 1024 });
  const status = /^(sat|unsat|unknown)$/m.exec(result.stdout ?? '')?.[1] ?? 'error';
  const output = { status, exitCode: result.status, signal: result.signal, stderr: result.stderr,
    milliseconds: performance.now() - started, stdout: result.stdout, error: result.error?.message };
  if (status === 'sat') {
    const bindings = new Map([...result.stdout.matchAll(/\((op|depth|value)_(\d+) (\d+)\)/g)]
      .map(match => [`${match[1]}_${match[2]}`, Number(match[3])]));
    const ops = [];
    for (let t = 0; t < encoded.slots; t++) {
      const kind = bindings.get(`op_${t}`), depth = bindings.get(`depth_${t}`), value = bindings.get(`value_${t}`);
      if (kind === 0) ops.push(['load', Number(encoded.values[value].slice(2))]);
      else if (kind === 1) ops.push(['dup', depth]);
      else if (kind === 2) ops.push(['swap', depth]);
      else if (kind !== 3) throw new Error('incomplete SMT model');
    }
    output.ops = ops; output.replay = replay(encoded.problem, ops);
    output.swaps = ops.filter(op => op[0] === 'swap').length;
  }
  return output;
}

function main() {
  const reach = Number(process.argv[2] ?? 16), bound = Number(process.argv[3] ?? 4);
  const output = process.argv[4] ?? `/tmp/carrier-smt-r${reach}-s${bound}.json`;
  const timeoutMs = Number(process.argv[5] ?? 60000), cycle = Array.from({ length: reach - 1 }, (_, i) => `v:${43 + i}`);
  const problem = normalizeCase({ source: [], target: ['v:42', ...cycle, ...cycle, ...cycle, 'v:42'],
    spills: Array.from({ length: reach }, (_, i) => 42 + i), caps: { swap: reach, dup: reach } });
  const encoded = encodeBoundedTrace(problem, bound, { timeoutMs });
  fs.writeFileSync(output + '.smt2', encoded.text);
  const result = solveBoundedTrace(encoded);
  const report = { scope: 'Finite SMT search of every trace with at most the given SWAP budget, exact target, and exactly one LOAD per fresh kind. DUP uses ordinary values; there is no fixed ancestry, birth order, or interval-presence restriction. NOPs only pad the end of shorter traces. Frozen-prefix constraints follow from the operation reach limit.',
    solver: process.env.Z3_BIN ?? 'z3', problem, swapBudget: bound, slots: encoded.slots, timeoutMs, result,
    interpretation: 'sat includes an independently replayed trace; unsat excludes only this finite trace bound; unknown or solver error is inconclusive.',
    reproduce: `Z3_BIN=<z3-path> node scripts/optimality-bounded-trace-smt.mjs ${reach} ${bound} ${output} ${timeoutMs}` };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({ ...report, result: { ...result, stdout: undefined } }));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
