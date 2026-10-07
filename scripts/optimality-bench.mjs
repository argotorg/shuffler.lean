#!/usr/bin/env node
/** Reproducible offline benchmark. Production algorithms run only in Lean. */
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import { createHash } from 'node:crypto';
import { spawn } from 'node:child_process';
import { pathToFileURL } from 'node:url';
import { baseline, compareCandidate, compareWitness, normalizeCase, reserve, solve } from './optimality-oracle.mjs';

const A = 'v:42', B = 'v:43', C = 'v:44', Z = 'l:0', O = 'l:1';
const repeat = (value, count) => Array(count).fill(value);
const weights = [[1, 0], [0, 1], [1, 1], [4, 1], [5, 1], [6, 1]];

export function random(seed) {
  let state = seed >>> 0;
  return () => { state += 0x6d2b79f5; let x = state;
    x = Math.imul(x ^ x >>> 15, x | 1); x ^= x + Math.imul(x ^ x >>> 7, x | 61);
    return ((x ^ x >>> 14) >>> 0) / 4294967296; };
}

export function smokeCases() {
  const wide = `l:${1n << 248n}`;
  const identity = n => Array.from({ length: n }, (_, i) => i);
  return [
    { id: 'empty', source: [], target: [] },
    { id: 'identity-distinct', source: [A, B], target: [A, B] },
    { id: 'append-baseline', source: [A], target: [A, Z, A] },
    { id: 'birth-order', source: [A], target: ['l:2', O, A] },
    { id: 'below-top-cycle', source: [A, B, C], target: [B, A, C] },
    { id: 'equal-top-cycle', source: [A, B, A], target: [B, A, A] },
    { id: 'bbu-literal-hole', source: [...repeat(Z, 16), O], target: [O, ...repeat(Z, 16), O],
      mapping: identity(17).map(i => i + 1) },
    { id: 'bbu-swap-only-seed', source: [A, ...repeat(Z, 16)], target: [...repeat(Z, 16), A, A],
      mapping: identity(17).map(i => i === 0 ? 16 : i === 16 ? 0 : i) },
    { id: 'bbu-hidden-seed', source: [Z, A, ...repeat(Z, 15)], target: [Z, A, Z, A, ...repeat(Z, 15)],
      mapping: identity(17).map(i => i + 2) },
    { id: 'bbu-equal-assignment', source: repeat(Z, 18), target: repeat(Z, 18),
      mapping: identity(18).map(i => i === 0 ? 17 : i === 17 ? 0 : i) },
    { id: 'carry-17', source: [A], target: [...repeat(Z, 17), A] },
    { id: 'carry-33', source: [A], target: [...repeat(Z, 33), A] },
    { id: 'short-wide-copy', source: [wide, ...repeat(Z, 15)], target: [wide, ...repeat(Z, 16), wide] },
    { id: 'long-wide-copy', source: [wide, ...repeat(Z, 15)], target: [wide, ...repeat(Z, 32), wide] },
    { id: 'load-swap-tradeoff', source: [A, B, ...repeat(Z, 14)],
      target: [A, A, ...repeat(Z, 14), C, B, A], spills: [42, 44] },
    { id: 'load-once-copy', source: [], target: [A, A, A], spills: [42] },
    { id: 'return-label-copy', source: ['return'], target: ['return', 'return'] },
    { id: 'absent-unspilled', source: [], target: [A] },
    { id: 'boundary-seed-collision', source: [A, ...repeat(Z, 16)],
      target: [A, ...repeat(Z, 16), A] },
  ];
}

function allWords(alphabet, length) {
  if (length === 0) return [[]];
  return allWords(alphabet, length - 1).flatMap(rest => alphabet.map(value => [...rest, value]));
}

function smallCases() {
  const result = [], alphabet = [Z, A, B];
  for (let size = 0; size <= 3; size++) for (let final = size; final <= 4; final++) {
    for (const source of allWords(alphabet, size)) for (const target of allWords(alphabet, final)) {
      for (const spills of [[], [42, 43]]) {
        const input = { id: `small-${result.length}`, source, target, spills };
        if (reserve(normalizeCase(input))) result.push(input);
      }
    }
  }
  return result;
}

function boundaryCases() {
  const result = [];
  for (const size of [15, 16, 17, 18]) for (const gap of [0, 1, 2, 15, 16, 17, 31, 32, 33]) {
    for (const position of [...new Set([0, Math.max(0, size - 16), size - 1])]) {
      const source = repeat(Z, size); source[position] = A;
      result.push({ id: `append-size${size}-position${position}-gap${gap}`,
        source, target: [...source, ...repeat(Z, gap), A], spills: [42] });
    }
  }
  for (const width of [1, 2, 32]) {
    const value = `l:${1n << BigInt(8 * (width - 1))}`;
    for (const gap of [1, 2, 15, 16, 17, 31, 32, 33]) result.push({
      id: `literal-width${width}-gap${gap}`, source: [value, ...repeat(Z, 15)],
      target: [value, ...repeat(Z, 15 + gap), value],
    });
  }
  return result;
}

function randomCases(seed, count) {
  const next = random(seed), choose = values => values[Math.floor(next() * values.length)];
  const result = [], alphabet = [A, B, Z, O];
  for (let index = 0; index < count; index++) {
    const size = choose([0, 1, 2, 4, 15, 16, 17, 18]);
    const source = Array.from({ length: size }, () => choose(alphabet));
    let stack = [...source]; const ops = [], added = [], spills = choose([[], [42], [42, 43, 44]]);
    const births = choose([0, 1, 2, 3, 15, 16, 17]);
    for (let round = 0; round < births + 4; round++) {
      if (stack.length > 1 && next() < .6) {
        const depth = 1 + Math.floor(next() * Math.min(16, stack.length - 1));
        const position = stack.length - depth - 1;
        [stack[position], stack[stack.length - 1]] = [stack.at(-1), stack[position]];
        ops.push(['swap', depth]);
      }
      if (round >= births) continue;
      if (stack.length > 0 && next() < .6) {
        const depth = 1 + Math.floor(next() * Math.min(16, stack.length));
        const value = stack[stack.length - depth]; stack.push(value); added.push(value); ops.push(['dup', depth]);
      } else if (spills.length && next() < .3) {
        const id = choose(spills), value = `v:${id}`; stack.push(value); added.push(value); ops.push(['load', id]);
      } else {
        const value = choose([Z, O]); stack.push(value); added.push(value); ops.push(['push', value]);
      }
    }
    result.push({ id: `random-${seed}-${index}`, source, target: stack, missing: added, spills,
      referenceOps: ops });
  }
  return result;
}

function mediumCases(seed, count) {
  const next = random(seed), choose = values => values[Math.floor(next() * values.length)];
  return Array.from({ length: count }, (_, index) => {
    const final = choose([5, 6, 7, 8]), size = Math.floor(next() * (final + 1));
    const source = Array.from({ length: size }, () => choose([Z, A, B]));
    const spills = choose([[], [42], [42, 43]]);
    const available = [Z, A, B].filter(value => value === Z || source.includes(value) ||
      spills.includes(Number(value.slice(2))));
    const missing = Array.from({ length: final - size }, () => choose(available));
    const target = [...source, ...missing];
    for (let i = target.length - 1; i > 0; i--) {
      const j = Math.floor(next() * (i + 1)); [target[i], target[j]] = [target[j], target[i]];
    }
    return { id: `medium-${seed}-${index}`, source, target, missing, spills };
  });
}

function sparseCases(seed, count) {
  const next = random(seed), choose = values => values[Math.floor(next() * values.length)];
  return Array.from({ length: count }, (_, index) => {
    const size = choose([16, 17, 18, 19, 20]), source = repeat(Z, size);
    for (let i = 0; i < choose([1, 2]); i++) source[Math.floor(next() * size)] = choose([A, B]);
    const spills = choose([[], [42], [42, 43]]), births = choose([0, 1, 2, 3]);
    let stack = [...source], addedNonzero = false;
    const ops = [], missing = [];
    for (let round = 0; round < births + 5; round++) {
      if (next() < .75) {
        const positions = stack.flatMap((value, position) => position < stack.length - 1 &&
          stack.length - position - 1 <= 16 && (value !== Z || next() < .2) ? [position] : []);
        if (positions.length) {
          const position = choose(positions), depth = stack.length - position - 1;
          [stack[position], stack[stack.length - 1]] = [stack.at(-1), stack[position]];
          ops.push(['swap', depth]);
        }
      }
      if (round >= births) continue;
      const candidates = stack.flatMap((value, position) => value !== Z && stack.length - position <= 16 ? [position] : []);
      if (!addedNonzero && candidates.length && next() < .4) {
        const position = choose(candidates), value = stack[position];
        ops.push(['dup', stack.length - position]); missing.push(value); stack.push(value); addedNonzero = true;
      } else {
        ops.push(['push', Z]); missing.push(Z); stack.push(Z);
      }
    }
    return { id: `sparse-${seed}-${index}`, source, target: stack, missing, spills, referenceOps: ops };
  });
}

function twoSeedCases() {
  const result = [], a = `l:${1n << 248n}`;
  for (const width of [1, 32]) for (const reverse of [false, true]) {
    const b = width === 1 ? O : `l:${(1n << 248n) + 1n}`;
    for (const gap of [0, 1, 14, 15, 16, 17, 30, 31, 32, 33]) {
      const source = [a, b, ...repeat(Z, 14)];
      result.push({ id: `two-seed-width32-${width}-gap${gap}-${reverse ? 'ba' : 'ab'}`,
        source, target: [...source, ...repeat(Z, gap), ...(reverse ? [b, a] : [a, b])] });
    }
  }
  return result;
}

function twoSeedPlacementCases() {
  const result = [], wideA = `l:${1n << 248n}`, wideB = `l:${(1n << 248n) + 1n}`;
  for (const [kind, a, b] of [['wide-narrow', wideA, O], ['wide-wide', wideA, wideB], ['hard', A, B]]) {
    for (const reverse of [false, true]) for (const gap of [0, 1, 14, 15, 16, 17, 30, 31, 32, 33]) {
      const source = [a, b, ...repeat(Z, 14)];
      result.push({ id: `two-seed-place-${kind}-gap${gap}-${reverse ? 'ba' : 'ab'}`,
        source, target: [b, a, ...repeat(Z, 14 + gap), ...(reverse ? [b, a] : [a, b])] });
    }
  }
  return result;
}

function noGrowthCases(seed, count) {
  const next = random(seed), choose = values => values[Math.floor(next() * values.length)];
  return Array.from({ length: count }, (_, index) => {
    const size = choose([0, 1, 2, 16, 17, 18, 32, 64, 128]), frozen = Math.max(0, size - 17);
    const alphabet = Array.from({ length: choose([2, 3, 5, 17]) }, (_, i) => `v:${100 + i}`);
    const source = [...repeat(Z, frozen), ...Array.from({ length: size - frozen }, () => choose(alphabet))];
    const target = [...source];
    for (let i = size - 1; i > frozen; i--) {
      const j = frozen + Math.floor(next() * (i - frozen + 1));
      [target[i], target[j]] = [target[j], target[i]];
    }
    const current = [...source], ops = [];
    const swap = position => { const top = current.length - 1;
      [current[position], current[top]] = [current[top], current[position]];
      ops.push(['swap', top - position]); };
    for (let i = frozen; i + 1 < size; i++) if (current[i] !== target[i]) {
      const j = current.findIndex((value, position) => position > i && value === target[i]);
      if (j !== size - 1) swap(j); swap(i);
    }
    return { id: `no-growth-${seed}-${index}`, source, target, missing: [], referenceOps: ops };
  });
}

function loadCases() {
  const result = [];
  for (const depth of [0, 15]) for (const gap of [1, 16, 17, 33]) {
    for (const width of [0, 1, 32]) for (const gasModel of ['cpp', 'evm']) {
      const source = [A, ...repeat(Z, depth)];
      result.push({ id: `load-${gasModel}-width${width}-depth${depth}-gap${gap}`,
        source, target: [...source, ...repeat(Z, gap), A], spills: [42], loadWidths: [[42, width]], gasModel });
    }
  }
  return result;
}

function mixedCases(seed, count) {
  const next = random(seed), choose = values => values[Math.floor(next() * values.length)];
  const wide = `l:${1n << 248n}`;
  return Array.from({ length: count }, (_, index) => {
    const size = choose([0, 1, 2, 4, 15, 16, 17, 18, 20]), source = repeat(Z, size);
    const active = choose([1, 2, 3]);
    for (let i = 0; i < active && size > 0; i++) source[Math.floor(next() * size)] = choose([O, wide, A, B, 'return']);
    const spills = choose([[], [42], [43], [42, 43]]), gasModel = choose(['cpp', 'evm']);
    const loadWidths = spills.map(id => [id, choose([0, 1, 2, 32])]);
    const births = choose([0, 1, 2, 3]), stack = [...source], ops = [], missing = [];
    for (let round = 0; round < births + 4; round++) {
      if (stack.length > 1 && next() < .65) {
        const depth = 1 + Math.floor(next() * Math.min(16, stack.length - 1));
        const position = stack.length - depth - 1;
        [stack[position], stack[stack.length - 1]] = [stack.at(-1), stack[position]];
        ops.push(['swap', depth]);
      }
      if (round >= births) continue;
      let value;
      if (stack.length && next() < .5) {
        const depth = 1 + Math.floor(next() * Math.min(16, stack.length));
        value = stack[stack.length - depth]; ops.push(['dup', depth]);
      } else if (spills.length && next() < .5) {
        const id = choose(spills); value = `v:${id}`; ops.push(['load', id]);
      } else { value = choose([Z, O, wide]); ops.push(['push', value]); }
      stack.push(value); missing.push(value);
    }
    return { id: `mixed-${seed}-${index}`, source, target: stack, missing, spills,
      gasModel, loadWidths, referenceOps: ops };
  });
}

function plantedCases(seed, count) {
  const next = random(seed), choose = items => items[Math.floor(next() * items.length)];
  const wide = `l:${1n << 248n}`, narrow = 'l:256';
  const pool = [Z, O, narrow, wide, A, B, C, 'return'];
  return Array.from({ length: count }, (_, index) => {
    const family = index % 3, spills = [42, 43, 44].filter(() => next() < .5);
    const loadWidths = spills.map(id => [id, choose([0, 1, 2, 32])]);
    const gasModel = choose(['cpp', 'evm']);
    let height = choose([0, 1, 2, 5, 15, 16, 17, 18, 32, 64, 128]);
    if (family !== 0) height = Math.max(16, height);
    const frozen = repeat(Z, Math.max(0, height - 17));
    const kinds = pool.slice(0, 2).concat(pool.slice(2).filter(() => next() < .65));
    let source = frozen.concat(Array.from({ length: height - frozen.length }, () =>
      next() < .6 ? Z : choose(kinds)));
    if (family === 1) source = [...repeat(Z, height - 16), choose([A, B, wide, O]), ...repeat(Z, 15)];
    if (family === 2) source = [...repeat(Z, height - 16), choose([A, wide]), choose([B, O]), ...repeat(Z, 14)];
    const stack = [...source], missing = [], ops = [];
    const apply = op => {
      const [kind, arg] = op;
      if (kind === 'swap') {
        const position = stack.length - arg - 1;
        [stack[position], stack[stack.length - 1]] = [stack.at(-1), stack[position]];
      } else {
        const value = kind === 'dup' ? stack[stack.length - arg] : kind === 'load' ? `v:${arg}` : arg;
        stack.push(value); missing.push(value);
      }
      ops.push(op);
    };
    const zeros = n => { for (let j = 0; j < n; j++) apply(['push', Z]); };
    if (family === 1) {
      apply(['dup', 16]);
      let gap = choose([1, 2, 15, 16, 17, 31, 32, 33, 63, 64, 65, 96, 127, 128]);
      while (gap > 0) { const block = Math.min(16, gap); zeros(block); apply(['swap', block]); gap -= block; }
      for (let j = 0, copies = Math.floor(next() * 4); j < copies; j++) apply(['dup', 1]);
    } else if (family === 2) {
      apply(['dup', 15]); apply(['swap', 16]); apply(['swap', 15]); apply(['dup', 16]);
      let gap = choose([1, 2, 14, 15, 16, 17, 29, 30]);
      while (gap > 0) {
        const block = Math.min(15, gap); zeros(block);
        apply(['swap', block + 1]); apply(['swap', 1]);
        if (block > 1) apply(['swap', block]); gap -= block;
      }
    } else {
      const births = choose([0, 1, 2, 3, 15, 16, 17, 31, 32, 33, 64, 96, 128]);
      const events = Array.from({ length: 1 + Math.floor(next() * 8) }, () =>
        choose([0, births, Math.min(births, 1), Math.min(births, 16), Math.floor(next() * (births + 1))]));
      const seen = new Set([JSON.stringify(stack)]);
      for (let birth = 0; birth <= births; birth++) {
        for (let j = 0; j < events.filter(event => event === birth).length; j++) {
          const depths = Array.from({ length: Math.min(16, stack.length - 1) }, (_, d) => d + 1)
            .filter(d => stack[stack.length - d - 1] !== stack.at(-1));
          if (!depths.length) continue;
          const depth = choose(depths), position = stack.length - depth - 1;
          const candidate = [...stack]; [candidate[position], candidate[candidate.length - 1]] = [candidate.at(-1), candidate[position]];
          const key = JSON.stringify(candidate); if (seen.has(key)) continue;
          apply(['swap', depth]); seen.add(key);
        }
        if (birth === births) continue;
        if (next() < .65 || stack.length === 0) apply(['push', Z]);
        else if (next() < .85) {
          const depth = 1 + Math.floor(next() * Math.min(16, stack.length));
          apply(stack[stack.length - depth] === Z ? ['push', Z] : ['dup', depth]);
        } else {
          const value = choose([O, narrow, wide]);
          const position = stack.lastIndexOf(value), depth = stack.length - position;
          apply(position >= 0 && depth <= 16 ? ['dup', depth] : ['push', value]);
        }
        seen.add(JSON.stringify(stack));
      }
    }
    return { id: `planted-${seed}-${index}`, source, target: stack, missing, spills, gasModel, loadWidths,
      planted: { seed, index, family, swaps: ops.filter(op => op[0] === 'swap').length }, referenceOps: ops };
  });
}

function plantedChainCases(seed, count) {
  const next = random(seed), choose = items => items[Math.floor(next() * items.length)];
  const wide = `l:${1n << 248n}`;
  const palette = [Z, O, 'l:256', wide, ...Array.from({ length: 17 }, (_, i) => `v:${100 + i}`)];
  return Array.from({ length: count }, (_, index) => {
    const height = choose([2, 3, 5, 16, 17, 18, 32, 64, 128, 256, 512]);
    const live = Math.min(17, height), source = [...repeat(Z, height - live), ...palette.slice(0, live)];
    const spills = Array.from({ length: 17 }, (_, i) => 100 + i).filter(() => next() < .5);
    const loadWidths = spills.map(id => [id, choose([0, 1, 2, 32])]);
    const stack = [...source], missing = [], ops = [], selected = new Set();
    const swap = position => {
      const depth = stack.length - position - 1;
      [stack[position], stack[stack.length - 1]] = [stack.at(-1), stack[position]];
      ops.push(['swap', depth]); selected.add(position);
    };
    const birth = value => {
      const position = stack.lastIndexOf(value), depth = stack.length - position;
      if (value === Z) ops.push(['push', Z]);
      else if (position >= 0 && depth <= 16) ops.push(['dup', depth]);
      else if (value.startsWith('v:')) ops.push(['load', Number(value.slice(2))]);
      else ops.push(['push', value]);
      stack.push(value); missing.push(value);
    };
    const rounds = choose([1, 2, 3, 4, 8, 16]);
    for (let round = 0; round < rounds; round++) {
      const available = Array.from({ length: Math.min(16, stack.length - 1) }, (_, depth) => stack.length - depth - 2)
        .filter(position => !selected.has(position));
      if (index % 3 === 1) available.reverse();
      const pathLength = index % 4 === 0 && round === 0 ? available.length : choose([1, 2, 3, 4, 8]);
      for (const position of available.slice(0, pathLength)) {
        if (stack[position] !== stack.at(-1)) swap(position);
      }
      const value = index % 4 === 0 && round === 0 ? 'l:99' : next() < .55 ? stack.at(-1) : choose([Z, O, wide]);
      birth(value);
      const previousTop = stack.length - 2;
      if (!selected.has(previousTop) && stack[previousTop] !== stack.at(-1) && (index % 4 === 0 || next() < .85)) {
        swap(previousTop);
      }
    }
    return { id: `planted-chains-${seed}-${index}`, source, target: stack, missing, spills,
      gasModel: choose(['cpp', 'evm']), loadWidths, referenceOps: ops,
      planted: { seed, index, family: 'open-chains', rounds, swaps: ops.filter(op => op[0] === 'swap').length } };
  });
}

export function casesFor(suite, seed = 1, limit = Infinity) {
  const sampleCount = Number.isFinite(limit) ? limit : 200;
  let base = suite === 'smoke' ? smokeCases() : suite === 'small' ? smallCases() :
    suite === 'boundary' ? boundaryCases() : suite === 'random' ?
      randomCases(seed, Number.isFinite(limit) ? Math.ceil(limit / 6) : 200) :
      suite === 'medium' ? mediumCases(seed, sampleCount) :
      suite === 'sparse' ? sparseCases(seed, sampleCount) :
      suite === 'two-seed' ? twoSeedCases() :
      suite === 'two-seed-placement' ? twoSeedPlacementCases() :
      suite === 'no-growth' ? noGrowthCases(seed, sampleCount) :
      suite === 'loads' ? loadCases() :
      suite === 'mixed' ? mixedCases(seed, sampleCount) :
      suite === 'planted' ? plantedCases(seed, sampleCount) :
      suite === 'planted-chains' ? plantedChainCases(seed, sampleCount) : null;
  if (!base) throw new Error(`unknown suite ${suite}`);
  const result = base.flatMap(input => {
    const widths = input.loadWidths ? ['supplied'] : input.spills?.length ? [1, 2, 32] : [1];
    return widths.flatMap(width => weights.map(([gas, bytes]) => normalizeCase({ ...input,
      id: `${input.id}/w${width}/g${gas}b${bytes}`, weights: { gas, bytes },
      loadWidths: input.loadWidths ?? (input.spills ?? []).map(id => [id, width]),
      gasModel: input.gasModel ?? 'cpp' })));
  });
  if (result.length > limit) {
    const next = random(seed);
    for (let i = result.length - 1; i > 0; i--) {
      const j = Math.floor(next() * (i + 1)); [result[i], result[j]] = [result[j], result[i]];
    }
    return result.slice(0, limit);
  }
  return result;
}

export function summarize(records, configuration) {
  const algorithms = {};
  for (const record of records) for (const [name, comparison] of Object.entries(record.comparisons ?? {})) {
    const stats = algorithms[name] ??= { cases: 0, successes: 0, feasibilityFailures: 0,
      oracleComparisons: 0, exact: 0, zeroExcessViolations: 0, maxCostRatio: 1, maxExcessRatio: 1,
      certificates: { exactBaseline: 0, exactLineage: 0, exactStatic: 0, exactNoGrowth: 0, twiceLineage: 0, twiceStatic: 0 },
      maxInstructionsPerSize: 0, worstExcessCase: null,
      scope: comparison.scope, witnessComparisons: 0, witnessViolations: 0,
      witnessPositiveExcessComparisons: 0, witnessZeroExcessComparisons: 0,
      witnessZeroExcessViolations: 0, maxCandidateExcessWithZeroWitness: 0,
      worstZeroExcessWitnessCase: null,
      maxWitnessExcessRatio: null, worstWitnessCase: null, worstWitnessComparison: null };
    if (comparison.status === 'not-applicable') continue;
    stats.cases++;
    if (comparison.feasibilityFailure) stats.feasibilityFailures++;
    if (comparison.status !== 'ok') continue;
    stats.successes++;
    if (comparison.witness) {
      stats.witnessComparisons++;
      if (comparison.witness.twiceExcessViolation) stats.witnessViolations++;
      const witness = comparison.witness;
      const candidateExcess = witness.candidateScore - witness.baseline;
      const referenceExcess = witness.witnessScore - witness.baseline;
      if (referenceExcess > 0) {
        stats.witnessPositiveExcessComparisons++;
        const value = candidateExcess / referenceExcess;
        if (stats.maxWitnessExcessRatio === null || value > stats.maxWitnessExcessRatio) {
          stats.maxWitnessExcessRatio = value; stats.worstWitnessCase = record.problem.id;
          stats.worstWitnessComparison = { caseId: record.problem.id, baseline: witness.baseline,
            candidateScore: witness.candidateScore, witnessScore: witness.witnessScore,
            candidateExcess, witnessExcess: referenceExcess };
        }
      } else {
        stats.witnessZeroExcessComparisons++;
        if (candidateExcess > 0) stats.witnessZeroExcessViolations++;
        if (candidateExcess > stats.maxCandidateExcessWithZeroWitness) {
          stats.maxCandidateExcessWithZeroWitness = candidateExcess;
          stats.worstZeroExcessWitnessCase = record.problem.id;
        }
      }
    }
    for (const [kind, certified] of Object.entries(comparison.certificates ?? {})) {
      if (certified) stats.certificates[kind] = (stats.certificates[kind] ?? 0) + 1;
    }
    const size = Math.max(1, record.problem.source.length + record.problem.target.length);
    stats.maxInstructionsPerSize = Math.max(stats.maxInstructionsPerSize, comparison.instructions / size);
    if (comparison.exact !== null) {
      stats.oracleComparisons++; if (comparison.exact) stats.exact++;
      if (comparison.zeroExcessViolation) stats.zeroExcessViolations++;
      const larger = (a, b) => a === 'inf' ? false : b === 'inf' || b > a;
      if (larger(stats.maxCostRatio, comparison.costRatio)) stats.maxCostRatio = comparison.costRatio;
      if (larger(stats.maxExcessRatio, comparison.excessRatio)) {
        stats.maxExcessRatio = comparison.excessRatio; stats.worstExcessCase = record.problem.id;
      }
    }
  }
  return { configuration,
    witnessRatioReporting: { version: 2, finiteMaximumUsesPositiveReferenceExcess: true,
      zeroReferenceExcessReportedSeparately: true },
    cases: records.length,
    oracle: records.reduce((counts, record) => { counts[record.oracle.status] = (counts[record.oracle.status] ?? 0) + 1; return counts; }, {}),
    oracleStates: records.reduce((total, record) => total + record.oracle.states, 0),
    modelDisagreements: records.filter(record => record.modelError).map(record => ({ id: record.problem.id, error: record.modelError })),
    algorithms };
}

function fingerprint(root, accept) {
  const files = [];
  const walk = directory => {
    if (!fs.existsSync(directory)) return;
    for (const item of fs.readdirSync(directory, { withFileTypes: true })) {
      const file = path.join(directory, item.name);
      if (item.isDirectory()) walk(file);
      else if (accept(file)) files.push(file);
    }
  };
  walk(root);
  const hash = createHash('sha256');
  for (const file of files.sort()) hash.update(file).update('\0').update(fs.readFileSync(file)).update('\0');
  return { sha256: hash.digest('hex'), files: files.length };
}

function productionFingerprint() {
  return { source: fingerprint('Shuffler', file => file.endsWith('.lean')),
    artifacts: fingerprint('.lake/build/lib/lean/Shuffler', file => /\.olean(?:\.private|\.server)?$/.test(file)) };
}

async function main(args) {
  const arg = (name, fallback) => { const index = args.indexOf(name); return index < 0 ? fallback : args[index + 1]; };
  const suite = arg('--suite', 'smoke'), seed = Number(arg('--seed', '1'));
  const limit = Number(arg('--cases', suite === 'smoke' ? '10000' : '200'));
  const stateLimit = Number(arg('--state-limit', '100000'));
  const skipOracle = args.includes('--skip-oracle');
  const selectedAlgorithms = arg('--algorithms', null)?.split(',') ?? null;
  if (!Number.isSafeInteger(seed) || seed < 0 || !Number.isSafeInteger(limit) || limit < 1) {
    throw new Error('seed must be a natural number and cases must be positive');
  }
  const inputPath = arg('--input', null);
  const cases = inputPath ? fs.readFileSync(inputPath, 'utf8').split('\n').filter(line => line.trim())
    .map(line => normalizeCase(JSON.parse(line))) : casesFor(suite, seed, limit);
  const emit = arg('--emit-cases', null);
  if (emit) { fs.writeFileSync(emit, cases.map(problem => JSON.stringify(problem)).join('\n') + '\n'); return; }
  const records = cases.map((problem, index) => {
    if (index % 20 === 0) process.stderr.write(`oracle ${index}/${cases.length}\n`);
    const oracle = skipOracle ? { model: problem.model, status: 'not-run', reason: 'skip-oracle', states: 0 } :
      solve(problem, { stateLimit });
    const modelError = problem.expectedOracleScore !== undefined && oracle.status === 'optimal' &&
      oracle.score !== problem.expectedOracleScore ? 'expected oracle score differs' : undefined;
    return { problem, oracle, modelError };
  });
  const noLean = args.includes('--no-lean');
  const versionBefore = noLean ? null : productionFingerprint();
  const runnerPath = arg('--runner', null);
  let snapshot = null;
  if (!noLean) {
    const input = records.map(({ problem, oracle }) => JSON.stringify({ ...problem,
      algorithms: selectedAlgorithms, referenceOps: oracle.ops ?? problem.referenceOps })).join('\n') + '\n';
    if (runnerPath) {
      const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'optimality-bench-'));
      const file = path.join(directory, 'runner');
      fs.copyFileSync(runnerPath, file); fs.chmodSync(file, 0o755);
      snapshot = { file, sha256: createHash('sha256').update(fs.readFileSync(file)).digest('hex') };
    }
    const command = snapshot?.file ?? 'lake';
    const commandArgs = snapshot ? [] : ['env', 'lean', '--run', 'Bench/Optimality.lean'];
    const productionLog = arg('--production-log', null);
    if (productionLog) fs.writeFileSync(productionLog, '');
    const responses = await new Promise((resolve, reject) => {
      const child = spawn(command, commandArgs, { stdio: ['pipe', 'pipe', 'pipe'] });
      const values = []; let pending = '', stderr = '', bytes = 0;
      const accept = line => {
        if (!line.trim()) return;
        const value = JSON.parse(line); values.push(value);
        if (productionLog) fs.appendFileSync(productionLog, line + '\n');
        if (values.length % 20 === 0 || values.length === records.length) {
          process.stderr.write('production ' + values.length + '/' + records.length + '\n');
        }
      };
      child.stdout.setEncoding('utf8'); child.stderr.setEncoding('utf8');
      child.stdout.on('data', chunk => {
        try {
          bytes += Buffer.byteLength(chunk);
          if (bytes > 128 * 1024 * 1024) throw new Error('Lean output exceeds 128 MiB');
          pending += chunk;
          let end;
          while ((end = pending.indexOf('\n')) >= 0) { accept(pending.slice(0, end)); pending = pending.slice(end + 1); }
        } catch (error) { child.kill(); reject(error); }
      });
      child.stderr.on('data', chunk => { stderr += chunk; });
      child.on('error', reject); child.stdin.on('error', reject);
      child.on('close', status => {
        try {
          if (status !== 0) throw new Error('Lean runner failed (' + status + '):\n' + stderr);
          accept(pending); resolve(values);
        } catch (error) { reject(error); }
      });
      child.stdin.end(input);
    });
    if (responses.length !== records.length) throw new Error('Lean returned a different number of cases');
    for (let i = 0; i < records.length; i++) {
      const record = records[i], response = responses[i], result = response.result;
      record.production = response;
      if (!result || result.id !== record.problem.id) { record.modelError = response.error ?? 'case id mismatch'; continue; }
      if (result.actualCaps && result.actualReserve !== reserve(record.problem)) record.modelError = 'Reserve disagreement';
      const modelBaseline = baseline(record.problem);
      if (result.generationBaseline !== undefined && Number.isFinite(modelBaseline) &&
          result.generationBaseline !== modelBaseline) record.modelError = 'generation baseline disagreement';
      if ((record.oracle.status === 'optimal' || record.problem.referenceOps) && result.reference?.status !== 'ok') {
        record.modelError = 'reference trace rejected by Lean';
      }
      record.comparisons = {};
      for (const [name, candidate] of Object.entries(result.algorithms)) {
        try {
          const comparison = compareCandidate(record.problem, candidate, record.oracle);
          comparison.scope = name === 'old-bbu' ? 'original-generation-and-final-permutation' : 'completed-source-to-target';
          const referenceOps = record.oracle.ops ?? record.problem.referenceOps;
          if (comparison.status === 'ok' && referenceOps && result.reference?.status === 'ok') {
            comparison.witness = { ...compareWitness(record.problem, candidate.ops, referenceOps),
              source: record.oracle.ops ? 'oracle' : 'supplied' };
            if (comparison.witness.witnessScore !== result.reference.score) throw new Error('reference cost disagreement');
            if (comparison.witness.twiceExcessViolation &&
                (comparison.certificates.twiceStatic || comparison.certificates.twiceLineage)) {
              throw new Error('factor-two certificate disagrees with a replayed witness');
            }
          }
          record.comparisons[name] = comparison;
          if (comparison.status === 'ok' && record.oracle.status === 'optimal') {
            const flags = comparison.certificates;
            if ((flags.exactBaseline || flags.exactLineage || flags.exactStatic || flags.exactNoGrowth) && !comparison.exact) {
              throw new Error('exact certificate disagrees with oracle');
            }
            if ((flags.twiceLineage || flags.twiceStatic) &&
                BigInt(comparison.score) + BigInt(modelBaseline) > 2n * BigInt(record.oracle.score)) {
              throw new Error('factor-two certificate disagrees with oracle');
            }
          }
        }
        catch (error) { record.modelError = `${name}: ${error.message}`; }
      }
    }
  }
  const versionAfter = noLean ? null : productionFingerprint();
  const summary = summarize(records, { suite: inputPath ? 'input' : suite, inputPath, seed, cases: limit, stateLimit, skipOracle, noLean, selectedAlgorithms,
    weights, loadWidths: [1, 2, 32], model: 'actual-16/17', node: process.version,
    leanToolchain: fs.readFileSync('lean-toolchain', 'utf8').trim(),
    runnerSnapshot: snapshot,
    versionBefore, versionAfter,
    stableArtifacts: noLean ? null : versionBefore.artifacts.sha256 === versionAfter.artifacts.sha256,
    stableSources: noLean ? null : versionBefore.source.sha256 === versionAfter.source.sha256 });
  const output = arg('--output', null), summaryPath = arg('--summary', null);
  if (output) fs.writeFileSync(output, records.map(record => JSON.stringify(record)).join('\n') + '\n');
  if (summaryPath) fs.writeFileSync(summaryPath, JSON.stringify(summary, null, 2) + '\n');
  process.stdout.write(JSON.stringify(summary, null, 2) + '\n');
  if (summary.modelDisagreements.length) process.exitCode = 1;
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  main(process.argv.slice(2)).catch(error => { console.error(error.stack); process.exitCode = 1; });
}
