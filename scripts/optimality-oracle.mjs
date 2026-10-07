#!/usr/bin/env node
/** Offline exact oracle. This file is never imported by a production planner.
 * Values are exact Lean values, bottom-to-top stacks use string keys, and POP
 * is excluded. Search uses the actual SWAP16/DUP16 limits unless a case has an
 * explicit reduced-cap label. Gas excludes memory expansion and spill stores.
 */
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';

const WORD_LIMIT = 1n << 256n;
const isNat = value => Number.isSafeInteger(value) && value >= 0;
const check = (condition, message) => { if (!condition) throw new Error(message); };
const equalStack = (a, b) => a.length === b.length && a.every((v, i) => v === b[i]);
const stackKey = stack => stack.join('|');
const addCost = (a, b) => ({ gas: a.gas + b.gas, bytes: a.bytes + b.bytes });
const counts = values => values.reduce((map, value) => map.set(value, (map.get(value) ?? 0) + 1), new Map());
const equalCounts = (a, b) => a.size === b.size && [...a].every(([v, n]) => b.get(v) === n);

export function normalizeValue(value) {
  check(typeof value === 'string', 'value must be a string');
  if (value === 'wildcard' || value === 'return') return value;
  const match = /^(l|v):([0-9]+)$/.exec(value);
  check(match, `invalid value ${value}`);
  const number = BigInt(match[2]);
  if (match[1] === 'l') check(number < WORD_LIMIT, 'literal exceeds 256 bits');
  else check(number <= BigInt(Number.MAX_SAFE_INTEGER), 'variable id is not a safe integer');
  return `${match[1]}:${number}`;
}

export function normalizeCase(input) {
  check(Array.isArray(input.source) && Array.isArray(input.target), 'source and target must be arrays');
  const source = input.source.map(normalizeValue), target = input.target.map(normalizeValue);
  const weights = input.weights ?? { gas: 1, bytes: 1 };
  check(isNat(weights.gas) && isNat(weights.bytes) && weights.gas + weights.bytes > 0,
    'weights must be safe natural numbers and cannot both be zero');
  const caps = input.caps ?? { swap: 16, dup: 16 };
  check(isNat(caps.swap) && caps.swap >= 1 && caps.swap <= 16 && caps.dup === caps.swap,
    'supported cap pairs are equal ordinal limits from 1 through 16');
  const spills = [...new Set(input.spills ?? [])];
  check(spills.every(isNat), 'spill ids must be safe natural numbers');
  const loadWidths = input.loadWidths ?? [];
  check(loadWidths.every(pair => Array.isArray(pair) && pair.length === 2 && isNat(pair[0]) &&
    isNat(pair[1]) && pair[1] <= 32), 'LOAD widths must be 0 through 32');
  check(new Set(loadWidths.map(pair => pair[0])).size === loadWidths.length, 'duplicate LOAD width');
  const remaining = counts(source);
  const missing = input.missing === undefined ? target.filter(value => {
    const count = remaining.get(value) ?? 0;
    if (count > 0) { remaining.set(value, count - 1); return false; }
    return true;
  }) : input.missing.map(normalizeValue);
  const gasModel = input.gasModel ?? 'cpp';
  check(gasModel === 'cpp' || gasModel === 'evm', 'gasModel must be cpp or evm');
  if (input.mapping !== undefined) {
    check(Array.isArray(input.mapping) && input.mapping.length === source.length &&
      input.mapping.every(destination => isNat(destination) && destination < target.length),
      'mapping must give one target index per source');
    check(new Set(input.mapping).size === input.mapping.length, 'mapping must be injective');
    check(input.mapping.every((destination, sourceIndex) => source[sourceIndex] === target[destination]),
      'mapping must preserve exact values');
  }
  return { ...input, id: String(input.id ?? 'unnamed'), source, target, missing, spills,
    weights: { ...weights }, caps: { ...caps }, gasModel, loadWidths,
    model: caps.swap === 16 ? 'actual-16/17' : 'reduced-cap' };
}

export function score(problem, cost) {
  const result = problem.weights.gas * cost.gas + problem.weights.bytes * cost.bytes;
  check(Number.isSafeInteger(result), 'weighted cost exceeds safe integer range');
  return result;
}

export function literalWidth(value) {
  if (value === 'wildcard') return 0;
  check(value.startsWith('l:'), 'literal width requires a literal');
  const number = BigInt(value.slice(2));
  return number === 0n ? 0 : Math.ceil(number.toString(16).length / 2);
}

const freelyPushed = value => value === 'wildcard' || value.startsWith('l:');
const spilled = (problem, value) => value.startsWith('v:') && problem.spills.includes(Number(value.slice(2)));
const free = (problem, value) => freelyPushed(value) || spilled(problem, value);

export function opCost(problem, op) {
  switch (op[0]) {
    case 'swap': case 'dup': return { gas: 3, bytes: 1 };
    case 'push': {
      const width = literalWidth(op[1]);
      return { gas: width === 0 ? 2 : 3, bytes: width + 1 };
    }
    case 'load': {
      const width = problem.loadWidths.find(pair => pair[0] === op[1])?.[1] ?? 1;
      return { gas: problem.gasModel === 'evm' && width === 0 ? 5 : 6, bytes: width + 2 };
    }
    default: throw new Error(`unsupported no-POP opcode ${op[0]}`);
  }
}

function directOp(problem, value) {
  if (freelyPushed(value)) return ['push', value];
  if (spilled(problem, value)) return ['load', Number(value.slice(2))];
  return null;
}

/** Necessary generation cost if every retained occurrence stayed reachable. */
export function baseline(problem) {
  let result = 0;
  const oldValues = new Set(problem.source), duplicate = score(problem, { gas: 3, bytes: 1 });
  for (const [value, count] of counts(problem.missing)) {
    const direct = directOp(problem, value);
    const introduction = direct ? score(problem, opCost(problem, direct)) : Infinity;
    const later = Math.min(duplicate, introduction);
    result += oldValues.has(value) ? count * later : introduction + (count - 1) * later;
  }
  return result;
}

/** Direct translation of Reserve, independent from the search below. */
export function reserve(problem) {
  const { source, target, missing, caps } = problem;
  if (!equalCounts(counts([...source, ...missing]), counts(target))) return false;
  const frozen = Math.max(0, source.length - caps.swap - 1);
  if (!equalStack(source.slice(0, frozen), target.slice(0, frozen))) return false;
  const needed = new Map([...new Set(missing)].filter(value => !free(problem, value)).map(value => [value, 1]));
  if (missing.length > 0 && source.length >= caps.swap + 1) {
    const value = target[frozen];
    needed.set(value, (needed.get(value) ?? 0) + 1);
  }
  const window = counts(source.slice(frozen));
  return [...needed].every(([value, count]) => (window.get(value) ?? 0) >= count);
}

/** Replay all guards, including exact endpoint and addition multiset. */
export function replay(problem, ops) {
  let stack = [...problem.source], cost = { gas: 0, bytes: 0 };
  const added = [];
  for (const op of ops) {
    check(Array.isArray(op) && op.length === 2, 'operation must have one argument; POP is excluded');
    const [kind, argument] = op;
    if (kind === 'swap') {
      check(isNat(argument) && argument >= 1 && argument <= problem.caps.swap && argument < stack.length,
        'illegal SWAP depth');
      const position = stack.length - argument - 1;
      [stack[position], stack[stack.length - 1]] = [stack[stack.length - 1], stack[position]];
    } else if (kind === 'dup') {
      check(isNat(argument) && argument >= 1 && argument <= problem.caps.dup && argument <= stack.length,
        'illegal DUP index');
      const value = stack[stack.length - argument]; stack.push(value); added.push(value);
    } else if (kind === 'push') {
      const value = normalizeValue(argument);
      check(freelyPushed(value), 'PUSH requires a freely generated value');
      stack.push(value); added.push(value);
    } else if (kind === 'load') {
      check(isNat(argument) && problem.spills.includes(argument), 'LOAD requires a spilled variable');
      const value = `v:${argument}`; stack.push(value); added.push(value);
    } else throw new Error(`unsupported no-POP opcode ${kind}`);
    cost = addCost(cost, opCost(problem, op));
  }
  check(equalStack(stack, problem.target), 'replay endpoint differs from target');
  check(equalCounts(counts(added), counts(problem.missing)), 'replay additions differ from H');
  return { target: stack, added, cost, score: score(problem, cost), instructions: ops.length };
}

class Heap {
  constructor(compare) { this.items = []; this.compare = compare; }
  get length() { return this.items.length; }
  push(value) {
    const items = this.items; items.push(value); let index = items.length - 1;
    while (index > 0) {
      const parent = (index - 1) >>> 1;
      if (this.compare(items[parent], value) <= 0) break;
      items[index] = items[parent]; index = parent;
    }
    items[index] = value;
  }
  pop() {
    const items = this.items, result = items[0], last = items.pop();
    if (items.length === 0) return result;
    let index = 0;
    while (2 * index + 1 < items.length) {
      let child = 2 * index + 1;
      if (child + 1 < items.length && this.compare(items[child + 1], items[child]) < 0) child++;
      if (this.compare(last, items[child]) <= 0) break;
      items[index] = items[child]; index = child;
    }
    items[index] = last; return result;
  }
}

function compareCosts(problem, a, b) {
  return score(problem, a) - score(problem, b) || a.gas - b.gas || a.bytes - b.bytes;
}

function moves(problem, stack, desiredCounts, generationChoices, pareto = false) {
  const result = [];
  for (let depth = 1; depth <= problem.caps.swap && depth < stack.length; depth++) {
    const position = stack.length - depth - 1;
    if (stack[position] === stack.at(-1)) continue;
    const next = [...stack]; [next[position], next[next.length - 1]] = [next.at(-1), next[position]];
    result.push({ stack: next, op: ['swap', depth], cost: { gas: 3, bytes: 1 } });
  }
  if (stack.length >= problem.target.length) return result;
  const present = counts(stack);
  for (const [value, direct] of generationChoices) {
    if ((present.get(value) ?? 0) >= desiredCounts.get(value)) continue;
    let choice = direct, duplicate = null;
    for (let index = 1; index <= problem.caps.dup && index <= stack.length; index++) {
      if (stack[stack.length - index] === value) {
        duplicate = { op: ['dup', index], cost: { gas: 3, bytes: 1 } };
        if (!choice || compareCosts(problem, duplicate.cost, choice.cost) <= 0) choice = duplicate;
        break;
      }
    }
    if (pareto) {
      const choices = [direct, duplicate].filter(Boolean);
      for (const candidate of choices) {
        if (choices.some(other => other !== candidate && dominates(other.cost, candidate.cost) &&
            (!dominates(candidate.cost, other.cost) || other === choices[0]))) continue;
        result.push({ stack: [...stack, value], ...candidate });
      }
    } else if (choice) result.push({ stack: [...stack, value], ...choice });
  }
  return result;
}

const dominates = (first, second) => first.gas <= second.gas && first.bytes <= second.bytes;

/** Exhaust the nondominated gas/byte labels. Limits never certify a frontier. */
export function solvePareto(problem, { stateLimit = 100_000, labelLimit = 500_000 } = {}) {
  check(isNat(stateLimit) && stateLimit >= 1, 'stateLimit must be positive');
  check(isNat(labelLimit) && labelLimit >= 1, 'labelLimit must be positive');
  const started = performance.now(), desiredCounts = counts(problem.target);
  const summary = { model: problem.model, states: 0, labels: 0, expanded: 0, edges: 0 };
  const finish = result => ({ ...summary, ...result, milliseconds: performance.now() - started });
  if (!equalCounts(counts([...problem.source, ...problem.missing]), desiredCounts)) {
    return finish({ status: 'infeasible', reason: 'count-balance' });
  }
  const generationChoices = [...new Set(problem.missing)].map(value => {
    const op = directOp(problem, value); return [value, op ? { op, cost: opCost(problem, op) } : null];
  });
  const nodes = new Map(); let serial = 0;
  const heap = new Heap((a, b) => a.cost.gas + a.cost.bytes - b.cost.gas - b.cost.bytes ||
    a.cost.gas - b.cost.gas || a.serial - b.serial);
  const initial = { stack: problem.source, cost: { gas: 0, bytes: 0 }, previous: null,
    op: null, serial: serial++ };
  const targetKey = stackKey(problem.target);
  nodes.set(stackKey(problem.source), [initial]); heap.push(initial);
  summary.states = 1; summary.labels = 1;
  while (heap.length) {
    const current = heap.pop(), key = stackKey(current.stack);
    if (!nodes.get(key)?.includes(current)) continue;
    summary.expanded++;
    if (key === targetKey) continue;
    if (nodes.get(targetKey)?.some(goal => dominates(goal.cost, current.cost))) continue;
    for (const next of moves(problem, current.stack, desiredCounts, generationChoices, true)) {
      summary.edges++;
      const frozen = Math.max(0, next.stack.length - problem.caps.swap - 1);
      if (!next.stack.slice(0, frozen).every((value, index) => value === problem.target[index])) continue;
      const nextKey = stackKey(next.stack), old = nodes.get(nextKey) ?? [];
      const cost = addCost(current.cost, next.cost);
      if (old.some(label => dominates(label.cost, cost))) continue;
      if (!old.length && nodes.size >= stateLimit) return finish({ status: 'limit', reason: 'state-limit' });
      if (summary.labels >= labelLimit) return finish({ status: 'limit', reason: 'label-limit' });
      const node = { ...next, cost, previous: current, serial: serial++ };
      nodes.set(nextKey, [...old.filter(label => !dominates(cost, label.cost)), node]);
      heap.push(node); summary.states = nodes.size; summary.labels++;
    }
  }
  const goals = nodes.get(targetKey);
  if (!goals) return finish({ status: 'infeasible', reason: 'exhausted' });
  const frontier = goals.map(goal => {
    const ops = []; for (let node = goal; node.op !== null; node = node.previous) ops.push(node.op);
    ops.reverse();
    return { cost: replay(problem, ops).cost, ops, instructions: ops.length };
  }).sort((a, b) => a.cost.gas - b.cost.gas || a.cost.bytes - b.cost.bytes);
  return finish({ status: 'optimal', frontier });
}

/** Dijkstra with a deterministic state limit. A limit is never an optimum. */
export function solve(problem, { stateLimit = 100_000 } = {}) {
  check(isNat(stateLimit) && stateLimit >= 1, 'stateLimit must be positive');
  const started = performance.now();
  const base = baseline(problem), desiredCounts = counts(problem.target);
  const summary = { model: problem.model, baseline: Number.isFinite(base) ? base : null,
    reserve: reserve(problem), states: 0, expanded: 0, edges: 0 };
  const finish = result => ({ ...summary, ...result, milliseconds: performance.now() - started });
  if (!equalCounts(counts([...problem.source, ...problem.missing]), desiredCounts)) {
    return finish({ status: 'infeasible', reason: 'count-balance' });
  }
  const generationChoices = [...new Set(problem.missing)].map(value => {
    const op = directOp(problem, value); return [value, op ? { op, cost: opCost(problem, op) } : null];
  });
  const nodes = new Map(); let serial = 0;
  const heap = new Heap((a, b) => compareCosts(problem, a.cost, b.cost) || a.serial - b.serial);
  const initial = { stack: problem.source, cost: { gas: 0, bytes: 0 }, previous: null,
    op: null, serial: serial++ };
  nodes.set(stackKey(problem.source), initial); heap.push(initial); summary.states = 1;
  while (heap.length) {
    const current = heap.pop(), key = stackKey(current.stack);
    if (nodes.get(key) !== current) continue;
    summary.expanded++;
    if (equalStack(current.stack, problem.target)) {
      const ops = []; for (let node = current; node.op !== null; node = node.previous) ops.push(node.op);
      ops.reverse();
      const checked = replay(problem, ops);
      return finish({ status: 'optimal', cost: checked.cost, score: checked.score, ops,
        instructions: ops.length, excess: checked.score - base });
    }
    for (const next of moves(problem, current.stack, desiredCounts, generationChoices)) {
      summary.edges++;
      const frozen = Math.max(0, next.stack.length - problem.caps.swap - 1);
      if (!next.stack.slice(0, frozen).every((value, index) => value === problem.target[index])) continue;
      const nextKey = stackKey(next.stack), old = nodes.get(nextKey), cost = addCost(current.cost, next.cost);
      if (old && compareCosts(problem, old.cost, cost) <= 0) continue;
      if (!old && nodes.size >= stateLimit) return finish({ status: 'limit', reason: 'state-limit' });
      const node = { ...next, cost, previous: current, serial: serial++ };
      nodes.set(nextKey, node); heap.push(node); summary.states = nodes.size;
    }
  }
  return finish({ status: 'infeasible', reason: 'exhausted' });
}

export function ratio(numerator, denominator) {
  if (denominator === 0) return numerator === 0 ? 1 : 'inf';
  return numerator / denominator;
}

export function compareCandidate(problem, candidate, oracle) {
  if (!candidate || candidate.status !== 'ok') return { status: candidate?.status ?? 'missing',
    feasibilityFailure: reserve(problem) };
  const checked = replay(problem, candidate.ops);
  if (candidate.cost) check(checked.cost.gas === candidate.cost.gas && checked.cost.bytes === candidate.cost.bytes,
    'production/model cost disagreement');
  const base = baseline(problem);
  return { status: 'ok', ...checked, excess: checked.score - base,
    certificates: candidate.certificates ?? {},
    exact: oracle.status === 'optimal' ? checked.score === oracle.score : null,
    costRatio: oracle.status === 'optimal' ? ratio(checked.score, oracle.score) : null,
    excessRatio: oracle.status === 'optimal' ? ratio(checked.score - base, oracle.score - base) : null,
    zeroExcessViolation: oracle.status === 'optimal' && oracle.score === base && checked.score > base };
}

/** A violating replayed witness disproves factor two because OPT is no larger. */
export function compareWitness(problem, candidateOps, witnessOps) {
  const candidate = replay(problem, candidateOps), witness = replay(problem, witnessOps);
  const base = baseline(problem);
  check(Number.isFinite(base), 'a valid witness must have a finite baseline');
  return { baseline: base, candidateScore: candidate.score, witnessScore: witness.score,
    candidateCost: candidate.cost, witnessCost: witness.cost,
    twiceExcessViolation: BigInt(candidate.score) + BigInt(base) > 2n * BigInt(witness.score),
    excessRatioAgainstWitness: ratio(candidate.score - base, witness.score - base) };
}

async function main(args) {
  const inputIndex = args.indexOf('--input'), limitIndex = args.indexOf('--state-limit');
  const stateLimit = limitIndex < 0 ? 100_000 : Number(args[limitIndex + 1]);
  const input = fs.readFileSync(inputIndex < 0 ? 0 : args[inputIndex + 1], 'utf8');
  for (const [index, line] of input.split('\n').entries()) {
    if (!line.trim()) continue;
    try {
      const problem = normalizeCase(JSON.parse(line));
      process.stdout.write(`${JSON.stringify({ id: problem.id, ...solve(problem, { stateLimit }) })}\n`);
    } catch (error) {
      throw new Error(`input line ${index + 1}: ${error.message}`, { cause: error });
    }
  }
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  main(process.argv.slice(2)).catch(error => { console.error(error.message); process.exitCode = 1; });
}
