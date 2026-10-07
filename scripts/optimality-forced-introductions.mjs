#!/usr/bin/env node
/** Offline reachability check with a limit on direct introductions of one value. */
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import { normalizeCase, reserve } from './optimality-oracle.mjs';

export function reachableWithDirectLimit(problem, value, limit, stateLimit = 200000) {
  const tracked = new Set(Array.isArray(value) ? value : [value]);
  const counts = stack => stack.reduce((result, item) => result.set(item, (result.get(item) ?? 0) + 1), new Map());
  const desired = counts(problem.target), key = state => JSON.stringify([state.stack, state.direct]);
  const first = { stack: problem.source, direct: 0, ops: [] }, queue = [first], seen = new Set([key(first)]);
  for (let index = 0; index < queue.length; index++) {
    const current = queue[index], stack = current.stack;
    if (JSON.stringify(stack) === JSON.stringify(problem.target)) {
      return { status: 'reachable', states: seen.size, ops: current.ops, direct: current.direct };
    }
    const next = [], push = (stack, op, direct = current.direct) =>
      next.push({ stack, direct, ops: [...current.ops, op] });
    for (let depth = 1; depth <= Math.min(problem.caps.swap, stack.length - 1); depth++) {
      const copy = [...stack], lower = copy.length - depth - 1;
      if (copy[lower] === copy.at(-1)) continue;
      [copy[lower], copy[copy.length - 1]] = [copy.at(-1), copy[lower]];
      push(copy, ['swap', depth]);
    }
    if (stack.length < problem.target.length) {
      const present = counts(stack);
      for (const [added, count] of desired) {
        if ((present.get(added) ?? 0) >= count) continue;
        const position = stack.lastIndexOf(added), depth = stack.length - position;
        if (position >= 0 && depth <= problem.caps.dup) push([...stack, added], ['dup', depth]);
        if (tracked.has(added) && current.direct >= limit) continue;
        const direct = current.direct + (tracked.has(added) ? 1 : 0);
        if (added.startsWith('l:')) push([...stack, added], ['push', added], direct);
        else if (added.startsWith('v:') && problem.spills.includes(Number(added.slice(2)))) {
          push([...stack, added], ['load', Number(added.slice(2))], direct);
        }
      }
    }
    for (const state of next) {
      const frozen = Math.max(0, state.stack.length - problem.caps.swap - 1);
      if (!state.stack.slice(0, frozen).every((item, position) => problem.target[position] === item)) continue;
      const id = key(state); if (seen.has(id)) continue;
      if (seen.size >= stateLimit) return { status: 'limit', states: seen.size };
      seen.add(id); queue.push(state);
    }
  }
  return { status: 'unreachable', states: seen.size };
}

function main(output) {
  const prefixRun = process.argv.includes('--prefix-run');
  const initialReserve = process.argv.includes('--initial-reserve');
  const sourceAlphabet = initialReserve ? ['l:0', 'l:1', 'v:42'] : ['l:0', 'l:1'];
  const words = (alphabet, n) => n === 0 ? [[]] : words(alphabet, n - 1).flatMap(rest => alphabet.map(v => [...rest, v]));
  let checked = 0, states = 0, first = null;
  const bounds = {};
  outer: for (let n = 2; n <= 4; n++) for (const source of words(sourceAlphabet, n)) {
    for (const births of [2, 3]) for (const target of words(['l:0', 'l:1', 'v:42'], n + births)) {
      if (target[n - 2] !== 'v:42') continue;
      const problem = normalizeCase({ source, target, spills: [42], caps: { swap: 2, dup: 2 } });
      if (problem.missing.filter(v => v === 'v:42').length < 2 || !reserve(problem)) continue;
      const frozen = Math.max(0, n - 3);
      const boundary = n >= 3 && target[frozen] === 'v:42' ? 1 : 0;
      if (initialReserve && source.slice(frozen).filter(v => v === 'v:42').length !== boundary) continue;
      let run = 0;
      while (target[n - 2 + run] === 'v:42') run++;
      const required = prefixRun ? Math.min(problem.missing.filter(v => v === 'v:42').length, run + 1) : 2;
      const result = reachableWithDirectLimit(problem, 'v:42', required - 1);
      checked++; states += result.states;
      bounds[required] = (bounds[required] ?? 0) + 1;
      if (result.status !== 'unreachable') { first = { problem, required, result }; break outer; }
    }
  }
  const shorter = normalizeCase({ source: ['l:0'], target: ['v:42', 'l:0', 'v:42'],
    spills: [42], caps: { swap: 2, dup: 2 } });
  const report = { status: 'finite reachability evidence, not a proof', checked, states, first,
    completed: first === null, boundVersion: prefixRun ? 'min(H(v), prefixRun(T,p,v)+1)' : 'two introductions', bounds,
    condition: initialReserve ? 'n >= R; p=n-R; T[p]=v; window.count(v)=boundary.count(v); H(v)>=2' :
      'n >= R; p=n-R; T[p]=v; v absent from source; H(v)>=2',
    domain: { cap: 2, sourceLengths: [2, 3, 4], sourceAlphabet,
      targetAlphabet: ['l:0', 'l:1', 'v:42'], births: [2, 3], directLimit: 'proposed lower bound minus 1', stateLimit: 200000 },
    shorterStack: { problem: shorter, result: reachableWithDirectLimit(shorter, 'v:42', 1) } };
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify(report, null, 2));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  main(process.argv[2] ?? '/tmp/forced-introduction-check.json');
}
