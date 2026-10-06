<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Confirmed findings and open leads

Final stop snapshot: 2026-10-06 22:14 UTC. The user stopped the search for
a handoff. Production Permute has no concrete failing input yet.

## F1: KLEE accepts paths that skip the comparisons

Insert this one statement into a copied actual solc Permute body:

```cpp
if (m_data[0] == 0U) std::exit(0);
```

For size three and permutation `[1,0,2]`, the original KLEE runner reported
17 completed paths, no partial paths or errors, and a successful comparison.
Four paths terminated before the observations were compared.

Concrete witnesses include `[0,0,0]`, `[0,65280,65280]`, `[0,255,0]`, and
`[0,255,4294967295]`. Baseline code returns on these inputs. The variant exits.

Evidence: `spikes/clight-permute/build/equiv-alive2/klee-exit-probe/` and
the adjacent `klee-exit-probe.inc`. The corrected driver writes a completion
marker after comparisons and checks every resulting KTest for that marker.
It rejects all four omitted-comparison paths. The unmodified size-three
baseline passes all 13 marked paths. The agent has added parser tests and
a permanent early-exit mutation. Parent review and commits are pending.

This is a false equivalence result in the checking pipeline. It is not a
counterexample to the unchanged production C or its Rocq theorem.

## F2: SAW proof success can accompany partial symbolic execution

The same conditional early-exit change caused SAW to print both
`Symbolic simulation completed with side conditions` and
`Proof succeeded! equivalence`. The result extraction accepted a partial
symbolic result. Thus the printed proof success alone did not establish
return and comparison on every valid input.

The corrected runner rejects partial symbolic execution. Separate changes
to actual C and C++ source now yield `incomplete/partial_execution`, while
the unchanged size-two swap case proves. See
`spikes/clight-permute/tests/equiv-saw/completion.py`, `verify.py`, and
`test_driver.py`, plus that agent's status for logs.

This is also a checking-pipeline gap, not an unchanged-production witness.

## F3: SAW can retain an old result after a failed build

A failed build could leave a previous result JSON visible. The runner now
clears the result before building. The agent reports a passing regression.
The code and evidence are still uncommitted.

## F4: The original Rocq check records but does not reject new axioms

An isolated copy of the actual complete-call theorem was changed to
`Admitted`. Another copy used an explicit false axiom. Both compiled, and
`coqchk` accepted them. This is expected behavior from a kernel that permits
declared assumptions; `coqchk` alone is not an axiom-policy check.

`check-assumptions.py` now permits only the six inherited assumptions found
in the baseline report. `tests/proof-challenge/ProofContract.v` states the
required public theorem type independently. The integrated baseline passed.
The isolated guard driver initially mixed warnings into the assumptions
report. That output capture is corrected. The repeat passed baseline,
admitted-theorem, and false-axiom controls before the user stop. The last
two controls remain unfinished in that repeat; do not call it complete.

Evidence: `spikes/clight-permute/build/proof-challenge/guards/` and
`/tmp/permute-proof-guards.log`.

## F5: Coverage can pair a stale binary with changed source

`guided-coverage.sh` does not currently bind the coverage binary to the
current source hashes before rendering source text. An edit without rebuild
can mislabel old counters. The saved campaign source hashes were checked
and match; their current reported totals are not invalidated by this lead.
A manifest check and stale-source/binary negative tests remain to be added.

## F6: KLEE function-coverage parsing counted call-arc rows

The first parser counted callgrind call-arc summaries as instruction rows.
This could report more covered instructions than total instructions. The
agent fixed it and added regression tests. It does not change the path,
assertion, or error results. Raw summaries are being recomputed.

## F7: uninitialized Clight temporary accepted by the printer

Clight can propagate `Vundef` through `Sset` and discard it. A printed C
read of an uninitialized automatic scalar can have undefined behavior.
The current printer does not check definite assignment for all accepted
ASTs. The isolated witness is now confirmed. A function with the normal
ABI and body `v8 = v9; return 0U;` has a checked Clight `eval_funcall`
theorem returning zero for all arguments. The unchanged printer accepts
it. GCC 15.3 reports the uninitialized `v9` read. The C automatic-local
read needs a separate definedness argument; the Clight result alone does
not provide it.

The stronger reproduction prefixes the actual Permute AST with
`Sset i (reg i)`. Its proof preserves the existing full Clight call's
result, final memory, and trace. Both `coqc` and full `coqchk` passed.
The unchanged printer emits `v8 = v8;` before initialization. GCC and
Clang both report the uninitialized read. Corrected KLEE still accepts
that C variant for all 13 marked size-three paths. Frama-C's independent
initialization check instead generates an obligation `Prove: false`.

Artifacts: `spikes/clight-permute/build/equiv-saw/undef-probe/`,
`build/equiv-alive2/klee-uninitialized-copy/`, and
`build/frama-c/undef-prefix-1/initialization-wp.log`, all under the spike.
The checking agent confirmed that current printer sources match the
compiled sources used for the probe. The unchanged Permute's temporary
reads appear initialized. This is a demonstrated proof/translation-chain
gap under mutation, not a failing input for the unchanged production AST.

## Explicit boundaries, not production failures

- Forced allocation failure makes the allocation-free C succeed while the
  C++ oracle throws `bad_alloc`. Current equivalence claims explicitly
  assume successful allocation. The separate test confirms that boundary.
- Fil-C misses a one-element overrun within allocator rounding in its
  detection control. ASan and other evidence remain separate.
- The oracle does not compare the complete persistent `Emission::m_mapping`
  object. The C contract makes scratch arrays unspecified. A future claim
  about the full Emission object needs another relation.
- Malformed-permutation rejection is not universally proved.
- ACSL/source-C correctness and full C/C++ equivalence through size 1024
  remain incomplete.
