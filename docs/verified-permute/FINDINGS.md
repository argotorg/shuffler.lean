<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Confirmed findings and open leads

Resumed verification is recorded in [WORKING_STATUS.md](WORKING_STATUS.md).
The review now starts with the [core definitions and public theorems](README.md).
The earlier stop snapshot below remains historical evidence.

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

After resumption, a fresh eight-control campaign completed. Baseline passed;
admissions, false axioms, shadowed names, unsafe recursion, unsafe positivity,
an impossible precondition, and a `True` postcondition had their expected
rejections. Both unsafe-typing variants pass `coqchk` itself. The added
kernel-context policy rejects them and checks full axiom names. The
short-name collision did not bypass the original complete theorem check.
The fresh sources and logs are archived under
`spikes/clight-permute/proof-results/reviewed-2026-10-06/guards/`.

Evidence: `spikes/clight-permute/build/proof-challenge/guards/` and
`/tmp/permute-proof-guards.log`.

## F5: Coverage can pair a stale binary with changed source

The original `guided-coverage.sh` did not bind the coverage binary to the
current source hashes before rendering source text. An edit without rebuild
could mislabel old counters. The saved campaign source hashes were checked
and match; their current reported totals are not invalidated by this lead.
A source/binary manifest check has now been added. Eleven tests pass,
including rejection by the actual reporting script for stale sources,
stale binaries, and invalidated builds. A fresh native replay retained
72/76 LLVM outcomes and 72/84 exported outcomes. The original reports
remain archived; their matching source hashes are unchanged.

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

The later [candidate assignment check](../../spikes/clight-permute/tests/initialization/README.md)
accepts the actual Permute AST and rejects the self-copy prefix. Its
expression-read lemma and computed Permute result are kernel checked.
Twenty-one examples and seven weakened-checker controls have their
expected results. Later kernel checks establish statement-level soundness
for an explicit control-path model and connect terminating Clight
executions to that model. The connection retains actual branch decisions
and intermediate states. The abstract prefix proof has no concrete
small-step or divergence link yet. Memory byte initialization and the C
translation are separate; this checker is outside the production pipeline.
F7 remains open. See the
[execution proof archive](../../spikes/clight-permute/tests/results/extended-2026-10-06/assignment-execution-proof/README.md).

## F8: KLEE can pass after a feasible branch is not explored

A copied production C body adds this statement after clearing `out`:

```c
if (v2[0] == 42U) return 2U;
```

At length one with permutation `[0]`, normal KLEE exploration rejects the
copy with an assertion witness: input `[42]` returns 2 while the oracle
returns 0. A controlled run with `--max-forks=0 --rng-initial-seed=1`
instead reports one completed path, zero partial paths, no errors, and a
valid completion marker. The current runner reports `pass=true` and exits
zero. The feasible failing branch was not explored.

The log records `skipping fork (max-forks reached)` and the statistics record
an inhibited fork. KLEE can also inhibit forks above its memory cap; the
current runner does not check that counter. The explicit fork-limit control
demonstrates the result-gate gap. It does not show that a default production
run hit its memory cap.

Evidence: `spikes/clight-permute/build/equiv-alive2/path-loss-probe/`,
including the changed source, normal rejection, limited false pass, wrapper
options, logs, bitcode, manifests, and KTests. The false pass is under
`forks-disabled-seed-1/`. The runner now rejects inhibited forks and abnormal
state termination using the statistics database, and rejects skip-fork
warnings. Both symbolic runners use this check. Nine policy tests and four
actual KLEE controls pass. The limited faulty source and limited baseline
are both rejected; the unrestricted baseline passes and the unrestricted
faulty source has its assertion witness.

All 153 retained completed cases at lengths one through five were checked
for inhibited forks, early termination, and solver termination; all these
counters are zero. This finding does not invalidate those completed cases.
It is a checking-pipeline defect, not an unchanged-production C failure.

The stronger check also passed an audit of 167 retained cases and 71,587
marked paths: lengths one through five, the selected length-six swap, and
the thirteen restricted large profiles. A fresh lengths-one-through-three
run passed all nine cases and 85 paths with the new check.

## F9: Code under test can restrict inputs through the KLEE API

A copied C body contains:

```c
klee_assume(v2[0] != 42U);
if (v2[0] == 42U) return 2U;
```

At length one, the actual runner reports success on one completed path,
with a completion marker and zero inhibited forks, partial paths, or errors.
The assumption inside the program under test excludes input 42. The same
faulty return without the assumption is rejected with an assertion witness.
The reported unrestricted-input comparison therefore depends on a condition
introduced by the tested source, not the declared harness domain.

This probe adds a verifier API call; it is not a failure of unchanged
production C and is outside the printer's accepted Clight subset. The
result gate needs to separate trusted harness assumptions from code under
test before this workflow is used for more programs.

Both runners now inspect the compiled program symbols before linking the
trusted harness. They reject definitions or references whose names start
with `klee_`. The comparison checks the C, C++ oracle, and allocator wrapper
modules; the rejection runner checks its C module. Eight symbol-boundary
tests pass, including actual runner rejection of declared and defined
`klee_assume` functions. The nine rejection tests and four fork-loss controls
also pass after this change. All 167 retained program-module sets pass the
new symbol check.

Evidence: `spikes/clight-permute/build/equiv-alive2/klee-assume-probe/`.
A separate `klee_silent_exit` probe was rejected because it has a partial
path. An `llvm.assume` probe did not hide the faulty return under the current
KLEE settings; the assertion witness was retained. Do not report either
of these two controls as a false pass.

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
