<!-- SPDX-License-Identifier: GPL-3.0-or-later -->

# Frama-C work status

## Current pause: 2026-10-07

The user asked to wrap up and commit. All runs from this task have stopped.
The [evidence archive](../../../spikes/clight-permute/tests/results/frama-c-2026-10-07/README.md)
contains the proof inputs, reports, SMT obligations, controls, and hashes.

| Component | Valid / scheduled goals | Saved run |
| --- | ---: | --- |
| Safety | 641/641 | `full-final-20261007/safety` |
| Termination | 337/337 | `full-final-20261007/termination` |
| Target | 313/313 | `full-final-20261007/target` |
| Trace | 393/393 | `trace-promoted-20261007/trace` |
| Status | 495/495 | `status-promoted-v14-20261007/status` |
| Success | 570/570 | `success-source-controls-final-20261007/baseline` |

All six components pass individually. The 2,749 obligations include helper
lemmas and repeated facts across components. A separate check of the saved
reports and annotated inputs passes the current report and composition
checks. It checks identical C tokens, equal input conditions, matching
contract definitions, and coverage of every full-contract clause.

The input domain remains all valid permutations of lengths 1–1024, arbitrary
initialized unsigned 32-bit data, and six valid, disjoint arrays. Scratch
arrays need no initial contents. This contract does not cover invalid inputs.
Termination is proved separately from partial correctness on the same C
and inputs. Status excludes return value two; the proved
`guarded_success_iff` lemma combines the guarded success conditions into
the original equivalence. See the [tool review guide](../../../spikes/clight-permute/tests/frama-c/README.md).

Seven control suites and all 52 tool tests pass. The status source suite
rejects both faulty mutations, but reports failure because the wrong-target
case expects `collected_changed` instead of the earlier failed prerequisite
`collect_value`. That expectation remains to be corrected and checked.
The success source suite stopped after its baseline passed. Its parentheses
case was interrupted; its two faulty variants were not run.

The fresh combined run stopped during trace. It has no completed root
summary and is not a completed full run. Finish that run in a new directory
and complete the two source control suites before declaring validation
complete. No further proof jobs were started for this wrap-up.

The resumed work also found an omitted prerequisite in an early focused
mutation control ([F10](../FINDINGS.md#f10-a-focused-frama-c-mutation-test-omitted-a-failed-prerequisite)).
Whole-component controls now include all prerequisites. A memory-dependent
loop variant produced a false decrease condition in a terminating one-cell
probe; the retained ghost-counter proof avoids that encoding issue. A missing
reverse-scan invariant was an annotation gap. None is a bug found in unchanged
production C. A 10-second safety timeout also cleared in the 30-second run.

These are Frama-C/WP and SMT results. They are not proof terms checked by
Rocq, and they do not prove the printer, compiler, or Lean–Rocq bridge.
Production C and the Rocq proof are unchanged. The sections below preserve
earlier states; they do not describe the current component results.

## Historical pause: 2026-10-07

The user asked to wrap up this work and pause. No Frama-C or solver process
remains active. This overrides the earlier deadline. The result is still
**641/642 memory goals valid**, with main-loop termination unproved.
Initialization controls and all 25 tool tests pass.

The final [rank experiment](../../../spikes/clight-permute/tests/results/extended-2026-10-06/frama-rank-experiments/README.md)
proves the all-integer bounds lemma in a copied source. Frame and update
remain unproved. All reports, proof scripts, SMT obligations, and diagnostic
sources are archived. The production rank-lemma file is unchanged.

After user authorization to resume, the next step is to instantiate the
positive induction hypothesis at `n - 1` for frame/update. Check all lemma
prerequisites before use. Then add the main-loop measure and finish the
source-C contract. The historical results below do not constitute a full
source-C proof.

## Resumed check

A later focused check now proves all nine fill-invariant and target-
initialization obligations on the production C. A parentheses control
also passes. Removing the target store leaves the fill-invariant
preservation goal unproved. The WP strategy instantiates the existing
surjection premise at the index in the outer goal access. It adds no
assumption and changes no C token. The runner now applies prover and
tactic selection in the WP stage after `-then`. All 25 tool tests pass.
See the [initialization archive](../../../spikes/clight-permute/tests/results/extended-2026-10-06/frama-initialization/README.md).

The full memory pass `memory-target-strategy` then completed with
**641/642 explicit goals valid**. Only main-loop termination remains
unproved. The runner returns nonzero. Its
[archive](../../../spikes/clight-permute/tests/results/extended-2026-10-06/frama-memory-strategy/README.md)
retains the reports, sources, proof scripts, and selected SMT obligations.
This is still an incomplete memory contract and not the full functional
proof. The original count/rank experiment leaves all three lemmas unproved
under `build/frama-c/rank-lemmas-current-v2/`. The later all-integer variant
proves only the bounds goal, as recorded above.

After the user's resume instruction, `memory-resumed-9` ran with the final
solver setup. It completed with 635/642 valid goals, one unknown, and six
timeouts. The runner correctly reported failure. Target initialization and
main-loop termination remain open; the other pending goals are listed in
`build/frama-c/memory-resumed-9/summary.json`. This run does not supersede
the earlier 642/644 memory result.

All 24 annotation, report, version, and solver-wrapper tests passed in the
Frama-C Nix shell. An earlier invocation outside that shell failed because
the required solver was unavailable; that log remains in `/tmp`.

The stopped handoff below records the earlier work. See
[the current main status](../WORKING_STATUS.md) for the resumed scope.

Final handoff: **2026-10-06 22:13 UTC**. **Work is stopped at the user's
request. No Frama-C or solver job from this task is still running.**
The prior deadline was 2026-10-07 09:00 UTC (11:00 CEST). The stop request
overrides the earlier instruction to continue until that deadline.

There is **no complete Frama-C source-C proof yet**. No C defect or new native
counterexample has been found in this work. A valid local WP goal is not a
complete safety proof while a required loop invariant remains unproved.

## Source and contract

The production file is `spikes/clight-permute/permute.c`. Its SHA-256 remains:

```
a120dccaaa1a7783231f7b4482f76f515ef6c099f4e0e73279f1228e634cfb78
```

`tests/frama-c/annotate.py` adds ACSL comments to a copy. It checks that all C
tokens, after removal of comments and white space, match the production
file. It checks the function, seven loops, and selected statement anchors.
It does not change the printer, AST, algorithm, or production C file.
Each named proof run retains its annotated source, source hash, command,
per-goal JSON report, log, and generated SMT obligations under
`spikes/clight-permute/build/frama-c/`.

The full contract covers every valid permutation, all initialized 32-bit
unsigned input values including duplicates, and every size `1 <= n <= 1024`.
It requires six valid, disjoint arrays. Only data and permutation must be
initialized on entry. It asks for:

- Exact target values from the original data and destination permutation.
- Success iff every original value deeper than 16 already has its target value.
- Correct final data on success.
- No defensive return value 2 on this domain.
- Valid trace depths, initialized trace entries, and exact recursive trace replay.
- Every trace step exchanges different values.
- Valid partial trace and exact blocked position/excess on a blocked return.
- Bounds, initialization, frame conditions, and termination.

A separate memory pass uses the same input domain and the same C tokens.
It leaves the functional theorem to the full pass. It still requests
termination; the absent main-loop rank is an unproved obligation in that
pass. It does not assume termination or add safety assumptions.

The independent C/AST memory review is at
[../review-memory.md](../review-memory.md). It found no C/AST mismatch.
The caller must supply live typed arrays with the stated capacities and
exclusive access. The Clight theorem uses separate memory blocks at offset
zero. Its byte-permission model does not itself establish ISO C object type,
lifetime, or subobject rules. A completed Clight call theorem does not prove
the printer or GCC/Clang translation.

## Recorded results

These totals count explicit entries in `goals.json`. Frama-C's terminal
summary can add automatic termination or unreachable-path entries; those
extra entries are not included in the table.

| Run | Explicit goals | Valid | Pending | Notes |
| --- | ---: | ---: | ---: | --- |
| `memory-target-strategy` | 642 | 641 | 1 | Initialization strategy and prover selection in the WP stage. Only main-loop termination is pending. |
| `full-1` | 774 | 604 | 170 | Z3, 3-second limit; full iff and trace contract. |
| `full-2` | 774 | 657 | 117 | Z3/CVC5, 10-second limit; full iff and trace contract. |
| `memory-1` | 597 | 572 | 25 | Z3, 5-second limit. |
| `memory-2` | 601 | 586 | 15 | Added permutation invariant; Z3, 15 seconds. |
| `memory-3` | 601 | 590 | 11 | Added CVC5; 10 seconds. |
| `memory-4` | 601 | 565 | 36 | Solver configuration experiment. CVC5 failed with a Why3 `Not_found` error; this run is not a success. |
| `memory-5` | 605 | 595 | 10 | Added original-input frame facts; Z3/CVC5, 10 seconds. Finished while this status file was written. |
| `memory-6` | none | none | none | ACSL parse error: multiple statement assertions in one comment. Corrected before `memory-7`. |
| `memory-7` | 644 | 642 | 2 | Best completed memory pass. Open goals: target initialization and main-loop termination. |
| `memory-8` | 642 | 626 | 16 | CVC5 registry/configuration failure. Z3 completed the other goals. This is not an improvement over `memory-7`. |
| `target-init-direct` | 9 | 8 | 1 | Focused diagnostic; target-initialization establishment still pending. |
| `lemmas-1` | 3 | 0 | 3 | Induction experiments for count bounds, frame, and update lemmas. No lemma is accepted as proved. |

The best completed memory pass, `memory-7`, still needs main-loop
termination and target initialization after validation. Its other explicit
runtime, initialization, array-frame, and bound goals are discharged. That
does not establish full safety while target initialization is open.
The full proof also needs matching
completeness, the main-loop rank, count updates, trace-prefix frame facts,
and the source-C reachability argument. The separate Rocq reachability
proof does not fill these source-C obligations.

Frama-C reports skipped generic guards for pointer alignment and function
pointer calls. This function has no function pointer calls or casts. The
Typed model and the live typed-array caller contract must justify alignment;
the warning is retained in every log.

`run.py` returns nonzero if a goal is unproved. It checks the scheduled goal
count, unique goal IDs, required postconditions, memory/initialization
categories, loop categories, and termination coverage. Negative report tests
check empty reports, removed goals/categories, removed trace properties,
duplicate IDs, false success fields, timeouts, smoke goals, and wrong
function names. Five annotation tests passed before later annotation edits;
they have not been rerun after the stop request. Twelve report tests passed.
Three version-header tests and four tests with the actual CVC5 binary passed.
These tests do not turn an incomplete proof into a complete proof.

## Stopped jobs and files

The former active jobs all finished before the final process scan. No signal
was needed. `build/frama-c/stopped-jobs.json` records an empty owned-process
set. The earlier process snapshot is retained in
`build/frama-c/processes-status-2204.json`.

| Completed run | Former session ID | Former OS PID | Log |
| --- | ---: | ---: | --- |
| `full-2` | 63127 | 52747 | `build/frama-c/full-2/wp.log` |
| `memory-7` | 52755 | 59328 | `build/frama-c/memory-7/wp.log` |

Each was launched from `spikes/clight-permute` with:

```
nix develop --impure --expr 'import ./tests/frama-c/shell.nix' \
  --command python3 tests/frama-c/run.py --mode MODE --name RUN --timeout 10
```

The exact Frama-C command is in each run's `manifest.json`. New experiments
may have a log and per-goal JSON outside a named run directory. Relevant
source files are `tests/frama-c/shell.nix`, `annotate.py`, `run.py`,
`test_annotations.py`, `test_report.py`, `test_solver_version.py`,
`test_solver_wrapper.py`, and `lemmas.acsl`. The last file
contains unproved lemma obligations and proof-strategy experiments; it is not
yet included as a proved library by the full C annotation generator.

## License checks

See [../../../spikes/clight-permute/tests/frama-c/LICENSE_AUDIT.md](../../../spikes/clight-permute/tests/frama-c/LICENSE_AUDIT.md).
The proof shell sets `allowUnfree = false`. The checked versions are
Frama-C 33.0, Why3 1.8.2, Z3 4.16.0, CVC5 1.3.4, and Python 3.14.7.
Frama-C and Why3 use LGPL terms with the exceptions and component notices
listed in the audit. Z3 is MIT. The selected CVC5 binary package is marked
GPL-3.0-only. The local files are GPL-3.0-or-later.

The checked runtime closures contain no Alt-Ergo. The runner permits prover
detection only for Z3 and CVC5, with a local Why3 configuration.
Why3's top-level license warns about possible non-commercial GUI icon sets.
Its installed image tree contains only the Why3 logo and FatCow icons; the
FatCow notice is CC-BY-3.0. No installed non-commercial icon set was found.
The tool audit checks package metadata and installed notices; it is not a
review of every source file in every transitive dependency.

Why3 does not parse the shorter CVC5 1.3 version line. The current runner
writes a local adapter which changes only the version-header format. It
keeps the actual version number and all license text. Every solver call
executes the real CVC5 binary with the original arguments. Native and adapted
SAT/UNSAT calls passed, and an invalid solver option remained an error.

A second issue came from option order: Frama-C resolved a solver name before
it read the local Why3 configuration. `run.py` now places the local config
before prover selection. An isolated follow-up used the correct CVC5 1.3.4
identifier and had no `Not_found` error. The later memory passes above use
the corrected solver setup and WP-stage options. Do not
treat the old CVC5 failures in `memory-4` or `memory-8` as proof results.

## Uninitialized-copy control

The copied source under `build/frama-c/undef-prefix-1/` inserts `v8 = v8;`
before the first output write. The production source is unchanged. This
tests the known difference between a Clight `Vundef` copy and a C read of an
uninitialized automatic variable.

Frama-C retained the assignment. Its RTE pass added
`assert rte: initialization: \\initialized(&v8);` immediately before it,
at `rte.c:56`. WP reduced the first initialization obligation to
**`Prove: false`** under the normal valid-permutation contract. This is an
explicit failed safety condition, not a timeout used as a witness. The log
is `initialization-wp.log`; the report is `initialization-goals.json`.
The mutant source, token-preserving annotated copy, and hashes are retained.

The first attempted property selector produced zero goals. Its `wp.log`
is retained as a failed diagnostic. The corrected selector was
`-wp-prop initialization`. No empty report is accepted by the proof runner.

## Completed validation

The MSan work is complete. See
[../../../spikes/clight-permute/tests/MSAN_RESULTS.md](../../../spikes/clight-permute/tests/MSAN_RESULTS.md).
The deliberate uninitialized-read probe failed as expected. The initialized
control passed. The instrumented target replayed 846 saved inputs, with 802
unique hashes, and ran 73,316 new executions in 61 seconds. No target MSan
report or C/C++ mismatch was found. The MSan runner records and retries only
the exact pre-main shadow-memory mapping failure. It does not retry target
errors. These campaigns have not been repeated for this status report.

The challenge matrix is complete. See
[../../../spikes/clight-permute/tests/challenge/README.md](../../../spikes/clight-permute/tests/challenge/README.md).
All 17 variants built. Fourteen behavior changes each have a concrete test
failure. The baseline and two behavior-preserving controls passed. Build
failures, crashes, and timeouts did not count as successful witnesses.
Each passing run checked 695 valid cases with ten native calls per case,
plus invalid-API cases. Source-regeneration rejection is recorded separately
from semantic tests. No unrun formal verifier is reported as a success.

## Historical resume instructions

Do not resume unless the user authorizes it. After authorization, use a new
run name so that existing artifacts remain intact:

```
cd spikes/clight-permute
nix develop --impure --expr 'import ./tests/frama-c/shell.nix' \\
  --command python3 tests/frama-c/run.py --mode memory --name memory-9 --timeout 10
```

For the full theorem, use `--mode full --name full-3`. These commands use the
latest annotation generator and final solver-configuration order. Their
expected current result is still failure while required goals are open.

The remaining proof work after user authorization is:

1. Finish frame/update induction and retain original statements as corollaries.
2. Use the checked rank facts to prove main-loop termination.
3. Complete the full functional contract, including trace replay and the
   success condition. Target initialization is already valid in the memory pass.
4. Continue negative controls for each added proof step and result check.

No filesystem fault or chaos tests are planned; the user excluded them.
