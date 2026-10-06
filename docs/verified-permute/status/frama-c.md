<!-- SPDX-License-Identifier: GPL-3.0-or-later -->

# Frama-C work status

Updated: **2026-10-06 22:04 UTC**. The active bug-hunt deadline is
**2026-10-07 09:00 UTC** (11:00 CEST). Proof jobs continue.

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
| `full-1` | 774 | 604 | 170 | Z3, 3-second limit; full iff and trace contract. |
| `memory-1` | 597 | 572 | 25 | Z3, 5-second limit. |
| `memory-2` | 601 | 586 | 15 | Added permutation invariant; Z3, 15 seconds. |
| `memory-3` | 601 | 590 | 11 | Added CVC5; 10 seconds. |
| `memory-4` | 601 | 565 | 36 | Solver configuration experiment. CVC5 failed with a Why3 `Not_found` error; this run is not a success. |
| `memory-5` | 605 | 595 | 10 | Added original-input frame facts; Z3/CVC5, 10 seconds. Finished while this status file was written. |
| `memory-6` | none | none | none | ACSL parse error: multiple statement assertions in one comment. Corrected before `memory-7`. |
| `target-init-direct` | 9 | 8 | 1 | Focused diagnostic; target-initialization establishment still pending. |
| `lemmas-1` | 3 | 0 | 3 | Induction experiments for count bounds, frame, and update lemmas. No lemma is accepted as proved. |

The most recent completed memory pass, `memory-5`, still needs main-loop
termination, target initialization after validation, and some array frame
and initialization facts across swaps. The full proof also needs matching
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
function names. Five annotation tests passed. Twelve report tests passed.
These tests do not turn an incomplete proof into a complete proof.

## Active jobs and files

At this update, these sessions continue. Session IDs are tool-session IDs,
not operating-system PIDs.

| Run | Session ID | OS PID | Log |
| --- | ---: | ---: | --- |
| `full-2` | 63127 | 52747 | `build/frama-c/full-2/wp.log` |
| `memory-7` | 52755 | 59328 | `build/frama-c/memory-7/wp.log` |

The process snapshot and complete command lines are retained in
`build/frama-c/processes-status-2204.json`.

Each was launched from `spikes/clight-permute` with:

```
nix develop --impure --expr 'import ./tests/frama-c/shell.nix' \
  --command python3 tests/frama-c/run.py --mode MODE --name RUN --timeout 10
```

The exact Frama-C command is in each run's `manifest.json`. New experiments
may have a log and per-goal JSON outside a named run directory. Relevant
source files are `tests/frama-c/shell.nix`, `annotate.py`, `run.py`,
`test_annotations.py`, `test_report.py`, and `lemmas.acsl`. The last file
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

Why3 does not parse the shorter CVC5 1.3 version line. An attempt to fill its
version field caused `Not_found` failures. The current runner retains the
working detected identifier and saves the actual `cvc5 --version` output.
This tool compatibility issue is still under review.

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

## Next work

1. Finish and inspect the active per-goal reports.
2. Prove target initialization through an explicit finite-surjection helper.
3. Complete local array frame and trace-append facts without changing C tokens.
4. Prove the count/rank and trace-frame lemmas, then use them in the full pass.
5. Close normalization completeness and the source-C iff theorem.
6. Continue negative checks of proof-result handling and all requested bug classes.

No filesystem fault or chaos tests are planned; the user excluded them.
