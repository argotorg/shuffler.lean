<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Permute working status

Final stop snapshot: **2026-10-06 22:14 UTC**. This is a handoff, not a
completion report. **Work is stopped at the user's request.** All child
agents have stopped their jobs. Root stopped its remaining guard-test job.
No verification work was restarted after the stop clarification.

Latest updates since the initial snapshot:

- The uninitialized-copy finding now applies to a prefix on the actual
  Permute AST. Its full-call result, final memory, and trace are preserved
  by a proof accepted by `coqc` and `coqchk`. The unchanged printer emits
  `v8 = v8;` before initialization. GCC and Clang warn; Frama-C generates
  an initialization obligation that reduces to `false`.
- Corrected KLEE campaign stopped at 69/153 cases and 21,361 marked paths.
  All 13 restricted large profiles completed, with 99 marked paths. The
  two mutation campaigns completed: 12 local and 16 shared controls.
- Best completed Frama-C memory pass: **642/644** goals. The open goals
  are target initialization after validation and main-loop termination.
  Best recorded full pass: **657/774**. Neither is a complete proof.
- Root's guard output capture is fixed. Baseline, admitted-theorem, and
  false-axiom controls passed their expected checks. The repeat was stopped
  during the remaining controls; do not call the whole rerun complete.
- The promoted reachability build now fails on ambiguous `SolcModel.vo`
  load paths, after the first Nix path issue was corrected. Use an isolated
  build directory to avoid the old root-level objects. Do not claim the
  promoted modules or full-call corollary are checked yet.

## Paused objective and former deadline

Find a concrete bug or gap in the generated C, its Clight/Rocq proof chain,
or its relation to the actual solc C++ Permute operation. Continue until
**2026-10-07 09:00 UTC / 11:00 CEST**, unless the user changes the deadline.
The user subsequently requested a stop and handoff to a new agent. That
request overrides the earlier deadline. The objective is unfinished and is
to be paused, not marked complete. There is no user-set token budget.

The user authorizes local defensive testing, source changes, reviews,
parallel agents, and commits. They explicitly ask for continued effort and
for all bug categories below. Filesystem chaos tests are excluded at their
request. Resume verification only under the new agent's user instruction.

Required constraints:

- Do not depend on non-commercial-only code. Use only CompCert's expressly
  LGPL source subset. Do not use `clightgen`, `ccomp`, or compiler passes.
- New project code is GPL-3.0-or-later. Preserve upstream notices.
- Keep the printer small and reviewable. It is trusted code.
- Use actual production C and pinned solc bodies in tests and comparisons.
- Report incomplete proofs, timeouts, path restrictions, assumptions, and
  unreachable branches. Do not turn any of these into a proof success.
- Use Simple Technical English. Keep commit messages factual and direct.

## Repository and commits

Workspace:
`/home/me/.local/state/subagent/2e500090cbba/jpkjfmrfie/repo`

Branch: `bbu-recursive`. Original base:
`0e92d2a1a9b720a9e127814d8c2c4192055638ce`.

Last development commit before status snapshots: `416cd6c`.
Initial handoff snapshot commit: `08db708`.
The initial Rocq work, LGPL selection, Clight implementation, printer,
proof layers, solc tests, guided fuzzing, research report, and Fil-C results
are committed as 15 separate commits. See [review-guide.md](review-guide.md)
for the ordered commit list and scope.

The newer symbolic tools, MSan report, source mutations, proof-check
hardening, reviews, and reachability theorem work are not yet committed.
The production `permute.c` and printer are unchanged by those experiments.

## Current bug categories

Count these as bugs or proof-chain gaps:

1. A valid-contract input causes a C memory error or undefined behavior.
2. C, Clight, and the Rocq model disagree on an observable result.
3. The C and actual solc oracle disagree on their stated common domain.
4. A valid input does not terminate.
5. Status, trace, blocked position, excess depth, or partial data is wrong.
6. The C printer changes the proved Clight behavior.
7. A behavior-changing Clight mutation within the theorem domain passes the
   complete proof pipeline.
8. A verifier reports success after dropping feasible paths, omitting an
   observation, using stale objects/results, admitting a claim, or weakening
   its premises or conclusion.
9. A required behavior is absent from the specification or theorem.

Equivalent changes should pass semantic checks. Raw source regeneration
can reject an equivalent byte change; that is a provenance check, not a
semantic counterexample. Invalid pointer/object inputs are outside the
current memory contract. Malformed-permutation rejection has tests but
does not yet have a universal theorem.

## Confirmed findings

See [FINDINGS.md](FINDINGS.md) for details and witness paths.

- **KLEE false equivalence pass:** inserting a conditional `exit(0)` in the
  actual C++ body let feasible paths skip all final comparisons. The old
  runner still reported success. A per-path completion marker now rejects
  those paths. The agent has tested the fix and is repeating final campaigns.
- **SAW false equivalence pass:** a conditional early exit gave a partial
  symbolic result and a printed proof success. The runner now rejects
  partial symbolic execution. Controls for both C and C++ are tested.
- **SAW stale result report:** a failed build could leave an older successful
  result file. The runner now clears results before building; its regression
  test passed according to the agent.
- **Proof-check gap:** `coqchk` accepts an admitted theorem or an explicit
  axiom. The existing script printed assumptions but did not reject new
  ones. An assumption allowlist and independent public theorem type check
  are being added. Their integrated baseline passes, but the isolated
  guard-test driver currently mixes warnings into the assumptions report
  and needs correction before that test can be called complete.
- **Coverage provenance gap:** source coverage can be reported from an old
  binary alongside changed source. Current archived hashes match, but the
  coverage script needs a source/binary manifest check before future reports.
- **Accepted-printer-subset gap:** an isolated normal-ABI Clight function
  that copies an uninitialized temporary and returns zero has a checked
  Clight call theorem. The unchanged printer emits an uninitialized C local
  read. The reproduction is confirmed; current Permute appears to initialize
  its own temporaries. A separate definite-assignment obligation is needed.

No concrete memory error or wrong result in the unchanged production C
has been found as of this snapshot. This is not an absence-of-bugs claim.

## Established Rocq/Clight result

`spikes/clight-permute/ClightCorrect.v` proves the actual complete Clight
call against `SolcModel.solc_permute`, including duplicate normalization
and suppression of swaps between equal values.

Domain: valid permutations, lengths 1 through 1024, uint32 values, six
separate live writable unsigned array objects, pointers to their first
elements, and stated capacities. Only data and permutation are initialized
inputs; work arrays and unwritten trace storage can be uninitialized.

The theorem proves defined execution, the exact model result, final or
partial arrays, trace/output fields, and status zero or one. It does not
assume that the call executes successfully. Empty and oversized calls have
separate theorems. Malformed permutation rejection is tested only.

The original integrated check passed `coqchk` on 62 modules. Evidence is
committed under `spikes/clight-permute/proof-results`. The model-to-Lean
relation is not machine checked; the original Lean model lacks the solc
duplicate rules. GCC/Clang, extraction, the printer, and C object/ABI
conditions remain part of the trust boundary.

The new `Reachability.v` proves, for arbitrary nonempty model sizes:

```text
success iff every initially incorrect value-position is at depth <= 16
blocked iff some initially incorrect value-position is at depth > 16
```

Here `target[j] = initial_data[inverse_permutation(j)]`. This is about
values, not `permutation[j] != j`, which is wrong for duplicates.
The scratch version compiled and both iff theorems were closed under the
global context. The promoted module adds a valid-trace corollary and needs
the full integration check. `ClightReachability.v` is written to connect
status zero/one to this predicate under the existing full-call premises.
Its first compile command failed before compilation because the Nix shell
path was relative to the wrong directory. Do not claim that corollary is
checked yet. See [status/root.md](status/root.md).

## Fuzzing and memory tools

The actual oracle uses solc revision
`cd1b0a209b17d3f6dd124bd89e1b9bcdff79b912`. It hash-checks full upstream
files and copies the reached bodies without changes. It tests internal
Permute with unsigned value IDs, not the full compiler.

| Check | Result |
| --- | --- |
| GCC/Clang matrix | Six configurations; each passed 4,435 exhaustive and 20,000 fixed-seed random cases, plus boundaries/rejections |
| libFuzzer + ASan/UBSan | 381,174 executions; no mismatch or sanitizer finding |
| AFL++ + ASan/UBSan | 228,026 executions; no saved crashes/hangs/timeouts |
| Fil-C 0.686 | 4,435 exhaustive, boundaries/rejections, 100,000 random, 802 unique saved inputs; no target error |
| MSan with instrumented C++ libraries and libFuzzer | All 482 libFuzzer files and 364 AFL files replayed; 73,316 further executions; no target report |
| Source mutation/metamorphic matrix | All 14 behavior changes detected; baseline and two equivalent changes pass |
| Rocq AST/model mutations | All 32 changed variants compile, then fail dependent proofs; both equivalent controls pass |

Both original guided corpora cover 72 reachable outcomes. Raw LLVM totals
remain C **46/49**, C++ **26/27**, combined **72/76 (94.74%)**. Three C error
outcomes and one C++ assertion failure are unreachable under the contracts.
The user accepted those four exclusions from the stopping criterion.
The supplemental export retains eight impossible constant-loop alternatives
and gives 72/84. Never call the raw result 100%.

Fil-C did not detect a one-element overrun inside allocation rounding in
its separate control; it detected a larger overrun. This limit is recorded.
LeakSanitizer could not start in the container and was disabled. ASan and
UBSan remained active. MSan had two final-run pre-main mapping failures;
only their exact signature was retried. Its deliberate uninitialized-read
control reported a heap origin, and the initialized control passed.

## Symbolic and source-C proof work

- [SAW status](status/saw.md): SAW 1.5, supported LLVM 20, explicit solver
  dependencies. Both size-two permutations are proved for arbitrary uint32
  values. Size-three work is incomplete. Twelve faulty source variants
  produced solver counterexamples; two equivalent changes were proved.
- [KLEE status](status/klee.md): pinned source build with LLVM 19 and Z3,
  active UB checks and no unsupported external calls. Old size-one through
  five runs need final completion-marker evidence. Corrected reruns and
  large restricted profiles are active. Restricted size-1024 profiles are
  not a proof for every size-1024 input.
- [Frama-C status](status/frama-c.md): direct source-C WP work with an ACSL
  reachability/trace contract. The annotation step preserves all C tokens.
  Recent memory pass: 572/597 goals; full pass: 604/774 goals. Further runs
  use Z3 and CVC5. **There is no complete Frama-C proof yet.**

Alive2 was tried with the actual oracle. Recursive range-v3 calls and loop
expansion prevented a justified comparison. That lane moved to KLEE. No
Alive2 equivalence proof is claimed.

Full C/C++ equivalence for every permutation through size 1024 is not
established. That remains a goal; enumeration alone will not scale.

## Stopped agent assignments

The agents had these assignments; all child agents are now idle:

- Root: orchestration, commits, proof guards, AST/model mutation checks,
  reachability theorem, evidence integration, and coverage provenance fix.
- `c_memory_review`: SAW, solver/runtime assumptions, Rocq specification
  review, and the possible uninitialized-temporary printer gap.
- `lgpl_build`: KLEE, large symbolic profiles, completion checks, source
  mutation proofs, and printer/tool review.
- `solc_fuzz`: Frama-C/ACSL, source memory review, and completed MSan and
  metamorphic/source-mutation work.

The three review reports are `review-spec.md`, `review-translation.md`, and
`review-memory.md` in this directory. They are working documents.

## Next actions for the continuing agent

1. Save this handoff and each agent's detailed status.
2. Finish the isolated guard-control rerun; its output capture is corrected.
   Test unsafe Rocq typing flags as separate negative controls.
3. Compile and check the promoted reachability modules; update the public
   type fixture and required assumption list as appropriate.
4. Add source/binary provenance checks to coverage reporting with negative
   tests for stale sources and binaries.
5. Preserve and review the SAW/KLEE early-exit counterexamples and fixes.
   Finish marked campaigns; do not reuse old success reports as final proof.
6. Continue Frama-C goals without hidden assumptions or skipped categories.
7. Preserve and address the confirmed accepted-printer-subset uninitialized
   temporary gap. Current Permute appears to initialize all temporaries, so
   distinguish the translation-subset gap from an actual Permute witness.
8. Add paired model/implementation mutations, deeper boundary combinations,
   compiler/LTO checks, and independent reachability property tests.
9. Archive MSan, source/proof mutation, symbolic-tool, and review evidence;
   commit it in separate reviewable chunks. Exclude all binaries and caches,
   including the newly created `.frama-c/` cache directory.
10. Follow the new user instruction on when to resume and for how long.
    Keep concrete findings separate from hypotheses, unsupported cases,
    and results outside the contract.

The user reported repeated platform cybersecurity-classifier interruptions.
This is authorized local defensive validation. One earlier subagent turn
was blocked; the task resumed and completed MSan. No platform classifier
can be changed by the repository code or agent. Preserve exact blocked-step
information if it recurs; do not treat a blocked step as a completed check.
