<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Permute working status

## Current pause: 2026-10-07

The user later requested removal of the bulk result files. The current tree
keeps summaries; the removed outputs remain in commit `a9b8307`.
See the [result storage note](../../spikes/clight-permute/tests/results/README.md).
Historical references below describe the files saved at the time of each run.

The user asked to wrap up and commit the resumed Frama-C work. All runs from
this task have stopped. No other verification campaign was restarted.

All six components have complete individual reports: safety **641/641**,
termination **337/337**, target **313/313**, trace **393/393**, status
**495/495**, and success **570/570**. The saved-input audit checks every
reported obligation, identical production C tokens, the same input domain,
and full contract coverage. The total is **2,749 obligations**, with overlap
between components. All **52 tool tests** and seven control suites pass.

The fresh `full-final-20261007` run stopped during trace and has no completed
root summary. The status source control suite reports failure: its wrong
target mutation fails `collect_value` and `injective_selected`, while the
test expects `collected_changed`. This expectation remains to be corrected.
The success source control suite stopped after its 570/570 baseline; the
parentheses run and two faulty variants remain incomplete or unrun.

See [the Frama-C status](status/frama-c.md) and
[the saved result summary](../../spikes/clight-permute/tests/results/frama-c-2026-10-07/README.md).
Production C, Rocq, the AST, and the printer are unchanged. No new bug was
found in unchanged production C. F10 records a control-scope error.
The printer and Lean–Rocq proof gaps remain open. Resume only on user request.

## Historical pause: 2026-10-07

The user asked to wrap up Frama-C and pause to save tokens. This instruction
overrides the earlier 11:00 CEST deadline. No verification process remains
active. The work is paused, not complete. Resume only on user instruction.

- Frama-C memory pass: **641/642 explicit goals valid**. Main-loop
  termination remains open. The runner reports failure.
- Initialization controls: baseline and parentheses pass all nine selected
  goals; removing the target store leaves an invariant unproved. All 25
  Frama-C tool tests pass.
- The final copied-source rank experiment proves the all-integer bounds
  lemma. Frame and update lemmas remain unproved. The
  [rank archive](../../spikes/clight-permute/tests/results/extended-2026-10-06/frama-rank-experiments/README.md)
  records the results and next proof step. No production lemma changed.
- The longer KLEE rejection campaign has stopped. Length 32 timed out;
  length 64 was interrupted for the pause. Both are incomplete. The
  [archive](../../spikes/clight-permute/tests/results/extended-2026-10-06/rejected-large-extended/README.md)
  retains partial paths and the length-64 solver error.

The Clight-to-Rocq theorem remains the main proof. The C translation link,
full source-C contract, and concrete divergent-execution connection for
the assignment checker remain open. No new unchanged-production-C bug was
found. At the pause, no commits had been made; the user then requested a
commit of this work. All later references below to active or next work
describe the state before this pause.

## Continued testing to 11:00 CEST

At 2026-10-06 22:53 UTC, the active user goal again requests testing until
11:00 CEST on 2026-10-07 (09:00 UTC), with findings recorded. This instruction
takes precedence over the earlier deadline and stop notes below.

The previous turn completed the corrected KLEE lengths-one-through-five
audit and archived its evidence. This was progress, not a pending run.
The length-six symbolic comparison and symbolic C API rejection run have
finished. The main theorem assumes a valid permutation; the rejection
behavior needs separate checks.

The new rejection runner passed nine tests against production C and
changed copies. All malformed permutations and unrestricted unsigned
32-bit data pass at lengths 1, 2, 3, 4, 5, 6, and 8. The separate symbolic
empty/oversized check also passes. Lengths 16, 17, 18, 32, and 64 reached
the 120-second limit with partial paths and no error witnesses. That
campaign has finished and correctly returns nonzero. No completion claim
is made for these larger sizes.

The length-six pilot for permutation `[1,0,2,3,4,5]` reached its 600-second
limit: 4,121 completed paths and 522 partial paths, with no errors. It was
correctly rejected as incomplete. A separate run with a 1,800-second limit
completed all 4,683 marked paths in about 614 seconds, without errors or
inhibited forks. This is one selected permutation, not a full length-six
campaign.

Current evidence paths:

- `spikes/clight-permute/build/equiv-alive2/rejected-extended/`
- `spikes/clight-permute/build/equiv-alive2/klee-extended-n6-pilot/`
- `spikes/clight-permute/build/equiv-alive2/klee-extended-n6-swap/`
- `/tmp/permute-rejected-controls.log`

See the [rejection check contract](../../spikes/clight-permute/tests/equiv-alive2/rejected-inputs.md).

The inhibited-fork hypothesis is confirmed as [F8](FINDINGS.md): an explicit
fork-limit control causes the current runner to accept a faulty C copy.
One path completes with its marker while a feasible failing branch is not
explored. The normal unrestricted run finds the assertion failure. Both
runners now reject inhibited forks and abnormal state termination. Nine
policy tests and four actual KLEE controls pass.

[F9](FINDINGS.md) records a second domain gap: a `klee_assume` call inside
the tested C removes input 42 while the old gate reports success. Both
runners now reject KLEE control symbols in compiled program modules before
linking the trusted harness. Eight boundary tests pass, including real
compiler/runner controls for declared and defined KLEE functions. The nine
rejection tests and four fork-loss controls still pass.

All 167 retained cases (71,587 marked paths) pass both new audits. This
includes the complete lengths-one-through-five domain, the selected
length-six permutation, and thirteen restricted large profiles. A fresh
lengths-one-through-three run with the fork check passed nine cases and
85 paths. The old result files remain unchanged.

Evidence is in
[the extended results archive](../../spikes/clight-permute/tests/results/extended-2026-10-06/README.md).
Direct execution comparisons between Rocq/Clight and generated C now pass
1,110 selected cases on GCC and Clang at `-O0`, `-O2`, and `-O3`. These
include 784 successful results, 68 blocked results, and 258 rejected
inputs. The small campaign has 925 cases; the boundary campaign has 185.
The extracted interpreter uses the actual AST and CompCert memory, with
undefined initial scratch memory and local temporaries. Its successful
body return is connected to a full call by a checked wrapper theorem.
The kernel policy reports 12 allowed upstream axioms and no unsafe settings.

The new comparison tool passes eight tests, including ten shared C
mutation controls, process exit, timeout, fuel exhaustion, and malformed
records. During development, the controls exposed a missing equal-value
swap case and a record-count check omitted from the comparison helper.
Both were corrected before the campaigns. They do not change prior
production evidence. See the [test contract](../../spikes/clight-permute/tests/rocq-eval/README.md).

The further KLEE rejection run at lengths 16, 17, and 18 completed with
31, 33, and 35 marked paths. All 99 paths pass with no errors, partial
paths, or lost forks. Each case had a 1,800-second limit. Its directory is
`spikes/clight-permute/build/equiv-alive2/rejected-depth-extended/`.
The [run summary](../../spikes/clight-permute/tests/results/extended-2026-10-06/README.md)
includes the bitcode, statistics, source snapshots, and all witnesses.
Lengths 32 and 64 remain incomplete from the earlier short run.
The generated-program campaign also completed: 128 distinct C sources,
50 input cases per program, and all six GCC/Clang builds pass. This is
6,400 interpreter cases and 38,400 native comparisons. The tests cover
unsigned wraparound, array index arithmetic, branches, nested bounded
loops, inner breaks, early returns, and renamed identifiers. Three faulty
printer controls are detected; the baseline and a parentheses control
pass. A hand-calculated arithmetic record also agrees with the interpreter
and all six C builds. The generic extraction prints the production
`permute.c` byte for byte. These are finite tests, not a printer proof.
See the [generated-program archive](../../spikes/clight-permute/tests/results/extended-2026-10-06/printer-eval/README.md).

A longer KLEE rejection run at lengths 32 and 64 is active, with a
3,600-second limit per case, under
`spikes/clight-permute/build/equiv-alive2/rejected-large-extended/`.
Length 32 reached that limit with 27 completed and 32 partial paths, no
error witnesses, and no lost forks. Its result is incomplete. Length 64
is now running under the same process.
The sanitizer follow-up passes all 128 generated programs on the same
6,400 cases with Clang `-O1`, AddressSanitizer, and UBSan. Buffer-overflow
and invalid-shift controls produce the expected diagnostics and nonzero
exits. Leak detection is disabled after an environment failure: the
LeakSanitizer thread scan cannot run here. The tested functions use stack
objects only. See the [sanitizer archive](../../spikes/clight-permute/tests/results/extended-2026-10-06/printer-sanitizers/README.md).

A candidate Rocq check for assignment before temporary reads now accepts
the actual Permute AST and rejects the known undefined self-copy prefix.
Twenty-one examples and nine baseline/mutation controls have their
expected results. The kernel check passes. The expression-read lemma and
the computed Permute result are closed under the global context.
This candidate is supporting evidence; it is not a new production gate. See the
[assignment-check archive](../../spikes/clight-permute/tests/results/extended-2026-10-06/assignment-check/README.md).

The statement-level argument now passes a fresh kernel check. It covers
complete paths and finite prefixes in an explicit control model, including
branch joins, loop exits, nested breaks, and later iterations. Five path
witnesses include unsafe reads. All four public path theorems are closed
under the global context. See the
[path-proof archive](../../spikes/clight-permute/tests/results/extended-2026-10-06/assignment-path-proof/README.md).

A further proof connects every terminating Clight execution in the
supported statement form to an execution record. Records preserve actual
expression evaluations, branch decisions, intermediate environments,
memories, traces, and outcomes. They map to the control model, where the
checker proves safety. The actual Permute body has the required form and
the resulting theorem. Five independent execution type fixtures pass.
The fresh `coqchk` and kernel policy pass with 12 allowed upstream axioms
and no unsafe settings. These concrete theorems retain upstream CompCert
assumptions; unlike the path theorems, they are not closed under the
global context. See the
[execution-proof archive](../../spikes/clight-permute/tests/results/extended-2026-10-06/assignment-execution-proof/README.md).

Nineteen [proof controls](../../spikes/clight-permute/tests/results/extended-2026-10-06/assignment-proof-controls/README.md)
also have their expected results. Seven weakened checker copies compile
with all 21 example tests removed, then fail a named soundness statement.
Five changed execution-record definitions fail coverage, erasure, or path
proofs. The two baselines and two parentheses controls pass. Three real
compiler-error controls are excluded from proof-failure evidence.

The proved property is prior assignment of temporary names. Memory byte
initialization and C translation are separate. The abstract prefix proof
still needs a concrete small-step or divergence link. F7 remains open.
Next work is to challenge this new proof connection and examine the
remaining prefix and memory obligations. The active KLEE run remains
separate and must be polled through its current process.

The Frama-C follow-up now proves all nine selected fill-invariant and
target-initialization goals on production C. An equivalent parentheses
control passes. Removing the target store fails the fill invariant. The
strategy instantiates an existing premise and preserves all C tokens.
All 25 tool tests pass. The
[initialization archive](../../spikes/clight-permute/tests/results/extended-2026-10-06/frama-initialization/README.md)
retains these results. The full memory pass `memory-target-strategy` now
has 641/642 explicit goals valid. Only main-loop termination is pending.
The runner correctly returns nonzero. The
[full memory-pass archive](../../spikes/clight-permute/tests/results/extended-2026-10-06/frama-memory-strategy/README.md)
records the result. The count/rank lemmas also remain open. No source-C
proof completion is claimed.

## Resumed work: 2026-10-06

The user has resumed verification and clarified the main purpose: review
the C ↔ Lean proof-of-concept workflow, starting with the core Rocq
definitions and theorems. Additional tools and mutations supply independent
supporting evidence. A verified Lean ↔ Rocq bridge is future work, outside
the current scope. No token budget was set. The later active deadline is
recorded above.

Start at [README.md](README.md), then read [trust-boundary.md](trust-boundary.md).
The public theorem is now `PermuteCorrect.clight_refines_model`, with
`PermuteSpec` and `ModelSpec` as separate specification modules. The expanded
type remains checked independently. The refactored full proof build and
`coqchk` have passed; evidence is under
`spikes/clight-permute/proof-results/reviewed-2026-10-06/`.

Other completed resumed checks:

- The saved uninitialized-copy reproduction passed its proof and compiler
  checks. It still demonstrates the accepted-printer-subset gap.
- SAW's unchanged baseline, both early-exit controls, and stale-result
  control had their expected results in a fresh output directory.
- Coverage now requires matching source and binary manifests. Eleven
  tests pass, including rejection by the actual reporting script for stale
  source, stale binary, and invalidated build. A fresh replay gives 72/76
  LLVM outcomes and 72/84 exported outcomes.
- The new kernel-context policy checks full axiom names and unsafe typing
  settings. Its tests and the existing assumption tests pass. A shadowed
  short-name probe did not bypass the whole existing theorem check.
- The Frama-C run with the final solver setup completed with 635/642 valid
  goals, one unknown, and six timeouts. It is incomplete and does not
  supersede the earlier 642/644 memory result. Its 24 driver tests pass.
- All eight proof-policy controls had their expected results. Both selected
  behavior changes failed dependent proofs, and both equivalent source
  controls passed after the review refactor. Their sources and logs are
  archived with the reviewed proof evidence.

- The corrected KLEE length-five run completed all 120 permutations and
  64,920 marked paths. An audit combined these with the retained lengths
  one through four: 153 cases and 66,805 marked paths, with no partial paths
  or errors. The audit checked source and bitcode hashes and read each
  completion witness again. This covers unrestricted unsigned 32-bit
  values at lengths one through five under the recorded runtime model.

The resumed runs above have finished. Their
[supporting evidence index](../../spikes/clight-permute/tests/results/resumed-2026-10-06/README.md)
records results and limits. The open proof links remain open.
No sub-agents have been started in the resumed work.

## Earlier stopped handoff

The remainder of this file preserves the earlier handoff. The resumed
section above takes precedence over its stop instructions and old file map.

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
