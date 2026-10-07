# KLEE and translation-review status

## Current pause: 2026-10-07

Work is paused at the user's request; no KLEE process remains active.
The [longer rejection campaign](../../../spikes/clight-permute/tests/results/extended-2026-10-06/rejected-large-extended/README.md)
is incomplete. Length 32 times out with 27 completed and 32 partial paths.
Length 64 is interrupted for the pause with 4 completed and 43 partial
paths and one solver error. The runner returns 1. No success is claimed
for either case.

## Continued checks

The [extended archive](../../../spikes/clight-permute/tests/results/extended-2026-10-06/README.md)
records the later checks and two confirmed gate defects, F8 and F9.
Both runners now reject inhibited forks, abnormal termination, missing
statistics, and KLEE control symbols in the compiled program modules.
The four fork-loss controls, eight symbol-boundary tests, and nine C API
rejection tests pass. The saved F9 source is rejected before KLEE starts.

Both new policies also pass on all 167 retained comparison cases and
71,587 marked paths. This includes the full lengths-one-through-five
domain, one length-six permutation, and thirteen restricted large
profiles. It does not establish all length-six cases.

The new symbolic rejection checks complete at lengths 1 through 6 and 8,
and for empty/oversized calls. A longer run also completes lengths 16,
17, and 18 with 99 marked paths in total. Lengths 32 and 64 time out
in the earlier short run with partial paths and no error witness.
Those two sizes remain incomplete.

## Resumed verification

The corrected run now covers all valid permutations at lengths one through
five, with unrestricted symbolic unsigned 32-bit values, including duplicates.
All 153 cases and 66,805 marked paths pass. No partial paths or errors remain
in this domain. Length five contributes 120 cases and 64,920 marked paths.

The audit combines only lengths one through four from
`build/equiv-alive2/klee-complete-checked/manifest.json` with the new
`build/equiv-alive2/klee-resumed-n5/manifest.json`. It checks the exact
permutation sets, current source hashes, linked-bitcode hashes, logs, error
files, path counts, and every completion witness. The driver/parser tests
also pass: 16 tests.

See the [archived audit and results](../../../spikes/clight-permute/tests/results/resumed-2026-10-06/README.md).
This is a finite-domain C/C++ check under KLEE's LLVM and successful-allocation
models. It does not close the Lean relation or printer proof gap. The larger
profiles below remain restricted families.

The resumed campaign is complete. The earlier stopped snapshot below is
retained as history; its length-five completion status no longer applies.

## Earlier stopped snapshot

Final snapshot: **2026-10-06 22:12:20 UTC**. Owner: `/root/lgpl_build`.
**Stopped at the user's request.** That request overrides the earlier
deadline of 2026-10-07 09:00 UTC (11:00 CEST). All active jobs owned by this
task were stopped. Logs and artifacts were retained. No further test,
proof, fix, or review will start in this agent.

Repository: `/home/me/.local/state/subagent/2e500090cbba/jpkjfmrfie/repo`.
All artifact paths below are relative to this repository.

## Results and scope

The runner compiles the actual generated C, the pinned solc Permute body,
and its reached vector/range-v3 code. It compares status, all final or
partial data, trace count, the complete written trace prefix, blocked
offset, and excess depth. It does not compare scratch outputs, trace
suffixes, or the final `Emission::m_mapping` object.

The corrected complete-domain run has finished all permutations at
lengths 1 through 4. Every input element is an unrestricted symbolic
32-bit unsigned value; duplicate values are included.

| Length | Permutations | Paths per permutation | Result |
| --- | ---: | ---: | --- |
| 1 | 1 | 1 | Passed with completion markers |
| 2 | 2 | 3 | Passed with completion markers |
| 3 | 6 | 13 | Passed with completion markers |
| 4 | 24 | 75 | Passed with completion markers |
| 5 | 36 of 120 finished in corrected run | 541 | Stopped; no complete-domain claim yet |

At the final snapshot, the corrected run has **69 of 153 cases** and **21,361
completed paths**, with zero errors and zero partial paths in finished
cases. The older run, without the completion guard, finished **153 of 153
cases** and **66,805 completed paths**. It remains useful raw evidence,
but the corrected run is the intended final evidence. A completed full
run through length five must have **153 cases and 66,805 paths**.

The corrected large-profile campaign finished **13 of 13 profiles**,
with **99 marked paths** in total:

- Lengths 17, 18, and 19: exchange destinations 0 and 1; values are
  `[A,B,C,...,C]`. Each passed 13 paths. This reaches success, immediate
  blocking, and blocking after a completed swap.
- Lengths 18 and 1024: exchange the first and last destinations; values
  are copies of A followed by B. Each passed 3 paths.
- Lengths 255, 256, 257, 512, and 1024: reverse destinations; values
  alternate A and B. Each passed 3 paths.
- Lengths 33, 257, and 1024: rotate destinations by one; values repeat A,B,C.
  Each passed 13 paths.

Each symbol is an unrestricted unsigned value, and different symbols
may be equal. These are explicit restricted families. They do not prove
all values or permutations at these lengths.

Both corrected mutation campaigns finished:

- **12 local controls passed**: 10 faulty changes rejected, 2 equivalent
  changes accepted. This includes pointer-error, signed-overflow, data,
  status, trace, and early-exit controls.
- **16 shared matrix controls passed**: 14 faulty changes rejected with
  assertion witnesses, 2 equivalent changes accepted. The domains include
  length-18 blocked results and the length-1024 size boundary.

The full C/C++ equivalence claim through length 1024, or for arbitrary
lengths, remains unproved. No wrong result or memory access has been found
in the unchanged generated C under its stated call contract.

## Actual defects found

### False equivalence after early process exit

An actual solc-body copy with this statement passed the first KLEE gate:

```cpp
if (m_data[0] == 0U) std::exit(0);
```

At length three, permutation `[1,0,2]`, the old gate reported **17
completed paths, zero partial paths, no errors, and pass=true**. Four paths
exited before the result comparisons. Function coverage did not detect
this. Concrete generated witnesses include:

```text
[0, 0, 0]
[0, 65280, 65280]
[0, 255, 0]
[0, 255, 4294967295]
```

The corrected harness calls the comparison function and then creates
a one-byte symbolic object named `checks_completed`. Every terminal
KTest must contain the expected input object followed by this marker.
The KTest count must equal the completed-path count. The same mutant is
now rejected for **four missing markers**. The unchanged case passes
with **13 marked paths**. Seven parser/completion tests pass.

Evidence under `spikes/clight-permute/build/equiv-alive2/`:

- `klee-exit-probe.inc`: the actual source edit.
- `klee-exit-probe/`: the false pass, logs, bitcode, and witnesses.
- `klee-exit-probe-fixed/`: the same source rejected by the new gate.
- `klee-completion-positive/`: unchanged positive control.
- `klee-mutations-checked/cpp-early-exit/`: persistent regression result.

This is a KLEE harness defect. It is not a production C counterexample.
The same probe exposed a SAW false pass. The SAW owner reproduced and
fixed its acceptance of a partial symbolic result; see that agent's
status and `tests/equiv-saw/README.md`.

### Coverage parser defect

The first KLEE coverage parser counted Callgrind call-summary rows as
individual instructions. This produced counts larger than denominators.
It did not affect semantic assertions or path/error counts. The fixed
parser skips rows after `calls=`, checks the counter layout, and requires
boolean instruction-coverage values. Four tests pass.

The old `klee-complete` process loaded the old parser. It finished before
the stop request. Its manifest counters have now been repaired from raw
`run.istats` with this command:

```sh
python3 spikes/clight-permute/tests/equiv-alive2/klee_coverage.py \
  spikes/clight-permute/build/equiv-alive2/klee-complete/manifest.json
```

The older `klee-mutations-final/*/manifest.json` files were also repaired.
Raw stdout logs remain unchanged. Do not rewrite them to conceal the
original reporting error. The
current `*-checked` runs use the fixed parser.

### Large-case file names

The initial runner named a directory with the full permutation. Large
cases exceeded file-name limits. The runner now uses a SHA-256 suffix
when the name is long and retains the full permutation in the manifest.
Five domain/name tests pass.

## Printer initialization finding

Update **2026-10-06 22:07:24 UTC**: the isolated case is confirmed.
`/root/c_memory_review` checked `uninitialized_copy_returns_zero` in Rocq
for a function with the normal ABI and body `v8 = v9; return 0U;`, for all
arguments. The unchanged printer accepts it. GCC 15.3 reports that v9 is
used uninitialized. Reproduction files are under
`spikes/clight-permute/build/equiv-saw/undef-probe/`.

A copied actual Permute C source with a prefixed `v8 = v8;` also passes
the corrected KLEE comparison at length three, permutation `[1,0,2]`:
13 marked paths, no errors. This confirms that KLEE's selected safety
checks do not reject an unused uninitialized scalar read. Evidence:
`build/equiv-alive2/klee-uninitialized-copy.c` and
`build/equiv-alive2/klee-uninitialized-copy/`.

The memory-review agent was composing the complete Permute Clight call
specification with the same self-copy prefix. The Frama-C agent confirmed
that its RTE pass retains the C self-copy and creates an initialization
obligation. WP reduces that obligation to **`Prove: false`** under the
normal valid-permutation contract. Evidence:
`build/frama-c/undef-prefix-1/rte.c:56` and
`build/frama-c/undef-prefix-1/initialization-wp.log`. The first property
filter selected zero goals; that unsuccessful attempt is retained in
`wp.log` and is not the safety witness.

Clight can copy `Vundef` from an uninitialized temporary into another
temporary and continue. An unused read of an uninitialized automatic C
scalar can still have undefined behavior. The printer checks types and
syntax; it does not check definite assignment. Its header explicitly
delegates initialization to proof obligations.

Thus an `eval_funcall` correctness theorem alone does not establish
definite assignment for every accepted AST. The current Permute source
appears to initialize its used temporaries. This is a limit of the general
printer-subset claim, not yet a production counterexample.

`/root/c_memory_review` owns the isolated Clight/printer probe and its
preserved reproduction. No production printer or Rocq file was changed by this
agent. A separate interface limit is that the oracle discards final
`Emission::m_mapping`; full Emission-state equivalence would need a relation
for its equal-value mapping exchanges.

## Stopped and finished jobs

There are **no task-owned KLEE/compiler jobs still running**. The corrected
full-domain run and its current compiler/KLEE children received SIGTERM.
Its session returned exit status 143. The other campaigns had finished.

Use this shell prefix for all commands:

```sh
nix develop --impure --expr \
  'import ./spikes/clight-permute/tests/equiv-alive2/klee-shell.nix' --command
```

| Job | Session | Main process PID | Status at snapshot |
| --- | ---: | ---: | --- |
| Old complete n1–5 run | 55474 | 32184 | Finished: 153/153 cases |
| Corrected complete n1–5 run | 43858 | 53894 | Stopped: 69/153 cases |
| Corrected large profiles | 8055 | 53893 | Finished: 13/13 profiles |

The final stopped process set was: shell 53892, runner 53894, KLEE workers
62967/62995/63006, and compiler processes 63057/63059. A post-stop process
check found no active runner/profile/coverage process owned by this task.
The former length-1024 profile runner 59118 and KLEE child 59208 had
already finished. Coverage-repair session 72001 also finished with status 0.

The corrected campaign has four unrecorded case directories. They were
in progress when stopped and must not be counted as completed evidence:

```text
n5-1-3-0-2-4
n5-1-3-0-4-2
n5-1-3-2-0-4
n5-1-3-2-4-0
```

Commands after the shell prefix:

```sh
python3 spikes/clight-permute/tests/equiv-alive2/run-klee.py \
  --sizes 1,2,3,4,5 --jobs 4 --max-time 240s \
  --output spikes/clight-permute/build/equiv-alive2/klee-complete

python3 spikes/clight-permute/tests/equiv-alive2/run-klee.py \
  --sizes 1,2,3,4,5 --jobs 4 --max-time 240s \
  --output spikes/clight-permute/build/equiv-alive2/klee-complete-checked

python3 spikes/clight-permute/tests/equiv-alive2/profile-campaign.py \
  --output spikes/clight-permute/build/equiv-alive2/klee-profiles-checked
```

Each command's stdout/stderr is in the sibling file named
`<output-directory>-command.log`. Each case retains build logs, linked
bitcode, KLEE logs, statistics, instruction records, and KTests. Manifests
are updated after each completed case. New runs require new output paths.

Finished control sessions: 40073 (`klee-mutations-checked`) and 51128
(`klee-shared-matrix-checked`). Early `*-marked` starts failed before any
proof because the Z3 CLI was absent from the shell. The shell now includes
the same pinned Z3 package explicitly; version 4.16.0 was checked. These
failed logs remain available. They are not proof results.

## Tool and license assumptions

- KLEE commit `9a36a6782b814fe1fa37439652b875114faa0e20`, LLVM/Clang 19.1.7,
  Z3 4.16.0, and pinned repository Nixpkgs; `allowUnfree = false`.
- KLEE, KDAlloc, and its freestanding runtime: NCSA. LLVM and the selected
  UBSan runtime: Apache-2.0 with LLVM exception. Z3: MIT. No noncommercial
  tool or solver is selected. Further component terms are in the README.
- KLEE's ordinary new/delete model assumes successful allocations and
  eight-byte allocation alignment. Allocation failure and C++ exceptions
  remain outside the checked domain. C++ is compiled with exceptions off.
- Large cases link the unchanged GCC `new_opnt.cc` body, GPL-3.0-or-later
  with GCC Runtime Library Exception 3.1. Revision:
  `4db0e8df15bef836558857c291c323add11d035c`; SHA-256:
  `4c2466f46ae448de78523a245600acbbbca8680409e7f477f1939de28bac48c0`.
  Its ordinary-new call uses KLEE's allocation model. No replacement sort
  or Permute algorithm is used.
- All source compilation uses O0 with signed-overflow, shift, integer
  division, and array-bound instrumentation. KLEE keeps memory checking,
  assertions, `--external-calls=none`, and its UBSan runtime enabled.
- KLEE is not a complete uninitialized-read detector. LLVM/C differences,
  object lifetime/effective type, the printer, and GCC/Clang remain relevant
  trust or call-contract conditions.
- No loop-unroll cutoff is used. Partial paths, timeouts, error files,
  changed source hashes, external calls, or missing completion markers
  fail the current runner.

Alive2 remains inconclusive. It left recursive range-v3 calls outside its
intraprocedural proof. No Alive2 proof is claimed. Fil-C testing was
completed earlier and archived by the parent; its allocator-rounding limit
remains documented in `tests/FILC_RESULTS.md`.

## Files and changes

This agent owns uncommitted files in
`spikes/clight-permute/tests/equiv-alive2/`, plus
`docs/verified-permute/review-translation.md` and this status file. It made
no commits in this phase and did not change production Rocq, printer, or
shared build files.

The test directory contains the pinned tool shells, actual-source
wrappers, full-symbolic and grouped-value drivers, runner, completion
wrapper/parser, coverage parser, upstream allocation fetcher, mutation
campaigns, large-profile campaign, README, and their tests. Raw results
are under ignored `spikes/clight-permute/build/equiv-alive2/`.

## Exact resume command and remaining work

Do not resume without the user's later instruction. To restart the full
marked campaign, use a **new** output directory. This command does not
overwrite or infer completion from the stopped run:

```sh
nix develop --impure --expr \
  'import ./spikes/clight-permute/tests/equiv-alive2/klee-shell.nix' \
  --command python3 spikes/clight-permute/tests/equiv-alive2/run-klee.py \
  --sizes 1,2,3,4,5 --jobs 4 --max-time 240s \
  --output spikes/clight-permute/build/equiv-alive2/klee-resumed-full \
  > spikes/clight-permute/build/equiv-alive2/klee-resumed-full-command.log 2>&1
```

For a resume that reuses completed cases, first check every source hash
in `klee-complete-checked/manifest.json` against the current file. Then
run the **84 missing length-five permutations**, each with a fresh
output directory, and join only successful marked results. The recorded
length-five prefix ends at `[1,2,4,3,0]`. The four unrecorded directories
above are among those missing cases. If any source or proof harness has
changed, use the fresh full run instead.

1. Resume or restart the corrected full n1–5 run after authorization.
2. Require all 153 cases and 66,805 marked paths for the full small-domain
   result. Do not infer completion from the old campaign.
3. Old coverage manifests have been repaired. Keep raw logs unchanged.
4. Update the README with final counts and retain a concise evidence set
   for parent archival.
5. Review the confirmed Vundef/printer probe with the parent. Keep the
   current-code claim separate from the general accepted-subset claim.
6. Follow the user's next scope and deadline. Small-domain proofs and
   selected large profiles do not close the all-size C/C++ proof gap.
