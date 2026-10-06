# KLEE and translation-review status

Snapshot: **2026-10-06 22:04:43 UTC**. The active bug search ends at
**2026-10-07 09:00 UTC (11:00 CEST)**. Owner: `/root/lgpl_build`.
The work is active. No active job was stopped for this status report.

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
| 5 | 16 of 120 finished in corrected run | 541 | Running; no complete-domain claim yet |

At the snapshot, the corrected run has **49 of 153 cases** and **10,541
completed paths**, with zero errors and zero partial paths in finished
cases. The older run, without the completion guard, has **147 of 153
cases** and **63,559 completed paths**. It remains useful raw evidence,
but the corrected run is the intended final evidence. A completed full
run through length five must have **153 cases and 66,805 paths**.

The corrected large-profile campaign has passed **12 of 13 profiles**:

- Lengths 17, 18, and 19: exchange destinations 0 and 1; values are
  `[A,B,C,...,C]`. Each passed 13 paths. This reaches success, immediate
  blocking, and blocking after a completed swap.
- Lengths 18 and 1024: exchange the first and last destinations; values
  are copies of A followed by B. Each passed 3 paths.
- Lengths 255, 256, 257, 512, and 1024: reverse destinations; values
  alternate A and B. Each passed 3 paths.
- Lengths 33 and 257: rotate destinations by one; values repeat A,B,C.
  Each passed 13 paths.
- The length-1024 rotation with A,B,C is still running.

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

The old running `klee-complete` process loaded the old parser. After it
finishes, repair only its manifest counters from raw `run.istats`:

```sh
python3 spikes/clight-permute/tests/equiv-alive2/klee_coverage.py \
  spikes/clight-permute/build/equiv-alive2/klee-complete/manifest.json
```

Also repair the older `klee-mutations-final/*/manifest.json` files. Do not
rewrite old stdout logs to conceal the original reporting error. The
current `*-checked` runs use the fixed parser.

### Large-case file names

The initial runner named a directory with the full permutation. Large
cases exceeded file-name limits. The runner now uses a SHA-256 suffix
when the name is long and retains the full permutation in the manifest.
Five domain/name tests pass.

## Pending printer lead

Clight can copy `Vundef` from an uninitialized temporary into another
temporary and continue. An unused read of an uninitialized automatic C
scalar can still have undefined behavior. The printer checks types and
syntax; it does not check definite assignment. Its header explicitly
delegates initialization to proof obligations.

Thus an `eval_funcall` correctness theorem alone does not establish
definite assignment for every accepted AST. The current Permute source
appears to initialize its used temporaries. This is a limit of the general
printer-subset claim, not yet a production counterexample.

`/root/c_memory_review` owns the isolated Clight/printer probe and will
report the result. No production printer or Rocq file was changed by this
agent. A separate interface limit is that the oracle discards final
`Emission::m_mapping`; full Emission-state equivalence would need a relation
for its equal-value mapping exchanges.

## Active jobs

Use this shell prefix for all commands:

```sh
nix develop --impure --expr \
  'import ./spikes/clight-permute/tests/equiv-alive2/klee-shell.nix' --command
```

| Job | Session | Main process PID | Status at snapshot |
| --- | ---: | ---: | --- |
| Old complete n1–5 run | 55474 | 32184 | 147/153 cases |
| Corrected complete n1–5 run | 43858 | 53894 | 49/153 cases |
| Corrected large profiles | 8055 | 53893 | 12/13 profiles |

The active length-1024 profile runner PID is 59118; its current KLEE child
PID is 59208. Worker PIDs in the n1–5 runs change after each case.

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

## Next work

1. Finish the corrected full n1–5 run and the final length-1024 profile.
2. Require all 153 cases and 66,805 marked paths for the full small-domain
   result. Do not infer completion from the old campaign.
3. Repair old coverage manifests after their processes finish. Keep raw
   logs unchanged.
4. Update the README with final counts and retain a concise evidence set
   for parent archival.
5. Review the isolated Vundef/printer probe with the parent. Keep the
   current-code claim separate from the general accepted-subset claim.
6. Continue the bug search until the stated deadline. Small-domain proofs
   and selected large profiles do not close the all-size C/C++ proof gap.
