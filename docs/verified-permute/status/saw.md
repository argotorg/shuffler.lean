<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# SAW and specification review status

## Resumed checks

The user resumed verification. The isolated uninitialized-copy driver
`tests/equiv-saw/undef-copy/check.sh` completed successfully. The Clight
transfer proof passed, and GCC and Clang rejected the printed uninitialized
read as required by the control.

The completion campaign ran in a fresh `build/equiv-saw/completion-resumed/`
directory. The size-two swap baseline proved; early exit in either C or C++
was reported incomplete; the failed-build stale-result control passed.
All four controls had their expected results. Five classifier tests passed.
No additional full-domain equivalence claim follows from these controls.

The stopped handoff below is retained as history. See
[the current main status](../WORKING_STATUS.md) for the resumed scope.

Final stop snapshot: **2026-10-06 22:13:41 UTC**. Agent: `/root/c_memory_review`.

**The user requested a stop and handoff. All active task jobs are stopped.**
The earlier 2026-10-07 09:00 UTC deadline no longer authorizes more work.
The main body below preserves the 22:04:34 snapshot. The final handoff
section at the end overrides its active-job and pending-probe statements.

## Scope and file ownership

I own `spikes/clight-permute/tests/equiv-saw/` and its reports. I have not
changed production C, the printer, proof sources, or the shared shell.
Build output is under ignored `spikes/clight-permute/build/equiv-saw/`.
Do not commit. Do not use Alt-Ergo, non-commercial tools, lax memory
settings, assumed sorting contracts, replacement sorts, or lost paths.

Source files in the SAW directory:

- `shell.nix`, `fetch_runtime.py`, `build.sh`, `verify.py`, `miter.c`;
- `mutations.py`, `completion.py`, `test_driver.py`;
- `allocation_failure.cpp`, `allocation_failure.sh`;
- `README.md`, `LICENSES.md`, `hackage-licenses.json`,
  `submodule-licenses.json`.

Associated reports:

- `docs/verified-permute/equivalence-tools.md`: initial literature review,
  now linked to the actual tool trials;
- `docs/verified-permute/review-spec.md`: three-pass specification review,
  updated for the promoted reachability theorems.

All SAW source files are currently untracked. The literature report is
modified; the specification review and this status file are untracked.
Other agents own the remaining shared-workspace changes. `git diff --check`
passed before this status update.

## Tool and license selection

Use this environment from the repository root:

```sh
nix develop --impure --expr 'import ./spikes/clight-permute/tests/equiv-saw/shell.nix'
```

- SAW **1.5**, source `957290e76d916986902ef5bb6ae664090c8295eb`, BSD-3-Clause.
- Official **no-solvers** archive `saw-1.5-ubuntu-22.04-X64.tar.gz`.
  SHA-256 `ca8a2bc81caee606f03ec538b0f5cf299ea4571b65a9812553b15fb37d014826`.
- Clang/LLVM **20.1.8**, Apache-2.0 with LLVM exception.
- Z3 **4.16.0**, MIT; Yices **2.7.0**, GPL-3.0-or-later.
- GCC **15.3.0** allocation source at
  `4db0e8df15bef836558857c291c323add11d035c`, GPL-3.0-or-later with
  GCC Runtime Library Exception 3.1.
- range-v3 **0.12.0**, Boost Software License 1.0.
- solc oracle source `cd1b0a209b17d3f6dd124bd89e1b9bcdff79b912`, GPL3+.
- Nixpkgs `c7def046b9a883d46974757852106483d741586f`,
  `allowUnfree = false`.

The audit covered all 350 release freeze-file entries: 345 Hackage records
and five GHC distribution packages. It also checked 19 Git submodule
license notices, native LMDB and libBF notices, and the executable's dynamic
library list. No non-commercial term was found in the selected notices.
Details and exact primary URLs are in `LICENSES.md` and the two JSON files.
This is a declaration/source-notice audit, not a reproducible-build proof
of the upstream binary. No tool binary was added to tracked files.

SAW binary:
`/nix/store/1awvcmc77wmh3qfb4z8dr95n9xay622h-saw-tools-1.5/bin/saw`.
Python outside Nix:
`/nix/store/01gr3gdb268lr8zwppsaq9s49pizkwf4-system-path/bin/python3`.

## Proof scope and assumptions

The miter runs unchanged production `permute.c` and the actual pinned solc
body on equal input values in separate arrays. Each normal case fixes one
valid permutation and leaves every input word symbolic over all unsigned
32-bit values, including duplicates. It compares status, complete final or
partial data, all three output fields, trace length, and only the written
trace prefix. It checks the trace bound before reading that prefix.

Only data and permutation inputs are initialized. Scratch and output arrays
start uninitialized. There are no user algorithm overrides or loop bounds.
C is compiled at O1; C++ at O0 with `-Xclang -disable-O0-optnone`. Both
disable loop and SLP vectorization. The LLVM `lower-constant-intrinsics`
pass lowers `llvm.is.constant`, unsupported by SAW 1.5.

The bitcode links unchanged GCC `new_op.cc`, `new_opnt.cc`, `del_op.cc`, and
`del_ops.cc`. Crucible's built-in malloc still assumes successful fresh
allocation. The result excludes allocation failure, custom allocator or
new-handler effects, and allocation exceptions. Source-to-LLVM translation,
LLVM poison/freeze limitations, and built-in libc models remain trusted.
This is not a general ISO C/C++ UB-freedom theorem.

The default path solver is Z3; the final proof tactic is also Z3. SAW 1.5
still checks that Yices exists when path checking begins. A direct run with
Yices removed from PATH failed with that requirement. The README was
corrected after source and process inspection showed the default uses Z3.

## Completed positive evidence

The unchanged program has complete SAW proofs for these cases, with
arbitrary full-width values:

| Permutation | Longer-run time |
| --- | ---: |
| `[0]` | 1.318 s |
| `[0,1]` | 3.522 s |
| `[1,0]` | 5.877 s |
| `[0,1,2]` | 18.508 s |
| `[0,2,1]` | 202.395 s |

The first 180-second trial timed out on the other four length-three cases.
No counterexample to the unchanged algorithm has been found by this agent.
No claim covers all permutations through length 1024.

`build/equiv-saw/completion-audit.json` rechecks all five longer-run success
logs, plus both equivalent mutation logs, with the new totality rule.
All seven remain complete. This audit is needed because the active longer
run loaded `verify.py` before the totality fix.

## Counterexamples and proof-harness gaps

1. `mutations.py` rejected all **12 faulty variants** with explicit solver
   counterexamples: C status, data, trace value/count, blocked/excess fields,
   depth limit; C++ status, data, trace, blocked/excess fields. Both equivalent
   changes proved. Results: `build/equiv-saw/mutations/results.json`.
2. The separate output-increment control failed with input `[0,4294967295]`.
   Log: `build/equiv-saw/negative-control/n2-1_0/proof.log`.
3. **SAW accepted a partial execution.** Adding `exit(0)` when the first
   data word is zero still produced `Proof succeeded! equivalence`.
   SAW logs `Symbolic simulation completed with side conditions.` and
   checks only surviving return paths. This matches Crucible `PartialRes`
   handling in SAW's `getGlobalPair`. The runner now rejects this marker.
   `completion.py` tested the unchanged baseline, exit inserted into actual
   C, and exit inserted into the actual solc body. Baseline proves; both
   variants are incomplete/partial_execution. Results:
   `build/equiv-saw/completion/results.json`.
4. **Old results survived a failed build.** A missing C source left a prior
   success result available. The runner now clears results before building.
   The same integration regression passes. Five classifier unit tests pass.
5. **Allocation-failure boundary confirmed.** `allocation_failure.sh` runs
   unchanged C, then forces C++ operator new to throw. It prints:
   `C returns success; the unchanged C++ oracle throws bad_alloc.`
   This is outside the stated successful-allocation assumption.

The partial-result guard is tied to the pinned SAW version and normal
information output. Review it when changing SAW. Proof success alone is
not sufficient.

## Active jobs at this timestamp

| Session | Process | Work | Logs/results |
| --- | --- | --- | --- |
| **97189** | Python 44842; SAW 48363 | All permutations n1..3, 2400 s per case; currently `[1,0,2]` | `build/equiv-saw/full-n3/` |
| **49605** | Python 53154; SAW 53252 | n18, swap0/17, source `[A]*17+[B]`, unrestricted 32-bit A/B, 1800 s limit | `build/equiv-saw/boundary-n18/` |
| **53856** | Python 58575; SAW 58623 | `[1,0,2]` with both C and miter at O0, 600 s limit | `build/equiv-saw/c-o0-trial/` |

The main command is:

```sh
python3 spikes/clight-permute/tests/equiv-saw/verify.py \
  --max-n 3 --timeout 2400 \
  --out spikes/clight-permute/build/equiv-saw/full-n3
```

The other jobs were started by short Python orchestration commands. Their
exact compiler commands are in `build.log`; generated `.saw` files are the
complete proof scripts. The n18 proof script is `family.saw` under the
permutation directory. It uses two fresh words, repeats the first word 17
times, and adds no order or inequality precondition.

Use `write_stdin` with the session IDs to collect output. Do not treat a
live run, a timeout, or a proof message with the partial-result marker as
complete evidence.

## Completed unsuccessful performance trials

- Ordered value partitions: n3 has 13 classes. Some tie classes proved,
  but six distinct-value classes exceeded 90 s. Results under
  `representative-trial/`. The strengthened independent coverage theorem
  reconstructs every input from class representatives. Coverage n1..4
  proved; n5 timed out at 120 s. Coverage alone proves no equivalence.
- `mem2reg`: n3 `[1,0,2]` timed out at 180 s.
- `sroa,mem2reg,instcombine,simplifycfg`: n2 and n3 failed with a Crucible
  poison-value evaluation error. See `sroa-trial/`.
- Full UBSan: n2 failed because pointer-overflow instrumentation compares
  a pointer representation with an integer. Strict Crucible rejects that
  comparison. No memory relaxation was enabled. See `ubsan-trial/`.
- Path checking disabled: n2 timed out after 300 s and used about 12 GB.
  The n3 follow-up was stopped after 51 s. See `no-path-sat-trial/`.
- Explicit Yices path solver: n2 proved in 16.158 s; n3 timed out at 300 s.
  Session 89715 is complete. See `yices-path-trial/`.
- 100 ms path-query timeout: n2 proved; n3 failed with Z3 `push canceled`.
  See `short-query-trial/`. This is a tool failure, not an algorithm
  counterexample.

## Specification review

`review-spec.md` covers domain satisfiability, input/scratch initialization,
permutation direction, duplicate normalization, exact trace observations,
partial failure state, and proof boundaries.

The previously missing reachability criterion is now resolved in the
promoted `Reachability.v` and `ClightReachability.v`. I read both modules.
The condition is equality of initial and required **values** at every
position deeper than 16; it is not whether the original permutation fixes
those indices. The strict boundary is depth greater than 16. The proof
uses deep-position preservation, normalization fixed points, selected-slot
bounds, and no exhaustion. The call corollary keeps the valid-input memory
premises and n<=1024, and links status0/1 to reachable/unreachable.
The review records these additions. Parent owns kernel checks and proof
source changes.

Full-domain C++ source equivalence and malformed-permutation rejection
remain outside the universal Clight call proof.

## Current additional probe

The other reviewer identified that Clight can copy `Vundef` with Sset and
then discard it. Reading an uninitialized automatic C scalar can be UB.
Current Permute initializes each temporary before its reads, but the
printer only checks syntax/types and delegates initialization to proofs.
An `eval_funcall` theorem alone does not exclude this Vundef copy.

An isolated proof/printer probe is in
`build/equiv-saw/undef-probe/{Probe.v,print_probe.ml}`. It has not yet passed
coqc: line39 used an unsupported `simpl only` tactic form. The intended
function is `v8 = v9; return 0U;` with the normal ABI and declared locals.
Next: fix that tactic, prove its Clight call, print it using the unchanged
printer, and record compiler uninitialized-read diagnostics. This is a
possible general printer-contract gap, not a demonstrated production bug.

## Next steps

1. Finish the isolated Vundef-copy probe and report its precise scope.
2. Collect the three active jobs and audit all accepted logs with the
   current complete-execution rule.
3. Keep the measured domain small and explicit. Do not claim all-size
   source equivalence from these finite experiments.
4. Preserve completed evidence in a short tracked results report when
   the active jobs finish; build files remain ignored.
5. Continue tests that challenge actual assumptions until the parent's
   deadline, without changing production files or adding restricted tools.


## Final stop and handoff

The user stop instruction was received after the first status snapshot.
No new proof, test, fix, or review was started after that instruction.
Task drivers and their SAW/Z3 children received SIGTERM at
**2026-10-06 22:12:42 UTC**. Exact commands, process IDs, and working
folders are saved in `build/equiv-saw/stopped.json`.

There are **no active task proof or compiler processes**. The stopped SAW
and Z3 processes 48363, 48375, 53252, 53268, and 63191 were visible only
as zombies during the final check; they are not executing. The driver
sessions were collected and closed.

### Final job states

- Session **97189**, full n1..3: stopped with exit143 while simulating
  `[1,0,2]`. The five previously proved cases remain valid under the
  completion audit. The other four length-three cases have no new proof.
  `full-n3/results.json` records only the five completed cases.
- Session **49605**, n18 two-value family: stopped with exit143. It had
  reached `Checking proof obligations equivalence...`, but no success
  marker was produced. It is **incomplete**, not proved. Its results file
  is empty because the driver was stopped before recording a final result.
- Session **53856**, C/miter O0 trial: completed before the stop request
  with a **600-second timeout**. Results: `c-o0-trial/results.json`.
- Session **72886**, stronger Vundef probe: **completed with exit0**
  before the stop. Full `coqchk` reports `Modules were successfully checked`.
  Both compiler diagnostic logs contain the expected uninitialized read.

### Confirmed full-Permute Vundef transfer gap

The isolated `Probe.prefix_preserves_call` theorem is now compiled and
kernel-checked. It prefixes the **actual Permute AST** with
`Sset i (reg i)`. At function entry, `i` contains `Vundef`; copying it to
itself leaves the entire temporary map unchanged. The theorem transfers
**every original Clight call result and final memory**, with the original
empty external-event trace, to the prefixed AST. Thus the existing
functional and array postconditions also transfer.

The unchanged production printer accepts the prefixed AST and emits
`v8 = v8;` before initialization. GCC15.3 and Clang from the parent shell
both report that `v8` is uninitialized when read. C11 6.3.2.1 paragraph2
makes this automatic-scalar read undefined. This confirms that the general
transfer argument requires a separate C initialization condition. Current
Permute itself still has each temporary assigned before its reads; this
probe does not establish a defect in the unchanged generated C.

Completed evidence:

- `build/equiv-saw/undef-probe/Probe.v` and `Probe.vo`;
- `build/equiv-saw/undef-probe/proof.log`;
- `build/equiv-saw/undef-probe/kernel.log`;
- `build/equiv-saw/undef-probe/print_prefixed.ml`;
- `build/equiv-saw/undef-probe/prefixed.c`;
- `build/equiv-saw/undef-probe/gcc.log` and `clang.log`.

The probe's printed assumptions are the same six imported CompCert/library
assumptions used by this development, including external-function and
inline-assembly semantics; no new axiom or admitted proof was added.
The production `Permute.v` and `printer.ml` were compared with the compiled
`build/project` copies and matched.

The source was preserved before the stop in these **new untracked files**:

- `tests/equiv-saw/undef-copy/UndefCopy.v` (same proof, renamed module);
- `tests/equiv-saw/undef-copy/print_prefixed.ml`;
- `tests/equiv-saw/undef-copy/check.sh`;
- `tests/equiv-saw/undef-copy/README.md`.

These paths are relative to `spikes/clight-permute/`. The new reproducible
`check.sh` has **not been executed**. It copies current production sources,
rebuilds extraction and the printer in isolation, checks the proof, and
uses `-Werror=uninitialized` to require rejection of the variant after the
unchanged C passes. The completed manual probe used warning diagnostics
instead of that new driver's error requirement. Running the new driver is
pending work for the next agent. No production printer or proof was fixed.

### Resume commands for the next agent

Do not run these without a new instruction to resume. To check the new
self-contained Vundef regression using the already built audited CompCert
dependencies:

```sh
nix develop --impure --expr 'import ./spikes/clight-permute/shell.nix' \
  --command sh spikes/clight-permute/tests/equiv-saw/undef-copy/check.sh
```

To retry the unfinished n3 case without overwriting the earlier evidence:

```sh
nix develop --impure --expr 'import ./spikes/clight-permute/tests/equiv-saw/shell.nix' \
  --command python3 spikes/clight-permute/tests/equiv-saw/verify.py \
  --permutation 1,0,2 --timeout 2400 \
  --out spikes/clight-permute/build/equiv-saw/resumed-n3-102
```

The n18 bitcode and `family.saw` script are complete and can be rerun
unchanged from the SAW shell. Put its new log in a separate filename and
apply `verify.classify(exit_code, log_text, "Proof succeeded! equivalence")`.
Require a complete result, not only the proof-success text.

The next substantive choice is how to state and discharge the separate
C initialization condition. Keep that decision outside the proof and
printer syntax claims until it has evidence. Parent and the other review
agent have been told about the confirmed full-Permute transfer gap.
