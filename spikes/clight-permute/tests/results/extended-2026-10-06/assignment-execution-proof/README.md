<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Assignment proof linked to Clight execution

**Historical summary.** Raw reports, generated files, and source copies
were removed from the current tree at the user's request. They remain
in commit `a9b8307`. File paths below refer to that saved state unless
they link to a file still in the current tree. These outputs are not
required to build the proofs or run the test tools.

`AssignmentExec.v` links the candidate assignment check
to terminating Clight executions. `recorded_exec` adds assignment names
and read-check flags to the actual expression evaluations, branch choices,
intermediate environments, memories, traces, and outcomes. It does not
assume that a read is safe. A witness records an undefined self-copy with
a false safety flag.

The checked results are:

- `recorded_erases`: each execution record gives a Clight execution.
- `execution_recorded`: every terminating Clight execution in the
  supported statement form has a record, from any initial name list.
- `recorded_path`: each record gives a path in the explicit control model.
- `checked_execution_safe`: every record for a checked statement has a
  true safety flag.
- `permute_execution_safe`: every terminating execution of the actual
  Permute body has a safe record, starting with its parameter names.

The coverage proof excludes `Out_continue` through the supported form and
the induction. It rules out a loop exit from the `Sskip` tail. It retains
the actual branch decision and intermediate states in compound rules.
It does not only select an abstract path with the same final outcome.

`ExecContract.v` checks five public types.
`SoundContract.v` checks the four control-path types.
The kernel check (`kernel.log`) and policy (`kernel-policy.log`) pass:
12 allowed upstream axioms and no unsafe typing settings in the imported
context. The execution theorem report (`AssignmentExec.log`) lists upstream
assumptions from CompCert semantics. These concrete theorems are not
reported as closed under the global context. The control-path theorems
are closed (`AssignmentSound.log`).

The claim is prior assignment of temporary names. An assigned value can
still be `Vundef`, for example after a load from uninitialized memory.
Memory validity, initialized bytes, declaration rules, and Clight-to-C
translation require separate arguments. The abstract prefix theorem
does not yet have a concrete small-step or divergence connection. These
theorems do not establish the existence of a successful execution; the
main Permute theorem supplies that result on its stated domain.

The checker remains outside the production pipeline. F7 remains open.
`results.json` records build and source hashes;
`archive.json` records the retained files. All source and
artifact hashes were checked before this archive was made. The build is
`spikes/clight-permute/build/initialization/execution-checked/`.
