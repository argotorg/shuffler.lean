<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Candidate check for assignment before temporary reads

`AssignmentCheck.v` checks the actual Clight AST. It starts with parameter
names assigned and local temporary names unassigned. It checks reads in
expressions, conditions, array addresses, stored values, and return values.
It joins branch paths by intersection. It keeps separate normal and break
exits, removes returned paths from later statements, and consumes inner
breaks at the matching loop.

The checker examines each loop body from the state before its first
iteration. Assignment sets can only grow. This is the reason for using
that state as the conservative loop input. The statement-level proof now
checks this rule against an explicit control-path model and terminating
Clight execution. The checker remains outside the production pipeline.

The checker has two initial results:

- `uses_covers_reads`: a successful expression check includes each
  syntactically read temporary in the supplied assignment list.
- `permute_passes_assignment_check`: the actual `Permute.permute` AST
  passes the check. Rocq computes this fact in the kernel-checked proof.

Both statements are closed under the global context.

`AssignmentSound.v` defines paths over actual Clight statements. Both
condition branches are possible. Each path records assignment names and
a safety flag that can be false. `complete_path_safe` proves read safety
and exit assignment guarantees. `prefix_safe` covers finite prefixes,
including later loop iterations, without a termination premise.
`checked_function_prefix` and `permute_prefix_safe` start with parameter
names. These four theorems are closed under the global context.
`SoundContract.v` checks their types. Five witnesses check that unsafe
paths and loop boundaries are present in the model.

`AssignmentExec.v` connects that model to actual Clight execution.
`recorded_exec` retains expression evaluation, the selected branch,
intermediate environments, memories, traces, and outcomes. Safety is not
a premise of that relation. `recorded_erases` maps each record to a real
execution. `execution_recorded` covers every terminating execution in
the supported statement form. `recorded_path` maps each record to the
control model. `checked_execution_safe` proves that all records of a
checked statement have a true safety flag. `permute_execution_safe`
applies this result to the actual body. `ExecContract.v` checks five
public types. The concrete theorems retain upstream CompCert assumptions;
their reports and the kernel policy are in the
[execution archive](../results/extended-2026-10-06/assignment-execution-proof/README.md).

This is not a C-definedness theorem. Prior assignment does not imply that
the assigned value is defined. A load can supply `Vundef`. Memory validity,
byte initialization, declaration rules, and Clight-to-C translation need
separate arguments. The abstract prefix theorem has no concrete small-step
or divergence link yet. The execution result assumes an execution exists;
it does not replace the main Permute theorem's existence result.

The examples include the known uninitialized self-copy and the same
prefix on the actual Permute body. Both fail the check. Copying the
initialized length parameter before Permute passes. Other examples cover
one-branch assignment, returned branches, zero loop iterations, different
break paths, nested breaks, unreachable code, invalid top-level breaks,
and fallthrough. A passing memory-load example marks the scope limit
explicitly.

`check.py` compiles the baseline and changed copies. Seven weakened
decisions must fail their named negative example. A duplicate-assignment
control must pass. Import errors, syntax errors, and failures at an
unrelated theorem do not count as detected mutations. The unchanged
checker also runs through `coqchk` and the existing kernel policy.

`proof_controls.py` challenges the proof independently of those examples.
Seven weakened checker copies compile with all 21 examples removed, then
fail the named soundness theorem or branch-join lemma. Five changed
execution-record definitions fail coverage, erasure, or path theorems.
The baseline and parentheses controls pass. Three real compiler-error
controls check that unrelated failures do not count. All 19 outcomes are
in the [proof-control archive](../results/extended-2026-10-06/assignment-proof-controls/README.md).

Use the proof shell and an existing [Clight execution build](../rocq-eval/README.md):

```sh
nix develop --impure --expr 'import ./spikes/clight-permute/shell.nix'
python3 spikes/clight-permute/tests/initialization/check.py --base /tmp/permute-eval-build --output /tmp/assignment-check
python3 spikes/clight-permute/tests/initialization/sound.py --base /tmp/permute-eval-build --output /tmp/assignment-proof
python3 spikes/clight-permute/tests/initialization/proof_controls.py --base /tmp/permute-eval-build --output /tmp/assignment-proof-controls
```

The output directory must be new. This check does not change the printer
or the production proof pipeline. The known printer initialization gap
remains open.
