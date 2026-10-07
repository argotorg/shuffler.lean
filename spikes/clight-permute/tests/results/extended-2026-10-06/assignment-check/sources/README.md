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
that state as the conservative loop input. The rule still needs a complete
statement-level soundness proof. It is a candidate supporting check.

Two proved statements currently exist:

- `uses_covers_reads`: a successful expression check includes each
  syntactically read temporary in the supplied assignment list.
- `permute_passes_assignment_check`: the actual `Permute.permute` AST
  passes the check. Rocq computes this fact in the kernel-checked proof.

Both statements are closed under the global context. The result is not
a C-definedness theorem. A prior assignment can copy an undefined memory
value. Memory validity, byte initialization, declaration rules, and the
Clight-to-C translation need separate arguments.

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

Use the proof shell and an existing [Clight execution build](../rocq-eval/README.md):

```sh
nix develop --impure --expr 'import ./spikes/clight-permute/shell.nix'
python3 spikes/clight-permute/tests/initialization/check.py --base /tmp/permute-eval-build --output /tmp/assignment-check
```

The output directory must be new. This check does not change the printer
or the production proof pipeline. The known printer initialization gap
remains open.
