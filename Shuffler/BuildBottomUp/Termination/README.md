Review [Defs.lean](Defs.lean) and [Theorems.lean](Theorems.lean) in this order,
after comparing the [implementation](../Defs.lean) with C++.

1. **Inputs.** `buildBottomUp_terminates` requires `Invariant 0 state`.
2. **Actual code.** The equality in `loopBody` connects the extracted body,
   initial configuration, and work after the loop to `buildBottomUp`.
3. **Continuing steps.** `Continues` includes exactly the `.ok (.yield ...)`
   results. The equality in `repeatStep` connects the step to Lean's loop.
   `Continues.repeatM_body_eq` shows that exactly these results call the next
   iteration, with the returned control and state. Done and error results exit.
4. **Body audit.** `bodyForTerminationCheck` in [Theorems.lean](Theorems.lean)
   exposes the body without its attached proof. The equality and audit checks
   are in the same file. `rfl` checks equality with the actual body.
   Batteries' `#print opaques` follows named logical
   dependencies recursively. `#guard_msgs` permits exactly
   `String.Internal.append`; a different report fails the build. Other named
   helpers use Lean's checked definitions. The
   [tests](../../../Tests/BuildBottomUpTermination.lean) also detect a nested
   `while` and a partial helper.
5. **Finite iterations.** The public theorem proves
   `Acc (Continues (loopBody source target spills).val) ((none, 0), state)`.
   This excludes an infinite chain of continuing steps. Each body call must
   also finish.
6. **Exit.** If each body call finishes, the loop reaches `.done` or an error.
   The work after the loop, `finishAction`, also uses terminating definitions.
   Exclusion of assertion errors is a separate claim.

The body audit cannot inspect functions supplied in the input. `Mapping` still
stores lookup functions, so runtime termination assumes that these functions
finish. Finite tables are a proposed change. The audit is a build check, not
a separate theorem about runtime evaluation. We trust Lean's kernel, compiler,
runtime primitives, and `implemented_by` replacements.

The measure and branch proofs are proof details in [Lemmas](../Lemmas).
Lean checks them; they are outside this public review.

Lean 4.34.0 sources:
[Loop.forIn](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/While.lean#L95-L104),
[repeatM.body](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/While.lean#L20-L24),
[Acc](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/WF.lean#L19-L31).
